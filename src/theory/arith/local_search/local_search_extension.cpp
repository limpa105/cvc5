/******************************************************************************
 * Top contributors (to current version):
 * Elizaveta Pertseva
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Local Search extension.
 */

#include "theory/arith/local_search/local_search_extension.h"

#include <algorithm>
#include <cmath>
#include <iomanip>
#include <limits>
#include <queue>
#include <random>
#include <set>
#include <vector>

#include "expr/node_builder.h"
#include "theory/arith/arith_preprocess.h"
#include "theory/arith/theory_arith.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace local_search {

/** Overloading << to print __int128_t values **/
std::ostream& operator<<(std::ostream& dest, __int128_t value)
{
  std::ostream::sentry s(dest);
  if (s)
  {
    __uint128_t tmp = value < 0 ? -value : value;
    char buffer[128];
    char* d = std::end(buffer);
    do
    {
      --d;
      *d = "0123456789"[tmp % 10];
      tmp /= 10;
    } while (tmp != 0);
    if (value < 0)
    {
      --d;
      *d = '-';
    }
    int len = std::end(buffer) - d;
    if (dest.rdbuf()->sputn(d, len) != len)
    {
      dest.setstate(std::ios_base::badbit);
    }
  }
  return dest;
}

__int128_t Literal::calculateDelta(std::vector<__int128_t>& assignment)
{
  __int128_t sum = (__int128_t)0;
  for (int i = 0; i < coefficients.size(); ++i)
  {
    sum += assignment[variables[i]] * (__int128_t)coefficients[i];
  };
  return sum - (__int128_t)threshold;
};

void Literal::printAllocation()
{
  std::cout << '\n' << "Equation:" << equation;
  std::cout << '\n' << "Variables: ";
  for (__int128_t var : variables)
  {
    std::cout << var << " ";
  };
  std::cout << '\n' << "Coefficients: ";
  for (int var : coefficients)
  {
    std::cout << var << " ";
  };
  std::cout << "\n"
            << "Threshold: " << threshold;
  std::cout << "\n"
            << "Delta: " << delta;
  std::cout << std::endl;
};

LocalSearchExtension::LocalSearchExtension(Env& env, TheoryArith& parent)
    : EnvObj(env),
      d_parent(parent),
      d_varMap(context()),
      d_varList(context()),
      d_facts(context()),
      d_numVars(0)
{
}

LocalSearchExtension::~LocalSearchExtension() {}

void LocalSearchExtension::preRegisterTerm(TNode node)
{
  if (node.isVar() && node.hasName())
  {
    int currentIdx = variablesValues.size();
    nameToIdx[node.getName()] = currentIdx;

    // all variables start at 0
    // TODO: Future implementation if variable has bounds start
    // add those bounds
    variablesValues.push_back(0);

    // at the start no variable is present in any literal
    variablesToLiterals.push_back(std::set<int>());

    // also add the node for the solution
    d_varList.push_back(node);
  }
}

void LocalSearchExtension::presolve()
{
  // In current implementation there is nothing to presolve as all
  // data structures are set up  when we process assertion but this is
  // might be an ineffective way to do this and will need to change in future
  return;
}

void LocalSearchExtension::notifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Trace("theory::arith::idl")
      << "IdlExtension::notifyFact(): processing " << fact << std::endl;
  d_facts.push_back(fact);
}

Node LocalSearchExtension::ppStaticRewrite(TNode atom)
{
  // In current implementation there is nothing to rewrite as all rewrites
  // happen when setting up data structures but this might change in future
  // implementations
  return atom;
}

void LocalSearchExtension::postCheck(Theory::Effort level)
{
  if (!Theory::fullEffort(level))
  {
    return;
  }

  Trace("theory::arith::idl")
      << "IdlExtension::postCheck(): number of facts = " << d_facts.size()
      << std::endl;

  for (Node fact : d_facts)
  {
    // For simplicity, we reprocess all the literals that have been asserted to
    // this theory solver. A better implementation would process facts in
    // notifyFact().
    Trace("theory::arith::idl")
        << "IdlExtension::check(): processing " << fact << std::endl;
    processAssertion(fact);
  }

  if (!LocalSearch())
  {
    // Return a conflict that includes all the literals that have been asserted
    // to this theory solver. A better implementation would only include the
    // literals involved in the conflict here.
    NodeBuilder conjunction(Kind::AND);
    for (Node fact : d_facts)
    {
      conjunction << fact;
    }
    Node conflict = conjunction;
    // Send the conflict using the inference manager. Each conflict is assigned
    // an ID. Here, we use  ARITH_CONF_IDL_EXT, which indicates a generic
    // conflict detected by this extension
    d_parent.getInferenceManager().conflict(conflict,
                                            InferenceId::ARITH_CONF_IDL_EXT);
    return;
  }
  // Note: Local Search currently does not return conflict but will be
  // implemented in future versions. Right now in case of UNSAT it will not
  // terminate
}

bool LocalSearchExtension::collectModelInfo(TheoryModel* m,
                                            const std::set<Node>& termSet)
{
  NodeManager* nm = NodeManager::currentNM();
  // Assignments are stored in variablesValues so we add the last assignment
  // to the model
  for (size_t i = 0; i < variablesValues.size(); i++)
  {
    m->assertEquality(
        d_varList[i], nm->mkConstInt((int)variablesValues[i]), true);
  }
  return true;
}

std::set<int> LocalSearchExtension::sampleWithReplacement(
    const std::set<int>& originalSet, int sampleSize)
{
  std::vector<int> elements(originalSet.begin(), originalSet.end());
  std::set<int> sampledSet;
  std::uniform_int_distribution<> dis(0, elements.size() - 1);
  for (int i = 0; i < sampleSize; ++i)
  {
    int index = dis(rd_generator);
    sampledSet.insert(elements[index]);
  }
  return sampledSet;
}

__int128_t LocalSearchExtension::getUpperBound(double value)
// 2.5 -> 2 && -2.5 -> -3
{
  if (value > 0)
  {
    return std::ceil(value);
  }
  else
  {
    return std::floor(value);
  }
};

void LocalSearchExtension::printSet(std::set<int> mySet, std::string name)
{
  std::cout << name << ": ";
  for (int const& elem : mySet)
  {
    std::cout << elem << " ";
  }
  std::cout << "\n";
  return;
};

void LocalSearchExtension::printUnsat()
{
  printSet(unsatLiterals, "UNSAT");
  return;
}

void LocalSearchExtension::printChange(std::vector<__int128_t> change)
{
  for (const auto& pair : nameToIdx)
  {
    std::cout << pair.first << ":" << change[pair.second] << " ";
  }
  std::cout << std::endl;
}

void LocalSearchExtension::processAssertion(TNode assertion)
{
  Literal literal;
  literal.equation = assertion;
  literal.isNot = assertion.getKind() == Kind::NOT;
  // continue to child if Not
  TNode atom = literal.isNot ? assertion[0] : assertion;
  literal.isEqual = atom.getKind() == Kind::EQUAL;
  int idx_literal = literals.size();
  // Check that the parser worked and we are only dealing with
  // == or >=
  Assert(literal.isEqual || atom.getKind() == Kind::GEQ);
  Assert(atom.getNumChildren() == 2);
  // CVC5 parses everthing as >= but local search works on <= so
  // we will need to flip the signs but this is equivalent to moving
  // all variables to RHS and constants to LHS
  TNode LHS = atom[0];
  TNode RHS = atom[1];
  parseOneSide(LHS, literal);
  // Now move all vars to RHS
  for (auto& v : literal.coefficients)
  {
    v *= -1;
  }
  // Move threshold back to RHS
  literal.threshold *= -1;
  parseOneSide(RHS, literal);
  literal.delta = literal.calculateDelta(variablesValues);
  for (const auto& var : literal.variables)
  {
    // add ability to map from variables to literal
    variablesToLiterals[var].insert(idx_literal);
  }
  if (!checkIfSat(literal, literal.delta))
  {
    unsatLiterals.insert(idx_literal);
  }
  addLiteral(literal);
}

void LocalSearchExtension::parseOneSide(TNode& side, Literal& literal)
{
  if (side.getKind() == Kind::ADD)
  {
    for (int i = 0; i < side.getNumChildren(); ++i)
    {
      TNode child = side[i];
      parseOneSide(child, literal);
    }
  }
  else if (side.getKind() == Kind::MULT)
  {
    literal.coefficients.push_back(side[0].getConst<Rational>().getDouble());
    literal.variables.push_back(nameToIdx[side[1].getName()]);
  }
  else
  {
    if (side.isConst())
    {
      // move to a different side if constant
      literal.threshold += -1 * side.getConst<Rational>().getDouble();
    }
    else
    {
      // In case just variable we have a coefficient of 1
      literal.coefficients.push_back(1);
      literal.variables.push_back(nameToIdx[side.getName()]);
    }
  }
}

bool LocalSearchExtension::checkIfSat(Literal literal, __int128_t delta)
{
  // SAT delta values for the 4 possible cases
  if ((!literal.isNot && literal.isEqual && delta == (__int128_t)0)
      || (literal.isNot && !literal.isEqual && delta > (__int128_t)0)
      || (literal.isNot && literal.isEqual && delta != (__int128_t)0)
      || (!literal.isNot && !literal.isEqual && delta <= (__int128_t)0))
  {
    return true;
  }
  return false;
}

std::vector<std::tuple<std::vector<__int128_t>, int, int>>
LocalSearchExtension::getPossibleMoves(bool inDscore)
{
  std::vector<std::tuple<std::vector<__int128_t>, int, int>> allowedMoves;
  std::set<int> allowedLiterals;
  if (!inDscore)
  {
    allowedLiterals = unsatLiterals;
  }
  else
  {
    // If in Distance Score Mode randomly sample NUMLITCONSIDER variables
    allowedLiterals = sampleWithReplacement(unsatLiterals, NUMLITCONSIDER);
  }
  for (int const& literal_idx : allowedLiterals)
  {
    Literal chosenLiteral = literals[literal_idx];
    assert(chosenLiteral.variables.size() != 0);
    // For all variables in an UNSAT literal compute a potential critical move
    for (int varIdxInLit = 0; varIdxInLit < chosenLiteral.variables.size();
         varIdxInLit++)
    {
      int varIdxInSlv = chosenLiteral.variables[varIdxInLit];
      auto move =
          criticalMove(varIdxInLit, varIdxInSlv, chosenLiteral, inDscore);
      // If cirtical move was found add it to allowed moves but add varIdxInSlv
      // to make computing the score easier
      if (move)
      {
        for (auto const& item : move.value())
        {
          allowedMoves.push_back(
              std::make_tuple(item.first, item.second, varIdxInSlv));
        }
      }
    }
  }
  return allowedMoves;
}

std::optional<std::vector<std::pair<std::vector<__int128_t>, int>>>
LocalSearchExtension::criticalMove(int varIdxInLit,
                                   int varIdxInSlv,
                                   Literal literal,
                                   bool inDscore)
{
  __int128_t delta;
  int direction;
  std::vector<std::pair<std::vector<__int128_t>, int>> results;
  int coef = literal.coefficients[varIdxInLit];
  // case : ==
  if (literal.isEqual && !literal.isNot)
  {
    __int128_t deltaSum = literal.delta;
    if (coef != 0 && deltaSum % coef == 0)
    {
      delta = deltaSum / coef;
    }
    else
    {
      delta = (deltaSum * coef > 0) ? -1 : 1;
    }

    // case: not ==
  }
  else if (literal.isEqual && literal.isNot)
  {
    if (inDscore || doNotMove[2 * varIdxInSlv + 1] <= 0)
    {
      std::vector<__int128_t> change1 = variablesValues;
      change1[varIdxInSlv] -= 1;
      results.push_back(std::make_pair(change1, 0));
    }
    // If in Dscore all moves are always allowed (we do not check the doNotMove
    // list)
    if (inDscore || doNotMove[2 * varIdxInSlv] <= 0)
    {
      std::vector<__int128_t> change2 = variablesValues;
      change2[varIdxInSlv] += 1;
      results.push_back(std::make_pair(change2, 1));
    }
    if (results.size() > 0)
    {
      return results;
    }
    else
    {
      return std::nullopt;
    }
    // case: >=
  }
  else if (!literal.isNot)
  {
    delta = getUpperBound(std::abs((double)literal.delta / (double)coef));
    if (coef < 0) delta *= (__int128_t)-1;
    // case: not >=
  }
  else
  {
    delta = getUpperBound(std::abs((double)(1 - literal.delta) / (double)coef));
    if (coef > 0) delta *= (__int128_t)-1;
  }
  if (delta == 0)
  {
    // delta should never be zero
    AlwaysAssert(false);
  }
  assert(delta != 0);
  direction = delta > 0 ? 0 : 1;
  // Check that we have not moved the variable in the opposite direction in less
  // than allowed num of iterations if we have no critical move can be preformed
  if (!inDscore && doNotMove[2 * varIdxInSlv + (direction ^ 1)] > 0)
  {
    return std::nullopt;
  }
  std::vector<__int128_t> change = variablesValues;
  change[varIdxInSlv] -= delta;
  results.push_back(std::make_pair(change, direction));
  return results;
}

int LocalSearchExtension::computeScore(std::vector<__int128_t> change,
                                       int varIdx)
{
  // score: how many new SAT clauses we get from a new assignment -
  // new UNSAT clauses we get from a new assignment
  int score = 0;
  for (int literalIdx : variablesToLiterals[varIdx])
  {
    Literal literal = literals[literalIdx];
    int newDelta = literal.calculateDelta(change);
    bool newSat = checkIfSat(literal, newDelta);
    bool oldSat = checkIfSat(literal, literal.delta);
    // if a literal became SAT increment score
    if (!oldSat && newSat)
    {
      score += 1 * literal.weight;
    }
    // If a literal became UNSAT decrement the score
    if (oldSat && !newSat)
    {
      score -= 1 * literal.weight;
    }
  }
  return score;
}

int LocalSearchExtension::computeDistanceScore(Literal literal,
                                               std::vector<__int128_t> change,
                                               int varIdx)
{
  // Distance score: how far away we are from being SAT. If SAT distance is zero
  // case >=
  if (!literal.isEqual && !literal.isNot)
  {
    return std::max(literal.calculateDelta(change), (__int128_t)0)
           * literal.weight;

    // case ==
  }
  else if (literal.isEqual && !literal.isNot)
  {
    __int128_t delta = literal.calculateDelta(change);
    if (delta < 1)
    {
      delta = delta * -1;
    }
    return std::max(delta, (__int128_t)0) * literal.weight;

    // case not >=
  }
  else if (!literal.isEqual && literal.isNot)
  {
    return -1 * std::min(literal.calculateDelta(change) - 1, (__int128_t)0)
           * literal.weight;

    // case: not ==
  }
  else
  {
    if (literal.calculateDelta(change) == 0)
    {
      return 1 * literal.weight;
    }
    else
    {
      return 0;
    }
  }
}

__int128_t LocalSearchExtension::stepForward(std::vector<__int128_t> change,
                                             int varIdx,
                                             int direction)
{
  variablesValues = change;
  // For all values in doNotMove decrement by 1
  for (int& value : doNotMove)
  {
    if (value != 0)
    {
      value--;
    }
  }
  // update the move for the change
  doNotMove[2 * varIdx + (direction)] =
      DONOTMOVECONST + doNotMoveDistribution(rd_generator);
  // record satLiterals to update unsatLiterals later on
  std::set<int> satLiterals = std::set<int>();
  int score = 0;
  for (auto& literal_idx : variablesToLiterals[varIdx])
  {
    Literal literal = literals[literal_idx];
    __int128_t oldDelta = literal.delta;
    bool oldSat = checkIfSat(literal, oldDelta);
    literals[literal_idx].delta = literals[literal_idx].calculateDelta(change);
    bool newSat =
        checkIfSat(literals[literal_idx], literals[literal_idx].delta);
    // If variable became UNSAT decrement score by weight
    if (oldSat && !newSat)
    {
      unsatLiterals.insert(literal_idx);
      score -= literal.weight;
    }
    // If variable became SAT increment score by weight
    if (!oldSat && newSat)
    {
      satLiterals.insert(literal_idx);
      score += literal.weight;
    }
  }
  std::set<int> result;
  if (satLiterals.size() == 0)
  {
    // If we ever get here we are experiencing an overflow in delta calculation
    // and need to restart
    nonImprove = MAXNONIMPROVE + 1;
    return 0;
  }
  // compute unsatLiterals - new satLiterals
  std::set_difference(unsatLiterals.begin(),
                      unsatLiterals.end(),
                      satLiterals.begin(),
                      satLiterals.end(),
                      std::inserter(result, result.end()));
  unsatLiterals = result;
  return score;
};

bool LocalSearchExtension::checkIfSolutionSat()
{
  for (Literal literal : literals)
  {
    if (!checkIfSat(literal, literal.calculateDelta(variablesValues)))
    {
      return false;
    }
  }
  return true;
}

void LocalSearchExtension::restart()
{
  std::vector<int> tempVec(variablesValues.size() * 2 + 1, 0);
  doNotMove = tempVec;
  std::vector<__int128_t> tempVec2(variablesValues.size(), (__int128_t)0);
  variablesValues = tempVec2;
  unsatLiterals = std::set<int>();
  for (int i = 0; i < literals.size(); i++)
  {
    // recompute the deltas with the initial assignment and set weights back to
    // 1
    literals[i].delta = literals[i].calculateDelta(variablesValues);
    literals[i].weight = 1;
    if (!checkIfSat(literals[i], literals[i].delta))
    {
      unsatLiterals.insert(i);
    }
  }
}

void LocalSearchExtension::applyPAWS()
{
  std::uniform_real_distribution<> distr(0.0, 1.0);
  // If smoothing activated decrease satisfied by 1 and
  // increase unsatisfied by 1: since we do not keep track
  // of satisfied this is equivalent to decreasing all by 1
  // and increasing unsatified by 2.
  if (distr(rd_generator) < SMOOTHING)
  {
    for (int const& i : unsatLiterals)
    {
      literals[i].weight += 2;
    }
    for (int i = 0; i < literals.size(); i++)
    {
      if (literals[i].weight > 1)
      {
        literals[i].weight -= 1;
      }
    }
  }
  // If not smoothing just increase unsatisfied by 1
  else
  {
    for (int const& i : unsatLiterals)
    {
      literals[i].weight += 1;
    }
  }
}

bool LocalSearchExtension::LocalSearch()
{
  // Initialize doNotMove and random generator
  std::vector<int> tempVec(variablesValues.size() * 2 + 1, 0);
  doNotMove = tempVec;
  std::random_device rd;
  std::mt19937 gen(rd());
  rd_generator = gen;
  rd_generator.seed(1);
  std::uniform_int_distribution<> tempDistribution(0, 10);
  doNotMoveDistribution = tempDistribution;
  int satScore = literals.size() - unsatLiterals.size();
  int bestScore = satScore;
  // This should be a heuristic in the future
  while (true)
  {
    // If a solution has been found
    if (unsatLiterals.size() == 0)
    {
      // Check that all literals are SAT
      if (!checkIfSolutionSat())
      {
        AlwaysAssert(false);
      }
      return true;
    }
    // First try computing a decreasing change using regular score
    std::vector<std::tuple<std::vector<__int128_t>, int, int>> possibleMoves =
        getPossibleMoves(false);
    int bestDirection;
    std::vector<__int128_t> bestChange;
    int bestVarIdx;
    bool decreasingChangeExists = false;
    for (auto move : possibleMoves)
    {
      auto change = std::get<0>(move);
      int direction = std::get<1>(move);
      int varIdxInSlv = std::get<2>(move);
      int score = computeScore(change, varIdxInSlv);
      // decreasing means more SAT than last time
      if (bestScore < score + satScore)
      {
        decreasingChangeExists = true;
        bestScore = score + satScore;
        bestDirection = direction;
        bestChange = change;
        bestVarIdx = varIdxInSlv;
      }
    }
    // If no decreasing option found activate Distance Score
    if (!decreasingChangeExists)
    {
      // change clause weights using PAWS scheme
      applyPAWS();
      bestScore = std::numeric_limits<int>::max();
      std::vector<std::tuple<std::vector<__int128_t>, int, int>>
          newPossibleMoves = getPossibleMoves(true);
      for (auto move : newPossibleMoves)
      {
        auto change = std::get<0>(move);
        int direction = std::get<1>(move);
        int varIdxInSlv = std::get<2>(move);
        int score = 0;
        for (int literal_idx : variablesToLiterals[varIdxInSlv])
        {
          Literal literal = literals[literal_idx];
          score +=
              (computeDistanceScore(literal, change, varIdxInSlv)
               - computeDistanceScore(literal, variablesValues, varIdxInSlv));
        }
        // Best distance score is that which minimizes distance to SAT compared
        // to current assignment
        if (score < bestScore
            || (score == bestScore
                && doNotMove[2 * varIdxInSlv + direction ^ 1]
                       < doNotMove[2 * bestVarIdx + bestDirection ^ 1]))
        {
          decreasingChangeExists = true;
          bestDirection = direction;
          bestVarIdx = varIdxInSlv;
          bestScore = score;
          bestChange = change;
        }
      }
    }
    assert(decreasingChangeExists);
    // Change assignment
    satScore += stepForward(bestChange, bestVarIdx, bestDirection);
    bestScore = satScore;
    nonImprove += 1;
    if (nonImprove > MAXNONIMPROVE)
    {
      restart();
      satScore = literals.size() - unsatLiterals.size();
      bestScore = satScore;
      nonImprove = 0;
    }
  }
}

}  // namespace local_search
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
