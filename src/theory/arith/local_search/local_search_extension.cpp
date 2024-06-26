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
#include <chrono>
#include <fstream>
#include <tuple>


#include "expr/node_builder.h"
#include "theory/arith/arith_preprocess.h"
#include "theory/arith/theory_arith.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

using namespace std::chrono;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace local_search {

Integer Literal::calculateDelta(std::vector<Integer>& assignment)
{
  Integer sum = 0;
  for (int i = 0; i < coefficients.size(); ++i)
  {
    sum += assignment[variables[i]] * coefficients[i];
  };
  return sum - threshold;
};

void Literal::printAllocation()
{
  std::cout << '\n' << "Equation:" << equation;
  std::cout << '\n' << "Variables: ";
  for (Integer var : variables)
  {
    std::cout << var << " ";
  };
  std::cout << '\n' << "Coefficients: ";
  for (Integer var : coefficients)
  {
    std::cout << var << " ";
  };
  std::cout << "\n"
            << "Threshold: " << threshold;
  std::cout << "\n"
            << "Delta: " << delta;
  std::cout << std::endl;
  std::cout << "\n"
            << "IsNot: " << isNot;
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
  d_facts.push_back(std::make_tuple(atom, pol, fact));

}

Node LocalSearchExtension::ppStaticRewrite(TNode atom)
{
  // In current implementation there is nothing to rewrite as all rewrites
  // happen when setting up data structures but this might change in future
  // implementations
  return atom;
}

bool LocalSearchExtension::postCheck(Theory::Effort level)
{
  foundASolution = false;
  if (!Theory::fullEffort(level))
  {
    //return;
    MAXNONIMPROVE = 100;
  }
  else {
    MAXNONIMPROVE = 10000;
  }

  Trace("theory::arith::idl")
      << "IdlExtension::postCheck(): number of facts = " << d_facts.size()
      << std::endl;

  auto start = high_resolution_clock::now();
  currentLiteralsIdx.clear();
  d_Bounds.clear();
  unsatLiterals.clear();
  idxToCount.clear();
  totalAsserts = 0;
  idxToMainIdx.clear();
  sentSmartConflict = false;
  //if (level == Theory::EFFORT_FULL) 
  dls_conflict.clear();
  ConflictFound = false;
  std::vector<std::set<int>> tempMap(variablesValues.size(), std::set<int>());
  variablesToLiterals = tempMap;
  std::vector<std::optional<std::pair<Integer,int>>> tempUp(variablesValues.size(), std::nullopt);
  upperBound = tempUp;
  std::vector<std::optional<std::pair<Integer,int>>> tempEq(variablesValues.size(), std::nullopt);
  equalBound = tempEq;
  std::vector<std::optional<std::pair<Integer,int>>> tempLower(variablesValues.size(), std::nullopt);
  lowerBound = tempLower;
  auto stop = high_resolution_clock::now();
  auto duration = duration_cast<microseconds>(stop - start);
  //std::cout << duration.count() << "\n";
  equalities.clear();
  inequalities.clear();
  nonequalities.clear();
  for (auto i :d_facts){
    Node fact = std::get<2>(i);
  if (fact.getKind()==Kind::EQUAL){
    equalities.push_back(fact);
  }
  else if (fact.getKind()==Kind::GEQ){
    inequalities.push_back(fact);
  }
  else if (fact.getKind()==Kind::NOT && fact[0].getKind()==Kind::GEQ ){
    inequalities.push_back(fact);
  }
  else if (fact.getKind()==Kind::NOT && fact[0].getKind()==Kind::EQUAL ){
    nonequalities.push_back(fact);
  }
  else{
    AlwaysAssert(false);
  }
  }
  // std::cout << "EQUALITIES\n";
  //  for(auto eq:equalities){
  //      std::cout << eq << "\n";
  //  }
  //  std::cout << "NON EQUALITIES\n";
  //    for(auto eq:nonequalities){
  //      std::cout << eq << "\n";
  //  }
  //  std::cout << "INEQUALITIES\n";
  //  for(auto eq:inequalities){
  //      std::cout << eq << "\n";
  //  }
  //std::cout << inequalities.size() << "\n";
  // std::cout << equalities.size() << "\n";
  if (inequalities.size()!= 0){
  auto result = substituteVariables(equalities, inequalities);
  equalities = result.second;
  // std::cout << equalities.size() << "\n";
  inequalities = result.first;
    // std::cout << "NEW EQUALITIES\n";
    // for(auto eq:equalities){
    //   std::cout << eq << "\n";
    // }
    // std::cout << "NEW INEQUALITIES\n";
    // for(auto eq:inequalities){
    //   std::cout << eq << "\n";
    // }
  for(int i=0; i<inequalities.size(); i++){
    processAssertion(inequalities[i], i);
  }
  } else {
     for(int i=0; i<equalities.size(); i++){
     processAssertion(equalities[i], i);
   }
  }
  for(int i=0; i<nonequalities.size(); i++){
    processAssertion(nonequalities[i], i);
  }

  if (LocalSearch()){
    Trace("arith") << "local search found a solution"  << std::endl;
    foundASolution = true;
    return false;
  }
  Trace("arith") << "simplex needed"  << std::endl;
  return true;


  // if (!LocalSearch())
  // {
  //   // Return a conflict that includes all the literals that have been asserted
  //   // to this theory solver. A better implementation would only include the
  //   // literals involved in the conflict here.
  //   NodeBuilder conjunction(Kind::AND);
  //   for (Node fact : d_facts)
  //   {
  //     conjunction << fact;
  //   }
  //   Node conflict = conjunction;
  //   // Send the conflict using the inference manager. Each conflict is assigned
  //   // an ID. Here, we use  ARITH_CONF_IDL_EXT, which indicates a generic
  //   // conflict detected by this extension
  //   d_parent.getInferenceManager().conflict(conflict,
  //                                           InferenceId::ARITH_CONF_IDL_EXT);
  //   return;
  // }
  // // Note: Local Search currently does not return conflict but will be
  // implemented in future versions. Right now in case of UNSAT it will not
  // terminate
}

Integer LocalSearchExtension::evalExpression(Node fact){
  if (fact.getKind() == Kind::CONST_INTEGER){
    return fact.getConst<Rational>().getNumerator();
  }
  if (fact.getKind() == Kind::VARIABLE || fact.getKind() ==Kind::SKOLEM){
    return variablesValues[nameToIdx[fact.getName()]];
  }

  if (fact.getKind() == Kind::MULT){
    Integer product = 1;
    for (int i =0; i<fact.getNumChildren(); i++){
      product *= evalExpression(fact[i]);
    }
    return product;
  }
  if (fact.getKind() == Kind::ADD){
    Integer summation = 0;
    for (int i =0; i<fact.getNumChildren(); i++){
      summation += evalExpression(fact[i]);
    }
    return summation;
  }
  AlwaysAssert(false) << fact.getKind();

};

bool LocalSearchExtension::collectModelInfo(TheoryModel* m,
                                            const std::set<Node>& termSet)
{
  NodeManager* nm = NodeManager::currentNM();
  // Assignments are stored in variablesValues so we add the last assignment
  // to the model
   for (int i=equalities.size()-1; i>=0; i--){
    variablesValues[nameToIdx[equalities[i][0].getName()]] = evalExpression(equalities[i][1]);
  }
  for (size_t i = 0; i < variablesValues.size(); i++)
  {
    m->assertEquality(d_varList[i], nm->mkConstInt(variablesValues[i]), true);
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


Integer LocalSearchExtension::getUpperBound(Integer a, Integer b)
// a/b = 2.5 -> 3 &&  a/b = -2.5 -> -3
{
  // if result is positivie
  if (a.sgn() == b.sgn())
  {
    return a.ceilingDivideQuotient(b);
  }
  else
  {
    // if result is negative
    return a.floorDivideQuotient(b);
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

std::pair<Node,bool> LocalSearchExtension::subVarHelper(Node fact, Node ogf, Node newf, bool changed) {
    if (fact == ogf){
        return std::make_pair(newf, true);
    }
    if (fact.getNumChildren()!=0){
        std::vector<std::pair<Node, bool>> children ;
        for (int i =0; i<fact.getNumChildren(); i++){
            children.push_back(subVarHelper(fact[i], ogf, newf, changed));
        }
        NodeManager* nm = NodeManager::currentNM();
        std::vector<Node> result;
        for(auto child: children){
          if (child.second == true){
            changed = true;
          }
          result.push_back(child.first);
        }
        return std::make_pair(rewrite(nm->mkNode(fact.getKind(), result)), changed);
    }
    return std::make_pair(fact,changed);

}

std::pair<std::vector<Node>, std::vector<Node>> LocalSearchExtension::substituteVariables(std::vector<Node> equalities, std::vector<Node> inequalities){
    std::vector<Node> done_equalities;
    if (equalities.size() == 0){
      return std::make_pair(inequalities,equalities);
    }

    //std::cout << "Equalie" << equalities.size() << "\n";
    //std::cout << "HELLO\n";
        // Need to think about case where fact is just not present in any case
      while(!equalities.empty()) {
        //std::cout << "In the loop\n";
        Node currentEquality = equalities.back();
        done_equalities.push_back(currentEquality);
        equalities.pop_back();
        if (currentEquality[0].getKind()!=Kind::VARIABLE){
          nonequalities.push_back(currentEquality);
          continue;
        }
        bool changeMade = false;
        //std::cout << "NEW ITER\n";
      for (int i=0; i<equalities.size(); i++) {
            Node equality = equalities[i];
            auto value = subVarHelper(equality, currentEquality[0], currentEquality[1], false);
            Node result = value.first;
            if (value.second){
              changeMade = true;
            } else {
              //std::cout << "CHANGE NOT MADE\n";
            }
            if (result.getKind() == Kind::CONST_BOOLEAN){
              if(result.getConst<bool>() == true){
              equalities.erase(equalities.begin()+i);
              i--;
             } else {
              ConflictFound = true;
              // std::cout << result;
              // //std::cout << "CONFLICT FOUND EQ\n";
              // std::cout << equality << "," << currentEquality << "\n";
              return std::make_pair(inequalities, done_equalities);
             }
            } else {
            equalities[i] = result;
            }
        }
        for (int i=0; i<inequalities.size(); i++) {
          Node equality = inequalities[i];
          // std::cout << "Starting subs\n";
          // std::cout << currentEquality << "\n";
          // std::cout << "INEquality\n";
          // std::cout << equality << "\n";
           auto value = subVarHelper(equality, currentEquality[0], currentEquality[1], false);
            Node result = value.first;
            if (value.second){
          //      std::cout << "Starting subs\n";
          //  std::cout << currentEquality << "\n";
          // std::cout << "INEquality\n";
          // std::cout << equality << "\n";
          //     std::cout << "Result\n";
              changeMade = true;
              //std::cout << result << "\n";
            }
            if (result.getKind() == Kind::CONST_BOOLEAN){
              if (result.getConst<bool>() == true){
              inequalities.erase(inequalities.begin()+i);
              i--;
            } else {
             
              ConflictFound = true;
              std::cout << result;
              // std::cout << "CONFLICT FOUND INEQ\n";
              // std::cout << equality << "," << currentEquality << "\n";
              //AlwaysAssert(false) << equality << "," << currentEquality<< "," << result;
              return std::make_pair(inequalities, done_equalities);
            }
            } else {
            inequalities[i] = result;
            }

        }
       for (int i=0; i<nonequalities.size(); i++) {
            Node equality = nonequalities[i];
            // std::cout << "NONquality\n";
            // std::cout << equality << "\n";
            auto answer = subVarHelper(equality, currentEquality[0], currentEquality[1],false);
            Node result = answer.first;
            if (answer.second){
          //      std::cout << "Starting subs\n";
          //  std::cout << currentEquality << "\n";
          // std::cout << "NONEquality\n";
          // std::cout << equality << "\n";
          //     std::cout << "Result\n";
              changeMade = true;
              //std::cout << result << "\n";
            }
            if (result.getKind() == Kind::CONST_BOOLEAN){
              if (result.getConst<bool>() == true){
              nonequalities.erase(nonequalities.begin()+i);
              i--;
            } else{
              ConflictFound = true;
              // std::cout << result;
              // std::cout << "CONFLICT FOUND NONEQ\n";
              // std::cout << equality << "," << currentEquality << "\n";
               //AlwaysAssert(false) << equality << "," << currentEquality;
              return std::make_pair(inequalities, done_equalities);;
            }
            } else {
            nonequalities[i] = result;
            }
        }
         if (!changeMade){
            //std::cout << "CHANGE WASNT MADE\n";
           nonequalities.push_back(currentEquality);
        }
      // std::cout << "Equalities processed" << "\n";
      // std::cout << done_equalities.size() << "\n";
      }
  return std::make_pair(inequalities, done_equalities);
}


void LocalSearchExtension::printUnsat()
{
  printSet(unsatLiterals, "UNSAT");
  return;
}

void LocalSearchExtension::printChange(std::vector<Integer> change)
{
  for (const auto& pair : nameToIdx)
  {
    std::cout << pair.first << ":" << change[pair.second] << " ";
  }
  std::cout << std::endl;
}

void LocalSearchExtension::processAssertion(TNode assertion, int MainIdx)
{
  //
  //AlwaysAssert(totalAsserts == idxToCount.size());
  //std::cout << "First:" << assertion << "\n";
  totalAsserts +=1;
  int idx_literal = currentLiteralsIdx.size();
  // CASE 1: Literal has already been processed
  if (idToIdxLiteral.count(assertion.getId())>0){
    if(std::find(currentLiteralsIdx.begin(), currentLiteralsIdx.end(), idToIdxLiteral.at(assertion.getId())) != currentLiteralsIdx.end()){
      return;
    }
    currentLiteralsIdx.push_back(idToIdxLiteral.at(assertion.getId()));
    idxToMainIdx[idx_literal] = MainIdx;
    //std::cout << "Added to idx count old\n";
    AlwaysAssert(idxToCount.count(idx_literal)==0);
    idxToCount[idx_literal]= 0;
    allLiterals[currentLiteralsIdx[idx_literal]].delta = allLiterals[currentLiteralsIdx[idx_literal]].calculateDelta(variablesValues);
    allLiterals[currentLiteralsIdx[idx_literal]].weight = 1;
    Literal literal = allLiterals[currentLiteralsIdx[idx_literal]];
    for (const auto& var : literal.variables)
    {
    // add ability to map from variables to literal
    variablesToLiterals[var].insert(idx_literal);
    }
    if (!checkIfSat(literal, literal.delta))
    {
    unsatLiterals.insert(idx_literal);
    }

    return;
  }
  //idxToCount[currentLiteralsIdx[allLiterals.size()]]= 0;
  // CASE 2: Has not been processed
  bool isNot = assertion.getKind() == Kind::NOT;
  TNode atom = isNot ? assertion[0] : assertion;
  // if Upper Bound 
//   if (atom.getKind()==Kind::GEQ && atom[0].isVar() && atom[1].isConst()){
//     //std::cout << "UPPER\n";
//     int varIdx = nameToIdx[atom[0].getName()];
//     // x >= 2 -> x 
//     Integer limit = atom[1].getConst<Rational>().getNumerator();
//     if (!isNot) {
//     // not x >= 2 > x <2 -> x <= 1
//       if (upperBound[varIdx].has_value()){
//         variablesValues[varIdx] = Integer::max(upperBound[varIdx].value().first, limit);
//         upperBound[varIdx] = std::make_pair(variablesValues[varIdx], MainIdx);
//         d_Bounds.push_back(MainIdx);
// ////PAUSe
//       } else {
//       variablesValues[varIdx] = limit;
//       upperBound[varIdx] = std::make_pair(limit, MainIdx);
//       d_Bounds.push_back(MainIdx);
//       }
//     } else {
//        if (lowerBound[varIdx].has_value()){
//         variablesValues[varIdx] = Integer::min(lowerBound[varIdx].value().first, limit-1);
//         upperBound[varIdx] = std::make_pair(variablesValues[varIdx], MainIdx);
//         d_Bounds.push_back(MainIdx);
//       } else {
//       //std::cout << limit << "\n";
//       variablesValues[varIdx] = limit -1;
//       lowerBound[varIdx] = std::make_pair(limit -1, MainIdx);
//       d_Bounds.push_back(MainIdx);
//       }
//     }
//     for (auto idx : variablesToLiterals[varIdx]) {
//       allLiterals[currentLiteralsIdx[idx]].delta = allLiterals[currentLiteralsIdx[idx]].calculateDelta(variablesValues);
//       if (!checkIfSat(allLiterals[currentLiteralsIdx[idx]], allLiterals[currentLiteralsIdx[idx]].delta)){
//           unsatLiterals.insert(idx);
//       }
//       else {
//         unsatLiterals.erase(idx);
//       }
//     }
//     return;
//   }
//   // Equal
//   if (!isNot && assertion.getKind()==Kind::EQUAL && assertion[0].isVar() && assertion[1].isConst()){
//     //std::cout << "EQUAL\n";
//     int varIdx = nameToIdx[assertion[0].getName()];
//     Integer limit = assertion[1].getConst<Rational>().getNumerator();
//     if (equalBound[varIdx].has_value() && 
//           (equalBound[varIdx].value().first!= limit)){
//         ConflictFound = true; 
//         dls_conflict.push_back(d_facts[equalBound[varIdx].value().second]);
//     }
//     variablesValues[varIdx] = limit;
//     equalBound[varIdx] = std::make_pair(limit, MainIdx);
//     d_Bounds.push_back(MainIdx);
//     for (auto idx : variablesToLiterals[varIdx]) {
//     allLiterals[currentLiteralsIdx[idx]].delta = allLiterals[currentLiteralsIdx[idx]].calculateDelta(variablesValues);
//     if (!checkIfSat(allLiterals[currentLiteralsIdx[idx]], allLiterals[currentLiteralsIdx[idx]].delta)){
//           unsatLiterals.insert(idx);
//       }
//     else {
//       unsatLiterals.erase(idx);
//     }
//     }
//     return;
//   }
//   if (!isNot && assertion.getKind()==Kind::GEQ && assertion[0].getKind()==Kind::MULT && assertion[0][1].isVar() &&  assertion[0][0].getConst<Rational>().getNumerator() == Integer(-1) && assertion[1].isConst()){
//     std::cout << "Lower\n";
//     int varIdx = nameToIdx[assertion[0][1].getName()];
//     Integer limit = Integer(-1) * assertion[1].getConst<Rational>().getNumerator();
//     if (lowerBound[varIdx].has_value()){
//       variablesValues[varIdx] = Integer::min(lowerBound[varIdx].value().first, limit);
//       lowerBound[varIdx] = std::make_pair(variablesValues[varIdx], MainIdx);
//       d_Bounds.push_back(MainIdx);
//     } 
//     else {
//     variablesValues[varIdx] =  limit;
//     lowerBound[varIdx] =  std::make_pair(limit, MainIdx);
//     d_Bounds.push_back(MainIdx);
//     }
//     for (auto idx : variablesToLiterals[varIdx]) {
//       allLiterals[currentLiteralsIdx[idx]].delta = allLiterals[currentLiteralsIdx[idx]].calculateDelta(variablesValues);
//     if (!checkIfSat(allLiterals[currentLiteralsIdx[idx]], allLiterals[currentLiteralsIdx[idx]].delta)){
//         unsatLiterals.insert(idx);
//       }
//     else {
//       unsatLiterals.erase(idx);
//     }
//     }
//     return;
//   }
  //std::cout << "Cont:" << assertion << "\n";
  processedAsserts +=1;



  Literal literal;
  literal.equation = assertion;
  literal.isNot = assertion.getKind() == Kind::NOT;
  // continue to child if Not
  //TNode atom = literal.isNot ? assertion[0] : assertion;
  literal.isEqual = atom.getKind() == Kind::EQUAL;
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
    v *= Integer(-1);
  }
  // Move threshold back to RHS
  literal.threshold *= Integer(-1);
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
  //std::cout << "Added to idx count\n";
  idToIdxLiteral[assertion.getId()] = allLiterals.size();
  currentLiteralsIdx.push_back(allLiterals.size());
  idxToMainIdx[idx_literal] = MainIdx;
  AlwaysAssert(idxToCount.count(idx_literal)==0);
  idxToCount[idx_literal]= 0;
  allLiterals.push_back(literal);
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
    literal.coefficients.push_back(side[0].getConst<Rational>().getNumerator());
    literal.variables.push_back(nameToIdx[side[1].getName()]);
  }
  else
  {
    if (side.isConst())
    {
      // move to a different side if constant
      literal.threshold +=
          Integer(-1) * side.getConst<Rational>().getNumerator();
    }
    else
    {
      // In case just variable we have a coefficient of 1
      literal.coefficients.push_back(Integer(1));
      literal.variables.push_back(nameToIdx[side.getName()]);
    }
  }
}

bool LocalSearchExtension::checkIfSat(Literal literal, Integer delta)
{
  // SAT delta values for the 4 possible cases
  if ((!literal.isNot && literal.isEqual && delta == Integer(0))
      || (literal.isNot && !literal.isEqual && delta > Integer(0))
      || (literal.isNot && literal.isEqual && delta != Integer(0))
      || (!literal.isNot && !literal.isEqual && delta <= Integer(0)))
  {
    return true;
  }
  return false;
}

std::vector<std::tuple<std::vector<Integer>, int, int>>
LocalSearchExtension::getPossibleMoves(bool inDscore)
{
  std::vector<std::tuple<std::vector<Integer>, int, int>> allowedMoves;
  std::set<int> allowedLiterals;
  std::vector<int> allowedVariables;
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
    Literal chosenLiteral = allLiterals[currentLiteralsIdx[literal_idx]];
    AlwaysAssert(chosenLiteral.variables.size() != 0);
    if(chosenLiteral.variables.size() > 100){
      std::vector<int> temp(chosenLiteral.variables.size()) ; // vector with 100 ints.
      allowedVariables = temp;
      std::iota (std::begin(allowedVariables ), std::end(allowedVariables), 0); 
      std::mt19937 rng(std::random_device{}());
      std::shuffle(begin(allowedVariables), end(allowedVariables), rng);
      allowedVariables.resize(100);
    } else {
      std::vector<int> temp(chosenLiteral.variables.size()) ; // vector with 100 ints.
      allowedVariables = temp;
      std::iota (std::begin(allowedVariables ), std::end(allowedVariables), 0); 
    }
    // For all variables in an UNSAT literal compute a potential critical move
    for (int varIdxInLit: allowedVariables)
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


bool LocalSearchExtension::checkBounds(Integer value, int idx){
  if (upperBound[idx].has_value()){
     if (upperBound[idx].value().first > value){
       return false;
     }
  }
  if (equalBound[idx].has_value()){
     if (equalBound[idx].value().first != value){
       return false;
    }
  }
  // x <= 1 -> x =2 bad 
  if (lowerBound[idx].has_value()){
     if (lowerBound[idx].value().first < value){
       return false;
    }
  }
  return true;
}


std::optional<std::vector<std::pair<std::vector<Integer>, int>>>
LocalSearchExtension::criticalMove(int varIdxInLit,
                                   int varIdxInSlv,
                                   Literal literal,
                                   bool inDscore)
{
  Integer delta;
  int direction;
  std::vector<std::pair<std::vector<Integer>, int>> results;
  Integer coef = literal.coefficients[varIdxInLit];
  // case : ==
  if (literal.isEqual && !literal.isNot)
  {
    Integer deltaSum = literal.delta;
    if (coef != 0 && coef.divides(deltaSum))
    {
      delta = getUpperBound(deltaSum, coef);
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
      std::vector<Integer> change1 = variablesValues;
      change1[varIdxInSlv] -= 1;
      if (checkBounds(change1[varIdxInSlv], varIdxInSlv)){
        results.push_back(std::make_pair(change1, 0));
      }
    }
    // If in Dscore all moves are always allowed (we do not check the doNotMove
    // list)
    if (inDscore || doNotMove[2 * varIdxInSlv] <= 0)
    {
      std::vector<Integer> change2 = variablesValues;
      change2[varIdxInSlv] += 1;
      if (checkBounds(change2[varIdxInSlv], varIdxInSlv)) {
        results.push_back(std::make_pair(change2, 1));
      }
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
    delta = getUpperBound(literal.delta.abs(), coef.abs());
    if (coef < 0) delta *= Integer(-1);
    // case: not >=
  }
  else
  {
    delta = getUpperBound((Integer(1) - literal.delta).abs(), coef.abs());
    if (coef > 0) delta *= Integer(-1);
  }
  if (delta == 0)
  {
    // delta should never be zero
    AlwaysAssert(false);
  }
  AlwaysAssert(delta != 0);
  direction = delta > 0 ? 0 : 1;
  // Check that we have not moved the variable in the opposite direction in less
  // than allowed num of iterations if we have no critical move can be preformed
  if (!inDscore && doNotMove[2 * varIdxInSlv + (direction ^ 1)] > 0)
  {
    return std::nullopt;
  }
  std::vector<Integer> change = variablesValues;
  change[varIdxInSlv] -= delta;
  if (checkBounds(change[varIdxInSlv], varIdxInSlv)) {
  results.push_back(std::make_pair(change, direction));
  return results;
  }
  else {
    return std::nullopt;
  }
}

int LocalSearchExtension::computeScore(std::vector<Integer> change, int varIdx)
{
  // score: how many new SAT clauses we get from a new assignment -
  // new UNSAT clauses we get from a new assignment
  int score = 0;
  for (int literalIdx : variablesToLiterals[varIdx])
  {
    Literal literal = allLiterals[currentLiteralsIdx[literalIdx]];
    Integer newDelta = literal.calculateDelta(change);
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

Integer LocalSearchExtension::computeDistanceScore(Literal literal,
                                                   std::vector<Integer> change,
                                                   int varIdx)
{
  // Distance score: how far away we are from being SAT. If SAT distance is zero
  // case >=
  if (!literal.isEqual && !literal.isNot)
  {
    return Integer::max(literal.calculateDelta(change), 0) * literal.weight;

    // case ==
  }
  else if (literal.isEqual && !literal.isNot)
  {
    Integer delta = literal.calculateDelta(change);
    if (delta < 1)
    {
      delta = delta * -1;
    }
    return Integer::max(delta, 0) * literal.weight;

    // case not >=
  }
  else if (!literal.isEqual && literal.isNot)
  {
    return Integer(-1)
           * Integer::min(literal.calculateDelta(change) - Integer(1), 0)
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

int LocalSearchExtension::stepForward(std::vector<Integer> change,
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
    Literal literal = allLiterals[currentLiteralsIdx[literal_idx]];
    Integer oldDelta = literal.delta;
    bool oldSat = checkIfSat(literal, oldDelta);
    allLiterals[currentLiteralsIdx[literal_idx]].delta = allLiterals[currentLiteralsIdx[literal_idx]].calculateDelta(change);
    bool newSat =
        checkIfSat(allLiterals[currentLiteralsIdx[literal_idx]], allLiterals[currentLiteralsIdx[literal_idx]].delta);
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
    Assert(false);
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
  for (int idx : currentLiteralsIdx)
  {
    Literal literal = allLiterals[idx];
    if (!checkIfSat(literal, literal.calculateDelta(variablesValues)))
    {
      literal.printAllocation();
      printChange(variablesValues);
      return false;
    }
  }
  return true;
}

void LocalSearchExtension::restart()
{
  std::vector<int> tempVec(variablesValues.size() * 2 + 1, 0);
  doNotMove = tempVec;
  std::vector<Integer> tempVec2(variablesValues.size(), Integer(0));
  variablesValues = tempVec2;
  for (int i=0; i<variablesValues.size(); i++){
    if (upperBound[i].has_value()){
      variablesValues[i] = upperBound[i].value().first;
    }
    if (lowerBound[i].has_value()){
      variablesValues[i] = lowerBound[i].value().first;
    }
    if (equalBound[i].has_value()){
      variablesValues[i] = equalBound[i].value().first;
    }
  }
  unsatLiterals = std::set<int>();
  for (int i = 0; i < currentLiteralsIdx.size(); i++)
  {
    // recompute the deltas with the initial assignment and set weights back to
    // 1
    allLiterals[currentLiteralsIdx[i]].delta = allLiterals[currentLiteralsIdx[i]].calculateDelta(variablesValues);
    allLiterals[currentLiteralsIdx[i]].weight = 1;
    if (!checkIfSat(allLiterals[currentLiteralsIdx[i]], allLiterals[currentLiteralsIdx[i]].delta))
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
      allLiterals[currentLiteralsIdx[i]].weight += 2;
    }
    for (int i = 0; i < currentLiteralsIdx.size(); i++)
    {
      if (allLiterals[currentLiteralsIdx[i]].weight > 1)
      {
        allLiterals[currentLiteralsIdx[i]].weight -= 1;
      }
    }
  }
  // If not smoothing just increase unsatisfied by 1
  else
  {
    for (int const& i : unsatLiterals)
    {
      allLiterals[currentLiteralsIdx[i]].weight += 1;
    }
  }
}


bool LocalSearchExtension::LocalSearch()
{
 if (ConflictFound == true){
     return false;
  }
  // for (int i = 0; i < variablesValues.size(); i++ ){
  //   if (upperBound[i].has_value() && lowerBound[i].has_value() && upperBound[i].value().first > lowerBound[i].value().first){
  //     dls_conflict.push_back(d_facts[upperBound[i].value().second]);
  //     dls_conflict.push_back(d_facts[upperBound[i].value().second]);
  //     ConflictFound = true;
  //     return false;
  //   }
  // }
  std::random_device rd;
    
    // Choose a random number between 1 and 10000 as part of the file name
  std::default_random_engine eng(rd());
  std::uniform_int_distribution<int> distr(1, 10000);
  int random_number = distr(eng);
    
    // Generate a random file name
  // std::string filename = "~/Documents/WINTER2024/fake/cvc5/expr/file_" + std::to_string(random_number) + ".txt";
  // std::cout << "Created file" << filename << "\n";

  // myFile = filename;
  // std::ofstream file(myFile);
  // std::cout << myFile << "\n";
  // std::cout << "Current Assertions:" << currentLiteralsIdx.size() << "\n";
  // std::cout << "Total Assertions:" << totalAsserts << "\n";
  // First attempt at detecting a conflict 
  // Initialize doNotMove and random generator
  std::vector<int> tempVec(variablesValues.size() * 2 + 1, 0);
  doNotMove = tempVec;
  //std::random_device rd;
  std::mt19937 gen(rd());
  rd_generator = gen;
  //rd_generator.seed(1);
  std::uniform_int_distribution<> tempDistribution(0, 10);
  doNotMoveDistribution = tempDistribution;
  int satScore = currentLiteralsIdx.size() - unsatLiterals.size();
  int bestScore = satScore;
  Integer bestScoreInteger;
  int restartCount = 0;
  nonImprove = 0;
  int oldUnsat = unsatLiterals.size();
  // This should be a heuristic in the future
  while (restartCount < 2)
  {
    //std::cout << unsatLiterals.size() << "\n";
    //file << unsatLiterals.size() << std::endl;
    //printUnsat();
    // If a solution has been found
    if (unsatLiterals.size() == 0)
    {
      // Check that all literals are SAT
      if (!checkIfSolutionSat())
      {
        AlwaysAssert(false);
      }
      //printChange(variablesValues);
      //file.close();
      return true;
    } else {
      for (const int& val : unsatLiterals) {
        idxToCount[val] +=1;
    }
    }
    // First try computing a decreasing change using regular score
    std::vector<std::tuple<std::vector<Integer>, int, int>> possibleMoves =
        getPossibleMoves(false);
    int bestDirection;
    std::vector<Integer> bestChange;
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
      bestScoreInteger = Integer(std::numeric_limits<int>::max());
      std::vector<std::tuple<std::vector<Integer>, int, int>> newPossibleMoves =
          getPossibleMoves(true);
      for (auto move : newPossibleMoves)
      {
        auto change = std::get<0>(move);
        int direction = std::get<1>(move);
        int varIdxInSlv = std::get<2>(move);
        Integer score = 0;
        for (int literal_idx : variablesToLiterals[varIdxInSlv])
        {
          Literal literal = allLiterals[currentLiteralsIdx[literal_idx]];
          score +=
              (computeDistanceScore(literal, change, varIdxInSlv)
               - computeDistanceScore(literal, variablesValues, varIdxInSlv));
        }
        // Best distance score is that which minimizes distance to SAT compared
        // to current assignment
        if (score < bestScoreInteger
            || (score == bestScore
                && doNotMove[2 * varIdxInSlv + direction ^ 1]
                       < doNotMove[2 * bestVarIdx + bestDirection ^ 1]))
        {
          decreasingChangeExists = true;
          bestDirection = direction;
          bestVarIdx = varIdxInSlv;
          bestScoreInteger = score;
          bestChange = change;
        }
      }
    }
    //std::cout << "WE GOT HERE!\n";
    if (!decreasingChangeExists)
    {
      //std::cout << "No CHANGE\n";
      nonImprove = MAXNONIMPROVE + 1;
    }
    else
    {
      // Change assignment
      satScore += stepForward(bestChange, bestVarIdx, bestDirection);
      bestScore = satScore;
      nonImprove += 1;
    }
    if (nonImprove > MAXNONIMPROVE)
    {
      if (restartCount == MAXRESTARTCOUNT){

        return false;
      }
      restartCount +=1;
      restart();
      satScore = currentLiteralsIdx.size() - unsatLiterals.size();
      bestScore = satScore;
    }
  }
}

std::vector<std::tuple<TNode, bool, TNode>> LocalSearchExtension::conflict(){
  AlwaysAssert(idxToCount.size() == d_facts.size());
  // if (ConflictFound){
  //   return dls_conflict;
  // };
  // std::vector<Node> d_conflict;
  // std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
  // return d_conflict;
  // No explicit conflict has been then sort the conflicts 
  std::cout << "IDXTOCOUNDSIZE" << idxToCount.size() << "\n";
  std::cout << "Asserts" << totalAsserts << "\n";
   std::cout << "facts SIZE:" << d_facts.size() << "\n";



  std::vector<std::pair<int, int>> vec(idxToCount.begin(), idxToCount.end());


  // // Sort the vector by value using a custom comparator
  std::sort(vec.begin(), vec.end(), [](const std::pair<int, int>& a, const std::pair<int, int>& b) {
       return a.second < b.second; // Compare by value
   });

   int total = std::accumulate(vec.begin(), vec.end(), 0, [](int acc, const std::pair<int, int>& pair) {
        return acc + pair.second;
   });
  
   mean = static_cast<int>(total) / vec.size();

   orderedCount = vec;

   for (const auto& pair : orderedCount) {
         if (pair.second >= mean) {
             dls_conflict.push_back(d_facts[pair.first]);
        }
     }
    // for (const int idx: d_Bounds){
    //   dls_conflict.push_back(d_facts[idx]);
    // }
  std:: cout << mean << "\n";
  sentSmartConflict = true;
  std::cout << "SMART CONFLICT SIZE:" << dls_conflict.size() << "\n";
  
  return dls_conflict;

}

std::vector<std::tuple<TNode, bool, TNode>> LocalSearchExtension::getTrivialConflict(bool lookedAtSmart){
  std::vector<std::pair<int, int>> vec(idxToCount.begin(), idxToCount.end());
  std::sort(vec.begin(), vec.end(), [](const std::pair<int, int>& a, const std::pair<int, int>& b) {
       return a.second < b.second; // Compare by value
   });
  orderedCount = vec;

  // for (auto pair: orderedCount) {
  //   std::cout << "(" << pair.first << "," << pair.second << ")" << ", ";
  // }
  // std::cout <<"\n";

  if (!sentSmartConflict || !lookedAtSmart) {
    dls_conflict.clear();
    for( auto&i: orderedCount){
      dls_conflict.push_back(d_facts[i.first]);
    }
    //std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(dls_conflict));
    AlwaysAssert(dls_conflict.size() == d_facts.size());
    return dls_conflict;
  }
 else {
    dls_conflict.clear();
    std:: cout << mean << "\n";
    for (const auto& pair : orderedCount) {
         if (pair.second < mean) {
             dls_conflict.push_back(d_facts[pair.first]);
        }
     }
    // for (const int idx: d_Bounds){
    //   dls_conflict.push_back(d_facts[idx]);
    // }
    std::cout << "Other CONFLICT SIZE:" << dls_conflict.size() << "\n";

    std::cout << "facts SIZE:" << d_facts.size() << "\n";
    return dls_conflict;

  }
}

}  // namespace local_search
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
