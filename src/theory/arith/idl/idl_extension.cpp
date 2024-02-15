/******************************************************************************
 * Top contributors (to current version):
 *   Liza Pertseva 
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * IDL extension.
 */

#include "theory/arith/idl/idl_extension.h"

#include <iomanip>
#include <queue>
#include <set>
#include <vector>

#include "expr/node_builder.h"
#include "theory/arith/theory_arith.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace idl {

IdlExtension::IdlExtension(Env& env, TheoryArith& parent)
    : EnvObj(env),
      d_parent(parent),
      d_varMap(context()),
      d_varList(context()),
      d_facts(context()),
      d_numVars(0)
{
}

IdlExtension::~IdlExtension() {
}

void IdlExtension::preRegisterTerm(TNode node)
{
  if (node.isVar() && node.hasName()){
      int current_idx = variableValues.size();
      nameToIdx[node.getName()] = current_idx;
      // all variables start at 0 
      // TODO: Future implementation if variable has bounds start 
      // at those bounds 
      variableValues.push_back(0);
      // at the start no variable is present in any literal
      variablesToLiterals.push_back(std::set<int>());
  }
    
}

void IdlExtension::presolve()
{
  // In current implementation there is nothing to presolve as all
  // data structures are set up  when we process assertion but this is an
  // ineffective way to do this and will need to change in future
  return;
}


void IdlExtension::notifyFact(
  // I don't understand what this method is doing 
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Trace("theory::arith::idl")
      << "IdlExtension::notifyFact(): processing " << fact << std::endl;
  d_facts.push_back(fact);
}

Node IdlExtension::ppStaticRewrite(TNode atom)
{
  // In current implementation there is nothing to rewrite as all rewrites happen 
  // when setting up data structures but this might change in future implementations
  return atom;
}

void IdlExtension::postCheck(Theory::Effort level)
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

  // Currently does not return conflict but will be implemented in future versions 
  // Right now in case of UNSAT it will not terminate 
}

bool IdlExtension::collectModelInfo(TheoryModel* m,
                                    const std::set<Node>& termSet)
{
  std::vector<Rational> distance(d_numVars, Rational(0));

  int num_edges = d_matrix.size();

  for (int k=0; k<num_edges-1; ++k){
    for (int i = 0; i<num_edges; ++i){
      for(int j =0; j<num_edges; ++j){
        //std::cout << d_matrix[i][j] << "";
        if (d_valid[i][j] && distance[j] > distance[i] + d_matrix[i][j]){
          distance[j] = distance[i] + d_matrix[i][j];
        }
      }
    }
  }

  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 0; i < d_numVars; i++)
  {
    // Assert that the variable's value is equal to its distance in the model
    m->assertEquality(d_varList[i], nm->mkConstInt(distance[i]), true);
  }

  return true;
}

void IdlExtension::processAssertion(TNode assertion)
{
  bool polarity = assertion.getKind() != Kind::NOT;
  TNode atom = polarity ? assertion : assertion[0];
  Assert(atom.getKind() == Kind::LEQ);
  std::cout << atom[0].getKind();
  Assert(atom[0].getKind() == Kind::SUB);
  TNode var1 = atom[0][0];
  TNode var2 = atom[0][1];

  Rational value = (atom[1].getKind() == Kind::NEG)
                       ? -atom[1][0].getConst<Rational>()
                       : atom[1].getConst<Rational>();

  if (!polarity)
  {
    std::swap(var1, var2);
    value = -value - Rational(1);
  }

  size_t index1 = d_varMap[var1];
  size_t index2 = d_varMap[var2];

  if (!d_valid[index1][index2] || value < d_matrix[index1][index2])
  {
    d_valid[index1][index2] = true;
    d_matrix[index1][index2] = value;
  }
}

bool IdlExtension::negativeCycle()
{
  int INF= 1e7;
  int num_edges = d_matrix.size();
  std::vector<int> distance(num_edges, INF);
  distance[0] = 0;
  for (int k=0; k<num_edges-1; ++k){
    for (int i = 0; i<num_edges; ++i){
      for(int j =0; j<num_edges; ++j){
        //std::cout << d_matrix[i][j] << "";
        if (d_valid[i][j] && distance[j] > distance[i] + d_matrix[i][j].getDouble()){
          distance[j] = distance[i] + d_matrix[i][j].getDouble();
        }
      }
    }
  }
   for (int i = 0; i<num_edges; ++i){
      for(int j =0; j<num_edges; ++j){
        if (d_valid[i][j] && distance[j]> distance[i] + d_matrix[i][j].getDouble())
          return true;
    };
   };

  // --------------------------------------------------------------------------
  // TODO: write the code to detect a negative cycle.
  // --------------------------------------------------------------------------

  return false;
};

void IdlExtension::printMatrix(const std::vector<std::vector<Rational>>& matrix,
                               const std::vector<std::vector<bool>>& valid)
{
  std::cout << "      ";
  for (size_t j = 0; j < d_numVars; ++j)
  {
    std::cout << std::setw(6) << d_varList[j];
  }
  std::cout << std::endl;
  for (size_t i = 0; i < d_numVars; ++i)
  {
    std::cout << std::setw(6) << d_varList[i];
    for (size_t j = 0; j < d_numVars; ++j)
    {
      if (valid[i][j])
      {
        std::cout << std::setw(6) << matrix[i][j];
      }
      else
      {
        std::cout << std::setw(6) << "oo";
      }
    }
    std::cout << std::endl;
  }
}

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
