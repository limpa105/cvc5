/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__IDL__IDL_EXTENSION_H
#define CVC5__THEORY__ARITH__IDL__IDL_EXTENSION_H

#include "context/cdlist.h"
#include "smt/env_obj.h"
#include "theory/skolem_lemma.h"
#include "theory/theory.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class TheoryArith;

namespace idl {

class Literal {
 public:
  /** Parse one side of the literal AST **/
  void parseOneSide(internal::TNode &side, Literal &literal); // parses one side of AST 

  /** Calculate LHS - RHS **/
  int calculateDelta(std::vector<int>& assignment);  // calculates LHS - RHS

  /** Coefficients of the literal: 1x+2y <=3 -> [1,2] */
  std::vector<int> coefficients; 

  /** Index of variables in solvers's current assignment in the order they appear 
   * in the literal **/
  std::vector<int> variables;  // variables based on their index stored in the solver 

  /** Constants present in the equation **/
  int threshold; 

  /** LHS - RHS **/
  int delta;  

  /** true if literal is negated false otherwise **/ 
  bool isFalse = false ;

  /** true if literal is == and false if it is >= 
   * (this is needed as rewrites for == can result in
   *  getting stuck in a local optima ) **/ 
  bool isEqual = false; 
};

class IdlExtension : protected EnvObj
{

 public:

  /** A list all parsed literals **/
  std::vector<Literal> literals; 

  /** Current assignment of the search **/
  std::vector<int> variableValues; 

  /** A set of idx of the unsat literals under current assignment **/
  std::set<int> unsatLiterals;

  /** ith entry is the set of literals that ith variable in
   * VariablesValues is present */ 
  std::vector<std::set<int>> variablesToLiterals;

  /** A map of variable name to its index in values **/
  std::map<std::string, int> nameToIdx;


  IdlExtension(Env& env, TheoryArith& parent);
  ~IdlExtension();

  /** Register a term that is in the formula */
  void preRegisterTerm(TNode);

  /** Set up the solving data structures */
  void presolve();

  /** Called for each asserted literal */
  void notifyFact(
      TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal);

  /** Pre-processing of input atoms */
  Node ppStaticRewrite(TNode atom);

  /** Check for conflicts in the current facts */
  void postCheck(Theory::Effort level);

  /** Get all information regarding the current model */
  bool collectModelInfo(TheoryModel* m, const std::set<Node>& termSet);

 private:

  /** Process a new assertion */
  void processAssertion(TNode assertion);

  /** Return true iff the graph has a negative cycle */
  bool negativeCycle();

  /** Print the matrix */
  void printMatrix(const std::vector<std::vector<Rational>>& matrix,
                   const std::vector<std::vector<bool>>& valid);

  typedef context::CDHashMap<TNode, size_t> TNodeToUnsignedCDMap;

  /** The owner of this extension */
  TheoryArith& d_parent;

  /** Map from variables to the first element of their list */
  TNodeToUnsignedCDMap d_varMap;

  /** Context-dependent vector of variables */
  context::CDList<TNode> d_varList;

  /** Context-dependent list of asserted theory literals */
  context::CDList<TNode> d_facts;

  /** i,jth entry is true iff there is an edge from i to j. */
  std::vector<std::vector<bool>> d_valid;

  /** i,jth entry stores weight for edge from i to j. */
  std::vector<std::vector<Rational>> d_matrix;

  /** Number of variables in the graph */
  size_t d_numVars;
}; /* class IdlExtension */

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
