/******************************************************************************
 * Top contributors (to current version):
 *  Elizaveta Pertseva
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Local Search extension based on https://arxiv.org/pdf/2211.10219.pdf
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__IDL__IDL_EXTENSION_H
#define CVC5__THEORY__ARITH__IDL__IDL_EXTENSION_H

#include <iostream>
#include <random>
#include <unordered_map>

#include "context/cdlist.h"
#include "smt/env_obj.h"
#include "theory/skolem_lemma.h"
#include "theory/theory.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class TheoryArith;

namespace local_search {

class Literal
{
 public:
  /** Coefficients of the literal: 1x+2y <=3 -> [1,2] */
  std::vector<Integer> coefficients;

  /** Index of variables in solvers's current assignment in the order they
   * appear in the literal **/
  std::vector<int> variables;

  /** Constants present in the equation **/
  Integer threshold = Integer(0);

  /** LHS - RHS **/
  Integer delta;

  /** true if literal is negated false otherwise **/
  bool isNot = false;

  /** true if literal is == and false if it is >=
   * (this is needed as rewrites for == can result in
   *  getting stuck in a local optima ) **/
  bool isEqual = false;

  /** weight of the score **/
  int weight = 1;

  /** The equation of the literal (stored for debugging) **/
  TNode equation;

  /** Calculate LHS - RHS **/
  Integer calculateDelta(
      std::vector<Integer>& assignment);  // calculates LHS - RHS

  /** Prints current internal data structures **/
  void printAllocation();
};

class LocalSearchExtension : protected EnvObj
{
 public:

  bool foundASolution = false;

  LocalSearchExtension(Env& env, TheoryArith& parent);
  ~LocalSearchExtension();

  /** Register a term that is in the formula */
  void preRegisterTerm(TNode);

  std::vector<std::tuple<TNode, bool, TNode>> conflict();

  std::vector<std::tuple<TNode, bool, TNode>> getTrivialConflict();

  /** Set up the solving data structures */
  void presolve();

  /** Called for each asserted literal */
  void notifyFact(
      TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal);

  /** Pre-processing of input atoms */
  Node ppStaticRewrite(TNode atom);

  /** Check for conflicts in the current facts. 
   * Returns true if conflicts have been found
  */
  bool postCheck(Theory::Effort level);

  /** Get all information regarding the current model */
  bool collectModelInfo(TheoryModel* m, const std::set<Node>& termSet);

  std::vector<std::tuple<TNode, bool, TNode>> dls_conflict;

 private:
  /** -------------------------------------------------------------
   * The variables below are inherited from IDL Extension  */
  typedef context::CDHashMap<TNode, size_t> TNodeToUnsignedCDMap;

  bool ConflictFound; 

  std::unordered_map<int, int> idxToMainIdx;

  std::map<int, int> idxToCount;
  /** The owner of this extension */
  TheoryArith& d_parent;

  /** Map from variables to the first element of their list */
  TNodeToUnsignedCDMap d_varMap;

  /** Context-dependent vector of variables */
  context::CDList<TNode> d_varList;

  /** Context-dependent list of asserted theory literals */
  context::CDList<std::tuple<TNode, bool, TNode>> d_facts;

  /** i,jth entry is true iff there is an edge from i to j. */
  std::vector<std::vector<bool>> d_valid;

  /** Number of variables in the graph */
  size_t d_numVars;
  /** ---------------------------------------------------------------- **/

  /** Parameter after how many iterations should one restart*/
  const int MAXNONIMPROVE = 100000;

  const int MAXRESTARTCOUNT = 1;

  /** Number of literals to consider when in Distance Score*/
  const int NUMLITCONSIDER = 3;

  /** Smallest number of iterations that we do not change the variable after
   * changing it once */
  const int DONOTMOVECONST = 3;

  float SMOOTHING = 0.0003;

  /** Random number generator **/
  std::mt19937 rd_generator;

  /** A list of current parsed literals **/
  std::vector<int> currentLiteralsIdx;

  /** A list of ALL literals in the problem **/
  std::vector<Literal> allLiterals;

  std::map<uint64_t, int> idToIdxLiteral;


  /** Current assignment of the search **/
  std::vector<Integer> variablesValues;

  int totalAsserts = 0;

  int processedAsserts = 0;

  bool checkBounds(Integer Value, int idx);

  /** A set of idx of the unsat literals under current assignment **/
  std::set<int> unsatLiterals;

  std::string myFile;

  /** ith entry is the set of literals that ith variable in
   * variablesValues is present */
  std::vector<std::set<int>> variablesToLiterals;

  /** A map of variable name to its index in values **/
  std::map<std::string, int> nameToIdx;


  /** A list of indexes that cannot be moved as they
   *  were moved < n iterations ago **/
  std::vector<int> doNotMove;

  std::vector<int> d_Bounds;

  std::vector<std::optional<std::pair<Integer,int>>> upperBound;

  std::vector<std::optional<std::pair<Integer,int>>>  lowerBound;

  std::vector<std::optional<std::pair<Integer,int>>>  equalBound;


  /** Number of iterations since last restart **/
  int nonImprove = 0;

  /** Distribution from which to randomly select for how many steps
   * we can't increment/decrement the variable **/
  std::uniform_int_distribution<> doNotMoveDistribution;

  /** Helper function to sample from a set with replacement **/
  std::set<int> sampleWithReplacement(const std::set<int>& originalSet,
                                      int sampleSize);



  /** Helper function to get custom upperbound when dividing a by b
   * ex a/b=- -1.5 -> -2 || a/b = 1.5 ->2 **/
  Integer getUpperBound(Integer a, Integer b);

  /** Helper function to print a set **/
  void printSet(std::set<int> mySet, std::string name);

  /** Prints the Unsat literals **/
  void printUnsat();

  /** Prints a potential change **/
  void printChange(std::vector<Integer> change);

  /** Add a literal to the LS solver **/
  //void addLiteral(Literal literal) { literals.push_back(literal); }

  /** Process a new assertion into the local data structures */
  void processAssertion(TNode assertion, int MainIndx);

  /** Parse one side of the literal AST **/
  void parseOneSide(internal::TNode& side, Literal& literal);

  /** Checks if a Literal is SAT **/
  bool checkIfSat(Literal literal, Integer delta);

  /** get allowed critical moves at the current point in the search **/
  std::vector<std::tuple<std::vector<Integer>, int, int>> getPossibleMoves(
      bool inDscore);

  /** Computes a critical move for a variable based on its position in a literal
   * Params:
   * varIdxInLit: variables position in literal.variables
   * varIdxInSlv: variables position in slv.variables
   * literal: the selected unsat literal
   * inDscore: if we are in regular mode or in distance score
   * Returns:
   * vector<int> : possible new assignment
   * int: direction of change
   * none -> if no moves are allowed **/
  std::optional<std::vector<std::pair<std::vector<Integer>, int>>> criticalMove(
      int varIdxInLit, int varIdxInSlv, Literal literal, bool inDscore);

  /** Computes score of a potential assignment change **/
  int computeScore(std::vector<Integer> change, int varIdx);

  /** Computes distance score of a potential assignment change (how far away it
   * is from truth)**/
  Integer computeDistanceScore(Literal literal,
                               std::vector<Integer> change,
                               int varIdx);

  /** Step forward in the LS by switching the assignment to a new one **/
  int stepForward(std::vector<Integer> change, int varIdx, int direction);

  /** Safety check to make sure the solution is SAT **/
  bool checkIfSolutionSat();

  /** Restarts local search **/
  void restart();

  /** Recalculates the weight of the clauses according to the PAWS scheme **/
  void applyPAWS();

  /** Main driver function of Local Search **/
  bool LocalSearch();

}; /* class localSearchExtension */

}  // namespace local_search
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
