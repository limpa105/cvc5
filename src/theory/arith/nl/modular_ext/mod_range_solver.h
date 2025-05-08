/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for pow2 constraints.
 */

#ifndef CVC5__THEORY__ARITH__NL__MODEXT__MOD_RANGE_SOLVER_H
#define CVC5__THEORY__ARITH__NL__MODEXT__MOD_RANGE_SOLVER_H

#include <vector>

#include "theory/arith/nl/modular_ext/bounds.h"
#include "theory/arith/nl/modular_ext/integer_ring.h"
#include "theory/arith/nl/modular_ext/modular_ring.h"
#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/arith/inference_manager.h"

namespace cvc5::internal {
namespace theory {
namespace arith {


namespace nl {

/** pow2 solver class
 *
 */
class ModRangeSolver : protected EnvObj
{
 public:
  ModRangeSolver(Env& env, InferenceManager& im);
  ~ModRangeSolver();

  void initLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts);


  void preRegisterTerm(Node n);




 private:

  bool failedOnce = false;
  // The inference manager that we push conflicts and lemmas to.
  InferenceManager& d_im;

   /**
  * Facts, in notification order.
  */
  context::CDList<Node> d_facts;

  /**
  * IntegerRing corresponding to the solver.
  */
  IntegerRing myIntegerRing;

    /**
    * ModularRings corresponding to the solver.
     */
  std::map<Integer, std::unique_ptr<ModularRing>> myModularRings;

    /**
    * Map from each variable to its lower and upper bounds.
    */
  std::map<std::string, std::pair<Bound, Bound>> bounds;

  std::vector<Node> myVariables;

  /**
  * Prints out the state of the solver (rings, elements in rings & bounds)
  * for debugging purposes
  */
  void printSystemState();

  void processFact(Node node);

  std::map<Node,Node> tempSkolemMap;

  /**
  * Set the conflict to be all facts.
  */
  void setTrivialConflict();

}; /* class ModRangeSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__POW2_SOLVER_H */