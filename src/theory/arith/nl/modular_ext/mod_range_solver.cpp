/******************************************************************************
 * Top contributors (to current version):
 *   Elizaveta Pertseva,
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of modRange solver.
 */

#include "theory/arith/nl/modular_ext/mod_range_solver.h"
#include "theory/arith/nl/modular_ext/bounds.h"
#include "theory/arith/nl/modular_ext/integer_ring.h"
#include "theory/arith/nl/modular_ext/modular_ring.h"
#include "theory/arith/nl/modular_ext/ring.h"
#include "theory/rewriter.h"
#include "theory/arith/nl/modular_ext/utils.h"
#include "util/integer.h"
#include "util/rational.h"
#include "expr/skolem_manager.h"


using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {




ModRangeSolver::ModRangeSolver(Env& env,
                       InferenceManager& im)
    : EnvObj(env),
    d_im(im), 
    d_facts(context()),
    myIntegerRing(env)
{
}

bool ModRangeSolver::traverseOriginEq(
  std::vector<EqOrigin>& eqs,
  const std::vector<Node>& assertions,
  std::vector<Node>& result,
  std::set<int>& visited_gbs,
  Ring F
) {
  for (const auto& origin : eqs) {
    if (origin.value == -1) {
      return false; // early termination
    }

    if (origin.gb == 0) {
      result.push_back(assertions[origin.value]);
    } else {
      if (visited_gbs.count(origin.gb)) {
        continue; // already visited this GB
      }
      visited_gbs.insert(origin.gb);

      auto it = F.pastGbs.find(origin.gb);
      if (it == F.pastGbs.end()) {
        return false; // GB not found
      }

      if (!traverseOriginEq(it->second, assertions, result, visited_gbs, F)) {
        return false; // recursive failure
      }
    }
  }
  return true;
}

std::vector<Node> ModRangeSolver::collectCores(
  const std::vector<Node>& assertions,
  Ring F
) {
  std::vector<Node> result;
  std::set<int> globally_visited;

  if (!traverseOriginEq(F.origin_eq, assertions, result, globally_visited, F)) {
    return {};
  }

  return result;
}


ModRangeSolver::~ModRangeSolver() {}

void ModRangeSolver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  if (failedOnce){
    for (auto& as: false_asserts){
    //std::cout << as << "\n";
     d_im.lemma(nodeManager()->mkNode(Kind::EQUAL, replaceMMMod(as, nodeManager())[0], as[0]), InferenceId::ARITH_NL_MOD_RANGE_SOLVER);
    }
    return;
  }
  // CLEAR STATE HERE 
  for (auto &pair: myModularRings){
    pair.second->clearState();
  }
  myIntegerRing.clearState();
  for (auto &bd: bounds){
    bd.second =  std::make_pair(Bound::negativeInfinity(), Bound::positiveInfinity());
  };
  for(int i =0; i< assertions.size(); i++){
      processFact(assertions[i], EqOrigin{i, 0});
  }
  for (const auto& [name, boundPair] : bounds)
    {
      const Bound& lower = boundPair.first;
      const Bound& upper = boundPair.second;

      if (upper < lower)
      {
        Trace("mod-range-solver") << "o.g bds unsat" << std::endl;
         d_im.lemma(nodeManager()->mkNode(Kind::NOT, nodeManager()->mkNode(Kind::AND, assertions)), InferenceId::ARITH_NL_MOD_RANGE_SOLVER);
         return;

      }
    }
  int count = 0;
  bool infoToLearn = true;
  Trace("mod-range-solver") << "Started solving " << std::endl;
  printSystemState();
  for (auto &pair: myModularRings){
    pair.second->allEqsOg = true;
  }
  myIntegerRing.allEqsOg = true;
  while(infoToLearn){
    infoToLearn = false;
    count +=1;
    // First we look at the fields:
    Trace("mod-range-solver") << "lifting" << std::endl;
    for (auto &pair: myModularRings){
      // 1) Lift
      for (Node &eq: pair.second->equalities){
        if (checkIfConstraintIsMet(eq, pair.second->modulus, bounds)){
            if(myIntegerRing.reduceAddEquality(eq, EqOrigin{-1,-1})){
              infoToLearn = true;
            };
        }
        }
       for (int i = pair.second->DiseqMoved; i < pair.second->disequalities.size(); i++){
          Node diseq = pair.second->disequalities[i];
          if(myIntegerRing.AddDisquality(diseq, pair.second->origin_diseq[i])){
            infoToLearn = true;
          };
       }
       pair.second->DiseqMoved = pair.second->disequalities.size();
       // 2) Compute GB
       if(pair.second->computeGB() == Result::UNSAT){
        //std::cout << "UNSAT" << "\n";
        Trace("mod-range-solver") << "returned unsat field gb" << std::endl;
        d_im.lemma(nodeManager()->mkNode(Kind::NOT, nodeManager()->mkNode(Kind::AND, assertions)), InferenceId::ARITH_NL_MOD_RANGE_SOLVER);
        return;
       }
       // 3) Reduce Diseq
       if(pair.second->checkDiseq() == Result::UNSAT){
        Trace("mod-range-solver") << "returned unsat field diseq" << std::endl;
        d_im.lemma(nodeManager()->mkNode(Kind::NOT, nodeManager()->mkNode(Kind::AND, assertions)), InferenceId::ARITH_NL_MOD_RANGE_SOLVER);
        return;
       }
       
    }
    //printSystemState();
    // Then we look at the integers 
    // 0) Tighten bounds
    Trace("mod-range-solver") << "tightening bounds" << std::endl;
    if (myIntegerRing.tightenBounds(bounds) == Result::UNSAT){
       Trace("mod-range-solver") << "returned unsat bounds" << std::endl;
        d_im.lemma(nodeManager()->mkNode(Kind::NOT, nodeManager()->mkNode(Kind::AND, assertions)), InferenceId::ARITH_NL_MOD_RANGE_SOLVER);
        return;

    };
    // 1) Lower
    Trace("mod-range-solver") << "lowering" << std::endl;
    for (int i = myIntegerRing.EqsMoved; i< myIntegerRing.equalities.size(); i++){
      for (auto &pair: myModularRings){
        Node eq = myIntegerRing.equalities[i];
        if (pair.second->reduceAddEquality(eq, myIntegerRing.origin_eq[i])){
          infoToLearn = true;
        };
      }
    }
    myIntegerRing.EqsMoved = myIntegerRing.equalities.size();
    for (auto &diseq: myIntegerRing.disequalities){
      for (auto &pair: myModularRings){
        if (checkIfConstraintIsMet(diseq, pair.second->modulus, bounds, true)){
          if(pair.second->AddDisquality(diseq, -1)){
            infoToLearn = true;
          };
        }
      }
    }
    // 2) Compute GB
    if(myIntegerRing.computeGB(myVariables, bounds) == Result::UNSAT){
        Trace("mod-range-solver") << "returned unsat int gb" << std::endl;
        d_im.lemma(nodeManager()->mkNode(Kind::NOT, nodeManager()->mkNode(Kind::AND, assertions)), InferenceId::ARITH_NL_MOD_RANGE_SOLVER);
         return;
       }
    // 3) Reduce Diseq
     if(myIntegerRing.checkDiseq() == Result::UNSAT){
        Trace("mod-range-solver") << "returned unsat int diseq" << std::endl;
        printSystemState();
        std::vector<Node> result = collectCores(assertions, myIntegerRing);
        for (int k = 0; k< result.size(); k++){
          std::cout << "Assertion" << k << "\n";
        }
        d_im.lemma(nodeManager()->mkNode(Kind::NOT, nodeManager()->mkNode(Kind::AND, assertions)), InferenceId::ARITH_NL_MOD_RANGE_SOLVER);
        return;
       }
  }

  Trace("mod-range-solver") << "returned unknown" << std::endl;
  failedOnce = true;
  printSystemState();
  //AlwaysAssert(false);
  for (auto& as: false_asserts){
    //std::cout << as << "\n";
     d_im.lemma(nodeManager()->mkNode(Kind::EQUAL, replaceMMMod(as, nodeManager())[0], as[0]), InferenceId::ARITH_NL_MOD_RANGE_SOLVER);
  }    
};

void ModRangeSolver::preRegisterTerm(Node node){
    if (isVariableOrSkolem(node)){
          bounds[node.getName()] = std::make_pair(Bound::negativeInfinity(), Bound::positiveInfinity());
          myVariables.push_back(node);
    }
    if (node.getKind() == Kind::CONST_INTEGER){
        Integer constant = node.getConst<Rational>().getNumerator();
        if (constant < 0){constant = constant * -1;};
        // Do not create moduli for 0 or 1
        if (constant == 0 || constant == 1 ){
            return;
        }
        if (myModularRings.count(constant)==0){
            myModularRings[constant] =  std::make_unique<ModularRing>(d_env, constant);
        } 
 }
};

void ModRangeSolver::processFact(Node node, EqOrigin index){
  // strip down to the polynomial
  //std::cout << node << "\n";
  NodeManager* nm = nodeManager();
  bool isNeg = (node.getKind() == Kind::NOT);
  if (isNeg) {
    node = node[0];
  }
  bool isEq = (node.getKind() == Kind::EQUAL);
  bool isMod = (isEq & (node[0].getKind() == Kind::MM_MOD));
  if (isEq){
    //std::cout << "we should not be here\n";
    if(isMod){
      Node exp = node[0][0];
      Integer modulo = node[0][1].getConst<Rational>().getNumerator();
      ModularRing* currRing = myModularRings[modulo].get();
      if (isNeg){
        currRing->disequalities.push_back(nm->mkNode(Kind::EQUAL, exp, nm->mkConstInt(0)));
        currRing->origin_diseq.push_back(index.value);
      } else {
         currRing->equalities.push_back(nm->mkNode(Kind::EQUAL, exp, nm->mkConstInt(0)));
         currRing->origin_eq.push_back(index);
      }
    } else {
      Node exp = nm->mkNode(Kind::SUB, node[0], node[1]);
      if (isNeg){
        myIntegerRing.disequalities.push_back(nm->mkNode(Kind::EQUAL, exp, nm->mkConstInt(0)));
        myIntegerRing.origin_diseq.push_back(index.value);
      } else {
        myIntegerRing.equalities.push_back(nm->mkNode(Kind::EQUAL, exp, nm->mkConstInt(0)));
        myIntegerRing.origin_eq.push_back(index);
      }
    }
  } else {
    if (node[0].getKind() == Kind::MM_MOD){
      return;
    }
    // Non Skolem case
    if (isVariableOrSkolem(node[0]) && node[1].getKind()==Kind::CONST_INTEGER){
      auto ogBound = bounds.find(node[0].getName());
      Integer newBound = node[1].getConst<Rational>().getNumerator();
      AlwaysAssert(node.getKind() == Kind::GEQ) << "unsupported inequality";
      AlwaysAssert(ogBound!= bounds.end()) << "unregistered variable";
      if (!isNeg){
           ogBound->second.first= std::max(Bound(newBound), ogBound->second.first);
      } else {
            ogBound->second.second = std::min(Bound((newBound-1)), ogBound->second.second);
      }
    } //Skolem Case
    else {
      Trace("debug-process-fact") << node << "\n";
      if (node[0].getKind() == Kind::MM_MOD){
        return;
      } else {
         AlwaysAssert(node.getKind() == Kind::GEQ) << "unsupported inequality";
         Integer bd; 
         if (node[1].getKind() == Kind::CONST_INTEGER){
            bd = node[1].getConst<Rational>().getNumerator();
            node = node[0];
         } else {
            bd = Integer(0);
            node = nm->mkNode(Kind::SUB, node[0], node[1]);
         }
          Node sk;
          if (tempSkolemMap.find(node) != tempSkolemMap.end())
           {
              sk = tempSkolemMap[node];
           } else {
              SkolemManager* sm = nm->getSkolemManager();
              sk = sm->mkDummySkolem("Var", nm->integerType());
              bounds[sk.getName()] = std::make_pair(Bound::negativeInfinity(), Bound::positiveInfinity());
           }
            auto ogBound = bounds.find(sk.getName());
            AlwaysAssert(ogBound!= bounds.end()) << "unregistered variable";
            if (!isNeg){
                ogBound->second.first= std::max(Bound(bd), ogBound->second.first);
            } else {
                  ogBound->second.second = std::min(Bound((bd)), ogBound->second.second);
            }
      }
    }
   }
  }



void ModRangeSolver::printSystemState(){
    std::cout << "Num Rings:" << myModularRings.size()+1 << "\n"; 
    std::cout << "ZZ Ring " << "\n";
    std::cout << "\tequalities:" << "\n";
    for (auto i: myIntegerRing.equalities) {
        std::cout << "\t\t" <<  i << "\n";
    }
    std::cout << "\tdisequalities:" << "\n";
    for (auto i: myIntegerRing.disequalities) {
        std::cout << "\t\t" << i << "\n";
    }
    for (auto& pair: myModularRings){
        std::cout << "ZZ/" << pair.first << "\n";
        //std::cout << "Status:" << pair.second.status << "\n";
        std::cout << "\tequalities:" << "\n";
         for (int i =0; i< pair.second->equalities.size(); i++) {
            std::cout << "\t\t" <<  pair.second->equalities[i] << "\n";
        }
        std::cout << "\tdisequalities" << "\n";
        //std::cout << pair.second.inequalities.size() << "\n";
        for (int i = 0; i<pair.second->disequalities.size(); i++) {
            std::cout << "\t\t" << pair.second->disequalities[i]  << "\n";
        }
    }
    std::cout << "Bounds\n";
    for (auto& i : bounds)
    {
      std::cout << "\t" << i.first << ":(" << i.second.first.toString() << ", " << i.second.second.toString() << ")\n";
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
