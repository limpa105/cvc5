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

ModRangeSolver::~ModRangeSolver() {}

void ModRangeSolver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  for(auto& fact: assertions){
      processFact(fact);
  }
  int count = 0;
  bool infoToLearn = false;
  Trace("mod-range-solver") << "Starred solving " << std::endl;
  while(count < 3 ){
    count +=1;
    //Trace("mod-range-solver") << "Starred solving " << std::endl;
    //printSystemState();
    // Lower + compute GBs in the moduli ring
    for (auto &pair: myModularRings){
      for (Node &eq: pair.second->equalities){
        if (checkIfConstraintIsMet(eq, pair.second->modulus, bounds)){
          myIntegerRing.reduceAddEquality(eq);
        }
        }
       for (auto &diseq: pair.second->disequalities){
        myIntegerRing.AddDisquality(diseq);
       }
       if(pair.second->computeGB() == Result::UNSAT){
        std::cout << "UNSAT" << "\n";
        d_im.lemma(nodeManager()->mkNode(Kind::NOT, nodeManager()->mkNode(Kind::AND, assertions)), InferenceId::ARITH_NL_MOD_RANGE_SOLVER);
        return;
       }
    }
    //printSystemState();
    // Lift + compute GBs in the Integer ring
    for (auto &eq: myIntegerRing.equalities){
      for (auto &pair: myModularRings){
        pair.second->reduceAddEquality(eq);
      }
    }
    for (auto &diseq: myIntegerRing.disequalities){
      for (auto &pair: myModularRings){
        if (checkIfConstraintIsMet(diseq, pair.second->modulus, bounds, true)){
          pair.second->reduceAddEquality(diseq);
        }
      }
    }
    if(myIntegerRing.computeGB(myVariables, bounds) == Result::UNSAT){
      std::cout << "UNSAT" << "\n";
        d_im.lemma(nodeManager()->mkNode(Kind::NOT, nodeManager()->mkNode(Kind::AND, assertions)), InferenceId::ARITH_NL_MOD_RANGE_SOLVER);
         return;
       }
    //std::cout << "got to here\n";
  }

  std::cout << "UNKNOWN" << "\n";
  for (auto& as: false_asserts){
    //std::cout << as << "\n";
     d_im.lemma(nodeManager()->mkNode(Kind::EQUAL, replaceMMMod(as, nodeManager())[0], as[0]), InferenceId::ARITH_NL_MOD_RANGE_SOLVER);
  }    
  //printSystemState();
  //AlwaysAssert(false);
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

void ModRangeSolver::processFact(Node node){
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
      } else {
         currRing->equalities.push_back(nm->mkNode(Kind::EQUAL, exp, nm->mkConstInt(0)));
      }
    } else {
      Node exp = nm->mkNode(Kind::SUB, node[0], node[1]);
      if (isNeg){
        myIntegerRing.disequalities.push_back(nm->mkNode(Kind::EQUAL, exp, nm->mkConstInt(0)));
      } else {
        myIntegerRing.equalities.push_back(nm->mkNode(Kind::EQUAL, exp, nm->mkConstInt(0)));
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
      if (node[0].getKind() == Kind::MM_MOD){
        return;
      }else {
        //std::cout << node[0].getKind() << "\n";
      }
      // thoughts even like 3x < 6 be in this case.. is this okay? yes
      // hopefully 
      AlwaysAssert(false) <<  node << "NOT IMPLEMENTED YET";
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
    std::cout << "DONE!" << "\n";
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
