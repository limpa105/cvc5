#include "theory/arith/nl/modular_ext/integer_ring.h"
#include "theory/arith/arith_rewriter.h"
#include <CoCoA/ideal.H>
#include <CoCoA/BigInt.H>
#include <CoCoA/CpuTimeLimit.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/ring.H>


namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {


  Ring::Ring(Env& env):
    EnvObj(env)
    {};

  bool Ring::reduceAddEquality(Node fact){
        fact = rewrite(fact);
        if (std::find(equalities.begin(), equalities.end(), fact) == equalities.end()){
          equalities.push_back(fact);
          return true;
        }
        return false;
     }

  bool Ring::AddDisquality(Node fact){
        fact = rewrite(fact);
        if (std::find(disequalities.begin(), disequalities.end(), fact) == disequalities.end()){
          disequalities.push_back(fact);
          return true;
        }
        return false;
      }


  void Ring::prepGB(CocoaEncoder& enc){
     for (const Node& node : equalities)
      {
        enc.addFact(node);
      }
  }

  Result Ring::analyzeGB(CocoaEncoder& enc){
    std::cout << "oh\n";
    for (const Node& node :equalities)
      {
        std::cout << node << "\n";
        enc.addFact(node);
      }
    std::cout << "huh1\n";
    std::vector<CoCoA::RingElem> generators;
    generators.insert(generators.end(), enc.polys().begin(), enc.polys().end());
    std::vector<Node> newPoly;
    CoCoA::ideal ideal = CoCoA::ideal(generators);
    std::cout << "huh\n";
    const auto basis = GBasis(ideal);
      if (basis.size() == 1 && CoCoA::deg(basis.front()) == 0)
      {
        return Result::UNSAT;
      }
      newPoly = enc.cocoaToNode(basis, nodeManager());
      equalities = newPoly;
      return Result::UNKNOWN;
  }


      //std::cout << "Scanned Integers \n";
      //std::cout << "Got weights \n";
      // assert facts
      






}  // namespace nl
}  // namespace arith
} // namespace modular
} // namespace cvc5::internal