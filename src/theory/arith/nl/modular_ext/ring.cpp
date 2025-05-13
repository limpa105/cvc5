#include "theory/arith/nl/modular_ext/integer_ring.h"
#include "theory/arith/arith_rewriter.h"
#include <CoCoA/ideal.H>
#include <CoCoA/BigInt.H>
#include <CoCoA/CpuTimeLimit.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/ring.H>
#include <CoCoA/TmpGPoly.H>
#include "CoCoA/ideal.H"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

  Ring::Ring(Env& env):
    EnvObj(env)
  {
  }

  bool Ring::reduceAddEquality(Node fact){
    fact = rewrite(fact);
    if (std::find(equalities.begin(), equalities.end(), fact) == equalities.end()){
        if (gbBasis.empty() || GBTimeOut) {
            equalities.push_back(fact);
            newEqSinceGB = true;
            return true;
          } else {
            CoCoA::RingElem poly;
            std::optional<CoCoA::RingElem> maybePoly = d_encoder.tryEncodeFact(fact);
            if (!maybePoly)
            {
            equalities.push_back(fact);
            newEqSinceGB = true;
            return true;
            }
            else
            {
              poly = *maybePoly;
            }
          CoCoA::ideal I = CoCoA::ideal(gbBasis);
         
          CoCoA::RingElem reduced = CoCoA::NF(poly, I);  // Or: poly % I
          if (CoCoA::IsZero(reduced)) {
            return false;
          } else {
            equalities.push_back(fact);
            newEqSinceGB = true;
            return true;
          }
          }
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
    for (const Node& node : equalities) {
      enc.addFact(node);
    }
  }

  Result Ring::analyzeGB(CocoaEncoder& enc){
    Trace("intgb") << "Adding facts\n";
    for (const Node& node : equalities) {
      enc.addFact(node);
    }
    Trace("intgb") << "Constructing ideal\n";
    std::vector<CoCoA::RingElem> generators;
    generators.insert(generators.end(), enc.polys().begin(), enc.polys().end());
    std::vector<Node> newPoly;
    CoCoA::ideal ideal = CoCoA::ideal(generators);
    Trace("intgb") << "Computing GB for" <<  enc.polyRing() << std::endl;
    std::vector<Poly> basis;
    try {
      basis = GBasis(ideal, CoCoA::CpuTimeLimit(30));
    }
    catch (CoCoA::TimeoutException& t) {
      GBTimeOut = true;
      return Result::UNKNOWN;
    }
    if (basis.size() == 1 && CoCoA::deg(basis.front()) == 0) {
      return Result::UNSAT;
    }
    // Store the GB basis and encoder
    gbBasis = basis;
    //d_polyRing = enc.polyRing();
    d_encoder =  enc;
    newPoly = enc.cocoaToNode(basis, nodeManager());
    equalities = newPoly;
    newEqSinceGB = false;
    DiseqReduced = 0;
    EqsMoved = 0;
    return Result::UNKNOWN;
  }

Result Ring::checkDiseq()
{
  Trace("diseq") << "Starting checkDiseq...\n";

  if (gbBasis.empty())
  {
    Trace("diseq") << "Gröbner basis is empty, returning UNKNOWN.\n";
    return Result::UNKNOWN;
  }

  // Wrap your GB into a CoCoA ideal
  CoCoA::ideal I = CoCoA::ideal(gbBasis);

  for (int i = DiseqReduced; i<disequalities.size(); i++)
  {
    Node diseq = disequalities[i];
    Trace("diseq") << "Processing disequality: " << diseq << "\n";

    std::optional<CoCoA::RingElem> maybePoly = d_encoder.tryEncodeFact(diseq);
    if (!maybePoly)
    {
      Trace("diseq") << "Could not encode disequality, skipping: " << diseq << "\n";
      continue;
    }

    CoCoA::RingElem poly = *maybePoly;
    Trace("diseq") << "Encoded polynomial: " << poly << "\n";

    CoCoA::RingElem reduced = CoCoA::NF(poly, I);
    Trace("diseq") << "Reduced form: " << reduced << "\n";

    if (CoCoA::IsZero(reduced))
    {
      Trace("diseq") << "Disequality reduces to 0 → contradiction → UNSAT\n";
      return Result::UNSAT;
    }
  }
  DiseqReduced = disequalities.size();
  Trace("diseq") << "No disequality reduced to 0 → returning UNKNOWN\n";
  return Result::UNKNOWN;
}


}  // namespace nl
}  // namespace arith
} // namespace modular
} // namespace cvc5::internal