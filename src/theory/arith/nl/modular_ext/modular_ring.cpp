#include "theory/arith/nl/modular_ext/modular_ring.h"
#include "theory/arith/nl/modular_ext/int_cocoa_encoder.h"
#include <CoCoA/SparsePolyOps-RingElem.H>

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

ModularRing::ModularRing(Env& env, Integer& modulus)
  : Ring(env), modulus(modulus)
{
}

Result ModularRing::computeGB() {
  if (gbBasis.empty()) {
    // If GB basis doesn't exist, compute it
    CocoaEncoder enc(d_env);
    prepGB(enc);
    Result res = analyzeGB(enc);
    if (res == Result::UNSAT) {
      return res;
    }
    // Store the computed GB basis
    gbBasis = enc.getGBBasis();
    d_polyRing = enc.getPolyRing();
  }
  return Result::UNKNOWN;
}

CoCoA::RingElem ModularRing::reduceAgainstGB(CoCoA::RingElem poly) {
  if (gbBasis.empty()) {
    // If GB basis doesn't exist, compute it
    computeGB();
  }
  
  // Reduce the polynomial against the GB basis using CoCoA's reduction
  return CoCoA::NR(poly, gbBasis);
}

Result ModularRing::checkDisequalitiesAgainstGB() {
  if (gbBasis.empty()) {
    // If GB basis doesn't exist, compute it
    computeGB();
  }

  // Check each disequality
  for (const Node& diseq : disequalities) {
    // Convert the disequality to a CoCoA polynomial
    CocoaEncoder enc(d_env);
    enc.addFact(diseq);
    CoCoA::RingElem poly = enc.getPoly(diseq);
    
    // Reduce against GB basis
    CoCoA::RingElem reduced = reduceAgainstGB(poly);
    
    // Check if reduced to 0
    if (CoCoA::IsZero(reduced)) {
      return Result::UNSAT;
    }
  }
  return Result::UNKNOWN;
}

}
}
}
}