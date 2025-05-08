#include "theory/arith/nl/modular_ext/modular_ring.h"
#include "theory/arith/nl/modular_ext/int_cocoa_encoder.h"
#include <CoCoA/SparsePolyOps-RingElem.H>
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

ModularRing::ModularRing(Env& env, Integer& modulus)
  : Ring(env), modulus(modulus)
{
  isPrime = modulus.isProbablePrime();
}

Result ModularRing::computeGB() {
  if (!isPrime || !newEqSinceGB || equalities.size()<2 || GBTimeOut){
   Trace("intgb") << "Skipping GB computation for modulus = " << modulus << "\n";

  if (!isPrime)
  {
    Trace("intgb") << "- Reason: modulus is not prime: " << modulus << "\n";
  }

  if (!newEqSinceGB)
  {
    Trace("intgb") << "- Reason: no new equalities since last GB\n";
  }

  if (equalities.size() < 2)
  {
    Trace("intgb") << "- Reason: too few equalities: size = " << equalities.size() << "\n";
  }

  if (GBTimeOut)
  {
    Trace("intgb") << "- Reason: previous GB computation timed out\n";
  }

    return Result::UNKNOWN;
  }
  CocoaEncoder enc = CocoaEncoder(modulus);
  prepGB(enc);
  enc.endScanModulo();
  return analyzeGB(enc);
}

Node ModularRing::modOut(Node fact)
{
  NodeManager* nm = nodeManager();
  Kind k = fact.getKind();
  // Recurse on ADD or MULT (or NONLINEAR_MULT)
  if (k == Kind::ADD || k == Kind::MULT || k == Kind::NONLINEAR_MULT)
  {
    std::vector<Node> children;
    for (const Node& c : fact)
    {
      children.push_back(modOut(c));
    }
    return nm->mkNode(k, children);
  }
  // Leave variables and skolems unchanged
  if (isVariableOrSkolem(fact))
  {
    return fact;
  }
  // Handle constant integers
  if (k == Kind::CONST_INTEGER)
  {
    Integer val = fact.getConst<Rational>().getNumerator();
    val = val.floorDivideRemainder(modulus);  // val := val mod modulos

    Integer half = modulus.floorDivideQuotient(2);
    // Normalize to symmetric range (e.g., -3 to 3 for mod 7)
    if (val.abs() >= half)
    {
      if (val > 0)
      {
        val -= modulus;
      }
      else
      {
        val += modulus;
      }
    }

    // Final check — must be within field
    AlwaysAssert(val.abs() < modulus.abs()) << "Modulo-reduced value out of range: " << val << " mod " << modulus;

    // Reduce 0 mod modulos to zero node
    if (modulus.divides(val))
    {
      return nm->mkConstInt(0);
    }

    return nm->mkConstInt(val);
  }
  if (k == Kind::EQUAL){
    return nm->mkNode(Kind::EQUAL, modOut(fact[0]), modOut(fact[1]));
  }
  if (k == Kind::SUB) {
    Node negated = nm->mkNode(Kind::MULT, nm->mkConstInt(Integer(-1)), modOut(fact[1]));
    return nm->mkNode(Kind::ADD, modOut(fact[0]), negated);
  }

  AlwaysAssert(false) << "Unsupported kind in modOut: " << k << " for node " << fact;
}

bool ModularRing::reduceAddEquality(Node fact){
    fact = modOut(fact);
    return Ring::reduceAddEquality(fact);
}

  bool ModularRing::AddDisquality(Node fact){
    fact = modOut(fact);
    return Ring::AddDisquality(fact);

  }



 
}
}
}
}