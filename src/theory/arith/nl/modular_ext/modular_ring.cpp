#include "theory/arith/nl/modular_ext/modular_ring.h"
#include "theory/arith/nl/modular_ext/int_cocoa_encoder.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

ModularRing::ModularRing(Env& env, Integer& modulus)
  : Ring(env), modulus(modulus)
{
}


Result ModularRing::computeGB(){
  if (!isPrime){
    return Result::UNKNOWN;
  }
  CocoaEncoder enc = CocoaEncoder(modulus);
  prepGB(enc);
  enc.endScanModulo();
  return analyzeGB(enc);
}


}
}
}
}