#include "theory/arith/nl/modular_ext/ring.h"
#include "smt/env_obj.h"
#include "util/integer.h"

#ifndef CVC5__THEORY__ARITH__NL__MODEXT__MODULAR_RING_H
#define CVC5__THEORY__ARITH__NL__MODEXT__MODULAR_RING_H


namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

class IntegerRing;

class ModularRing : public Ring
{
 public:
  ModularRing(Env& env, Integer& modulus);

  Node modOut(Node fact);

  bool reduceAddEquality(Node fact, EqOrigin index);

  bool AddDisquality(Node fact, int index);

  Integer modulus;

  bool isPrime;

  Result computeGB();

 private:
};

}  // namespace nl
}  // namespace arith
} // namespace modular
} // namespace cvc5::internal

#endif // CVC5__THEORY__ARITH__MODULAR_RING_H