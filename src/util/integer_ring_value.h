#include "cvc5_public.h"


#ifndef CVC5__RING_INTEGERVALUE_H
#define CVC5__RING_INTEGERVALUE_H

#include "util/integer.h"

namespace cvc5::internal {

class IntegerRingValue: public Integer
{
 public:
 IntegerRingValue(Integer v)
  : Integer(v)
{}
};
}

#endif