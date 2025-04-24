#include "theory/arith/nl/modular_ext/bounds.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

namespace nl {

Bound::Bound() : type(Type::POS_INFINITY), value(std::nullopt) {}

Bound::Bound(const Integer& v) : type(Type::FINITE), value(v) {}

Bound Bound::negativeInfinity() {
  Bound b;
  b.type = Type::NEG_INFINITY;
  b.value.reset();
  return b;
}

Bound Bound::positiveInfinity() {
  Bound b;
  b.type = Type::POS_INFINITY;
  b.value.reset();
  return b;
}


bool Bound::isInfinite() const  {
  return type != Type::FINITE;;
}

std::optional<Integer>& Bound::getValue() {
  return value;
}

const std::optional<Integer>& Bound::getValue() const {
  return value;
}

void Bound::setValue(Integer& v) {
  type = Type::FINITE;
  value = v;
}

void Bound::setPositiveInfinity() {
  type = Type::POS_INFINITY;
  value.reset();
}

void Bound::setNegativeInfinity() {
  type = Type::NEG_INFINITY;
  value.reset();
}

bool Bound::operator<(const Bound& other) const{
  if (type == other.type) {
    if (type == Type::FINITE) {
      return value.value() < other.value.value();
    }
    return false; // infinities are equal in their kind
  }

  if (type == Type::NEG_INFINITY) return true;
  if (other.type == Type::NEG_INFINITY) return false;

  if (type == Type::FINITE) return other.type == Type::POS_INFINITY;
  return false; // type is POS_INFINITY, other must be finite
}

bool Bound::operator==(const Bound& other) const  {
  if (type != other.type) return false;
  if (type == Type::FINITE) return value == other.value;
  return true;
}

std::string Bound::toString() const  {
  switch (type) {
    case Type::NEG_INFINITY: return "-∞";
    case Type::POS_INFINITY: return "∞";
    case Type::FINITE: return value->toString();
  }
  //AlwaysAssert(false);
}

void Bound::setTo( Bound& other) {
  type = other.type;
  value = other.value;
}

}
}
}
}