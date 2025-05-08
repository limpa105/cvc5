#ifndef CVC5__THEORY__ARITH__NL__MODEXT__BOUNDS_H
#define CVC5__THEORY__ARITH__NL__MODEXT__BOUNDS_H

#include <optional>
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

class Bound {
public:
  enum class Type {
    NEG_INFINITY,
    FINITE,
    POS_INFINITY
  };

  Bound();  // pos_infinity by default
  Bound(const Integer& v);  // finite value
  static Bound negativeInfinity();
  static Bound positiveInfinity();

  bool isInfinite() const;

  std::optional<Integer>& getValue();


  void setValue(const Integer& v);  // set to a new finite value
  void setTo( Bound& other);
  void setInfinite(); 
  void setPositiveInfinity();
  void setNegativeInfinity();                   
  void clear();                   

  bool operator<(const Bound& other) const;
  bool operator==(const Bound& other) const;

  std::string toString() const;

  const std::optional<Integer>& getValue() const;

private:

  Type type;

  std::optional<Integer> value;
};
}
}
}
}
#endif // BOUND_H
