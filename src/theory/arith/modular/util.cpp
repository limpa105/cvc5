#include "theory/arith/modular/util.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace modular_range_solver {
bool isFfLeaf(const Node& n)
{
  return 
         !(n.getKind() == Kind::ADD
              || n.getKind() == Kind::MULT
              || n.getKind() == Kind::NONLINEAR_MULT
              || n.getKind() == Kind::NEG);
}

bool isFfTerm(const Node& n) { return true; }

bool isFfFact(const Node& n)
{
  return (n.getKind() == Kind::EQUAL)
         || (n.getKind() == Kind::NOT && n[0].getKind() == Kind::EQUAL);
}
}
}
}
}