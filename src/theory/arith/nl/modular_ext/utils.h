
#ifndef CVC5__THEORY__ARITH__NL__MODEXT__UTILS_H
#define CVC5__THEORY__ARITH__NL__MODEXT__UTILS_H


#include "expr/node_traversal.h"
#include "theory/arith/nl/modular_ext/bounds.h"
// external includes
#include <CoCoA/BigInt.H>
#include <CoCoA/ring.H>
// std includes
#include <optional>
#include <sstream>
#include <vector>
#include "util/integer.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
bool isVariableOrSkolem(Node node);

/** Is this a field term with non-field kind? */
bool isFfLeaf(const Node& n);
/** Is this a field term? */
bool isFfTerm(const Node& n);
/** Is this a field fact (equality of disequality)? */
bool isFfFact(const Node& n);

/** A polynomial. (note: C++/Cocoa doesn't distinguish this from Scalar) */
using Poly = CoCoA::RingElem;
/** A coefficient. (note: C++/Cocoa doesn't distinguish this from Poly) */
using Scalar = CoCoA::RingElem;
/** A list of polynomials. */
using Polys = std::vector<Poly>;
/** A partial input (point/vector with optional entries) to a polynomial */
using PartialPoint = std::vector<std::optional<Scalar>>;
/** An input (point/vector) to a polynomial */
using Point = std::vector<Scalar>;


std::optional<Scalar> cocoaEval(Poly poly, const PartialPoint& values);

/** total evaluation of polynomials */
Scalar cocoaEval(Poly poly, const Point& values);


/** convert an Integer to CoCoA::BitInt. */
CoCoA::BigInt intToCocoa(const Integer& i);

/** get the string representation of a type that implements operator<<. */
template <typename T>
std::string extractStr(const T& t)
{
  std::ostringstream o;
  o << t;
  return o.str();
}


void collectVars(const Node& t, std::unordered_set<Node>& vars);

bool containsVariable(const Node& node, Node targetNode);

std::vector<std::vector<long>> grevlexWeighted(std::vector<long> weights);

bool checkIfConstraintIsMet(Node equality, Integer modulos, std::map<std::string, std::pair<Bound, Bound> > Bounds, bool ineq = false);

std::vector<long> boundsToWeights(std::vector<CoCoA::symbol>& vars,
                                  std::map<std::string, std::pair<Bound, Bound>>& bounds);

Node replaceMMMod(Node exp, NodeManager* nm);


}
}
}
}
#endif // CVC5__THEORY__ARITH__NL__MODEXT_UTILS_H