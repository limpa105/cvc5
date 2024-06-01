
#include "cvc5_private.h"

#ifndef CVC5__THEORY__INT__UTIL_H
#define CVC5__THEORY__INT__UTIL_H

// external includes
#ifdef CVC5_USE_COCOA
#include <CoCoA/ring.H>
#endif /* CVC5_USE_COCOA */

// std includes
#include <unordered_map>

// internal includes
#include "expr/node.h"
#include "util/integer.h"


namespace cvc5::internal {
namespace theory {
namespace arith {
namespace modular_range_solver {

/** Is this a field term with non-field kind? */
bool isFfLeaf(const Node& n);
/** Is this a field term? */
bool isFfTerm(const Node& n);
/** Is this a field fact (equality of disequality)? */
bool isFfFact(const Node& n);
}
}
}
}

#endif