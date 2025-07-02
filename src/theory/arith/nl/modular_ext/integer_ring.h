#ifndef CVC5__THEORY__ARITH__INTEGER_RING_H
#define CVC5__THEORY__ARITH__INTEGER_RING_H

#include "theory/arith/nl/modular_ext/ring.h"
#include "theory/arith/nl/modular_ext/bounds.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

    class IntegerRing : public Ring {

        public: 

         IntegerRing(Env& env);

         Result computeGB(std::vector<Node> variables, std::map<std::string, std::pair<Bound, Bound>> bounds);

        std::pair<Bound, Bound> inferBoundsRecursive(
            const Node& node,
            std::map<std::string, std::pair<Bound, Bound>>& Bounds);

        std::pair<Node, Node> separateTerms(const Node& node, Node targetNode);

         Result tightenBounds(std::map<std::string, std::pair<Bound, Bound>>& Bounds);

    };

} // namespace modular
} // namespace airth
} // namespace modular
} // namespace cvc5::internal

#endif // CVC5__THEORY__ARITH__INETGER_RING_H