#ifndef CVC5__THEORY__ARITH__RING_H
#define CVC5__THEORY__ARITH__RING_H

#include "expr/node.h"
#include "smt/env_obj.h"
#include "util/integer.h"
#include "util/result.h"
#include "context/cdlist.h"
#include "theory/arith/nl/modular_ext/int_cocoa_encoder.h"


namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

    class Ring: protected EnvObj {

    public:
        Ring(Env& env);
        /**
        * Equalities living in the ring.
        */
        std::vector<Node> equalities;

        /**
        * Disequalities living in the ring with the not operator dropped.
        */
        std::vector<Node> disequalities;

        /**
        * Current Status of the ring can either be unknown of unsat.
        */
        Result status = Result::UNKNOWN;

        /**
        * Checks if equalities/disequalities in the ring are unsat:
        * 1. 1 in equalities.
        * 2. a negated disequality is implied by equalites
        */
        Result CheckUnsat();

        bool reduceAddEquality(Node fact);

        bool AddDisquality(Node fact);

        void prepGB(CocoaEncoder& enc);

        Result analyzeGB(CocoaEncoder& enc);

        bool reduceAgainstGB(Node eq);

    } ;


} // namespace modular
} // namespace airth
} // namespace modular
} // namespace cvc5::internal

#endif // CVC5__THEORY__ARITH__RING_H