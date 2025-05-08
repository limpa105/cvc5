#ifndef CVC5__THEORY__ARITH__RING_H
#define CVC5__THEORY__ARITH__RING_H

#include "expr/node.h"
#include "smt/env_obj.h"
#include "util/integer.h"
#include "util/result.h"
#include "context/cdlist.h"
#include "theory/arith/nl/modular_ext/int_cocoa_encoder.h"
#include <CoCoA/SparsePolyRing.H>

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

        bool GBTimeOut = false;
        /**
        * Disequalities living in the ring with the not operator dropped.
        */
        std::vector<Node> disequalities;

        /**
        * Current Status of the ring can either be unknown of unsat.
        */
        Result status = Result::UNKNOWN;

        /**
        * Stores the computed Groebner basis for this ring as CoCoA polynomials
        */
        std::vector<CoCoA::RingElem> gbBasis;

        /**
        * The polynomial ring used for GB computations
        */
        std::shared_ptr<CoCoA::SparsePolyRing> d_polyRing;

        /**
        * The encoder used for GB computations
        */
        std::unique_ptr<CocoaEncoder> d_encoder;

        /**
        * Checks if equalities/disequalities in the ring are unsat:
        * 1. 1 in equalities.
        * 2. a negated disequality is implied by equalites
        */
        Result CheckUnsat();

        /**
        * Checks if any disequality reduces to 0 modulo the GB basis
        * @return Result::UNSAT if a disequality reduces to 0, Result::UNKNOWN otherwise
        */
        Result checkDiseq();

        bool reduceAddEquality(Node fact);

        bool AddDisquality(Node fact);

        void prepGB(CocoaEncoder& enc);

        Result analyzeGB(CocoaEncoder& enc);

    } ;

} // namespace nl
} // namespace arith
} // namespace theory
} // namespace cvc5::internal

#endif // CVC5__THEORY__ARITH__RING_H