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


struct EqOrigin {
    int value; 
    int gb;
};

std::ostream& operator<<(std::ostream& os, const EqOrigin& e);

    class Ring: protected EnvObj {

    public:
        Ring(Env& env);
        /**
        * Equalities living in the ring.
        */
        bool allEqsOg = true;

        bool newEqSinceGB = false;

        int EqsMoved = 0;

        int DiseqMoved = 0;

        int DiseqReduced = 0;

        std::vector<EqOrigin> unsatCause;

        std::vector<EqOrigin> origin_eq;

        std::map<int, std::vector<EqOrigin>> pastGbs;

        std::vector<int> origin_diseq;

        CocoaEncoder d_encoder;

        std::vector<CoCoA::RingElem> gbBasis;

        Result checkDiseq();

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

        void clearState(){equalities.clear(), disequalities.clear(), GBTimeOut = false; newEqSinceGB = true; EqsMoved = 0; DiseqMoved = 0; DiseqReduced = 0; gbBasis.clear();}
        /**
        * Checks if equalities/disequalities in the ring are unsat:
        * 1. 1 in equalities.
        * 2. a negated disequality is implied by equalites
        */
        Result CheckUnsat();

        bool reduceAddEquality(Node fact, EqOrigin index);

        bool AddDisquality(Node fact, int index);

        void prepGB(CocoaEncoder& enc);

        Result analyzeGB(CocoaEncoder& enc,  std::vector<int> indices = {});

    } ;

} // namespace modular
} // namespace airth
} // namespace modular
} // namespace cvc5::internal

#endif // CVC5__THEORY__ARITH__RING_H