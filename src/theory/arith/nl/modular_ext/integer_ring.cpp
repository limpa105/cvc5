#include "theory/arith/nl/modular_ext/integer_ring.h"
#include "theory/arith/nl/modular_ext/utils.h"
#include <CoCoA/error.H>

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {


  IntegerRing::IntegerRing(Env& env)
    : Ring(env){

    };

  Result IntegerRing::computeGB(std::vector<Node> variables, std::map<std::string, std::pair<Bound, Bound>> bounds){
  if (equalities.size() < 2 || GBTimeOut){
      return Result::UNKNOWN;
  }
  try {
  CocoaEncoder enc = CocoaEncoder();
   for (const Node& node :equalities)
      {
        enc.addFact(node);
      }
  std::vector<long> weights = boundsToWeights(enc.d_syms, bounds);
  Trace("intgb") << "Weights: ";
    for (long w : weights) Trace("intgb") << w << " ";
    Trace("intgb") << "\nCalling endScanIntegers...\n";

    enc.endScanIntegers(weights);

    Trace("intgb") << "Calling analyzeGB...\n";
    return analyzeGB(enc);

} catch (const CoCoA::ErrorInfo& e) {
  std::cerr << "[Exception] " << e << std::endl;
  AlwaysAssert(false);
  //return {}; // or false, or nullptr
}
}

}  // namespace nl
}  // namespace arith
} // namespace modular
} // namespace cvc5::internal