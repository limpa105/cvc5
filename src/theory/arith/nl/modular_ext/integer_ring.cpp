#include "theory/arith/nl/modular_ext/integer_ring.h"
#include "theory/arith/nl/modular_ext/utils.h"
#include <CoCoA/error.H>
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {


  IntegerRing::IntegerRing(Env& env)
    : Ring(env){

    };

  Result IntegerRing::computeGB(std::vector<Node> variables, std::map<std::string, std::pair<Bound, Bound>> bounds){
  if (!newEqSinceGB || equalities.size()<2 || GBTimeOut ){
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


std::pair<Bound, Bound> IntegerRing::inferBoundsRecursive(
    const Node& node,
    std::map<std::string, std::pair<Bound, Bound>>& Bounds)
{
  if (node.getKind() == Kind::CONST_INTEGER) {
    Integer constValue = node.getConst<Rational>().getNumerator();
    return {Bound(constValue), Bound(constValue)};
  } else if (isVariableOrSkolem(node)) {
    std::string varName = node.getName();
    return Bounds.at(varName);
  }

  if (node.getKind() == Kind::ADD) {
    Bound sumLower = Bound::negativeInfinity();
    Bound sumUpper = Bound::positiveInfinity();
    bool lowerInit = true, upperInit = true;

    for (const Node& child : node) {
      auto [childLower, childUpper] = inferBoundsRecursive(child, Bounds);

      if (childLower.isInfinite()) {
        if (!childLower.getValue().has_value()) sumLower = Bound::negativeInfinity();
      } else {
        if (lowerInit) {
          sumLower = childLower;
          lowerInit = false;
        } else {
          sumLower.setValue(*sumLower.getValue() + *childLower.getValue());
        }
      }

      if (childUpper.isInfinite()) {
        if (!childUpper.getValue().has_value()) sumUpper = Bound::positiveInfinity();
      } else {
        if (upperInit) {
          sumUpper = childUpper;
          upperInit = false;
        } else {
          sumUpper.setValue(*sumUpper.getValue() + *childUpper.getValue());
        }
      }
    }

    return {sumLower, sumUpper};
  }

  if (node.getKind() == Kind::MULT || node.getKind() == Kind::NONLINEAR_MULT) {
    std::vector<std::pair<Bound, Bound>> terms;
    for (const Node& child : node) {
      terms.push_back(inferBoundsRecursive(child, Bounds));
    }

    // Initialize product bounds
    std::vector<Integer> possibleProducts;

    // Compute all min/max products from the bound corners
    std::function<void(size_t, Integer)> dfs = [&](size_t i, Integer acc) {
      if (i == terms.size()) {
        possibleProducts.push_back(acc);
        return;
      }
      const auto& [lo, hi] = terms[i];
      if (!lo.isInfinite()) dfs(i + 1, acc * *lo.getValue());
      if (!hi.isInfinite() && *hi.getValue() != *lo.getValue()) dfs(i + 1, acc * *hi.getValue());
    };

    dfs(0, Integer(1));

    if (possibleProducts.empty()) {
      return {Bound::negativeInfinity(), Bound::positiveInfinity()};
    } else {
      auto [minIt, maxIt] = std::minmax_element(possibleProducts.begin(), possibleProducts.end());
      return {Bound(*minIt), Bound(*maxIt)};
    }
  }

  if (node.getKind() == Kind::SUB) {
    auto [leftLo, leftHi] = inferBoundsRecursive(node[0], Bounds);
    auto [rightLo, rightHi] = inferBoundsRecursive(node[1], Bounds);

    Bound resultLo, resultHi;

    if (leftLo.isInfinite() || rightHi.isInfinite()) {
      resultLo = Bound::negativeInfinity();
    } else {
      resultLo = Bound(*leftLo.getValue() - *rightHi.getValue());
    }

    if (leftHi.isInfinite() || rightLo.isInfinite()) {
      resultHi = Bound::positiveInfinity();
    } else {
      resultHi = Bound(*leftHi.getValue() - *rightLo.getValue());
    }

    return {resultLo, resultHi};
  }


  AlwaysAssert(false) << node.getKind();  // Unsupported kind
}



std::pair<Node, Node> IntegerRing::separateTerms(const Node& node, Node targetNode) {
    std::vector<Node> withTarget, withoutTarget;
    NodeManager* nm = nodeManager();
    if (isVariableOrSkolem(node)){
        if (containsVariable(node,targetNode)){
            return {nm->mkConstInt(0), node };
        } else {
            AlwaysAssert(false);
        }
        
    }
    else if (node.getKind() == Kind::ADD) {
        for (size_t i = 0; i < node.getNumChildren(); ++i) {
            Node child = node[i];
            if (containsVariable(child, targetNode)) {
                withTarget.push_back(child);
            } else {
                withoutTarget.push_back(child);
            }
        }
        Node withTargetNode = rewrite(nm->mkNode(Kind::ADD, withTarget));
        Node withoutTargetNode = rewrite(nm->mkNode(Kind::ADD, withoutTarget));
        return {withoutTargetNode, withTargetNode};

    } else if (node.getKind() == Kind::MULT) {
          if (containsVariable(node,targetNode)){
            return {nm->mkConstInt(0), node };
        } else {
            return {node, nm->mkConstInt(0)};
        }
    } else {
        AlwaysAssert(false) << node;
    }
}

Result IntegerRing::tightenBounds(std::map<std::string, std::pair<Bound, Bound>>& Bounds) {
  const int MAX_ROUNDS = 10;
  const int MAX_UPDATES_PER_VAR = 5;
  int round = 0;

  std::set<Node> varsToProcess;
  std::map<Node, int> updateCounts;
  std::map<Node, std::set<Node>> dependencyGraph;

  Trace("trace-tighten-bds") << "Starting tightenBounds on " << equalities.size() << " equalities\n";

  for (const auto& eq : equalities) {
    std::unordered_set<Node> vars;
    collectVars(eq, vars);
    varsToProcess.insert(vars.begin(), vars.end());
  }

  while (round++ < MAX_ROUNDS && !varsToProcess.empty()) {
    Trace("trace-tighten-bds") << "Round " << round << ", processing " << varsToProcess.size() << " vars\n";

    bool changedThisRound = false;
    std::set<Node> updatedVars;

    for (size_t i = 0; i < equalities.size(); ++i) {
      const Node& lhs = equalities[i][0];
      const Node& rhs = equalities[i][1];
      std::unordered_set<Node> eqVars;
      collectVars(equalities[i], eqVars);

      bool relevant = false;
      for (const auto& v : eqVars) {
        if (varsToProcess.count(v)) {
          relevant = true;
          break;
        }
      }
      if (!relevant) continue;

      Trace("trace-tighten-bds") << "- Processing equality " << equalities[i] << "\n";

      // Case: x = c
      if (isVariableOrSkolem(lhs) && rhs.getKind() == Kind::CONST_INTEGER) {
        Integer val = rhs.getConst<Rational>().getNumerator();
        Bound b(val);
        Bounds[lhs.getName()] = std::make_pair(b, b);
        updatedVars.insert(lhs);
        newEqSinceGB = true;
        changedThisRound = true;
        Trace("trace-tighten-bds") << "  - Set fixed bound for " << lhs << ": " << val << "\n";
        continue;
      }

      for (const auto& targetVar : eqVars) {
         Trace("trace-tighten-bds") << "  - Looking @ " << targetVar << "\n";
          Trace("trace-tighten-bds") << " Has updateCounts? " << updateCounts[targetVar] << "\n";
        if (updateCounts[targetVar] >= MAX_UPDATES_PER_VAR) {
          Trace("trace-tighten-bds") << "  - Skipping " << targetVar << ", hit update limit\n";
          continue;
        }

        NodeManager* nm = nodeManager();
        Node offset = nm->mkNode(Kind::ADD, rhs, nm->mkNode(Kind::MULT, nm->mkConstInt(-1), lhs));
        std::pair<Node, Node> separated = separateTerms(rewrite(offset), targetVar);
          Trace("trace-tighten-bds") << "  - seperated terms" << separated << "\n";
        const Node& targetTerm = separated.second;
        Integer coeff = -1;

        if (targetTerm.getKind() != Kind::MULT ||
            targetTerm.getNumChildren() != 2 ||
            targetTerm[0].getKind() != Kind::CONST_INTEGER) {
          Trace("trace-tighten-bds") << "  - Could not isolate variable " << targetVar << "\n";
          continue;
        }
         Trace("trace-tighten-bds") << "coef?" << targetTerm[0] << "\n";
        coeff *= targetTerm[0].getConst<Rational>().getNumerator();
        if (coeff == 0) {
          Trace("trace-tighten-bds") << "  - Coefficient is zero for " << targetVar << ", skipping\n";
          continue;
        }

        bool skip = false;
        std::unordered_set<Node> tempVars;
        collectVars(separated.first, tempVars);
        for (const auto& dep : tempVars) {
          if (dep == targetVar) {
            Trace("trace-tighten-bds") << "  - Cycle detected in " << targetVar << "\n";
            skip = true;
            break;
          }
          dependencyGraph[targetVar].insert(dep);
        }
        if (skip) continue;
         Trace("trace-tighten-bds") << "trying to recurse" << "\n";
        auto inferred = inferBoundsRecursive(separated.first, Bounds);
        Trace("trace-tighten-bds") << "inferred!!" << "\n";
         if (!inferred.first.getValue().has_value() ||
            !inferred.second.getValue().has_value()) {
            Trace("trace-tighten-bds") << "  - Inference failed or incomplete bounds.\n";
            continue;
        }
        Rational lowerRat = Rational(*inferred.first.getValue()) / Rational(coeff);
        Rational upperRat = Rational(*inferred.second.getValue()) / Rational(coeff);
        Rational minRat = (lowerRat < upperRat) ? lowerRat : upperRat;
        Rational maxRat = (lowerRat > upperRat) ? lowerRat : upperRat;

        Integer inferredLower = minRat.ceiling();
        Integer inferredUpper = maxRat.floor();

        Bound newLower(inferredLower);
        Bound newUpper(inferredUpper);
        auto& current = Bounds[targetVar.getName()];
        Bound& curLower = current.first;
        Bound& curUpper = current.second;

        Trace("trace-tighten-bds") << "  - Inferred bounds for " << targetVar
                                   << ": [" << inferredLower << ", " << inferredUpper << "]\n";

        // Check contradiction before update
        if (!newLower.isInfinite() && !newUpper.isInfinite() && inferredLower > inferredUpper) {
          Trace("trace-tighten-bds") << "  - Contradiction! inferred lower > upper for " << targetVar << "\n";
          return Result::UNSAT;
        }

        bool updated = false;

        // Lower bound update
        if (!newLower.isInfinite()) {
          if (curLower.isInfinite() || *newLower.getValue() > *curLower.getValue()) {
            curLower.setTo(newLower);
            updated = true;
            Trace("trace-tighten-bds") << "  - Updated lower bound of " << targetVar << " to " << *newLower.getValue() << "\n";
          }
        }

        // Upper bound update
        if (!newUpper.isInfinite()) {
          if (curUpper.isInfinite() || *newUpper.getValue() < *curUpper.getValue()) {
            curUpper.setTo(newUpper);
            updated = true;
            Trace("trace-tighten-bds") << "  - Updated upper bound of " << targetVar << " to " << *newUpper.getValue() << "\n";
          }
        }

        if (!curLower.isInfinite() && !curUpper.isInfinite() &&
            *curLower.getValue() > *curUpper.getValue()) {
          Trace("trace-tighten-bds") << "  - Contradiction after update for " << targetVar << "\n";
          return Result::UNSAT;
        }

        if (updated) {
          updatedVars.insert(targetVar);
          updateCounts[targetVar]++;
          newEqSinceGB = true;
          changedThisRound = true;

          if (!curLower.isInfinite() && !curUpper.isInfinite() &&
              *curLower.getValue() == *curUpper.getValue()) {
            Node eqNode = nm->mkNode(Kind::EQUAL, targetVar, nm->mkConstInt(*curLower.getValue()));
            Trace("trace-tighten-bds") << "  - Bound collapsed to point: adding equality " << eqNode << "\n";
            reduceAddEquality(eqNode);
          }
        }
      }
    }

    if (!changedThisRound) {
      Trace("trace-tighten-bds") << "No changes in round " << round << ", stopping\n";
      break;
    }

    varsToProcess = updatedVars;
  }

  Trace("trace-tighten-bds") << "Finished tightenBounds\n";
  return Result::UNKNOWN;
}






}  // namespace nl
}  // namespace arith
} // namespace modular
} // namespace cvc5::internal