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

  for (const auto& eq : equalities) {
    std::unordered_set<Node> vars;
    collectVars(eq, vars);
    varsToProcess.insert(vars.begin(), vars.end());
  }

  while (round++ < MAX_ROUNDS && !varsToProcess.empty()) {
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

      // Case: x = c
      if (isVariableOrSkolem(lhs) && rhs.getKind() == Kind::CONST_INTEGER) {
        Integer val = rhs.getConst<Rational>().getNumerator();
        Bound b(val);
        Bounds[lhs.getName()] = std::make_pair(b, b);
        updatedVars.insert(lhs);
        newEqSinceGB = true;
        //this->novelBound = true;
        newEqSinceGB = true;
        changedThisRound = true;
        continue;
      }

      for (const auto& targetVar : eqVars) {
        if (updateCounts[targetVar] >= MAX_UPDATES_PER_VAR) continue;

        NodeManager* nm = nodeManager();
        Node offset = nm->mkNode(Kind::ADD, rhs, nm->mkNode(Kind::MULT, nm->mkConstInt(-1), lhs));
        std::pair<Node, Node> separated = separateTerms(rewrite(offset), targetVar);

        const Node& targetTerm = separated.second;
        Integer coeff = -1;

        if (targetTerm.getKind() != Kind::MULT ||
            targetTerm.getNumChildren() != 2 ||
            targetTerm[0].getKind() != Kind::CONST_INTEGER) {
          continue;
        }

        coeff *= targetTerm[0].getConst<Rational>().getNumerator();
        if (coeff == 0) continue;

        bool skip = false;
        std::unordered_set<Node> tempVars;
        collectVars(separated.first, tempVars);
        for (const auto& dep : tempVars) {
          if (dep == targetVar) {
            std::cerr << "Cycle detected on " << targetVar << ", skipping.\n";
            skip = true;
            break;
          }
          dependencyGraph[targetVar].insert(dep);
        }
        if (skip) continue;

        auto inferred = inferBoundsRecursive(separated.first, Bounds);
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

        // Check contradiction before update
        if (!newLower.isInfinite() && !newUpper.isInfinite() && inferredLower > inferredUpper) {
          return Result::UNSAT;
        }

        bool updated = false;

        // Lower bound update
        if (!newLower.isInfinite()) {
          if (curLower.isInfinite() || *newLower.getValue() > *curLower.getValue()) {
            curLower.setTo(newLower);
            updated = true;
          }
        }

        // Upper bound update
        if (!newUpper.isInfinite()) {
          if (curUpper.isInfinite() || *newUpper.getValue() < *curUpper.getValue()) {
            curUpper.setTo(newUpper);
            updated = true;
          }
        }

        // Post-update contradiction
        if (!curLower.isInfinite() && !curUpper.isInfinite() &&
            *curLower.getValue() > *curUpper.getValue()) {
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
            reduceAddEquality(eqNode);
          }
        }
      }
    }

    if (!changedThisRound) break;
    varsToProcess = updatedVars;
  }

  return Result::UNKNOWN;
}





}  // namespace nl
}  // namespace arith
} // namespace modular
} // namespace cvc5::internal