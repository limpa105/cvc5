
#include "theory/arith/nl/modular_ext/utils.h"
// external includes
#include <CoCoA/BigIntOps.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <cmath>
// std includes
#include <iostream>
#include "util/rational.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
bool isVariableOrSkolem(Node node) {
    return (node.getKind() == Kind::VARIABLE || node.getKind() == Kind::SKOLEM);
}

bool isFfLeaf(const Node& n)
{
  return 
         !(n.getKind() == Kind::ADD
              || n.getKind() == Kind::MULT
              || n.getKind() == Kind::NONLINEAR_MULT
              || n.getKind() == Kind::NEG
              || n.getKind() == Kind::EQUAL
              || n.getKind() == Kind::NOT);
}

bool isFfTerm(const Node& n) { return true; }

bool isFfFact(const Node& n)
{
  return (n.getKind() == Kind::EQUAL)
         || (n.getKind() == Kind::NOT); //&& n[0].getKind() == Kind::EQUAL);
}

std::optional<Scalar> cocoaEval(Poly poly, const PartialPoint& values)
{
  CoCoA::ring coeffs = CoCoA::CoeffRing(CoCoA::owner(poly));
  Scalar out = CoCoA::zero(coeffs);
  for (auto it = CoCoA::BeginIter(poly), end = CoCoA::EndIter(poly); it != end;
       ++it)
  {
    Scalar term = CoCoA::coeff(it);
    std::vector<CoCoA::BigInt> exponents;
    CoCoA::BigExponents(exponents, CoCoA::PP(it));
    for (size_t i = 0, n = exponents.size(); i < n; ++i)
    {
      if (!CoCoA::IsZero(exponents[i]))
      {
        if (!values[i].has_value())
        {
          return {};
        }
        term *= CoCoA::power(*values[i], exponents[i]);
      }
    }
    out += term;
  }
  return {out};
}

Scalar cocoaEval(Poly poly, const Point& values)
{
  CoCoA::ring coeffs = CoCoA::CoeffRing(CoCoA::owner(poly));
  Scalar out = CoCoA::zero(coeffs);
  for (auto it = CoCoA::BeginIter(poly), end = CoCoA::EndIter(poly); it != end;
       ++it)
  {
    Scalar term = CoCoA::coeff(it);
    std::vector<CoCoA::BigInt> exponents;
    CoCoA::BigExponents(exponents, CoCoA::PP(it));
    for (size_t i = 0, n = exponents.size(); i < n; ++i)
    {
      if (!CoCoA::IsZero(exponents[i]))
      {
        term *= CoCoA::power(values[i], exponents[i]);
      }
    }
    out += term;
  }
  return out;
}


CoCoA::BigInt intToCocoa(const Integer& i)
{
  return CoCoA::BigIntFromString(i.toString());
}

std::vector<std::vector<long>> grevlexWeighted(std::vector<long> weights){
  int numRows = 1;
  int numColumns = weights.size();
  int grevColumns = numColumns - numRows;
  std::vector<std::vector<long>> finalMatrix(grevColumns, std::vector<long>(numColumns, 0));
  for (int i =0; i<grevColumns; ++i){
    for (int j = 0; j<numColumns; ++j){
      if (i+j < grevColumns){
        finalMatrix[i][j] = 1;
      }
      else {
        finalMatrix[i][j] = 0;
    }
  }
  }
  finalMatrix.insert(finalMatrix.begin(),weights);
  return finalMatrix;
}


std::optional<std::pair<Bound,Bound>> getBounds(Node fact, Integer new_field, std::map<std::string, std::pair<Bound, Bound> > Bounds, bool ineq=false){
   if (isVariableOrSkolem(fact))
  {
    auto it = Bounds.find(fact.getName());
    if (it != Bounds.end())
    {
      return it->second;
    }
    AlwaysAssert(false) << "No bounds found for " << fact.getName();
    return std::nullopt;
  }

  // Constant
  if (fact.getKind() == Kind::CONST_INTEGER)
  {
    Integer coef = fact.getConst<Rational>().getNumerator();
    Bound b(coef);
    if (!ineq && new_field.divides(coef))
    {
      Bound zero(Integer(0));
      return std::make_pair(zero, zero);
    }
    return std::make_pair(b, b);
  }

  // Multiplication
  if (fact.getKind() == Kind::MULT || fact.getKind() == Kind::NONLINEAR_MULT)
  {
    Bound one(Integer(1));
    Bound minProd = one;
    Bound maxProd = one;

    for (int i = 0; i < fact.getNumChildren(); ++i)
    {
      auto childBoundsOpt = getBounds(fact[i], new_field, Bounds, ineq);
      if (!childBoundsOpt.has_value())
      {
        return std::nullopt;
      }

      Bound a = childBoundsOpt->first;
      Bound b = childBoundsOpt->second;

      if (a.isInfinite() || b.isInfinite() ||
          !a.getValue().has_value() || !b.getValue().has_value())
      {
        return std::nullopt;
      }

      Integer a1 = a.getValue().value();
      Integer a2 = b.getValue().value();

      std::vector<Integer> products = {
          minProd.getValue().value() * a1,
          minProd.getValue().value() * a2,
          maxProd.getValue().value() * a1,
          maxProd.getValue().value() * a2};

      Integer newMin = *std::min_element(products.begin(), products.end());
      Integer newMax = *std::max_element(products.begin(), products.end());

      minProd = Bound(newMin);
      maxProd = Bound(newMax);
    }

    return std::make_pair(minProd, maxProd);
  }

  // Addition
  AlwaysAssert(fact.getKind() == Kind::ADD) << fact;
  Integer sumMin(0), sumMax(0);
  for (int i = 0; i < fact.getNumChildren(); ++i)
  {
    auto childBoundsOpt = getBounds(fact[i], new_field, Bounds, ineq);
    if (!childBoundsOpt.has_value())
    {
      return std::nullopt;
    }

    Bound a = childBoundsOpt->first;
    Bound b = childBoundsOpt->second;

    if (a.isInfinite() || b.isInfinite() ||
        !a.getValue().has_value() || !b.getValue().has_value())
    {
      return std::nullopt;
    }

    sumMin += a.getValue().value();
    sumMax += b.getValue().value();
  }

  return std::make_pair(Bound(sumMin), Bound(sumMax));
}


 bool checkIfConstraintIsMet(
    Node equality,
    Integer modulos,
    std::map<std::string, std::pair<Bound, Bound>> Bounds,
    bool ineq)
{
  auto lhsOpt = getBounds(equality[0], modulos, Bounds, ineq);
  if (!lhsOpt.has_value())
  {
    return false;
  }

  auto rhsOpt = getBounds(equality[1], modulos, Bounds, ineq);
  if (!rhsOpt.has_value())
  {
    return false;
  }

  const Bound& lhsMin = lhsOpt->first;
  const Bound& lhsMax = lhsOpt->second;
  const Bound& rhsMin = rhsOpt->first;
  const Bound& rhsMax = rhsOpt->second;

  if (lhsMin.isInfinite() || lhsMax.isInfinite() ||
      rhsMin.isInfinite() || rhsMax.isInfinite() ||
      !lhsMin.getValue().has_value() || !lhsMax.getValue().has_value() ||
      !rhsMin.getValue().has_value() || !rhsMax.getValue().has_value())
  {
    return false;
  }

  Integer upper = lhsMax.getValue().value() - rhsMin.getValue().value();
  Integer lower = lhsMin.getValue().value() - rhsMax.getValue().value();

  if (lower.abs() >= modulos || upper.abs() >= modulos)
  {
    return false;
  }

  return true;
}

void collectVars(const Node& t, std::unordered_set<Node>& vars)
{
  if (t.isVar())
  {
    vars.insert(t);
  }
  else
  {
    for (const Node& child : t)
    {
      collectVars(child, vars);
    }
  }
}


std::vector<long> boundsToWeights(std::vector<CoCoA::symbol>& vars,
                                  std::map<std::string, std::pair<Bound, Bound>>& bounds) {
    std::vector<long> weights;

    for (CoCoA::symbol& sym : vars) {
        std::string var = extractStr(sym);
        auto it = bounds.find(var);
        if (it == bounds.end()) {
            // No bound info — use default
            weights.push_back(1);
            continue;
        }

         Bound& b1 = it->second.first;
         Bound& b2 = it->second.second;

        if (b1.isInfinite() || b2.isInfinite() ||
            !b1.getValue().has_value() || !b2.getValue().has_value()) {
            weights.push_back(LONG_MAX);
        } else {
            Integer abs1 = b1.getValue().value().abs();
            Integer abs2 = b2.getValue().value().abs();
            Integer max = (abs1 > abs2) ? abs1 : abs2;
            auto dbg = max.getLong();
            long weight = static_cast<long>(std::log(dbg) * 10.0);
            weights.push_back(weight > 0 ? weight : 1);
        }
    }

    return weights;
}


Node replaceMMMod(Node exp, NodeManager* nm){
    if (exp.getKind() == Kind::MM_MOD){
        return nm->mkNode(Kind::INTS_MODULUS_TOTAL, exp[0], exp[1]);
    }
    if (exp.getNumChildren() == 0) {
        return exp;
    }
    std::vector<Node> exps;
    for (int i=0; i<exp.getNumChildren(); i ++){
        exps.push_back(replaceMMMod(exp[i], nm));
    }
    return nm->mkNode(exp.getKind(), exps);
}


}
}
}
}