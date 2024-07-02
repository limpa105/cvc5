/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * parsing Singular output
 */

#include "theory/ff/singular_parse.h"

// external includes

// std includes
#include <cctype>
#include <string>

// internal includes
#include "theory/ff/util.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace ff {
namespace singular {

// anonymous namespace for file-local function
namespace {

uint32_t safeStringToUint32(std::string_view s)
{
  for (const char& c : s)
  {
    AlwaysAssert(std::isdigit(c)) << "Non digit char " << c << " in: " << s;
  }
  AlwaysAssert(s.size() > 0) << "empty integer";
  return static_cast<uint32_t>(std::stoul(std::string(s)));
}

Integer safeStringToUinteger(std::string_view s)
{
  for (const char& c : s)
  {
    AlwaysAssert(std::isdigit(c)) << "Non digit char " << c << " in: " << s;
  }
  AlwaysAssert(s.size() > 0) << "empty integer";
  return Integer(std::string(s));
}

}  // namespace

Var::Var(Name&& name_) : name(name_), indices() {}

Var::Var(Name&& name_, std::vector<Index>&& indices_)
    : name(name_), indices(indices_)
{
}

Var Var::parse(std::string_view s)
{
  size_t startP = s.find('(');
  Name name = std::string(s.substr(0, startP));
  for (const char& c : name)
  {
    AlwaysAssert(std::isalpha(c))
        << "Non alphabetic char " << c << " in: " << s;
  }
  std::vector<Index> indices;
  while (startP != std::string_view::npos)
  {
    size_t endP = s.find(")", startP);
    AlwaysAssert(endP != std::string_view::npos) << "missing ) in: " << s;
    std::string_view idxStr = s.substr(startP + 1, endP - startP - 1);
    indices.push_back(safeStringToUint32(idxStr));
    startP = s.find("(", endP);
    if (startP == std::string_view::npos)
    {
      break;
    }
    AlwaysAssert(startP = endP + 1) << "extra chars before ( in: " << s;
  }
  return Var{std::move(name), std::move(indices)};
}

bool Var::operator==(const Var& rhs) const
{
  return std::tie(name, indices) == std::tie(rhs.name, rhs.indices);
}

VarPower VarPower::parse(std::string_view s)
{
  Power power = 1;
  std::string_view varStr = s;
  size_t caretIdx = s.find("^");
  if (caretIdx != std::string_view::npos)
  {
    varStr = s.substr(0, caretIdx);
    power = safeStringToUint32(s.substr(caretIdx + 1));
  }
  return VarPower{Var::parse(varStr), power};
}

bool VarPower::operator==(const VarPower& rhs) const
{
  return std::tie(var, power) == std::tie(rhs.var, rhs.power);
}

Monomial Monomial::parse(std::string_view s)
{
  Integer coeff{1};
  size_t start = 0, end = 0;
  if (std::isdigit(s[0]))
  {
    end = s.find("*", start);
    std::string_view coeffStr = s.substr(start, end - start);
    coeff = safeStringToUinteger(coeffStr);
    start = end + (end != std::string_view::npos);
    AlwaysAssert(end == std::string_view::npos || start < s.size())
        << "trailing * in: " << s;
  }
  std::vector<VarPower> varPowers;
  while (start < s.size())
  {
    end = s.find("*", start);
    varPowers.push_back(VarPower::parse(s.substr(start, end - start)));
    start = end + (end != std::string_view::npos);
  }
  return Monomial{std::move(coeff), std::move(varPowers)};
}

bool Monomial::operator==(const Monomial& rhs) const
{
  return std::tie(coeff, varPowers) == std::tie(rhs.coeff, rhs.varPowers);
}

Polynomial Polynomial::parse(std::string_view s)
{
  Polynomial poly;
  size_t start = 0, end = 0;
  while (start < s.size())
  {
    end = s.find_first_of("+-", start);
    poly.monomials.push_back(Monomial::parse(s.substr(start, end - start)));
    if (start > 0 && s[start - 1] == '-')
    {
      poly.monomials.back().coeff *= -1;
    }
    start = end + (end != std::string_view::npos);
  }
  return poly;
}

bool Polynomial::operator==(const Polynomial& rhs) const
{
  return monomials == rhs.monomials;
}

std::ostream& operator<<(std::ostream& o, const Var& v)
{
  o << v.name;
  for (const auto& i : v.indices)
  {
    o << "(" << i << ")";
  }
  return o;
}

std::ostream& operator<<(std::ostream& o, const VarPower& v)
{
  o << v.var;
  if (v.power != 1)
  {
    o << "^" << v.power;
  }
  return o;
}

std::ostream& operator<<(std::ostream& o, const Monomial& v)
{
  if (!v.coeff.isOne())
  {
    o << v.coeff << "*";
  }
  for (size_t i = 0, n = v.varPowers.size(); i < n; ++i)
  {
    o << v.varPowers[i];
    if (i + 1 < n)
    {
      o << "*";
    }
  }
  return o;
}

std::ostream& operator<<(std::ostream& o, const Polynomial& v)
{
  AlwaysAssert(v.monomials[0].coeff > 0);
  o << v.monomials[0];
  for (size_t i = 1, n = v.monomials.size(); i < n; ++i)
  {
    if (v.monomials[i].coeff > 0)
    {
      o << "+" << v.monomials[i];
    }
    else
    {
      o << v.monomials[i];
    }
  }
  return o;
}

std::ostream& operator<<(std::ostream& o, const std::vector<Polynomial>& v)
{
  o << "{";
  for (size_t i = 0, n = v.size(); i < n; ++i)
  {
    if (i > 0)
    {
      o << ", ";
    }
    o << v[i];
  }
  o << "}";
  return o;
}

std::vector<Polynomial> parsePolynomialList(std::string_view s)
{
  std::vector<Polynomial> polys;
  size_t start = 0, end = 0, eq = 0;
  while (start < s.size())
  {
    end = s.find("\n", start);
    if (start != end)
    {
      eq = s.find("=", start);
      polys.push_back(Polynomial::parse(s.substr(eq + 1, end - eq - 1)));
    }
    start = end + 1;
  }
  return polys;
}

}  // namespace singular
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
