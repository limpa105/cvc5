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
 * parsing Singular output; assumes the singular ring has at least one variable
 * that has multiple characters in its name or is indexed.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__SINGULAR_PARSE_H
#define CVC5__THEORY__FF__SINGULAR_PARSE_H

// external includes

// std includes
#include <iosfwd>

// internal includes
#include "base/output.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

namespace singular {

/** A variable name */
using Name = std::string;
/** A variable index */
using Index = uint32_t;
/** A variable power */
using Power = uint32_t;

/** A variable */
struct Var
{
  /** Its name (ASCII) */
  Name name;
  /** Any indices */
  std::vector<Index> indices;
  /** index-free construction */
  Var(Name&& name_);
  /** standard construction */
  Var(Name&& name_, std::vector<Index>&& index_);
  /** Parse from a string (view) */
  static Var parse(std::string_view s);
  /** Equality */
  bool operator==(const Var& rhs) const;
};

/** A variable raised to a (non-zero, by convention) power. */
struct VarPower
{
  Var var;
  Power power;
  /** Parse from a string (view) */
  static VarPower parse(std::string_view s);
  /** Equality */
  bool operator==(const VarPower& rhs) const;
};

/** A monomial */
struct Monomial
{
  Integer coeff;
  /** A list of variable powers, by convention: no repeated variables */
  std::vector<VarPower> varPowers;
  /** Parse from a string (view) */
  static Monomial parse(std::string_view s);

  /** Equality */
  bool operator==(const Monomial& rhs) const;

  Monomial operator/(const Monomial& rhs) const;

  Monomial lcm(const Monomial& rhs);


};

/** A polynomial */
struct Polynomial
{
  std::vector<Monomial> monomials{};
  /** Parse from a string (view) */
  static Polynomial parse(std::string_view s);
  /** Equality */
  bool operator==(const Polynomial& rhs) const;

  Monomial lm();

  Integer lc();
};

/** output */
std::ostream& operator<<(std::ostream& o, const Var& v);
std::ostream& operator<<(std::ostream& o, const VarPower& v);
std::ostream& operator<<(std::ostream& o, const Monomial& v);
std::ostream& operator<<(std::ostream& o, const Polynomial& v);
std::ostream& operator<<(std::ostream& o, const std::vector<Polynomial>& v);

/** parse a list of polynomials */
std::vector<Polynomial> parsePolynomialList(std::string_view s);

}  // namespace singular

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__SINGULAR_PARSE_H */
