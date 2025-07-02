/******************************************************************************
 * Top contributors (to current version):
 *   Elizaveta Pertseva
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of shadow elimination node conversion
 */

#include "expr/int_to_ff_converter.h"
#include "util/rational.h"
#include "expr/node.h"
#include "expr/node_converter.h"
#include "util/finite_field_value.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {


IntToFFNodeConverter::IntToFFNodeConverter(NodeManager* nm, const Integer& modulus, bool forceIdem)
  : NodeConverter(nm, forceIdem),  // Call base class constructor
    d_modulus(modulus)
{
}

Node IntToFFNodeConverter::postConvert(Node node)
{
   switch (node.getKind())
  {
     case Kind::CONST_INTEGER:
        return d_nm->mkConst(FiniteFieldValue(node.getConst<Rational>().getNumerator(),FfSize(d_modulus)) );
     case Kind::MULT:
        return d_nm->mkNode(Kind::FINITE_FIELD_MULT, node);
     case Kind::NONLINEAR_MULT:
        return d_nm->mkNode(Kind::FINITE_FIELD_MULT, node);
     case Kind::ADD:
        return d_nm->mkNode(Kind::FINITE_FIELD_ADD, node);
     case Kind::EQUAL:
        return node;
     default:
        AlwaysAssert(false) << node.getKind() << "cannot be translated into ff";
    }
}
}  // namespace cvc5::internal