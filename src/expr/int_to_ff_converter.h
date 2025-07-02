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
#include "cvc5_private.h"

#ifndef CVC5__EXPR__INT_TO_FF_CONVERTER_H
#define CVC5__EXPR__INT_TO_FF_CONVERTER_H

#include <unordered_set>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "util/integer.h"

namespace cvc5::internal {

class IntToFFNodeConverter : public NodeConverter
{
 public:
  IntToFFNodeConverter(NodeManager* nm, const Integer& modulus, bool forceIdem = false);

  Node postConvert(Node n) override;

 private:
  Integer d_modulus;
};


}  // namespace cvc5::internal

#endif