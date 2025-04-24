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

#ifndef CVC5__EXPR__MM_MOD_CONVERTER_H
#define CVC5__EXPR__MM_MOD_CONVERTER_H

#include <unordered_set>

#include "expr/node.h"
#include "expr/node_converter.h"

namespace cvc5::internal {

class MmModNodeConverter : public NodeConverter
{
 public:
  using NodeConverter::NodeConverter; // Inherit the constructor

  // Override the postConvert function
  Node postConvert(Node n) override;
};

}  // namespace cvc5::internal

#endif