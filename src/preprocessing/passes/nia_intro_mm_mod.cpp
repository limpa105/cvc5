/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Liana Hadarean, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The BvIntroPow2 preprocessing pass.
 *
 * Traverses the formula and applies the IsPowerOfTwo rewrite rule. This
 * preprocessing pass is particularly useful on QF_BV/pspace benchmarks and
 * can be enabled via option `--bv-intro-pow2`.
 */

#include "preprocessing/passes/nia_intro_mm_mod.h"

#include <unordered_map>

#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "util/integer.h"
#include "util/rational.h"
#include "expr/mm_mod_converter.h"


namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using NodeMap = std::unordered_map<Node, Node>;
using namespace cvc5::internal::theory;

NIAIntroMmMod::NIAIntroMmMod(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "nia-intro-mm-mod"){};

PreprocessingPassResult NIAIntroMmMod::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = nodeManager();
  MmModNodeConverter d_converter = MmModNodeConverter(nm);

  //std::unordered_map<Node, Node> cache;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node cur = (*assertionsToPreprocess)[i];
    Node res = d_converter.convert(cur);
    if (res != cur)
    {
      res = rewrite(res);
      assertionsToPreprocess->replace(i, res);
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}



}  // namespace passes
}  // namespace preprocessing

}  // namespace cvc5::internal
