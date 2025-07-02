/******************************************************************************
 * Top contributors (to current version):
 *   Elizaveta Pertseva
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The NIAIntroMmMod preprocessing pass.
 *
 * Traverses the formula and applies the IsMmMod rewrite rule. This
 * preprocessing pass is necessary to use the multi modular extension 
 * and can be enabled via option `--nia-intro-mm-mod`.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__NIA_INTRO_MM_MOD_H
#define CVC5__PREPROCESSING__PASSES__NIA_INTRO_MM_MOD_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class  NIAIntroMmMod : public PreprocessingPass
{
 public:
   NIAIntroMmMod(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;


};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__BV_INTRO_POW2_H */
