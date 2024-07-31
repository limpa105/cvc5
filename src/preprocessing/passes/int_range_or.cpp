/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * parse ff bitsums
 */

#include "preprocessing/passes/int_range_or.h"

// external includes

// std includes
#include <unordered_set>
#include <algorithm>

// internal includes
#include "expr/algorithm/flatten.h"
#include "expr/node_traversal.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/arith/arith_utilities.h"
#include "util/integer.h"



namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace cvc5::internal::theory::arith;
using namespace cvc5::internal;

IntRangeOr::IntRangeOr(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "int-range-or")
{
}


PreprocessingPassResult IntRangeOr::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // collect bits
  std::unordered_set<Node> bits;
  std::map<Node, std::set<Node>> rangeNodes;
  std::map<Node, uint64_t> orNodes;
  auto nm = NodeManager::currentNM();

  for (uint64_t i = 0, n = assertionsToPreprocess->size(); i < n; ++i)
  {
    Node assertion = (*assertionsToPreprocess)[i];
    std::cout << assertion << "\n";
    if ((assertion.getKind() == Kind::EQUAL || 
            assertion.getKind() == Kind::GEQ ||
            assertion.getKind() == Kind::LEQ) 
            && assertion[0].getKind() == Kind::VARIABLE && 
            assertion[1].getKind() == Kind::CONST_INTEGER){
                rangeNodes[assertion[0]].insert(assertion);
    }
    //TODO: NOT SOUND FIX LATER!
    if (assertion.getKind() == Kind::AND) {
        for (int j= 0; j<assertion.getNumChildren(); j++){
            Node child = assertion[j];
            std::cout << "CHILD" << child << "\n";
        if ((child.getKind() == Kind::EQUAL || 
            child.getKind() == Kind::GEQ ||
            child.getKind() == Kind::LEQ) 
            && child[0].getKind() == Kind::VARIABLE && 
            child[1].getKind() == Kind::CONST_INTEGER){
                rangeNodes[child[0]].insert(assertion);
            }
        }
    }
    if (assertion.getKind() == Kind::OR) {
        // Check that all children are the same varible
        Node MainVar;
        std::vector<Integer> missing ={};
        Node replacement;
        if (assertion[0][0].getKind() != Kind::VARIABLE){
            continue;
        } else {
            MainVar = assertion[0][0];
        }
        std::vector<Integer> ranges;
        for (int k = 0; k<assertion.getNumChildren(); k++) {
            if (assertion[k].getKind()!= Kind::EQUAL ||
                assertion[k][0] != MainVar ||
                 assertion[k][1].getKind() != Kind::CONST_INTEGER)
                 {
            if (assertion[k].getKind() == Kind::EQUAL &&
                ((assertion[k][0] == MainVar &&
                assertion[k][1].getKind() == Kind::VARIABLE) ||
                (assertion[k][1] == MainVar &&
                assertion[k][0].getKind() == Kind::VARIABLE)
                )){
                    std::cout << MainVar << "ADDED\n"; 
                    orNodes[MainVar] = i;
                    
            }
                    goto end;
            }
            ranges.push_back(assertion[k][1].getConst<Rational>().getNumerator());
        }
        std::sort(ranges.begin(), ranges.end());
        for (size_t j = 0; j < ranges.size() - 1; j++) {
        Integer current = ranges[j];
        std::cout << "Current" << current << "\n";
        Integer next = ranges[j + 1];
        std::cout << "Next" << next << "\n";
        current+=1;
        while(current!=next){
            missing.push_back(current);
            std::cout << "Current_loop:" << current << "\n";
            current+=1;
        }
        }
        std::cout << "Finished this loop\n";
        std::cout << ranges[0] << "\n";
        std::cout << ranges[ranges.size()-1] << "\n";
        std::cout << MainVar << "\n";
        replacement = nm->mkNode(
            Kind::AND,
            nm->mkNode(Kind::GEQ, MainVar, nm->mkConstInt(ranges[0])),
            nm->mkNode(Kind::LEQ, MainVar, nm->mkConstInt(ranges[ranges.size()-1]))
        );
        rangeNodes[MainVar].insert(nm->mkNode(Kind::GEQ, MainVar, nm->mkConstInt(ranges[0])));
        rangeNodes[MainVar].insert(nm->mkNode(Kind::LEQ, MainVar, nm->mkConstInt(ranges[ranges.size()-1])));
        std::cout << "Replacement" << replacement << "\n";
        assertionsToPreprocess->replace(i, replacement);
        std::cout << "Failed to replace?\n";
        if(missing.size()>0){
            for(Integer h: missing){
             std::cout << "Starting missing" << h << "\n";
            assertionsToPreprocess->push_back(
                nm->mkNode(Kind::NOT,
                nm->mkNode(Kind::EQUAL, MainVar, nm->mkConstInt(h))));
                std::cout << "Added missing" << "\n";
            }
        }    
end:
    continue;
  }
}
  if (orNodes.size()>0){
    for(auto mainNode: orNodes){
        std::vector<Integer> ranges;
        std::vector<Integer> missing;
        Node replacement;
        Node MainVar = mainNode.first;
        Node assertion = (*assertionsToPreprocess)[mainNode.second];
        for (int k = 0; k<assertion.getNumChildren(); k++) {
            if (assertion[k].getKind()!= Kind::EQUAL ||

              ( ( assertion[k][0] != mainNode.first ||
                 ( assertion[k][1].getKind() != Kind::CONST_INTEGER &&
                assertion[k][1].getKind() != Kind::VARIABLE )) 
                &&
                ( assertion[k][1] != mainNode.first ||
                 ( assertion[k][0].getKind() != Kind::CONST_INTEGER &&
                assertion[k][0].getKind() != Kind::VARIABLE )))){
                    std::cout << "FAILED FIRSt" << assertion[k] << "\n";
                    goto end2;
                }
            if (assertion[k][1].getKind() == Kind::CONST_INTEGER){
                    ranges.push_back(assertion[k][1].getConst<Rational>().getNumerator());
            } else {
                if (rangeNodes.count(assertion[k][1])> 0){
                    for (auto fact: rangeNodes[assertion[k][1]]){
                        ranges.push_back(fact[1].getConst<Rational>().getNumerator());
                    }
                }
                else if(rangeNodes.count(assertion[k][0])> 0){
                    for (auto fact: rangeNodes[assertion[k][0]]){
                        ranges.push_back(fact[1].getConst<Rational>().getNumerator());
                    }
                }
                else {
                    std::cout << "FAILED sECOND" << assertion[k] << "\n";
                    goto end2;
                }

            }
        std::sort(ranges.begin(), ranges.end());
        for (size_t j = 0; j < ranges.size() - 1; j++) {
        Integer current = ranges[j];
        std::cout << "Current" << current << "\n";
        Integer next = ranges[j + 1];
        std::cout << "Next" << next << "\n";
        current+=1;
        while(current!=next){
            missing.push_back(current);
            std::cout << "Current_loop:" << current << "\n";
            current+=1;
        }
        }
        std::cout << "Finished this loop\n";
        std::cout << ranges[0] << "\n";
        std::cout << ranges[ranges.size()-1] << "\n";
        replacement = nm->mkNode(
            Kind::AND,
            nm->mkNode(Kind::GEQ, MainVar, nm->mkConstInt(ranges[0])),
            nm->mkNode(Kind::LEQ, MainVar, nm->mkConstInt(ranges[ranges.size()-1]))
        );
        std::cout << "Replacement" << replacement << "\n";
        assertionsToPreprocess->replace(mainNode.second, replacement);
        std::cout << "Failed to replace?\n";
        if(missing.size()>0){
            for(Integer h: missing){
             std::cout << "Starting missing" << h << "\n";
            assertionsToPreprocess->push_back(
                nm->mkNode(Kind::NOT,
                nm->mkNode(Kind::EQUAL, MainVar, nm->mkConstInt(h))));
                std::cout << "Added missing" << "\n";
            }    

        }
end2:
    continue;
  }
}
}
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
