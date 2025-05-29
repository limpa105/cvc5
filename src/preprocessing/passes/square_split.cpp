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
 * parse (x)(x-1)
 */

#include "preprocessing/passes/square_split.h"

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

Node mkDisjunction(NodeManager* nm, Node x)
{
  return nm->mkNode(Kind::OR,
                    nm->mkNode(Kind::EQUAL, x, nm->mkConstInt(0)),
                    nm->mkNode(Kind::EQUAL, x, nm->mkConstInt(1)));
}

bool isXTimesXMinus1(Node n, Node& x)
{
  // Match: (x * (x - 1)) or ((x - 1) * x)
  if (n.getKind() == Kind::MULT && n.getNumChildren() == 2)
  {
    Node a = n[0], b = n[1];
    if (a.getKind() == Kind::VARIABLE && b.getKind() == Kind::SUB &&
        b.getNumChildren() == 2 && b[0] == a &&
        b[1].isConst() && b[1].getConst<Rational>().getNumerator() == 1)
    {
      x = a;
      return true;
    }
    if (b.getKind() == Kind::VARIABLE && a.getKind() == Kind::SUB &&
        a.getNumChildren() == 2 && a[0] == b &&
        a[1].isConst() && a[1].getConst<Rational>().getNumerator() == 1)
    {
      x = b;
      return true;
    }
  }

  // Match: (+ (* -1 x) (* x x)) or (+ (* x x) (* -1 x))
  if (n.getKind() == Kind::ADD && n.getNumChildren() == 2)
  {
    for (int i = 0; i < 2; ++i)
    {
      Node neg = n[i];
      Node sqr = n[1 - i];
      if (neg.getKind() == Kind::MULT && neg.getNumChildren() == 2 &&
          neg[0].isConst() && neg[0].getConst<Rational>() == -1 &&
          neg[1].isVar() &&
          sqr.getKind() == Kind::NONLINEAR_MULT && sqr.getNumChildren() == 2 &&
          sqr[0].isVar() && sqr[1].isVar() &&
          sqr[0] == sqr[1] &&
          sqr[0] == neg[1])
      {
        x = neg[1];
        return true;
      }
    }
  }

  return false;
}



SquareSplit::SquareSplit(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "square-split")
{



}

//  assertionsToPreprocess->replace(mainNode.second, replacement);

PreprocessingPassResult SquareSplit::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm =  nodeManager();
  //std::vector<std::tuple<uint64_t, Node, Node, Rational>> modCandidates;
  std::unordered_map<Node, std::vector<std::pair<uint64_t, Integer>>> modCandidates;
  std::unordered_map<Node, std::vector<std::pair<uint64_t, Node>>> modDeferred;

  // Pass 1 Detect square roots
  for (uint64_t i = 0, n = assertionsToPreprocess->size(); i < n; ++i)
  {
    Node assertion = (*assertionsToPreprocess)[i];
     Trace("square-split") << "Assertion: " << assertion << "\n";
    
    if (assertion.getKind() == Kind::EQUAL &&
            assertion[0].getType().isBoolean() &&
            assertion[1].getKind() == Kind::EQUAL)
            {
            assertion = assertion[1];
            }

    if (assertion.getKind() == Kind::EQUAL &&
        assertion[0].getKind() == Kind::CONST_INTEGER &&
        assertion[0].getConst<Rational>().isZero()){
            assertion = nm->mkNode(Kind::EQUAL, assertion[1], assertion[0]);
        }
  
    if (assertion.getKind() == Kind::EQUAL &&
        assertion[1].getKind() == Kind::CONST_INTEGER &&
        assertion[1].getConst<Rational>().isZero())
    {
      //std::cout << assertion[0].getKind() << "\n";
      Node lhs = assertion[0];
      // Simple (x * (x - 1)) = 0
      if (lhs.getKind() == Kind::MULT || lhs.getKind() == Kind::ADD)
      {
        Node x;
        if (isXTimesXMinus1(lhs, x))
        {
          assertionsToPreprocess->replace(i, mkDisjunction(nm, x));
          Trace("square-split") << "Replacing assertion at index " << i << ":\n"
                      << "  Old: " << assertion << "\n"
                      << "  New: " << mkDisjunction(nm, x) << "\n";
        }
      }
    // Moduli (x * (x - 1)) mod p = 0
      else if ((lhs.getKind() == Kind::INTS_MODULUS || lhs.getKind() == Kind::INTS_MODULUS_TOTAL)  &&
               (lhs[0].getKind() == Kind::MULT || lhs[0].getKind()== Kind::ADD)) //&&
               //lhs[1].getKind() == Kind::CONST_INTEGER   && lhs[1].getConst<Rational>().getNumerator().isProbablePrime())
      {
        //std::cout << "LOOK HERE" << assertion << "\n";
        Node x;
        //Node modNode = lhs[1]
        if (isXTimesXMinus1(lhs[0], x))
        {
            //std::cout << "PASSED" << assertion << "\n";
            if(lhs[1].getKind() == Kind::CONST_INTEGER   && lhs[1].getConst<Rational>().getNumerator().isProbablePrime()){
                modCandidates[x].emplace_back(i, lhs[1].getConst<Rational>().getNumerator());
            }
            if (lhs[1].getKind() == Kind::VARIABLE) {
                //std::cout << "We should've pushed something\n";
                modDeferred[x].emplace_back(i, lhs[1]);
            }
        }
      }
    }
  }
  // Pass 2 if modCandidates size is bigger than 
  if (modDeferred.size() > 0 || modCandidates.size()>0){
    std::unordered_map<Node, bool> hasLower, hasUpper;
    std::vector<Node> clauses;
    for (uint64_t i = 0, n = assertionsToPreprocess->size(); i < n; ++i)
    {
        Node a = (*assertionsToPreprocess)[i];
        if (a.getKind() == Kind::AND){
            for (int j = 0; j< a.getNumChildren(); j++){
                clauses.push_back(a[j]);
            }
        }
    }
    for (Node a : clauses){
        //Node a = (*assertionsToPreprocess)[i];
        Node kindNode = a;
        bool isNegated = false;
        if (a.getKind() == Kind::NOT && a[0].getKind() != Kind::NOT)
        {
        kindNode = a[0];
        isNegated = true;
        }
        Node clause = a;
        // symbolic case 
        if (clause.getKind() == Kind::GEQ &&
            clause[0].getKind() == Kind::ADD &&
            clause[0].getNumChildren() == 2 &&
            clause[1].isConst() &&
            clause[1].getConst<Rational>() >= 1 &&
            ((clause[0][0].isVar() &&
            clause[0][1].getKind() == Kind::MULT &&
            clause[0][1].getNumChildren() == 2 &&
            clause[0][1][0].isConst() &&
            clause[0][1][0].getConst<Rational>() == -1 &&
            clause[0][1][1].isVar()) ||
            (clause[0][1].isVar() &&
            clause[0][0].getKind() == Kind::MULT &&
            clause[0][0].getNumChildren() == 2 &&
            clause[0][0][0].isConst() &&
            clause[0][0][0].getConst<Rational>() == -1 &&
            clause[0][0][1].isVar())))
        {
            Node xVar = clause[0][1].getKind() == Kind::MULT ? clause[0][1][1] : clause[0][0][1];
            Node pVar = clause[0][0].isVar() ? clause[0][0] : clause[0][1];
            if (modDeferred.find(xVar) != modDeferred.end())
            {
            for (const auto& [_, mod] : modDeferred[xVar])
            {
                if (pVar.getName() == mod.getName())
                {
                hasUpper[xVar] = true;
                }
            }
            } 
            break;
            // pattern matched: xVar is bounded by pVar symbolically
        }

        if ((kindNode.getKind() != Kind::GEQ && kindNode.getKind() != Kind::GT &&
            kindNode.getKind() != Kind::LT && kindNode.getKind() != Kind::LEQ) ||
            !kindNode[0].isVar() || !kindNode[1].isConst())
        {
        continue;
        }

        Node var = kindNode[0];
        Integer r = kindNode[1].getConst<Rational>().getNumerator();
        Kind k = kindNode.getKind();

        // Flip sense if negated
        if (isNegated)
        {
        switch (k)
        {
            case Kind::GEQ: k = Kind::LT; break;
            case Kind::GT:  k = Kind::LEQ; break;
            case Kind::LEQ: k = Kind::GT; break;
            case Kind::LT:  k = Kind::GEQ; break;
            default: break;
        }
        }

        switch (k)
        {
        case Kind::GEQ:
            if (r <= 0) hasLower[var] = true;

            break;
        case Kind::GT:
            if (r < 0) hasLower[var] = true;
            break;
        case Kind::LT:
        case Kind::LEQ:
            if (modCandidates.find(var) != modCandidates.end())
            {
            for (const auto& [_, mod] : modCandidates[var])
            {
                if ((k == Kind::LT && r >= mod) || (k == Kind::LEQ && r > mod))
                {
                hasUpper[var] = true;
                }
            }
            } 
            break;
        default: break;
        }
    }

  // Pass 3 make the assertions 
  for (const auto& [x, vec] : modCandidates)
    {
        Trace("square-split") << "Regular mod " << x << "\n";
    if (!(hasLower[x] && hasUpper[x])){
        continue;
    }
      Trace("square-split") << "passed! " << x << "\n";

        for (const auto& [i, _] : vec)
        {
            
          Trace("square-split") << "Replacing assertion at index " << i << ":\n"
                      << "  Old: " <<  (*assertionsToPreprocess)[i] << "\n"
                       << "  New: " << mkDisjunction(nm, x) << "\n";
       assertionsToPreprocess->push_back(mkDisjunction(nm, x));
        }
    }
   // }
// std::cout << "looking at deferred\n";
// for (const auto& [x, vec] : modDeferred)
// {
//      Trace("square-split") << "DEFFERED " << x << "\n";
//   if (!hasLower.count(x) || !hasUpper.count(x)) continue;

//   for (const auto& [idx, p] : vec)
//   {
//     Integer val; // Explicitly a Rational
//     bool foundAssignment = false;

//     // Look for: (= p const)
//     for (uint64_t j = 0, m = assertionsToPreprocess->size(); j < m; ++j)
//     {
//       Node a = (*assertionsToPreprocess)[j];
//       if (a.getKind() == Kind::EQUAL && a[0] == p && a[1].isConst())
//       {
//         val = a[1].getConst<Rational>().getNumerator();
//         foundAssignment = true;
//         break;
//       }
//     }

//     if (foundAssignment && val.isProbablePrime())
//     {
//         Trace("square-split") << "huh " << x << "\n";
//          Trace("square-split") << "Replacing assertion at index " << idx << ":\n"
//                       << "  Old: " <<  (*assertionsToPreprocess)[idx] << "\n"
//                       << "  New: " << mkDisjunction(nm, x) << "\n";
//       assertionsToPreprocess->replace(idx, mkDisjunction(nm, x));
//     }
//   }
// }

  }         
   
 return PreprocessingPassResult::NO_CONFLICT;

}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal