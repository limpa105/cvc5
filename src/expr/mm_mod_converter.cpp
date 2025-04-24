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

#include "expr/mm_mod_converter.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

Node MmModNodeConverter::postConvert(Node node)
{
    if (node.getKind() == Kind::EQUAL){
        if (node[0].getKind() == Kind::INTS_MODULUS_TOTAL &&
        node[1].getKind() == Kind::CONST_INTEGER && 
        node[1].getConst<Rational>() == Integer(0) &&
        node[0][1].getKind() == Kind::CONST_INTEGER){
            return (d_nm->mkNode(Kind::EQUAL, d_nm->mkNode(Kind::MM_MOD, node[0][0], node[0][1]), node[1]));
         }
     // 0 = x mod n for n in Z
     if (node[1].getKind() == Kind::INTS_MODULUS_TOTAL &&
        node[0].getKind() == Kind::CONST_INTEGER && 
        node[0].getConst<Rational>() == Integer(0) &&
        node[1][1].getKind() == Kind::CONST_INTEGER){
            return d_nm->mkNode(Kind::EQUAL,
                d_nm->mkNode(Kind::MM_MOD, node[1][0], node[1][1]), node[0]);

     }
     if (node[0].getKind() == Kind::INTS_MODULUS_TOTAL &&
        node[1].getKind() == Kind::INTS_MODULUS_TOTAL && 
        node[0][1].getKind() == Kind::CONST_INTEGER &&
        node[1][1].getKind() == Kind::CONST_INTEGER &&
        node[0][1].getConst<Rational>() ==  node[1][1].getConst<Rational>()
        ){
            return d_nm-> mkNode(Kind::EQUAL, 
                d_nm->mkNode(Kind::MM_MOD, d_nm->mkNode(Kind::SUB, node[0][0], node[1][1]), 
                node[0][1]), d_nm->mkConstInt(Rational(0)));
        }

    }
    return node;

    }

}  // namespace cvc5::internal