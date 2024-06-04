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
 * encoding Nodes as cocoa ring elements.
 */



#include "theory/ff/cocoa_encoder.h"


// external includes
#include <CoCoA/BigInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/RingQQ.H>
#include <CoCoA/matrix.H>
#include <CoCoA/DenseMatrix.H>
#include <CoCoA/error.H>
#include <CoCoA/PPOrdering.H>

// std includes
#include <sstream>
#include <list>
#include <algorithm>
#include <string>

// internal includes
#include "expr/node_traversal.h"
#include "theory/ff/cocoa_util.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

#define LETTER(c) (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z'))

// CoCoA symbols must start with a letter and contain only letters, numbers, and
// underscores.
//
// Our encoding is described within
CoCoA::symbol cocoaSym(const std::string& varName, std::optional<size_t> index)
{
  std::ostringstream o;
  for (const auto c : varName)
  {
    // letters and numbers as themselves
    uint8_t code = c;
    if (LETTER(c) || ('0' <= c && c <= '9'))
    {
      o << c;
    }
    // _ as __
    else if ('_' == c)
    {
      o << "__";
    }
    // other as _xXX (XX is hex)
    else
    {
      o << "_x"
        << "0123456789abcdef"[code & 0x0f]
        << "0123456789abcdef"[(code >> 4) & 0x0f];
    }
  }
  // if we're starting with something bad, prepend u__; note that the above
  // never produces __.
  std::string s = o.str();
  if (!LETTER(s[0]))
  {
    s.insert(0, "u__");
  }
  return index.has_value() ? CoCoA::symbol(s, *index) : CoCoA::symbol(s);
}

CocoaEncoder::CocoaEncoder(const FfSize& size) : FieldObj(size) {}


CoCoA::symbol CocoaEncoder::freshSym(const std::string& varName,
                                     std::optional<size_t> index)
{
  Trace("ff::cocoa::sym") << "CoCoA sym for " << varName;
  if (index.has_value())
  {
    Trace("ff::cocoa::sym") << "[" << *index << "]";
  }
  Trace("ff::cocoa::sym") << std::endl;
  Assert(d_stage == Stage::Scan);
  std::optional<size_t> suffix = {};
  CoCoA::symbol sym("dummy");
  std::string symString;
  do
  {
    std::string n = suffix.has_value()
                        ? varName + "_" + std::to_string(suffix.value())
                        : varName;
    sym = cocoaSym(n, index);
    symString = extractStr(sym);
    if (suffix.has_value())
    {
      *suffix += 1;
    }
    else
    {
      suffix = std::make_optional(0);
    }
  } while (d_vars.count(symString));
  d_vars.insert(symString);
  d_syms.push_back(sym);
  return sym;
}

void CocoaEncoder::endScan()
{
  Assert(d_stage == Stage::Scan);
  d_stage = Stage::Encode;
  d_polyRing = CoCoA::NewPolyRing(CoCoA::RingZZ(), d_syms);
  for (size_t i = 0, n = d_syms.size(); i < n; ++i)
  {
    d_symPolys.insert({extractStr(d_syms[i]), CoCoA::indet(*d_polyRing, i)});
  }
}

std::set<Node> CocoaEncoder::getCurVars(){
  std::set<Node> answer;
  for (auto i: d_syms){
    answer.insert(d_symNodes[extractStr(i)]);
  }
  return answer;
}

void CocoaEncoder::endScanIntegers(std::vector<long> upperBoundWeights){
  Assert(d_stage == Stage::Scan);
  std::cout << "Passed assert\n";
  d_stage = Stage::Encode;
  std::cout << d_syms.size() << "\n";
  std::vector<std::vector<long>> k = grevlexWeighted(upperBoundWeights);
  std::cout << "got order \n";
  CoCoA::matrix m = CoCoA::NewDenseMat(CoCoA::RingZZ(), k);
  std::cout << "Made matrix\n";
  try {
  d_polyRing = CoCoA::NewPolyRing(CoCoA::RingZZ(), d_syms, CoCoA::NewMatrixOrdering(m, d_syms.size()-1));
  } catch (const CoCoA::ErrorInfo& e) {
    std::cout << e << "\n";
    AlwaysAssert(false);
  }
  std::cout << "Made ring\n";

  for (size_t i = 0, n = d_syms.size(); i < n; ++i)
  {
    d_symPolys.insert({extractStr(d_syms[i]), CoCoA::indet(*d_polyRing, i)});
  }
  std::cout << d_polyRing.value() << "\n";
}

void CocoaEncoder::addFact(const Node& fact)
{
  Assert(isFfFact(fact));
  if (d_stage == Stage::Scan)
  {
    for (const auto& node :
         NodeDfsIterable(fact, VisitOrder::POSTORDER, [this](TNode nn) {
           return d_scanned.count(nn);
         }))
    {
      if (!d_scanned.insert(node).second)
      {
        continue;
      }
      if (isFfLeaf(node) && !node.isConst())
      {
        Trace("ff::cocoa") << "CoCoA var sym for " << node << std::endl;
        CoCoA::symbol sym = freshSym(node.getName());
        Assert(!d_varSyms.count(node));
        Assert(!d_symNodes.count(extractStr(sym)));
        d_varSyms.insert({node, sym});
        d_symNodes.insert({extractStr(sym), node});
      }
      else if (node.getKind() == Kind::NOT && isFfFact(node))
      {
        Trace("ff::cocoa") << "CoCoA != sym for " << node << std::endl;
        CoCoA::symbol sym = freshSym("diseq", d_diseqSyms.size());
        d_diseqSyms.insert({node, sym});
      }
      else if (node.getKind() == Kind::FINITE_FIELD_BITSUM)
      {
        Trace("ff::cocoa") << "CoCoA bitsum sym for " << node << std::endl;
        CoCoA::symbol sym = freshSym("bitsum", d_bitsumSyms.size());
        d_bitsumSyms.insert({node, sym});
        d_symNodes.insert({extractStr(sym), node});
      }
    }
  }
  else
  {
    Assert(d_stage == Stage::Encode);
    encodeFact(fact);
    d_polys.push_back(d_cache.at(fact));
  }
}

std::vector<Node> CocoaEncoder::bitsums() const
{
  std::vector<Node> bs;
  for (const auto& [b, _] : d_bitsumSyms)
  {
    bs.push_back(b);
  }
  return bs;
}

const Node& CocoaEncoder::symNode(CoCoA::symbol s) const
{
  Assert(d_symNodes.count(extractStr(s)));
  return d_symNodes.at(extractStr(s));
}

bool CocoaEncoder::hasNode(CoCoA::symbol s) const
{
  return d_symNodes.count(extractStr(s));
}

std::vector<std::pair<size_t, Node>> CocoaEncoder::nodeIndets() const
{
  std::vector<std::pair<size_t, Node>> out;
  for (size_t i = 0, end = d_syms.size(); i < end; ++i)
  {
    if (hasNode(d_syms[i]))
    {
      Node n = symNode(d_syms[i]);
      // skip indets for !=
      if (isFfLeaf(n))
      {
        out.emplace_back(i, n);
      }
    }
  }
  return out;
}

FiniteFieldValue CocoaEncoder::cocoaFfToFfVal(const Scalar& elem)
{
  Assert(CoCoA::owner(elem) == coeffRing());
  std::cout << size() << "\n";
  return ff::cocoaFfToFfVal(elem, size());
}

const Poly& CocoaEncoder::symPoly(CoCoA::symbol s) const
{
  Assert(d_symPolys.count(extractStr(s)));
  return d_symPolys.at(extractStr(s));
}

void CocoaEncoder::encodeTerm(const Node& t)
{
  std::cout << "Encoding::" << t << "\n";
  Assert(d_stage == Stage::Encode);

  // for all un-encoded descendents:
  for (const auto& node :
       NodeDfsIterable(t, VisitOrder::POSTORDER, [this](TNode nn) {
         return d_cache.count(nn);
       }))
  {
    // a rule must put the encoding here
    Poly elem;
    if (isFfFact(node) || isFfTerm(node))
    {
      Trace("ff::cocoa::enc") << "Encode " << node;
      // ff leaf
      if (isFfLeaf(node) && !node.isConst())
      {
        elem = symPoly(d_varSyms.at(node));
      }
      // ff.add
      else if (node.getKind() == Kind::FINITE_FIELD_ADD)
      {
        elem = CoCoA::zero(*d_polyRing);
        for (const auto& c : node)
        {
          elem += d_cache[c];
        }
      }
      // ff.mul
      else if (node.getKind() == Kind::FINITE_FIELD_MULT)
      {
        elem = CoCoA::one(*d_polyRing);
        for (const auto& c : node)
        {
          elem *= d_cache[c];
        }
      }
      // ff.bitsum
      else if (node.getKind() == Kind::FINITE_FIELD_BITSUM)
      {
        Poly sum = CoCoA::zero(*d_polyRing);
        Poly two = CoCoA::one(*d_polyRing) * 2;
        Poly twoPow = CoCoA::one(*d_polyRing);
        for (const auto& c : node)
        {
          sum += twoPow * d_cache[c];
          twoPow *= two;
        }
        elem = symPoly(d_bitsumSyms.at(node));
        d_bitsumPolys.push_back(sum - elem);
      }
      // ff constant
      else if (node.getKind() == Kind::CONST_FINITE_FIELD)
      {
        elem = CoCoA::one(*d_polyRing)
               * intToCocoa(node.getConst<FiniteFieldValue>().getValue());
      }
      // !!
      else
      {
        Unimplemented() << node;
      }
    }
    // cache the encoding
    d_cache.insert({node, elem});
  }
}

void CocoaEncoder::encodeFact(const Node& f)
{
  Assert(d_stage == Stage::Encode);
  Assert(isFfFact(f));
  // ==
  if (f.getKind() == Kind::EQUAL)
  {
    encodeTerm(f[0]);
    encodeTerm(f[1]);
    d_cache.insert({f, d_cache.at(f[0]) - d_cache.at(f[1])});
  }
  // !=
  else
  {
    encodeTerm(f[0][0]);
    encodeTerm(f[0][1]);
    Poly diff = d_cache.at(f[0][0]) - d_cache.at(f[0][1]);
    d_cache.insert({f, diff * symPoly(d_diseqSyms.at(f)) - 1});
  }
}


std::vector<long> CocoaEncoder::AddCoefToWeights(std::vector<long> weights){

}

std::vector<Node> CocoaEncoder::cocoaToNode(std::vector<CoCoA::RingElem> basis, NodeManager* nm){
  std::vector<Node> result;
  for (CoCoA::RingElem RingPolynomial: basis){
    //std::vector<Node> NodePolynomial;
    std::vector<Node> LHS;
    //LHS.push_back(nm->mkConst(0));
    std::vector<Node> RHS;
    //RHS.push_back(nm->mkConst(0));
    std::cout << RingPolynomial << "\n";
    Integer ComDenom;
    try {
     ComDenom =  Integer(extractStr(CommonDenom(RingPolynomial)));
    } catch (const CoCoA::ErrorInfo& e) {
      ComDenom = Integer(1);
    }
    //if extractStr()
    Node randVar = d_symNodes.begin()->second;
    for (CoCoA::SparsePolyIter iter=CoCoA::BeginIter(RingPolynomial); !CoCoA::IsEnded(iter); ++iter)
      {
        Integer IntCoef;
        if (extractStr(coeff(iter)).find('/') != std::string::npos){
          std::string fraction = extractStr(coeff(iter));
          size_t pos = fraction.find('/');
          std::cout << fraction.substr(0, pos) << "\n";
          Integer Overflow = ComDenom.ceilingDivideQuotient(Integer(fraction.substr(pos+1)));
          IntCoef = Integer(fraction.substr(0, pos)) * Overflow;
        } else {
          IntCoef = Integer(extractStr(coeff(iter))) * ComDenom;
        }
        bool positive = IntCoef > 0;
        if (!positive) {
          IntCoef = IntCoef *-1;
        }
        //Node randVar = d_symNodes.begin()->second;
        Node Coeff = nm->mkConst(FiniteFieldValue(IntCoef, randVar.getType().getFfSize()));
        std::cout << "coeff: " << coeff(iter)  << "\tPP: " << PP(iter)  << "\n";
        CoCoA::RingElem tempMonomial = CoCoA::monomial(d_polyRing.value(), PP(iter));
        int degree = deg(tempMonomial);
        if (degree == 0) {
          if(positive){
            LHS.push_back(Coeff);
          } else {
            RHS.push_back(Coeff);
          }
        }
        // TODO NEED TO ADD A CHECK IF ITS A CONSTANT!!!!
        else if (CoCoA::IsIndet(tempMonomial)) {
          // we just have one variable
          if(positive){
            LHS.push_back(nm->mkNode(Kind::FINITE_FIELD_MULT, Coeff, d_symNodes[extractStr(tempMonomial)]));
          } else{
            RHS.push_back(nm->mkNode(Kind::FINITE_FIELD_MULT, Coeff, d_symNodes[extractStr(tempMonomial)]));
          }
        }
        else if (IsIndetPosPower(tempMonomial)){
          // we have one variable to a power:
          size_t pos = extractStr(tempMonomial).find('^');
          std::string variable = extractStr(tempMonomial).substr(0,pos);
          Node mult =  Coeff;
          while (degree > 0){
            mult = nm->mkNode(Kind::FINITE_FIELD_MULT, mult,d_symNodes[variable]);
            degree = degree - 1;
          }
          if (positive){
            LHS.push_back(mult);
          } else {
            RHS.push_back(mult);
          }
        } else {
           // we have two or more variables :(
          std::cout << "INPUT" << extractStr(PP(iter)) << "\n";
          //int multiplication = std::count(extractStr(PP(iter)).begin(), extractStr(PP(iter)).end(), '*');
          // Currently do not support two variables and one variable to a power will change later
          std::cout << "DEGREE" << degree << "\n";
          //std::cout << "Multiplication" << multiplication << "\n";
          //AlwaysAssert(degree == multiplication);
          std::istringstream tokenStream(extractStr(PP(iter)));
          Node mult = Coeff;
          std::string token;
          while(std::getline(tokenStream, token, '*') ){
            std::cout << "We are here\n";
            if (token.find('^') != std::string::npos){ 
            std::cout << "entered x*y^2 part\n";
            std::istringstream token_ss(token);
            int count = 0;
            std::string tok;
            Node symbol;
            while (std::getline(token_ss, tok, '^')) {
              if (count == 0){
                symbol = d_symNodes[tok];
                mult = nm->mkNode(Kind::FINITE_FIELD_MULT, mult,symbol);
                count +=1;
              }
              else {
                int deg = std::stoi(tok);
                while (deg > 0){
                  mult =  nm->mkNode(Kind::FINITE_FIELD_MULT, mult, symbol);
                  deg = deg-1;

                }
              }
            }
            } else {
            std::cout << "did not enter the bad part\n";
            mult = nm->mkNode(Kind::FINITE_FIELD_MULT, mult, d_symNodes[token]);
            }
          }
          //AlwaysAssert(false);
         if (positive){
            LHS.push_back(mult);
          } else {
            RHS.push_back(mult);
          }
        }
      }
      // if (outside.size() > 0) {
      //   std::vector<Node> outsideVector(outside.begin(), outside.end());
      //   Node outsideNode = nm->mkNode(Kind::FINITE_FIELD_MULT, outsideVector);
      //   if (LHS.size()>0 && RHS.size()>0){
      //   result.push_back(nm->mkNode(
      //     Kind::EQUAL, 
      //     nm->mkNode(Kind::FINITE_FIELD_MULT, outsideNode, 
      //         nm->mkNode(Kind::FINITE_FIELD_ADD, LHS)),
      //     nm->mkNode(Kind::FINITE_FIELD_MULT, outsideNode,
      //         nm->mkNode(Kind::FINITE_FIELD_ADD, RHS))));
      //   }
      //   else if(LHS.size()>0){
      //     result.push_back(nm->mkNode(
      //     Kind::EQUAL, 
      //     nm->mkNode(Kind::FINITE_FIELD_MULT, outsideNode, 
      //         nm->mkNode(Kind::FINITE_FIELD_ADD, LHS)),
      //     nm->mkConst(FiniteFieldValue::mkZero(size()))));
      //   } else if(RHS.size()>0){
      //     result.push_back(nm->mkNode(
      //     Kind::EQUAL, 
      //     nm->mkConst(FiniteFieldValue::mkZero(size())),
      //     nm->mkNode(Kind::FINITE_FIELD_MULT, outsideNode,
      //         nm->mkNode(Kind::FINITE_FIELD_ADD, RHS))));
      //   }
      //   else {
      //     AlwaysAssert(false);
      //   }
      // }
      
      if (LHS.size()>0 && RHS.size()>0){
        result.push_back(nm->mkNode(
          Kind::EQUAL, 
              nm->mkNode(Kind::FINITE_FIELD_ADD, LHS),
              nm->mkNode(Kind::FINITE_FIELD_ADD, RHS)));
        }
        else if(LHS.size()>0){
          result.push_back(nm->mkNode(
          Kind::EQUAL,  
              nm->mkNode(Kind::FINITE_FIELD_ADD, LHS),
          nm->mkConst(FiniteFieldValue::mkZero(size()))));
        } else if(RHS.size()>0){
          result.push_back(nm->mkNode(
          Kind::EQUAL, 
          nm->mkConst(FiniteFieldValue::mkZero(size())),
              nm->mkNode(Kind::FINITE_FIELD_ADD, RHS)));
        }
        else {
          AlwaysAssert(false);
        }
      //next_iteration: ;
    }
    return result;

  }

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

 /* CVC5_USE_COCOA */
