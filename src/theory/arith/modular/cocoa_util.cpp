
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
 * CoCoA utilities
 */

#ifdef CVC5_USE_COCOA

#include "theory/arith/modular/cocoa_util.h"

// external includes
#include <CoCoA/BigIntOps.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-RingElem.H>

// std includes
#include <iostream>

// internal includes

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace modular_range_solver {

std::optional<Scalar> cocoaEval(Poly poly, const PartialPoint& values)
{
  CoCoA::ring coeffs = CoCoA::CoeffRing(CoCoA::owner(poly));
  Scalar out = CoCoA::zero(coeffs);
  for (auto it = CoCoA::BeginIter(poly), end = CoCoA::EndIter(poly); it != end;
       ++it)
  {
    Scalar term = CoCoA::coeff(it);
    std::vector<CoCoA::BigInt> exponents;
    CoCoA::BigExponents(exponents, CoCoA::PP(it));
    for (size_t i = 0, n = exponents.size(); i < n; ++i)
    {
      if (!CoCoA::IsZero(exponents[i]))
      {
        if (!values[i].has_value())
        {
          return {};
        }
        term *= CoCoA::power(*values[i], exponents[i]);
      }
    }
    out += term;
  }
  return {out};
}

Scalar cocoaEval(Poly poly, const Point& values)
{
  CoCoA::ring coeffs = CoCoA::CoeffRing(CoCoA::owner(poly));
  Scalar out = CoCoA::zero(coeffs);
  for (auto it = CoCoA::BeginIter(poly), end = CoCoA::EndIter(poly); it != end;
       ++it)
  {
    Scalar term = CoCoA::coeff(it);
    std::vector<CoCoA::BigInt> exponents;
    CoCoA::BigExponents(exponents, CoCoA::PP(it));
    for (size_t i = 0, n = exponents.size(); i < n; ++i)
    {
      if (!CoCoA::IsZero(exponents[i]))
      {
        term *= CoCoA::power(values[i], exponents[i]);
      }
    }
    out += term;
  }
  return out;
}


CoCoA::BigInt intToCocoa(const Integer& i)
{
  return CoCoA::BigIntFromString(i.toString());
}

std::vector<std::vector<long>> grevlexWeighted(std::vector<long> weights){
  //std::cout << "Grev Order\n";
  int numRows = 1;
  int numColumns = weights.size();
  //std::cout << weights.size() << "\n";
  int grevColumns = numColumns - numRows;
  std::vector<std::vector<long>> finalMatrix(grevColumns, std::vector<long>(numColumns, 0));
//   std::cout << finalMatrix.size() << "\n";
//   std::cout << finalMatrix[0].size() << "\n";
//   std::cout << "Starting for loop\n";
  for (int i =0; i<grevColumns; ++i){
    for (int j = 0; j<numColumns; ++j){
      if (i+j < grevColumns){
        finalMatrix[i][j] = 1;
      }
      else {
        finalMatrix[i][j] = 0;
    }
  }
  }
  //std::cout << "Created first matrix \n";
  finalMatrix.insert(finalMatrix.begin(),weights);
  //std::cout << "Created final matrix \n";
  return finalMatrix;
}

}
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
