/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of ff term parsing.
 */

#include <cstdio>
#include <filesystem>
#include <fstream>
#include <memory>
#include <sstream>
#include <string>
#include <utility>

#include "base/check.h"
#include "test.h"
#include "theory/ff/singular_parse.h"

namespace cvc5::internal {

using namespace theory::ff::singular;

namespace test {

class TestFfSingularParser : public TestInternal
{
};

TEST_F(TestFfSingularParser, varParse)
{
  {
    EXPECT_EQ(Var::parse("x"), (Var{{"x"}, {}}));
    EXPECT_EQ(Var::parse("y"), (Var{{"y"}, {}}));
    EXPECT_EQ(Var::parse("xx"), (Var{{"xx"}, {}}));
    EXPECT_EQ(Var::parse("x(1)"), (Var{{"x"}, {1}}));
    EXPECT_EQ(Var::parse("x(1)(2)"), (Var{{"x"}, {1, 2}}));
  }
}

TEST_F(TestFfSingularParser, varPowerParse)
{
  {
    EXPECT_EQ(VarPower::parse("x"), (VarPower{Var{{"x"}, {}}, 1}));
    EXPECT_EQ(VarPower::parse("y"), (VarPower{Var{{"y"}, {}}, 1}));
    EXPECT_EQ(VarPower::parse("xx"), (VarPower{Var{{"xx"}, {}}, 1}));
    EXPECT_EQ(VarPower::parse("x(1)"), (VarPower{Var{{"x"}, {1}}, 1}));
    EXPECT_EQ(VarPower::parse("x(1)(2)"), (VarPower{Var{{"x"}, {1, 2}}, 1}));
    EXPECT_EQ(VarPower::parse("x^3"), (VarPower{Var{{"x"}, {}}, 3}));
    EXPECT_EQ(VarPower::parse("y^1"), (VarPower{Var{{"y"}, {}}, 1}));
    EXPECT_EQ(VarPower::parse("xx^54"), (VarPower{Var{{"xx"}, {}}, 54}));
  }
}

TEST_F(TestFfSingularParser, monomialParse)
{
  {
    EXPECT_EQ(Monomial::parse("x"),
              (Monomial{1, {VarPower{Var{{"x"}, {}}, 1}}}));
    EXPECT_EQ(Monomial::parse("y"),
              (Monomial{1, {VarPower{Var{{"y"}, {}}, 1}}}));
    EXPECT_EQ(Monomial::parse("1"), (Monomial{1, {}}));
    EXPECT_EQ(Monomial::parse("xx"),
              (Monomial{1, {VarPower{Var{{"xx"}, {}}, 1}}}));
    EXPECT_EQ(Monomial::parse("x(1)"),
              (Monomial{1, {VarPower{Var{{"x"}, {1}}, 1}}}));
    EXPECT_EQ(Monomial::parse("x(1)(2)"),
              (Monomial{1, {VarPower{Var{{"x"}, {1, 2}}, 1}}}));
    EXPECT_EQ(Monomial::parse("x^3"),
              (Monomial{1, {VarPower{Var{{"x"}, {}}, 3}}}));
    EXPECT_EQ(Monomial::parse("y^1"),
              (Monomial{1, {VarPower{Var{{"y"}, {}}, 1}}}));
    EXPECT_EQ(Monomial::parse("xx^54"),
              (Monomial{1, {VarPower{Var{{"xx"}, {}}, 54}}}));
    EXPECT_EQ(Monomial::parse("5*xx"),
              (Monomial{5, {VarPower{Var{{"xx"}, {}}, 1}}}));
    EXPECT_EQ(
        Monomial::parse("5*x*y"),
        (Monomial{5,
                  {VarPower{Var{{"x"}, {}}, 1}, VarPower{Var{{"y"}, {}}, 1}}}));
  }
}

TEST_F(TestFfSingularParser, polynomialParse)
{
  {
    EXPECT_EQ(Polynomial::parse("x"),
              (Polynomial{{Monomial{1, {VarPower{Var{{"x"}, {}}, 1}}}}}));
    EXPECT_EQ(Polynomial::parse("y"),
              (Polynomial{{Monomial{1, {VarPower{Var{{"y"}, {}}, 1}}}}}));
    EXPECT_EQ(Polynomial::parse("1"), (Polynomial{{Monomial{1, {}}}}));
    EXPECT_EQ(Polynomial::parse("xx"),
              (Polynomial{{Monomial{1, {VarPower{Var{{"xx"}, {}}, 1}}}}}));
    EXPECT_EQ(Polynomial::parse("x(1)"),
              (Polynomial{{Monomial{1, {VarPower{Var{{"x"}, {1}}, 1}}}}}));
    EXPECT_EQ(Polynomial::parse("x(1)(2)"),
              (Polynomial{{Monomial{1, {VarPower{Var{{"x"}, {1, 2}}, 1}}}}}));
    EXPECT_EQ(Polynomial::parse("x^3"),
              (Polynomial{{Monomial{1, {VarPower{Var{{"x"}, {}}, 3}}}}}));
    EXPECT_EQ(Polynomial::parse("y^1"),
              (Polynomial{{Monomial{1, {VarPower{Var{{"y"}, {}}, 1}}}}}));
    EXPECT_EQ(Polynomial::parse("xx^54"),
              (Polynomial{{Monomial{1, {VarPower{Var{{"xx"}, {}}, 54}}}}}));
    EXPECT_EQ(Polynomial::parse("5*xx"),
              (Polynomial{{Monomial{5, {VarPower{Var{{"xx"}, {}}, 1}}}}}));
    EXPECT_EQ(Polynomial::parse("5*xx-x+4*y"),
              (Polynomial{{Monomial{5, {VarPower{Var{{"xx"}, {}}, 1}}},
                           Monomial{-1, {VarPower{Var{{"x"}, {}}, 1}}},
                           Monomial{4, {VarPower{Var{{"y"}, {}}, 1}}}}}));
  }
}

/** Return the path a fresh a temporary file. */
std::filesystem::path tmpPath()
{
  char name[L_tmpnam];
  if (std::tmpnam(name))
  {
    return std::filesystem::path(name);
  }
  else
  {
    AlwaysAssert(false) << "Could not create tempfile";
  }
}

/** Write contents to a temporary file and return its path. */
std::filesystem::path writeToTmpFile(std::string contents)
{
  std::filesystem::path path = tmpPath();
  std::ofstream f(path);
  f << contents;
  f.close();
  return path;
}

std::string readFileToString(std::filesystem::path path)
{
  std::ifstream t(path);
  std::stringstream buffer;
  buffer << t.rdbuf();
  return buffer.str();
}

/** Run Singular on this program and return the output. */
std::string runSingular(std::string program)
{
  std::filesystem::path output = tmpPath();
  std::filesystem::path input = writeToTmpFile(program);
  std::stringstream commandStream;
  commandStream << "Singular -q -t " << input << " > " << output;
  std::string command = commandStream.str();
  int exitCode = std::system(command.c_str());
  Assert(exitCode == 0) << "Singular errored\nCommand: " << command;
  std::string outputContents = readFileToString(output);
  Assert(outputContents.find("?") == std::string::npos) << "Singular error:\n"
                                                        << outputContents;
  std::filesystem::remove(output);
  std::filesystem::remove(input);
  return outputContents;
}

VarPower v(const char* s) { return VarPower{Var{std::string(s), {}}, 1}; }
Polynomial p(Integer i, const char* s)
{
  return Polynomial{{Monomial{i, {v(s)}}}};
}

Polynomial p(Integer i) { return Polynomial{{Monomial{i, {}}}}; }

TEST_F(TestFfSingularParser, intGbUniOneGcd)
{
  {
    std::string input =
        "ring r = integer, (dummyName,x), dp;"
        "ideal i = 2x, 5x;"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 1);
    EXPECT_EQ(polys[0], p(1, "x"));
  }
}

TEST_F(TestFfSingularParser, intGbUniNotOneGcd)
{
  {
    std::string input =
        "ring r = integer, (dummyName,x), dp;"
        "ideal i = 4x, 6x;"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 1);
    EXPECT_EQ(polys[0], p(2, "x"));
  }
}

TEST_F(TestFfSingularParser, intGbMultiOne)
{
  {
    std::string input =
        "ring r = integer, (dummyName,x,y), dp;"
        "ideal i = x, x*y-1;"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 1);
    EXPECT_EQ(polys[0], p(1));
  }
}

TEST_F(TestFfSingularParser, intGbMultiNotOne)
{
  {
    std::string input =
        "ring r = integer, (dummyName,x,y), dp;"
        "ideal i = x, y-x;"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 2);
  }
}

TEST_F(TestFfSingularParser, fieldGbMultiNotOne)
{
  {
    std::string input =
        "ring r = 7, (dummyName,x,y), dp;"
        "ideal i = x2-1, y-x2;"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 2);
  }
}

TEST_F(TestFfSingularParser, fieldGbMultiPlus)
{
  {
    std::string input =
        "ring r = 7, (dummyName,x,y), dp;"
        "ideal i = x2+y;"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 1);
  }
}

TEST_F(TestFfSingularParser, bigFieldGbMultiPlus)
{
  {
    // using the standard prime field coefficient syntax does not work for p >
    // 2147483647 (see:
    // https://www.singular.uni-kl.de/Manual/4-0-3/sing_162.htm#SEC201) "ring
    // r = (integer,
    // 46670133589800051886943986164409419013068489203278719581003409320849341574189),
    // (dummyName,x,y), dp;"
    std::string input =
        "ring r = (integer, "
        "46670133589800051886943986164409419013068489203278719581003409320849"
        "34"
        "1574189), (dummyName,x,y), dp;"
        "ideal i = x2+y;"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 1);
  }
}

TEST_F(TestFfSingularParser, bvGbMultiPlus)
{
  {
    std::string input =
        "ring r = (integer,16), (dummyName,x,y), dp;"
        "ideal i = x2+y;"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 1);
  }
}

TEST_F(TestFfSingularParser, bigBvGbMultiPlus)
{
  {
    // 2^64 = 18446744073709551616
    std::string input =
        "ring r = (integer,18446744073709551616), (dummyName,x,y), dp;"
        "ideal i = x2+y;"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 1);
  }
}

TEST_F(TestFfSingularParser, bvGbMultiWithIndexedNames)
{
  {
    // "Monomials which contain an indexed ring variable must be built from
    // ring_variable and coefficient with the operations * and ^"
    // from: https://www.singular.uni-kl.de/Manual/4-0-3/sing_149.htm#SEC188
    std::string input =
        "ring r = (integer,32), (dummyName,x(1..10)), dp;"
        "ideal i = x(1)+2*x(2)+4*x(3);"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 1);
  }
}

TEST_F(TestFfSingularParser, bvGbMultiWithTwoIndexedNames)
{
  {
    std::string input =
        "ring r = (integer,32), (dummyName,x(1..10),y(2..4)), dp;"
        "ideal i = x(1)+2*x(2)+4*x(3)-y(2);"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 1);
  }
}

TEST_F(TestFfSingularParser, bvGbMultiWithMultiIndexedName)
{
  {
    std::string input =
        "ring r = (integer,32), (dummyName,x(1..10)(2..4)), dp;"
        "ideal i = x(1)(2)*x(2)(2),x(3)(4);"
        "std(i);"
        "quit;";
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), 2);
  }
}

TEST_F(TestFfSingularParser, bvGbMultiBigOuput)
{
  {
    size_t count = 100;
    std::stringstream inputStream;
    inputStream << "ring r = (integer,32), (dummyName,x(1.." << count
                << ")), dp;"
                   "ideal i = ";
    for (size_t i = 1; i <= count; ++i)
    {
      if (i > 1)
      {
        inputStream << ", ";
      }
      inputStream << "x(" << i << ")";
    }
    inputStream << ";"
                   "std(i);"
                   "quit;";
    std::string input = inputStream.str();
    std::string output = runSingular(input);
    std::vector<Polynomial> polys = parsePolynomialList(output);
    EXPECT_EQ(polys.size(), count);
  }
}

}  // namespace test
}  // namespace cvc5::internal
