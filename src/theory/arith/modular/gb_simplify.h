#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/theory.h"
#include "util/integer.h"
#include "util/result.h"
#include "theory/arith/theory_arith.h"
#include "theory/ff/singular_parse.h"

#ifndef GB_SIMPLIFY_H
#define GB_SIMPLIFY_H


using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory::ff::singular;


namespace cvc5::internal {
namespace theory {
namespace arith {
namespace modular_range_solver {


// Forward Declaration 
class Field;
class RangeSolver;
class IntegerField;


std::vector<Node> SimplifyViaGB(Field *F, std::map<std::string, std::pair<Integer, Integer> > Bounds, NodeManager* nm, bool inIntegers);

std::vector<Node> SimplifyViaGB(IntegerField *F, std::map<std::string, std::pair<Integer, Integer> > Bounds, NodeManager* nm, bool inIntegers);

std::string runSingular(std::string program);

std::string ReplaceGBStringInput(std::string old, std::string input, std::stringstream &value);

std::string nodeToString(const Node node);

Node monomialToNode(Monomial mono, NodeManager* nm, Field *F);

std::string replaceDots(std::string name);

extern Integer BIGINT;

}
}
}
}
#endif // GB_SIMPLIFY_H