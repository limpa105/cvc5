


#include <cerrno>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <unordered_map>
#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "options/ff_options.h"
#include "smt/env_obj.h"
#include "theory/arith/modular/int_cocoa_encoder.h"
#include "theory/arith/modular/range-solver.h"
#include "theory/ff/singular_parse.h"
#include "util/cocoa_globals.h"
#include "util/finite_field_value.h"
#include "theory/decision_manager.h"
#include <typeinfo>
#include <utility>
#include <algorithm>
#include <utility>
#include "util/result.h"
#include "util/statistics_registry.h"
#include "util/utility.h"
#include <cmath>
#include <iostream>
#include <string>
#include <sstream>
#include <vector>
#include <regex>
#include <cstdlib>
#include <thread>
#include <future>
#include <chrono>
//#include "theory/ff/multi_roots.h"
// #include <CoCoA/BigInt.H>
// #include <CoCoA/QuotientRing.H>
// #include <CoCoA/RingZZ.H>
// #include <CoCoA/RingQQ.H>
// #include <CoCoA/TmpGReductor.H>
 // #include <CoCoA/GBEnv.H>
 // #include <CoCoA/SparsePolyOps-ideal.H>
// #include <CoCoA/ring.H>
// #include <CoCoA/SparsePolyRing.H>
// #include <CoCoA/PolyRing.H>
 #include <CoCoA/library.H>



using namespace cvc5::internal::theory;

using namespace cvc5::internal::kind;

using namespace cvc5::internal::theory::ff::singular;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace modular_range_solver {


/////////////////////////////////////////////////// UTILS ////////////////////////////////////////////////////////////////////

 Integer BIGINT = Integer("26697537170649044179042152467634255803129704511815242562837925141177577913409118302943186911045680008195241138225131464058766427708039764790250144472755736885526820882067462431042573357558604819957849");

 long BIGINTLOG = 10 * log2(BIGINT.getDouble());

bool isVariableOrSkolem(Node node) {
    return node.getKind() == Kind::VARIABLE || node.getKind() == Kind::SKOLEM;
}

std::string singular_command_weighted = "option(redSB); ring r = (integer, {1}), ({2}), (wp({4})); ideal I= {5}; ideal G= std(I); G; quit;";
std::string singular_command_reduce = "ring r = (integer, {1}), ({2}), (wp({4})); ideal I= {5}; reduce({6}, I); quit;";
std::string singular_command_unweighted = "option(redSB); ring r = (integer, {1}), ({2}), (Dp); ideal I= {5}; ideal G= std(I); G; quit;";
std::string singular_command_reduce_uw = "ring r = (integer, {1}), ({2}), (Dp); ideal I= {5}; reduce({6}, I); quit;";

std::optional<std::pair<Integer,Integer>> getBounds(Node fact, Integer new_field, std::map<std::string, std::pair<Integer, Integer> > Bounds, bool ineq=false){
    //TODO MAKE THIS NON OPTIONAL!!!!
    if (isVariableOrSkolem(fact)) {
        if (Bounds.find(fact.getName())!= Bounds.end()){
            //std::optional<Integer> answer = Bounds[fact.getName()] -Integer(1);
            return  Bounds[fact.getName()];
        }
        AlwaysAssert(false) << "No bounds found for" << fact.getName();
    }
    // Constant
    if (fact.getKind() == Kind::CONST_INTEGER){
        Integer coef = fact.getConst<Rational>().getNumerator();
        if (!ineq && new_field.divides(coef)){
            return std::make_pair(Integer(0), Integer(0));
        }
        return std::make_pair(coef, coef);
    }
    // Multiplication
    if (fact.getKind() == Kind::MULT || fact.getKind()== Kind::NONLINEAR_MULT){
        std::pair<Integer,Integer> acmBounds = std::make_pair(Integer(1), Integer(1));
        for (int i=0; i<fact.getNumChildren(); i++){
            std::optional<std::pair<Integer, Integer>> result = getBounds(fact[i], new_field, Bounds, ineq);
            if (result.has_value()){
                Integer p1 = acmBounds.first * result.value().first;
                Integer p2 = acmBounds.second * result.value().second;
                Integer p3 = acmBounds.first * result.value().second;
                Integer p4 = acmBounds.second * result.value().first;

               acmBounds.first = Integer::min(Integer::min(p1,p2), Integer::min(p3,p4));
               acmBounds.second =Integer::max(Integer::max(p1,p2), Integer::max(p3,p4));
            }
            else {
                return {};
            }
        }
        return acmBounds;
    }
    AlwaysAssert(fact.getKind() == Kind::ADD) << fact;
    std::pair<Integer,Integer> acmBounds = std::make_pair(Integer(0), Integer(0));
    for (int i=0; i<fact.getNumChildren(); i++){
         std::optional<std::pair<Integer, Integer>> result = getBounds(fact[i], new_field, Bounds, ineq);
            if (result.has_value()){
                acmBounds.first += result.value().first;
                acmBounds.second += result.value().second;
            }
            else {
                return {};
            }

    }
    return acmBounds;
}

std::set<std::string> getVarsHelper(Node eq){
    std::set<std::string> answer;
    if (eq.getKind() == Kind::CONST_INTEGER){
        return answer;;
    }
     if (isVariableOrSkolem(eq)){
        answer.insert(eq.getName());
        return answer;
    }
    if (eq.getNumChildren() > 1){
        for (int i =0; i<eq.getNumChildren(); i++){
        std::set<std::string> moreVars = getVarsHelper(eq[i]);
        answer.insert(moreVars.begin(), moreVars.end());
        }
        return answer;       
    }
    AlwaysAssert(false) << eq;
}


// std::set<Node> getVars(std::vector<Node> eqs){
//     std::set<Node> answer;
//     for (auto eq: eqs){
//         std::set<Node> moreVars = getVarsHelper(eq);
//         answer.insert(moreVars.begin(), moreVars.end());
//     }
//     return answer;
// }

void noCoCoALiza()
{
    std::cout << "cvc5 can't solve field problems since it was not configured with "
      "--cocoa\n";
    AlwaysAssert(false);
}

std::vector<CoCoA::RingElem> getCococaGB(Field *F){
      if ((*F).equalities.size() <= 1) {
        AlwaysAssert(false) << "NEED TO THINK ABOUT THIS\n";
      }
      CocoaEncoder enc = CocoaEncoder();
      for (const Node& node : (*F).equalities)
      {
        enc.addFact(node);
      }
;
      enc.endScan();
      for (const Node& node :(*F).equalities)
      {
        enc.addFact(node);
      }

      std::vector<CoCoA::RingElem> generators;
      generators.insert(
          generators.end(), enc.polys().begin(), enc.polys().end());
      std::vector<Node> newPoly;
      CoCoA::ideal ideal = CoCoA::ideal(generators);
      auto basis = CoCoA::GBasis(ideal);
      return basis
}


// TODO: Need to find max by iterating through equations.
std::vector<long> getWeights(std::map<std::string, Node> variables, std::map<std::string, std::pair<Integer, Integer> > Bounds, bool weightedGB, std::set<std::string> notVars){
    std::vector<long> answer;
    for (auto i: variables){
        // std::ostringstream oss;
        // oss << i;
        // std::string symbol = d_symNodes[oss.str()].getName();
        std::string symbol= i.second.getName();
        //std::cout << i << "\n";
        // size_t pos = symbol.find("___");
        // if (pos != std::string::npos) {
        //     while ((pos = symbol.find("___", pos)) != std::string::npos) {
        //     symbol.replace(pos, 3, "__");
        //     pos += 2;
        //     }
        // } else  {
        // size_t pos = symbol.find("__");
        // if (pos != std::string::npos) {
        //     while ((pos = symbol.find("__", pos)) != std::string::npos) {
        //     symbol.replace(pos, 2, "_");
        //     pos += 1;
        // }
        
        
        if (Bounds.find(symbol)!= Bounds.end()){
            long result = 10*log2(Bounds[symbol].second.getDouble());
            //std::cout << result << "\n";
            answer.push_back(long(result));
        }
        else {
            //AlwaysAssert(false);
            if(symbol.find("Q_HOLDER") != std::string::npos){
                answer.push_back(2);
                Bounds[symbol] = std::make_pair(0, 2);
                //Bounds.insert(std::make_pair(symbol, 2));
            } else {
            //std::cout << oss.str() << "\n";
            AlwaysAssert(false) << symbol << "has no bound??";
            float result = BIGINTLOG;
            //std::cout << "NOBOUND" << result << "\n";
            answer.push_back(long(result));
            }
        }
        if (!weightedGB && notVars.find(symbol) !=notVars.end()){
            std::cout << "SUBTRACTING WEIGHTS\n";
            answer[answer.size()-1] = std::min((answer[answer.size()-1] - 30), (long)0);
        }
    }
    return answer;
} 

std::string ReplaceGBStringInput(std::string old, std::string input, std::stringstream &value){
    std::string value_str = value.str();
    size_t pos = input.find(old);
    if (pos != std::string::npos){
            input.replace(pos, 3, value_str);
    } else {
        return input;
        AlwaysAssert(false);
    }
    return input;
}



// Function to parse and convert S-expression style equations
std::string nodeToString(const Node node) {
   if (node.getKind() == Kind::EQUAL){
        AlwaysAssert(node[1].getConst<Rational>() == 0);
        return nodeToString(node[0]);
   }
   std::string answer;
   if (node.getNumChildren() > 0){
   for (int i =0; i<node.getNumChildren(); i++){
        if (node[i].getNumChildren()>0){
            answer+= "(" + nodeToString(node[i]) + ")";
        }
        else {
            answer+=nodeToString(node[i]);
        }
        if (i!= node.getNumChildren()-1){
            std::stringstream ss;
            ss << (node.getKind());
            answer+= ss.str(); 
        }
    }
   return answer;
   }
   return node.toString();
}


std::string replaceDots(std::string name) {
    std::string str = name;
    size_t start_pos = 0;
    while((start_pos = str.find('.', start_pos)) != std::string::npos) {
        str.replace(start_pos, 1, "_");
        start_pos += 1; // Move past the replaced part
    }
    return str;
}


// Copied from Alex Ozdemir

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
  //std::cout << program << "\n";
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
  //std::cout << outputContents << "\n";
  return outputContents;
}


Node monomialToNode(Monomial mono, NodeManager* nm, Field *F){
    std::vector<Node> powers;
    powers.push_back(nm->mkConstInt(mono.coeff));
    for(auto i: mono.varPowers){
        for (int j =0; j< i.power; j++){
            powers.push_back((*F).myVariables[i.var.name]);
        }
    }
    return nm->mkNode(Kind::MULT, powers);
}

std::vector<Node> SimplifyViaGB(Field *F, std::map<std::string, std::pair<Integer, Integer> > Bounds, NodeManager* nm, bool WeightedGB){
    // std::cout << (*F).modulos << "\n";
    // std::cout << (*F).equalities.size() << "\n";
      if ((*F).equalities.size() <= 1) {
        return (*F).equalities;
      }
      //std::cout << "Getting weights\n";
     std::vector<long> weights = getWeights((*(*F).solver).myVariables, (*(*F).solver).Bounds, WeightedGB, (*(*F).solver).myNotVars);
     //std::cout << "Got Weights\n";
    // std::ifstream inputFile("theory/arith/modular/gb_input.txt");

    // // Check if the file was successfully opened
    // if (!inputFile.is_open()) {
    //     AlwaysAssert(false) << "Singular GB input file does not exist";
    // }
    // Read and print the contents of the file
    std::string line;
    //if(WeightedGB){
     line = singular_command_weighted;
   //} else {
     //line = singular_command_unweighted;
   //}

    //}
    //inputFile.close();
    std::stringstream ss;
    ss << (*F).modulos;
    line = ReplaceGBStringInput("{1}", line, ss);
    ss.str("");
    ss.clear();
    //std::cout << (*F).myNodes.size() << "\n";
    int bound_count = 0;
    for (auto it =  (*(*F).solver).myVariables.begin(); it != (*(*F).solver).myVariables.end(); ++it) {
        ss << it->first;
        if (std::next(it) != (*(*F).solver).myVariables.end()) {
            ss << ",";
        }
    }
     //std::cout << "Got Variables\n";
    line = ReplaceGBStringInput("{2}", line, ss);
    ss.str("");
    ss.clear();
    
    //std::cout << line << "\n";
    // ss << upperBounds.size();
    // line = ReplaceGBStringInput("{3}", line, ss);
    // ss.str("");
    // ss.clear();

    for (auto it = weights.begin(); it != weights.end(); ++it) {
        ss << *it;
        if (std::next(it) != weights.end()) {
            ss << ",";
        }
    }
    line = ReplaceGBStringInput("{4}", line, ss);
    ss.str("");
    ss.clear();
    //std::cout << line << "\n";
    for (auto it = (*F).equalities.begin(); it != (*F).equalities.end(); ++it) {
        ss << replaceDots(nodeToString(nm->mkNode(Kind::SUB, (*it)[0], (*it)[1])));
        if (std::next(it) != (*F).equalities.end()) {
            ss << ",";
        }
    }
    // std::cout << "Got Equalities";
    line = ReplaceGBStringInput("{5}", line, ss);
    ss.str("");
    ss.clear();
    //std::string command = "Singular -q -t -c \" " + line + "\"";
    //std::cout << line << "\n";
    //int result = system(command.c_str());
    //AlwaysAssert(false);
    std::string output = "";
    std::vector<Node> GBPolys;
    auto result = std::make_shared<std::string>("");
    std::shared_ptr<bool> done = std::make_shared<bool>(false);
    std::mutex resultMutex;
     //std::cout << "Running Singular\n";
    // Launch the function asynchronously
    auto future = std::async(std::launch::async, [&]() {
        auto res = runSingular(line);
        {
            std::lock_guard<std::mutex> lock(resultMutex);
            *result = res;
            *done = true;
            //std::cout << "Function completed." << "\n";
        }
    });
    auto start = std::chrono::steady_clock::now();
    while (std::chrono::steady_clock::now() - start < std::chrono::seconds(60)) {
        {
            std::lock_guard<std::mutex> lock(resultMutex);
            if (*done) {
                output= *result;
                break; // Return the final result if the function completes
            }
        }
        //std::this_thread::sleep_for(std::chrono::seconds(1)); // Check every second
    }

    if (output.empty()){
        AlwaysAssert(false);
    }
    std::vector<Polynomial> polys = parsePolynomialList(output);
    if(polys.size()==1 && polys[0]== Polynomial{{Monomial{1, {}}}}){
        return GBPolys;
    }
    //std::cout << "OG GB\n";
    for (auto p: polys){
        std::vector<Node> products;
        for (auto m: p.monomials){
            //std::cout << m << "\n";
            products.push_back(monomialToNode(m, nm, F));
        }
        GBPolys.push_back(nm->mkNode(Kind::EQUAL, 
        nm->mkNode(Kind::ADD, products), nm->mkConstInt(0)));
    }
    std::vector<Node> EmptyPolys;
    /// NOW WE WILL REDUCE THE INEQUALITIES AGAINST THE COMPUTED BASIS 
    //if (WeightedGB){
    line = singular_command_reduce;
    //} else {
    //l//ine = singular_command_reduce_uw;
    //} 
    ss.str("");
    ss.clear();
    ss << (*F).modulos;
     line = ReplaceGBStringInput("{1}", line, ss);
        ss.str("");
        ss.clear();
        //std::cout << (*F).myNodes.size() << "\n";
        bound_count = 0;
        for (auto it =  (*(*F).solver).myVariables.begin(); it != (*(*F).solver).myVariables.end(); ++it) {
                ss << it->first;
            if (std::next(it) != (*(*F).solver).myVariables.end()) {
                ss << ",";
            }
        }
        line = ReplaceGBStringInput("{2}", line, ss);
        ss.str("");
        ss.clear();
        
        ss.str("");
        ss.clear();
        
        //std::cout << line << "\n";
        // ss << upperBounds.size();
        // line = ReplaceGBStringInput("{3}", line, ss);
        // ss.str("");
        // ss.clear();

        for (auto it = weights.begin(); it != weights.end(); ++it) {
            ss << *it;
            if (std::next(it) != weights.end()) {
                ss << ",";
            }
        }
        line = ReplaceGBStringInput("{4}", line, ss);
        ss.str("");
        ss.clear();
        //std::cout << line << "\n";
        // ss << upperBounds.size();
        // line = ReplaceGBStringInput("{3}", line, ss);
        // ss.str("");
        // ss.clear();
        //std::cout << line << "\n";
        for (auto it = GBPolys.begin(); it != GBPolys.end(); ++it) {
            ss << replaceDots(nodeToString(nm->mkNode(Kind::SUB, (*it)[0], (*it)[1])));
            if (std::next(it) != GBPolys.end()) {
                ss << ",";
            }
        }
        line = ReplaceGBStringInput("{5}", line, ss);
        (*F).mySingularReduce = line;
        //std::cout << "we got here\n";
       // std::cout << (*F).inequalities.size() << "\n";
        if ((*F).inequalities.size() > 0){
        for(int i =0; i<(*F).inequalities.size(); i++){
            ss.str("");
            ss.clear();
            ss << replaceDots(nodeToString(nm->mkNode(Kind::SUB, (*F).inequalities[0][0], (*F).inequalities[0][1])));
            line = ReplaceGBStringInput("{6}", line, ss);
            std::string output = runSingular(line);
            //std::cout << line <<"\n";
            //std::cout << output << "\n" ;
            size_t pos =output.find('\n');
            std::string result = output.substr(pos + 1);
            try{
            if (std::stoi(result) == 0){
                std::cout << "OUTPUT ZERO WWOOO\n";
                (*F).status = Result::UNSAT;
                std::cout << "set status unsat?\n";
                return EmptyPolys;
            }
            } catch (const std::invalid_argument& e) { //std::cout << output << "\n";
            } catch (const std::out_of_range& e) { //std::cout << output << "\n"; }
            };
        }
        }
       // std::cout << "but we did not get here\n";


    return GBPolys;
    


    //   SingularEncoder enc = SingularEncoder((*F).modulos.getUnsignedInt(),
    //   (*F).myVariables,
    //   (*F).myNodes,
    //   weights,
    //   nm);
      
    //   for (auto i: (*F).equalities){
    //     enc.addFact(i);
    //   }

    //    std::vector<Node> newPoly = enc.computeGB();
    //    return newPoly
}




      //std::cout << "Got here" << (*F).modulos << "\n";
    //   CocoaEncoder enc = CocoaEncoder();
    //   //std::cout << "Made encoder \n";
    //   // collect leaves
    //   for (const Node& node : (*F).equalities)
    //   {
    //     enc.addFact(node);
    //   }
    //   if (WeightedGB){
    //     //std::cout << enc.d_syms << "\n";
    //   //std::cout << "Added facts first time \n";
    //   std::vector<long> boundWeights = getWeights(enc.d_syms, enc.d_symNodes, upperBounds);
    // //   for (auto i: boundWeights){
    // //     std::cout << i << ",";
    // //   }
    //   //std::cout << "\n";
    //   enc.endScanIntegers(boundWeights);
    //   }
    //   else {
    //     //std::cout << "NORMAL GB SCAN\n";
    //     enc.endScan();
    //   }
    //   //std::cout << "Scanned Integers \n";
    //   //std::cout << "Got weights \n";
    //   // assert facts
    //   for (const Node& node :(*F).equalities)
    //   {
    //     enc.addFact(node);
    //   }
    //   //std::cout << "Added facts a second time \n";

    //   // compute a GB
    // //   std::vector<CoCoA::RingElem> generators;
    // //   generators.insert(
    // //       generators.end(), enc.polys().begin(), enc.polys().end());
    // //       //std::cout << "Computed generators \n";
    // // for (auto i: generators){
    // //   //std::cout << i << "\n";
    // //     };
    // //   std::vector<Node> newPoly;
    // //   if ((*F).inequalities.size()>0){
    // //     std::vector<Node> intersection;
    // //     std::set<Node> eqVars = enc.getCurVars();
    // //     std::set<Node> neqVars = getVars((*F).inequalities);
    // //     std::set_intersection(eqVars.begin(), eqVars.end(),
    // //                         neqVars.begin(), neqVars.end(),
    // //                         std::back_inserter(intersection));
    // //     // if (intersection.empty()){
    // //     //     (*F).status = Result::SAT;
    // //     //     return newPoly;
    // //     // }
    // //   }
    //   //ff::Tracer tracer(generators);
    //   //tracer.setFunctionPointers();
    //   CoCoA::ideal ideal = CoCoA::ideal(generators);
    //   CoCoA::GReductor tempRed = CoCoA::GReductor(
    //     CoCoA::GRingInfo(enc.d_polyRing.value(), false, false,CoCoA::NewDivMaskNull(), CoCoA::CpuTimeLimit(100.0)), generators, CoCoA::GReductor::AffineAlg);
    //   // << "This worked\n";
    //   const int numRed = 1;
    //   try {
    //   tempRed.myDoGBasis();
    //    } catch (const CoCoA::ErrorInfo& e) {
    //     //std::cout << e << "\n";
    //     AlwaysAssert(false);
    //     }
    //  // std::cout << "Computed basis?\n";
    //   std::vector<CoCoA::RingElem> basis;
    //   std::list<CoCoA::GPoly> basis2;
    //   //basis = CoCoA::GBasis(ideal);
    //   //std::cout << "Computed Basis\n";
    //   tempRed.myGBasis(basis);
    //   //std::cout << "Finished something?\n";
    //   for (auto i : basis ){
    //     //std::cout << i << "\n";
    //   }
    //   //std::cout << tempRed.GetNReductions() << "\n";
    //   //basis.clear();
    //   //basis = CoCoA::GBasis(ideal);
      
    //   //std::cout << "This also worked??\n";
    //   //std::cout << "NEW\n";
    //   //std::ostringstream oss;
    //   //std::cout << tempRed.GetNReductions() << "\n";
    //   //std::cout << oss.str() << "\n";
    
    // //   tempRed.myMinGens(basis);
    // //   std::cout << "Finished something?\n";
    // //   for (int i = 0; i<basis.size(); i++){
    // //     std::cout << basis[i] << "\n";
    // //   }
    //   //AlwaysAssert(false);

    
    //   //tracer.unsetFunctionPointers();
    //   //std::vector<size_t> coreIndices = tracer.trace(basis.front());
    //   //for (size_t i : coreIndices)
    //         //{

  

    //   if (basis.size() == 1 && CoCoA::deg(basis.front()) == 0)
    //   {
    //     return newPoly;
    //   }
    //   //std::cout << "Computed basis \n";
    //   //std::cout << "BASIS\n";
    //   newPoly = enc.cocoaToNode(basis, nm);
    //   //std::cout << "Finished Conversion\n";
    //   //std::cout << newPoly.size() << "\n";

    //   return newPoly;


bool checkIfConstraintIsMet(Node equality, Integer modulos, std::map<std::string, std::pair<Integer, Integer> > Bounds, bool ineq = false){
   // std::cout << "EQ:" << equality << "\n";
    if (auto LHS  = getBounds(equality[0], modulos, Bounds, ineq) ){
        //std::cout << "LHS" << LHS.value() << "\n";
        if (auto RHS  = getBounds(equality[1], modulos, Bounds, ineq) ){
            //Subtract LHS - RHS 
            Integer upper = LHS.value().second - RHS.value().first;
            Integer lower = LHS.value().first  - RHS.value().second;
            //std::cout << "[" << lower << "," << upper << "]" << "\n";
            if (lower.abs() >= modulos){
                //std::cout << "failed lower\n";
                return false;
            }
             if (upper.abs() >= modulos){
                return false;
            }
            
            //std::cout << "RHS" << LHS.value() << "\n";
            // if ((LHS.value().first + RHS.value().second) >= modulos){
            //     return false;
            // }
            // if ((RHS.value().first + LHS.value().second) >= modulos){
            //     return false;
            // }

        } else {
            return false;
        }
    } else {
        return false;
    }
    return true; 
}



bool IntegerField::checkUnsat(){
    for(int i=0; i<inequalities.size(); i++){
        if (inequalities[i].getKind()== Kind::CONST_BOOLEAN &&
            inequalities[i].getConst<bool>() == true){
            status = Result::UNSAT;
            return true;
            }
        for(int j=0; j<equalities.size(); j++){
            if((inequalities[i][0]==equalities[j][0]) &&
               (inequalities[i][1]==equalities[j][1]) ){
                // std::cout << "INTEGER UNSAT:" << "\n";
                // std::cout << "INEQ:" << inequalities[i] << "\n";
                // std::cout << "EQ" << equalities[j] << "\n";
                status = Result::UNSAT;
                return true;
               }
        }
    }
    return false;
}

/////////////////////////////////////////////////// INTEGERFIELD ////////////////////////////////////////////////////////////////////

IntegerField::IntegerField(Env &env):EnvObj(env){};

bool IntegerField::Simplify(std::map<Integer, Field>& fields, std::map<std::string, std::pair<Integer, Integer> > Bounds){
    //std::cout << "STARTED INTEGERS\n";
    //CancelConstants();
    NodeManager* nm = NodeManager::currentNM();
    checkUnsat();
    // if (status == Result::UNSAT){
    //     return false;
    // }
    substituteVariables();
    //clearEqualities();
    //for (Node poly: newPoly){
        //std::cout << "New Poly F:" << poly << "\n \n \n";
        //std::cout << poly << "\n";
        //addEquality(rewrite(poly));
    //}
    //AlwaysAssert(equalities.size() == newPoly.size());
    //std::cout << "FINISHED ADDING FOR INTEGERS\n";
    for (auto& fieldPair : fields){
        //std::cout << "LOWERING\n";
        Lower(fieldPair.second,Bounds);
    }
    //std::cout << "FINISHED LOWERING\n";
    return true;
}

void IntegerField::addEquality(Node equality){
    //std::cout << "INTEGER FIELD LOOKING ATT" << equality << "\n";
    if (std::find(equalities.begin(), equalities.end(), equality) == equalities.end()){
        //std::cout << "ADDED\n";
        equalities.push_back(equality);
    }
};

void IntegerField::addInequality(Node inequality){
    if (std::find(inequalities.begin(), inequalities.end(), inequality) == inequalities.end()){
        inequalities.push_back(inequality);
    }

};

// Can always lower Equalities 
void IntegerField::Lower(Field& field, std::map<std::string, std::pair<Integer, Integer> > Bounds){
    for (int i=0; i<equalities.size(); i++){
            field.addEquality(equalities[i], false);
// Need to check if can lower 
    for (int i=0; i<inequalities.size(); i++){
        if (checkIfConstraintIsMet(inequalities[i], field.modulos, Bounds, true)){
                field.addInequality(inequalities[i]);
        }
    }

}
}

void IntegerField::CancelConstants(){
    for (int i=0; i<equalities.size(); i++){
        Node fact = equalities[i];
        if (fact[0].getKind() == Kind::FINITE_FIELD_MULT &&  
        fact[1].getKind()== Kind::FINITE_FIELD_MULT &&
        fact[0][0].getConst<FiniteFieldValue>().getValue() == fact[1][0].getConst<FiniteFieldValue>().getValue())
        {
            NodeManager* nm = NodeManager::currentNM();
            addEquality(rewrite(nm->mkNode(Kind::EQUAL, fact[0][1], fact[1][1])));
        }
    }      
    for (int i=0; i<inequalities.size(); i++){
        Node fact = inequalities[i];
        if (fact[0].getKind() == Kind::FINITE_FIELD_MULT &&  
        fact[1].getKind()== Kind::FINITE_FIELD_MULT &&
        fact[0][0].getConst<FiniteFieldValue>().getValue() == fact[1][0].getConst<FiniteFieldValue>().getValue())
        {
            NodeManager* nm = NodeManager::currentNM();
            inequalities.push_back(rewrite(nm->mkNode(Kind::EQUAL, fact[0][1], fact[1][1])));
        }
        }
}

/////////////////////////////////////////////////// FIELD ////////////////////////////////////////////////////////////////////


Field::Field(Env & env, Integer mod, RangeSolver* solv):EnvObj(env){
    modulos = mod;
    solver = solv;
    }

Integer inverse(Integer n, Integer p){
    Integer u = n;
    Integer v = p;
    Integer x1 = 1;
    Integer x2 = 0;
    Integer q;
    Integer r;
    Integer x;
    while( u!=1){
        q = v.floorDivideQuotient(u);
        r = v.floorDivideRemainder(u);
        x = x2 - q*x1;
        v = u;
        u = r;
        x2 = x1;
        x1 = x;
    }
    return x1.floorDivideRemainder(p);
}
// bool Field::CheckIfInvSmaller(Node eq){
//     if (eq.getKind() == Kind::CONST_INTEGER){
//         if (inverse(eq.getConst<Rational>().getNumerator()) 

//    }
// }

Integer Field::smallerInverse(Node fact){
    if (fact.getKind() == Kind::CONST_INTEGER){
        Integer temp = fact.getConst<Rational>().getNumerator().abs();
        if (temp.abs() == 1){
            return 0;
        }
        Integer inv = temp.moduloInverse(modulos).abs();
        if( inv < temp.abs() ){
            // std::cout << "TEMP" << temp <<"\n";
            // std::cout << "MOD" << modulos <<"\n";
            // std::cout << "INV" << inv <<"\n";
            return inv;
        }
        return 0;
    }
    for (int i = 0; i< fact.getNumChildren(); i++){
        Integer inv = smallerInverse(fact[i]);
        if (inv!=0){
            return inv;
        }
    }
    return 0;
}

void Field::CancelConstants(){
    if (!modulos.isProbablePrime()){
        return;
    }
    //std::cout << "CANCEL CONSTANTS FOR" <<modulos << "\n";
    for (int i=0; i<equalities.size(); i++){
        Node fact = equalities[i];
        // std::cout << toString(fact[0].getKind()) << "\n";
        // std::cout << (fact[0].getKind() == Kind::MULT) << "\n";
        // std::cout << (fact[1].getKind() == Kind::MULT) << "\n";
        if ( (fact[0].getKind() == Kind::MULT || fact[0].getKind() == Kind::NONLINEAR_MULT)  &&  
        (fact[1].getKind() == Kind::MULT || fact[1].getKind() == Kind::NONLINEAR_MULT) 
        && fact[0].getNumChildren() ==2 && fact[1].getNumChildren() ==2){
        //std::cout << "PAssed check1"  << fact << "\n";
            if (fact[0][0] == fact[1][0])
            {
                NodeManager* nm = NodeManager::currentNM();
                addEquality(rewrite(nm->mkNode(Kind::EQUAL, fact[0][1], fact[1][1])), true);
            }
            if (fact[0][1] == fact[1][1])
            {
                 //std::cout << "PAssed check2"  << fact << "\n";
                NodeManager* nm = NodeManager::currentNM();
                addEquality(rewrite(nm->mkNode(Kind::EQUAL, fact[0][0], fact[1][0])), true);
            }
            if (fact[0][1] == fact[1][0])
            {
                 //std::cout << "PAssed check2"  << fact << "\n";
                NodeManager* nm = NodeManager::currentNM();
                addEquality(rewrite(nm->mkNode(Kind::EQUAL, fact[0][0], fact[1][1])), true);
            }
            if (fact[0][0] == fact[1][1])
            {
                 //std::cout << "PAssed check2"  << fact << "\n";
                NodeManager* nm = NodeManager::currentNM();
                addEquality(rewrite(nm->mkNode(Kind::EQUAL, fact[0][1], fact[1][0])), true);
            }


        }
    }      
    for (int i=0; i<inequalities.size(); i++){
        Node fact = inequalities[i];
         if (fact[0].getKind() == Kind::MULT &&  
        fact[1].getKind()== Kind::MULT){
            if (fact[0][0].getConst<Rational>().getValue() == fact[1][0].getConst<Rational>().getValue())
            {
                NodeManager* nm = NodeManager::currentNM();
                addEquality(rewrite(nm->mkNode(Kind::EQUAL, fact[0][1], fact[1][1])), true);
            }
            if (fact[0][1].getConst<Rational>().getValue() == fact[1][1].getConst<Rational>().getValue())
            {
                NodeManager* nm = NodeManager::currentNM();
                addEquality(rewrite(nm->mkNode(Kind::EQUAL, fact[0][0], fact[1][0])), true);
            }

        }
        }
}

Node Field::modOut(Node fact){
    //s//td::cout << fact << "\n";
     NodeManager* nm = NodeManager::currentNM();
     std::vector<Node> left;
     if (fact.getKind()== Kind::ADD){
        for(int i =0; i<fact.getNumChildren(); i++) {
        left.push_back(modOut(fact[i]));
        }
        return nm->mkNode(Kind::ADD, left);
     }
     if(fact.getKind()== Kind::MULT || fact.getKind()==Kind::NONLINEAR_MULT){
        for(int i =0; i<fact.getNumChildren(); i++) {
        left.push_back(modOut(fact[i]));
        }
        return nm->mkNode(Kind::MULT, left);
    }
    if(isVariableOrSkolem(fact)){
        //std::cout << fact;
        return fact;
    }
    if(fact.getKind()== Kind::CONST_INTEGER){
        //std::cout << "Before mod:" << fact.getConst<Rational>().getNumerator() << "\n";
        Integer new_value =fact.getConst<Rational>().getNumerator();
        if (!(new_value < 0 && new_value > modulos * -1)){
        new_value =new_value.floorDivideRemainder(modulos);
        }
        if (( new_value.abs() >= modulos.floorDivideQuotient(2)) && new_value * -1 < modulos ){
             if (new_value >0){
             new_value =  new_value- modulos;
             }
             else {
                new_value = new_value + modulos;
             }
        }
        // if (( new_value.abs() >= modulos.floorDivideQuotient(2)) && new_value * -1 > modulos ){
        //      new_value =  new_value + modulos;
        // }
        //std::cout << "After mod:" << modulos << "\n";
        if(modulos.divides(new_value)){
            return nm->mkConstInt(0);
        }
        Integer temp;
        if (new_value < 0){
            temp = new_value *-1;
        } else {
            temp = new_value;
        }
        // if (temp!=0 && temp!=1 && (*solver).fields.count(temp) == 0){
        //     Field temp_field = Field(d_env, temp, solver);
        //     temp_field.myNodes = myNodes;
        //     temp_field.myVariables = myVariables;
        //     (*solver).fields.insert(std::make_pair(temp,temp_field));
        //     // temp_field.myNodes = myNodes;
        //     // (*solver).fields[temp].myVariables = myVariables;
        // }
        // if (new_value > 0 && modulos.floorDivideQuotient(2) < new_value){
        //    //std::cout << "positive to negative\n";
        //     Node help= nm->mkConstInt(new_value - modulos);
        //     //std::cout << "LOOOk " << help.getConst<FiniteFieldValue>().getValue()<< "\n";
        //    // std::cout << help << "\n";
        //     //std::cout << rewrite(help)<< "\n";
        //     return help;
        // }
        // if (new_value < 0 && (modulos.floorDivideQuotient(2) < Integer(-1) * new_value)){
        //     //std::cout << "negative to positive\n";
        //     Node help= nm->mkConstInt(new_value + modulos);
        //     //std::cout << "LOOOk " << help.getConst<FiniteFieldValue>().getValue()<< "\n";
        //    // std::cout << help << "\n";
        //     //std::cout << rewrite(help)<< "\n";
        //     return help;
        // } 
        AlwaysAssert(new_value.abs() < modulos.abs()) << new_value  << "," << modulos;
        return nm->mkConstInt(new_value);
    }
    AlwaysAssert(false) << "Unsupported kind type in modout" << fact.getKind();

       

    // std::vector<Node> left;
    // NodeManager* nm = NodeManager::currentNM();
    // /// TODO FIX THIS
    // //std::cout << "Modout with" << fact << "\n";
    // if (fact.getKind()== Kind::FINITE_FIELD_ADD){
    // for(int i =0; i<fact.getNumChildren(); i++) {
    //     if (fact[i].getKind() == Kind::FINITE_FIELD_MULT && fact[i][0].getKind() == Kind::CONST_FINITE_FIELD 
    //     && modulos.divides(fact[i][0].getConst<FiniteFieldValue>().getValue())){}
    //     else {
    //         left.push_back(fact[i]);
    //     }
    // }
    // } else if (fact.getKind()== Kind::FINITE_FIELD_MULT) {
    //     if (fact[0].getKind() == Kind::CONST_FINITE_FIELD  && modulos.divides(fact[0].getConst<FiniteFieldValue>().getValue())){}
    //     else {
    //         if (fact[0].getKind() == Kind::CONST_FINITE_FIELD && (fact[0].getConst<FiniteFieldValue>().getValue() > 0 && modulos.floorDivideQuotient(2) < fact[0].getConst<FiniteFieldValue>().getValue())){
    //             Node new_fact =nm->mkConst(FiniteFieldValue(fact[0].getConst<FiniteFieldValue>().getValue() - modulos, modulos));
    //             fact[0] = new_fact;
    //             left.push_back(fact);
    //         }
    //         else {
    //         left.push_back(fact);
    //         }
    //     }
    // } else if (fact.getKind() == Kind::CONST_FINITE_FIELD  && modulos.divides(fact.getConst<FiniteFieldValue>().getValue())){}
    // else {
    //     left.push_back(fact);
    // }
    // if (left.size()==0){
    //     left.push_back(nm->mkConst(FiniteFieldValue::mkZero(modulos)));
    // }
    // //std::cout << "Finished \n";
    // return rewrite(nm->mkNode(Kind::FINITE_FIELD_ADD, left));
};


void Field::addEquality(Node fact, bool inField, bool GBAddition){
    //std::cout <<"Adding equality:" << fact << "\n";
    fact = rewrite(fact); 
    if (fact.getKind() == Kind::CONST_BOOLEAN){
        if (fact.getConst<bool>() == false){
            status = Result::UNSAT;
            //std::cout << "WE ARE HERE TM\n";
        }
        return;
    } 
    if (inField && std::find(equalities.begin(), equalities.end(), fact) == equalities.end()
        && fact.getKind() != Kind::CONST_BOOLEAN && fact.getKind()!=Kind::NULL_EXPR){
        AlwaysAssert(fact.getKind() == Kind::EQUAL) << fact;
        //GBAddition = true;
        if(!GBAddition){
            // std::stringstream ss;
            // ss.str("");
            // ss.clear();
            // NodeManager* nm = NodeManager::currentNM();
            // ss << replaceDots(nodeToString(nm->mkNode(Kind::SUB, fact[0], fact[1])));
            // // if (mySingularReduce.empty()){
            //     newEqualitySinceGB = true;
            //     equalities.push_back(fact);
            //     return;
            // }
            //std::cout << "NEW EQUALITY" << fact << "\n";
            newEqualitySinceGB = true;
            equalities.push_back(fact);
            ALLequalities.push_back(fact);
            return;
            //std::string line = mySingularReduce;
            // line = ReplaceGBStringInput("{6}", line, ss);
            // // std::cout << "About to run Singular\n";
            // // std::cout << line << "\n";
            // // std::cout << "running Singular\n";
            // std::string output = runSingular(line);
            // // std::cout << "ran singular\n";
            // size_t pos =output.find('\n');
            // std::string result = output.substr(pos + 1);
            // //std::cout << line <<"\n";
            // //std::cout << output << "\n" ;
            // try{
            // if (std::stoi(result) == 0){
            //     return;
            // }
            // } catch (const std::invalid_argument& e) { 
            //     //std::cout << output << "\n";
            //     newEqualitySinceGB = true;
            //     equalities.push_back(fact);
            //     //std::cout << "For:" << modulos << "\n";
            //     return;
            // } catch (const std::out_of_range& e) { 
            //     //std::cout << output << "\n"; 
            //     newEqualitySinceGB = true;
            //     equalities.push_back(fact);
            //     //std::cout << "For:" << modulos << "\n";
            //     return;
               // };

        }

        //if(inField){
        newEqualitySinceGB = true;
        equalities.push_back(fact);
        ALLequalities.push_back(fact);
        return;
        //return;
    } else if (!inField) {
    //std::cout << "BEFORE" << fact << "\n";
        NodeManager* nm = NodeManager::currentNM();
        Node LHS = modOut(fact[0]);
        Node RHS = modOut(fact[1]);
    //std::cout << "LHS:" << LHS << "\n";
    //std::cout << "RHS:" << RHS << "\n";
        Node result = nm->mkNode(Kind::EQUAL, LHS, RHS);
        // if (std::find(equalities.begin(), equalities.end(), result) == equalities.end()
        // && result.getKind() != Kind::CONST_BOOLEAN && result.getKind()!=Kind::NULL_EXPR){
        addEquality(result, true, GBAddition);
             //std::cout << "\nNEW EQ:" << fact << "\n" << "for " << modulos;
            //newEqualitySinceGB = true;

        }
    //std::cout << "result" << result << "\n";
    //std::cout << rewrite(result) << "\n";
   // std::cout << "CHECK END\n";
   //std::cout << "After" << result << "\n";
    
    return;
    }
    //std::cout << "Already existed\n";
    //std::cout <<"Done adding equality:" << fact << "\n";

bool Field::ShouldLearnLemmas(Node fact,std::map<std::string, std::pair<Integer, Integer> > Bounds ){
    if (fact[0].getKind() == Kind::VARIABLE
    && (fact[1].getKind() == Kind::MULT || fact[1].getKind() == Kind::NONLINEAR_MULT)
    && fact[1][0].getKind() == Kind::VARIABLE
    && fact[1][1].getKind() == Kind::VARIABLE
    && fact[0].getName() == fact[1][0].getName()
    && fact[0].getName() == fact[1][1].getName()
    & modulos.isProbablePrime()) {
        NodeManager* nm = NodeManager::currentNM();
        lemmas.push_back(nm->mkNode(Kind::OR,
        nm->mkNode(Kind::EQUAL, fact[0],  nm->mkConstInt(0)) ,
        nm->mkNode(Kind::EQUAL, fact[0],  nm->mkConstInt(0))));
        status = Result::UNSAT;
        return true;
    }
    if (fact[1].getKind() == Kind::VARIABLE
    && (fact[0].getKind() == Kind::MULT || fact[0].getKind() == Kind::NONLINEAR_MULT)
    && fact[0][0].getKind() == Kind::VARIABLE
    && fact[0][1].getKind() == Kind::VARIABLE
    && fact[1].getName() == fact[0][0].getName()
    && fact[1].getName() == fact[0][1].getName()
    & modulos.isProbablePrime()) {
        NodeManager* nm = NodeManager::currentNM();
        lemmas.push_back(nm->mkNode(Kind::OR,
        nm->mkNode(Kind::EQUAL, fact[1], nm->mkConstInt(0)),
        nm->mkNode(Kind::EQUAL, fact[1], nm->mkConstInt(1))));
        status = Result::UNSAT;
        return true;
    }




    // if(fact[1].getKind()==Kind::CONST_FINITE_FIELD && 
    // fact[1].getConst<FiniteFieldValue>().getValue() == 0 
    // && fact[0].getKind() == Kind::FINITE_FIELD_MULT
    // && fact[0][0].getKind() == Kind::VARIABLE
    // && fact[0][1].getKind() == Kind::VARIABLE
    // && upperBounds[fact[0][0].getName()]<= modulos
    // && upperBounds[fact[0][1].getName()]<= modulos){
    //     NodeManager* nm = NodeManager::currentNM();
    //     lemmas.push_back(nm->mkNode(Kind::OR,
    //     nm->mkNode(Kind::EQUAL, fact[0][1], nm->mkConst(FiniteFieldValue::mkZero(fact[0].getType().getFfSize()) )),
    //     nm->mkNode(Kind::EQUAL, fact[0][0], nm->mkConst(FiniteFieldValue::mkZero(fact[0].getType().getFfSize()) ))));
    //     status = Result::UNSAT;
    //     return true;
    // }
    // if(fact[0].getKind()==Kind::CONST_FINITE_FIELD && 
    // fact[0].getConst<FiniteFieldValue>().getValue() == 0 
    // && fact[1].getKind() == Kind::FINITE_FIELD_MULT
    // && fact[1][0].getKind() == Kind::VARIABLE
    // && fact[1][1].getKind() == Kind::VARIABLE
    // && upperBounds[fact[1][0].getName()]<= modulos
    // && upperBounds[fact[1][1].getName()]<= modulos
    // ){
    //     NodeManager* nm = NodeManager::currentNM();
    //     lemmas.push_back(nm->mkNode(Kind::OR,
    //     nm->mkNode(Kind::EQUAL, fact[1][1], nm->mkConst(FiniteFieldValue::mkZero(fact[0].getType().getFfSize()) )),
    //     nm->mkNode(Kind::EQUAL, fact[1][0], nm->mkConst(FiniteFieldValue::mkZero(fact[0].getType().getFfSize()) ))));
    //     status = Result::UNSAT;
    //     return true;
    // }
    return false;

}


void Field::addInequality(Node fact){
    fact = rewrite(fact);
    if (fact.getKind() == Kind::CONST_BOOLEAN){
        if (fact.getConst<bool>() == true){
            status = Result::UNSAT;
            //std::cout << "WE ARE HERE TM\n";
        }
        return;
    }
    NodeManager* nm = NodeManager::currentNM();
    Node LHS = modOut(fact[0]);
    Node RHS = modOut(fact[1]);
    Node result = rewrite(nm->mkNode(Kind::EQUAL, LHS, RHS));
    if (std::find(inequalities.begin(), inequalities.end(), result) == inequalities.end()){
    inequalities.push_back(result);
    }
};


bool Field::Simplify(IntegerField& Integers, std::map<std::string, std::pair<Integer, Integer> > Bounds, bool WeightedGB, int startLearningLemmas){
    //std::cout << "Starting field simplifcation \n";
    // for (int i =0; i< equalities.size(); i++) {
    //         //std::cout << equalities[i] << "\n";
    //     }
    //Lift(Integers, upperBounds,startLearningLemmas);
    substituteVariables();
    // std::cout << "finished sub\n";
    // std::cout << "Started UNSAT\n";
    // //CancelConstants();
    // // std::cout << "equalities\n";
    // //  for (auto i: equalities) {
    // //     std::cout << i << "\n";
    // // }
    // // std::cout << "inequalities:" << "\n";
    // // for (auto i: inequalities) {
    // //     std::cout << i << "\n";
    // // }
    //checkUnsat();
    // Lift(Integers, Bounds,startLearningLemmas);
    //substituteVariables();
    //std::cout << "Substitute Vars done \n";
    //substituteEqualities();
    //std::cout << "Substitute Eqs done \n";
    //std::cout << "Checking Unsat is done \n";
    if (status == Result::UNSAT){
        return false;
    }
    //std::cout << "Finished UNSAT\n";
    
    NodeManager* nm = NodeManager::currentNM();
    if (newEqualitySinceGB ){
        //std::cout << "STARING GB\n";
        std::vector<Node> newPoly = SimplifyViaGB(this, Bounds, nm, WeightedGB);
        //TODO FOR LEGIBILITY THIS SHOULD BE SWAPPED 
         //std::cout << "Finished GB\n";
         //std::cout << newPoly.size() << "\n";
        if (newPoly.size() == 0 && equalities.size()!=0){
            //std::cout << equalities.size() << "\n";
            std::cout << "GB FAULT \n";
            status = Result::UNSAT;
            return false;
        }
       if (newPoly.size() != 0 && newPoly[0]== nm->mkConstInt(Integer(0))){
            return false;
            std::cout << "GB TOOK TOO LONG\n";
        }
        //std::cout <<  "Finished GB check\n";
        clearEqualities();
        for (Node poly: newPoly){
            //std::cout << "New Poly F:" << poly << "\n";
            if (rewrite(poly).getKind() == Kind::CONST_BOOLEAN && 
                rewrite(poly).getConst<bool>() == false){
                     status = Result::UNSAT;
                     //AlwaysAssert(lemmas.size()==0) << modulos;
                    return false;
            }
            addEquality(rewrite(poly), false, true);
            //std::cout << "WHAT\n";
        }
        newEqualitySinceGB = false;
        // std::cout << "MOD:" << modulos << "\n";
        // std::cout << "Equalities\n";
        // for(auto i : equalities){
        //     std::cout << i << "\n";
        // }
        // std::cout << equalities.size() << "\n";
        // std::cout << newPoly.size() << "\n";
        //AlwaysAssert(equalities.size() == newPoly.size());
    }
    // if (!WeightedGB && inequalities.size()>0 && equalities.size()>0){
    //     std::string line = singular_command_unweighted; 
    //     std::stringstream ss;
    //     ss << modulos;
    //     line = ReplaceGBStringInput("{1}", line, ss);
    //     ss.str("");
    //     ss.clear();
    //     //std::cout << (*F).myNodes.size() << "\n";
    //     int bound_count = 0;
    //     for (auto it =  (*solver).myVariables.begin(); it != (*solver).myVariables.end(); ++it) {
    //             ss << it->first;
    //         if (std::next(it) != (*solver).myVariables.end()) {
    //             ss << ",";
    //         }
    //     }
    //     line = ReplaceGBStringInput("{2}", line, ss);
    //     ss.str("");
    //     ss.clear();
        
    //     //std::cout << line << "\n";
    //     // ss << upperBounds.size();
    //     // line = ReplaceGBStringInput("{3}", line, ss);
    //     // ss.str("");
    //     // ss.clear();

    //     //std::cout << line << "\n";
    //     for (auto it = equalities.begin(); it != equalities.end(); ++it) {
    //         ss << replaceDots(nodeToString(nm->mkNode(Kind::SUB, (*it)[0], (*it)[1])));
    //         if (std::next(it) != equalities.end()) {
    //             ss << ",";
    //         }
    //     }
    //     line = ReplaceGBStringInput("{5}", line, ss);
    //     for(int i =0; i<inequalities.size(); i++){
    //         ss.str("");
    //         ss.clear();
    //         ss << replaceDots(nodeToString(nm->mkNode(Kind::SUB, inequalities[0][0], inequalities[0][1])));
    //         line = ReplaceGBStringInput("{6}", line, ss);
    //         std::string output = runSingular(line);
    //         std::cout << line <<"\n";
    //         std::cout << output << "\n" ;
    //         try{
    //         if (std::stoi(output) == 0){
    //             std::cout << "output zero! woo\n";
    //             status = Result::UNSAT;
    //             return false;
    //         }
    //         } catch (const std::invalid_argument& e) {
    //         } catch (const std::out_of_range& e) {};
    //     }
    //     //AlwaysAssert(false);

    // }
    //std::cout << "ADDED ALL EQUALITIES FOR FIELDS\n";
    //std::cout << "SIZE" << equalities.size() << "\n";
    //substituteVariables();
    //std::cout << "Substitute Vars done \n";
    //substituteEqualities();
    //std::cout << "Substitute Eqs done \n";
    //std::cout << "Checking Unsat is done \n";
    if (status == Result::UNSAT){
        return false;
    }
    //std::cout << "STARTING LIFTING GASP!\n";
    Lift(Integers, Bounds,startLearningLemmas);
    //std::cout << "finished lifting\n";
    return true;
};

bool isIntersectionNotEmpty(const std::set<std::string>& set1, const std::set<std::string>& set2) {
    // Check if any of the sets are empty
    if (set1.empty() || set2.empty()) {
        return false;
    }
    
    // Create a vector to store the intersection
    std::vector<std::string> intersection;

    // Find the intersection of the two sets
    std::set_intersection(set1.begin(), set1.end(),
                          set2.begin(), set2.end(),
                          std::back_inserter(intersection));

    // Return true if the intersection is not empty
    return !intersection.empty();
}

void Field::Lift(IntegerField& integerField, std::map<std::string, std::pair<Integer, Integer> > Bounds, int LearnLemmas){
     for (int i=0; i<equalities.size(); i++){
        if (checkIfConstraintIsMet(equalities[i], modulos, Bounds)){
            integerField.addEquality(equalities[i]);
        }
        else if(LearnLemmas == 1){
        // && LearntLemmasFrom.find(equalities[i])==LearntLemmasFrom.end()){
            ShouldLearnLemmas(equalities[i], Bounds);
            //LearntLemmasFrom.insert(equalities[i]);
        }
        else if(LearnLemmas == 2 && LearntLemmasFrom.find(equalities[i])==LearntLemmasFrom.end()
        && isIntersectionNotEmpty(getVarsHelper(equalities[i]), (*solver).myNotVars)){
        // && LearntLemmasFrom.find(equalities[i])==LearntLemmasFrom.end()){
            // std::cout << "TRY TO RANGE LIFT:" << equalities[i] << "for" << modulos<< "\n";
            // std::cout << equalities[i][1].getNumChildren()  << "\n";
            // std::cout <<  checkIfConstraintIsMet(equalities[i], modulos*2, Bounds) << "\n";
            if (equalities[i][1].getNumChildren() > 0 && checkIfConstraintIsMet(equalities[i], modulos*2, Bounds)){
                std::cout << "RANGE LIFT:" << equalities[i] << "\n";
                //AlwaysAssert(false);
                NodeManager* nm = NodeManager::currentNM();
                SkolemManager* sm = nm->getSkolemManager();
                Node sk = sm->mkDummySkolem("Q_HOLDER", nm->integerType());
                (*solver).myNodes.insert(sk);
                (*solver).myVariables[sk.getName()] = sk;
                lemmas.push_back(rewrite(nm->mkNode(Kind::EQUAL, equalities[i][0], 
                nm->mkNode(Kind::ADD, equalities[i][1],nm->mkNode(Kind::MULT, sk, nm->mkConstInt(Integer(modulos)))))));
                lemmas.push_back(rewrite(nm->mkNode(Kind::OR,
                                nm->mkNode(Kind::EQUAL, sk, nm->mkConstInt(Integer(0))),
                                 nm->mkNode(Kind::EQUAL, sk, nm->mkConstInt(Integer(1))))));
                std::cout << "LOOOK HERE!!!" << sk.getName() << "\n";
                (*solver).Bounds[sk.getName()] = std::make_pair(0,2);
                LearntLemmasFrom.insert(equalities[i]);
                status = Result::UNSAT;
                return;
        }
        }
        else {
            Integer inv = smallerInverse(equalities[i]);
            if(inv!=0){
                // std::cout << "INV:" << inv << "\n";
                // std::cout << "BEFORE" << equalities[i] << "\n";
                NodeManager* nm = NodeManager::currentNM();
                Node eq = nm->mkNode(Kind::
                EQUAL,
                rewrite(nm->mkNode(Kind::MULT, nm->mkConstInt(inv), equalities[i][0])),
                rewrite(nm->mkNode(Kind::MULT, nm->mkConstInt(inv), equalities[i][1])));
                // std::cout << "AFTER" << eq << "\n";
                // std::cout << "AFTER" << rewrite(eq) << "\n";
                addEquality(eq, false);
                //td::cout << "AFTER" << equalities[i] << "\n";
                //AlwaysAssert(inv != 1);
                //i--;
            }
        }

        // else if(LearnLemmas && LearntLemmasFrom.find(equalities[i])==LearntLemmasFrom.end()
        //     && ShouldLearnLemmas(equalities[i], upperBounds)){
        //         std::cout << equalities[i] << "\n";
        //         AlwaysAssert(false);
        //     // TODO THIS IS WRONG THINK ABOUT THIS AND FIX THIS 
        //     if (checkIfConstraintIsMet(equalities[i], modulos*2, upperBounds)){
        //         std::cout << equalities[i] << "\n";
        //         AlwaysAssert(false);
        //         NodeManager* nm = NodeManager::currentNM();
        //         SkolemManager* sm = nm->getSkolemManager();
        //         Node sk = sm->mkDummySkolem("Q_HOLDER", nm->integerType());
        //         (*solver).myNodes.insert(sk);
        //         (*solver).myVariables[sk.getName()] = sk;
        //         lemmas.push_back(rewrite(nm->mkNode(Kind::EQUAL, equalities[i][0], 
        //         nm->mkNode(Kind::ADD, equalities[i][1],nm->mkNode(Kind::MULT, sk, nm->mkConstInt(Integer(modulos)))))));
        //         lemmas.push_back(rewrite(nm->mkNode(Kind::OR,
        //                         nm->mkNode(Kind::EQUAL, sk, nm->mkConstInt(Integer(0))),
        //                          nm->mkNode(Kind::EQUAL, sk, nm->mkConstInt(Integer(1))))));
        //     //std::cout << "LOOOK HERE!!!" << sk.getName() << "\n";
        //         upperBounds[sk.getName()] = 2;
        //         LearntLemmasFrom.insert(equalities[i]);
        //         status = Result::UNSAT;
        //         return;
        //     }
        // }
     }
    // Can always lift inequalities
    for (int j=0; j<inequalities.size(); j++){
            //std::cout << "Adding inequality" << inequalities[j] << "\n";
            integerField.addInequality(inequalities[j]);
    }
}


void Field::substituteEqualities(){
    if (equalities.size() > 2){
        for (int i = 0; i< equalities.size(); i++){
            for(int j= i+1; j<equalities.size(); j++){
            if (equalities[i][0] == equalities[j][0] && i!=j){
                NodeManager* nm = NodeManager::currentNM();
                Node result = rewrite(nm->mkNode(Kind::EQUAL, equalities[i][1], equalities[j][1]));
                if (result.getKind() != Kind::CONST_BOOLEAN){
                        addEquality(result, true);}
            }
            if (equalities[i][1] == equalities[j][1] && i!=j){
                NodeManager* nm = NodeManager::currentNM();
                Node result = rewrite(nm->mkNode(Kind::EQUAL, equalities[i][0], equalities[j][0]));
                if (result.getKind() != Kind::CONST_BOOLEAN){
                        addEquality(result, true);}
            } 
        }
    }
}
}

Node Field::subVarHelper(Node fact, Node ogf, Node newf) {
    //  std::cout << 'Fact' << fact << "\n";
    //  std::cout << 'OGF' << ogf << "\n";
    //  std::cout << "Equality:" << (fact==ogf) << "\n";
    if (fact == ogf){
        return newf;
    }
    if (fact.getNumChildren()!=0){
        std::vector<Node> children ;
        for (int i =0; i<fact.getNumChildren(); i++){
            children.push_back(subVarHelper(fact[i], ogf, newf));
        }
        NodeManager* nm = NodeManager::currentNM();
        return nm->mkNode(fact.getKind(), children);
    }
    return fact;
}

Node IntegerField::subVarHelper(Node fact, Node ogf, Node newf) {
    //  std::cout << 'Fact' << fact << "\n";
    //  std::cout << 'OGF' << ogf << "\n";
    //  std::cout << "Equality:" << (fact==ogf) << "\n";
    if (fact == ogf){
        return newf;
    }
    if (fact.getNumChildren()!=0){
        std::vector<Node> children ;
        for (int i =0; i<fact.getNumChildren(); i++){
            children.push_back(subVarHelper(fact[i], ogf, newf));
        }
        NodeManager* nm = NodeManager::currentNM();
        return nm->mkNode(fact.getKind(), children);
    }
    return fact;

}

void IntegerField::substituteVariables(){
    if (equalities.size() <= 1){ 
        return;
    }
    //std::vector<Node> neqEq;
    for (int i =0; i<equalities.size(); i++){
        Node fact = equalities[i];
        //std::cout << "FACT:" << fact << "\n";
        if (isVariableOrSkolem(fact[0]) && fact[1].getKind() == Kind::CONST_INTEGER){
            for (int j=0; j<equalities.size(); j++){
                if (j!=i){
                //std::cout << "OLD:" << equalities[j] << "\n";  
                equalities[j] = subVarHelper(equalities[j], equalities[i][0], equalities[i][1]);   
                //std::cout << "NEW:" << equalities[j] << "\n";
                //std::cout << "REW:" << rewrite(equalities[j]) << "\n";
                }   
            }
            for (int k=0; k<inequalities.size(); k++){
                inequalities[k] = rewrite(subVarHelper(inequalities[k], equalities[i][0], equalities[i][1]));
                if (inequalities[k].getKind() == Kind::CONST_BOOLEAN && inequalities[k].getConst<bool>()== false){
                    inequalities.erase(inequalities.begin()+k);
                    k--;
                } 
                // std::cout << "NEW:" << inequalities[k] << "\n";
                // std::cout << "REW:" << rewrite(inequalities[k]) << "\n"; 
            }
            // equalities.erase(equalities.begin()+i);
            //  i--;
        }
    }
    // std::cout << "Equalities\n";
    // for (int i =0; i<equalities.size(); i++){
    //     std::cout << equalities[i] << "\n";
    // }

}


void Field::substituteVariables(){
    if (equalities.size() == 0){ 
        return;
    }
    //std::vector<Node> neqEq;
    for (int i =0; i<equalities.size(); i++){
        //std::cout << "Starting new fac loop\n";
        Node fact = equalities[i];
        //std::cout << "FACT:" << fact << "\n";
        if (isVariableOrSkolem(fact[0]) && fact[1].getKind() == Kind::CONST_INTEGER){
            for (int j=0; j<equalities.size(); j++){
                if (j!=i){
                //std::cout << "OLD:" << equalities[j] << "\n";  
                equalities[j] = subVarHelper(equalities[j], equalities[i][0], equalities[i][1]);   
                // std::cout << "NEW:" << equalities[j] << "\n";
                // std::cout << "REW:" << rewrite(equalities[j]) << "\n";
                }   
            }
            for (int k=0; k<inequalities.size(); k++){
                inequalities[k] = rewrite(subVarHelper(inequalities[k], equalities[i][0], equalities[i][1]));
                if (inequalities[k].getKind() == Kind::CONST_BOOLEAN && inequalities[k].getConst<bool>()== false){
                    inequalities.erase(inequalities.begin()+k);
                    k--;
                } 
                // std::cout << "NEW:" << inequalities[k] << "\n";
                // std::cout << "REW:" << rewrite(inequalities[k]) << "\n"; 
            }
        }
        //std::cout << "Finished fact loop\n";
    }
    // std::cout << "Finished subs\n";
    // std::cout << "Equalities\n";
    // for (int i =0; i<equalities.size(); i++){
    //     std::cout << equalities[i] << "\n";
    // }
    // std::cout << "InEqualities\n";
    // for (int i =0; i<inequalities.size(); i++){
    //     std::cout << inequalities[i] << "\n";
    // }
    // std::cout << "Done\n";

}

//std::cout << "Substitute variables\n";
    // for (int i = 0; i<equalities.size(); i++){
    //     Node fact = equalities[i];
    //     //std::cout << "We are here?" << fact << "\n";
    // if ( (isVariableOrSkolem(fact[0]) 
    //     &&  isVariableOrSkolem(fact[1]) )|| 
    //    (isVariableOrSkolem(fact[0]) && 
    //     fact[1].getKind() == Kind::CONST_INTEGER
    //     )){
    //     std::vector<Node> new_inequalities;
    //         for(Node assert: inequalities){
    //             if (assert!=fact){
    //             //      std::cout << "STARTING";
    //             //      std::cout << "EQ:" << fact << "\n";
    //             //      std::cout << "INEQ:" << assert << "\n";
    //             Node new_ineq = subVarHelper(assert, fact[0], fact[1]);
    //             // std::cout << "NEW INEQ:" << new_ineq << "\n";
    //              new_ineq = rewrite(new_ineq);
    //             // std::cout << "NEW INEQ REWRITE:" << new_ineq << "\n";
    //             if(new_ineq.getKind() == Kind::CONST_BOOLEAN){
    //                 if (new_ineq.getConst<bool>() == false){
    //                     //  std::cout << "INEQ"<< assert << "\n";
    //                     //  std::cout << "FACT" << fact << "\n";
    //                     // AlwaysAssert(false);
    //                     // new_inequalities.push_back(assert);
    //                 }
    //                 if (new_ineq.getConst<bool>() == true){
    //                     // std::cout << "SUB VARS\n";
    //                     // std::cout << assert << "\n";
    //                     // std::cout << fact << "\n";
    //                     status = Result::UNSAT;
    //                     return;
    //                 }
    //             } else {
    //             new_inequalities.push_back(new_ineq);}
    //             }
    //         }
    //     // if (isVariableOrSkolem(fact[1])){
    //     //             Node new_ineq = rewrite(subVarHelper(assert, fact[1], fact[0]));
    //     //         if(new_ineq.getKind() == Kind::CONST_BOOLEAN){
    //     //             if (new_ineq.getConst<bool>() == false){
    //     //                 // std::cout << "OH NO!!!!!"  << "\n";
    //     //                 // std::cout << fact << "\n";
    //     //                 // std::cout << assert << "\n";
    //     //                 AlwaysAssert(false);
    //     //                  new_inequalities.push_back(assert);
    //     //             }
    //     //             if (new_ineq.getConst<bool>() == true){
    //     //                 std::cout << "SUB VARS\n";
    //     //                 std::cout << assert << "\n";
    //     //                 std::cout << fact << "\n";
    //     //                  status = Result::UNSAT;
    //     //                 return;
    //     //             }
    //     //         } else {
    //     //         new_inequalities.push_back(new_ineq);}
    //     //         }
    //     //         } else {
    //     //             status = Result::UNSAT;
    //     //             return;
    //     //         }
    //     //     }
    //     //clearInequalities();
    //     for(auto j:new_inequalities){
    //         addInequality(j);
    //     }
    //}
    // if  (isVariableOrSkolem(fact[1]) && !isVariableOrSkolem(fact[0])){
    //     std::vector<Node> new_inequalities;
    //         for(Node assert: inequalities){
    //             if (assert!=fact){
    //             std::cout << "Sub var\n";
    //             Node new_ineq = subVarHelper(assert, fact[1], fact[0]);
    //             std::cout << "End Sub var\n";
    //             if(new_ineq.getKind() == Kind::CONST_BOOLEAN){
    //                 if (new_ineq.getConst<bool>() == false){
    //                 }
    //                 if (new_ineq.getConst<bool>() == true){
    //                     // std::cout << "SUB VARS\n";
    //                     // std::cout << assert << "\n";
    //                     // std::cout << fact << "\n";
    //                      status = Result::UNSAT;
    //                     return;
    //                 }
    //             } else {
    //             new_inequalities.push_back(new_ineq);}
    //             } else {
    //                 // std::cout << "SUB VARS\n";
    //                 // std::cout << assert << "\n";
    //                 // std::cout << fact << "\n";
    //                 status = Result::UNSAT;
    //                 return;
    //             }
    //         }
        //clearInequalities();
        // for(auto j:new_inequalities){
        //     addInequality(j);
        // }

    //}
    // }
    // }


bool Field::checkUnsat(){
    if (equalities.size() == 0 || inequalities.size() == 0){
        return false;
    }
    if (status == Result::UNSAT){
        return true;
    }
    for(int i=0; i<inequalities.size(); i++){
        if (inequalities[i].getKind()== Kind::CONST_BOOLEAN &&
            inequalities[i].getConst<bool>() == true){
            status = Result::UNSAT;
            return true;
            }
        for(int j=0; j<equalities.size(); j++){
            if((inequalities[i][0]==equalities[j][0]) &&
               (inequalities[i][1]==equalities[j][1]) ){
                // std::cout << "FIELD UNSAT\n";
                // std::cout << "INEQ:" << inequalities[i] << "\n";
                // std::cout << "EQ:" << equalities[j] << "\n";
                status = Result::UNSAT;
                return true;
               }
        }
    }
    return false;
}

/////////////////////////////////////////////////// RangeSolver ////////////////////////////////////////////////////////////////////

RangeSolver::RangeSolver(Env& env, TheoryArith& parent)
    :EnvObj(env), integerField(env), d_facts(context()){}

void RangeSolver::preRegisterTerm(TNode node){ 
      /// Check Field  ONLY WHEN OPERATION IS EQUAL OR NOT EQUAL
    //   if (node.getKind() == Kind::VARIABLE) {
    //     TypeNode ty = node[0].getType();
    //     std::cout << ty << "\n";
    //     if (upperBounds.find(node.getName()) == upperBounds.end()){
    //         upperBounds[node.getName()] = ty.getFfSize();
    //     }
    //     else {
    //         upperBounds[node.getName()] = std::min(ty.getFfSize(), upperBounds[node.getName()]);
    //     }
    //   }
        if (node.getKind() == Kind::VARIABLE ){
            // if (upperBounds.count(node.getName())==0){
            std::string singularName = replaceDots(node.getName());
            myVariables[singularName] = node;
            myNodes.insert(node);
            // }
            Bounds[node.getName()] = std::make_pair(Integer(-1) *BIGINT, BIGINT);
        }
      if (node.getKind() == Kind::CONST_INTEGER){
        Integer constant = node.getConst<Rational>().getNumerator();
        if (constant < 0){constant = constant * -1;};
        if (constant == 0 || constant == 1 ){
            return;
        }
        else if (fields.count(constant)==0){
            fields.insert(std::make_pair(constant, Field(d_env,constant, this)));
      } 
      } else {
        if (node.getKind() == Kind::EQUAL) {
            if (node[0].getKind() == Kind::INTS_MODULUS || node[0].getKind() == Kind::INTS_MODULUS_TOTAL){
                Integer new_size = node[0][1].getConst<Rational>().getNumerator();
                 if (fields.count(new_size) == 0) {
                fields.insert(std::make_pair(new_size, Field(d_env,new_size, this)));
            }
        }
      }
    }
}



void RangeSolver::notifyFact(TNode fact){
    d_facts.emplace_back(fact); 
}

void RangeSolver::processFact(TNode fact){
    //std::cout << fact << "\n";
    NodeManager* nm = NodeManager::currentNM();
    if(fact.getKind() == Kind::GEQ && fact[0].getNumChildren()<=1){
        AlwaysAssert(fact[1].getKind()==Kind::CONST_INTEGER) << fact;
        Integer Bound = fact[1].getConst<Rational>().getNumerator();
        if (fact[0].getKind()!=Kind::VARIABLE){
            AlwaysAssert(false) << fact;
            }
            else {
            Bounds[fact[0].getName()].first = Bound;
            }
    }
    else if(fact.getKind() == Kind::GEQ && fact[0].getNumChildren()>1){
        if (fact[0].getKind() == Kind::MULT && 
            fact[0][0].getKind() == Kind::CONST_INTEGER &&
            fact[0][0].getConst<Rational>().getNumerator() == Integer(-1) &&
            fact[0][1].getKind() == Kind::VARIABLE &&
            fact[1].getKind() == Kind::CONST_INTEGER){
            //std::cout << "PROCESSING" << fact << "\n";
            }
            Integer Bound = Integer(-1) * fact[1].getConst<Rational>().getNumerator();
            Bounds[fact[0][1].getName()].second = Bound;

            //AlwaysAssert(fact[1].getConst<Rational>().getNumerator() == Integer(0)) << fact;}
    }
    else if(fact.getKind() == Kind::NOT && fact[0].getKind()==Kind::GEQ){
            AlwaysAssert(fact[0][1].getKind()==Kind::CONST_INTEGER) << fact;
            Integer Bound = fact[0][1].getConst<Rational>().getNumerator()-1;
            //AlwaysAssert(Bound > 0) << fact;
        if (fact[0][0].getKind()!=Kind::VARIABLE){
            AlwaysAssert(false) << fact;
            //     NodeManager* nm = NodeManager::currentNM();
            //     SkolemManager* sm = nm->getSkolemManager();
            //     Node sk = sm->mkDummySkolem("Var", nm->integerType());
            //     upperBounds[sk.getName()] = Bound;
            //     Node new_node = nm->mkNode(Kind::EQUAL, sk, fact[0]);
            //     auto it = fields.find(new_node[0].getType().getFfSize());
            //     if (it != fields.end()) {
            // //std::cout << "Adding Equality\n";
            //     it->second.addEquality(new_node, false);
            //     } else {;
            //         AlwaysAssert(false);
            //     }
            //     std::cout << sk.getName() << "\n";

            }
            else {
            Bounds[fact[0][0].getName()].second = Bound;
            }
        }
    else if (fact.getKind() == Kind::EQUAL) {
        if (fact[0].getKind() == Kind::INTS_MODULUS || fact[0].getKind() == Kind::INTS_MODULUS_TOTAL){
            Integer size = fact[0][1].getConst<Rational>().getNumerator();
            auto it = fields.find(size);
            if (it != fields.end()) {
            //std::cout << "Adding Equality\n";
             it->second.addEquality(
                nm->mkNode(Kind::EQUAL, fact[0][0], nm->mkConstInt(0)), false, true);
            } else {;
            AlwaysAssert(false);
        }
        }
        else {
            integerField.addEquality(fact);
        }
    }
    else if (fact.getKind() == Kind::NOT){
        AlwaysAssert(fact[0].getKind()== Kind::EQUAL) << fact;
        std::set<std::string> newNotVars = getVarsHelper(fact[0]);
        //std::cout << "got here\n";
        myNotVars.insert(newNotVars.begin(), newNotVars.end());
        if (fact[0][0].getKind() == Kind::INTS_MODULUS || fact[0][0].getKind() == Kind::INTS_MODULUS_TOTAL){
            Integer size = fact[0][0][1].getConst<Rational>().getNumerator();
            auto it = fields.find(size);
            if (it != fields.end()) {
            //std::cout << "Adding Equality\n";
             it->second.addInequality(nm->mkNode(Kind::EQUAL, fact[0][0][0], nm->mkConstInt(0)));
            } else {
            //printSystemState();
            AlwaysAssert(false) << fact[0][0];
        }
        }
        else {
            integerField.addInequality(fact[0]);
        }
    }
    else {
        std::cout << "Not set up for this fact\n";
        AlwaysAssert(false);
    }
    //std::cout << "Done with fact\n";

}

void RangeSolver::setTrivialConflict()
{
  std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
}


Result RangeSolver::Solve(){
    #ifdef CVC5_USE_COCOA
    #else 
        noCoCoALiza();
    #endif
    //std::cout << "We are here\n";
    int count = 0;
    bool WeightedGB = true;
    int startLearningLemmas = 0;
    for (auto& fieldPair :fields){
            fieldPair.second.newEqualitySinceGB = true;
            fieldPair.second.myNodes = myNodes;
            fieldPair.second.myVariables = myVariables;
        }
    bool movesExist = true;
    while(movesExist){
        
        // //std::cout << count << "\n";
    // if (count>3){
    //  AlwaysAssert(false);
    // }
    // count+=1;
    //   if (count >=10){
    //     startLearningLemmas = 1;    
    //    }
    //   if (count >=25){
    //        WeightedGB = false;
    //        startLearningLemmas = 0;
    //     }
    // //          //startLearningLemmas = true;
    // //     }
    //     if (count >=20){
    //      WeightedGB = true;
    //       startLearningLemmas = 2;
    //     //      //startLearningLemmas = true;
    //      }
    //    if (count >=30){
    //          AlwaysAssert(false);
    //  }
        printSystemState();
        //std::cout << "FINISHED INTEGERS\n";
        for (auto& fieldPair :fields){
            fieldPair.second.Simplify(integerField, Bounds, WeightedGB, startLearningLemmas);
            if (fieldPair.second.status == Result::UNSAT && fieldPair.second.lemmas.size()== 0){
                return Result::UNSAT;
            }

        }
        integerField.Simplify(fields, Bounds);
        if (integerField.status == Result::UNSAT){
            integerField.status = Result::UNKNOWN;
            return Result::UNSAT;
        }
        //std::cout << "FINISHED FIELDS\n";
        bool saturated = false;
        for (auto fieldPair :fields){
            saturated = true;
            if (fieldPair.second.status == Result::UNSAT){
                //std::cout << "WE HERE\n";
                if (fieldPair.second.lemmas.size()> 0){
                    Lemmas = fieldPair.second.lemmas;
                    //std::cout << "LEARNED NEW LEMMA" << Lemma << "\n";
                    fieldPair.second.lemmas.clear();
                    AlwaysAssert( fieldPair.second.lemmas.size()==0);
                    fieldPair.second.status = Result::UNKNOWN;
                    return Result::UNKNOWN;

                }
                //std::cout << "UNSAT\n";
                //printSystemState();
                fieldPair.second.status = Result::UNKNOWN;
                return Result::UNSAT;
            }
            if (fieldPair.second.newEqualitySinceGB == true){
                saturated = false;
                //std::cout << fieldPair.second.modulos << "\n";
            }
        }
        if (saturated && startLearningLemmas){
            std::cout << "GB SATURATED NOTHING TO DO\n";
            movesExist = false;
        }
        // if (saturated && startLearningLemmas){
        //         //AlwaysAssert(false) << "GB SATURATED NOTHING TO DO\n";
        //    WeightedGB = false ;
        // }
        if (saturated){
            startLearningLemmas = 2;
        }
        //     startLearningLemmas = true;
        //      //AlwaysAssert(false);
        // }
    
        //   if (integerField.status == Result::SAT){
        //         //std::cout << "WE GOT SAT\n";
        //     return Result::SAT;
         count +=1;
         }

       //Now we need to go back to the ST procedure from finite fields 

        //step 1: find the largest field in the map
        auto it = fields.rbegin(); // reverse iterator to the last element of the map
        Field largestRing = it->second; 
        
        //step 2: compute an ideal for said field using CoCoA
        std::vector<CoCoA::RingElem> myIdeal = getCococaGB(&largestRing);

        //step 3: run the applyZero from finite fields 
        std::vector<CoCoA::RingElem> root = ff::findZero(myIdeal, d_env);

          if (root.empty())
          {
            // UNSAT
            setTrivialConflict();
            return Result::UNSAT;
          }
          else
          {
            std::cout << "Found model but we don't know how to process it\n";
          }
    //       {
    //         // SAT: populate d_model from the root
    //         Assert(d_model.empty());
    //         NodeManager* nm = NodeManager::currentNM();
    //         for (const auto& [idx, node] : enc.nodeIndets())
    //         {
    //           if (isFfLeaf(node))
    //           {
    //             Node value = nm->mkConst(enc.cocoaFfToFfVal(root[idx]));
    //             Trace("ff::model")
    //                 << " " << node << " = " << value << std::endl;
    //             d_model.emplace(node, value);
    //           }
    //         }
    //       }
    //     }
    //   }
        //(not ultiamtely it will probably be something else but idk how to do that rn)


        //count +=1;
};

 std::vector<Node>& RangeSolver::conflict() {

    d_conflict.clear();
    std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
    return d_conflict;}

Result RangeSolver::postCheck(Theory::Effort level){
    //std::cout << level << "\n";
    integerField.clearAll();
    for(auto &f : fields){
        f.second.clearAll();
    }
    for (auto fact:d_facts){
        processFact(fact);
    }
    //std::cout << level << "\n";
    return Solve();
}

void RangeSolver::printSystemState(){
    std::cout << "\n\n PRINTING STATE \n";
    std::cout << "Num Fields:" << fields.size() << "\n"; 
    std::cout << "INTEGER" << "\n";
    std::cout << "equalities:" << "\n";
    for (auto i: integerField.equalities) {
        std::cout << i << "\n";
    }
    std::cout << "inequalities:" << "\n";
    for (auto i: integerField.inequalities) {
        std::cout << i << "\n";
    }
    for (auto pair: fields){
        std::cout << pair.first << "\n";
        std::cout << pair.second.status << "\n";
        std::cout << "equalities" << "\n";
         for (int i =0; i< pair.second.equalities.size(); i++) {
            std::cout << pair.second.equalities[i] << "\n";
        }
        std::cout << "inequalities" << "\n";
         for (auto i: pair.second.inequalities) {
            std::cout << i << "\n";
        }
    }
    std::cout << "Bounds\n";
    for(auto i : Bounds){
        std::cout << "(" << i.first << "," << i.second  << ")\n";
    }
    std::cout << "DONE!" << "\n\n\n";
}






}
}
}
}
