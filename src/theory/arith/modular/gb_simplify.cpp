

#include <filesystem>
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
#include "theory/arith/modular/gb_simplify.h"
#include "theory/ff/multi_roots.h"
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


using namespace cvc5::internal::kind;

using namespace cvc5::internal::theory::ff::singular;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace modular_range_solver {

std::string singular_command_weighted = "option(redSB); ring r = (integer, {1}), ({2}), (wp({4})); ideal I= {5}; ideal G= std(I); G; quit;";
std::string singular_command_weighted_integers = "option(redSB); ring r = integer, ({2}), (Dp); ideal I= {5}; ideal G= std(I); G; quit;";
std::string singular_command_reduce_integers = "ring r = integer, ({2}), (Dp); ideal I= {5}; reduce({6}, I); quit;";

std::string singular_command_reduce = "ring r = (integer, {1}), ({2}), (wp({4})); ideal I= {5}; reduce({6}, I); quit;";
std::string singular_command_unweighted = "option(redSB); ring r = (integer, {1}), ({2}), (Dp); ideal I= {5}; ideal G= std(I); G; quit;";
std::string singular_command_reduce_uw = "ring r = (integer, {1}), ({2}), (Dp); ideal I= {5}; reduce({6}, I); quit;";

Integer BIGINT = Integer("26697537170649044179042152467634255803129704511815242562837925141177577913409118302943186911045680008195241138225131464058766427708039764790250144472755736885526820882067462431042573357558604819957849");

long BIGINTLOG = 10 * log2(BIGINT.getDouble());

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

std::string replaceDots(std::string name) {
    std::string str = name;
    // if (!str.empty() && str.front() == '_') {
    //     str = "xxx" + str; // Prepend "xxx" to input
    // }
    size_t start_pos = 0;
    while((start_pos = str.find('.', start_pos)) != std::string::npos) {
        str.replace(start_pos, 1, "_");
        start_pos += 1; // Move past the replaced part
    }
    start_pos = 0;
    while((start_pos = str.find('_', start_pos)) != std::string::npos) {
        str.replace(start_pos, 1, "x");
        start_pos += 1; // Move past the replaced part
    }
    return str;
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
        // if (!weightedGB && notVars.find(symbol) !=notVars.end()){
        //     std::cout << "SUBTRACTING WEIGHTS\n";
        //     answer[answer.size()-1] = std::min((answer[answer.size()-1] - 30), (long)0);
        // }
    }
    return answer;
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


Node monomialToNode(Monomial mono, NodeManager* nm, IntegerField *F){
    std::vector<Node> powers;
    powers.push_back(nm->mkConstInt(mono.coeff));
    for(auto i: mono.varPowers){
        for (int j =0; j< i.power; j++){
            powers.push_back((*(*F).solver).myVariables[i.var.name]);
        }
    }
    return nm->mkNode(Kind::MULT, powers);
}



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

std::vector<Node> SimplifyViaGB(Field *F, std::map<std::string, std::pair<Integer, Integer> > Bounds, NodeManager* nm, bool inIntegers){
    // std::cout << (*F).modulos << "\n";
    // std::cout << (*F).equalities.size() << "\n";
      if ((*F).equalities.size() <= 1) {
        return (*F).equalities;
      }
      //std::cout << "Getting weights\n";
     std::vector<long> weights = getWeights((*(*F).solver).myVariables, (*(*F).solver).Bounds, false, (*(*F).solver).myNotVars);
     //std::cout << "Got Weights\n";
    // std::ifstream inputFile("theory/arith/modular/gb_input.txt");

    // // Check if the file was successfully opened
    // if (!inputFile.is_open()) {
    //     AlwaysAssert(false) << "Singular GB input file does not exist";
    // }
    // Read and print the contents of the file
    std::string line;

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
   // std::cout << "got weights\n";
    line = ReplaceGBStringInput("{4}", line, ss);
    ss.str("");
    ss.clear();
    //std::cout << (*F).equalities.size() << "\n";
    for (auto it = (*F).equalities.begin(); it != (*F).equalities.end(); ++it) {
        //std::cout <<(*it) << "\n";
        ss << replaceDots(nodeToString(nm->mkNode(Kind::SUB, (*it)[0], (*it)[1])));
        if (std::next(it) != (*F).equalities.end()) {
            ss << ",";
        }
    }
    //std::cout << "Got Equalities";
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
        //std::cout << (*F).inequalities.size() << "\n";
        if ((*F).inequalities.size() > 0){
        for(int i =0; i<(*F).inequalities.size(); i++){
            if ((*F).inequalities[i].getKind() == Kind::CONST_BOOLEAN &&
                    (*F).inequalities[i].getConst<bool>()==  true){
                        //AlwaysAssert(false);
                        (*F).status = Result::UNSAT;
                        std::cout << "set status unsat?" << (*F).modulos << "\n";
                        //AlwaysAssert(false);
                        return EmptyPolys;
                    }
           // std::cout << (*F).inequalities[i] << "\n";
            ss.str("");
            ss.clear();
            ss << replaceDots(nodeToString(nm->mkNode(Kind::SUB, (*F).inequalities[i][0], (*F).inequalities[i][1])));
            line = ReplaceGBStringInput("{6}", line, ss);
            auto result = std::make_shared<std::string>("");
            std::shared_ptr<bool> done = std::make_shared<bool>(false);
    std::mutex resultMutex;
    //std::cout << "Running Singular2\n";
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
            //std::cout << line <<"\n";
            //std::cout << output << "\n" ;
            size_t pos =output.find('\n');
            std::string result1 = output.substr(pos + 1);
            try{
            if (std::stoi(result1) == 0){
                std::cout << "OUTPUT ZERO WWOOO\n";
                (*F).status = Result::UNSAT;
                std::cout << "set status unsat?" << (*F).modulos << "\n";
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


std::vector<Node> SimplifyViaGB(IntegerField *F, std::map<std::string, std::pair<Integer, Integer> > Bounds, NodeManager* nm, bool inIntegers){
    // std::cout << (*F).modulos << "\n";
    // std::cout << (*F).equalities.size() << "\n";
      if ((*F).equalities.size() <= 1) {
        return (*F).equalities;
      }
      //std::cout << "Getting weights\n";
     //std::cout << "Got Weights\n";
    // std::ifstream inputFile("theory/arith/modular/gb_input.txt");

    // // Check if the file was successfully opened
    // if (!inputFile.is_open()) {
    //     AlwaysAssert(false) << "Singular GB input file does not exist";
    // }
    // Read and print the contents of the file
   //} else {
     //
     
    std::string line = singular_command_weighted_integers;


    //}
    //inputFile.close();
    std::stringstream ss;
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
    

   // std::cout << "got weights\n";
    //std::cout << (*F).equalities.size() << "\n";
    for (auto it = (*F).equalities.begin(); it != (*F).equalities.end(); ++it) {
        //std::cout <<(*it) << "\n";
        ss << replaceDots(nodeToString(nm->mkNode(Kind::SUB, (*it)[0], (*it)[1])));
        if (std::next(it) != (*F).equalities.end()) {
            ss << ",";
        }
    }
    //std::cout << "Got Equalities";
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

    line = singular_command_reduce_integers;
    //} else {
    //l//ine = singular_command_reduce_uw;
    //} 
    ss.str("");
    ss.clear();
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
        

        
        //std::cout << line << "\n";
        // ss << upperBounds.size();
        // line = ReplaceGBStringInput("{3}", line, ss);
        // ss.str("");
        // ss.clear();

       
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
        //(*F).mySingularReduce = line;
        //std::cout << "we got here\n";
        //std::cout << (*F).inequalities.size() << "\n";
        if ((*F).inequalities.size() > 0){
        for(int i =0; i<(*F).inequalities.size(); i++){
            if ((*F).inequalities[i].getKind() == Kind::CONST_BOOLEAN &&
                    (*F).inequalities[i].getConst<bool>()==  true){
                        //AlwaysAssert(false);
                        (*F).status = Result::UNSAT;
                        std::cout << "set status unsat? integers" << "\n";
                        //AlwaysAssert(false);
                        return EmptyPolys;
                    }
           // std::cout << (*F).inequalities[i] << "\n";
            ss.str("");
            ss.clear();
            ss << replaceDots(nodeToString(nm->mkNode(Kind::SUB, (*F).inequalities[i][0], (*F).inequalities[i][1])));
            line = ReplaceGBStringInput("{6}", line, ss);
            auto result = std::make_shared<std::string>("");
            std::shared_ptr<bool> done = std::make_shared<bool>(false);
    std::mutex resultMutex;
    //std::cout << "Running Singular2\n";
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
            //std::cout << line <<"\n";
            //std::cout << output << "\n" ;
            size_t pos =output.find('\n');
            std::string result1 = output.substr(pos + 1);
            try{
            if (std::stoi(result1) == 0){
                std::cout << "OUTPUT ZERO WWOOO\n";
                (*F).status = Result::UNSAT;
                std::cout << "set status unsat? INTEGERS" << "\n";
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

}
}
}
}
