

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
#include "theory/arith/modular/util.h"
#include "theory/arith/modular/gb_simplify.h"
#include "theory/arith/modular/range-solver.h"
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
#include <cmath>
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



//using namespace cvc5::internal::theory::ff;

using namespace cvc5::internal::kind;

using namespace cvc5::internal::theory::ff::singular;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace modular_range_solver {


/////////////////////////////////////////////////// UTILS ////////////////////////////////////////////////////////////////////

int gcd(int a, int b) {
    return b == 0 ? a : gcd(b, a % b);
}

void printBasis(const std::vector<std::vector<Rational>>& basis) {
    std::cout << "The basis vectors are:\n";
    for (const auto& vec : basis) {
        std::cout << "(";
        for (size_t i = 0; i < vec.size(); ++i) {
            std::cout << vec[i];
            if (i < vec.size() - 1) {
                std::cout << ", ";  // Add commas between elements
            }
        }
        std::cout << ")\n";  // Ensure each vector is printed on a new line
    }
}

bool isVariableOrSkolem(Node node) {
    return (node.getKind() == Kind::VARIABLE || node.getKind() == Kind::SKOLEM);
}

// Function to perform integer Gaussian elimination and return the rank of the matrix
// Function to perform Gaussian elimination and return the rank

    
    // Forward Elimination process
 int gaussianEliminationRank(std::vector<std::vector<Rational>>& matrix, int rows, int cols) {
    int rank = 0;

    for (int col = 0; col < cols; ++col) {
        // Find the first row with a non-zero entry in the current column
        int pivotRow = -1;
        for (int r = rank; r < rows; ++r) {
            if (matrix[r][col].abs() > 0) { // Use std::abs for absolute value
                pivotRow = r;
                break;
            }
        }

        // If no pivot is found, continue to the next column
        if (pivotRow == -1) {
            continue;
        }

        // Move the pivot row to the current rank position
        if (pivotRow != rank) {
            for (int c = 0; c < cols; ++c) {
                Rational temp = matrix[rank][c];
                matrix[rank][c] = matrix[pivotRow][c];
                matrix[pivotRow][c] = temp;
            }
        }

        // Normalize the pivot row
        Rational pivotValue = matrix[rank][col];
        for (int c = col; c < cols; ++c) {
            matrix[rank][c] /= pivotValue;
        }

        // Eliminate the current column in all other rows
        for (int r = 0; r < rows; ++r) {
            if (r != rank && matrix[r][col].abs() > 0) {
                Rational factor = matrix[r][col];
                for (int c = col; c < cols; ++c) {
                    matrix[r][c] -= factor * matrix[rank][c];
                }
            }
        }

        ++rank;  // Increase rank after processing this column
    }

    return rank;
}

// Function to check if adding a new vector keeps the set linearly independent
bool isLinearlyIndependent(const std::vector<std::vector<Rational>>& matrix, const std::vector<Rational>& newVec, int rows, int cols, int rank) {
    // Create a temporary matrix to test linear independence
    std::vector<std::vector<Rational>> tempMatrix = matrix;
    tempMatrix.push_back(newVec);
    return gaussianEliminationRank(tempMatrix, rows + 1, cols) > rank;
}

// Main function to find a full linearly independent basis
std::vector<std::vector<Rational>> findBasis(const std::vector<std::vector<Rational>>& inputVectors) {
    int n = inputVectors.size();
    int d = inputVectors[0].size();  // Dimension of the vectors
    AlwaysAssert(n <= d);  // Ensure input doesn't exceed the number of dimensions

    // Copy input vectors to the matrix
    std::vector<std::vector<Rational>> matrix = inputVectors;

    // Perform Gaussian elimination to determine the current rank
    int rank = gaussianEliminationRank(matrix, n, d);

    // Add standard basis vectors to complete the matrix if needed
    for (int i = 0; i < d; ++i) {
        std::vector<Rational> e_i(d, Rational(0));
        e_i[i] = Rational(1);  // Create a standard basis vector

        // Check if adding this vector maintains linear independence
        if (isLinearlyIndependent(matrix, e_i, n, d, rank)) {
            ++rank;
            matrix.push_back(e_i);  // Add to matrix
            ++n;
        }

        if (rank == d) {
            break;  // Stop if a full basis is found
        }
    }

    return matrix;
}


std::vector<int> parseGlpkOutput(const std::string& output) {
    std::map<int, int> sortedVariableMap;  // Map to store variables in order of gb_x index
     std::vector<int> variableMap;
    if (output.size()==0) {
        //std::cout << "No feasible solution found." << std::endl;
        return variableMap;
    }
    if (output.find("INTEGER OPTIMAL") == std::string::npos) {
        //std::cout << "No feasible solution found." << std::endl;
        return variableMap;
    }


    // Updated regex to capture all "gb_x" variables, with or without the "*"
    std::regex variableRegex(R"(\s*\d+\s+(gb_(\d+))\s*(\*?)\s+(-?\d+\.?\d*))");
    std::smatch match;

    // Use regex to find all "gb_x" variables and their values from the Activity column
    std::string::const_iterator searchStart(output.cbegin());
    while (std::regex_search(searchStart, output.cend(), match, variableRegex)) {
        int index = std::stoi(match[2]);   // Extract the numerical part (e.g., "0" in "gb_0")
        int value = std::stoi(match[4]);   // Extract the variable value from the Activity column
        sortedVariableMap[index] = value;  // Store the value with its index in the map

        // Move the search start to the next position
        searchStart = match.suffix().first;
    }

    // Extract the values from the map, which will be sorted by the gb_x index
    for (const auto& pair : sortedVariableMap) {
        variableMap.push_back(pair.second);  // Add the values in sorted order
    }
    //\n";
    return variableMap;
}

std::vector<int> parseGurobiOutput(const std::string& output) {
    // Check if the model is infeasible
    std::vector<int> variableMap;
    // std::cout << "SIZE:" << output.size() << "\n";
    // if (output.size()==0) {
    //     std::cout << "No feasible solution found." << std::endl;
    //     return variableMap;
    // }

    // Check if the model is optimal
    if (output.find("Objective value") != std::string::npos) {
        std::size_t start = output.find("\n", 0) + 1;
        // Find the section where the optimal solution is printed
        //std::size_t start = output.find("Optimal solution:");
        if (start == std::string::npos) {
            std::cout << "No variable values found." << std::endl;
            return variableMap;
        }

        // Extract the part of the string that contains the variable values
        std::string variableSection = output.substr(start);

        // Refined regex: match variable names (e.g., alphanumeric names) and their values
        std::regex variableRegex(R"((gb_(\d+))\s+(-?\d+))");
        std::smatch match;

        // Map to store variable values with the numeric part as key (to sort later)
        std::map<int, int> sortedVariableMap;

        // Use regex to find "gb" variables and their values
        std::string::const_iterator searchStart(variableSection.cbegin());
        while (std::regex_search(searchStart, variableSection.cend(), match, variableRegex)) {
            int index = std::stoi(match[2]);  // Extract the numeric part (e.g., "0" in "gb_0")
            int value = std::stoi(match[3]);  // Extract the value
            sortedVariableMap[index] = value; // Store the value using the index as key

            // Move the search start to the next position
            searchStart = match.suffix().first;
        }

        // Now that we have all variables in sorted order by index (gb_0, gb_1, ...)
        for (const auto& pair : sortedVariableMap) {
            variableMap.push_back(pair.second); // Push the values in sorted order
        }

        return variableMap;
    }
    return variableMap;
}

std::string stringify(std::map<std::string, Integer> elements, std::string op) {
    std::string result = ""; 
    for (auto& pair : elements) {
        std::string i = pair.second.toString() + " " + pair.first;
        //std::cout << i << "\n";
        // Check if the operator is "-" and the first character of the element is "-"
        if (i[0] == '-') {
            result += " " + i;  // Use "+" instead of "-"
        } else {
            result += " " + op + " " + i;  // Regular operation
        }
    }
    //std::cout << "finished stringify\n";
    return result;
}


std::string stringify_gurobi(std::vector<std::string> elements, std::string op){
    std::string result =""; 
    for (auto i: elements){
        if (op == "+" && i[0] == '-') {
            result += " " + i;  // Use "+" instead of "-"
        } else if (op == "-" && i[0] == '-'){
            result += " + " + i.substr(1);;
        }
        else {
            result += " " + op + " " + i;  // Regular operation
        }
    }
    // std::cout << op << "\n";
    // std::cout << result << "\n";
    return result;
}

std::vector<Rational> getLastRow(Node eq, std::map<std::string, std::vector<Rational>> monomials){
    int current_len;
    for (auto pair: monomials){
        //std::cout << pair.first << ":";
        // for (auto i: pair.second){
        //     std::cout << i << ",";
        // }
        // std::cout << "\n";
    }
    current_len = (monomials.begin()->second).size();
        //std::cout << "RESULTING EQUATION:" << eq << "\n";
        for (int h = 0; h<=eq.getNumChildren(); h++) {
            if (h == eq.getNumChildren() && h!=0){
                      continue;
                  }
            Node node;
            if (eq.getNumChildren() == 0){
                      node = eq;
                  } else {
                      node = eq[h];
                  }
            // std::cout << node << "\n";
            // std::cout << node << "\n";
            if (node.getKind() == Kind::CONST_INTEGER){
                monomials["constant"].push_back(node.getConst<Rational>());
            }
            else if (isVariableOrSkolem(node) ){
                monomials[node.getName()].push_back(1); 
            }
            else if (node.getKind() == Kind::MULT || node.getKind() == Kind::NONLINEAR_MULT){ 
                if (node.getNumChildren() == 2 && node[0].getKind() == Kind::CONST_INTEGER) {
                    monomials[node[1].getName()].push_back(node[0].getConst<Rational>()); 
                    continue;
                };
                int k = 0;
                Rational constInt = 1;
                if (node[0].getKind() == Kind::CONST_INTEGER){
                    k = 1;
                    constInt = node[0].getConst<Rational>();
                }
                std::string name = "";
                for (int j = k; j < node.getNumChildren(); j ++){
                    name += node[j].getName() + "_";
                }
                monomials[name].push_back(constInt); 
            }
            else {
                AlwaysAssert(false) << node << "\n";
            }
        }
        for (auto pair: monomials){
        //std::cout << pair.first << ":";
        // for (auto i: pair.second){
        //     std::cout << i << ",";
        // }
        // std::cout << "\n";
    }
        for (auto &pair: monomials){
            if (pair.second.size() == current_len +1){
                continue;
            } else if (pair.second.size() == current_len) {
                pair.second.push_back(0);
            }  else {
                AlwaysAssert(false) << "matrix construction messed up" << pair.first << ":" << pair.second.size() << "," << current_len << "\n";
            }
        }
    // for (auto pair: monomials){
    //     std::cout << pair.first << ":";
    //     std::cout << pair.second[0];
        
    //     std::cout << "\n";
    // }
    std::vector<Rational> temp;
    //std::cout << "NEW VECTOR:";
    for (auto pair:  monomials){
        temp.push_back(pair.second[current_len]);
        //std::cout << pair.second[current_len] << ",";
    }
    //std::cout << "\n";
    return temp;

}

std::map<std::string, std::vector<Rational>> Field::collectMonomials(IntegerField z, Field f, NodeManager* nm){
    // We need to only consider monomials that are in R^=
    std::map<std::string, std::vector<Rational>> monomials;
    std::vector<Node> procEqual;
    std::vector<Node> zEqual;
    std::vector<Node> allowedZ;
    for (auto i: f.equalities){
            procEqual.push_back(rewrite(nm->mkNode(
                Kind::ADD, i[0], rewrite(nm->mkNode( Kind::MULT, i[1], 
                nm->mkConstInt(-1))))));
    }
    for (auto i: z.equalities){
            zEqual.push_back(rewrite(nm->mkNode(
                Kind::ADD, i[0], rewrite(nm->mkNode( Kind::MULT, i[1], 
                nm->mkConstInt(-1))))));
    }
    // pass one initialize allowed monomials  
    for (int i = 0; i< procEqual.size(); i++){
        Node eq = procEqual[i];
    
        for (int h = 0; h<=eq.getNumChildren(); h++) {
            if (h == eq.getNumChildren() && h!=0){
                      continue;
                  }
            Node node;
            if (eq.getNumChildren() == 0){
                      node = eq;
                  } else {
                      node = eq[h];
                  }
            //std::cout << node << "\n";
            if (node.getKind() == Kind::CONST_INTEGER){
                monomials["constant"] = std::vector<Rational>();
            }
            else if (isVariableOrSkolem(node)){
                monomials[node.getName()] = std::vector<Rational>(); 
            }
             else if (node.getKind() == Kind::MULT || node.getKind() == Kind::NONLINEAR_MULT){
                //std::cout << "We are here?\n";
                if (node[0].getKind() == Kind::CONST_INTEGER && isVariableOrSkolem(node[1]) && node.getNumChildren() == 2){
                    monomials[node[1].getName()] = std::vector<Rational>(); 
                    continue;
                }
                if (node[1].getKind() == Kind::NONLINEAR_MULT){
                    //std::cout << "We should be here?\n";
                    std::string name ="";
                    for (int j = 0; j < node[1].getNumChildren(); j ++){
                        name += node[1][j].getName() + "_";
                    }
                    //std::cout << name << "\n";
                    monomials[name] = std::vector<Rational>(); 
                } else {
                    AlwaysAssert(false) << node << "\n";
                } 
            }
            else {
                AlwaysAssert(false) << node << "\n";
            }
        }
    }

    bool broken;
    for (int i = 0 ; i< zEqual.size(); i++){
        broken = false;
        Node eq = zEqual[i];
        for (int h = 0; h<=eq.getNumChildren(); h++) {
            if (h == eq.getNumChildren() && h!=0){
                      continue;
                  }
            Node node;
            if (eq.getNumChildren() == 0){
                      node = eq;
                  } else {
                      node = eq[h];
                  }
            //std::cout << node << "\n";
            if (node.getKind() == Kind::CONST_INTEGER){
                if (monomials.find("constant") != monomials.end()){
                        broken = true;
                        break;
                    } 
                    continue;
            }
            else if ( isVariableOrSkolem(node)){
                if (monomials.find(node.getName()) != monomials.end()){
                    broken = true;
                    break;
                }
            }
            else if (node.getKind() == Kind::MULT || node.getKind() == Kind::NONLINEAR_MULT){ 
                if (node.getNumChildren() == 2 && node[0].getKind() == Kind::CONST_INTEGER) {
                    if (monomials.find(node[1].getName()) != monomials.end()){
                        broken = true;
                        break;
                    } 
                    continue;
                };
                int k = 0;
                if (node[0].getKind() == Kind::CONST_INTEGER){
                    k = 1;
                }
                std::string name = "";
                for (int j = k; j < node.getNumChildren(); j ++){
                    name += node[j].getName() + "_";
                }
                if (monomials.find(name) != monomials.end()){
                    broken = true;
                    break;
                }
            }
            else {
                AlwaysAssert(false) << node << "\n";
            }
        }
        if (!broken){
            allowedZ.push_back(zEqual[i]);
        }
    }
    int current_len;
    for (auto i: allowedZ){
        current_len = (monomials.begin()->second).size();
        Node eq = i;
       for (int h = 0; h<=eq.getNumChildren(); h++) {
            if (h == eq.getNumChildren() && h!=0){
                      continue;
                  }
            Node node;
            if (eq.getNumChildren() == 0){
                      node = eq;
                  } else {
                      node = eq[h];
                  }
            //std::cout << node << "\n";
            if (node.getKind() == Kind::CONST_INTEGER){
                monomials["constant"].push_back(node.getConst<Rational>());
            }
            else if (isVariableOrSkolem(node) ){
                monomials[node.getName()].push_back(1); 
            }
            else if (node.getKind() == Kind::MULT || node.getKind() == Kind::NONLINEAR_MULT){ 
                if (node.getNumChildren() == 2 && node[0].getKind() == Kind::CONST_INTEGER) {
                    monomials[node[1].getName()].push_back(node[0].getConst<Rational>()); 
                    continue;
                };
                int k = 0;
                Rational constInt = 1;
                if (node[0].getKind() == Kind::CONST_INTEGER){
                    k = 1;
                    constInt = node[0].getConst<Rational>();
                }
                std::string name = "";
                for (int j = k; j < node.getNumChildren(); j ++){
                    name += node[j].getName() + "_";
                }
                monomials[name].push_back(constInt); 
            }
            else {
                AlwaysAssert(false) << node << "\n";
            }
        }
        for (auto &pair: monomials){
            if (pair.second.size() == current_len +1){
                continue;
            } else if (pair.second.size() == current_len) {
                pair.second.push_back(Rational(0));
            }  else {
                AlwaysAssert(false) << "matrix construction messed up\n";
            }
    }
    }
    // for (auto &pair: monomials){
    //     std::cout << pair.first << "\n";
    // }
    return monomials;
    
}

std::vector<std::vector<double>> convertToDoubleMatrix(const std::vector<std::vector<int>>& intMatrix) {
    std::vector<std::vector<double>> doubleMatrix(intMatrix.size(), std::vector<double>(intMatrix[0].size()));

    for (size_t i = 0; i < intMatrix.size(); ++i) {
        for (size_t j = 0; j < intMatrix[i].size(); ++j) {
            doubleMatrix[i][j] = static_cast<double>(intMatrix[i][j]);
        }
    }

    return doubleMatrix;
}

Rational logify(Rational i){
    return i;
    if (i.abs() <= 2){
        return i;
    } else {
        int addConst = std::round(log2(i.getNumerator().abs().getDouble()));
        if (i<0){
            addConst *= -1;
        }
        return Integer(addConst);
    }                                                 
}




void write_gurobi_query_new(const std::string& filename, std::vector<Node> equalities,
                        std::map<std::string, 
                        std::pair<Integer, Integer>>& bounds,
                        NodeManager* nm,
                        Integer modulos,
                        std::vector<std::vector<Rational>> pastSolutions,
                        std::vector<std::string> monomials,
                        int iteration) {
    std::map<std::string, std::vector<Node>> nonlinearMap;
    std::map<std::string, std::vector<std::string>> varCoefMap;
    std::vector<std::string> new_vars;
    std::map<std::string, std::pair<Integer, Integer>> nonlinearBounds;
    Integer addConst = Integer(0);
    std::vector<std::string> officialConst;
    std::ofstream file(filename);
    if (!file.is_open()) {
        std::cerr << "Error: Could not open the file for writing." << std::endl;
        AlwaysAssert(false);
        return;
    }  
    for (auto i:monomials){
        varCoefMap[i] =  std::vector<std::string>();

    }
    //std::cout << "Writing to file: " << filename << std::endl;  // Debug print
    
    // file << "#include \"/Library/gurobi1103/macos_universal2/include/gurobi_c++.h\"\n"
    //      << "#include <iostream>\n"
    //      << "int main() {\n"I 
    //      << "    GRBEnv env = GRBEnv();\n"
    //      << "    env.start();\n"
    //      << "    GRBModel model = GRBModel(&env);\n";
    for(int j = 0; j<equalities.size(); j++){
        new_vars.push_back("gb_"+ std::to_string(j));
    // Currently operating under the fact that the all the terms are of the form
    // + (*..) no pluses inside multiplication if this is not true need to through an 
    // error :) 
        //std::cout << "MAIN EQUALITY: " << equalities[j] << "\n";
        Node eq = equalities[j];
        for (int h = 0; h<=eq.getNumChildren(); h++) {
            if (h == eq.getNumChildren() && h!=0){
                      continue;
                  }
            Node node;
            if (eq.getNumChildren() == 0){
                      node = eq;
                  } else {
                      node = eq[h];
                  }
            // x = z this should become x + (-1) z = 0;
            // issue what about x = 0 this becomes just x...
            //  for (int k = 0; k<=eq.getNumChildren(); k++) {
            //     if (k == eq.getNumChildren() && k!=0){
            //          continue;
            //      }
            //     // Node node;
            //     if (eq.getNumChildren() == 0){
            //          node = eq;
            //      } else {
            //          node = eq[k];
            //      }
            //std::cout << "tiny equalities: " << node << "\n";
            if (node.getKind() == Kind::CONST_INTEGER){
                Integer temp = node.getConst<Rational>().getNumerator();
                // if (temp <= 2){
                //      addConst = static_cast<int>(temp.getSignedInt());
                // } else {
                //      addConst = static_cast<int>(std::round(log2(temp.getSignedInt())));
                //     if (node.getConst<Rational>().getNumerator() <0){
                //         addConst *= -1;
                //     }
                // }
                //std::cout << "WHY IS THIS ZERO" << temp << "\n";
                varCoefMap["constant"].push_back(temp.toString() + "  " + new_vars[j]);
                //std::cout <<  equalities[j] << "\n";
                //std::cout << officialConst << "\n";
                //AlwaysAssert(false);
                //varCoefMap["const"].push_back(addConst);
                //varCoefMap[node.getName()].push_back(new_vars[j]);
                
            }
            else if (isVariableOrSkolem(node)){
                if (varCoefMap.find(node.getName()) == varCoefMap.end()){
                    AlwaysAssert(false) << node << "\n";
                    varCoefMap[node.getName()].push_back(new_vars[j]);
                } else {
                    varCoefMap[node.getName()].push_back(new_vars[j]);
                }
            }
            else if (node.getKind() == Kind::MULT || node.getKind() == Kind::NONLINEAR_MULT){
                if (node.getNumChildren() == 2 && node[0].getKind() == Kind::CONST_INTEGER) {
                    //if (node[0].getConst<Rational>().getNumerator().abs() <= 2){
                        addConst = node[0].getConst<Rational>().getNumerator();
                    //      std::cout << "ADDing" << addConst << "\n";
                    //  } else {
                    //      addConst = static_cast<int>(std::round(log2(node[0].getConst<Rational>().getNumerator().abs().getDouble())));
                    //      if (node[0].getConst<Rational>().getNumerator() <0){
                    //          addConst *= -1;
                    //      }
                    //      std::cout << "ADDing" << addConst << "\n";
                    //  }
                    if (node[1].getKind() == Kind::NONLINEAR_MULT){
                        // case when we have multiplication of variables so need to make new variable
                        std::string name = "";
                        std::vector<Node> myNodes; 
                        Integer LB = 1;
                        Integer UB = 1;
                        for (int i = 0; i<node[1].getNumChildren(); i++) {
                            AlwaysAssert(isVariableOrSkolem(node[1][i])) << node[i];
                            name += node[1][i].getName() + "_";
                            myNodes.push_back(node[1][i]);
                            Integer pos1 = LB * bounds[node[1][i].getName()].second;
                            Integer pos2 = UB * bounds[node[1][i].getName()].second;
                            Integer pos3 = LB * bounds[node[1][i].getName()].first;
                            Integer pos4 = LB * bounds[node[1][i].getName()].second;
                            LB = Integer::min(Integer::min(pos1,pos2), Integer::min(pos3,pos4));
                            UB = Integer::max(Integer::max(pos1,pos2), Integer::max(pos3,pos4));
                        }
                        if (varCoefMap.find(name) == varCoefMap.end()){
                            AlwaysAssert(false) << node << "NAME:" << name << "\n";
                            varCoefMap[name].push_back(addConst.toString() + "  " + new_vars[j]);
                        } else {
                            varCoefMap[name].push_back(addConst.toString() + "  " + new_vars[j]);
                        }
                        nonlinearMap[name] = myNodes;
                        nonlinearBounds[name] = std::make_pair(LB, UB);
                        // we need to get the resulting lower and upper bounds,
                    } else { AlwaysAssert(isVariableOrSkolem(node[1])  ) << node[1] << "\n";
                    if (varCoefMap.find(node[1].getName()) == varCoefMap.end()){
                        AlwaysAssert(false) << node << "\n";
                        varCoefMap[node[1].getName()].push_back(addConst.toString() + "  " + new_vars[j]);
                    } else {
                         varCoefMap[node[1].getName()].push_back(addConst.toString() + "  " + new_vars[j]);
                    }
                    }
                } else {
                    addConst = Integer(1);
                    std::string name = "";
                    std::vector<Node> myNodes; 
                    Integer UB = 1;
                    Integer LB = 1;
                    for (int i = 0; i<node.getNumChildren(); i++) {
                        if (i == 0 && node[i].getKind()== Kind::CONST_INTEGER){ 
                        //    if (node[i].getConst<Rational>().getNumerator().abs() <= 2){
                                    addConst = node[i].getConst<Rational>().getNumerator();
                        //             std::cout << "ADDing" << addConst << "\n";
                        //  } else {
                        //         addConst = static_cast<int>(std::round(log2(node[i].getConst<Rational>().getNumerator().abs().getDouble())));
                        //         if (node.getConst<Rational>().getNumerator() <0){
                        //             addConst *= -1;
                        //         }
                        //         std::cout << "ADDing" << addConst << "\n";
                        //         }
                        //     if (addConst > 2000000000 || addConst < -2000000){
                        //         AlwaysAssert(false);
                        //     }
                            continue;
                        }
                        AlwaysAssert(isVariableOrSkolem(node[i]));
                        name += node[i].getName() + "_";
                        myNodes.push_back(node[i]);
                        Integer pos1 = LB * bounds[node[i].getName()].second;
                        Integer pos2 = UB * bounds[node[i].getName()].second;
                        Integer pos3 = LB * bounds[node[i].getName()].first;
                        Integer pos4 = LB * bounds[node[i].getName()].second;
                        LB = Integer::min(Integer::min(pos1,pos2), Integer::min(pos3,pos4));
                        UB = Integer::max(Integer::max(pos1,pos2), Integer::max(pos3,pos4));
                    }
                    // if (addConst > 2000000000 || addConst < -2000000){
                    //     AlwaysAssert(false);
                    // }
                     if (varCoefMap.find(name) == varCoefMap.end()){
                        AlwaysAssert(false) << node << "\n";
                         //varCoefMap[name].push_back(addConst.toString() + "  " + new_vars[j]);
                    } else {
                        AlwaysAssert(false) << node << "\n";
                        varCoefMap[name].push_back(addConst.toString() + "  " + new_vars[j]);
                    }
                    nonlinearMap[name] = myNodes;
                    nonlinearBounds[name] = std::make_pair(LB, UB);
                }

            } else {
                AlwaysAssert(false) << node.getKind();
            }
        //}
        }
    }
    nonlinearBounds["constant"] = std::make_pair(1,1);
    file << "Maximize" << std::endl;
    file << "obj: ";
    for (size_t i = 0; i < new_vars.size() - 1; ++i) {
        file << new_vars[i] << " + ";
    }
    file << new_vars[new_vars.size()-1];
    file << std::endl;
    file << std::endl;
    file << "Subject To\n";
    // Okay now we have our data structures its time to write stuff :) 
    // First write in all the variables we made.
    
    // for (const auto& var : new_vars) {
    //     file << "    GRBVar " << var << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << var << "\");" << std::endl;
    // }
    std::map<std::string, std::string> pos_relu_vars;
    std::map<std::string, std::string> neg_relu_vars;
    std::map<std::string, std::string> neg_coefficients;
    std::map<std::string, std::string> pos_coefficients;
    std::vector<std::string> binaries;
    std::string upper_bound ="";
    std::string lower_bound ="";
    for (auto&  pair: varCoefMap) {
        pos_relu_vars[pair.first] = pair.first + "coef_pos_relu";
        neg_relu_vars[pair.first] = pair.first + "coef_neg_relu";
        neg_coefficients[pair.first] = pair.first + "neg_coef";
        pos_coefficients[pair.first] = pair.first + "pos_coef";
        Integer UB; 
        Integer LB;
        auto it = bounds.find(pair.first);
        if (it != bounds.end()) {
            // std::cout << it->first << "\n";
            // std::cout << (it->second.second).toString() << "\n";
            // if ((it->second.first).abs() <= 2) {
                LB = it->second.first;
            // } else {
            // LB = static_cast<int>(std::round(log2((it->second.first).getDouble())));
            // }
            // std::cout << it->second.first<< "turned into" <<  LB << "\n";
            // if ( (it->second.second).abs() <= 2) {
                UB = it->second.second;
            // } else {
            // UB = static_cast<int>(std::round(log2((it->second.second).getDouble())));
            // }
            //std::cout << it->second.second<< "turned into" <<  UB << "\n";
        } else {
            it = nonlinearBounds.find(pair.first);
            if (it != bounds.end()) {
            // std::cout << it->first << "\n";
            // std::cout << (it->second.second).toString() << "\n";
            // if ((it->second.first).abs() <= 2) {
                LB = it->second.first;
            // } else {
            // LB = static_cast<int>(std::round(log2((it->second.first).getDouble())));
            // }
            // std::cout << it->second.first<< "turned into" <<  LB << "\n";
            // if ((it->second.second).abs() <= 2) {
                UB = it->second.second;
            // } else {
            // UB = static_cast<int>(std::round(log2((it->second.second).getDouble())));
            // }
            // std::cout << it->second.second<< "turned into" <<  UB << "\n";
             } else {
                 AlwaysAssert(false) << pair.first;
           
           }
        }
        //std::cout << UB.toString() << "\n";
        if (upper_bound.size() == 0){
            upper_bound = UB.toString() + "  " + pos_relu_vars[pair.first] + " - " + LB.toString() + "  " + neg_relu_vars[pair.first];
        } else {
            upper_bound += " + " + UB.toString() + "  " + pos_relu_vars[pair.first] + " - " + LB.toString() + "  " + neg_relu_vars[pair.first];
        }
        if (lower_bound.size() == 0){
            lower_bound = LB.toString() + "  " + pos_relu_vars[pair.first] + " - " + UB.toString() + "  " + neg_relu_vars[pair.first];
        } else {
            lower_bound += " + " + LB.toString() + "  " + pos_relu_vars[pair.first] + " - " + UB.toString() + "  " + neg_relu_vars[pair.first];
        }

        // Integer maxPos = Integer(static_cast<int>(std::round(log2(modulos.getDouble() -1))));
        Integer maxPos = modulos - 1;
        /// WE THINK EVERYTHING AFTER HERE IS WRONG :( 
        //file << "    GRBVar " << neg_coefficients[pair.first] << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << neg_coefficients[pair.first] << "\");" << std::endl;
        //file << "    GRBVar " << pos_coefficients[pair.first] << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << pos_coefficients[pair.first] << "\");" << std::endl;
        //file << "    GRBVar " << pos_relu_vars[pair.first] << " = model.addVar(0, GRB_INFINITY, 0.0, 'I', \"" << pos_relu_vars[pair.first] << "\");" << std::endl;
        //file << "    GRBVar " << neg_relu_vars[pair.first] << " = model.addVar(0, GRB_INFINITY, 0.0, 'I', \"" << neg_relu_vars[pair.first]  << "\");" << std::endl;
        file << pos_coefficients[pair.first] << ": " << pos_coefficients[pair.first] << stringify_gurobi(pair.second, "-") << " = 0" << "\n";
        binaries.push_back(pair.first + "pos_binary");
        file << "geq1_" << pos_coefficients[pair.first] << ": " <<  pos_relu_vars[pair.first]  << " - "  << pos_coefficients[pair.first] << " >= " << "0" << "\n";
        file << "geq2_" << pos_coefficients[pair.first] << ": " <<  pos_relu_vars[pair.first] << " >= " << "0" << "\n";
        file << "leq1_" << pos_coefficients[pair.first] << ": " <<  pos_relu_vars[pair.first] << " - " << pos_coefficients[pair.first] <<  " + "  << maxPos << " " << binaries[binaries.size()-1] <<  " <= " << maxPos << "\n";
        file << "leq2_" << pos_coefficients[pair.first] << ": " <<  pos_relu_vars[pair.first]  <<  " - "  << maxPos << " " << binaries[binaries.size()-1] << " <= 0" << "\n";
       

        //file << pos_relu_vars[pair.first] << ": " << pos_relu_vars[pair.first] << " MAX (" << pos_coefficients[pair.first] << " , 0 )" << "\n";
        file << neg_coefficients[pair.first] << ": "  << neg_coefficients[pair.first] << stringify_gurobi(pair.second, "+") << " = 0" << "\n";
        binaries.push_back(pair.first + "neg_binary");
        file << "geq1_" << neg_coefficients[pair.first] << ": " <<  neg_relu_vars[pair.first]  << " - "  << neg_coefficients[pair.first] << " >= " << "0" << "\n";
        file << "geq2_" << neg_coefficients[pair.first] << ": " <<  neg_relu_vars[pair.first] << " >= " << "0" << "\n";
        file << "leq1_" << neg_coefficients[pair.first] << ": " <<  neg_relu_vars[pair.first] << " - " << neg_coefficients[pair.first] << " + "  << maxPos << " " << binaries[binaries.size()-1] <<  " <= " << maxPos << "\n";
        file << "leq2_" << neg_coefficients[pair.first] << ": " <<  neg_relu_vars[pair.first]  <<  " - "  << maxPos << " " << binaries[binaries.size()-1] << " <= 0" << "\n";
        //file << neg_relu_vars[pair.first] << ": " << neg_relu_vars[pair.first] << " MAX (" << neg_coefficients[pair.first] << " , 0 )" << "\n";
    
    }
    //std::cout << "upper : "  << upper_bound << " <= " <<  static_cast<int>(std::round(log2(modulos.getDouble() -1)))   << std::endl;
    //  file << "upper : "  << upper_bound << " <= " <<  static_cast<int>(std::round(log2(modulos.getDouble() -1)))   << std::endl;
    //  file << "lower : " <<  lower_bound <<  " >= " <<  "-  " <<  static_cast<int>(std::round(log2(modulos.getDouble() -1)))  << std::endl;
    file << "upper : "  << upper_bound << " <= " <<  (modulos-1).toString()   << std::endl;
    file << "lower : " <<  lower_bound <<  " >= " <<  "-  " << (modulos -1).toString()  << std::endl;
    std::string nonzero="";
    for (auto&  pair: varCoefMap) {
        if (nonzero.size()==0){
            nonzero = neg_relu_vars[pair.first] + " + " + pos_relu_vars[pair.first];
        } else {
            nonzero += " + " + neg_relu_vars[pair.first] + " + " + pos_relu_vars[pair.first];
        }
    }

    file << "nonzero : " << nonzero << " >= 1" << std::endl;
    std::vector<std::string> c_old;
    std::vector<std::string> c_orth;
    if (pastSolutions.size()>0){
        std::vector<std::vector<Rational>> curBasis = findBasis(pastSolutions);
        //printBasis(curBasis);
        AlwaysAssert(curBasis.size() == curBasis[0].size()) << curBasis.size() << " but " << curBasis[0].size();
        for (int i =0; i<curBasis.size(); i++){
            Integer LCM = Integer(1);
            for (int j =0; j<curBasis[0].size(); j++) {
                
                if (curBasis[i][j]!= Rational(0)){
                    // std::cout << "NUM" << curBasis[i][j].getNumerator() << "\n";
                    // std::cout << "DENOM:" << curBasis[i][j].getDenominator() << "\n";
                    curBasis[i][j] = logify(curBasis[i][j].getNumerator())/logify(curBasis[i][j].getDenominator());
                    if (curBasis[i][j].getDenominator()!=Integer(1)){
                        LCM = LCM.lcm(curBasis[i][j].getDenominator());
                    }
                }
                }
                if (LCM!=1){
                    //std::cout << "triggered\n";
                    for (int j =0; j<curBasis[0].size(); j++) {
                        curBasis[i][j] = Rational(LCM) * curBasis[i][j];
                }
            }
        }
        //printBasis(curBasis);
        AlwaysAssert(curBasis.size() == curBasis[0].size()) << curBasis.size() << " but " << curBasis[0].size();
        int n = pastSolutions.size();
        std::vector<std::string> constraints;
        for(int i = 0;i <curBasis.size(); i++){
            constraints.push_back("");
            if (i < n){
                c_old.push_back("c_old" + std::to_string(i));
                //file << "    GRBVar " << c_old.back() << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << c_old.back() << "\");" << std::endl;

            } else {
                c_orth.push_back("c_orth" + std::to_string(i));
                 //file << "    GRBVar " << c_orth.back() << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << c_orth.back() << "\");" << std::endl;
            }

        }
        for(int i = 0;i <curBasis.size(); i++){
            for(int j=0; j<curBasis[i].size(); j ++){
                // c determined by i 
                std::string cur_c;
                // constraint determined by j 
                if (i < n){
                    cur_c = c_old[i];
                } else {
                    cur_c = c_orth[i-n];
                }
            if (constraints[j].size() == 0){
                constraints[j] = curBasis[i][j].toString() + " " +  cur_c;
            } else {
                 constraints[j] += " + " + curBasis[i][j].toString() + " " +  cur_c;

            }
            }
        }
        for(int i = 0; i<constraints.size(); i++){
            file << "const_" << i << " : " <<  constraints[i] << stringify_gurobi(varCoefMap[monomials[i]], "-") << " = 0" <<  std::endl;
        }
        // Instead we need to split case on which c_orth is non zero and also do greater than and less than 
        // I should ask Alex if we actually need 
        if (iteration % 2 == 0){
            file <<  "nonzero_c: " + c_orth[std::floor(iteration/2)] + " >= 1"<<  std::endl;
        } else {
            file <<  "nonzero_c: " + c_orth[std::floor(iteration/2)] + " <= -1"<<  std::endl;
        }
        // std::string nonzero_c = "";
        // for(int i=0; i<c_orth.size(); i++){
        //     if (nonzero_c == ""){
        //         nonzero_c = c_orth[i];
        //     } else {
        //         nonzero_c += " + " + c_orth[i];
        //     }
        // }
        // file <<  "nonzero_c : " + nonzero_c + " >= 1" << std::endl;


    }
    file << std::endl;
    file << "Bounds" << std::endl;
    // // now we have to define the bounds 
    for (auto i: c_orth){
        file << i << " free" << std::endl;
    }
    for (auto i: c_old){
        file << i << " free" << std::endl;
    }
    for (const auto& var : new_vars) {
        file << var <<  " free" << std::endl;
    }
    for (const auto&  pair: varCoefMap) {
        file << pos_relu_vars[pair.first] <<  " free" << std::endl;
        file << neg_relu_vars[pair.first] <<  " free" << std::endl;;
        file << neg_coefficients[pair.first] << " free" <<  std::endl; 
        file <<  pos_coefficients[pair.first] << " free" <<  std::endl;
    }

    // // now we have to define that all our variables are general
    // file << std::endl;
    file << "General" << std::endl;
    for (auto i: c_orth){
        file << i << std::endl;
    }
    for (auto i: c_old){
        file << i << std::endl;
    }
    for (const auto& var : new_vars) {
        file << var <<  std::endl;
    }
    for (const auto&  pair: varCoefMap) {
        //std::cout << "HUH??:" << pair.first << "\n";
        file << pos_relu_vars[pair.first] << std::endl;
        file << neg_relu_vars[pair.first] << std::endl;;
        file << neg_coefficients[pair.first] << std::endl; 
        file << pos_coefficients[pair.first] << std::endl;
    }

    file << std::endl;
    file << "Binaries" << std::endl;
    for (auto i: binaries){
        file << i << std::endl;
    }
    //std::cout << "We actually got here \n";

    // file << "    model.optimize();" << std::endl;
    // file << "    std::cout << \"Optimal solution:\" << std::endl;" << std::endl;
    // for (const auto&  var: new_vars) {
    //     file  << "    std::cout << \"" << var << ": \" << " << var << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
    // }
    // //  for (const auto&  var: pos_coefficients) {
    // //     file  << "    std::cout << \"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
    // // }
    // //  for (const auto&  var: neg_coefficients) {
    // //     file  << "    std::cout << \"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
    // // }
    // //  for (const auto&  var: pos_relu_vars) {
    // //     file  << "    std::cout << \"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
    // // }
    // //  for (const auto&  var: neg_relu_vars) {
    // //     file  << "    std::cout << \1"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
    // // }
    // file << "    };" << std::endl;
    
    //AlwaysAssert(false);

    // std::cout << "Sanity Check\n";
    // std::cout << "Number of OG Variables:" << varCoefMap.size() << "\n";
    // std::cout << "Number of New Variables:" << new_vars.size() << "\n";
    std::string hellp = readFileToString(filename);
    // std::cout << hellp << "\n";
    
    
   file.flush(); 
   file.close();

};




//  void write_glpk_query(const std::string& filename, std::vector<Node> equalities,
//                         std::map<std::string, 
//                         std::pair<Integer, Integer>>& bounds,
//                         NodeManager* nm,
//                         Integer modulos,
//                         std::vector<std::vector<int>> pastSolutions) {
//     std::map<std::string, std::vector<Node>> nonlinearMap;
//     std::map<std::string, std::map<std::string, Integer>> varCoefMap;
//     std::vector<std::string> new_vars;
//     std::map<std::string, std::pair<Integer, Integer>> nonlinearBounds;
//     Integer addConst = Integer(0);
//     std::ofstream file(filename);
//     if (!file.is_open()) {
//         std::cerr << "Error: Could not open the file for writing." << std::endl;
//         AlwaysAssert(false);
//         return;
//     }  
//     std::cout << "Writing to file: " << filename << std::endl;  // Debug print
//     // file << "#include \"/Library/gurobi1103/macos_universal2/include/gurobi_c++.h\"\n"
//     //      << "#include <iostream>\n"
//     //      << "int main() {\n"I 
//     //      << "    GRBEnv env = GRBEnv();\n"
//     //      << "    env.start();\n"
//     //      << "    GRBModel model = GRBModel(&env);\n";
//     for(int j = 0; j<equalities.size(); j++){
//         new_vars.push_back("gb_"+ std::to_string(j));
//     // Currently operating under the fact that the all the terms are of the form
//     // + (*..) no pluses inside multiplication if this is not true need to through an 
//     // error :) 
//         for (auto eq: equalities[j]){
//             std::cout << "Current:" << eq << "\n";
//             // x = z this should become x + (-1) z = 0;
//             Node node;
//              for (int k = 0; k<=eq.getNumChildren(); k++) {
//                 if (k == eq.getNumChildren() && k!=0){
//                      continue;
//                  }
//                 // Node node;
//                 if (eq.getNumChildren() == 0){
//                      node = eq;
//                  } else {
//                      node = eq[k];
//                  }
//                  std::cout << "Current node:" <<  node << "\n";
//             if (node.getKind() == Kind::CONST_INTEGER){
//                 if (node.getConst<Rational>().getNumerator().abs() <= 2){
//                     addConst = node.getConst<Rational>().getNumerator();
//                 } else {
//                     addConst = static_cast<int>(std::round(10*log2(node.getConst<Rational>().getNumerator().abs().getDouble())));
//                     if (node.getConst<Rational>().getNumerator() <0){
//                         addConst *= -1;
//                      }
//                 }
                
//                 if (varCoefMap.find("const") != varCoefMap.end()){
//                     if (varCoefMap["const"].find(new_vars[j]) != varCoefMap["const"].end()){
//                         varCoefMap["const"][new_vars[j]] += addConst;
//                     }
//                     else {
//                         varCoefMap["const"][new_vars[j]] = addConst;
//                     }
//                 } else {
//                     varCoefMap["const"][new_vars[j]] = addConst;
//                 }
//             } else if (isVariableOrSkolem(node)){
//                 AlwaysAssert(!node.getName().empty()) << node ;
//                 std::cout << node.getName() << "\n";
//                 if (varCoefMap.find(node.getName()) != varCoefMap.end()){
//                     if (varCoefMap[node.getName()].find(new_vars[j]) != varCoefMap[node.getName()].end()){
//                         varCoefMap[node.getName()][new_vars[j]] += 1;
//                     }
//                     else {
//                         varCoefMap[node.getName()][new_vars[j]] = 1;
//                     }
//                 } else {
//                     varCoefMap[node.getName()][new_vars[j]] = 1;
//                 }
//             }  else if (node.getKind() == Kind::MULT || node.getKind() == Kind::NONLINEAR_MULT){
//                 if (node.getNumChildren() == 2 && node[0].getKind() == Kind::CONST_INTEGER) {
//                     if (node[0].getConst<Rational>().getNumerator().abs() <= 2){
//                         addConst = node[0].getConst<Rational>().getNumerator();
//                         //std::cout << "ADDing" << addConst << "\n";
//                     } else {
//                         addConst = static_cast<int>(std::round(10*log2(node[0].getConst<Rational>().getNumerator().abs().getDouble())));
//                         if (node[0].getConst<Rational>().getNumerator() <0){
//                              addConst *= -1;
//                             }
//                         //std::cout << "ADDing" << addConst << "\n";
//                     }
//                     if (node[1].getKind() == Kind::NONLINEAR_MULT){
//                         // case when we have multiplication of variables so need to make new variable
//                         std::string name = "";
//                         std::vector<Node> myNodes; 
//                         Integer LB = 1;
//                         Integer UB = 1;
//                         for (int i = 0; i<node[1].getNumChildren(); i++) {
//                             AlwaysAssert(isVariableOrSkolem(node[1][i])) << node[i];
//                             name += node[1][i].getName() + "_";
//                             myNodes.push_back(node[1][i]);
//                             Integer pos1 = LB * bounds[node[1][i].getName()].second;
//                             Integer pos2 = UB * bounds[node[1][i].getName()].second;
//                             Integer pos3 = LB * bounds[node[1][i].getName()].first;
//                             Integer pos4 = LB * bounds[node[1][i].getName()].second;
//                             LB = Integer::min(Integer::min(pos1,pos2), Integer::min(pos3,pos4));
//                             UB = Integer::max(Integer::max(pos1,pos2), Integer::max(pos3,pos4));
//                         }
//                         // increment by addConst and use name and new_vars[j]
//                         AlwaysAssert(!name.empty()) << node ;
//                         std::cout << name << "\n";
//                         if (varCoefMap.find(name) != varCoefMap.end()){
//                             if (varCoefMap[name].find(new_vars[j]) != varCoefMap[name].end()){
//                                     varCoefMap[name][new_vars[j]] += addConst;
//                                 }
//                              else {
//                                 varCoefMap[name][new_vars[j]] = addConst;
//                             }
//                             } else {
//                             varCoefMap[name][new_vars[j]] = addConst;
//                             }
//                         nonlinearMap[name] = myNodes;
//                         nonlinearBounds[name] = std::make_pair(LB, UB);
//                         // we need to get the resulting lower and upper bounds,
//                     } else { AlwaysAssert(isVariableOrSkolem(node[1]) ) << node[1] << "\n";
//                     // now use node[1]
//                     AlwaysAssert(!node[1].getName().empty()) << node ;
//                     std::cout << node[1].getName() << "\n";
//                     if (varCoefMap.find(node[1].getName()) != varCoefMap.end()){
//                     if (varCoefMap[node[1].getName()].find(new_vars[j]) != varCoefMap[node[1].getName()].end()){
//                         varCoefMap[node[1].getName()][new_vars[j]] += addConst;
//                     }
//                     else {
//                         varCoefMap[node[1].getName()][new_vars[j]] = addConst;
//                     }
//                 } else {
//                     varCoefMap[node[1].getName()][new_vars[j]] = addConst;
//                 }
//                     }
//                 } else {
//                     addConst = Integer(1);
//                     std::string name = "";
//                     std::vector<Node> myNodes; 
//                     Integer UB = 1;
//                     Integer LB = 1;
//                     for (int i = 0; i<node.getNumChildren(); i++) {
//                         if (i == 0 && node[i].getKind()== Kind::CONST_INTEGER){ 
//                             if (node[i].getConst<Rational>().getNumerator().abs() <= 2){
//                                     addConst = node[i].getConst<Rational>().getNumerator();        
//                          } else {
//                                 addConst = static_cast<int>(std::round(10*log2(node[i].getConst<Rational>().getNumerator().abs().getDouble())));
//                                 if (node[i].getConst<Rational>().getNumerator() <0){
//                                 addConst *= -1;
//                                  }
//                                 }
                            
//                             if (addConst > 2000000000 || addConst < -2000000){
//                                 AlwaysAssert(false);
//                             }
//                             continue;
//                         }
//                         AlwaysAssert(isVariableOrSkolem(node[i]));
//                         name += node[i].getName() + "_";
//                         myNodes.push_back(node[i]);
//                         Integer pos1 = LB * bounds[node[i].getName()].second;
//                         Integer pos2 = UB * bounds[node[i].getName()].second;
//                         Integer pos3 = LB * bounds[node[i].getName()].first;
//                         Integer pos4 = LB * bounds[node[i].getName()].second;
//                         LB = Integer::min(Integer::min(pos1,pos2), Integer::min(pos3,pos4));
//                         UB = Integer::max(Integer::max(pos1,pos2), Integer::max(pos3,pos4));
//                     }
//                     if (addConst > 2000000000 || addConst < -2000000){
//                         AlwaysAssert(false);
//                     }
                    
//                 AlwaysAssert(!name.empty()) << node;
//                 std::cout << name << "\n";
//                 if (varCoefMap.find(name) != varCoefMap.end()){
//                     if (varCoefMap[name].find(new_vars[j]) != varCoefMap[name].end()){
//                         varCoefMap[name][new_vars[j]] += addConst;
//                     }
//                     else {
//                         varCoefMap[name][new_vars[j]] = addConst;
//                     }
//                 } else {
//                     varCoefMap[name][new_vars[j]] = addConst;
//                 }
//                 nonlinearMap[name] = myNodes;
//                 nonlinearBounds[name] = std::make_pair(LB, UB);
//                 }

//             } else {
//                 AlwaysAssert(false) << node.getKind();
//             }
//         }
//         }
//     }
//     nonlinearBounds["const"] = std::make_pair(1,1);
//     std::cout << "finished encoding";
//     // Okay now we have our data structures its time to write stuff :) 
//     // First write in all the variables we made.
    
//     // for (const auto& var : new_vars) {
//     //     file << "    GRBVar " << var << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << var << "\");" << std::endl;
//     // }
//     file << "Minimize \n";
//     file << "    minimize: " << new_vars[0];
//     for (size_t i = 1; i < new_vars.size(); ++i) {
//             file << " + " << new_vars[i];
//     }
//     file << std::endl;
//     file << std::endl;
//     file << "Subject To\n";
//     std::map<std::string, std::string> pos_relu_vars;
//     std::map<std::string, std::string> neg_relu_vars;
//     std::map<std::string, std::string> neg_coefficients;
//     std::map<std::string, std::string> pos_coefficients;
//     std::vector<std::string> binaries;
//     std::string upper_bound ="";
//     std::string lower_bound ="";
//     std::cout << varCoefMap.size();
//     for (auto&  pair: varCoefMap) {
//         if (pair.first.empty()) {
//             std::cout << "Warning: Empty outer key found!" << std::endl;
//         } else {
//             std::cout << "Outer key: " << pair.first << "\n";
//         }

//         // Iterate through inner map
//         for (const auto& innerPair : pair.second) {
//             std::cout << "    Inner key: " << innerPair.first << ", Value: " << innerPair.second << "\n";
//         }
//     }
//     for (auto&  pair: varCoefMap) {
//         std::cout << pair.first << "\n";
//         pos_relu_vars[pair.first] = pair.first + "coef_pos_relu";
//         neg_relu_vars[pair.first] = pair.first + "coef_neg_relu";
//         neg_coefficients[pair.first] = pair.first + "neg_coef";
//         pos_coefficients[pair.first] = pair.first + "pos_coef";
//         Integer UB; 
//         Integer LB;
//         auto it = bounds.find(pair.first);
//         if (it != bounds.end()) {
//             //std::cout << it->first << "\n";
//             //std::cout << (it->second.second).toString() << "\n";
//             if ((it->second.first).abs() <= 2) {
//                 LB = it->second.first;
//             } else {
//             LB = static_cast<int>(std::round(10 * log2((it->second.first).getDouble())));
//             }
//             std::cout << it->second.first<< "turned into" <<  LB << "\n";
//             if ( (it->second.second).abs() <= 2) {
//                 UB = it->second.second;
//             } else {
//             UB = static_cast<int>(std::round(10 * log2((it->second.second).getDouble())));
//             }
//             std::cout << it->second.second<< "turned into" <<  UB << "\n";
//         } else {
//             std::cout << "HUH?\n";
//             std::cout << pair.first << "\n";
//             it = nonlinearBounds.find(pair.first);
//             if (it != bounds.end()) {
//                 std::cout << "Something was found\n";
//                 std::cout << pair.first << "\n";
//                 std::cout << it->first << "\n";
//                 std::cout << it->second << "\n";
//             //std::cout << (it->second.second).toString() << "\n";
//             if ((it->second.first).abs() <= 2) {
//                 LB = it->second.first;
//             } else {
//             LB = static_cast<int>(std::round(10 * log2((it->second.first).getDouble())));
//             }
//             std::cout << it->second.first<< "turned into" <<  LB << "\n";
//             std::cout << "The issue is here\n";
//             if ((it->second.second).abs() <= 2) {
//                 UB = it->second.second;
//             } else {
//             UB = static_cast<int>(std::round(10 * log2((it->second.second).getDouble())));
//             }
//             std::cout << it->second.second<< "turned into" <<  UB << "\n";
//             } else {
//                 AlwaysAssert(false) << pair.first;
//             }
//         }
//         //std::cout << UB.toString() << "\n";
//         std::cout << "we are here???\n";
//         if (upper_bound.size() == 0){
//             upper_bound = UB.toString() + "  " + pos_relu_vars[pair.first] + " - " + LB.toString() + "  " + neg_relu_vars[pair.first];
//         } else {
//             upper_bound += " + " + UB.toString() + "  " + pos_relu_vars[pair.first] + " - " + LB.toString() + "  " + neg_relu_vars[pair.first];
//         }
//         if (lower_bound.size() == 0){
//             lower_bound = LB.toString() + "  " + pos_relu_vars[pair.first] + " - " + UB.toString() + "  " + neg_relu_vars[pair.first];
//         } else {
//             lower_bound += " + " + LB.toString() + "  " + pos_relu_vars[pair.first] + " - " + UB.toString() + "  " + neg_relu_vars[pair.first];
//         }

//         Integer maxPos = Integer(static_cast<int>(std::round(10*log2(modulos.getDouble() -1)))).ceilingDivideQuotient(Integer::max(LB*-1, UB));

//         //file << "    GRBVar " << neg_coefficients[pair.first] << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << neg_coefficients[pair.first] << "\");" << std::endl;
//         //file << "    GRBVar " << pos_coefficients[pair.first] << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << pos_coefficients[pair.first] << "\");" << std::endl;
//         //file << "    GRBVar " << pos_relu_vars[pair.first] << " = model.addVar(0, GRB_INFINITY, 0.0, 'I', \"" << pos_relu_vars[pair.first] << "\");" << std::endl;
//         //file << "    GRBVar " << neg_relu_vars[pair.first] << " = model.addVar(0, GRB_INFINITY, 0.0, 'I', \"" << neg_relu_vars[pair.first]  << "\");" << std::endl;
//         file << pos_coefficients[pair.first] << ": " << pos_coefficients[pair.first] << stringify(pair.second, "-") << " = 0" << "\n";
//         binaries.push_back(pair.first + "pos_binary");
//         file << "geq1_" << pos_coefficients[pair.first] << ": " <<  pos_relu_vars[pair.first]  << stringify(pair.second, "-") << " >= " << "0" << "\n";
//         file << "geq2_" << pos_coefficients[pair.first] << ": " <<  pos_relu_vars[pair.first] << " >= " << "0" << "\n";
//         file << "leq1_" << pos_coefficients[pair.first] << ": " <<  pos_relu_vars[pair.first] << stringify(pair.second, "-")  <<  " - "  << maxPos << " " << binaries[binaries.size()-1] << " <= " << 0 << "\n";
//         file << "leq2_" << pos_coefficients[pair.first] << ": " <<  pos_relu_vars[pair.first]  <<  " + "  << maxPos << " " << binaries[binaries.size()-1] << " <= " << maxPos << "\n";
       

//         //file << pos_relu_vars[pair.first] << ": " << pos_relu_vars[pair.first] << " MAX (" << pos_coefficients[pair.first] << " , 0 )" << "\n";
//         file << neg_coefficients[pair.first] << ": "  << neg_coefficients[pair.first] << stringify(pair.second, "+") << " = 0" << "\n";
//         binaries.push_back(pair.first + "neg_binary");
//          file << "geq1_" << neg_coefficients[pair.first] << ": " <<  neg_relu_vars[pair.first]  << stringify(pair.second, "+") << " >= " << "0" << "\n";
//         file << "geq2_" << neg_coefficients[pair.first] << ": " <<  neg_relu_vars[pair.first] << " >= " << "0" << "\n";
//         file << "leq1_" << neg_coefficients[pair.first] << ": " <<  neg_relu_vars[pair.first] << stringify(pair.second, "+")  <<  " - "  << maxPos << " " << binaries[binaries.size()-1] << " <= " << 0 << "\n";
//         file << "leq2_" << neg_coefficients[pair.first] << ": " <<  neg_relu_vars[pair.first]  <<  " + "  << maxPos << " " << binaries[binaries.size()-1] <<  " <= " << maxPos << "\n";
//         //file << neg_relu_vars[pair.first] << ": " << neg_relu_vars[pair.first] << " MAX (" << neg_coefficients[pair.first] << " , 0 )" << "\n";
        

//     }
//     file << "upper : "  << upper_bound << " <= " << static_cast<int>(std::round(10*log2(modulos.getDouble() -1)))  << std::endl;
//     file << "lower : " <<  lower_bound << " >= " <<  "-  " << static_cast<int>(std::round(10*log2(modulos.getDouble() -1)))  << std::endl;
//     std::string nonzero="";
//     for (auto&  pair: varCoefMap) {
//         if (nonzero.size()==0){
//             nonzero = neg_relu_vars[pair.first] + " + " + pos_relu_vars[pair.first];
//         } else {
//             nonzero += " + " + neg_relu_vars[pair.first] + " + " + pos_relu_vars[pair.first];
//         }
//     }

//     file << "nonzero : " << nonzero << " >= 1" << std::endl;
//     std::vector<std::string> c_old;
//     std::vector<std::string> c_orth;
//     if (pastSolutions.size()>0){
//         std::cout << "Started finding basis\n";
//         std::vector<std::vector<double>> curBasis = findBasis(pastSolutions);
//         std::cout << "So the issue is here?\n";
//         printBasis(curBasis);
//         AlwaysAssert(curBasis.size() == curBasis[0].size()) << curBasis.size() << " but " << curBasis[0].size();
//         int n = pastSolutions.size();
//         std::vector<std::string> constraints;
//         for(int i = 0;i <curBasis.size(); i++){
//             constraints.push_back("");
//             if (i < n){
//                 c_old.push_back("c_old" + std::to_string(i));
//                 //file << "    GRBVar " << c_old.back() << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << c_old.back() << "\");" << std::endl;

//             } else {
//                 c_orth.push_back("c_orth" + std::to_string(i));
//                  //file << "    GRBVar " << c_orth.back() << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << c_orth.back() << "\");" << std::endl;
//             }

//         }
//         for(int i = 0;i <curBasis.size(); i++){
//             for(int j=0; j<curBasis[i].size(); j ++){
//                 // c determined by i 
//                 std::string cur_c;
//                 // constraint determined by j 
//                 if (i < n){
//                     cur_c = c_old[i];
//                 } else {
//                     cur_c = c_orth[i-n];
//                 }
//             if (constraints[j].size() == 0){
//                 constraints[j] = std::to_string(curBasis[i][j]) + " " +  cur_c;
//             } else {
//                 if (curBasis[i][j] < 0){
//                     constraints[j] += std::to_string(curBasis[i][j]) + " " +  cur_c;
//                 } else {
//                     constraints[j] += " + " + std::to_string(curBasis[i][j]) + " " +  cur_c;
//                 }

//             }
//             }
//         }
//         for(int i = 0; i<constraints.size(); i++){
//             file << new_vars[i]  << " : " <<  constraints[i] << " - " << new_vars[i] << " = 0" <<  std::endl;
//         }
//         std::string nonzero_c = "";
//         for(int i=0; i<c_orth.size(); i++){
//             if (nonzero_c == ""){
//                 nonzero_c = c_orth[i];
//             } else {
//                 nonzero_c += " + " + c_orth[i];
//             }
//         }
//         file <<  "nonzero_c : " + nonzero_c + " >= 1" << std::endl;


//     }
//     file << std::endl;
//     file << "Bounds" << std::endl;
//     // now we have to define the bounds 
//     for (auto i: c_orth){
//         file << i << " free" << std::endl;
//     }
//     for (auto i: c_old){
//         file <<  i << " free" << std::endl;
//     }
//     for (const auto& var : new_vars) {
//         file <<  var <<  " free" << std::endl;
//     }
//     for (const auto&  pair: varCoefMap) {
//         file <<  pos_relu_vars[pair.first] <<  " free" << std::endl;
//         file <<  neg_relu_vars[pair.first] <<  " free" << std::endl;;
//         file <<  neg_coefficients[pair.first] << " free" <<  std::endl; 
//         file <<  pos_coefficients[pair.first] << " free" <<  std::endl;
//     }

//     // now we have to define that all our variables are general
//     file << std::endl;
//     file << "General" << std::endl;
//     for (auto i: c_orth){
//         file << i << std::endl;
//     }
//     for (auto i: c_old){
//         file << i << std::endl;
//     }
//     for (const auto& var : new_vars) {
//         file << var <<  std::endl;
//     }
//     for (const auto&  pair: varCoefMap) {
//         file << pos_relu_vars[pair.first] << std::endl;
//         file << neg_relu_vars[pair.first] << std::endl;;
//         file << neg_coefficients[pair.first] << std::endl; 
//         file << pos_coefficients[pair.first] << std::endl;
//     }

//     file << std::endl;
//     file << "Binaries" << std::endl;
//     for (auto i: binaries){
//         file << i << std::endl;
//     }
//     std::cout << "We actually got here \n";
//     // file << "    model.optimize();" << std::endl;
//     // file << "    std::cout << \"Optimal solution:\" << std::endl;" << std::endl;
//     // for (const auto&  var: new_vars) {
//     //     file  << "    std::cout << \"" << var << ": \" << " << var << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
//     // }
//     // //  for (const auto&  var: pos_coefficients) {
//     // //     file  << "    std::cout << \"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
//     // // }
//     // //  for (const auto&  var: neg_coefficients) {
//     // //     file  << "    std::cout << \"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
//     // // }
//     // //  for (const auto&  var: pos_relu_vars) {
//     // //     file  << "    std::cout << \"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
//     // // }
//     // //  for (const auto&  var: neg_relu_vars) {
//     // //     file  << "    std::cout << \"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
//     // // }
//     // file << "    };" << std::endl;
//     std::cout << "Sanity Check\n";
//     std::cout << "Number of OG Variables:" << varCoefMap.size() << "\n";
//     std::cout << "Number of New Variables:" << new_vars.size() << "\n";
//     std::string hellp = readFileToString(filename);
//     std::cout << hellp << "\n";
    
//    file.flush(); 
//    file.close();

// };
 
 
 
 void write_smt_query(const std::string& filename,
                     const std::vector<Node>& equalities, 
                     const std::vector<Node>& inequalities, 
                     const std::map<std::string, std::pair<Integer, Integer>>& bounds) {
    std::ofstream file(filename);
    if (!file.is_open()) {
        std::cerr << "Error: Could not open the file for writing." << std::endl;
        return;
    }
    // Start writing SMT-LIB content
    file << "(set-logic QF_NIA)\n\n";
    // Declare variables
    for (auto var : bounds) {
        file << "(declare-const " << var.first << " Int)\n";
    }
    file << "\n";
    // Write the equalities
    for (auto eq : equalities) {
        file << "(assert " << eq << ")\n";
    }
    file << "\n";
    // Write the inequalities
    for (auto ineq : inequalities) {
        file << "(assert (not " << ineq << "))\n";
    }
    file << "\n";
    // Write bounds as inequalities
    for (auto& bound : bounds) {
        const std::string& var = bound.first;
        const Integer& lower_bound = bound.second.first;
        const Integer& upper_bound = bound.second.second;
        file << "(assert (<= " << lower_bound << " " << var << "))\n";
        file << "(assert (<= " << var << " " << upper_bound << "))\n";
    }
    file << "\n";
    // Check satisfiability and get the model
    file << "(check-sat)\n(get-model)\n";
    file.close();
    std::cout << "SMT query successfully written to " << filename << std::endl;
}



std::string runcvc5(std::string input)
{
  //std::cout << program << "\n";
  std::filesystem::path output = tmpPath();
  //std::filesystem::path input = writeToTmpFile(program);
  std::stringstream commandStream;
  commandStream << "../../real_cvc5/cvc5/build/bin/cvc5  --produce-models " << input << " > " << output;
  std::string command = commandStream.str();
  Assert(exitCode == 0) << "Singular errored\nCommand: " << command;
  std::string outputContents = readFileToString(output);
  Assert(outputContents.find("?") == std::string::npos) << "Singular error:\n"
                                                        << outputContents;
  std::filesystem::remove(output);
  //std::filesystem::remove(input);
  //std::cout << outputContents << "\n";
  return outputContents;
}

std::string runGurobi(const std::string& filename)
{
  std::filesystem::path output1 = tmpPath();
  output1 = output1.concat(".sol");
  //std::string output1 = "hello.txt";
  //std::filesystem::path output2 = tmpPath();
//   std::cout << "Program is in " << filename << "\n";
//   std::cout << "We will write it to " << output1 << "\n";
  //std::filesystem::path input = writeToTmpFile(program);

  std::stringstream commandStream;
  //commandStream << "g++ " << filename <<  " -o " << output1 <<  " -I/Library/gurobi1103/macos_universal2/include -L/Library/gurobi1103/macos_universal2/lib /Library/gurobi1103/macos_universal2/lib/libgurobi110.dylib -lgurobi_c++";
  //commandStream << "/barrett/scratch/aozdemir/gurobi/cluster_gurobi_cl OutputFlag=0  ResultFile=" << output1 << " " << filename;
  commandStream << "/barrett/scratch/pertseva$ glpk/bin/glpsol --tmlim 60 --lp " << filename << " -o "  << output1 << " > h 2>&1" ;
  std::string command = commandStream.str();
  //std::cout << command << "\n";
  int exitCode = std::system(command.c_str());
  AlwaysAssert(exitCode == 0) << "Gurobi errored\nCommand: " << command;
//   std::cout << "Compilation worked\n";
//   exitCode = std::system(( output1.string() +  " >> " + output2.string()).c_str());
//     std::cout << "Running the command worked\n";
 std::string outputContents = readFileToString(output1);
 //std::cout << "Result:" << outputContents << "\n";
//   Assert(outputContents.find(" error:") == std::string::npos) << "Gurobi error:\n"
// std::string word;
    // Read the file word by word
  //std::filesystem::remove(filename);
  std::filesystem::remove(output1);
  //std::cout << outputContents << "\n";
  return outputContents;
}

std::string runGLPK(const std::string& filename)
{
  //std::cout << program << "\n";
  std::filesystem::path output1 = tmpPath();
  output1 = output1.concat(".sol");
  //std::string output1 = "hello.txt";
  //std::filesystem::path output2 = tmpPath();
  std::cout << "Program is in " << filename << "\n";
  std::cout << "We will write it to " << output1 << "\n";
  //std::filesystem::path input = writeToTmpFile(program);

  std::stringstream commandStream;
  //commandStream << "g++ " << filename <<  " -o " << output1 <<  " -I/Library/gurobi1103/macos_universal2/include -L/Library/gurobi1103/macos_universal2/lib /Library/gurobi1103/macos_universal2/lib/libgurobi110.dylib -lgurobi_c++";
  commandStream << "glpsol --tmlim 60 --lp " <<  filename << " -o " << output1;
  std::string command = commandStream.str();
  std::cout << command << "\n";
  int exitCode = std::system(command.c_str());
  AlwaysAssert(exitCode == 0) << "GLPK errored\nCommand: " << command;
//   std::cout << "Compilation worked\n";
//   exitCode = std::system(( output1.string() +  " >> " + output2.string()).c_str());
//     std::cout << "Running the command worked\n";
 std::string outputContents = readFileToString(output1);
 std::cout << "Result:" << outputContents << "\n";
//   Assert(outputContents.find(" error:") == std::string::npos) << "Gurobi error:\n"
// std::string word;
    // Read the file word by word
  //std::filesystem::remove(filename);
  std::filesystem::remove(output1);
  //std::cout << outputContents << "\n";
  return outputContents;
}




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
    AlwaysAssert(false) << eq << "," << eq.getKind();
}


std::set<std::string> getVars(std::vector<Node> eqs){
    std::set<std::string> answer;
    for (auto eq: eqs){
        std::set<std::string> moreVars = getVarsHelper(eq);
        answer.insert(moreVars.begin(), moreVars.end());
    }
    return answer;
}

void noCoCoALiza()
{
    std::cout << "cvc5 can't solve field problems since it was not configured with "
      "--cocoa\n";
    AlwaysAssert(false);
}

CoCoA::ideal getCocoaGB(Field *F, CocoaEncoder &enc, NodeManager* nm){
      if ((*F).equalities.size() <= 1) { 
        //return;
        //AlwaysAssert(false) << "NEED TO THINK ABOUT THIS\n";
      }
    //   if (!((*F).modulos).isProbablePrime()){
    //     AlwaysAssert(false) << "have not thought about how to do this with non primes\n";
    //   }
      //CocoaEncoder enc = CocoaEncoder((*F).modulos);
      std::vector<Node> negativeFacts;
      for (const Node& node : (*F).inequalities)
       {
        negativeFacts.push_back(nm->mkNode(Kind::NOT, node));
    }
      for (const Node& node : (*F).equalities)
      {
        enc.addFact(node);
      }
    for (const Node& node : negativeFacts)
       {
        enc.addFact(node);
    }
      enc.endScan();
      for (const Node& node :(*F).equalities)
      {
        enc.addFact(node);
      }
     for (const Node& node : negativeFacts)
        {
         enc.addFact(node);
     }
      std::cout << "Getting ideal?\n";

      std::vector<CoCoA::RingElem> generators;
      generators.insert(
          generators.end(), enc.polys().begin(), enc.polys().end());
      std::vector<Node> newPoly;
      std::cout << "Getting ideal?\n";
      try {
      CoCoA::ideal ideal = CoCoA::ideal(generators);
      }  catch (const CoCoA::ErrorInfo& e) {
        std::cerr << "Caught CoCoA::ErrorInfo exception: " << e << std::endl;
        AlwaysAssert(false);
      }

      return CoCoA::ideal(generators);
      //auto basis = CoCoA::GBasis(ideal);
      //return basis;
}




// Function to parse and convert S-expression style equations




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

Node IntegerField::substituteTargetVariableWithZero(const Node& node, std::string targetNode) {
     NodeManager* nm = NodeManager::currentNM();
    if ( isVariableOrSkolem(node) && node.getName() == targetNode) {
        // Replace target variable with zero
        return nm->mkConstInt(0);
    }

    // If the node has children, apply substitution to each child
    std::vector<Node> newChildren;
    bool hasChanged = false;

    for (size_t i = 0; i < node.getNumChildren(); ++i) {
        Node child = node[i];
        Node newChild = substituteTargetVariableWithZero(child, targetNode);

        if (newChild != child) {
            hasChanged = true;
        }

        newChildren.push_back(newChild);
    }

    // If any children changed, create a new node with substituted children
    if (hasChanged) {
        return nm->mkNode(node.getKind(), newChildren);
    } else {
        // Return the original node if no substitution was needed
        return node;
    }

}
bool containsVariable(const Node& node, std::string targetNode) {
    if (node.getName() == targetNode) {
        return true;
    }
    for (size_t i = 0; i < node.getNumChildren(); ++i) {
        if (containsVariable(node[i], targetNode)) {
            return true;
        }
    }
    return false;
}

std::pair<Node, Node> IntegerField::separateTerms(const Node& node, std::string targetNode) {
    std::vector<Node> withTarget, withoutTarget;
    NodeManager* nm = NodeManager::currentNM();
    if (isVariableOrSkolem(node)){
        if (containsVariable(node,targetNode)){
            return {nm->mkConstInt(0), node };
        } else {
            AlwaysAssert(false);
        }
        
    }
    else if (node.getKind() == Kind::ADD) {
        for (size_t i = 0; i < node.getNumChildren(); ++i) {
            Node child = node[i];
            if (containsVariable(child, targetNode)) {
                withTarget.push_back(child);
            } else {
                withoutTarget.push_back(child);
            }
        }
        Node withTargetNode = rewrite(nm->mkNode(Kind::ADD, withTarget));
        Node withoutTargetNode = rewrite(nm->mkNode(Kind::ADD, withoutTarget));
        return {withoutTargetNode, withTargetNode};

    } else if (node.getKind() == Kind::MULT) {
          if (containsVariable(node,targetNode)){
            return {nm->mkConstInt(0), node };
        } else {
            return {node, nm->mkConstInt(0)};
        }
    } else {
        AlwaysAssert(false) << node;
    }
}




bool IntegerField::tightenBounds(std::map<std::string, std::pair<Integer, Integer> > &Bounds){
this->novelBound = false;
bool newBound = true;
while (newBound) {
    newBound = false;
for (int i = 0; i < equalities.size(); i++) {
        //std::cout << equalities[i] << "\n";
        if ( isVariableOrSkolem(equalities[i][0])  && equalities[i][1].getKind() == Kind::CONST_INTEGER){
            //std::cout << "triggered\n";
            Integer value = equalities[i][1].getConst<Rational>().getNumerator();
            Bounds[equalities[i][0].getName()] = std::make_pair(value,value);
            continue;
        }
        std::set<std::string> variables = getVarsHelper(equalities[i]);
        
        std::vector<std::string> largeBoundVars;
        
        std::string maxVar;
        Integer maxRange = -1;

        for (const auto& var : variables) {
        //     Integer boundRange = Bounds[var].second - Bounds[var].first;
        //     if (boundRange > maxRange) {
        //         maxRange = boundRange;
        //         maxVar = var;
        //         isUnique = true; // Reset uniqueness as we found a larger range
        //     } else if (boundRange == maxRange) {
        //         isUnique = false; // Not unique if another variable shares this range
        //     }
        // }
        
        // if (!isUnique) {
        // //     continue;
        // } else {
            // std::string targetVar =maxVar;
            std::string targetVar = var;
            //std::cout << "INFERING BOUNDS FOR" << targetVar << "\n";
            //std::cout << equalities[i] << "\n";
            NodeManager* nm = NodeManager::currentNM();
            Node changed = nm->mkNode(Kind::ADD, equalities[i][1], nm->mkNode(Kind::MULT, nm->mkConstInt(-1), equalities[i][0]));
            std::pair<Node, Node> seperatedNodes = separateTerms(rewrite(changed),targetVar);
            Integer frac =  Integer(-1);
            // std::cout << "With" << seperatedNodes.second << "\n";
            // std::cout << "Without" << seperatedNodes.first << "\n";
            if (seperatedNodes.second.getNumChildren()>= 2){
                if (seperatedNodes.second.getKind() == Kind::MULT && 
                   seperatedNodes.second.getNumChildren() == 2 && 
                   seperatedNodes.second[0].getKind() == Kind::CONST_INTEGER ){
                    frac = frac * seperatedNodes.second[0].getConst<Rational>().getNumerator() ;
                    //std::cout << "Frac was set to true\n";
                   } else {
                    // std::cout << "ISOLATION FAILED for" << targetVar << "\n";
                    // std::cout << seperatedNodes.first << "\n";
                    // std::cout << seperatedNodes.second << "\n";
                    return true;
                   }
            }
            
           
            
            //Node finalNode = nm->mkNode(Kind::SUB, equalityNode[0], equalityNode[1]);
            std::pair<Integer, Integer> inferredBounds = inferBoundsRecursive(seperatedNodes.first, Bounds);
            //std::cout << inferredBounds << "\n";
            //Bounds[targetVar] = inferredBounds;
            //std::cout << targetVar << "\n";
	        // std::cout << "ogBounds" << Bounds[targetVar] << "\n";
            // std::cout << "INFEREED BOUNDS " << inferredBounds << "\n";
            // std::cout << "FRAC" << frac << "\n";
            Rational product1 = Rational(inferredBounds.first)/ Rational(frac);
            Rational product2 = Rational(inferredBounds.second)/ Rational(frac);
            //std::cout << "(" << product1 << "," << product2 << ")" << "\n";
            Integer upper = (Rational::max(product1, product2)).floor();
            Integer lower = (Rational::min(product1, product2)).ceiling();
            //std::cout << "(" << lower << "," << upper << ")" << "\n";
            inferredBounds = std::make_pair(lower,upper);
	    //std::cout << inferredBounds << "\n";
            // Integer products[4] = {
            //     childBounds.first * childBounds.first,
            //     childBounds.first * childBounds.second,
            //     childBounds.second * childBounds.first,
            //     childBounds.second * childBounds.second
            // };



            // if (frac){
            //     // Think about this
            //     Integer divisor = Integer(-1) * seperatedNodes.second[0].getConst<Rational>().getNumerator();
            //     inferredBounds = std::make_pair(inferredBounds.first.floorDivideQuotient(divisor), inferredBounds.second.floorDivideQuotient(divisor));
            //     std::cout << "INFEREED BOUNDS " << inferredBounds << "\n";
            // }
            //std::cout << targetVar << "\n";
            //std::cout << "oldBounds: " << Bounds[targetVar] << "\n";
            // if (inferredBounds.second <0){
            //     AlwaysAssert(false) << inferredBounds;
            // }
            
            if (inferredBounds.second < Bounds[targetVar].second){
                Bounds[targetVar].second = inferredBounds.second ;
                newBound = true;
                this->novelBound = true;
                //std::cout << inferredBounds.second;
                //std::cout << Bounds[targetVar].second;
            } 
            if (inferredBounds.first > Bounds[targetVar].first ){
                 Bounds[targetVar].first = inferredBounds.first;
                 this->novelBound = true;
                 newBound = true;
                 //std::cout << inferredBounds.second;
                 //std::cout << Bounds[targetVar].second;
            }
            //std::cout << "NewBounds " << Bounds[targetVar] << "\n";
            if (Bounds[targetVar].first > Bounds[targetVar].second){
                std::cout << "BOUNDS ISSUE!!!";
                //std::cout << targetVar << "\n";
                this->status = Result::UNSAT;
                return true;
            }
            if (Bounds[targetVar].first == Bounds[targetVar].second){
                std::string singularName = replaceDots(targetVar);
                Node target = this->solver->myVariables[singularName];
                this->addEquality(nm->mkNode(Kind::EQUAL, target, nm->mkConstInt(Bounds[targetVar].first)), false);
                //std::string singularName = replaceDots(sk.getName());
                //myVariables[singularName] = sk;
            }
            //AlwaysAssert(false);
        //}
    }
        
    }
    // if (newBound){
    //     this->novelBound = true;
    // }
}
    return true;
}

// Recursive helper function that returns both lower and upper inferred bounds
std::pair<Integer, Integer> IntegerField::inferBoundsRecursive(const Node& node, std::map<std::string,  std::pair<Integer, Integer>>& Bounds) {
    //std::cout << node << "\n";
    if (node.getKind() == Kind::CONST_INTEGER) {
        Integer constValue = node.getConst<Rational>().getNumerator();
        //std::cout << constValue << "\n";
        return {constValue, constValue};  // Both lower and upper are the constant value
    } else if ( isVariableOrSkolem(node)) {
        std::string varName = node.getName();
        return Bounds[varName];  // Return both lower and upper bounds for the variable
    }

     std::pair<Integer, Integer> result;
    if (node.getKind() == Kind::ADD) {
        Integer lowerSum = 0, upperSum = 0;
        for (Node child : node) {
            //std::cout << child << "\n";
            std::pair<Integer, Integer> childBounds = inferBoundsRecursive(child, Bounds);
            lowerSum += childBounds.first;
            upperSum += childBounds.second;
        }
        result = {lowerSum, upperSum};
    } else if (node.getKind() == Kind::MULT || node.getKind() == Kind::NONLINEAR_MULT) {
        Integer minProduct = 1;
        Integer maxProduct = 1;
        for (Node child : node) {
            //std::cout << node << "\n";
             std::pair<Integer, Integer> childBounds = inferBoundsRecursive(child, Bounds);

            // Multiply each combination of lower and upper bounds
            Integer products[4] = {
                childBounds.first * minProduct,
                childBounds.first * maxProduct,
                childBounds.second * minProduct,
                childBounds.second * maxProduct
            };
            minProduct = std::min({products[0], products[1], products[2], products[3]});
            maxProduct = std::max({products[0], products[1], products[2], products[3]});
            //std::cout << maxProduct << "\n";
        }
        
        result = {minProduct, maxProduct};
    } else if (node.getKind() == Kind::SUB) {
        std::pair<Integer, Integer> leftBounds = inferBoundsRecursive(node[0], Bounds);
        std::pair<Integer, Integer> rightBounds = inferBoundsRecursive(node[1], Bounds);
        result = {
            leftBounds.first - rightBounds.second,  // Min difference
            leftBounds.second - rightBounds.first    // Max difference
        };
    } else {
        AlwaysAssert(false);
    }

    // Handle other operations similarly if needed
    return result;
}


/////////////////////////////////////////////////// INTEGERFIELD ////////////////////////////////////////////////////////////////////

IntegerField::IntegerField(Env &env, RangeSolver* solver):EnvObj(env){this->solver = solver;};

bool IntegerField::Simplify(std::map<Integer, Field>& fields, std::map<std::string, std::pair<Integer, Integer> > &Bounds){
    //std::cout << "simplifying integers\n";
    NodeManager* nm = NodeManager::currentNM();
    tightenBounds(Bounds);
    if (status == Result::UNSAT){
        std::cout << "INTEGER UNSAT DUE TO BOUNDS\n";
        return false;
    }
    if (newEqualitySinceGB && !ranGB && !GBTimedOut){
       if(!runGB()){
        GBTimedOut = true;
       };
    }
    if (status == Result::UNSAT){
        return false;
    }
    if (newEqualitySinceGB && (inequalities.size()>0)){
    for(Node diseq: inequalities){
        //std::cout << diseq<< "\n";
        if (reduceAgainstGB(diseq)){
            status = Result::UNSAT;
         }
    }
    }
    newEqualitySinceGB = false;


    // if (unlowerableIneq){
    //     std::cout << "COMPUTING GB IN THE INTEGERS WOOO!\n";
    // std::vector<Node> newPoly = SimplifyViaGB(this, Bounds, nm, true);
    //     //     //TODO FOR LEGIBILITY THIS SHOULD BE SWAPPED 
    //     //      //std::cout << "Finished GB\n";
    //     //      //std::cout << newPoly.size() << "\n";

    //     //This should be switched!!! 
    //     if (newPoly.size() == 0 && equalities.size()!=0){
    //             std::cout << "GB TOOK TOO LONG\n";
    //             for (auto& fieldPair : fields){
    //     //std::cout << "LOWERING\n";
    //             Lower(fieldPair.second,Bounds);
    //             }
    //             unlowerableIneq = false;
    //             return false;

    //             return false;
    //             //std::cout << equalities.size() << "\n";
               
    //             //AlwaysAssert(false);
    //         }
    //     if (newPoly.size() != 0 && newPoly[0]== nm->mkConstInt(Integer(1))){
    //             std::cout << "INTEGER GB FAULT \n";
    //             status = Result::UNSAT;
    //             //AlwaysAssert(false);
                
    //             return false;
    //     }
    //         //std::cout <<  "Finished GB check\n";
    //         clearEqualities();
    //         for (Node poly: newPoly){
    //             //std::cout << "New Poly F:" << poly << "\n";
    //             if (rewrite(poly).getKind() == Kind::CONST_BOOLEAN && 
    //                 rewrite(poly).getConst<bool>() == false){
    //                     status = Result::UNSAT;
    //                     std::cout << "SOME ISSUE WE ARE NOT CATCHING\n" << poly;
    //                     //AlwaysAssert(lemmas.size()==0) << modulos;
    //                     return false;
    //             }
    //             addEquality(rewrite(poly));
    //         }
    // //}
    if (status == Result::UNSAT){
        std::cout << "INTEGER UNSAT AAAA\n";
        return false;
    }
    //substituteVariables();
    //clearEqualities();
    //for (Node poly: newPoly){
        //std::cout << "New Poly F:" << poly << "\n \n \n";
        //std::cout << poly << "\n";
        //addEquality(rewrite(poly));
    //}
    //AlwaysAssert(equalities.size() == newPoly.size());
    //std::cout << "FINISHED ADDING FOR INTEGERS\n";
    //int nonLowCount = 0;
    //std::cout << "lowering?\n";
    for (auto& fieldPair : fields){
        //std::cout << "LOWERING\n";
        Lower(fieldPair.second,Bounds);
        //nonLowCount +=  static_cast<int>(unlowerableIneq);
        // if (!unlowerableIneq){
        //     nonLowCount +=1;
        // }
    }
    // if(nonLowCount == 0){
    //     unlowerableIneq = true;
    //     }
    // else{
    //     unlowerableIneq = false;
    // }

    //std::cout << "FINISHED LOWERING\n" << unlowerableIneq << nonLowCount << "\n" ;
    return true;
}

void IntegerField::addEquality(Node fact, bool GBAddition){
    //std::cout << "INTEGER FIELD LOOKING ATT" << equality << "\n";
    fact = rewrite(fact); 
    if (fact.getKind() == Kind::CONST_BOOLEAN){
        if (fact.getConst<bool>() == false){
            status = Result::UNSAT;
        }
        return;
    } 
    if (std::find(equalities.begin(), equalities.end(), fact) == equalities.end()
        && fact.getKind() != Kind::CONST_BOOLEAN && fact.getKind()!=Kind::NULL_EXPR
        ){
        
        AlwaysAssert(fact.getKind() == Kind::EQUAL) << fact;
        if(!GBAddition){
            //std::cout << "Adding" << fact << "\n";
            if (!ranGB &!GBTimedOut){
                //std::cout << "We should be here?\n";
                if (!runGB()){
                    GBTimedOut = true;
                };
                ranGB = true;
            }
            //std::cout<< "Why are we here?\n";
            //std::cout << ranGB << GBTimedOut << "\n";
            if (GBTimedOut){
                newEqualitySinceGB = true;
                ranGB = false;
                mySingularReduce = "";
                equalities.push_back(fact);
                return;
            }
            if (reduceAgainstGB(fact)){
                
                return;
            } else {
                newEqualitySinceGB = true;
                ranGB = false;
                mySingularReduce = "";
                equalities.push_back(fact);
                return;
            }
        }
        equalities.push_back(fact);
        return;
    };
    return;
}

void IntegerField::addInequality(Node inequality){
    if (std::find(inequalities.begin(), inequalities.end(), inequality) == inequalities.end()){
        inequalities.push_back(inequality);
    }

};

// Can always lower Equalities 
void IntegerField::Lower(Field& field, std::map<std::string, std::pair<Integer, Integer> > Bounds){
    for (int i=0; i<equalities.size(); i++){
            field.addEquality(equalities[i], false, false);
    }
// Need to check if can lower 
    unlowerableIneq = false;
    for (int i=0; i<inequalities.size(); i++){
        if (checkIfConstraintIsMet(inequalities[i], field.modulos, Bounds, true)){
                field.addInequality(inequalities[i]);
        } else{
            unlowerableIneq = true;
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
        //if (!(new_value < 0 && new_value > modulos * -1)){
        new_value =new_value.floorDivideRemainder(modulos);
       // }
         if (( new_value.abs() >= modulos.floorDivideQuotient(2)) && new_value * -1 < modulos ){
              if (new_value >0){
              new_value =  new_value- modulos;
              }
              else {
                 new_value = new_value + modulos;
              }
        }
         if (( new_value.abs() >= modulos.floorDivideQuotient(2)) && new_value * -1 > modulos ){
              new_value =  new_value + modulos;
         }
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
    fact = rewrite(fact); 
   
    //std::cout << "IN FIELD" << inField << "\n";
    //std::cout << "GB ADdition" << GBAddition << "\n";
    if (fact.getKind() == Kind::CONST_BOOLEAN){
        if (fact.getConst<bool>() == false){
            status = Result::UNSAT;
        }
        return;
    } 
    if (inField && std::find(equalities.begin(), equalities.end(), fact) == equalities.end()
        && fact.getKind() != Kind::CONST_BOOLEAN && fact.getKind()!=Kind::NULL_EXPR
        ){
        //std::cout << "Why are we here?\n";
        AlwaysAssert(fact.getKind() == Kind::EQUAL) << fact;
        if(!GBAddition){
            //std::cout << "Then we should be here\n";
            if (!ranGB & !GBTimedOut){
                if(!runGB(solver->Bounds)){
                    GBTimedOut = true;
                };
                ranGB = true;
            }
            if (GBTimedOut){
               // std::cout << "We added TimeOUT" << fact << "\n";
                newEqualitySinceGB = true;
                ranGB = false;
                mySingularReduce = "";
                equalities.push_back(fact);
                //std::cout << "Existing equalities:" << "\n";
                // for (auto i: equalities){
                //     std::cout << i << "\n";
                    
                // }
                return;
            }
            if (reduceAgainstGB(solver->Bounds, fact)){
                return;
            } else {
                //std::cout << "We added Reduce" << fact << "\n";
                newEqualitySinceGB = true;
                ranGB = false;
                mySingularReduce = "";
                equalities.push_back(fact);
                ALLequalities.push_back(fact);
                //  std::cout << "Existing equalities:" << "\n";
                // for (auto i: equalities){
                //     std::cout << i << "\n";
                    
                // }
                return;
            }

        } else {
        equalities.push_back(fact);     
        ALLequalities.push_back(fact);
        return;
        }
    } else if (!inField) {
        NodeManager* nm = NodeManager::currentNM();
        Node LHS = modOut(fact[0]);
        Node RHS = modOut(fact[1]);
        Node result = nm->mkNode(Kind::EQUAL, LHS, RHS);
        addEquality(result, true, GBAddition);
        return;
    }
    return;
    }

bool Field::ShouldLearnLemmas(Node fact,std::map<std::string, std::pair<Integer, Integer> > Bounds ){
    if ( isVariableOrSkolem(fact[0])
    && (fact[1].getKind() == Kind::MULT || fact[1].getKind() == Kind::NONLINEAR_MULT)
    && isVariableOrSkolem(fact[1][0])
    && isVariableOrSkolem(fact[1][1]) 
    && fact[0].getName() == fact[1][0].getName()
    && fact[0].getName() == fact[1][1].getName()
    && modulos.isProbablePrime()) {
        NodeManager* nm = NodeManager::currentNM();
        lemmas.push_back(nm->mkNode(Kind::OR,
        nm->mkNode(Kind::EQUAL, fact[0],  nm->mkConstInt(0)) ,
        nm->mkNode(Kind::EQUAL, fact[0],  nm->mkConstInt(0))));
        status = Result::UNSAT;
        return true;
    }
    if ( isVariableOrSkolem(fact[1])
    && ( fact[0].getKind() == Kind::MULT || fact[0].getKind() == Kind::NONLINEAR_MULT)
    && isVariableOrSkolem(fact[0][0]) 
    && isVariableOrSkolem(fact[0][1]) 
    && fact[1].getName() == fact[0][0].getName()
    && fact[1].getName() == fact[0][1].getName()
    && modulos.isProbablePrime()) {
        NodeManager* nm = NodeManager::currentNM();
        lemmas.push_back(nm->mkNode(Kind::OR,
        nm->mkNode(Kind::EQUAL, fact[1], nm->mkConstInt(0)),
        nm->mkNode(Kind::EQUAL, fact[1], nm->mkConstInt(1))));
        status = Result::UNSAT;
        return true;
    }
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


bool Field::LiftViaILP(IntegerField& Integers, std::map<std::string, std::pair<Integer, Integer> > Bounds){
    NodeManager* nm = NodeManager::currentNM();
    std::vector<std::vector<Rational>> curBasis;
    std::string output; 
    std::vector<int> coefficients;
    std::vector<Node> procEqual;
    for (auto i: equalities){
            procEqual.push_back(rewrite(nm->mkNode(
                Kind::ADD, i[0], rewrite(nm->mkNode( Kind::MULT, i[1], 
                nm->mkConstInt(-1))))));
    }
    bool gurobiNew = true;
    std::map<std::string, std::vector<Rational>> monomialMap = collectMonomials(Integers, *this, nm);
    std::vector<std::string> monomials;
    for (const auto& pair : monomialMap) {
        monomials.push_back(pair.first);
    }
    for (int i =0; i<(monomialMap.begin()->second).size(); i++){
        std::vector<Rational> temp;
        for (const auto& pair : monomialMap) {
            temp.push_back(pair.second[i]);
            }
        curBasis.push_back(temp);
    }
        while(gurobiNew) {
            std::filesystem::path input = tmpPath();
            std::filesystem::remove(input);
            input = input.concat(".lp");
            write_gurobi_query_new(input, procEqual, Bounds, nm, modulos, curBasis, monomials, 0);
            auto result = std::make_shared<std::string>("");
            std::shared_ptr<bool> done = std::make_shared<bool>(false);
            std::mutex resultMutex;
            auto future = std::async(std::launch::async, [&]() {
                auto res = runGurobi(input);
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
            // if (output.empty()){
            //     AlwaysAssert(false);
            // }
            // std::cout << output << "\n";
            // std::cout << "we got here\n";
            // //AlwaysAssert(false);
            //std::cout << output << "\n";
            coefficients = parseGlpkOutput(output);
            if (coefficients.size() == 0 && curBasis.size() > 0){
                // TODO we now need to make an iteration here that case splits on the possiblec_orth being non zero 
                int iteration = 1;
                while (iteration < 2*(curBasis[0].size()-curBasis.size())){
                    write_gurobi_query_new(input, procEqual, Bounds, nm, modulos, curBasis, monomials, iteration);
                    auto result = std::make_shared<std::string>("");
                    std::shared_ptr<bool> done = std::make_shared<bool>(false);
                    std::mutex resultMutex;
                    auto future = std::async(std::launch::async, [&]() {
                    auto res = runGurobi(input);
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
                     coefficients = parseGlpkOutput(output);
                     if (coefficients.size() != 0){
                        break;
                    }
                    iteration +=1;
                //break;
            }
            }
            if (coefficients.size() == 0){
                break;
            }
            std::vector<Node> sum;
            //std::cout << coefficients.size() << "\n";
            for (int i=0; i<procEqual.size(); i++){
                //std::cout << procEqual[i] << "\n";
                Node tempResult =  nm->mkNode(Kind::MULT, procEqual[i], nm->mkConstInt(coefficients[i]));
                sum.push_back(rewrite(tempResult));       
            } 
            //std::cout << currBasis.size() << "\n";
            Node newEquality = rewrite(nm->mkNode(Kind::EQUAL, nm->mkNode(Kind::ADD, sum), nm->mkConstInt(0)));
            //std::cout << "But we did not get here\n";
            //std::cout << newEquality << "\n";
            AlwaysAssert(checkIfConstraintIsMet(newEquality, modulos, Bounds)) << "ILP produced nonliftable eq";
            //addEquality(newEquality, true, true);
            Integers.addEquality(newEquality, true);
            curBasis.push_back(getLastRow(rewrite(nm->mkNode(
                Kind::ADD, newEquality[0], rewrite(nm->mkNode( Kind::MULT, newEquality[1], 
                nm->mkConstInt(-1))))), monomialMap));
            //AlwaysAssert(curBasis.size() == curBasis[0].size()) << "getLastRow failed \n";
            //std::cout << newEquality << "\n";
            //AlwaysAssert(false);
        }

    return false;

}

bool Field::Simplify(IntegerField& Integers, std::map<std::string, std::pair<Integer, Integer> > Bounds, bool WeightedGB, int startLearningLemmas){
    NodeManager* nm = NodeManager::currentNM();
    //std::cout << "LIFTING FOR: " << modulos << "\n";
    if (equalities.size()>0 && newEqualitySinceGB){
         LiftViaILP(Integers, Bounds);
    }
    //Lift(Integers, Bounds,startLearningLemmas);
    if (newEqualitySinceGB && !ranGB && !GBTimedOut){
        if(!runGB(Bounds)){
            GBTimedOut = true;
        };
    }
    if (status == Result::UNSAT){
        return false;
    }
    if (newEqualitySinceGB && (inequalities.size()>0)){
    for(Node diseq: inequalities){
        //std::cout << diseq<< "\n";
        if (reduceAgainstGB(Bounds, diseq)){
            status = Result::UNSAT;
         }
    }
    }
    newEqualitySinceGB = false;
    //LiftViaILP(Integers, Bounds);


    // if (newEqualitySinceGB && (equalities.size()>1)){
    //     std::cout << "STARING GB IN FIELD\n";
    //     solver->totalGB+=1;
    //     std::vector<Node> newPoly = SimplifyViaGB(this, Bounds, nm, false);

    //     //TODO FOR LEGIBILITY THIS SHOULD BE SWAPPED 
    //      //std::cout << "Finished GB\n";
    //      //std::cout << newPoly.size() << "\n";
    //     if (newPoly.size() == 0 && equalities.size()!=0){
    //         //std::cout << equalities.size() << "\n";
    //         std::cout << "GB FAULT \n";
    //         status = Result::UNSAT;
    //         //AlwaysAssert(false);
    //         return false;
    //         //AlwaysAssert(false);
    //     }
    //    if (newPoly.size() != 0 && newPoly[0]== nm->mkConstInt(Integer(0))){
    //         return false;
    //         std::cout << "GB TOOK TOO LONG\n";
    //     }
    //     //std::cout <<  "Finished GB check\n";
    //     clearEqualities();
    //     //std::cout << newPoly.size() << "\n";
    //     bool complete = false;
    //     for (Node poly: newPoly){
    //         //std::cout << "New Poly F:" << poly << "\n";
    //         if (rewrite(poly).getKind() == Kind::CONST_BOOLEAN && 
    //             rewrite(poly).getConst<bool>() == false){
    //                  status = Result::UNSAT;
    //                  std::cout << modulos << "\n";
    //                  std::cout << "SOME ISSUE WE ARE NOT CATCHING\n";
    //                  //AlwaysAssert(lemmas.size()==0) << modulos;
    //                 return false;
    //         }
    //         // Here we should check if our theorem applies 
    //         if (!complete && !checkIfConstraintIsMet(rewrite(poly), modulos, Bounds)){
    //             if (poly[0].getKind() == Kind::ADD){
    //                 if (checkIfConstraintIsMet(poly[0][0], modulos, Bounds)){
    //                      complete = true;
    //                 }
    //             }

    //         }
    //         addEquality(rewrite(poly), false, true);
    //         //std::cout << "WHAT\n";
    //     }
    //     if (complete){
    //         solver->completeGB+=1;
    //     }

    //     newEqualitySinceGB = false;
        
    // }
   
    // if (status == Result::UNSAT){
    //     return false;
    // }
    //std::cout << "STARTING LIFTING GASP!\n";
    //Lift(Integers, Bounds,startLearningLemmas);
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
            integerField.addEquality(equalities[i], false);
        }
        else if(LearnLemmas == 2){
        // && LearntLemmasFrom.find(equalities[i])==LearntLemmasFrom.end()){
            ShouldLearnLemmas(equalities[i], Bounds);
            //LearntLemmasFrom.insert(equalities[i]);
        }
        else if(LearnLemmas == 3 && LearntLemmasFrom.find(equalities[i])==LearntLemmasFrom.end()
        && std::find((integerField.equalities).begin(), (integerField.equalities).end(), equalities[i]) == (integerField.equalities).end()
        && isIntersectionNotEmpty(getVarsHelper(equalities[i]), (*solver).myNotVars)){
        // && LearntLemmasFrom.find(equalities[i])==LearntLemmasFrom.end()){
            // std::cout << "TRY TO RANGE LIFT:" << equalities[i] << "for" << modulos<< "\n";
            // std::cout << equalities[i][1].getNumChildren()  << "\n";
            // std::cout <<  checkIfConstraintIsMet(equalities[i], modulos*2, Bounds) << "\n";
            if (equalities[i][1].getNumChildren() > 0 && checkIfConstraintIsMet(equalities[i], modulos*2, Bounds)){
                //std::cout << "RANGE LIFT:" << equalities[i] << " " << modulos << "\n";
                //AlwaysAssert(false);
                NodeManager* nm = NodeManager::currentNM();
                SkolemManager* sm = nm->getSkolemManager();
                Node sk = sm->mkDummySkolem("Q", nm->integerType());
                (*solver).myNodes.insert(sk);
                (*solver).myVariables[replaceDots(sk.getName())] = sk;
                lemmas.push_back(rewrite(nm->mkNode(Kind::EQUAL, equalities[i][0], 
                nm->mkNode(Kind::ADD, equalities[i][1],nm->mkNode(Kind::MULT, sk, nm->mkConstInt(Integer(modulos)))))));
                //BELOW IS LEMMAS THE OR VERSION
                (*solver).setTrivialConflict();
                Node conflict = nm->mkNode(Kind::AND, (*solver).d_conflict);
                //std::vector<Node> conflict2 = (*solver).d_conflict;
                //conflict1.push_back(nm->mkNode(Kind::EQUAL, sk, nm->mkConstInt(Integer(0))));
                //conflict2.push_back(nm->mkNode(Kind::EQUAL, sk, nm->mkConstInt(Integer(1))));
                 Node orStat = nm->mkNode(Kind::OR,
                                 nm->mkNode(Kind::EQUAL, sk, nm->mkConstInt(Integer(0))),
                                 nm->mkNode(Kind::EQUAL, sk, nm->mkConstInt(Integer(1))));
                lemmas.push_back(rewrite(orStat));
                lemmas.push_back(rewrite(nm->mkNode(Kind::LEQ, sk, nm->mkConstInt(Integer(1)))));
                lemmas.push_back(rewrite(nm->mkNode(Kind::GEQ, sk, nm->mkConstInt(Integer(0)))));
                //std::cout << "LOOOK HERE!!!" << sk.getName() << "\n";
                (*solver).Bounds[sk.getName()] = std::make_pair(0,2);
                LearntLemmasFrom.insert(equalities[i]);
                //std::cout << equalities.size() << "\n";
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
                modOut(rewrite(nm->mkNode(Kind::MULT, nm->mkConstInt(inv), equalities[i][0]))),
                modOut(rewrite(nm->mkNode(Kind::MULT, nm->mkConstInt(inv), equalities[i][1]))));
                //eq = modOut(rewrite(eq));
                if (checkIfConstraintIsMet(rewrite(eq), modulos, Bounds)){
                    //std::cout << "THIS ACTUALLY HELPED??\n";
                    integerField.addEquality(eq, false);
                }
                // std::cout << "AFTER" << eq << "\n";
                // std::cout << "AFTER" << rewrite(eq) << "\n";
                //if rewrite
                
                //Lift(rewrite(integerField, rewrite(eq), Bounds, LearnLemmas));
                //addEquality(eq, false, true);
                //td::cout << "AFTER" << equalities[i] << "\n";
                //AlwaysAssert(inv != 1);
                //i--;
            }
        }
     }
    // Can always lift inequalities
    for (int j=0; j<inequalities.size(); j++){
            //std::cout << "Adding inequality" << inequalities[j] << "\n";
            integerField.addInequality(inequalities[j]);
    }
   // std::cout << "HERE" << equalities.size() << "\n";
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
    :EnvObj(env), 
    integerField(env, this), 
    completeGB(statisticsRegistry().registerInt("theory::arith::modular::CompleteGBCalc", false)),
    totalGB(statisticsRegistry().registerInt("theory::arith::modular::totalGBCalc", false)),
    d_facts(context()) {}

void RangeSolver::preRegisterTerm(TNode node){ 
        //std::cout << node << "\n";
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
    if ( isVariableOrSkolem(node) ){
            // if (upperBounds.count(node.getName())==0){
            std::string singularName = replaceDots(node.getName());
            myVariables[singularName] = node;
            myNodes.insert(node);
            // }
           
            Bounds[node.getName()] = std::make_pair(Integer(-1) *BIGINT, BIGINT);
        }
      if (node.getKind() == Kind::CONST_INTEGER){
        if (node.getConst<Rational>() == Rational(0)){
            return;
        }
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
                 og_fields.insert(new_size);
                 if (fields.count(new_size) == 0) {
                fields.insert(std::make_pair(new_size, Field(d_env,new_size, this)));
            }
        }
      }
      return;
    }
}



void RangeSolver::notifyFact(TNode fact){
    d_facts.emplace_back(fact); 
}

void RangeSolver::processFact(TNode fact){
    NodeManager* nm = NodeManager::currentNM();
    if(fact.getKind() == Kind::GEQ && fact[0].getNumChildren()<=1){
        AlwaysAssert(fact[1].getKind()==Kind::CONST_INTEGER) << fact;
        Integer Bound = fact[1].getConst<Rational>().getNumerator();
        if (! isVariableOrSkolem(fact[0])){
            AlwaysAssert(false) << fact;
            }
            else {
            Bounds[fact[0].getName()].first = std::max({Bound, Bounds[fact[0].getName()].first});
            }
    }
    else if(fact.getKind() == Kind::GEQ && fact[0].getNumChildren()>1){
        if (fact[0].getKind() == Kind::MULT && 
            fact[0][0].getKind() == Kind::CONST_INTEGER &&
            fact[0][0].getConst<Rational>().getNumerator() == Integer(-1) &&
            isVariableOrSkolem(fact[0][1]) &&
            fact[1].getKind() == Kind::CONST_INTEGER){
            //std::cout << "PROCESSING" << fact << "\n";
            
            Integer Bound = Integer(-1) * fact[1].getConst<Rational>().getNumerator();
            Bounds[fact[0][1].getName()].second = std::min({Bound, Bounds[fact[0][1].getName()].second});
            }else {
            if (fact[1].getKind() == Kind::CONST_INTEGER){
                Integer Bound =  fact[1].getConst<Rational>().getNumerator();
                if (tempSkolemMap.find(fact[0])!= tempSkolemMap.end()){
                    Node sk = tempSkolemMap[fact[0]];
                    Bounds[sk.getName()].first = std::max(Bound,Bounds[sk.getName()].first );
                } else {
                SkolemManager* sm = nm->getSkolemManager();

                Node sk = sm->mkDummySkolem("Var", nm->integerType());
                Bounds[sk.getName()].first = Bound;
                Bounds[sk.getName()].second = BIGINT;
                Node new_node = nm->mkNode(Kind::EQUAL, sk, fact[0]);
                integerField.addEquality(new_node, true);
                std::string singularName = replaceDots(sk.getName());
                myVariables[singularName] = sk;
                myNodes.insert(sk);
                tempSkolemMap.insert(std::make_pair(fact[0], sk));
                }

            }
            else {
                AlwaysAssert(false) << "unsuppoirted case ";
            }

        }

            //AlwaysAssert(fact[1].getConst<Rational>().getNumerator() == Integer(0)) << fact;}
    }
    // (not X >= N)
    else if(fact.getKind() == Kind::NOT && fact[0].getKind()==Kind::GEQ){
            AlwaysAssert(fact[0][1].getKind()==Kind::CONST_INTEGER) << fact;
            Integer Bound = fact[0][1].getConst<Rational>().getNumerator()-1;
            //AlwaysAssert(Bound > 0) << fact;
            // (not -1*X >=N) --> -1*X < N --> X < N *-1
        if ( ! isVariableOrSkolem(fact[0][0]) ){

            if (fact[0][0].getKind() == Kind::MULT && 
                fact[0][0][0].getKind() == Kind::CONST_INTEGER && 
                fact[0][0][0].getConst<Rational>().getNumerator() == Integer(-1) && 
                isVariableOrSkolem(fact[0][0][1]) &&
                 fact[0][1].getKind() == Kind::CONST_INTEGER
                ){
                     Bound = Integer(-1) * Bound;
                    Bounds[fact[0][0][1].getName()].first = std::max({Bound, Bounds[fact[0][0][1].getName()].first}) ;

                }
            else {
                if (fact[0][1].getKind() == Kind::CONST_INTEGER){
                     //Integer Bound =  fact[0][1].getConst<Rational>().getNumerator();
                     if (tempSkolemMap.find(fact[0][0])!= tempSkolemMap.end()){
                        Node sk = tempSkolemMap[fact[0][0]];
                        Bounds[sk.getName()].second = std::min(Bound,Bounds[sk.getName()].second );
                    } else {
                     SkolemManager* sm = nm->getSkolemManager();
                     Node sk = sm->mkDummySkolem("Var", nm->integerType());
                     Bounds[sk.getName()].second = Bound;
                     Bounds[sk.getName()].first = Integer(-1) * BIGINT;
                     Node new_node = nm->mkNode(Kind::EQUAL, sk, fact[0][0]);
                     integerField.addEquality(new_node, true);
                     std::string singularName = replaceDots(sk.getName());
                     myVariables[singularName] = sk;
                     myNodes.insert(sk);
                    tempSkolemMap.insert(std::make_pair(fact[0][0], sk));
                    }

                } else {
                AlwaysAssert(false) << fact;
                }
            }
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
            Bounds[fact[0][0].getName()].second = std::min({Bound, Bounds[fact[0][0].getName()].second});
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
            integerField.addEquality(fact, true);
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
        //std::cout << "Not set up for this fact\n";
        AlwaysAssert(false);
    }
    //std::cout << "Done with fact\n";

}

void RangeSolver::setTrivialConflict()
{
  d_conflict.clear();
  std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
}

std::string findSmallestUpperBound(const std::map<std::string, std::pair<Integer, Integer>>& Bounds) {
    std::string result;
    Integer smallestUpperBound = std::numeric_limits<Integer>::max();

    for (const auto& entry : Bounds) {
        const std::string& key = entry.first;
        const Integer& upperBound = entry.second.second;

        if (upperBound < smallestUpperBound) {
            smallestUpperBound = upperBound;
            result = key;
        }
    }

    return result;
}

// getAssignedVariables(std::map<std::Node, Integer>& assignedVariables, std::vector<Node> equalities, std::map<std::string, std::pair<Integer, Integer> > Bounds ){
//     (for eq:equalities){
//         if (eq[0] == Kind::Var && eq[1] == Kind::CONST_INTEGER){
//             if Bounds[eq[0].getName()].first > eq[1] || 
//             assignedVariables[eq[0]] = eq[1];
//         }
//     }
// }

 

bool RangeSolver::addAssignment(Node asgn, Field *f){
    // std::cout << asgn << "\n";
    // std::cout << f->status << "\n";
    f->addEquality(asgn, true, true);
    // std::cout << f->status << "\n";
    f->Simplify(integerField, Bounds, false, 0);
    if (f->status == Result::UNSAT){
        //printSystemState();
        AlwaysAssert(false)<< "something bad with the model";
    }
    int count = 0;
     while(count < 3){
            //std::cout << count << "\n";
            for (auto& fieldPair :fields){
                fieldPair.second.Simplify(integerField, Bounds, false, 0);
                if (fieldPair.second.status == Result::UNSAT){
                        return false;
                    }
            }
            integerField.Simplify(fields, Bounds);
                if (integerField.status == Result::UNSAT){
                        //std::cout << "OH NO Integers!\n";
                    }
            count +=1;
     }
    return true; 

}


Result RangeSolver::Solve(){
    for (auto& fieldPair :fields){
            if (fieldPair.second.LearntLemmasFrom.size()!=0){
                AlwaysAssert(false);
            }
            fieldPair.second.LearntLemmasFrom.clear();
        }
    start:
    integerField.clearAll();
    tempSkolemMap.clear();
    integerField.status = Result::UNKNOWN;
    for(auto &f : fields){
        f.second.clearAll();
        f.second.status = Result::UNKNOWN;
    }
    //CLEAN BOUNDS HEARE
    for (auto &pair: Bounds){
        Bounds[pair.first]= std::make_pair(Integer(-1) *BIGINT, BIGINT);
    }
    for (auto fact:d_facts){
        processFact(fact);
        if (Bounds.find("") != Bounds.end()) {
            std::cout << fact << "\n";
            AlwaysAssert(false);
        }
    }
    // Check Bounds for incosinstency 
    for (auto &pair: Bounds){
        if (pair.first == ""){
            AlwaysAssert(false);
        }
        if (pair.second.first > pair.second.second){
            std::cout << "INITIAL BOUNDS WRONG\n";
            // std::cout << pair.first << "\n";
            return Result::UNSAT;
        }
    }
    std::vector<Node> newLemmas;
    for (auto fact:Lemmas){
        if (fact.getNumChildren()>0){
            if (fact.getKind() ==Kind::OR){
                processFact(fact[0]);
                for (int i =1; i<fact.getNumChildren(); i++){
                    newLemmas.push_back(fact[i]);
                }
            } else {
                processFact(fact);
            }

        } else {
            processFact(fact);
        }
    }
    Lemmas = newLemmas;
    int count = 0;
    bool WeightedGB = true;
    int startLearningLemmas = 0;
    for (auto& fieldPair :fields){
            fieldPair.second.newEqualitySinceGB = true;
            fieldPair.second.myNodes = myNodes;
            fieldPair.second.myVariables = myVariables;
            fieldPair.second.mySingularReduce = "";
        }
    bool movesExist = true;
    bool saturated;
    while(movesExist){
    //printSystemState();
    count+=1;
        for (auto& fieldPair :fields){
            fieldPair.second.Simplify(integerField, Bounds, WeightedGB, startLearningLemmas);
            if (fieldPair.second.status == Result::UNSAT && fieldPair.second.lemmas.size()== 0 && Lemmas.size()==0){
                std::cout << "LOOP COUNT" << count << "\n";
                return Result::UNSAT;
            }

        }
        //printSystemState();
        integerField.Simplify(fields, Bounds);
        if (integerField.status == Result::UNSAT){
            integerField.status = Result::UNKNOWN;
            std::cout << "LOOP COUNT" << count << "\n";
            //printSystemState();
            return Result::UNSAT;
        }
        //printSystemState();
    saturated = true;
        for (auto fieldPair :fields){
            if (fieldPair.second.status == Result::UNSAT){
                if (fieldPair.second.lemmas.size()> 0){
                    Lemmas.insert(Lemmas.end(), fieldPair.second.lemmas.begin(), fieldPair.second.lemmas.end());
                    fieldPair.second.lemmas.clear();
                    AlwaysAssert( fieldPair.second.lemmas.size()==0);
                    fieldPair.second.status = Result::UNKNOWN;
                    goto start;

                }
                if (Lemmas.size()> 0){
                    fieldPair.second.status = Result::UNKNOWN;
                    goto start;
                }
                fieldPair.second.status = Result::UNKNOWN;
                std::cout << "LOOP COUNT" << count << "\n";
                return Result::UNSAT;
            }
            if (fieldPair.second.newEqualitySinceGB == true){
                //std::cout << "not saturated b/c of GB\n";
                saturated = false;
                AlwaysAssert(!saturated);
            }
            if (integerField.novelBound == true){
                //std::cout << "not saturated b/c of INT Bound\n";
                saturated = false;
            }
            if (integerField.newEqualitySinceGB == true){
                //std::cout << "not saturated b/c of INT\n";
                saturated = false;
            }
        }
        if (saturated && startLearningLemmas == 2){
            startLearningLemmas = 3;
        }
        if (saturated && startLearningLemmas == 3){
            movesExist = false;
        }
        if (saturated && startLearningLemmas == 0){
            startLearningLemmas = 2;
        }
        }
        return Result::UNKNOWN;
    }


 std::vector<Node>& RangeSolver::conflict() {
    d_conflict.clear();
    std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
    return d_conflict;}

Result RangeSolver::postCheck(Theory::Effort level){
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
        std::cout << "equalities" <<  pair.second.equalities.size() << "\n";
         for (int i =0; i< pair.second.equalities.size(); i++) {
            std::cout << pair.second.equalities[i] << "\n";
        }
        std::cout << "inequalities" << "\n";
        //std::cout << pair.second.inequalities.size() << "\n";
        for (int i = 0; i<pair.second.inequalities.size(); i++) {
            std::cout << pair.second.inequalities[i]  << "\n";
        }
    }
    std::cout << "Bounds\n";
    for(auto i : Bounds){
        std::cout << "(" << i.first << "," << i.second  << ")\n";
    }
    std::cout << "DONE!" << "\n\n\n";
}

bool RangeSolver::collectModelInfo(TheoryModel* m,
                                            const std::set<Node>& termSet)
{
  NodeManager* nm = NodeManager::currentNM();
  // Assignments are stored in variablesValues so we add the last assignment
    for (Node node: myNodes){
        m->assertEquality(node, nm->mkConstInt(finalModel[node]), true);
    }   
  
   return true;
}



}
}
}
}
