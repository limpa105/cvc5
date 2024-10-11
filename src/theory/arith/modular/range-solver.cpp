

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

// Function to perform integer Gaussian elimination and return the rank of the matrix
int integerGaussianElimination(std::vector<std::vector<int>>& matrix, int n, int d) {
    int rank = 0;
    for (int col = 0; col < d; ++col) {
        // Find the pivot row in the current column
        int pivotRow = -1;
        for (int row = rank; row < n; ++row) {
            if (matrix[row][col] != 0) {
                pivotRow = row;
                break;
            }
        }
        // If no pivot is found, move to the next column
        if (pivotRow == -1) {
            continue;
        }

        // Swap the pivot row with the current row
        std::swap(matrix[rank], matrix[pivotRow]);

        // Normalize the pivot row by dividing by the GCD of the entire row
        int gcd = 0;
        for (int j = 0; j < d; ++j) {
            gcd = std::gcd(gcd, matrix[rank][j]);
        }
        if (gcd > 1) {
            for (int j = 0; j < d; ++j) {
                matrix[rank][j] /= gcd;
            }
        }

        // Ensure the leading coefficient is positive
        if (matrix[rank][col] < 0) {
            for (int j = 0; j < d; ++j) {
                matrix[rank][j] *= -1;
            }
        }

        // Eliminate the current column for all rows except the pivot row
        for (int row = 0; row < n; ++row) {
            if (row != rank && matrix[row][col] != 0) {
                int factor = matrix[row][col] / matrix[rank][col]; // Use integer division

                // Perform row operation: row = row - factor * pivot_row
                for (int j = 0; j < d; ++j) {
                    matrix[row][j] -= factor * matrix[rank][j];
                }

                // Normalize the row again to handle any common divisors introduced
                int rowGcd = 0;
                for (int j = 0; j < d; ++j) {
                    rowGcd = std::gcd(rowGcd, matrix[row][j]);
                }
                if (rowGcd > 1) {
                    for (int j = 0; j < d; ++j) {
                        matrix[row][j] /= rowGcd;
                    }
                }
            }
        }
        
        // Move to the next row
        ++rank;
    }

    return rank;
}

// Function to check if a vector is linearly independent from the current set of vectors
bool isLinearlyIndependent(const std::vector<std::vector<int>>& matrix, const std::vector<int>& vec, int n, int d, int rank) {
    // Create a copy of the matrix and add the new vector as a column
    std::vector<std::vector<int>> augmentedMatrix = matrix;
    augmentedMatrix.push_back(vec);

    // Perform Gaussian elimination again and check if the rank increases
    int newRank = integerGaussianElimination(augmentedMatrix, n + 1, d);

    return newRank > rank;  // If the rank increases, the vector is linearly independent
}

// Helper function to print the basis
void printBasis(const std::vector<std::vector<int>>& basis) {
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

std::vector<std::vector<int>> findBasis(const std::vector<std::vector<int>>& inputVectors) {
    int n = inputVectors.size();
    int d = inputVectors[0].size();  // Assuming all vectors have the same dimension

    // Copy the input vectors into a matrix
    std::vector<std::vector<int>> matrix = inputVectors;

    std::cout << "Original Basis\n";
    printBasis(inputVectors);
    std::cout << "No memeroy issues untill here?\n";

    // Perform integer Gaussian elimination on the matrix to get its rank
    int rank = integerGaussianElimination(matrix, n, d);
    AlwaysAssert(rank == n) << "rank:" << rank << " size" << n  ;
    std::cout << rank << "\n";

    // If we already have a full basis, return the input vectors
    if (rank == d) {
        return inputVectors;  // Already a full basis
    }
    std::cout << "Memeory issue = Gaussian elim\n";

    // Start with the original set of input vectors as the basis
    std::vector<std::vector<int>> basis = inputVectors;

    // Try to add standard basis vectors to complete the basis
    for (int i = 0; i < d; ++i) {
        std::vector<int> e_i(d, 0);
        e_i[i] = 1;  // e_i is the ith standard basis vector

        // Check if the standard basis vector is linearly independent
        if (isLinearlyIndependent(matrix, e_i, n, d, rank)) {
            ++rank;
            basis.push_back(e_i);
            matrix.push_back(e_i);  // Add the new vector to the matrix
            std::cout << "Added standard basis vector: ";
            for (auto j: e_i){
                std::cout << "," << j ;
            }
            std::cout << "\n";
            n +=1;
        } else {
            std::cout << "Did not add a vector";
            for (auto j: e_i){
                std::cout << "," << j;
            }
            std::cout << "\n";
        }
        std::cout << "Current rank: " << rank << std::endl;
        std::cout << "Current dim: " << d << std::endl;
        if (rank == d) {

            std::cout << "We exited early\n";
            break;  // Stop if we've found a full basis
        }
    }
    std::cout << "Memeory issue = adding stuff\n";

    return basis;
}



std::vector<int> parseGurobiOutput(const std::string& output) {
    // Check if the model is infeasible
    std::vector<int> variableMap;
    if (output.find("Model is infeasible") != std::string::npos) {
        std::cout << "No feasible solution found." << std::endl;
        return variableMap;
    }

    // Check if the model is optimal
    if (output.find("Optimal solution found") != std::string::npos) {

        // Find the section where the optimal solution is printed
        std::size_t start = output.find("Optimal solution:");
        if (start == std::string::npos) {
            std::cout << "No variable values found." << std::endl;
            return variableMap;
        }

        // Extract the part of the string that contains the variable values
        std::string variableSection = output.substr(start);

        // Refined regex: match variable names (e.g., alphanumeric names) and their values
        std::regex variableRegex(R"(([a-zA-Z_]\w*): (-?\d+\.?\d*))");
        std::smatch match;

        // Use regex to find variables and their values
        std::string::const_iterator searchStart(variableSection.cbegin());
        while (std::regex_search(searchStart, variableSection.cend(), match, variableRegex)) {
            std::string varName = match[1];
            int value = static_cast<int>(std::round(std::stod(match[2])));
            variableMap.push_back(value);

            // Move the search start to the next position
            searchStart = match.suffix().first;
        }

        // Print the map of variable names to their values
        // std::cout << "Variable to Value map:" << std::endl;
        // for (const auto& pair : variableMap) {
        //     std::cout << pair.first << ": " << pair.second << std::endl;
        // }
        return variableMap;
    }

    std::cout << "Unexpected output or status." << std::endl;
}

 void write_gurobi_query(const std::string& filename, std::vector<Node> equalities,
                        std::map<std::string, 
                        std::pair<Integer, Integer>>& bounds,
                        NodeManager* nm,
                        Integer modulos,
                        std::vector<std::vector<int>> pastSolutions) {
    std::map<std::string, std::vector<Node>> nonlinearMap;
    std::map<std::string, std::string> varCoefMap;
    std::vector<std::string> new_vars;
    std::map<std::string, std::pair<Integer, Integer>> nonlinearBounds;
    Integer addConst = Integer(0);
    std::ofstream file(filename);
    if (!file.is_open()) {
        std::cerr << "Error: Could not open the file for writing." << std::endl;
        AlwaysAssert(false);
        return;
    }  
    std::cout << "Writing to file: " << filename << std::endl;  // Debug print
    file << "#include \"/Library/gurobi1103/macos_universal2/include/gurobi_c++.h\"\n"
         << "#include <iostream>\n"
         << "int main() {\n"
         << "    GRBEnv env = GRBEnv();\n"
         << "    env.start();\n"
         << "    GRBModel model = GRBModel(&env);\n";
    for(int j = 0; j<equalities.size(); j++){
        new_vars.push_back("gb_"+ std::to_string(j));
    // Currently operating under the fact that the all the terms are of the form
    // + (*..) no pluses inside multiplication if this is not true need to through an 
    // error :) 
        // 
        for (auto eq: equalities[j]){
            std::cout << eq << "\n";
            // x = z this should become x + (-1) z = 0;
            Node node;
             for (int k = 0; k<=eq.getNumChildren(); k++) {
                if (k == eq.getNumChildren() && k!=0){
                     continue;
                 }
                // Node node;
                if (eq.getNumChildren() == 0){
                     node = eq;
                 } else {
                     node = eq[k];
                 }
            if (node.getKind() == Kind::CONST_INTEGER){
                if (node.getConst<Rational>().getNumerator().abs() <= 2){
                    addConst = node.getConst<Rational>().getNumerator();
                } else {
                    addConst = static_cast<int>(std::round(10*log2(node.getConst<Rational>().getNumerator().getDouble())));
                }
            }
            else if (node.getKind() == Kind::VARIABLE || node.getKind() == Kind::SKOLEM){
                if (varCoefMap.find(node.getName()) == varCoefMap.end()){
                    varCoefMap[node.getName()] =  new_vars[j];
                } else {
                    varCoefMap[node.getName()] += " + " + new_vars[j];
                }
            }
            else if (node.getKind() == Kind::MULT || node.getKind() == Kind::NONLINEAR_MULT){
                if (node.getNumChildren() == 2 && node[0].getKind() == Kind::CONST_INTEGER) {
                    if (node[0].getConst<Rational>().getNumerator().abs() <= 2){
                        addConst = node[0].getConst<Rational>().getNumerator();
                        std::cout << "ADDing" << addConst << "\n";
                    } else {
                        addConst = static_cast<int>(std::round(10*log2(node[0].getConst<Rational>().getNumerator().getDouble())));
                        std::cout << "ADDing" << addConst << "\n";
                    }
                    if (node[1].getKind() == Kind::NONLINEAR_MULT){
                        // case when we have multiplication of variables so need to make new variable
                        std::string name = "";
                        std::vector<Node> myNodes; 
                        Integer LB = 1;
                        Integer UB = 1;
                        for (int i = 0; i<node[1].getNumChildren(); i++) {
                            AlwaysAssert(node[1][i].getKind()==Kind::VARIABLE || node[1][i].getKind() == Kind::SKOLEM) << node[i];
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
                            varCoefMap[name] =addConst.toString() + " * " + new_vars[j];
                        } else {
                            varCoefMap[name] += " + " + addConst.toString() + " * " + new_vars[j];
                        }
                        nonlinearMap[name] = myNodes;
                        nonlinearBounds[name] = std::make_pair(LB, UB);
                        // we need to get the resulting lower and upper bounds,
                    } else { AlwaysAssert(node[1].getKind()==Kind::VARIABLE || node[1].getKind()==Kind::SKOLEM  ) << node[1] << "\n";
                    if (varCoefMap.find(node[1].getName()) == varCoefMap.end()){
                        varCoefMap[node[1].getName()] = addConst.toString() + " * " + new_vars[j];
                    } else {
                         varCoefMap[node[1].getName()] += " + "+  addConst.toString() + " * " + new_vars[j];
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
                            if (node[i].getConst<Rational>().getNumerator().abs() <= 2){
                                    addConst = node[i].getConst<Rational>().getNumerator();
                                    std::cout << "ADDing" << addConst << "\n";
                         } else {
                                addConst = static_cast<int>(std::round(10*log2(node[i].getConst<Rational>().getNumerator().getDouble())));
                                std::cout << "ADDing" << addConst << "\n";
                                }
                            if (addConst > 2000000000 || addConst < -2000000){
                                AlwaysAssert(false);
                            }
                            continue;
                        }
                        AlwaysAssert(node[i].getKind()==Kind::VARIABLE || node[i].getKind() == Kind::SKOLEM);
                        name += node[i].getName() + "_";
                        myNodes.push_back(node[i]);
                        Integer pos1 = LB * bounds[node[i].getName()].second;
                        Integer pos2 = UB * bounds[node[i].getName()].second;
                        Integer pos3 = LB * bounds[node[i].getName()].first;
                        Integer pos4 = LB * bounds[node[i].getName()].second;
                        LB = Integer::min(Integer::min(pos1,pos2), Integer::min(pos3,pos4));
                        UB = Integer::max(Integer::max(pos1,pos2), Integer::max(pos3,pos4));
                    }
                    if (addConst > 2000000000 || addConst < -2000000){
                        AlwaysAssert(false);
                    }
                     if (varCoefMap.find(name) == varCoefMap.end()){
                         varCoefMap[name] =addConst.toString() + " * " + new_vars[j];
                    } else {
                         varCoefMap[name] += " + " + addConst.toString() + " * " + new_vars[j];
                    }
                    nonlinearMap[name] = myNodes;
                    nonlinearBounds[name] = std::make_pair(LB, UB);
                }

            } else {
                AlwaysAssert(false) << node.getKind();
            }
        }
        }
    }
    // Okay now we have our data structures its time to write stuff :) 
    // First write in all the variables we made.
    
    for (const auto& var : new_vars) {
        file << "    GRBVar " << var << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << var << "\");" << std::endl;
    }
    std::map<std::string, std::string> pos_relu_vars;
    std::map<std::string, std::string> neg_relu_vars;
    std::map<std::string, std::string> neg_coefficients;
    std::map<std::string, std::string> pos_coefficients;
    for (const auto&  pair: varCoefMap) {
        pos_relu_vars[pair.first] = pair.first + "coef_pos_relu";
        neg_relu_vars[pair.first] = pair.first + "coef_neg_relu";
        neg_coefficients[pair.first] = pair.first + "neg_coef";
        pos_coefficients[pair.first] = pair.first + "pos_coef";
        file << "    GRBVar " << neg_coefficients[pair.first] << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << neg_coefficients[pair.first] << "\");" << std::endl;
        file << "    GRBVar " << pos_coefficients[pair.first] << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << pos_coefficients[pair.first] << "\");" << std::endl;
        file << "    GRBVar " << pos_relu_vars[pair.first] << " = model.addVar(0, GRB_INFINITY, 0.0, 'I', \"" << pos_relu_vars[pair.first] << "\");" << std::endl;
        file << "    GRBVar " << neg_relu_vars[pair.first] << " = model.addVar(0, GRB_INFINITY, 0.0, 'I', \"" << neg_relu_vars[pair.first]  << "\");" << std::endl;
        file << "    model.addConstr(" << pos_coefficients[pair.first] << " == "<< pair.second << ");" << std::endl;
        file << "    model.addGenConstrMax(" << pos_relu_vars[pair.first] << ", &" << pos_coefficients[pair.first] << ", 1, 0,\"max_const_" << pos_relu_vars[pair.first] << "\");" << std::endl;
        file << "    model.addConstr(" << neg_coefficients[pair.first] << " == -1 * ("<< pair.second << "));" << std::endl;
        file << "    model.addGenConstrMax(" << neg_relu_vars[pair.first] << ", &" << neg_coefficients[pair.first] << ", 1, 0, \"max_const_" << neg_relu_vars[pair.first] << "\");" << std::endl;
        
    }
    std::string upper_bound ="";
    std::string lower_bound ="";
    for (auto&  pair: varCoefMap) {
        Integer UB; 
        Integer LB;
        auto it = bounds.find(pair.first);
        if (it != bounds.end()) {
            //std::cout << it->first << "\n";
            //std::cout << (it->second.second).toString() << "\n";
            if ((it->second.first).abs() <= 2) {
                LB = it->second.first;
            } else {
            LB = static_cast<int>(std::round(10 * log2((it->second.first).getDouble())));
            }
            std::cout << it->second.first<< "turned into" <<  LB << "\n";
            if ( (it->second.second).abs() <= 2) {
                LB = it->second.second;
            } else {
            UB = static_cast<int>(std::round(10 * log2((it->second.second).getDouble())));
            }
            std::cout << it->second.second<< "turned into" <<  UB << "\n";
        } else {
            it = nonlinearBounds.find(pair.first);
            if (it != bounds.end()) {
            //std::cout << it->first << "\n";
            //std::cout << (it->second.second).toString() << "\n";
            if ((it->second.first).abs() <= 2) {
                LB = it->second.first;
            } else {
            LB = static_cast<int>(std::round(10 * log2((it->second.first).getDouble())));
            }
            std::cout << it->second.first<< "turned into" <<  LB << "\n";
            if ((it->second.second).abs() <= 2) {
                LB = it->second.second;
            } else {
            UB = static_cast<int>(std::round(10 * log2((it->second.second).getDouble())));
            }
            std::cout << it->second.second<< "turned into" <<  UB << "\n";
            } else {
                AlwaysAssert(false) << pair.first;
            }
        }
        //std::cout << UB.toString() << "\n";
        if (upper_bound.size() == 0){
            upper_bound = UB.toString() + " * " + pos_relu_vars[pair.first] + " - " + LB.toString() + " * " + neg_relu_vars[pair.first];
        } else {
            upper_bound += " + " + UB.toString() + " * " + pos_relu_vars[pair.first] + " - " + LB.toString() + " * " + neg_relu_vars[pair.first];
        }
        if (lower_bound.size() == 0){
            lower_bound = LB.toString() + " * " + pos_relu_vars[pair.first] + " - " + UB.toString() + " * " + neg_relu_vars[pair.first];
        } else {
            lower_bound += " + " + LB.toString() + " * " + pos_relu_vars[pair.first] + " - " + UB.toString() + " * " + neg_relu_vars[pair.first];
        }
    }
    file << "    model.addConstr(" << upper_bound << " <= " << static_cast<int>(std::round(10*log2(modulos.getDouble() -1))) <<  ");" << std::endl;
    file << "    model.addConstr(" << lower_bound << " >= " <<  "-1 * " << static_cast<int>(std::round(10*log2(modulos.getDouble() -1)))  << ");" << std::endl;
    std::string nonzero="";
    for (auto&  pair: varCoefMap) {
        if (nonzero.size()==0){
            nonzero = neg_relu_vars[pair.first] + " + " + pos_relu_vars[pair.first];
        } else {
            nonzero += " + " + neg_relu_vars[pair.first] + " + " + pos_relu_vars[pair.first];
        }
    }

    file << "    model.addConstr(" << nonzero << " >= 1);" << std::endl;

    if (pastSolutions.size()>0){
        std::vector<std::vector<int>> curBasis = findBasis(pastSolutions);
        std::cout << "So the issue is here?\n";
        printBasis(curBasis);
        AlwaysAssert(curBasis.size() == curBasis[0].size()) << curBasis.size() << " but " << curBasis[0].size();
        int n = pastSolutions.size();
        std::vector<std::string> c_old;
        std::vector<std::string> c_orth;
        std::vector<std::string> constraints;
        for(int i = 0;i <curBasis.size(); i++){
            constraints.push_back("");
            if (i < n){
                c_old.push_back("c_old" + std::to_string(i));
                file << "    GRBVar " << c_old.back() << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << c_old.back() << "\");" << std::endl;

            } else {
                c_orth.push_back("c_orth" + std::to_string(i));
                 file << "    GRBVar " << c_orth.back() << " = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, 'I', \"" << c_orth.back() << "\");" << std::endl;
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
                constraints[j] = cur_c + " * " + std::to_string(curBasis[i][j]);
            } else {
                 constraints[j] += " + " + cur_c + " * " + std::to_string(curBasis[i][j]);

            }
            }
        }
        for(int i = 0; i<constraints.size(); i++){
            file << "   model.addConstr(" << new_vars[i] << " == "  + constraints[i] + ");" << std::endl;
        }
        std::string nonzero_c = "";
        for(int i=0; i<c_orth.size(); i++){
            if (nonzero_c == ""){
                nonzero_c = c_orth[i];
            } else {
                nonzero_c += " + " + c_orth[i];
            }
        }
        file <<  "  model.addConstr(" + nonzero_c + " >= 1);" << std::endl;


    }
    std::cout << "We actually got here \n";
    file << "    model.optimize();" << std::endl;
    file << "    std::cout << \"Optimal solution:\" << std::endl;" << std::endl;
    for (const auto&  var: new_vars) {
        file  << "    std::cout << \"" << var << ": \" << " << var << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
    }
    //  for (const auto&  var: pos_coefficients) {
    //     file  << "    std::cout << \"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
    // }
    //  for (const auto&  var: neg_coefficients) {
    //     file  << "    std::cout << \"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
    // }
    //  for (const auto&  var: pos_relu_vars) {
    //     file  << "    std::cout << \"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
    // }
    //  for (const auto&  var: neg_relu_vars) {
    //     file  << "    std::cout << \"" << var.second << ": \" << " << var.second << ".get(GRB_DoubleAttr_X) << std::endl;" << std::endl;
    // }
    file << "    };" << std::endl;
    std::cout << "Sanity Check\n";
    std::cout << "Number of OG Variables:" << varCoefMap.size() << "\n";
    std::cout << "Number of New Variables:" << new_vars.size() << "\n";
    
   file.flush(); 
   file.close();

};
 
 
 
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
    for (const auto eq : equalities) {
        file << "(assert " << eq << ")\n";
    }
    file << "\n";
    // Write the inequalities
    for (const auto ineq : inequalities) {
        file << "(assert (not " << ineq << "))\n";
    }
    file << "\n";
    // Write bounds as inequalities
    for (const auto& bound : bounds) {
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
  int exitCode = std::system(command.c_str());
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
  //std::cout << program << "\n";
  std::filesystem::path output1 = tmpPath();
  std::filesystem::path output2 = tmpPath();
  std::cout << "Program is in " << filename << "\n";
  std::cout << "We will write it to " << output1 << "\n";
  std::cout << "And then compile it to " << output2 << "\n";
  //std::filesystem::path input = writeToTmpFile(program);

  std::stringstream commandStream;
  commandStream << "g++ " << filename <<  " -o " << output1 <<  " -I/Library/gurobi1103/macos_universal2/include -L/Library/gurobi1103/macos_universal2/lib /Library/gurobi1103/macos_universal2/lib/libgurobi110.dylib -lgurobi_c++";
  std::string command = commandStream.str();
  std::cout << command << "\n";
  int exitCode = std::system(command.c_str());
  Assert(exitCode == 0) << "Singular errored\nCommand: " << command;
  std::cout << "Compilation worked\n";
  exitCode = std::system(( output1.string() +  " >> " + output2.string()).c_str());
    std::cout << "Running the command worked\n";
  std::string outputContents = readFileToString(output2);
  std::cout << outputContents << "\n";
  Assert(outputContents.find(" error:") == std::string::npos) << "Gurobi error:\n"
                                                         << outputContents;
  std::filesystem::remove(output1);
  std::filesystem::remove(output2);
  std::filesystem::remove(filename);
  //std::filesystem::remove(input);
  //std::cout << outputContents << "\n";
  return outputContents;
}


bool isVariableOrSkolem(Node node) {
    return node.getKind() == Kind::VARIABLE || node.getKind() == Kind::SKOLEM;
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
    AlwaysAssert(false) << eq;
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

/////////////////////////////////////////////////// INTEGERFIELD ////////////////////////////////////////////////////////////////////

IntegerField::IntegerField(Env &env, RangeSolver* solver):EnvObj(env){this->solver = solver;};

bool IntegerField::Simplify(std::map<Integer, Field>& fields, std::map<std::string, std::pair<Integer, Integer> > Bounds){
    //std::cout << "STARTED INTEGERS\n";
    //CancelConstants();
    NodeManager* nm = NodeManager::currentNM();
    if (unlowerableIneq){
        std::cout << "COMPUTING GB IN THE INTEGERS WOOO!\n";
        std::vector<Node> newPoly = SimplifyViaGB(this, Bounds, nm, true);
        //     //TODO FOR LEGIBILITY THIS SHOULD BE SWAPPED 
        //      //std::cout << "Finished GB\n";
        //      //std::cout << newPoly.size() << "\n";
        if (newPoly.size() == 0 && equalities.size()!=0){
                //std::cout << equalities.size() << "\n";
                std::cout << "GB FAULT \n";
                status = Result::UNSAT;
                //AlwaysAssert(false);
                return false;
                //AlwaysAssert(false);
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
                        std::cout << "SOME ISSUE WE ARE NOT CATCHING\n";
                        //AlwaysAssert(lemmas.size()==0) << modulos;
                        return false;
                }
                addEquality(rewrite(poly));
            }
    }
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
    int nonLowCount = 0;
    for (auto& fieldPair : fields){
        //std::cout << "LOWERING\n";
        Lower(fieldPair.second,Bounds);
        //nonLowCount +=  static_cast<int>(unlowerableIneq);
        if (!unlowerableIneq){
            nonLowCount +=1;
        }
    }
    if(nonLowCount == 0){
        unlowerableIneq = true;
        }
    else{
        unlowerableIneq = false;
    }

    //std::cout << "FINISHED LOWERING\n" << unlowerableIneq << nonLowCount << "\n" ;
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
    if (fact.getKind() == Kind::CONST_BOOLEAN){
        if (fact.getConst<bool>() == false){
            status = Result::UNSAT;
            //std::cout << "WE ARE HERE TM\n";
        }
        return;
    } 
    if (inField && std::find(equalities.begin(), equalities.end(), fact) == equalities.end()
        && fact.getKind() != Kind::CONST_BOOLEAN && fact.getKind()!=Kind::NULL_EXPR
        //getVarsHelper(fact)
        ){
        AlwaysAssert(fact.getKind() == Kind::EQUAL) << fact;
        //GBAddition = true;
        if(!GBAddition){
            std::stringstream ss;
            ss.str("");
            ss.clear();
            NodeManager* nm = NodeManager::currentNM();
            ss << replaceDots(nodeToString(nm->mkNode(Kind::SUB, fact[0], fact[1])));
            if (mySingularReduce.empty()){
                newEqualitySinceGB = true;
                equalities.push_back(fact);
                return;
            }
            std::string line = mySingularReduce;
            line = ReplaceGBStringInput("{6}", line, ss);
            // std::cout << "About to run Singular\n";
            // std::cout << line << "\n";
            // std::cout << "running Singular\n";

             std::string output = "";
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
            // std::cout << "ran singular\n";
            size_t pos =output.find('\n');
            std::string myResult = output.substr(pos + 1);
            //std::cout << line <<"\n";
            //std::cout << output << "\n" ;
            try{
            if (std::stoi(myResult) == 0){
                return;
            }
            } catch (const std::invalid_argument& e) { 
                //std::cout << output << "\n";
                newEqualitySinceGB = true;
                equalities.push_back(fact);
                //std::cout << "For:" << modulos << "\n";
                return;
            } catch (const std::out_of_range& e) { 
                //std::cout << output << "\n"; 
                newEqualitySinceGB = true;
                equalities.push_back(fact);
                //std::cout << "For2:" << modulos << "\n";
                return;
            };
            //AlwaysAssert(false) << result;
            newEqualitySinceGB = true;
            equalities.push_back(fact);
             //std::cout << "NEW EQUALITY" << fact << "for" << modulos << "\n";
            ALLequalities.push_back(fact);

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
    NodeManager* nm = NodeManager::currentNM();
    // if (didGurobi< 2 &&  startLearningLemmas == 20 && equalities.size() > 1){
    //     bool gurobiNew = true;
    //     std::vector<std::vector<int>> curBasis;
    //     std::string output; 
    //     std::vector<int> coefficients;
    //     std::vector<Node> procEqual;
    //     for (auto i: equalities){
    //         procEqual.push_back(nm->mkNode(
    //             Kind::ADD, i[0], rewrite(nm->mkNode( Kind::MULT, i[1], 
    //             nm->mkConstInt(-1)))));
    //     }
    //     while(gurobiNew) {
    //         std::filesystem::path input = tmpPath();
    //         std::filesystem::remove(input);
    //         input = input.concat(".cpp");
    //         write_gurobi_query(input, procEqual, Bounds, nm, modulos, curBasis);
    //         output = runGurobi(input);
    //         coefficients = parseGurobiOutput(output);
    //         if (coefficients.size() == 0){
    //             gurobiNew = false; 
    //             break;
    //         }
    //         std::vector<Node> sum;
    //         std::cout << coefficients.size() << "\n";
    //         for (int i=0; i<procEqual.size(); i++){
    //             Node result =  nm->mkNode(Kind::MULT, procEqual[i], nm->mkConstInt(coefficients[i]));
    //             std::cout << result << "\n";
    //             sum.push_back(rewrite(result));
                    
    //         } 
    //         curBasis.push_back(coefficients);
    //         if (curBasis.size() == curBasis[0].size()){
    //             gurobiNew = false; 
    //             break;
    //         }
    //         addEquality(rewrite(nm->mkNode(Kind::EQUAL, nm->mkNode(Kind::ADD, sum), nm->mkConstInt(0))), false, true);
    //     }
    //     //AlwaysAssert(false);
    //     didGurobi +=1;
        
        
    // //     // std::cout << curBasis.size() << "\n";
    // //     // std::cout << curBasis[0].size() << "\n";
    // //     // std::vector<std::vector<int>> finalBasis = findBasis(curBasis);
    // //     // std::cout << finalBasis.size() << "\n";
    // //    //printBasis(finalBasis);
        
    // //     //PAUSE HERE 
    //  } 
    

    //std::cout << "Starting field simplifcation \n";
    // for (int i =0; i< equalities.size(); i++) {
    //         //std::cout << equalities[i] << "\n";
    //     }
    //std::cout << equalities.size() << "\n";
    //Lift(Integers, Bounds,startLearningLemmas);
    //std::cout << equalities.size() << "\n";
    //substituteVariables();
    //std::cout << equalities.size() << "\n";
    //std::cout << "finished sub\n";
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
    Lift(Integers, Bounds,startLearningLemmas);
    solver->printSystemState();
    //AlwaysAssert(false);
    //substituteVariables();
    //std::cout << "Substitute Vars done \n";
    //substituteEqualities();
    //std::cout << "Substitute Eqs done \n";
    //std::cout << "Checking Unsat is done \n";
    if (status == Result::UNSAT){
        return false;
    }
    //std::cout << "Finished UNSAT\n";
    
    if (newEqualitySinceGB ){
        //std::cout << "STARING GB\n";
        std::vector<Node> newPoly = SimplifyViaGB(this, Bounds, nm, false);
        //TODO FOR LEGIBILITY THIS SHOULD BE SWAPPED 
         //std::cout << "Finished GB\n";
         //std::cout << newPoly.size() << "\n";
        if (newPoly.size() == 0 && equalities.size()!=0){
            //std::cout << equalities.size() << "\n";
            std::cout << "GB FAULT \n";
            status = Result::UNSAT;
            //AlwaysAssert(false);
            return false;
            //AlwaysAssert(false);
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
                     std::cout << modulos << "\n";
                     std::cout << "SOME ISSUE WE ARE NOT CATCHING\n";
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
                std::cout << "LOOOK HERE!!!" << sk.getName() << "\n";
                for (auto& item : LearntLemmasFrom) {
                    std::cout << item << " ";
                }
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
                //std::cout << "INV:" << inv << "\n";
                //std::cout << "BEFORE" << equalities[i] << "\n";
                NodeManager* nm = NodeManager::currentNM();
                Node eq = nm->mkNode(Kind::
                EQUAL,
                modOut(rewrite(nm->mkNode(Kind::MULT, nm->mkConstInt(inv), equalities[i][0]))),
                modOut(rewrite(nm->mkNode(Kind::MULT, nm->mkConstInt(inv), equalities[i][1]))));
                //eq = modOut(rewrite(eq));
                if (checkIfConstraintIsMet(rewrite(eq), modulos, Bounds)){
                    integerField.addEquality(eq);
                }
                //std::cout << "AFTER" << eq << "\n";
                //std::cout << "AFTER" << rewrite(eq) << "\n";
                //if rewrite
                
                //Lift(rewrite(integerField, rewrite(eq), Bounds, LearnLemmas));
                //addEquality(eq, false, true);
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
   // std::cout << "HERE" << equalities.size() << "\n";
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
                Node newfact = rewrite(subVarHelper(equalities[j], equalities[i][0], equalities[i][1]));  
                if (newfact.getKind()!= Kind::CONST_BOOLEAN){
                    equalities[i] == newfact;
                }
                else {
                    if (newfact.getConst<bool>()== false){
                        status == Result::UNSAT;
                    } else {
                        equalities.erase(equalities.begin()+j);
                        j--;
                    }
                }

                //std::cout << "OLD:" << equalities[j] << "\n";  
                //equalities[j] = subVarHelper(equalities[j], equalities[i][0], equalities[i][1]);   
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
    if (equalities.size() <= 0){ 
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
                Node newfact = rewrite(subVarHelper(equalities[j], equalities[i][0], equalities[i][1]));  
                if (newfact.getKind()!= Kind::CONST_BOOLEAN){
                    equalities[i] = newfact;
                }
                else {
                    if (newfact.getConst<bool>()== false){
                        status = Result::UNSAT;
                    } else {
                        equalities.erase(equalities.begin()+j);
                        j--;
                    }
                }
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
    :EnvObj(env), integerField(env, this), d_facts(context()){}

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
    if (node.getKind() == Kind::VARIABLE ){
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
    //std::cout << fact << "\n";
    NodeManager* nm = NodeManager::currentNM();
    if(fact.getKind() == Kind::GEQ && fact[0].getNumChildren()<=1){
        AlwaysAssert(fact[1].getKind()==Kind::CONST_INTEGER) << fact;
        Integer Bound = fact[1].getConst<Rational>().getNumerator();
        if (! isVariableOrSkolem(fact[0])){
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
            if (fact[0][0].getKind() == Kind::MULT && 
                fact[0][0][0].getKind() == Kind::CONST_INTEGER && 
                fact[0][0][0].getConst<Rational>().getNumerator() == Integer(-1) && 
                fact[0][0][1].getKind() == Kind::VARIABLE &&
                 fact[0][1].getKind() == Kind::CONST_INTEGER
                ){
                    Integer Bound = Integer(-1) * fact[0][0][0].getConst<Rational>().getNumerator();
                    Bounds[fact[0][0][1].getName()].first = Bound;

                }
            else {
                if (fact[0][1].getKind() == Kind::CONST_INTEGER){
                     Integer Bound =  fact[0][1].getConst<Rational>().getNumerator();
                     NodeManager* nm = NodeManager::currentNM();
                     SkolemManager* sm = nm->getSkolemManager();
                     Node sk = sm->mkDummySkolem("Var", nm->integerType());
                     Bounds[sk.getName()].second = Bound-1;
                     Node new_node = nm->mkNode(Kind::EQUAL, sk, fact[0][0]);
                     integerField.addEquality(new_node);
                     std::string singularName = replaceDots(sk.getName());
                     myVariables[singularName] = sk;
                     myNodes.insert(sk);

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

 std::map<Node, Integer>  RangeSolver::getPossibleAssignment(Field* f, std::map<std::string, std::pair<Integer, Integer> > Bounds, NodeManager* nm ){
    std::map<Node, Integer> assignedVariables;
    std::vector<Node> oldEqualities;
    std::vector<std::pair<std::string, std::pair<Integer, Integer>>> sortedBounds(Bounds.begin(), Bounds.end());
    // Step 1: Learn which variables have already been assigned 
    std::set<std::string> currentVariables = getVars(f->equalities);
    for (auto eq: f->equalities){
        if (eq[0].getKind() == Kind::VARIABLE && eq[1].getKind() == Kind::CONST_INTEGER){
            Integer num = eq[1].getConst<Rational>().getNumerator().floorDivideRemainder(f->modulos);
            if (Bounds[eq[0].getName()].first > num || Bounds[eq[0].getName()].second < num ) {
                AlwaysAssert(false) << "The field was already UNSAT this should not happen\n";
            }
            assignedVariables[eq[0]] = num;
        }
    }
   

    // Step 2: Sort the vector by the upper bound (second element of the pair)
    std::sort(sortedBounds.begin(), sortedBounds.end(), [](const auto& lhs, const auto& rhs) {
        return lhs.second.second < rhs.second.second; // Compare upper bounds
    });

    for (const auto& entry : sortedBounds) {
         std::cout << "ASSIGNED VARIABLES\n";
     for (const auto& pair : assignedVariables) {
        const Node& node = pair.first;
        const Integer& value = pair.second;

        std::cout << "Node: " << node.getName() << ", Value: " << value << std::endl;
    }

        std::cout << entry.first << ": (" << entry.second.first << ", " << entry.second.second << ")" << std::endl;
        if (assignedVariables.find(myVariables[replaceDots(entry.first)]) != assignedVariables.end()) {
            std::cout << "Variable already assigned\n";
            continue;
        }
        if (currentVariables.find(entry.first) == currentVariables.end()) {
            std::cout << "Variable not present in the equation\n";
            continue;
        }
        Integer low_val = 0;
        Integer high_val = entry.second.second;
        bool toggle = true;
        Integer pos_val;

        while (low_val <= high_val){
            start_loop:
            pos_val = toggle ? low_val : high_val; // Alternate between low and high values
            toggle = !toggle; 
            if (toggle) {
                low_val+=1; // Increment low_val after using it
            } else {
                high_val-=1; // Decrement high_val after using it
            }
            oldEqualities = f->equalities;
            std::cout << "Trying:" << pos_val << std::endl;
            std::cout << f->status << "\n";
            std::cout << entry.first << "\n";

                std::cout << "MY VARIABLES\n";
     for (const auto& pair : myVariables) {
        //const Node& node = pair.first;
       // const Integer& value = pair.second;

        std::cout << pair.first << " : " << pair.second << std::endl;
    }

            //std::cout << myVariables[entry.first] << "\n";
             // get the Node variable and try adding to the ring
            f->addEquality(nm->mkNode(Kind::EQUAL, myVariables[replaceDots(entry.first)], nm->mkConstInt(pos_val)), false, true);
            std::vector<Node> newPoly = SimplifyViaGB(f, Bounds, nm, true);
            //TODO FOR LEGIBILITY THIS SHOULD BE SWAPPED 
            //std::cout << "Finished GB\n";
            //std::cout << newPoly.size() << "\n";
            if (newPoly.size() == 0){
                std::cout << "Bad Assignment \n";
                for(auto i: f->equalities){
                    std::cout << i << "\n";
                }
                pos_val +=1;
                f->equalities = oldEqualities;
                goto start_loop;
            }
            if (newPoly.size() != 0 && newPoly[0]== nm->mkConstInt(Integer(0))){
                 std::cout << "GB TOOK TOO LONG\n";
                 AlwaysAssert(false) << "No clue what to do here :(";
            }
            for (auto h: newPoly){
                Node eq = rewrite(h);
                std::cout << eq << "\n";
                if (eq[0].getKind() == Kind::VARIABLE && eq[1].getKind() == Kind::CONST_INTEGER){
                    Integer num = eq[1].getConst<Rational>().getNumerator().floorDivideRemainder(f->modulos);
                    if (Bounds[eq[0].getName()].first > num || Bounds[eq[0].getName()].second < num ) {
                        std::cout << "BOUNDS VIOLATED BADDD \n";
                        printSystemState();
                        std::cout << eq << "\n";
                        pos_val +=1;
                        f->equalities = oldEqualities;
                        goto start_loop;
                    }
                assignedVariables[eq[0]] = num;
                f->addEquality(eq, false, true);
                }
            }
        break; 
        }
    }
     std::cout << "We got here!\n";
     printSystemState();
     return assignedVariables;
 }


bool RangeSolver::addAssignment(Node asgn, Field *f){
    std::cout << asgn << "\n";
    std::cout << f->status << "\n";
    f->addEquality(asgn, true, true);
    std::cout << f->status << "\n";
    f->Simplify(integerField, Bounds, false, 0);
    if (f->status == Result::UNSAT){
        //printSystemState();
        AlwaysAssert(false)<< "something bad with the model";
    }
    int count = 0;
     while(count < 3){
            std::cout << count << "\n";
            for (auto& fieldPair :fields){
                fieldPair.second.Simplify(integerField, Bounds, false, 0);
                if (fieldPair.second.status == Result::UNSAT){
                        return false;
                    }
            }
            integerField.Simplify(fields, Bounds);
                if (integerField.status == Result::UNSAT){
                        std::cout << "OH NO Integers!\n";
                    }
            count +=1;
     }
    return true; 

}


Result RangeSolver::Solve(){
    #ifdef CVC5_USE_COCOA
    #else 
        noCoCoALiza();
    #endif
    for (auto& fieldPair :fields){
            fieldPair.second.LearntLemmasFrom.clear();
            //fieldPair.second.myNodes = myNodes;
            //fieldPair.second.myVariables = myVariables;
        }
    start:
    
    integerField.clearAll();
    for(auto &f : fields){
        f.second.clearAll();
    }
    for (auto fact:d_facts){
        processFact(fact);
    }
    std::vector<Node> newLemmas;
    for (auto fact:Lemmas){
        if (fact.getNumChildren()>0){
            if (fact.getKind() ==Kind::OR){
                processFact(fact[0]);
                newLemmas.push_back(fact[1]);
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
    //std::cout<< "START\n";
    //printSystemState();
    bool saturated;
    while(movesExist){
        //std::cout << "FINISHED ROUND" << count << "\n";
        printSystemState();
        
        // //std::cout << count << "\n";
    // if (count==0){
    //   AlwaysAssert(false);
    //  }
    //count+=1;
    std::cout << count << "\n";
    //   if (count >=2){
    //      AlwaysAssert(false);    
    //     }
    count+=1;
    
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
        //printSystemState();
        //std::cout << "FINISHED INTEGERS\n";
        for (auto& fieldPair :fields){
            //printSystemState();
            //std::cout << fieldPair.second.equalities.size() << "\n";
            fieldPair.second.Simplify(integerField, Bounds, WeightedGB, startLearningLemmas);
            if (fieldPair.second.status == Result::UNSAT && fieldPair.second.lemmas.size()== 0 && Lemmas.size()==0){
                printSystemState();
                return Result::UNSAT;
            }

        }
        integerField.Simplify(fields, Bounds);
        if (integerField.status == Result::UNSAT){
            integerField.status = Result::UNKNOWN;
            printSystemState();
            return Result::UNSAT;
        }
        //std::cout << "FINISHED FIELDS\n";
    saturated = true;
        for (auto fieldPair :fields){
            if (fieldPair.second.status == Result::UNSAT){
                // std::cout << "WE HERE\n";
                // std::cout << Lemmas.size() << "\n";
                d_conflict.clear();
                if (fieldPair.second.lemmas.size()> 0){
                    Lemmas.insert(Lemmas.end(), fieldPair.second.lemmas.begin(), fieldPair.second.lemmas.end());
                    //std::cout << "LEARNED NEW LEMMA" << Lemma << "\n";
                    fieldPair.second.lemmas.clear();
                    AlwaysAssert( fieldPair.second.lemmas.size()==0);
                    fieldPair.second.status = Result::UNKNOWN;
                    //fieldPair.second.LearntLemmasFrom.clear();
                    goto start;
                    //return Result::UNKNOWN;

                }
                if (Lemmas.size()> 0){
                    fieldPair.second.status = Result::UNKNOWN;
                    goto start;
                }
                //std::cout << "UNSAT\n";
                //printSystemState();
                fieldPair.second.status = Result::UNKNOWN;
                printSystemState();
                return Result::UNSAT;
            }
            if (fieldPair.second.newEqualitySinceGB == true){
                saturated = false;
                //std::cout << "NOT SATURATED:" << fieldPair.second.modulos << "\n";
                AlwaysAssert(!saturated);
            }
        }
        //std::cout << "Saturation status:" << saturated << "\n";
        if (saturated && startLearningLemmas == 2){
            //std::cout << "GB SATURATED NOTHING TO DO\n";
            startLearningLemmas = 3;
        }
        if (saturated && startLearningLemmas == 2){
            std::cout << "GB SATURATED NOTHING TO DO\n";
            movesExist = false;
        }
        if (saturated && startLearningLemmas == 1){
            std::cout << "Changed starting lemmas to Gurobi\n";
            startLearningLemmas  = 2;
        }
        // if (saturated && startLearningLemmas == 1.5){
        //     std::cout << "Changed starting lemmas to RangeLiftEq\n";
        //     startLearningLemmas  = 2;
        // }
        // // if (saturated && startLearningLemmas){
        // //         //AlwaysAssert(false) << "GB SATURATED NOTHING TO DO\n";
        // //    WeightedGB = false ;
        // // }
        if (saturated && startLearningLemmas == 0){
            std::cout << "Changed starting lemmas to LearnLemmas\n";
            ///movesExist = false;
            startLearningLemmas = 1;
        }
        //     startLearningLemmas = true;
        //      //AlwaysAssert(false);
        // }
    
        //   if (integerField.status == Result::SAT){
        //         //std::cout << "WE GOT SAT\n";
        //     return Result::SAT;
         //count +=1;
        }
        //AlwaysAssert(false);

       //Now we need to go back to the ST procedure from finite fields 
        //printSystemState();
        // step 0: only get the og fields 
        AlwaysAssert(false) << "Could not determine UNSAT :)";
        std::cout << "OG FIELD SIZE:" << og_fields.size() << "\n";
        std::map<Integer, Field*> myFields;
        for (auto i: og_fields){
            auto it = fields.find(i);
                if (it != fields.end()) {
                myFields.insert(std::make_pair(i, &it->second));
                } else {
                    // Handle the case where 'i' is not in 'fields'
                std::cerr << "Key not found in fields: " << i << std::endl;
                }
        }
        // for (const auto& entry : Bounds) {
        //         Integer i = entry.second.second;
        //         auto it = fields.find(i);
        //          if (it != fields.end()) {
        //         myFields.insert(std::make_pair(i, &it->second));
        //         } else {
        //             // Handle the case where 'i' is not in 'fields'
        //         }
        // }
        bool sat = false;

        auto it = myFields.end();
         --it;
        while (true){
        
        //step 1: find the largest field in the map
        // std::cout << "we are here" << myFields.size()<< "\n";
        //auto it = myFields.begin(); // reverse iterator to the last element of the map
         Field* smallestRing = it->second; 
        std::cout << "NEW RING TM\n";
        std::cout << smallestRing->modulos << "\n";
        NodeManager* nm = NodeManager::currentNM();
    //     if (!(smallestRing->modulos).isProbablePrime()){
    //         std::cout << smallestRing->modulos << "is NOT Prime \n";
    //         --it;
    //         continue;
    //    }
         if (smallestRing->equalities.size()==0){
         if (it == myFields.begin()) {
            break; // We are at the first element, stop the loop
        }
        --it;
         
        continue;
       }
       std::map<Node, Integer> assign = getPossibleAssignment(smallestRing, Bounds, nm);
       smallestRing->status = Result::UNKNOWN;

    //     CocoaEncoder enc = CocoaEncoder(smallestRing->modulos);
    //     std::cout << "stuck\n";
    //     CoCoA::ideal myIdeal = getCocoaGB(smallestRing, enc,nm);
    //     std::cout << "We got ideal\n";
    //      if (CoCoA::IsZeroDim(myIdeal)){
    //         std::cout << "WE HAVE ZERO DIMENSION" << smallestRing-> modulos << "\n";
    //      } else {
    //            std::cout << "Not zero dimension" << smallestRing-> modulos << "\n";
    //      }
    //     //  ++it;
    //     //  continue;
    //    }


        // std::cout<< "END\n";
        // //printSystemState();
        // //step 2: compute an ideal for said field using CoCoA
        // std::cout << "Why is this not working";
        // CocoaEncoder enc = CocoaEncoder(smallestRing->modulos);
        // CoCoA::ideal myIdeal = getCocoaGB(smallestRing, enc,nm);
        // std::cout << "Got cocoa Ideal\n";

        //  std::vector<CoCoA::RingElem> root;
        // //AlwaysAssert(false);
        // //step 3: run the applyZero from finite fields 
        //  try {
        // // Your code that might throw CoCoA::ErrorInfo
        // // For example, calling the findZero function
        // std::cout << "finding zero\n";
        // root = theory::ff::findZero(myIdeal);
        // } catch (const CoCoA::ErrorInfo& e) {
        // std::cerr << "Caught CoCoA::ErrorInfo exception: " << e << std::endl;
        // } catch (const std::exception& e) {
        //  AlwaysAssert(false);
        // std::cerr << "Caught standard exception: " << e.what() << std::endl;
        // } catch (...) {
        //  AlwaysAssert(false);
        // std::cerr << "Caught unknown exception." << std::endl;
        // }
        // //AlwaysAssert(false)
        // std::cout << "Zero found?\n";
        // std::cout << root.size() << "\n";
        // std::cout << root[0] << "\n";
        // std::cout << "Zero found?\n";

        //   if (root.empty())
        //   {

        //     std::cout << "um awkard...\n";
        //     // UNSAT
        //     setTrivialConflict();
        //     return Result::UNSAT;
        //   }
        //   else
        //   {
        //     std::cout << "Wow we are here?\n";
            std::unordered_map<Node, Integer> model;
            // First we need to save the state of the old system just in case we need to go back to it 
             for (auto &f: fields){
                    f.second.old_equalities = f.second.equalities;
                    f.second.old_inequalities = f.second.inequalities;
                }
                integerField.old_equalities = integerField.equalities;
                integerField.old_inequalities = integerField.inequalities;
            // Now we get the model and add it to the smallest field 
             size_t index = 0;
            // std::cout << (enc.getCurVars()) << "\n";
            sat = true;
            for (auto pair: assign)
            {
                
                Node node = pair.first;
                Integer literal = pair.second;
            
                if (!addAssignment(nm->mkNode(Kind::EQUAL, node,  nm->mkConstInt(literal)), smallestRing)){
                    sat = false;
                    break;
                }
                index+=1;
            } 
            // Then do the simplification for loop
            int count = 0; 
            std::cout << "starting simplification?\n";
            std::optional<Field*> unsatField; 
            for (auto &f: fields){
                if (f.second.status == Result::UNSAT) {
                    unsatField = &f.second;
                }
            }
            //printSystemState();Theorem
            std::cout << "Finished simplification\n"; 
            if (unsatField.has_value()){
                std::cout << "YIKES\n";
                printSystemState();
                std::cout << unsatField.value()->modulos << "\n";
                AlwaysAssert(false);



                // Integer g;
                // Integer u;
                // Integer v;
                // Integer::extendedGcd(g,u,v, smallestRing->modulos, (unsatField.value())->modulos);
                // std::cout << g << "\n";
                // std::vector<Node> newEqs;
                // if (g == Integer(1)){
                //     //printSystemState();
                //     std::vector<Polynomial> BasisA = computeSingularGB(smallestRing, Bounds, nm);
                //     std::vector<Polynomial> BasisB = computeSingularGB(unsatField.value(), Bounds, nm);
                //     for (Polynomial a: BasisA){
                //         for (Polynomial b: BasisB) {
                //             Node LHS_coef = rewrite(nm->mkConstInt(u * smallestRing->modulos* a.lc()));
                //             Node LHS = rewrite(nm->mkNode(Kind::MULT, monomialToNode((a.lm().lcm(b.lm()))/b.lm(), nm, smallestRing), LHS_coef, polynomialToNode(b, nm, smallestRing)));
                //             Node RHS_coef = rewrite(nm-> mkConstInt(v * unsatField.value()->modulos * b.lc()));
                //             Node RHS = rewrite(nm->mkNode(Kind::MULT, monomialToNode((a.lm().lcm(b.lm()))/a.lm(), nm, smallestRing), RHS_coef, polynomialToNode(a, nm, smallestRing)));
                //             newEqs.push_back(nm->mkNode(Kind::EQUAL, nm->mkNode(Kind::ADD, LHS, RHS), nm->mkConstInt(Integer(0))));
                //         }
                //     }
                     
                // } else {
                //     std::cout << "Something went wrong here\n";
                //     std::cout << g << "\n";
                //     std::cout << unsatField.value()->modulos << "\n";
                //     std::cout << smallestRing->modulos << "\n";
                //     AlwaysAssert(false);
                // }
                // std::cout << "LOOK HERE\n";
                // std::cout << smallestRing->modulos << "\n";
                // std::cout << unsatField.value()->modulos << "\n";
                // std::cout << smallestRing->modulos*unsatField.value()->modulos << "\n";
                // Field combo = Field(d_env, smallestRing->modulos*unsatField.value()->modulos, this);
                // for (Node eq: newEqs){
                //     std::cout << "NEWEQ:" << eq << "\n";
                //     combo.addEquality(eq, false, true);
                // }
                // //std::cout << myFields.size() << "\n";
                // myFields.erase(it);
                // auto it2 = myFields.find(unsatField.value()->modulos);
                //     if (it2 != myFields.end()) {
                //         myFields.erase(it2);
                // }
                // fields.insert(std::make_pair(combo.modulos, combo));
                // std::cout << "Adding" << combo.modulos << "\n";
                // myFields.insert(std::make_pair(combo.modulos, &combo));
                // //printSystemState();
                // it = myFields.begin();
            } else {
                std::cout << "UNSAT FIELD HAD NO VALUE\n";
                printSystemState();
                if (it == myFields.begin()) {
                break; // We are at the first element, stop the loop
                 }
                --it;
                //myFields.erase(myFields.begin());
            }
               

            std::cout << "This worked!\n";
               
            //std::cout << "We go here?\n";  
        }
         NodeManager* nm = NodeManager::currentNM();
        // We are at the point where each field has its own assignment but are all these assignments working with each other?
        for (auto &f: myFields){
            std::set<std::string> EqVars = getVars(f.second->equalities);
            std::set<std::string> NeqVars = getVars(f.second->inequalities);
            bool isSubset = std::includes(EqVars.begin(), EqVars.end(), NeqVars.begin(), NeqVars.end());
            if (isSubset){
                std::cout << "This field is SAT" << f.second->modulos << "\n";
                f.second->status = Result::SAT;
                for (Node eq: f.second->equalities){
                    if (Bounds[eq[0].getName()].second > f.second->modulos){
                        std::cout << eq << "We found an unliftable assignment yikes\n";
                        SkolemManager* sm = nm->getSkolemManager();
                        Node sk = sm->mkDummySkolem("C", nm->integerType());
                        Node lifted = nm->mkNode(Kind::EQUAL, eq[0], nm->mkNode(Kind::ADD, eq[1],
                        nm->mkNode(Kind::MULT, sk, nm->mkConstInt(f.second->modulos))));
                        Bounds[sk.getName()] = std::make_pair(Integer(-1) *BIGINT, BIGINT);
                        integerField.addEquality(lifted);
                        //integerField.Simplify();
                        //AlwaysAssert(false);  
                    }

                }
                //Node addition = nm->mkNode()
                // if the field is SAT then we have to lift all its assignments so we iterate through 
                // the assignments and if the bounds are too big then idk what to do because then the variables
                // can be set to different things in different fields... ugh this is confusing... 
                
            } else {
                std::cout << "This field is UNKNOWN" << f.second->modulos << "\n";
            }
            
        }
        write_smt_query("test.smt2",integerField.equalities, integerField.inequalities, Bounds);
        std::string output = runcvc5("test.smt2");
        parse_cvc5_output(output);
        return Result::SAT;
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


 std::vector<Node>& RangeSolver::conflict() {

    d_conflict.clear();
    std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
    return d_conflict;}

Result RangeSolver::postCheck(Theory::Effort level){
    //AlwaysAssert(false);
    //std::cout << level << "\n";
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

void RangeSolver::parse_cvc5_output(const std::string& cvc5_output) {
    std::istringstream stream(cvc5_output);
    std::string line;
    // Read the cvc5 output line by line
    while (std::getline(stream, line)) {
        // Check if the line contains "define-fun"
        if (line.find("(define-fun") != std::string::npos) {
            std::istringstream line_stream(line);
            std::string ignore, var_name, ignore_type;
            std::string value_str;


            // Extract the variable name and value from the line
            line_stream >> ignore >> var_name >> ignore_type >> ignore >> value_str;

            // Create the Node for the variable
            Node var_node = myVariables[var_name];
            value_str = value_str.substr(0, value_str.find(")"));

            std::cout << "we get here" << value_str << "\n";
            // Create the Integer for the value (handle large numbers)
            Integer value = Integer(value_str);

            std::cout << "we don't get here\n";

            // Insert the Node and Integer into the finalModel map
            finalModel[var_node] = value;
        }
    }
}



}
}
}
}
