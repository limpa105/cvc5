


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
//#include "theory/arith/modular/int_cocoa_encoder.h"
#include "theory/arith/modular/range-solver.h"
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
//#include "theory/arith/modular/singular_encoder.h"
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
// #include <CoCoA/library.H>





using namespace cvc5::internal::kind;

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


std::optional<std::pair<Integer,Integer>> getBounds(Node fact, Integer new_field, std::map<std::string, Integer > upperBounds){
    //Variable;
    if (isVariableOrSkolem(fact)) {
        if (upperBounds.find(fact.getName())!= upperBounds.end()){
            std::optional<Integer> answer = upperBounds[fact.getName()] -Integer(1);
            // ASSUMING BOUNDS CAN"T BE NEGATIVE THIS IS THEORETICALLY WRONG!!!!
            return std::make_pair(answer.value(), Integer(0));
         }
        return {};
    }
    // Constant
    if (fact.getKind() == Kind::CONST_INTEGER){
        Integer coef = fact.getConst<Rational>().getNumerator();
        if (new_field.divides(coef)){
            return std::make_pair(Integer(0), Integer(0));
        }
        if (coef > 0){
            return std::make_pair(coef, Integer(0));
        }
        return std::make_pair(Integer(0), coef);
    }
    // Multiplication
    if (fact.getKind() == Kind::MULT || fact.getKind()== Kind::NONLINEAR_MULT){
        Integer pos_product = Integer(1);
        Integer neg_product = Integer(1);
        for (int i=0; i<fact.getNumChildren(); i++){
            std::optional<std::pair<Integer, Integer>> result = getBounds(fact[i], new_field, upperBounds);
            if (result.has_value()){
                pos_product = pos_product*result.value().first;
                neg_product = neg_product*result.value().second;
            }
            else {
                return {};
            }
        }
        return std::make_pair(pos_product, neg_product);
    }
    AlwaysAssert(fact.getKind() == Kind::ADD) << fact;
    Integer pos_sum = Integer(0);
    Integer neg_sum = Integer(0);
    for (int i=0; i<fact.getNumChildren(); i++){
        auto result = getBounds(fact[i], new_field, upperBounds);
        if (result.has_value()){
            pos_sum +=result.value().first;
            neg_sum +=result.value().second;
        }
        else {
        return {};
        }
    }
    return std::make_pair(pos_sum, neg_sum);
}

std::set<Node> getVarsHelper(Node eq){
    std::set<Node> answer;
    if (eq.getKind() == Kind::CONST_INTEGER){
        return answer;;
    }
     if (isVariableOrSkolem(eq)){
        answer.insert(eq);
        return answer;
    }
    if (eq.getNumChildren() > 1){
        for (int i =0; i<eq.getNumChildren(); i++){
        std::set<Node> moreVars = getVarsHelper(eq[i]);
        answer.insert(moreVars.begin(), moreVars.end());
        }
        return answer;       
    }
    AlwaysAssert(false) << eq;
}


std::set<Node> getVars(std::vector<Node> eqs){
    std::set<Node> answer;
    for (auto eq: eqs){
        std::set<Node> moreVars = getVarsHelper(eq);
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

// TODO: Need to find max by iterating through equations.
std::vector<long> getWeights(std::vector<Node> variables, std::map<std::string, Integer > upperBounds){
    std::vector<long> answer;
    for (auto i: variables){
        // std::ostringstream oss;
        // oss << i;
        // std::string symbol = d_symNodes[oss.str()].getName();
        std::string symbol= i.getName();
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
        
        
        if (upperBounds.find(symbol)!= upperBounds.end()){
            long result = 10*log2(upperBounds[symbol].getDouble());
            //std::cout << result << "\n";
            answer.push_back(long(result));
        }
        else {
            AlwaysAssert(false);
            if(symbol.find("Q_HOLDER") != std::string::npos){
                answer.push_back(2);
                upperBounds[symbol] = 2;
            } else {
            //std::cout << oss.str() << "\n";
            AlwaysAssert(false) << symbol << "has no bound??";
            float result = BIGINTLOG;
            //std::cout << "NOBOUND" << result << "\n";
            answer.push_back(long(result));
            }
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
        AlwaysAssert(false);
    }
    return input;
}


std::vector<Node> SimplifyViaGB(Field *F, std::map<std::string, Integer > upperBounds, NodeManager* nm, bool WeightedGB){
      if ((*F).equalities.size() <= 1) {
        return (*F).equalities;
      }
    std::vector<long> weights = getWeights((*F).myNodes, upperBounds);
    std::ifstream inputFile("example.txt");

    // Check if the file was successfully opened
    if (!inputFile.is_open()) {
        AlwaysAssert(false) << "Singular GB input file does not exist";
    }
    // Read and print the contents of the file
    std::string line;
    std::getline(inputFile, line);
    inputFile.close();
    std::stringstream ss;
    ss << (*F).modulos;
    line = ReplaceGBStringInput("{1}", line, ss);
    ss.clear();
    ss << (*F).myNodes;
    line = ReplaceGBStringInput("{2}", line, ss);
    ss.clear();
    std::cout << line << "\n";
    AlwaysAssert(false);
    


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


bool checkIfConstraintIsMet(Node equality, Integer modulos, std::map<std::string, Integer > upperBounds){
    if (auto LHS  = getBounds(equality[0], modulos, upperBounds) ){
        //std::cout << LHS.value() << "\n";
       // std::cout << modulos << "\n";
        if (LHS.value().first >= modulos){
            return false;
        }
        if (LHS.value().second *-1 >= modulos){
            return false;
        }
    } else {
        return false;
    }
    if (auto RHS  = getBounds(equality[1], modulos, upperBounds) ){
        if (RHS.value().first >= modulos){
            return false;
        }
        if (RHS.value().second*-1 >= modulos){
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

bool IntegerField::Simplify(std::map<Integer, Field>& fields, std::map<std::string, Integer > upperBounds){
    //std::cout << "STARTED INTEGERS\n";
    //CancelConstants();
    NodeManager* nm = NodeManager::currentNM();
    checkUnsat();
    if (status == Result::UNSAT){
        return false;
    }
    //std::vector<Node> newPoly =  SimplifyViaGB(equalities, BIGINT, upperBounds, nm);
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
        Lower(fieldPair.second,upperBounds);
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
void IntegerField::Lower(Field& field, std::map<std::string, Integer > upperBounds){
    for (int i=0; i<equalities.size(); i++){
            field.addEquality(equalities[i], false);
// Need to check if can lower 
       // for (int i=processedInEqualitiesIndex; i<inequalities.size(); i++){
            //if (checkIfConstraintIsMet(inequalities[i], field.modulos, upperBounds)){
                //field.addInequality(inequalities[i]);
            //}
        //}

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


Field::Field(Env & env, Integer mod):EnvObj(env){
    modulos = mod;
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
        if (! (new_value < 0 && new_value > modulos * -1)){
        new_value =new_value.floorDivideRemainder(modulos);
        }
        if (( new_value >= modulos.floorDivideQuotient(2)) && new_value * -1 <= modulos ){
             new_value =  new_value- modulos;
        }
        //std::cout << "After mod:" << modulos << "\n";
        if(modulos.divides(new_value)){
            return nm->mkConstInt(0);
        }
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


void Field::addEquality(Node fact, bool inField){
    //std::cout <<"Adding equality:" << fact << "\n";
    fact = rewrite(fact); 
    if (fact.getKind() == Kind::CONST_BOOLEAN){
        AlwaysAssert(false) << fact;
    } 
    if (std::find(equalities.begin(), equalities.end(), fact) == equalities.end()
        && fact.getKind() != Kind::CONST_BOOLEAN && fact.getKind()!=Kind::NULL_EXPR){
            newEqualitySinceGB = true;
        AlwaysAssert(fact.getKind() == Kind::EQUAL) << fact;
        if(inField){
            equalities.push_back(fact);
        return;
    } else {
    //std::cout << "BEFORE" << fact << "\n";
    NodeManager* nm = NodeManager::currentNM();
    Node LHS = modOut(fact[0]);
    Node RHS = modOut(fact[1]);
    //std::cout << "LHS:" << LHS << "\n";
    //std::cout << "RHS:" << RHS << "\n";
    Node result = nm->mkNode(Kind::EQUAL, LHS, RHS);
    //std::cout << "result" << result << "\n";
    //std::cout << rewrite(result) << "\n";
   // std::cout << "CHECK END\n";
   //std::cout << "After" << result << "\n";
    addEquality(result, true);
    return;
    }
    }
    //std::cout << "Already existed\n";
    //std::cout <<"Done adding equality:" << fact << "\n";
};

bool Field::LearnLemmas(Node fact,std::map<std::string, Integer > upperBounds ){
    if (fact[0].getKind() == Kind::VARIABLE
    && fact[1].getKind() == Kind::FINITE_FIELD_MULT
    && fact[1][0].getKind() == Kind::VARIABLE
    && fact[1][1].getKind() == Kind::VARIABLE
    && fact[0].getName() == fact[1][0].getName()
    && fact[0].getName() == fact[1][1].getName()
    & modulos.isProbablePrime()) {
        NodeManager* nm = NodeManager::currentNM();
        lemmas.push_back(nm->mkNode(Kind::OR,
        nm->mkNode(Kind::EQUAL, fact[0], nm->mkConst(FiniteFieldValue::mkZero(fact[0].getType().getFfSize()) )),
        nm->mkNode(Kind::EQUAL, fact[0], nm->mkConst(FiniteFieldValue::mkOne(fact[0].getType().getFfSize()) ))));
        status = Result::UNSAT;
        return true;
    }
    if (fact[1].getKind() == Kind::VARIABLE
    && fact[0].getKind() == Kind::FINITE_FIELD_MULT
    && fact[0][0].getKind() == Kind::VARIABLE
    && fact[0][1].getKind() == Kind::VARIABLE
    && fact[1].getName() == fact[0][0].getName()
    && fact[1].getName() == fact[0][1].getName()
    & modulos.isProbablePrime()) {
        NodeManager* nm = NodeManager::currentNM();
        lemmas.push_back(nm->mkNode(Kind::OR,
        nm->mkNode(Kind::EQUAL, fact[1], nm->mkConst(FiniteFieldValue::mkZero(fact[0].getType().getFfSize()) )),
        nm->mkNode(Kind::EQUAL, fact[1], nm->mkConst(FiniteFieldValue::mkOne(fact[0].getType().getFfSize()) ))));
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
    NodeManager* nm = NodeManager::currentNM();
    Node LHS = modOut(fact[0]);
    Node RHS = modOut(fact[1]);
    Node result = rewrite(nm->mkNode(Kind::EQUAL, LHS, RHS));
    if (std::find(inequalities.begin(), inequalities.end(), result) == inequalities.end()){
    inequalities.push_back(result);
    }
};


bool Field::Simplify(IntegerField& Integers, std::map<std::string, Integer > upperBounds, bool WeightedGB, bool startLearningLemmas){
    std::cout << "Starting field simplifcation \n";
    // for (int i =0; i< equalities.size(); i++) {
    //         //std::cout << equalities[i] << "\n";
    //     }
    
    substituteVariables();
    std::cout << "finished sub\n";
    //std::cout << "Started UNSAT\n";
    // std::cout << "equalities\n";
    //  for (auto i: equalities) {
    //     std::cout << i << "\n";
    // }
    // std::cout << "inequalities:" << "\n";
    // for (auto i: inequalities) {
    //     std::cout << i << "\n";
    // }
    checkUnsat();
    //std::cout << "Finished UNSAT\n";
    if (status == Result::UNSAT){
        return false;
    }
    NodeManager* nm = NodeManager::currentNM();
    newEqualitySinceGB = true;
    if (newEqualitySinceGB){
        //std::cout << "STARING GB\n";
        std::vector<Node> newPoly = SimplifyViaGB(this, upperBounds, nm, WeightedGB);
        if (newPoly.size() == 0 && equalities.size()!=0){
            //std::cout << equalities.size() << "\n";
            //std::cout << "BAD BAD BAD\n";
            for(auto i : equalities){
                //std::cout << i << "\n";
            }
            std::cout << "GB FAULT \n";
            status = Result::UNSAT;
            return false;
        }
        //std::cout <<  "Finished GB\n";
        clearEqualities();
        for (Node poly: newPoly){
            // std::cout << "New Poly F:" << poly << "\n";
            // std::cout << "New Poly F:" << rewrite(poly) << "\n";
            addEquality(rewrite(poly), false);
            //std::cout << "WHAT\n";
        }
        // std::cout << "MOD:" << modulos << "\n";
        // std::cout << "Equalities\n";
        // for(auto i : equalities){
        //     std::cout << i << "\n";
        // }
        // std::cout << equalities.size() << "\n";
        // std::cout << newPoly.size() << "\n";
        //AlwaysAssert(equalities.size() == newPoly.size());
        newEqualitySinceGB = false;
        for (auto i: equalities){
        //     std::cout << i << "\n";
        // if (LearnLemmas(i, upperBounds)){
        //     std::cout << "OH NO" << "\n";
        //     return false;
        // }
        }
    }
    //std::cout << "ADDED ALL EQUALITIES FOR FIELDS\n";
    //std::cout << "SIZE" << equalities.size() << "\n";
    //substituteVariables();
    //std::cout << "Substitute Vars done \n";
    //substituteEqualities();
    //std::cout << "Substitute Eqs done \n";
    //std::cout << "Checking Unsat is done \n";
    //std::cout << "STARTING LIFTING GASP!\n";
    Lift(Integers, upperBounds,startLearningLemmas);
    return true;
};


void Field::Lift(IntegerField& integerField, std::map<std::string, Integer> upperBounds, bool LearnLemmas){
     for (int i=0; i<equalities.size(); i++){
        if (checkIfConstraintIsMet(equalities[i], modulos, upperBounds)){
            integerField.addEquality(equalities[i]);
        }
        else if(LearnLemmas && LearntLemmasFrom.find(equalities[i])==LearntLemmasFrom.end()){
            // TODO THIS IS WRONG THINK ABOUT THIS AND FIX THIS 
            if (checkIfConstraintIsMet(equalities[i], modulos*2, upperBounds)){
                NodeManager* nm = NodeManager::currentNM();
                SkolemManager* sm = nm->getSkolemManager();
                Node sk = sm->mkDummySkolem("Q_HOLDER", nm->integerType());
                lemmas.push_back(rewrite(nm->mkNode(Kind::EQUAL, equalities[i][0], 
                nm->mkNode(Kind::ADD, equalities[i][1],nm->mkNode(Kind::MULT, sk, nm->mkConstInt(Integer(modulos)))))));
                lemmas.push_back(rewrite(nm->mkNode(Kind::OR,
                                nm->mkNode(Kind::EQUAL, sk, nm->mkConstInt(Integer(0))),
                                 nm->mkNode(Kind::EQUAL, sk, nm->mkConstInt(Integer(1))))));
            //std::cout << "LOOOK HERE!!!" << sk.getName() << "\n";
                upperBounds[sk.getName()] = 2;
                LearntLemmasFrom.insert(equalities[i]);
                status = Result::UNSAT;
                return;
            }
        }
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

void Field::substituteVariables(){
    if (equalities.size() == 0 || inequalities.size() == 0){
        return;
    }
//std::cout << "Substitute variables\n";
    for (int i = 0; i<equalities.size(); i++){
        Node fact = equalities[i];
        //std::cout << "We are here?" << fact << "\n";
    if ( (isVariableOrSkolem(fact[0]) 
        //&&  isVariableOrSkolem(fact[1]) )|| 
       //(isVariableOrSkolem(fact[0]) && 
        //fact[1].getKind() == Kind::CONST_INTEGER
        )){
        std::vector<Node> new_inequalities;
            for(Node assert: inequalities){
                if (assert!=fact){
                //      std::cout << "STARTING";
                //      std::cout << "EQ:" << fact << "\n";
                //      std::cout << "INEQ:" << assert << "\n";
                Node new_ineq = subVarHelper(assert, fact[0], fact[1]);
                // std::cout << "NEW INEQ:" << new_ineq << "\n";
                 new_ineq = rewrite(new_ineq);
                // std::cout << "NEW INEQ REWRITE:" << new_ineq << "\n";
                if(new_ineq.getKind() == Kind::CONST_BOOLEAN){
                    if (new_ineq.getConst<bool>() == false){
                        //  std::cout << "INEQ"<< assert << "\n";
                        //  std::cout << "FACT" << fact << "\n";
                        // AlwaysAssert(false);
                        // new_inequalities.push_back(assert);
                    }
                    if (new_ineq.getConst<bool>() == true){
                        // std::cout << "SUB VARS\n";
                        // std::cout << assert << "\n";
                        // std::cout << fact << "\n";
                        status = Result::UNSAT;
                        return;
                    }
                } else {
                new_inequalities.push_back(new_ineq);}
                }
            }
        // if (isVariableOrSkolem(fact[1])){
        //             Node new_ineq = rewrite(subVarHelper(assert, fact[1], fact[0]));
        //         if(new_ineq.getKind() == Kind::CONST_BOOLEAN){
        //             if (new_ineq.getConst<bool>() == false){
        //                 // std::cout << "OH NO!!!!!"  << "\n";
        //                 // std::cout << fact << "\n";
        //                 // std::cout << assert << "\n";
        //                 AlwaysAssert(false);
        //                  new_inequalities.push_back(assert);
        //             }
        //             if (new_ineq.getConst<bool>() == true){
        //                 std::cout << "SUB VARS\n";
        //                 std::cout << assert << "\n";
        //                 std::cout << fact << "\n";
        //                  status = Result::UNSAT;
        //                 return;
        //             }
        //         } else {
        //         new_inequalities.push_back(new_ineq);}
        //         }
        //         } else {
        //             status = Result::UNSAT;
        //             return;
        //         }
        //     }
        //clearInequalities();
        for(auto j:new_inequalities){
            addInequality(j);
        }
    }
    if  (isVariableOrSkolem(fact[1]) && !isVariableOrSkolem(fact[0])){
        std::vector<Node> new_inequalities;
            for(Node assert: inequalities){
                if (assert!=fact){
                std::cout << "Sub var\n";
                Node new_ineq = subVarHelper(assert, fact[1], fact[0]);
                std::cout << "End Sub var\n";
                if(new_ineq.getKind() == Kind::CONST_BOOLEAN){
                    if (new_ineq.getConst<bool>() == false){
                    }
                    if (new_ineq.getConst<bool>() == true){
                        // std::cout << "SUB VARS\n";
                        // std::cout << assert << "\n";
                        // std::cout << fact << "\n";
                         status = Result::UNSAT;
                        return;
                    }
                } else {
                new_inequalities.push_back(new_ineq);}
                } else {
                    // std::cout << "SUB VARS\n";
                    // std::cout << assert << "\n";
                    // std::cout << fact << "\n";
                    status = Result::UNSAT;
                    return;
                }
            }
        //clearInequalities();
        for(auto j:new_inequalities){
            addInequality(j);
        }

    }
    }
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
            upperBounds[node.getName()] = BIGINT;
            if (myVariables.count(node) == 0){
            myVariables[node] = myNodes.size();
            myNodes.push_back(node);
        }
      if (node.getKind() == Kind::CONST_INTEGER){
        Integer constant = node.getConst<Rational>().getNumerator();
        if (constant < 0){constant = constant * -1;};
        if (constant == 0 || constant == 1 ){
            return;
        }
        else if (fields.count(constant)==0){
            fields.insert(std::make_pair(constant, Field(d_env,constant)));
      } } else {
        if (node.getKind() == Kind::EQUAL) {
            if (node[0].getKind() == Kind::INTS_MODULUS || node[0].getKind() == Kind::INTS_MODULUS_TOTAL){
                Integer new_size = node[0][1].getConst<Rational>().getNumerator();
                 if (fields.count(new_size) == 0) {
                fields.insert(std::make_pair(new_size, Field(d_env,new_size)));
            }
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
    if(fact.getKind() == Kind::GEQ){
            //AlwaysAssert(fact[1].getConst<Rational>().getNumerator() == Integer(0)) << fact;}
    }
    else if(fact.getKind() == Kind::NOT && fact[0].getKind()==Kind::GEQ){
            AlwaysAssert(fact[0][1].getKind()==Kind::CONST_INTEGER) << fact;
            Integer Bound = fact[0][1].getConst<Rational>().getNumerator();
            AlwaysAssert(Bound > 0) << fact;
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
            upperBounds[fact[0][0].getName()] = Bound;
            }
        }
    else if (fact.getKind() == Kind::EQUAL) {
        if (fact[0].getKind() == Kind::INTS_MODULUS || fact[0].getKind() == Kind::INTS_MODULUS_TOTAL){
            Integer size = fact[0][1].getConst<Rational>().getNumerator();
            auto it = fields.find(size);
            if (it != fields.end()) {
            //std::cout << "Adding Equality\n";
             it->second.addEquality(
                nm->mkNode(Kind::EQUAL, fact[0][0], nm->mkConstInt(0)), false);
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
        if (fact[0][0].getKind() == Kind::INTS_MODULUS || fact[0][0].getKind() == Kind::INTS_MODULUS_TOTAL){
            Integer size = fact[0][0][1].getConst<Rational>().getNumerator();
            auto it = fields.find(size);
            if (it != fields.end()) {
            //std::cout << "Adding Equality\n";
             it->second.addInequality(nm->mkNode(Kind::EQUAL, fact[0][0][0], nm->mkConstInt(0)));
            } else {;
            AlwaysAssert(false) << fact;
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


Result RangeSolver::Solve(){
    #ifdef CVC5_USE_COCOA
    #else 
        noCoCoALiza();
    #endif
    //std::cout << "We are here\n";
    int count = 0;
    bool WeightedGB = true;
    startLearningLemmas = false;
    while(true){
        count +=1;
        // if (count>2){
        //     AlwaysAssert(false);
        // }
          if (count >=10){
             WeightedGB = false;
          }
          if (count >=15){
            startLearningLemmas = true;
          }
          if (count >=20){
            AlwaysAssert(false);
          }
        printSystemState();
        integerField.Simplify(fields, upperBounds);
        if (integerField.status == Result::UNSAT){
            integerField.status = Result::UNKNOWN;
            return Result::UNSAT;
        }
        //std::cout << "FINISHED INTEGERS\n";
        for (auto& fieldPair :fields){
            fieldPair.second.Simplify(integerField, upperBounds, WeightedGB, startLearningLemmas);
        }
        //std::cout << "FINISHED FIELDS\n";
        for (auto fieldPair :fields){
            if (fieldPair.second.status == Result::UNSAT){
                if (fieldPair.second.lemmas.size()> 0){
                    Lemmas = fieldPair.second.lemmas;
                    //std::cout << "LEARNED NEW LEMMA" << Lemma << "\n";
                    fieldPair.second.lemmas.clear();
                    AlwaysAssert( fieldPair.second.lemmas.size()==0);
                    fieldPair.second.status = Result::UNKNOWN;
                    return Result::UNKNOWN;

                }
                //std::cout << "UNSAT\n";
                printSystemState();
                fieldPair.second.status = Result::UNKNOWN;
                return Result::UNSAT;
            }
            if (integerField.status == Result::SAT){
            //std::cout << "WE GOT SAT\n";
            return Result::SAT;
            }

        }
        count +=1;
    }
};

 std::vector<Node>& RangeSolver::conflict() {

    d_conflict.clear();
    std::copy(d_facts.begin(), d_facts.end(), std::back_inserter(d_conflict));
    return d_conflict;}

Result RangeSolver::postCheck(Theory::Effort level){
    
    integerField.clearAll();
    for(auto &f : fields){
        f.second.clearAll();
    }
    for (auto fact:d_facts){
        processFact(fact);
    }
    std::cout << level << "\n";
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
    std::cout << "Upper Bounds";
    for(auto i : upperBounds){
        std::cout << "(" << i.first << "," << i.second  << ")\n";
    }
    std::cout << "DONE!" << "\n\n\n";
}




}
}
}
}
