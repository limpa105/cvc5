


#include "theory/ff/range_solver_ff.h"
#include <cerrno>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <unordered_map>
#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "smt/env_obj.h"
#include "theory/ff/cocoa_encoder.h"
#include "theory/ff/core.h"
#include "theory/ff/multi_roots.h"
#include "theory/ff/split_gb.h"
#include "util/cocoa_globals.h"
#include "util/finite_field_value.h"
#include <typeinfo>
#include <utility>
#include <algorithm>
#include "util/result.h"
#include "util/statistics_registry.h"
#include "util/utility.h"
#include <cmath>
#include <CoCoA/BigInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/RingQQ.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/ring.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/PolyRing.H>
#include <CoCoA/library.H>

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace ff {

/////////////////////////////////////////////////// UTILS ////////////////////////////////////////////////////////////////////

 Integer BIGINT = Integer("26697537170649044179042152467634255803129704511815242562837925141177577913409118302943186911045680008195241138225131464058766427708039764790250144472755736885526820882067462431042573357558604819957849");

 long BIGINTLOG = 10 * log2(BIGINT.getDouble());

std::optional<Integer> getBounds(Node fact, Integer new_field, std::map<std::string, Integer > upperBounds){
    //Variable;
    if (fact.getKind() == Kind::VARIABLE) {
        if (upperBounds.find(fact.getName())!= upperBounds.end()){
            std::optional<Integer> answer = upperBounds[fact.getName()] -Integer(1);
            return answer;
         }
        return {};
    }
    // Constant
    if (fact.getKind() == Kind::CONST_FINITE_FIELD){
        Integer coef = fact.getConst<FiniteFieldValue>().getValue();
        if (new_field.divides(coef)){
            return Integer(0);
        }
        return coef;
    }
    // Multiplication
    if (fact.getKind() == Kind::FINITE_FIELD_MULT){
        Integer product = Integer(1);
        for (int i=0; i<fact.getNumChildren(); i++){
            std::optional<Integer> result = getBounds(fact[i], new_field, upperBounds);
            if (result.has_value()){
                product = product*result.value();
            }
            else {
                return {};
            }
        }
        return product;
    }
    Assert(fact.getKind() == Kind::FINITE_FIELD_ADD);
    Integer sum = Integer(0);
    for (int i=0; i<fact.getNumChildren(); i++){
        auto result = getBounds(fact[i], new_field, upperBounds);
        if (result.has_value()){
            sum +=result.value();
        }
        else {
        return {};
        }
    }
    return sum;
}

void noCoCoALiza()
{
    std::cout << "cvc5 can't solve field problems since it was not configured with "
      "--cocoa\n";
    AlwaysAssert(false);
}

// TODO: Need to find max by iterating through equations.
std::vector<long> getWeights(std::vector<CoCoA::symbol> symbols, std::map<std::string, Integer > upperBounds){
    std::vector<long> answer;
    for (auto i: symbols){
        std::ostringstream oss;
        oss << i;
        std::cout << i << "\n";
        if (upperBounds.find(oss.str())!= upperBounds.end()){

            long result = 10*log2(upperBounds[oss.str()].getDouble());
            std::cout << result << "\n";
            answer.push_back(long(result));
        }
        else {
            float result = BIGINTLOG;
            std::cout << "NOBOUND" << result << "\n";
            answer.push_back(long(result));
        }
    }
    return answer;
} 




std::vector<Node> SimplifyViaGB(std::vector<Node> equalities, Integer modulous, std::map<std::string, Integer > upperBounds, NodeManager* nm){
      if (equalities.size() <= 1) {
        return equalities;
      }
      //std::cout << "Got here" << modulous << "\n";
      CocoaEncoder enc((FfSize(modulous)) );
      //std::cout << "Made encoder \n";
      // collect leaves
      for (const Node& node : equalities)
      {
        enc.addFact(node);
      }
      //std::cout << "Added facts first time \n";
      std::vector<long> boundWeights = getWeights(enc.d_syms, upperBounds);
      enc.endScanIntegers(boundWeights);
      //std::cout << "Scanned Integers \n";
      //std::cout << "Got ring\n";
      //std::cout << "Got weights \n";
      // assert facts
      for (const Node& node : equalities)
      {
        enc.addFact(node);
      }
      //std::cout << "Added facts a second time \n";

      // compute a GB
      std::vector<CoCoA::RingElem> generators;
      generators.insert(
          generators.end(), enc.polys().begin(), enc.polys().end());
      //std::cout << "Computed generators \n";
      CoCoA::ideal ideal = CoCoA::ideal(generators);
      std::cout << "Computed ideal \n";
      auto basis = CoCoA::GBasis(ideal);
      std::vector<Node> newPoly;
      if (basis.size() == 1 && CoCoA::deg(basis.front()) == 0)
      {
        std::cout << "BADDDDD BADDD BADDD\n";
        return newPoly;
      }
      std::cout << "Computed basis \n";
      //std::cout << "BASIS\n";
      newPoly = enc.cocoaToNode(basis, nm);
      //std::cout << "Finished Conversion\n";
      //std::cout << newPoly.size() << "\n";

      return newPoly;
}


bool checkIfConstraintIsMet(Node equality, Integer modulos, std::map<std::string, Integer > upperBounds){
    if (auto LHS  = getBounds(equality[0], modulos, upperBounds) ){
        //std::cout << LHS.value() << "\n";
       // std::cout << modulos << "\n";
        if (LHS.value() >= modulos){
            return false;
        }
    } else {
        return false;
    }
    if (auto RHS  = getBounds(equality[1], modulos, upperBounds) ){
        if (RHS.value() >= modulos){
            return false;
        }
    } else {
        return false;
    } 
    return true;
}


/////////////////////////////////////////////////// INTEGERFIELD ////////////////////////////////////////////////////////////////////

IntegerField::IntegerField(Env &env):EnvObj(env){initCocoaGlobalManager();};

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
                std::cout << "WE GOT HEREEEEE \n";
                status = Result::UNSAT;
                return true;
               }
        }
    }
    return false;
}


Node IntegerField::subVarHelper(Node fact, Node ogf, Node newf) {
    if (fact == ogf){
        return newf;
    }
    if (fact.getNumChildren()!=0){
        std::vector<Node> children ;
        for (int i =0; i<fact.getNumChildren(); i++){
            children.push_back(subVarHelper(fact[i], ogf, newf));
        }
        NodeManager* nm = NodeManager::currentNM();
        return rewrite(nm->mkNode(fact.getKind(), children));
    }
    return fact;

}

void IntegerField::substituteVariables(){
    std::vector<Node> new_equalities;
    for (int i = 0; i<equalities.size(); i++){
        Node fact = equalities[i];
        //std::cout << "We are here?" << fact << "\n";
    if ( (fact[0].getKind() == Kind::VARIABLE && 
        fact[1].getKind() == Kind::VARIABLE) || (fact[0].getKind() == Kind::VARIABLE && 
        fact[1].getKind() == Kind::CONST_FINITE_FIELD)){
            std::vector<Node> new_inequalities;
            for(Node assert: inequalities){
                if (assert!=fact){
                new_inequalities.push_back(subVarHelper(assert, fact[0], fact[1]));
                } else {
                    status = Result::UNSAT;
                    return;
                }
            }
            inequalities = new_inequalities;
    }
    if (fact[0].getKind() == Kind::CONST_FINITE_FIELD && 
        fact[1].getKind() == Kind::VARIABLE){
            std::vector<Node> new_inequalities;
            for(Node assert: inequalities){
                if (assert!=fact){
                new_inequalities.push_back(subVarHelper(assert, fact[1], fact[0]));
                } else {
                    status = Result::UNSAT;
                    return;
                }
            }
            inequalities = new_inequalities;
    }
    }
}


bool IntegerField::Simplify(std::map<Integer, Field>& fields, std::map<std::string, Integer > upperBounds){
    std::cout << "STARTED INTEGERS\n";
    if (processedEqualitiesIndex > equalities.size()-1 && 
        processedInEqualitiesIndex > inequalities.size()-1){
            return false;
        }
    substituteVariables();
    CancelConstants();
    checkUnsat();
    NodeManager* nm = NodeManager::currentNM();
      if (newEqualitySinceGB){
         std::cout << "STARING GB\n";
         std::vector<Node> newPoly = SimplifyViaGB(equalities, BIGINT, upperBounds, nm);
         if (newPoly.size() == 0 && equalities.size()!=0){
             std::cout << equalities.size() << "\n";
            std::cout << "BAD BAD BAD\n";

             status = Result::UNSAT;
             return false;
        }
         std::cout <<  "Finished GB\n";
         clearEqualities();
         for (Node poly: newPoly){
             std::cout << "New Poly F:" << poly << "\n \n \n";
             addEquality(rewrite(poly));
             //std::cout << "WHAT\n";
        }
         std::cout << equalities.size() << "\n";
         std::cout << newPoly.size() << "\n";
         AlwaysAssert(equalities.size() == newPoly.size());
        newEqualitySinceGB = false;
    }
    checkUnsat();
    std::cout << "FINISHED ADDING FOR INTEGERS\n";
    for (auto& fieldPair : fields){
        //std::cout << "LOWERING\n";
        Lower(fieldPair.second,upperBounds);
    }
    //std::cout << "FINISHED LOWERING\n";
    processedEqualitiesIndex = std::max( int(equalities.size() -1), 0);
    processedInEqualitiesIndex = std::max( int(inequalities.size() -1),0);
    return true;
}

void IntegerField::addEquality(Node equality){
    //std::cout << "INTEGER FIELD LOOKING ATT" << equality << "\n";
    if (std::find(equalities.begin(), equalities.end(), equality) == equalities.end()){
        //std::cout << "ADDED\n";
        newEqualitySinceGB = true;
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
    for (int i=processedEqualitiesIndex; i<equalities.size(); i++){
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
    for (int i=processedEqualitiesIndex; i<equalities.size(); i++){
        Node fact = equalities[i];
        if (fact[0].getKind() == Kind::FINITE_FIELD_MULT &&  
        fact[1].getKind()== Kind::FINITE_FIELD_MULT &&
        fact[0][0].getConst<FiniteFieldValue>().getValue() == fact[1][0].getConst<FiniteFieldValue>().getValue())
        {
            NodeManager* nm = NodeManager::currentNM();
            addEquality(rewrite(nm->mkNode(Kind::EQUAL, fact[0][1], fact[1][1])));
        }
    }      
    for (int i=processedInEqualitiesIndex; i<inequalities.size(); i++){
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
    initCocoaGlobalManager();}

Node Field::modOut(Node fact){
    std::vector<Node> left;
    NodeManager* nm = NodeManager::currentNM();
    /// TODO FIX THIS
    //std::cout << "Modout with" << fact << "\n";
    if (fact.getKind()== Kind::FINITE_FIELD_ADD){
    for(int i =0; i<fact.getNumChildren(); i++) {
        if (fact[i].getKind() == Kind::FINITE_FIELD_MULT && fact[i][0].getKind() == Kind::CONST_FINITE_FIELD 
        && modulos.divides(fact[i][0].getConst<FiniteFieldValue>().getValue())){}
        else {
            left.push_back(fact[i]);
        }
    }
    } else if (fact.getKind()== Kind::FINITE_FIELD_MULT) {
        if (fact[0].getKind() == Kind::CONST_FINITE_FIELD  && modulos.divides(fact[0].getConst<FiniteFieldValue>().getValue())){}
        else {
            left.push_back(fact);
        }
    } else if (fact.getKind() == Kind::CONST_FINITE_FIELD  && modulos.divides(fact.getConst<FiniteFieldValue>().getValue())){}
    else {
        left.push_back(fact);
    }
    if (left.size()==0){
        left.push_back(nm->mkConst(FiniteFieldValue::mkZero(modulos)));
    }
    //std::cout << "Finished \n";
    return rewrite(nm->mkNode(Kind::FINITE_FIELD_ADD, left));
};


void Field::addEquality(Node fact, bool inField){
    //std::cout <<"Adding equality:" << fact << "\n";
    fact = rewrite(fact);    
    if (std::find(equalities.begin(), equalities.end(), fact) == equalities.end()
        && fact.getKind() != Kind::CONST_BOOLEAN && fact.getKind()!=Kind::NULL_EXPR){
            newEqualitySinceGB = true;
        AlwaysAssert(fact.getKind() == Kind::EQUAL) << fact.getKind();
        if(inField){
            equalities.push_back(fact);
    } else {
    NodeManager* nm = NodeManager::currentNM();
    Node LHS = modOut(fact[0]);
    Node RHS = modOut(fact[1]);
    Node result = nm->mkNode(Kind::EQUAL, LHS, RHS);
    addEquality(result, true);
    }
    }
    //std::cout <<"Done adding equality:" << fact << "\n";
};

void Field::addInequality(Node fact){
    NodeManager* nm = NodeManager::currentNM();
    Node LHS = modOut(fact[0]);
    Node RHS = modOut(fact[1]);
    Node result = rewrite(nm->mkNode(Kind::EQUAL, LHS, RHS));
    inequalities.push_back(rewrite(nm->mkNode(Kind::EQUAL, LHS, RHS)));
};


bool Field::Simplify(IntegerField& Integers, std::map<std::string, Integer > upperBounds){
    if (processedEqualitiesIndex > equalities.size()-1 && 
        processedInEqualitiesIndex > inequalities.size()-1){
            return false;
    }
    //std::cout << "Starting field simplifcation \n";
    //for (int i =0; i< equalities.size(); i++) {
           // std::cout << equalities[i] << "\n";
        //}
    substituteVariables();
    checkUnsat();
    if (status == Result::UNSAT){
        return false;
    }
    NodeManager* nm = NodeManager::currentNM();
    if (newEqualitySinceGB){
        std::cout << "STARING GB\n";
        std::vector<Node> newPoly = SimplifyViaGB(equalities,modulos, upperBounds, nm);
        if (newPoly.size() == 0 && equalities.size()!=0){
            std::cout << equalities.size() << "\n";
            std::cout << "BAD BAD BAD\n";

            status = Result::UNSAT;
            return false;
        }
        std::cout <<  "Finished GB\n";
        clearEqualities();
        for (Node poly: newPoly){
            //std::cout << "New Poly F:" << poly << "\n \n \n";
            addEquality(rewrite(poly), false);
            //std::cout << "WHAT\n";
        }
        //std::cout << equalities.size() << "\n";
       //std::cout << newPoly.size() << "\n";
        AlwaysAssert(equalities.size() == newPoly.size());
        newEqualitySinceGB = false;
    }
   // std::cout << "ADDED ALL EQUALITIES FOR FIELDS\n";
    //std::cout << "SIZE" << equalities.size() << "\n";
    //substituteVariables();
    std::cout << "Substitute Vars done \n";
    //substituteEqualities();
    //std::cout << "Substitute Eqs done \n";
    //std::cout << "Checking Unsat is done \n";
    Lift(Integers, upperBounds);
    processedEqualitiesIndex = std::max( int(equalities.size() -1), 0);
    processedInEqualitiesIndex = std::max( int(inequalities.size() -1),0);
    return true;
};


void Field::Lift(IntegerField& integerField, std::map<std::string, Integer> upperBounds){
     for (int i=processedEqualitiesIndex; i<equalities.size(); i++){
        if (checkIfConstraintIsMet(equalities[i], modulos, upperBounds)){
            integerField.addEquality(equalities[i]);
        }
     }
    // Can always lift inequalities
    for (int j=processedInEqualitiesIndex; j<inequalities.size(); j++){
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
    if (fact == ogf){
        return newf;
    }
    if (fact.getNumChildren()!=0){
        std::vector<Node> children ;
        for (int i =0; i<fact.getNumChildren(); i++){
            children.push_back(subVarHelper(fact[i], ogf, newf));
        }
        NodeManager* nm = NodeManager::currentNM();
        return rewrite(nm->mkNode(fact.getKind(), children));
    }
    return fact;

}

void Field::substituteVariables(){
    std::vector<Node> new_equalities;
    for (int i = 0; i<equalities.size(); i++){
        Node fact = equalities[i];
        //std::cout << "We are here?" << fact << "\n";
    if ( (fact[0].getKind() == Kind::VARIABLE && 
        fact[1].getKind() == Kind::VARIABLE) || (fact[0].getKind() == Kind::VARIABLE && 
        fact[1].getKind() == Kind::CONST_FINITE_FIELD)){
            std::vector<Node> new_inequalities;
            for(Node assert: inequalities){
                if (assert!=fact){
                new_inequalities.push_back(subVarHelper(assert, fact[0], fact[1]));
                } else {
                    status = Result::UNSAT;
                    return;
                }
            }
            inequalities = new_inequalities;
    }
    if (fact[0].getKind() == Kind::CONST_FINITE_FIELD && 
        fact[1].getKind() == Kind::VARIABLE){
            std::vector<Node> new_inequalities;
            for(Node assert: inequalities){
                if (assert!=fact){
                new_inequalities.push_back(subVarHelper(assert, fact[1], fact[0]));
                } else {
                    status = Result::UNSAT;
                    return;
                }
            }
            inequalities = new_inequalities;
    }

    }
}


bool Field::checkUnsat(){
    for(int i=0; i<inequalities.size(); i++){
        if (inequalities[i].getKind()== Kind::CONST_BOOLEAN &&
            inequalities[i].getConst<bool>() == true){
            status = Result::UNSAT;
            return true;
            }
        for(int j=0; j<equalities.size(); j++){
            if((inequalities[i][0]==equalities[j][0]) &&
               (inequalities[i][1]==equalities[j][1]) ){
                std::cout << "WE GOT HEREEEEE \n";
                status = Result::UNSAT;
                return true;
               }
        }
    }
    return false;
}

/////////////////////////////////////////////////// RangeSolver ////////////////////////////////////////////////////////////////////

RangeSolver::RangeSolver(Env& env)
    :EnvObj(env), integerField(env), d_facts(context()){}

void RangeSolver::preRegisterTerm(TNode node){ 
      /// Check Field  ONLY WHEN OPERATION IS EQUAL OR NOT EQUAL
      if (node.getKind() == Kind::CONST_FINITE_FIELD){
        Integer constant = node.getConst<FiniteFieldValue>().getValue();
        if (constant == 0 || constant == 1){
            return;
        }
        else if (fields.count(constant)==0){
            fields.insert(std::make_pair(constant, Field(d_env,constant)));
      } } else {
        if (node.getKind() == Kind::EQUAL) {
            TypeNode ty = node[0].getType();
            //std::cout << ty << "\n";
            //std::cout << ty.getFfSize() << "\n";
            if (fields.count( ty.getFfSize()) == 0) {
            fields.insert(std::make_pair(ty.getFfSize(), Field(d_env,ty.getFfSize())));
        }
      }
    }
}



void RangeSolver::notifyFact(TNode fact){
        //std::cout << fact << "\n";
        d_facts.emplace_back(fact); 
        if(fact.getKind() == Kind::FINITE_FIELD_LT){
            upperBounds[fact[0].getName()] = fact[1].getConst<FiniteFieldValue>().getValue();
        }
    else if (fact.getKind() == Kind::EQUAL) {
        //std::cout << fact[0].getType().getFfSize() << "\n";
        auto it = fields.find(fact[0].getType().getFfSize());
        if (it != fields.end()) {
            //std::cout << "Adding Equality\n";
             it->second.addEquality(fact, false);
        } else {;
            AlwaysAssert(false);
        }
    }
    else if (fact.getKind() == Kind::NOT){
        //std::cout << "INEQUALITY" << fact << "\n";
         auto it = fields.find(fact[0][1].getType().getFfSize());
        if (it != fields.end()) {
             it->second.addInequality(fact[0]);
        } else {
            AlwaysAssert(false);
        }
    }
    else {
        std::cout << "Not set up for this fact\n";
        AlwaysAssert(false);
    }
    std::cout << "Done with fact\n";

}


Result RangeSolver::Solve(){
    #ifdef CVC5_USE_COCOA
    #else 
        noCoCoALiza();
    #endif
    std::cout << "We are here\n";
    int count = 0;
    while(true){
        //if (count >=5){
            // AlwaysAssert(false);
        //}
        printSystemState();
        integerField.Simplify(fields, upperBounds);
        if (integerField.status == Result::UNSAT){
            return Result::UNSAT;
        }
        std::cout << "FINISHED INTEGERS\n";
        printSystemState();
        for (auto& fieldPair :fields){
            fieldPair.second.Simplify(integerField, upperBounds);
            std::cout << fieldPair.second.modulos << "\n";
             integerField.Simplify(fields, upperBounds);
                if (integerField.status == Result::UNSAT){
                 return Result::UNSAT;
            }
            printSystemState();
        }
        std::cout << "FINISHED FIELDS\n";
        for (auto fieldPair :fields){
            if (fieldPair.second.status == Result::UNSAT){
                return Result::UNSAT;
            }

        }
        count +=1;
    }
};

const std::vector<Node>& RangeSolver::conflict() const { return d_conflict; }

Result RangeSolver::postCheck(Theory::Effort){
    std::cout << "Hello???\n";
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
    std::cout << "DONE!" << "\n\n\n";
}





}
}
}
