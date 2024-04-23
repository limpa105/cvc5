


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

void SimplifyViaGB(std::vector<Node> equalities, Integer modulous){
      if (equalities.size() == 0) {
        return;
      }
      CocoaEncoder enc( (FfSize(modulous)) );
      std::cout << "Made encoder \n";
      // collect leaves
      for (const Node& node : equalities)
      {
        enc.addFact(node);
      }
      std::cout << "Added facts first time \n";

      enc.endScanIntegers();
      std::cout << "Scanned Integers \n";
      // assert facts
      for (const Node& node : equalities)
      {
        enc.addFact(node);
      }
      std::cout << "Added facts a second time \n";

      // compute a GB
      std::vector<CoCoA::RingElem> generators;
      generators.insert(
          generators.end(), enc.polys().begin(), enc.polys().end());
      std::cout << "Computed generators \n";
      CoCoA::ideal ideal = CoCoA::ideal(generators);
      std::cout << "Computed ideal \n";
      try {
      auto basis = CoCoA::GBasis(ideal);
      std::cout << "Computed basis \n";
      std::cout << "BASIS\n";
      for (auto i: basis){
        std::cout << i << "\n";
         for (CoCoA::SparsePolyIter iter=CoCoA::BeginIter(i); !CoCoA::IsEnded(iter); ++iter)
         {
            std::cout << "coeff: " << coeff(iter)  << "\tPP: " << PP(iter)  << "\n";
        }
      }
      } catch (const CoCoA::ErrorInfo e) {
      std::cout << e << "\n";
       AlwaysAssert(false);
      }

      // if it is trivial, create a conflict
      //bool is_trivial = basis.size() == 1 && CoCoA::deg(basis.front()) == 0;
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

bool IntegerField::Simplify(std::map<Integer, Field>& fields, std::map<std::string, Integer > upperBounds){
    if (processedEqualitiesIndex > equalities.size()-1 && 
        processedInEqualitiesIndex > inequalities.size()-1){
            return false;
        }
    CancelConstants();
    SimplifyViaGB(equalities, Integer(57885161));
    for (auto& fieldPair : fields){
        Lower(fieldPair.second,upperBounds);
    }
    processedEqualitiesIndex = std::max( int(equalities.size() -1), 0);
    processedInEqualitiesIndex = std::max( int(inequalities.size() -1),0);
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
    //std::cout << "Finished \n";
    NodeManager* nm = NodeManager::currentNM();
    return rewrite(nm->mkNode(Kind::FINITE_FIELD_ADD, left));
};


void Field::addEquality(Node fact, bool inField){
    fact = rewrite(fact);
    if (std::find(equalities.begin(), equalities.end(), fact) == equalities.end()
        && fact.getKind() != Kind::CONST_BOOLEAN && fact.getKind()!=Kind::NULL_EXPR){
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
    for (int i =0; i< equalities.size(); i++) {
            std::cout << equalities[i] << "\n";
        }
    SimplifyViaGB(equalities, modulos);
    //std::cout << "SIZE" << equalities.size() << "\n";
    //substituteVariables();
    //std::cout << "Substitute Vars done \n";
    //substituteEqualities();
    //std::cout << "Substitute Eqs done \n";
    checkUnsat();
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
    for (int i = processedEqualitiesIndex; i<equalities.size(); i++){
        Node fact = equalities[i];
        //std::cout << "We are here?" << fact << "\n";
    if (fact[0].getKind() == Kind::VARIABLE && 
        fact[1].getKind() == Kind::VARIABLE){
            //std::cout << fact << "\n";
            for(Node &assert: equalities){
                  //std::cout << "Assert Kind:" << assert.getKind() << "\n";
                 //std::cout << "Assert:" << assert << "\n";
                if (assert!=fact){
                    //std::cout << "Entering Sub Var\n";
                    Node result = (subVarHelper(assert, fact[0],fact[1]));
                    //std::cout << "exiting Sub Var" << result << "\n";
                    new_equalities.push_back(result);
                    //std::cout << "exiting add equality\n";
                }
                //else {
                    //new_equalities.push_back(fact);
                //}
            }
            //equalities = new_equalities;
            //std::vector<Node> new_inequalities;
            //for(Node assert: inequalities){
                //if (assert!=fact){
                //new_inequalities.push_back(subVarHelper(assert, fact[0], fact[1]));
                //} else {
                    //status = Result::UNSAT;
                    //return;
                //}
            //}
            //inequalities = new_inequalities;
    }
    }
    for (auto equality: new_equalities){
        addEquality(equality, false);
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
        if (fields.count(constant)==0){
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
        d_facts.emplace_back(fact); 
        if(fact.getKind() == Kind::FINITE_FIELD_LT){
            upperBounds[fact[0].getName()] = fact[1].getConst<FiniteFieldValue>().getValue();
        }
    else if (fact.getKind() == Kind::EQUAL) {
        auto it = fields.find(fact[0].getType().getFfSize());
        if (it != fields.end()) {
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

}


Result RangeSolver::Solve(){
    #ifdef CVC5_USE_COCOA
    #else 
        noCoCoALiza();
    #endif
    int count = 0;
    while(true){
        if (count >=5){
            AlwaysAssert(false);
        }
        printSystemState();
        integerField.Simplify(fields, upperBounds);
        for (auto& fieldPair :fields){
            fieldPair.second.Simplify(integerField, upperBounds);
        }
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
