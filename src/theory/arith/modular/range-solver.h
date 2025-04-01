

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/theory.h"
#include "util/integer.h"
#include "util/result.h"
#include "theory/arith/theory_arith.h"
#include "theory/theory_model.h"
#include "util/statistics_stats.h"


#ifndef RANGE_SOLVER_H
#define RANGE_SOLVER_H


namespace cvc5::internal {
namespace theory {
namespace arith {
namespace modular_range_solver {

// Forward Declaration 
class Field;
class RangeSolver;



class IntegerField: protected EnvObj{
    public:

        std::string mySingularReduce = "";

        bool GBTimedOut = false;

        bool novelBound; 

        bool newEqualitySinceGB = true;

        bool ranGB = false;

        IntegerField(Env &env, RangeSolver* solver);

        std::pair<Node, Node>  separateTerms(const Node& node, std::string targetNode);

        bool tightenBounds(std::map<std::string, std::pair<Integer, Integer> > &Bounds);

        Node substituteTargetVariableWithZero(const Node& node, std::string targetNode);

        std::pair<Integer, Integer> inferBoundsRecursive(const Node& node, std::map<std::string,  std::pair<Integer, Integer>>& Bounds);

        bool unlowerableIneq = false;

        RangeSolver* solver;

        Node subVarHelper(Node fact, Node ogf, Node newf);

        std::vector<Node> equalities;

        std::vector<Node> inequalities;

        std::vector<Node> old_equalities;

        std::vector<Node> old_inequalities;

        bool Simplify(std::map<Integer, Field>& fields, std::map<std::string, std::pair<Integer, Integer> > &Bounds);

        bool runGB();

        bool checkUnsatDiseq();

        bool reduceAgainstGB(Node eq);

        void addEquality(Node equality, bool GBAddition);

        void clearEqualities(){equalities.clear();};

        void clearInequalities(){inequalities.clear();};

        void substituteVariables();

        void addInequality(Node inequality);

        void Lower(Field& field, std::map<std::string, std::pair<Integer, Integer> > Bounds);

        void CancelConstants();

        bool checkUnsat();

        Result status = Result::UNKNOWN;

        void clearAll(){inequalities.clear(); equalities.clear(); status=Result::UNKNOWN;};



};

class Field:  protected EnvObj {
    public:   

        std::vector<long> getWeights2(std::map<std::string, Node> variables, std::map<std::string, std::pair<Integer, Integer>> Bounds, bool weightedGB, std::set<std::string> notVars);

        bool LiftViaILP(IntegerField& Integers, std::map<std::string, std::pair<Integer, Integer> > Bounds);

        std::map<std::string, std::vector<Rational>> collectMonomials(IntegerField z, Field f, NodeManager* nm);

        bool runGB(std::map<std::string, std::pair<Integer, Integer> > Bounds);

        bool checkUnsatDiseq();

        bool reduceAgainstGB(std::map<std::string, std::pair<Integer, Integer> > Bounds, Node eq);

        int didGurobi = 0;

        bool GBTimedOut = false;

        std::string mySingularReduce;
        
        void CancelConstants();

        Integer smallerInverse(Node fact);
        
        RangeSolver* solver;

        std::map<std::string, Node> myVariables;

        std::set<Node> myNodes;

        std::set<Node> LearntLemmasFrom = {};

        Result status = Result::UNKNOWN;

        Field(Env & env, Integer modulos, RangeSolver* solver);

        bool CheckIfInvSmaller(Node eq);

        Integer modulos;
 
        std::vector<Node> equalities;

        std::vector<Node> ALLequalities;

        std::vector<Node> inequalities;

        std::vector<Node> old_equalities;

        std::vector<Node> old_inequalities;

        void addEquality(Node equality, bool inField,  bool GBAddition=false);

        void clearEqualities(){equalities.clear();};

        void clearInequalities(){inequalities.clear();};

        void addInequality(Node inequality);

        bool checkUnsat();

        bool Simplify(IntegerField& Integers, std::map<std::string, std::pair<Integer, Integer> > Bounds,bool WeightedGB, int startLearningLemmas);

        Node modOut(Node fact);

        bool newEqualitySinceGB = true;

        bool ranGB = false;

        bool ShouldLearnLemmas(Node fact, std::map<std::string, std::pair<Integer, Integer> > Bounds);

        std::vector<Node> lemmas;

        void clearAll(){inequalities.clear(); equalities.clear(); lemmas.clear(); status=Result::UNKNOWN;};

        void Lift(IntegerField& integerField, std::map<std::string, std::pair<Integer, Integer> > Bounds, int LearnLemmas);

        void substituteEqualities();

        void substituteVariables();

        Node subVarHelper(Node fact, Node ogf, Node newf);


};

class RangeSolver : protected EnvObj
{
    public:

        IntStat completeGB ;

        IntStat timeoutGB ;

        IntStat totalGBilp ;

        IntStat totalGBtry ;  

        std::map<Node,Node> tempSkolemMap;

        bool addAssignment(Node asgn, Field* f);

        std::map<Node, Integer>  getPossibleAssignment(Field* f, std::map<std::string, std::pair<Integer, Integer> > Bounds, NodeManager* nm);

        std::set<Integer> og_fields;
        
        std::map<std::string, Node> myVariables;

        std::set<Node> myNodes;

        std::set<std::string> myNotVars;

        RangeSolver(Env& env, TheoryArith& parent);

        std::map<std::string, std::pair<Integer, Integer> > Bounds;

        void notifyFact(TNode fact);

        Result postCheck(Theory::Effort);

        IntegerField integerField;

        void preRegisterTerm(TNode node);

        void processFact(TNode node);

       std::vector<Node>& conflict() ;

        std::vector<Node> d_conflict;

        bool learnedLemma = false;

        std::vector<Node> Lemmas;

        std::map<Integer, Field> fields; 

        void setTrivialConflict();

        std::map<Node, Integer> finalModel;

        bool collectModelInfo(TheoryModel* m,
                                            const std::set<Node>& termSet);

        void parse_cvc5_output(const std::string& cvc5_output);

        void printSystemState();


    private:

        context::CDList<Node> d_facts;

        Result Solve();

        

};
}
}
}
}
#endif // RANGE_SOLVER_H
