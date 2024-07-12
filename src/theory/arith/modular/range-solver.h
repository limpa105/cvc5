

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/theory.h"
#include "util/integer.h"
#include "util/result.h"
#include "theory/arith/theory_arith.h"

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

        IntegerField(Env &env);

        std::vector<Node> equalities;

        std::vector<Node> inequalities;

        bool Simplify(std::map<Integer, Field>& fields, std::map<std::string, std::pair<Integer, Integer> > Bounds);

        void addEquality(Node equality);

        void clearEqualities(){equalities.clear();};

        void clearInequalities(){inequalities.clear();};

        void addInequality(Node inequality);

        void Lower(Field& field, std::map<std::string, std::pair<Integer, Integer> > Bounds);

        void CancelConstants();

        bool checkUnsat();

        Result status = Result::UNKNOWN;

        void clearAll(){inequalities.clear(); equalities.clear(); status=Result::UNKNOWN;};



};

class Field:  protected EnvObj {
    public: 

        std::string mySingularReduce;
        
        void CancelConstants();

        Integer smallerInverse(Node fact);
        
        RangeSolver* solver;

        std::map<std::string, Node> myVariables;

        std::set<Node> myNodes;

        std::set<Node> LearntLemmasFrom;

        Result status = Result::UNKNOWN;

        Field(Env & env, Integer modulos, RangeSolver* solver);

        bool CheckIfInvSmaller(Node eq);

        Integer modulos;
 
        std::vector<Node> equalities;

        std::vector<Node> inequalities;

        void addEquality(Node equality, bool inField,  bool GBAddition=false);

        void clearEqualities(){equalities.clear();};

        void clearInequalities(){inequalities.clear();};

        void addInequality(Node inequality);

        bool checkUnsat();

        bool Simplify(IntegerField& Integers, std::map<std::string, std::pair<Integer, Integer> > Bounds,bool WeightedGB, bool startLearningLemmas);

        Node modOut(Node fact);

        bool newEqualitySinceGB = false;

        bool ShouldLearnLemmas(Node fact, std::map<std::string, std::pair<Integer, Integer> > Bounds);

        std::vector<Node> lemmas;

        void clearAll(){inequalities.clear(); equalities.clear(); lemmas.clear(); status=Result::UNKNOWN;};

        void Lift(IntegerField& integerField, std::map<std::string, std::pair<Integer, Integer> > Bounds, bool LearnLemmas);

        void substituteEqualities();

        void substituteVariables();

        Node subVarHelper(Node fact, Node ogf, Node newf);


};

class RangeSolver : protected EnvObj
{
    public:

        
         std::map<std::string, Node> myVariables;

        std::set<Node> myNodes;

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

        bool startLearningLemmas = false;

        std::vector<Node> Lemmas;

        std::map<Integer, Field> fields; 


    private:

        context::CDList<Node> d_facts;

        Result Solve();

        void printSystemState();

};
}
}
}
}
#endif // RANGE_SOLVER_H
