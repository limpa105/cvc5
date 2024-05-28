#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/ff/stats.h"
#include "theory/ff/util.h"
#include "theory/theory.h"
#include "util/integer.h"
#include "util/result.h"


namespace cvc5::internal {
namespace theory {
namespace ff {

// Forward Declaration 
class Field;

class IntegerField: protected EnvObj{
    public:

        IntegerField(Env &env);

        std::vector<Node> equalities;

        std::vector<Node> inequalities;

        bool Simplify(std::map<Integer, Field>& fields, std::map<std::string, Integer > upperBounds);

        void addEquality(Node equality);

        void clearEqualities(){equalities.clear();};

        void addInequality(Node inequality);

        void Lower(Field& field, std::map<std::string, Integer > upperBounds);

        void CancelConstants();

        bool checkUnsat();

        Result status = Result::UNKNOWN;

        void clearAll(){inequalities.clear(); equalities.clear(); status=Result::UNKNOWN;};



};

class Field:  protected EnvObj {
    public: 

        Result status = Result::UNKNOWN;

        Field(Env & env, Integer modulos);

        Integer modulos;
 
        std::vector<Node> equalities;

        std::vector<Node> inequalities;

        void addEquality(Node equality, bool inField);

        void clearEqualities(){equalities.clear();};

        void addInequality(Node inequality);

        bool checkUnsat();

        bool Simplify(IntegerField& Integers, std::map<std::string, Integer > upperBounds);

        Node modOut(Node fact);

        bool newEqualitySinceGB = false;

        bool LearnLemmas(Node fact, std::map<std::string, Integer > upperBounds);

        std::vector<Node> lemmas;

        void clearAll(){inequalities.clear(); equalities.clear(); lemmas.clear(); status=Result::UNKNOWN;};

        void Lift(IntegerField& integerField, std::map<std::string, Integer> upperBounds);

        void substituteEqualities();

        void substituteVariables();

        Node subVarHelper(Node fact, Node ogf, Node newf);

};

class RangeSolver : protected EnvObj
{
    public:
        RangeSolver(Env& env);

        std::map<std::string, Integer > upperBounds;

        void notifyFact(TNode fact);

        Result postCheck(Theory::Effort);

        IntegerField integerField;

        void preRegisterTerm(TNode node);

        void processFact(TNode node);

       std::vector<Node>& conflict() ;

        std::vector<Node> d_conflict;

        bool learnedLemma = false;

        Node Lemma;


    private:

        context::CDList<Node> d_facts;

        std::map<Integer, Field> fields; 

        Result Solve();

        void printSystemState();

};
}
}
}
