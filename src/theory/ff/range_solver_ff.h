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


    private:

        int processedEqualitiesIndex = 0;

        int processedInEqualitiesIndex = 0;

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


    private:

        int processedEqualitiesIndex = 0;

        int processedInEqualitiesIndex = 0;

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

        const std::vector<Node>& conflict() const;

    private:

        context::CDList<Node> d_facts;

        std::map<Integer, Field> fields; 

        Result Solve();

        std::vector<Node> d_conflict{};

        void printSystemState();

};
}
}
}
