#pragma once

//
// Created by galls2 on 14/10/19.
//


#include <structures/kripke_structure.h>
#include <functional>

class AbstractState;
class AbstractClassificationNode;

class AbstractionClassifier {
public:
    explicit AbstractionClassifier(const KripkeStructure& kripke);

    bool exists_classification(const ConcreteState& cstate) const;
    AbstractClassificationNode& add_classification_tree(const ConcreteState& cstate, AbstractState& astate);
    AbstractState& classify_cstate(const ConcreteState &cstate);
    const KripkeStructure& get_kripke() const;
    AbstractState& update_classification(const AbstractState& astate, const ConcreteState& cstate);
    AbstractClassificationNode* split(AbstractState& astate, PropFormula& query_formula, AbstractState& astate_pos, AbstractState& astate_neg);
private:
    const KripkeStructure& _kripke;
    std::map<std::set<std::string>, std::unique_ptr<AbstractClassificationNode>> _classification_trees;

};

class AbstractClassificationNode
{
public:
    typedef bool QueryResult;
    AbstractClassificationNode(AbstractionClassifier& classifier, AbstractState* abs_state, const AbstractClassificationNode* parent=nullptr);
    size_t get_depth() const;
    bool is_leaf() const;
    const AbstractClassificationNode* get_parent() const;
    AbstractState* get_abs() const;
    AbstractState& classify(const ConcreteState& cstate) const;

    AbstractClassificationNode& get_successor(QueryResult query_result);
    const AbstractClassificationNode& get_successor(QueryResult query_result) const;

    friend class AbstractionClassifier;
#ifdef DEBUG
    void set_split_string(const std::string& str);
#endif
private:
    const AbstractionClassifier& _classifier;
    std::experimental::optional<std::function<QueryResult(const ConcreteState&)>> _query;
    std::map<QueryResult, std::unique_ptr<AbstractClassificationNode>> _successors;
    AbstractState* const _abs_state;
    const AbstractClassificationNode* _parent;
    const size_t _depth;
#ifdef DEBUG
    std::string _split_string;
#endif
};

