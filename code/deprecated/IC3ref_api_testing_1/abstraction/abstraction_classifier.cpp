//
// Created by galls2 on 14/10/19.
//

#include "abstraction_classifier.h"
#include <utility>
#include <configuration/omg_config.h>
#include <formulas/sat_solver.h>
#include <utils/z3_utils.h>
#include <utils/Stats.h>
#include "abstract_state.h"

using namespace avy;

AbstractionClassifier::AbstractionClassifier(const KripkeStructure &kripke) : _kripke(kripke) {}

const KripkeStructure &AbstractionClassifier::get_kripke() const {
    return _kripke;
}

bool AbstractionClassifier::exists_classification(const ConcreteState &cstate) const {

    std::set<std::string> ap_strings = cstate.string_sat_aps();
    const auto& it = _classification_trees.find(ap_strings);
    bool found = (it != _classification_trees.end());
    return found;
}

AbstractState &AbstractionClassifier::classify_cstate(const ConcreteState &cstate) {
    AVY_MEASURE_FN;

    std::set<std::string> ap_strings = cstate.string_sat_aps();
#ifdef DEBUG
    assert(exists_classification(cstate));
#endif

    const AbstractClassificationNode& cl_tree_root = *_classification_trees.at(ap_strings);
    AbstractState& abs_state = cl_tree_root.classify(cstate);

    #ifdef DEBUG
    assert(Z3SatSolver(cstate.get_conjunct().ctx()).is_sat(cstate.get_conjunct() && abs_state.get_formula().get_raw_formula()));
#endif

    return abs_state;
}

AbstractClassificationNode &AbstractionClassifier::add_classification_tree(const ConcreteState &cstate, AbstractState& astate)
{
    AVY_MEASURE_FN;

    std::set<std::string> ap_strings = cstate.string_sat_aps();

    std::unique_ptr<AbstractClassificationNode> cl = std::make_unique<AbstractClassificationNode>(*this, &astate);
    const auto res = _classification_trees.emplace(ap_strings, std::move(cl));
    assert(res.second);
    astate.set_cl_node(_classification_trees[ap_strings].get());
    return *((res.first)->second);
}

AbstractState &AbstractionClassifier::update_classification(const AbstractState &astate, const ConcreteState &cstate)
{
    AVY_MEASURE_FN;

    AbstractClassificationNode* cl = astate.get_cl_node();
    return cl->classify(cstate);
}

AbstractClassificationNode *
AbstractionClassifier::split(AbstractState &astate, PropFormula &query_formula, AbstractState &astate_pos,
                             AbstractState &astate_neg) {

    AVY_MEASURE_FN;

    AbstractClassificationNode* cl_node = astate.get_cl_node();
    assert(cl_node->is_leaf());

    cl_node->_successors.emplace(true, std::make_unique<AbstractClassificationNode>(*this, &astate_pos, cl_node));
    cl_node->_successors.emplace(false, std::make_unique<AbstractClassificationNode>(*this, &astate_neg, cl_node));
#ifdef DEBUG
    cl_node->get_successor(true).set_split_string(cl_node->get_abs()->_debug_name + std::string("::True"));
    cl_node->get_successor(false).set_split_string(cl_node->get_abs()->_debug_name + std::string("::False"));
#endif

    z3::context& ctx = query_formula.get_ctx();
    cl_node->_query.emplace([query_formula, &ctx] (const ConcreteState& cstate)
    {
#ifdef DEBUG
        Z3ExprSet cstate_vars = expr_vector_to_set(FormulaUtils::get_vars_in_formula(cstate.get_conjunct()));
        Z3ExprSet ps_vars = expr_vector_to_set(query_formula.get_vars_by_tag("ps"));
        assert(is_contained_z3_containers(cstate_vars, ps_vars));
        assert(FormulaUtils::is_cstate_conjunct(query_formula.get_raw_formula()));
#endif

        bool is_sat = FormulaUtils::are_two_conj_sat(query_formula.get_raw_formula(), cstate.get_conjunct());
        return is_sat;
    });

    return cl_node;
}

#ifdef DEBUG
void AbstractClassificationNode::set_split_string(const std::string& str) {
    _split_string = str;
}
#endif

AbstractClassificationNode::AbstractClassificationNode(AbstractionClassifier &classifier,
        AbstractState* abs_state, const AbstractClassificationNode *parent)
        : _classifier(classifier), _abs_state(abs_state), _parent(parent),
        _depth(_parent == nullptr ? 0 : _parent->get_depth() + 1)
{ }

size_t AbstractClassificationNode::get_depth() const {
    return _depth;
}

bool AbstractClassificationNode::is_leaf() const {
    return _successors.empty();
}

AbstractState &AbstractClassificationNode::classify(const ConcreteState &cstate) const {

    const AbstractClassificationNode* current = this;
    while (!current->_successors.empty())
    {
        assert(current->_query);
        const auto& query = current->_query.value();
        bool successor = query(cstate);
        current = &current->get_successor(successor);
    }
    assert(current->_abs_state);
    return *current->_abs_state;
}

AbstractState *AbstractClassificationNode::get_abs() const {
    return _abs_state;
}

const AbstractClassificationNode *AbstractClassificationNode::get_parent() const {
    return _parent;
}

AbstractClassificationNode& AbstractClassificationNode::get_successor(QueryResult query_result)
{
    assert(_successors.find(query_result) != _successors.end());
    return *_successors[query_result];
}

const AbstractClassificationNode& AbstractClassificationNode::get_successor(QueryResult query_result) const
{
    assert(_successors.find(query_result) != _successors.end());
    return *_successors.at(query_result);
}
