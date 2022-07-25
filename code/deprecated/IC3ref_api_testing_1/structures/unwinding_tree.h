#pragma once
//
// Created by galls2 on 04/10/19.
//

#include <queue>
#include <memory>
#include <vector>
#include <experimental/optional>
#include <set>
#include <abstraction/abstract_state.h>
#include <utils/omg_utils.h>
#include "concrete_state.h"

class UnwindingTree;
class KripkeStructure;
class Goal;
class AbstractState;

typedef std::unordered_map<AbstractState*, std::unordered_set<UnwindingTree*>> CandidateSet;

class UnwindingTree {
public:
    UnwindingTree(const KripkeStructure& kripke, ConcreteState& concrete_state, UnwindingTree * parent);
    size_t get_depth() const;
    const ConcreteState& get_concrete_state() const;
    const std::vector<std::unique_ptr<UnwindingTree>>& unwind_further();
    void reset_developed_in_tree();
    void set_developed(const Goal& goal);
    bool is_developed(const Goal& goal) const;
    void set_urgent(bool to_set);
    std::experimental::optional<AStateRef>  get_abs() const;
    void set_abs(AbstractState& astate);
    bool is_urgent() const;
    const std::vector<std::unique_ptr<UnwindingTree>>& get_successors() const;
    bool exist_successors() const;
    void map_subtree(const std::function<void(UnwindingTree &)> &mapper,
                     const std::function<bool(const UnwindingTree &)> &activation_condition);
    void map_upwards(const std::function<void(UnwindingTree &)> &mapper,
                     const std::function<bool(const UnwindingTree &)> &last_node_pred);
    bool any_of_upwards(const std::function<bool(const UnwindingTree &)> &predicate,
                       const std::function<bool(const UnwindingTree &)> &last_node_pred) const;
    bool is_concrete_lasso(const UnwindingTree& last_node) const;
    std::pair<CandidateSet, UnwindingTree*> find_abstract_lasso(const UnwindingTree& last_node);
    void add_label(bool positivity, const CtlFormula& spec);

    UnwindingTree* get_parent() const;

#ifdef DEBUG
    std::string to_string() const;
#endif
private:
    const KripkeStructure& _kripke;
    ConcreteState& _cstate;
    std::experimental::optional<AStateRef> _astate;
    UnwindingTree * const _parent;
    size_t _depth;
    bool _URGENT;
    std::vector<std::unique_ptr<UnwindingTree>> _successors;
    std::set<const Goal*> _developed;
};

auto cmp_nodes = [](const UnwindingTree* a, const UnwindingTree* b)
{
    if (a == b) return false;
    bool a_urgent = a->is_urgent();
    bool b_urgent = b->is_urgent();
    assert(!a_urgent || !b_urgent);
    if (a_urgent) return true;
    if (b_urgent) return false;
    if (a->get_depth() < b->get_depth()) return true;
    if (a->get_depth() > b->get_depth()) return false;
    return a < b;
};

typedef std::multiset <UnwindingTree*, decltype(cmp_nodes)> NodePriorityQueue;
