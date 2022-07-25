#pragma once
//
// Created by galls2 on 04/10/19.
//

#include "../structures/kripke_structure.h"
#include "../utils/z3_utils.h"
#include "abstract_state.h"
#include "../utils/omg_utils.h"

class UnwindingTree;
struct SplitFormulas;

struct EEClosureResult
{
    bool is_closed = false;
    std::experimental::optional<ConcreteState> src;
    std::experimental::optional<ConcreteState> dst;
};

struct AEClosureResult
{
    bool is_closed = false;
    std::experimental::optional<ConcreteState> violator;
};



struct RefinementResult
{
    bool is_split = true;
    AbstractState* astate_generalized = nullptr;
    AbstractState* astate_remainder = nullptr;
    std::experimental::optional<PropFormula> split_query;
};

class OmgModelChecker;

class AbstractStructure {
public:
    explicit AbstractStructure(const KripkeStructure& kripke, const OmgModelChecker* omg);
    AbstractState& create_astate_from_cstate(const ConcreteState& cstate);
    AbstractState& create_astate_from_astate_split(const AbstractState& astate, PropFormula sym_rep);

    EEClosureResult is_EE_closure(AbstractState& to_close , const std::set<ConstAStateRef>& close_with);
    EEClosureResult is_EE_closure2(const PropFormula& skeleton, AbstractState& to_close , const std::set<ConstAStateRef>& close_with, ISatSolver& sat_solver, const std::map<const AbstractState*, z3::expr>& astate_flags);

    AEClosureResult is_AE_closure(AbstractState& to_close , const std::set<ConstAStateRef>& close_with);

    const OmgModelChecker* get_omg() const;
    RefinementResult refine_exists_successor(const ConcreteState &src_cstate, AbstractState &src_abs,
                                 const ConstAbsStateSet &dsts_abs, const bool is_tse_possible, ISatSolver& sat_solver);

    RefinementResult refine_no_successor(const UnwindingTree& to_close_node, AbstractState& abs_src_witness,
            const ConstAbsStateSet &dsts_abs, const bool is_tse_possible, ISatSolver& sat_solver);

    RefinementResult refine_all_successors(const UnwindingTree& to_close_node, AbstractState& abs_src_witness,
            const ConstAbsStateSet &dsts_abs, const bool is_tse_possible, ISatSolver& sat_solver);

    std::set<ConstAStateRef> get_astates_by_property(const CtlFormula &prop);

private:
    const KripkeStructure& _kripke;
    const OmgModelChecker* _omg;
    std::set<AbstractState> _abs_states;

    std::map<AbstractState*, ConstAbsStateSet> _NE_may;
    std::map<AbstractState*, std::vector<ConstAbsStateSet>> _E_must;
    std::map<AbstractState*, std::vector<ConstAbsStateSet>> _E_may_over;
    std::map<AbstractState*, std::vector<std::pair<ConstAbsStateSet, EEClosureResult>>> _NE_may_over;

    std::pair<AbstractState*, AbstractState*> create_new_astates_and_update(AbstractState &abs_src_witness,
                                       SplitFormulas& new_abs_state_formulas);
};

