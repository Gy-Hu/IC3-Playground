//
// Created by galls2 on 04/10/19.
//
#include <algorithm>
#include "abstract_structure.h"
#include <utils/z3_utils.h>
#include <model_checking/omg_model_checker.h>
#include <utils/omg_utils.h>
#include <utils/Stats.h>

using namespace avy;

AbstractStructure::AbstractStructure(const KripkeStructure &kripke, const OmgModelChecker* omg) : _kripke(kripke), _omg(omg)
{}

AbstractState &AbstractStructure::create_astate_from_cstate(const ConcreteState &cstate)
{
    AVY_MEASURE_FN;

    CtlFormula::PropertySet pos, neg;
    cstate.aps_by_sat(pos, neg);

    const auto res =_abs_states.emplace(_kripke, pos, neg, _kripke.get_aps(), cstate.get_bis0_formula());
    assert(res.second);

    return const_cast<AbstractState&>(*res.first);
}

EEClosureResult AbstractStructure::is_EE_closure2(const PropFormula& skeleton, AbstractState &to_close,
                                                 const std::set<ConstAStateRef> &close_with, ISatSolver& sat_solver, const std::map<const AbstractState*, z3::expr>& astate_flags)
{
    AVY_MEASURE_FN;
    ConstAbsStateSet p_closers;

    for (const ConstAStateRef& cl : close_with)
    {
        p_closers.insert(&cl.get());
    }

    if (_E_may_over.find(&to_close) != _E_may_over.end())
    {
        const auto &possible_closers = _E_may_over[&to_close];
        for (const auto& closer_set : possible_closers) {
            const bool is_subset = std::includes(p_closers.begin(), p_closers.end(), closer_set.begin(), closer_set.end());
            if (is_subset) {
                DEBUG_PRINT("Known closure found!");
                return {true, {}, {}};
            }
        }
    }

    if (_NE_may_over.find(&to_close) != _NE_may_over.end())
    {
        const auto &known_violations = _NE_may_over[&to_close];
        for (const auto &violation : known_violations) {
            const bool is_subset = std::includes(violation.first.begin(), violation.first.end(), p_closers.begin(),
                                           p_closers.end());
            if (is_subset) {
                DEBUG_PRINT("Known violation found!");

                return violation.second;
            }
        }
    }

    EEClosureResult closure_result = FormulaInductiveUtils::is_EE_inductive_inc(skeleton, to_close, sat_solver, astate_flags);

    if (closure_result.is_closed)
    {
        _E_may_over[&to_close].emplace_back(std::move(p_closers));
    } else
    {
        _NE_may_over[&to_close].emplace_back(std::move(p_closers), closure_result);
    }

    return closure_result;
}


EEClosureResult AbstractStructure::is_EE_closure(AbstractState &to_close,
                                                 const std::set<ConstAStateRef> &close_with)
{
    ConstAbsStateSet p_closers, p_non_closers;
    if (_NE_may.find(&to_close) != _NE_may.end()) {
        p_non_closers = _NE_may[&to_close];
    }
    for (const ConstAStateRef& cl : close_with) {
        if (p_non_closers.find(&cl.get()) == p_non_closers.end()) p_closers.insert(&cl.get());
    }

    if (_E_may_over.find(&to_close) != _E_may_over.end())
    {
        const auto &possible_closers = _E_may_over[&to_close];
        for (const auto& closer_set : possible_closers) {
            const bool is_subset = std::includes(p_closers.begin(), p_closers.end(), closer_set.begin(), closer_set.end());
            if (is_subset) {
                DEBUG_PRINT("Known closure found!");
                return {true, {}, {}};
            }
        }
    }

    if (_NE_may_over.find(&to_close) != _NE_may_over.end())
    {
        const auto &known_violations = _NE_may_over[&to_close];
        for (const auto &violation : known_violations) {
            const bool is_subset = std::includes(violation.first.begin(), violation.first.end(), p_closers.begin(),
                                           p_closers.end());
            if (is_subset) {
                DEBUG_PRINT("Known violation found!");

                return violation.second;
            }
        }
    }

    EEClosureResult closure_result = FormulaInductiveUtils::is_EE_inductive(to_close, p_closers);

    if (closure_result.is_closed)
    {
        _E_may_over[&to_close].emplace_back(std::move(p_closers));
    } else
    {
        _NE_may_over[&to_close].emplace_back(std::move(p_closers), closure_result);
    }

    return closure_result;
}

const OmgModelChecker *AbstractStructure::get_omg() const{
    return _omg;
}

RefinementResult AbstractStructure::refine_exists_successor(const ConcreteState &src_cstate, AbstractState &src_abs,
                                                const ConstAbsStateSet &dsts_abs, bool is_tse_possible, ISatSolver& sat_solver) {
    AVY_MEASURE_FN;

    if (_E_must.find(&src_abs) != _E_must.end())
    {
        auto& must_options = _E_must[&src_abs];
        if (std::any_of(must_options.begin(), must_options.end(),
                [&dsts_abs](ConstAbsStateSet& opt)
                {
                    return std::includes(dsts_abs.begin(), dsts_abs.end(), opt.begin(), opt.end());
                }
                ))
        {
            return {false, nullptr, nullptr, {}};
        }
    }

    std::set<const PropFormula *> dst_abs_formulas;
    for (const auto& dst_astate : dsts_abs) dst_abs_formulas.insert(&dst_astate->get_formula());


    SplitFormulas split_formulas =
            FormulaSplitUtils::ex_pos(src_cstate.get_conjunct(),
                                      src_abs.get_formula(), dst_abs_formulas, _kripke, sat_solver);

    if (is_tse_possible && OmgConfig::get<bool>("Trivial Split Elimination") && !split_formulas.remainder_formula.is_sat())
    {
        DEBUG_PRINT("TSE (REFINE EXISTS SUCCESSOR)\n");
        _E_must[&src_abs].emplace_back(dsts_abs);
        return {false, nullptr, nullptr, {}};
    }

    const std::pair<AbstractState*, AbstractState*> res = create_new_astates_and_update(src_abs, split_formulas);

    const bool is_src_in_dsts = std::any_of(dsts_abs.begin(), dsts_abs.end(), [&src_abs] (const AbstractState* abs_dst) {return (*abs_dst) == src_abs; });

    if (is_src_in_dsts)
    {
        ConstAbsStateSet updated = dsts_abs;
        const size_t erase_res = updated.erase(&src_abs);
        assert(erase_res == 1);
        updated.insert({res.first, res.second});
        _E_must[res.first].emplace_back(std::move(updated));
    } else
    {
        _E_must[res.first].emplace_back(dsts_abs);
    }
    return { true, res.first, res.second, {split_formulas.query} };
}

template <typename T, typename S>
void inherit_values_in_dict(std::map<T, S>& dict, T& old_key, const std::set<T>& new_keys)
{
    for (const auto& new_key : new_keys) { dict[new_key] = dict[old_key]; }
}


RefinementResult AbstractStructure::refine_no_successor(const UnwindingTree &to_close_node, AbstractState &abs_src_witness,
                                            const ConstAbsStateSet &dsts_abs, const bool is_tse_possible, ISatSolver& sat_solver/* =true */)
{
    AVY_MEASURE_FN;

    if (_NE_may.find(&abs_src_witness) != _NE_may.end() &&
        std::all_of(dsts_abs.begin(), dsts_abs.end(),
                [this, &abs_src_witness](const AbstractState* astate)
                    {
                        return _NE_may[&abs_src_witness].find(astate) != _NE_may[&abs_src_witness].end();

                    }))
    {
        return {false, nullptr, nullptr, {}};
    }

    std::set<const PropFormula *> dst_abs_formulas;
    std::for_each(dsts_abs.begin(), dsts_abs.end(),
            [&dst_abs_formulas] (const AbstractState* astate) { dst_abs_formulas.insert(&astate->get_formula()); });

    SplitFormulas split_formulas =
            FormulaSplitUtils::ex_neg(to_close_node.get_concrete_state().get_conjunct(),
                                      abs_src_witness.get_formula(), dst_abs_formulas, _kripke, false, sat_solver);

#ifdef DEBUG
    Z3SatSolver solver(abs_src_witness.get_formula().get_ctx());
    assert(solver.is_sat(split_formulas.generalized_formula.get_raw_formula()));
#endif

    if (is_tse_possible && OmgConfig::get<bool>("Trivial Split Elimination") && !split_formulas.remainder_formula.is_sat())
    {
        // Code should never get here.
        assert(false);
        throw OmgException("Illegal TSE conducted");
    }

    const std::pair<AbstractState*, AbstractState*> res = create_new_astates_and_update(abs_src_witness, split_formulas);

    const bool is_src_in_dsts = std::any_of(dsts_abs.begin(), dsts_abs.end(), [&abs_src_witness] (const AbstractState* abs_dst) {return (*abs_dst) == abs_src_witness; });
    for (const AbstractState* abs_dst : dsts_abs) {_NE_may[res.first].insert(abs_dst); }
    if (is_src_in_dsts) { _NE_may[res.first].insert({res.first, res.second}); }

    const auto remove_redundant =
            [&res, &dsts_abs, is_src_in_dsts] (std::map<AbstractState*, std::vector<ConstAbsStateSet>>& dict)
            {
                if (dict.find(res.first) == dict.end()) return;
                for (ConstAbsStateSet &opt : dict[res.first])
                {
                    for (const AbstractState* it : dsts_abs) opt.erase(it);
                    if (is_src_in_dsts)
                    {
                        opt.erase(res.first);
                        opt.erase(res.second);
                    }
                }
            };

    remove_redundant(_E_must);
    remove_redundant(_E_may_over);

    assert(split_formulas.query.get_raw_formula().num_args() > 0);
    return { true, res.first, res.second, {split_formulas.query} };
}

std::pair<AbstractState*, AbstractState*> AbstractStructure::create_new_astates_and_update(AbstractState &abs_src_witness,
                                                      SplitFormulas& new_abs_state_formulas) {
    AbstractState& abs_no_successors = create_astate_from_astate_split(abs_src_witness, new_abs_state_formulas.generalized_formula);
    AbstractState& abs_residual = create_astate_from_astate_split(abs_src_witness, new_abs_state_formulas.remainder_formula);
    AbstractState* abs_src_witness_ptr = &abs_src_witness;

    std::set<AbstractState*> new_keys;
    new_keys.insert({&abs_no_successors, &abs_residual});
    inherit_values_in_dict<AbstractState*, std::vector<ConstAbsStateSet>>(_E_must, abs_src_witness_ptr, new_keys);
    inherit_values_in_dict<AbstractState*, std::vector<ConstAbsStateSet>>(_E_may_over, abs_src_witness_ptr, new_keys);

    const auto abs_state_set_updater = [&abs_src_witness_ptr, &new_keys] (std::pair<AbstractState*, std::vector<ConstAbsStateSet>> entry)
    {
        auto& entry_values = entry.second;
        for (auto& astate_set : entry_values)
        {
            if (astate_set.find(abs_src_witness_ptr) != astate_set.end())
            {
                astate_set.insert(new_keys.begin(), new_keys.end());
                astate_set.erase(abs_src_witness_ptr);
            }
        }
    };
    std::for_each(_E_must.begin(), _E_must.end(), abs_state_set_updater);
    std::for_each(_E_may_over.begin(), _E_may_over.end(), abs_state_set_updater);

    for_each(_NE_may.begin(), _NE_may.end(),
             [&abs_src_witness_ptr, &new_keys] (std::pair<AbstractState*, ConstAbsStateSet> entry)
          {
              if (entry.second.find(abs_src_witness_ptr) != entry.second.end())
              {
                  entry.second.insert(new_keys.begin(), new_keys.end());
                  entry.second.erase(abs_src_witness_ptr);
              }
          });

    for_each(_NE_may_over.begin(), _NE_may_over.end(), [&abs_src_witness_ptr, &new_keys]
    (std::pair<AbstractState*, std::vector<std::pair<ConstAbsStateSet, EEClosureResult>>> entry)
    {
        auto& entry_values = entry.second;
        for (auto& entry_value : entry_values)
        {
            if (entry_value.first.find(abs_src_witness_ptr) != entry_value.first.end())
            {
                entry_value.first.insert(new_keys.begin(), new_keys.end());
                entry_value.first.erase(abs_src_witness_ptr);
            }
        }
    });

    // Not deleting in order to not mess up the classifier
//    size_t erase_res = _abs_states.erase(abs_src_witness);
//    assert(erase_res == 1);

    return {&abs_no_successors, &abs_residual};
}

AbstractState &AbstractStructure::create_astate_from_astate_split(const AbstractState &astate, PropFormula sym_rep)
{
    const auto res =_abs_states.emplace(_kripke, astate.get_pos_labels(), astate.get_neg_labels(), _kripke.get_aps(), std::move(sym_rep));
    assert(res.second);

    return const_cast<AbstractState&>(*res.first);
}

RefinementResult
AbstractStructure::refine_all_successors(const UnwindingTree &to_close_node, AbstractState &abs_src_witness,
                                         const ConstAbsStateSet &dsts_abs, const bool is_tse_possible, ISatSolver& sat_solver) {
    AVY_MEASURE_FN;

    if (_E_may_over.find(&abs_src_witness) != _E_may_over.end() &&
        std::any_of(_E_may_over[&abs_src_witness].begin(), _E_may_over[&abs_src_witness].end(),
                    [&dsts_abs](const ConstAbsStateSet& astate_set)
                    {
                        // True iff astate_set \subseteq dsts_abs
                        return std::includes(dsts_abs.begin(), dsts_abs.end(), astate_set.begin(), astate_set.end());
                    }))
    {
        return {false, nullptr, nullptr, {}};
    }

    std::set<const PropFormula *> dst_abs_formulas;
    std::for_each(dsts_abs.begin(), dsts_abs.end(),
                  [&dst_abs_formulas] (const AbstractState* astate) { dst_abs_formulas.insert(&astate->get_formula()); });

    SplitFormulas split_formulas =
            FormulaSplitUtils::ex_neg(to_close_node.get_concrete_state().get_conjunct(),
                                      abs_src_witness.get_formula(), dst_abs_formulas, _kripke, true, sat_solver);

    if (is_tse_possible && OmgConfig::get<bool>("Trivial Split Elimination") && !split_formulas.remainder_formula.is_sat())
    {
        DEBUG_PRINT("TSE (REFINE ALL SUCCESSORS)\n");
        _E_must[&abs_src_witness].emplace_back(dsts_abs);
        _E_may_over[&abs_src_witness].emplace_back(dsts_abs);
        return {false, nullptr, nullptr, {}};
    }

    const std::pair<AbstractState*, AbstractState*> res = create_new_astates_and_update(abs_src_witness, split_formulas);

    const bool is_src_in_dsts = std::any_of(dsts_abs.begin(), dsts_abs.end(), [&abs_src_witness] (const AbstractState* abs_dst) {return (*abs_dst) == abs_src_witness; });

    if (is_src_in_dsts)
    {
        ConstAbsStateSet updated = dsts_abs;
        const size_t erase_res = updated.erase(&abs_src_witness);
        assert(erase_res == 1);
        updated.insert({res.first, res.second});
        _E_must[res.first].emplace_back(updated);
        _E_may_over[res.first].emplace_back(std::move(updated));

    } else
    {
        _E_must[res.first].emplace_back(dsts_abs);
        _E_may_over[res.first].emplace_back(dsts_abs);

    }

    return { true, res.first, res.second, {split_formulas.query} };
}

std::set<ConstAStateRef> AbstractStructure::get_astates_by_property(const CtlFormula &prop) {
    std::set<ConstAStateRef> to_ret;
    for (auto& it : _abs_states)
    {
        if (it.is_pos_labeled(prop)) to_ret.emplace(std::ref(it));
    }
    return to_ret;
}

AEClosureResult AbstractStructure::is_AE_closure(AbstractState &to_close, const std::set<ConstAStateRef> &close_with) {

    ConstAbsStateSet p_closers, p_non_closers;
    if (_NE_may.find(&to_close) != _NE_may.end()) {
        p_non_closers = _NE_may[&to_close];
    }
    for (const ConstAStateRef& cl : close_with) {
        if (p_non_closers.find(&cl.get()) == p_non_closers.end()) p_closers.insert(&cl.get());
    }

    const auto is_superset = [&to_close, &p_closers] (std::map<AbstractState*, std::vector<ConstAbsStateSet>>& dict) {
        if (dict.find(&to_close) != dict.end()) {
            for (const auto &closer_set : dict[&to_close]) {
                bool is_subset = std::includes(p_closers.begin(), p_closers.end(), closer_set.begin(),
                                               closer_set.end());
                if (is_subset)
                    return true;
            }
        }
        return false;
    };

    if (is_superset(_E_must) || is_superset(_E_may_over)) return {true, {}};


    AEClosureResult closure_result = FormulaInductiveUtils::is_AE_inductive(to_close, p_closers);

    if (closure_result.is_closed)
    {
        _E_must[&to_close].emplace_back(std::move(p_closers));
    }

    return closure_result;

}

