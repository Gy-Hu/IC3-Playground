//
// Created by galls2 on 29/09/19.
//

#include <utils/z3_utils.h>
#include <formulas/sat_solver.h>
#include <configuration/omg_config.h>
#include "kripke_structure.h"
#include <utils/Stats.h>

using namespace avy;

const std::vector<ConcreteState>& KripkeStructure::get_initial_states()
{
    AVY_MEASURE_FN;
    if (_initial_states.empty()) {
        z3::context &ctx = _transitions.get_raw_formula().ctx();

        std::unique_ptr<ISatSolver> solver = ISatSolver::s_solvers.at(OmgConfig::get<std::string>("Sat Solver"))(ctx);
        const auto &ps_vars = _transitions.get_vars_by_tag("ps");
        std::map<std::string, z3::expr_vector> mp = {{"ps", ps_vars}};
        PropFormula p(_init_formula, mp);
        std::vector<SatSolverResult> results = solver->all_sat(p, expr_vector_to_vector(ps_vars), true);

        for (const auto &result : results) {
            _initial_states.emplace_back(*this, result.to_conjunct());
        }
    }
    return _initial_states;
}

KripkeStructure::KripkeStructure(PropFormula tr, CtlFormula::PropertySet aps, const z3::expr &state_f,
        const z3::expr &init_f, const std::map<std::string, size_t>& ap_to_var_idx)
: _transitions(std::move(tr)), _aps(std::move(aps)), _state_formula(state_f), _init_formula(init_f), _ap_to_var_idx(ap_to_var_idx)
{ }

size_t KripkeStructure::get_var_num_by_ap(const std::string &ap_text) const {
    if (_ap_to_var_idx.find(ap_text) == _ap_to_var_idx.end())
    {
        throw AtomicPropositionDoesNotExist(ap_text.data());
    }
    return _ap_to_var_idx.at(ap_text);
}

const CtlFormula::PropertySet &KripkeStructure::get_aps() const {
    return _aps;
}

const PropFormula &KripkeStructure::get_tr() const {
    return _transitions;
}

const z3::expr &KripkeStructure::get_state_formula() const {
    return _state_formula;
}
