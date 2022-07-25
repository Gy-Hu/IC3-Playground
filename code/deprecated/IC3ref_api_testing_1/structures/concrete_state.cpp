//
// Created by galls2 on 04/10/19.
//

#include <cassert>
#include <formulas/sat_solver.h>
#include <utils/z3_utils.h>
#include <memory>
#include "concrete_state.h"
#include <algorithm>
#include <configuration/omg_config.h>
#include <utils/Stats.h>

using namespace avy;

ConcreteState::ConcreteState(const KripkeStructure& kripke, const z3::expr& conjunct)  : _kripke(kripke), _conjunct(conjunct)
{
#ifdef DEBUG
    std::vector<z3::expr> conj_vars = FormulaUtils::get_vars_in_formula(_conjunct);
    Z3ExprSet conj_vars_set(conj_vars.begin(), conj_vars.end());
    Z3ExprSet tr_ps_vars = expr_vector_to_set(_kripke.get_tr().get_vars_by_tag("ps"));

    assert(conj_vars_set.size()  == tr_ps_vars.size());
    for (const auto & it : conj_vars_set) {
        bool found = false;
        for (const auto &it2 : tr_ps_vars)
            if (z3::eq(it, it2)) found = true;
        assert(found);
    }
#endif
}

std::vector<ConcreteState>& ConcreteState::get_successors() {
    if (!_successors) compute_successors();
    return _successors.value();
}

void ConcreteState::compute_successors()
{
    AVY_MEASURE_FN;

    const PropFormula& tr = _kripke.get_tr();

    const z3::expr& raw_tr = tr.get_raw_formula();
    z3::context& ctx = raw_tr.ctx();
//    const z3::expr ns_raw_formula = _conjunct && raw_tr;
//    const z3::expr ns_raw_formula = (_conjunct && raw_tr).simplify();

    auto& raw_tr_deconst = const_cast<z3::expr&>(raw_tr);
    z3::expr_vector conjunt_literals = FormulaUtils::conjunct_to_literals(_conjunct);
    const z3::expr ns_raw_formula = raw_tr_deconst.substitute(tr.get_vars_by_tag("ps"), conjunt_literals).simplify();

    const auto& variables_map = tr.get_variables_map();

    PropFormula ns_formula(ns_raw_formula, variables_map);


    std::unique_ptr<ISatSolver> sat_solver = ISatSolver::s_solvers.at(OmgConfig::get<std::string>("Sat Solver"))(ctx);
    const z3::expr_vector& ns_vars = variables_map.at(std::string("ns"));
    std::vector<SatSolverResult> sat_results = sat_solver->all_sat(ns_formula, expr_vector_to_vector(ns_vars), true);
    std::vector<ConcreteState> successors;

    for (const auto& res : sat_results)
    {
        assert(res.get_is_sat());
        z3::expr conj = FormulaUtils::get_conj_from_sat_result(ctx, ns_vars, res);
        z3::expr named_conj = conj.substitute(tr.get_vars_by_tag("ns"), tr.get_vars_by_tag("ps"));
        successors.emplace_back(_kripke, std::move(named_conj));
    }
    _successors.emplace(successors);
}


std::ostream& operator<< (std::ostream& stream, const ConcreteState& concrete_state) {
    stream << concrete_state._conjunct.to_string();
    return stream;
}


#ifdef DEBUG
std::vector<bool> ConcreteState::to_bitvec() const
{
    z3::expr_vector vars = _kripke.get_tr().get_vars_by_tag("ps");
//    z3::solver solver(_kripke.get_tr().get_raw_formula().ctx());
    std::vector<bool> bits; bits.reserve(vars.size());
    for (size_t i = 0; i < vars.size(); ++i)
    {
        bool res = FormulaUtils::is_lit_agrees_with_conj(_conjunct, vars[i]);
        bits.push_back(res);
    }
    return bits;

}
#endif

void ConcreteState::aps_by_sat(CtlFormula::PropertySet& pos, CtlFormula::PropertySet& neg) const
{
    const z3::expr_vector& ps_vars = _kripke.get_tr().get_vars_by_tag("ps");
    const auto& aps = _kripke.get_aps();
    for (const CtlFormula* ap : aps)
    {
        size_t var_idx = _kripke.get_var_num_by_ap(ap->get_data());
        const z3::expr& var = ps_vars[var_idx];

        bool res = FormulaUtils::is_lit_agrees_with_conj(_conjunct, var);
        (res ? pos : neg).emplace(ap);
    }
}

PropFormula ConcreteState::get_bis0_formula() const {
    z3::context& ctx = _kripke.get_tr().get_raw_formula().ctx();
    const z3::expr_vector& ps_vars = _kripke.get_tr().get_vars_by_tag("ps");
    if (_kripke.get_aps().size() > 1) {
        z3::expr_vector bis0_parts(ctx);
        for (const CtlFormula *ap : _kripke.get_aps())
        {
            const size_t var_idx = _kripke.get_var_num_by_ap(ap->get_data());
            const z3::expr& var = ps_vars[var_idx];
            const bool is_pos_value = FormulaUtils::is_lit_agrees_with_conj(_conjunct, var);
            bis0_parts.push_back(is_pos_value ? var : (!var));
        }
        z3::expr raw_bis0 = z3::mk_and(bis0_parts);

        PropFormula bis0(raw_bis0, {{"ps",  ps_vars},
                                    {"in0", _kripke.get_tr().get_vars_by_tag("in0")}});
        return bis0;
    }
    else
    {
        assert(!_kripke.get_aps().empty());
        const CtlFormula* ap = *_kripke.get_aps().begin();
        const size_t var_idx = _kripke.get_var_num_by_ap(ap->get_data());
        const z3::expr& var = ps_vars[var_idx];
//        bool is_pos_value = z3::eq(m.eval(var), ctx.bool_val(true));
        const bool is_pos_value = FormulaUtils::is_lit_agrees_with_conj(_conjunct, var);

        PropFormula bis0(is_pos_value ? var : (!var), {{"ps",  ps_vars},
                                    {"in0", _kripke.get_tr().get_vars_by_tag("in0")}});
        return bis0;
    }
}

std::set<std::string> ConcreteState::string_sat_aps() const {
    std::set<std::string> sat_strs;

    const z3::expr_vector& ps_vars = _kripke.get_tr().get_vars_by_tag("ps");
    for (const CtlFormula* ap : _kripke.get_aps())
    {
        const size_t var_idx = _kripke.get_var_num_by_ap(ap->get_data());
        const z3::expr& var = ps_vars[var_idx];
        const bool res = FormulaUtils::is_lit_agrees_with_conj(_conjunct, var);
        if (res)
            sat_strs.insert(ap->get_data());
    }
    return sat_strs;
}

bool ConcreteState::operator==(const ConcreteState &other) const {
    return z3::eq(other._conjunct, _conjunct);
}

bool ConcreteState::operator!=(const ConcreteState &other) const {
    return !(*this == other);
}

const z3::expr &ConcreteState::get_conjunct() const {
    return _conjunct;
}

#ifdef DEBUG
std::string ConcreteState::to_bitvec_str() const {
    const auto bitvec = to_bitvec();
    std::string res;
    for (bool b : bitvec) res += (b ? "1 " : "0 ");
    return res;
}
#endif