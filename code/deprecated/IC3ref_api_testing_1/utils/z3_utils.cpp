//
// Created by galls2 on 08/10/19.
//

#include <unordered_set>
#include "z3_utils.h"
#include "version_manager.h"
#include "Stats.h"
#include <formulas/epr_solver.h>
#include <model_checking/omg_model_checker.h>
#include <structures/kripke_structure.h>

using namespace avy;

z3::expr to_var(z3::context& ctx, size_t val)
{
    return ctx.bool_const(VersionManager::new_version(val).data());
}

template <typename T>
z3::expr_vector iterable_to_expr_vec(z3::context& ctx, const T& iterable)
{
    z3::expr_vector expr_vector(ctx);
    for (const auto& it : iterable) expr_vector.push_back(it);
    return expr_vector;
}


std::string expr_vector_to_string(const z3::expr_vector& expr_vec)
{
    std::string res;
    for (unsigned i = 0; i < expr_vec.size(); ++i)
    {
    res += expr_vec[i].to_string() +"  ";
    }

    return res;
}

z3::expr_vector vec_to_expr_vec(z3::context& ctx, const std::vector<z3::expr>& vec)
{
    return iterable_to_expr_vec<std::vector<z3::expr>>(ctx, vec);
}


std::vector<z3::expr> expr_vector_to_vector(const z3::expr_vector& expr_vec)
{
    std::vector<z3::expr> s;
    for (size_t i = 0;i<expr_vec.size(); ++i) s.push_back(expr_vec[i]);
    return s;
}

SatResult Z3_val_to_sat_result(Z3_lbool v) {
    switch (v) {
        case Z3_lbool::Z3_L_UNDEF:
            return SatResult::UNDEF;
        case Z3_lbool::Z3_L_FALSE:
            return SatResult::FALSE;
        case Z3_lbool::Z3_L_TRUE:
            return SatResult::TRUE;
        default:
            throw(SatSolverResultException("Illegal SAT value"));
    }
}


EEClosureResult
FormulaInductiveUtils::is_EE_inductive(AbstractState &to_close, const ConstAbsStateSet &close_with) {
    const KripkeStructure& kripke = to_close.get_kripke();
    const PropFormula& tr = kripke.get_tr();

    const z3::expr_vector& ps_tr = tr.get_vars_by_tag("ps"), ns_tr = tr.get_vars_by_tag("ns"),
        in_0 = tr.get_vars_by_tag("in0"), in_1 = tr.get_vars_by_tag("in1");

    PropFormula src_formula = to_close.get_formula();
    z3::expr src_part = src_formula.get_raw_formula().substitute(src_formula.get_vars_by_tag("ps"), ps_tr)
                             .substitute(src_formula.get_vars_by_tag("in0"), in_0);

    z3::expr_vector dsts(ps_tr.ctx());
    for (const auto & closer : close_with)
    {
        PropFormula dst = closer->get_formula();
        z3::expr dst_raw_formula =
                dst.get_raw_formula()
                                 .substitute(dst.get_vars_by_tag("ps"), ns_tr)
                                 .substitute(dst.get_vars_by_tag("in0"), in_1);
        dsts.push_back(dst_raw_formula);
    }

    z3::expr dst_part = !z3::mk_or(dsts);

    z3::expr inductive_raw_formula = src_part && tr.get_raw_formula() && dst_part;
    PropFormula inductive_formula(inductive_raw_formula, {{"ps", ps_tr}, {"ns", ns_tr}});
    std::unique_ptr<ISatSolver> solver = ISatSolver::s_solvers.at(OmgConfig::get<std::string>("Sat Solver"))(ps_tr.ctx());
    SatSolverResult sat_res = solver->solve_sat(inductive_formula);
    if (!sat_res.get_is_sat()) // if the formula is UNSAT, there is NO cex to the inductiveness, so we have inductiveness
    {
        return {true, {}, {}};
    }
    else
    {
        z3::expr cstate_conj = FormulaUtils::get_conj_from_sat_result(ps_tr.ctx(), ps_tr, sat_res);
        auto cstate_src = ConcreteState(kripke, cstate_conj);
        z3::expr nstate_conj = FormulaUtils::get_conj_from_sat_result(ps_tr.ctx(), ns_tr, sat_res).substitute(ns_tr, ps_tr);
        auto nstate_src = ConcreteState(kripke, nstate_conj);
        return {false, cstate_src, nstate_src};
    }
}

ConcretizationResult
FormulaInductiveUtils::concrete_transition_to_abs(const std::unordered_set<UnwindingTree *> &src_nodes,
                                                  const AbstractState &astate, ISatSolver& sat_solver) {
    const KripkeStructure &kripke = astate.get_kripke();
    const PropFormula &tr = kripke.get_tr();
    z3::context &ctx = tr.get_ctx();

    const z3::expr_vector& ps_tr = tr.get_vars_by_tag("ps"), ns_tr = tr.get_vars_by_tag("ns"),
            in_0 = tr.get_vars_by_tag("in0"), in_1 = tr.get_vars_by_tag("in1");

    PropFormula astate_formula = astate.get_formula();
    const z3::expr dst_part = astate_formula.get_raw_formula()
            .substitute(astate_formula.get_vars_by_tag("ps"), ns_tr)
            .substitute(astate_formula.get_vars_by_tag("in0"), in_1);


    z3::expr_vector src_parts(ctx);
    std::vector<z3::expr> flags;

    const std::string SRC_KEY = "SRC_KEY";
    const std::string DST_KEY = "DST_KEY";
    for (const UnwindingTree* src_node : src_nodes)
    {
        const z3::expr &src_formula = src_node->get_concrete_state().get_conjunct();
        z3::expr flag = ctx.bool_const(VersionManager::next_version(SRC_KEY).data());

        z3::expr flagged_src = z3::implies(flag, src_formula);
        flags.push_back(flag);
        src_parts.push_back(flagged_src);
    }

    z3::expr dst_flag = ctx.bool_const(VersionManager::next_version(DST_KEY).data());
    src_parts.push_back(z3::implies(dst_flag, dst_part));
    z3::expr src = z3::mk_and(src_parts);

    const z3::expr& raw_formula = src;
    PropFormula is_tr_formula = PropFormula(raw_formula, {{"ps", ps_tr}, {"ns", ns_tr}});


    std::pair<int, SatSolverResult> res = sat_solver.inc_solve_sat(is_tr_formula, flags, {dst_flag});
    if (res.first < 0) {
        return ConcretizationResult();
    } else {
        auto first_node_it = src_nodes.begin();
        std::advance(first_node_it, static_cast<size_t>(res.first));
        z3::expr nstate_conj = FormulaUtils::get_conj_from_sat_result(ps_tr.ctx(), ns_tr, res.second).substitute(ns_tr, ps_tr);
        return ConcretizationResult(*first_node_it , ConcreteState(kripke, nstate_conj));
    }
}

AEClosureResult FormulaInductiveUtils::is_AE_inductive(AbstractState &to_close, const ConstAbsStateSet &close_with) {
    const KripkeStructure& kripke = to_close.get_kripke();
    const PropFormula& tr = kripke.get_tr();
    z3::context& ctx = tr.get_ctx();

    const z3::expr_vector& ps_tr = tr.get_vars_by_tag("ps"), ns_tr = tr.get_vars_by_tag("ns"),
            in_0 = tr.get_vars_by_tag("in0"), in_1 = tr.get_vars_by_tag("in1");

    PropFormula src_formula = to_close.get_formula();
    z3::expr src_part = src_formula.get_raw_formula().substitute(src_formula.get_vars_by_tag("ps"), ps_tr)
            .substitute(src_formula.get_vars_by_tag("in0"), in_0);

    z3::expr_vector dsts(ctx);
    for (const auto & closer : close_with)
    {
        PropFormula dst = closer->get_formula();
        z3::expr dst_raw_formula =
                dst.get_raw_formula()
                        .substitute(dst.get_vars_by_tag("ps"), ns_tr)
                        .substitute(dst.get_vars_by_tag("in0"), in_1);
        dsts.push_back(dst_raw_formula);
    }

    z3::expr dst_part = z3::mk_or(dsts);


    z3::expr inner_quantified = z3::implies(tr.get_raw_formula(), !dst_part);

    z3::expr_vector vars_to_quantify(ctx);
    for (size_t i = 0; i<ns_tr.size(); ++i) vars_to_quantify.push_back(ns_tr[i]);
    for (size_t i = 0; i<in_0.size(); ++i) vars_to_quantify.push_back(in_0[i]);

    z3::expr quantified_part = z3::forall(vars_to_quantify, inner_quantified); // in1 vars are not quanitifed as of the implication TR. Probably is true but possible BUG
    z3::expr inductive_raw_formula = kripke.get_state_formula() && src_part && quantified_part;

    PropFormula inductive_formula(inductive_raw_formula, {{"ps", ps_tr}});
    std::unique_ptr<IEprSolver> solver = IEprSolver::s_solvers.at(OmgConfig::get<std::string>("Epr Solver"))(ps_tr.ctx());
    SatSolverResult sat_res = solver->solve_sat(inductive_formula);
    if (!sat_res.get_is_sat()) // if the formula is UNSAT, there is NO cex to the inductiveness, so we have inductiveness
    {
        return {true, {}};
    }
    else
    {
        z3::expr cstate_conj = FormulaUtils::get_conj_from_sat_result(ps_tr.ctx(), ps_tr, sat_res);
        auto cstate_src = ConcreteState(kripke, cstate_conj);

        return {false, cstate_src};
    }
}

PropFormula FormulaInductiveUtils::create_EE_inductive_formula_skeleton(AbsStateSet abs_lead, const std::set<ConstAStateRef> &close_with, std::map<const AbstractState*, z3::expr>& astate_flags) // TODO why not constref
{
    AVY_MEASURE_FN;

    const KripkeStructure& kripke = (close_with.begin()->get()).get_kripke();
    const PropFormula& tr = kripke.get_tr();
    z3::context& ctx = tr.get_ctx();

    const z3::expr_vector& ps_tr = tr.get_vars_by_tag("ps"), ns_tr = tr.get_vars_by_tag("ns"),
            in_0 = tr.get_vars_by_tag("in0"), in_1 = tr.get_vars_by_tag("in1");


    z3::expr_vector astates_implications(ctx);
    for (const AbstractState* it : abs_lead)
    {
        PropFormula abs_formula = it->get_formula();
        z3::expr abs_implicant = abs_formula.get_raw_formula().substitute(abs_formula.get_vars_by_tag("ps"), ps_tr)
                .substitute(abs_formula.get_vars_by_tag("in0"), in_0);

        const std::string ABS_FLAG_FOR_EE = std::string("ABS_EE") + std::to_string(it->get_abs_idx());
        z3::expr flag = ctx.bool_const(VersionManager::next_version(ABS_FLAG_FOR_EE).data());
        astate_flags.emplace(it, flag);
        astates_implications.push_back(z3::implies(flag, abs_implicant));
    }
    z3::expr src_part = z3::mk_and(astates_implications);

    z3::expr_vector dsts(ctx);
    for (const auto & closer : close_with)
    {
        PropFormula dst = closer.get().get_formula();
        z3::expr dst_raw_formula =
                dst.get_raw_formula()
                        .substitute(dst.get_vars_by_tag("ps"), ns_tr)
                        .substitute(dst.get_vars_by_tag("in0"), in_1);
        dsts.push_back(dst_raw_formula);
    }

    z3::expr dst_part = !z3::mk_or(dsts);

    z3::expr inductive_raw_formula = src_part && dst_part; // && tr.get_raw_formula(); // && TR
    PropFormula inductive_formula(inductive_raw_formula, {{"ps", ps_tr}, {"ns", ns_tr}});
    return inductive_formula;

}

EEClosureResult
FormulaInductiveUtils::is_EE_inductive_inc(const PropFormula& skeleton, AbstractState& to_close, ISatSolver& solver, const std::map<const AbstractState*, z3::expr>& astate_flags)
{
    AVY_MEASURE_FN;

    const KripkeStructure& kripke = to_close.get_kripke();
    const PropFormula& tr = kripke.get_tr();

    z3::context& ctx = skeleton.get_ctx();

    const z3::expr_vector& ps_tr = tr.get_vars_by_tag("ps"), ns_tr = tr.get_vars_by_tag("ns"),
            in_0 = tr.get_vars_by_tag("in0"), in_1 = tr.get_vars_by_tag("in1");


    const AbstractState* astate_ptr = &const_cast<AbstractState&>(to_close);
    const z3::expr& astate_flag = astate_flags.at(astate_ptr);

    // create skeleton flag and send the solver the expressions SKELELTON_FLAG -> FLAG with a must flag of SKELETON_FLAG
    const std::string skeleton_flag_unique_name = VersionManager::next_version("EE_SKELETON_FLAG"); // TODO static constexpr
    z3::expr skeleton_flag = ctx.bool_const(skeleton_flag_unique_name.data());
    z3::expr raw_formula_to_solver = z3::implies(skeleton_flag, skeleton.get_raw_formula());

    PropFormula formula_to_solver(raw_formula_to_solver, skeleton.get_variables_map());
    auto res = solver.inc_solve_sat(formula_to_solver, {astate_flag}, {skeleton_flag});

    if (res.first == -1) // if the formula is UNSAT, there is NO cex to the inductiveness, so we have inductiveness
    {
        return {true, {}, {}};
    }
    else
    {
        SatSolverResult& sat_res = res.second;
        z3::expr cstate_conj = FormulaUtils::get_conj_from_sat_result(ps_tr.ctx(), ps_tr, sat_res);
        auto cstate_src = ConcreteState(kripke, cstate_conj);
        z3::expr nstate_conj = FormulaUtils::get_conj_from_sat_result(ps_tr.ctx(), ns_tr, sat_res).substitute(ns_tr, ps_tr);
        auto nstate_src = ConcreteState(kripke, nstate_conj);
        return {false, cstate_src, nstate_src};
    }

}


z3::expr FormulaUtils::negate(const z3::expr &expr) {
    return expr.is_not() ? expr.arg(0) : !expr;
}

z3::expr FormulaUtils::get_conj_from_sat_result(z3::context &ctx, const z3::expr_vector &conj_vars,
                                                const SatSolverResult &sat_result) {
    z3::expr_vector lits(ctx);
    for (size_t i = 0; i < conj_vars.size(); ++i) {
        z3::expr var = conj_vars[i];
        lits.push_back(sat_result.get_value(var) == SatResult::TRUE ? var : !var);
    }
    z3::expr conj = mk_and(lits);
    return conj;
}

std::vector<z3::expr> FormulaUtils::get_vars_in_formula(z3::expr const &e) {
    std::vector<z3::expr> vars;
    if (e.num_args() != 0) {
        unsigned num = e.num_args();
        for (unsigned i = 0; i < num; i++) {
            std::vector<z3::expr> sub_res = get_vars_in_formula(e.arg(i));
            vars.insert( vars.end(), sub_res.begin(), sub_res.end() );
        }
    }
    else {
        assert(e.is_bool());
        vars.push_back(e);
    }
    return vars;
}

bool FormulaUtils::is_cstate_conjunct(const z3::expr &f) {
    if (!f.is_and()) return false;
    for (unsigned int i = 0; i < f.num_args(); ++i) {
        if (!(f.arg(i).is_bool() || (f.arg(i).is_not() && f.arg(i).arg(0).is_bool())))
            return false;
    }
    return true;
}

bool FormulaUtils::is_lit_agrees_with_conj(const z3::expr &conj, const z3::expr &var) {
    for (unsigned int i = 0; i < conj.num_args(); ++i)
    {
        const z3::expr& current_lit = conj.arg(i);
        assert(current_lit.is_bool() || (current_lit.is_not() && current_lit.arg(0).is_bool()));
        if (current_lit.is_bool() && z3::eq(current_lit, var)) return true;
        else if (current_lit.is_not() && z3::eq(current_lit.arg(0), var)) return false;
    }
    assert(false);
}

bool FormulaUtils::is_conj_contained(const z3::expr &big_conj, const z3::expr &small_conj)
{
    AVY_MEASURE_FN;

    assert(big_conj.num_args() <= std::numeric_limits<uint16_t>::max() &&
           small_conj.num_args() <= std::numeric_limits<uint16_t>::max());

    // TODO optimize!!!!!!!!!!!!!!!!!!! from O(nm) to O(n+m)?
    for (uint16_t i = 0; i < small_conj.num_args(); ++i) {
        const z3::expr &v = small_conj.arg(i);
        for (uint16_t j = 0; j < small_conj.num_args(); j++) {
            if (z3::eq(big_conj.arg(j), v)) return true;
        }
    }
    return false;
}

z3::expr_vector FormulaUtils::conjunct_to_literals(const z3::expr &expr)
{
    z3::context& ctx = expr.ctx();

    z3::expr_vector to_return(ctx);

    assert(is_cstate_conjunct(expr));

    for (unsigned i = 0; i < expr.num_args(); ++i)
    {
        z3::expr to_insert = expr.arg(i).is_not() ? ctx.bool_val(false) : ctx.bool_val(true);
        to_return.push_back(to_insert);
    }

    return to_return;
}

bool FormulaUtils::are_two_conj_sat(const z3::expr & small_conj, const z3::expr& big_conj)
{
    AVY_MEASURE_FN;

    for (unsigned i = 0; i < small_conj.num_args(); ++i) {
        const z3::expr& small_lit = small_conj.arg(i);
        bool is_small_var_not = small_lit.is_not();
        const z3::expr& small_var = is_small_var_not ? small_lit.arg(0) : small_lit;
        for (unsigned j = 0; j < big_conj.num_args(); j++)
        {
            const z3::expr& big_lit = big_conj.arg(j);
            bool is_big_var_not = big_lit.is_not();
            const z3::expr& big_var = is_big_var_not ? big_lit.arg(0) : big_lit;
            if (z3::eq(small_var, big_var) && (is_small_var_not != is_big_var_not))
            {
                return false;
            }
        }
    }

    return true;
}

void FormulaSplitUtils::find_proving_inputs(const z3::expr& state_conj, const PropFormula& tr, z3::expr& dst, z3::expr_vector& input_values)
{
    z3::expr raw_formula_to_solve = state_conj && tr.get_raw_formula() && dst;
    PropFormula to_solve(raw_formula_to_solve, tr.get_variables_map());
    z3::context& ctx = tr.get_ctx();

    std::unique_ptr<ISatSolver> solver = ISatSolver::s_solvers.at(OmgConfig::get<std::string>("Sat Solver"))(ctx);

    SatSolverResult sat_result = solver->solve_sat(to_solve);
    assert(sat_result.get_is_sat());

    z3::expr_vector in0_vec = tr.get_vars_by_tag("in0");

    for (size_t in_i = 0; in_i < in0_vec.size(); ++in_i)
    {
        const z3::expr& in_var = in0_vec[in_i];
        SatResult in_var_val = sat_result.get_value(in_var);
        if (in_var_val == SatResult::TRUE) input_values.push_back(in_var);
        else if (in_var_val == SatResult::FALSE) input_values.push_back(!in_var);
    }
}

SplitFormulas
FormulaSplitUtils::ex_pos(const z3::expr &state_conj, const PropFormula &src_astate_f,
                          const std::set<const PropFormula *> &dsts_astates_f, const KripkeStructure& kripke, ISatSolver& sat_solver) {
    assert(FormulaUtils::is_cstate_conjunct(state_conj));

    const PropFormula &tr = kripke.get_tr();
    z3::context &ctx = state_conj.ctx();

#ifdef DEBUG
    Z3ExprSet ps_vars = expr_vector_to_set(tr.get_vars_by_tag("ps"));
    Z3ExprSet ps_vars_actual = expr_vector_to_set(FormulaUtils::get_vars_in_formula(state_conj));
    assert(is_contained_z3_containers(ps_vars_actual, ps_vars) && is_contained_z3_containers(ps_vars, ps_vars_actual));
#endif

    z3::expr_vector assumptions(ctx), assertions(ctx);
    std::map<z3::expr, unsigned int, Z3ExprComp> assumptions_map;

    add_flags_to_conj(state_conj, assumptions, assertions, assumptions_map, s_ex_pos_state_conj_str);
    z3::expr dst_formula_full = merge_dst_astate_formulas(dsts_astates_f, tr);

    z3::expr_vector input_values(ctx);
    FormulaSplitUtils::find_proving_inputs(state_conj, tr, dst_formula_full, input_values);
    z3::expr input_formula = z3::mk_and(input_values);
    add_flags_to_conj(input_formula, assumptions, assertions, assumptions_map, s_ex_pos_input_conj_str);

    z3::expr rest_of_formula = tr.get_raw_formula() && (!dst_formula_full);
    z3::expr final_assumption = ctx.bool_const(s_ex_pos_fin_flag_str);
    assumptions.push_back(final_assumption);
    assertions.push_back(z3::implies(final_assumption, rest_of_formula));

    PropFormula formula_to_check(z3::mk_and(assertions), tr.get_variables_map());

    SplitFormulas res = get_split_formulas(state_conj, src_astate_f, tr, assumptions, assumptions_map,
                                           final_assumption,
                                           formula_to_check, sat_solver);

    return res;
}

SplitFormulas
FormulaSplitUtils::ex_neg(const z3::expr &state_conj, const PropFormula &src_astate_f,
                          const std::set<const PropFormula *> &dsts_astates_f, const KripkeStructure &kripke, const bool is_negate_dsts, ISatSolver& sat_solver)
{
    AVY_MEASURE_FN;

    assert(FormulaUtils::is_cstate_conjunct(state_conj));

    const PropFormula &tr = kripke.get_tr();

#ifdef DEBUG
    Z3ExprSet ps_vars = expr_vector_to_set(tr.get_vars_by_tag("ps"));
    Z3ExprSet ps_vars_actual = expr_vector_to_set(FormulaUtils::get_vars_in_formula(state_conj));
    assert(is_contained_z3_containers(ps_vars_actual, ps_vars) && is_contained_z3_containers(ps_vars, ps_vars_actual));
#endif


    z3::context &ctx = state_conj.ctx();
    z3::expr_vector assumptions(ctx), assertions(ctx);
    std::map<z3::expr, unsigned int, Z3ExprComp> assumptions_map;

    add_flags_to_conj(state_conj, assumptions, assertions, assumptions_map, s_ex_neg_state_conj_str);

    z3::expr dst_formula_full = merge_dst_astate_formulas(dsts_astates_f, tr);
    if (is_negate_dsts)
    {
        dst_formula_full = !dst_formula_full;
    }

#ifdef DEBUG
    assert(Z3SatSolver(ctx).is_sat(dst_formula_full));
#endif

    z3::expr rest_of_formula = (tr.get_raw_formula() && dst_formula_full).simplify(); // TODO maybe substitute?

#ifdef DEBUG
    assert(Z3SatSolver(ctx).is_sat(rest_of_formula));
#endif

    z3::expr final_assumption = ctx.bool_const(s_ex_neg_fin_flag_str);
    assumptions.push_back(final_assumption);
    assertions.push_back(z3::implies(final_assumption, rest_of_formula));

    PropFormula formula_to_check(z3::mk_and(assertions), tr.get_variables_map());

    SplitFormulas res = get_split_formulas(state_conj, src_astate_f, tr, assumptions, assumptions_map,
                                           final_assumption,
                                           formula_to_check, sat_solver);
    return res;
}

SplitFormulas FormulaSplitUtils::get_split_formulas(const z3::expr &state_conj, const PropFormula &src_astate_formula,
                                                    const PropFormula &tr,
                                                    z3::expr_vector &assumptions,
                                                    std::map<z3::expr, unsigned int, Z3ExprComp> &assumptions_map,
                                                    const z3::expr &final_assumption,
                                                    const PropFormula &formula_to_check, ISatSolver& sat_solver)
{
    AVY_MEASURE_FN;
    z3::context& ctx = state_conj.ctx();


    z3::expr_vector unsat_core = sat_solver.get_unsat_core(formula_to_check, assumptions);

    z3::expr_vector assertions_selected(ctx);

#ifdef DEBUG
    bool exists_final_assumption = false;
    for (unsigned int i = 0; i < unsat_core.size(); ++i)
        if (eq(unsat_core[i], final_assumption)) {
            exists_final_assumption = true;
            break;
        }
    assert(exists_final_assumption);
#endif


    z3::expr_vector pos_assertions = get_assertions_from_unsat_core(state_conj, ctx, assumptions_map, unsat_core);
    z3::expr no_successor_part = mk_and(pos_assertions);

    assert(no_successor_part.is_and() && no_successor_part.num_args() > 0);

    // TODO change to A \cap C and A \cap (neg C) [[now it's A \cap C and A minus (A \cap C)
    z3::expr pos_split_part = (no_successor_part && src_astate_formula.get_raw_formula()).simplify();
    z3::expr neg_split_part = (src_astate_formula.get_raw_formula() && (!pos_split_part));

    const std::map<std::string, z3::expr_vector> abs_var_map = {
            {"ps", tr.get_vars_by_tag("ps")},
            {"in0", tr.get_vars_by_tag("in0")}
    };
    auto create_prop = [&abs_var_map](const z3::expr &raw_f) { return PropFormula(raw_f, abs_var_map); };
    SplitFormulas res = {PropFormula(no_successor_part, abs_var_map), PropFormula(pos_split_part, abs_var_map),
                         PropFormula(neg_split_part, abs_var_map)};

    return res;
}

z3::expr_vector FormulaSplitUtils::get_assertions_from_unsat_core(const z3::expr &state_conj, z3::context &ctx,
                                                                  std::map<z3::expr, unsigned int, Z3ExprComp> &assumptions_map,
                                                                  const z3::expr_vector &unsat_core) {
    z3::expr_vector pos_assertions(ctx);

    for (size_t i = 0 ;i < unsat_core.size(); ++i)
    {
        z3::expr unsat_core_item = unsat_core[i];
        if (assumptions_map.find(unsat_core_item) != assumptions_map.end())
        {
            z3::expr assertion = state_conj.arg(assumptions_map[unsat_core_item]);
            pos_assertions.push_back(assertion);
        }
    }
    return pos_assertions;
}


void
FormulaSplitUtils::add_flags_to_conj(const z3::expr &conj, z3::expr_vector &assumptions,
                                     z3::expr_vector &assertions,
                                     std::map<z3::expr, unsigned int, Z3ExprComp> &assumptions_map,
                                     const std::string &assumption_prefix)
 {
    AVY_MEASURE_FN;

     z3::context &ctx = conj.ctx();

     for (unsigned int i = 0; i < conj.num_args(); ++i)
    {
        const z3::expr &lit = conj.arg(i);
        z3::expr lit_assumption = ctx.bool_const(VersionManager::next_version(assumption_prefix).data());
        assumptions.push_back(lit_assumption);
        assertions.push_back(z3::implies(lit_assumption, lit));
        assumptions_map.emplace(lit_assumption, i);
    }
}


// TODO instead of tr just get the relevant expression vectors
z3::expr FormulaSplitUtils::merge_dst_astate_formulas(const std::set<const PropFormula *> &dsts_astates_f, const PropFormula& tr)
{
    AVY_MEASURE_FN;

    z3::context& ctx = tr.get_ctx();

    z3::expr_vector dsts(ctx);
    for (const PropFormula* const dst_formula : dsts_astates_f)
    {
#ifdef DEBUG
        Z3ExprSet ns_vars_actual = expr_vector_to_set(FormulaUtils::get_vars_in_formula(dst_formula->get_raw_formula()));
        assert(is_contained_z3_containers(ns_vars_actual, expr_vector_to_set(tr.get_vars_by_tag("ps"))));
#endif
        z3::expr dst_formula_raw = dst_formula->get_raw_formula();
        z3::expr dst_ns = dst_formula_raw.substitute(tr.get_vars_by_tag("ps"), tr.get_vars_by_tag("ns"));
        dsts.push_back(dst_ns);
    }

    z3::expr dst_formula_full = z3::mk_or(dsts).simplify();
    return dst_formula_full;
}

constexpr char FormulaSplitUtils::s_ex_neg_state_conj_str[];
constexpr char FormulaSplitUtils::s_ex_neg_fin_flag_str[];
constexpr char FormulaSplitUtils::s_ex_pos_state_conj_str[];
constexpr char FormulaSplitUtils::s_ex_pos_input_conj_str[];
constexpr char FormulaSplitUtils::s_ex_pos_fin_flag_str[];