//
// Created by galls2 on 05/10/19.
//

#include <algorithm>
#include <set>
#include <utils/z3_utils.h>
#include <utils/bdd_utils.h>
#include "sat_solver.h"
#include <utils/Stats.h>

using namespace avy;

SatSolverResult Z3SatSolver::solve_sat(const PropFormula &formula) {
    const z3::expr& raw_formula = formula.get_raw_formula().simplify();
    _solver.add(raw_formula);
    const z3::check_result sat_res = _solver.check();
    if (sat_res == z3::unsat) return SatSolverResult();
    else if (sat_res == z3::sat) return SatSolverResult(_solver.get_model(), formula.get_all_variables());
    else { assert(sat_res == z3::unknown); throw SatSolverResultException("SAT result is unknown"); }
}

std::vector<SatSolverResult> Z3SatSolver::all_sat(const PropFormula &formula, const std::vector<z3::expr>& vars, bool complete_assignments = false ) {
    std::vector<SatSolverResult> assignments;
    const z3::expr &raw_formula = formula.get_raw_formula().simplify();
    z3::solver solver(raw_formula.ctx());

    solver.add(raw_formula);
    while (solver.check() == z3::sat)
    {
        z3::model m = solver.get_model();

        SatSolverResult res(m, vars);
        const auto& assertions = solver.assertions();
        res.generalize_assignment(assertions);

        add_assignments(assignments ,res, vars, complete_assignments);
        z3::expr blocking_clause = get_blocking_clause(res, vars);
        solver.add(blocking_clause);
    }
    return assignments;
}

z3::expr Z3SatSolver::get_blocking_clause(const SatSolverResult& res, const std::vector<z3::expr> &var_vector) {
    z3::context& ctx = var_vector.begin()->ctx();
    z3::expr_vector literals(ctx);
    for (const z3::expr& var : var_vector)
    {
        const auto res_value = res.get_value(var);
        if (res_value != SatResult::UNDEF)
        {
            literals.push_back((res_value == SatResult::TRUE) ? (!var) : (var));
        }
    }

    return z3::mk_or(literals);
}

void Z3SatSolver::add_assignments(std::vector<SatSolverResult> &assignemnts, const SatSolverResult& result,
                                  const std::vector<z3::expr> &vars, bool complete_assignments) {
    assert(result.get_is_sat());
    if (!complete_assignments) {
        assignemnts.push_back(result);
        return;
    }
    else
    {
        std::set<size_t> undef_idxs;
        for (size_t i = 0; i < vars.size(); ++i) if (result.get_value(vars[i]) == SatResult::UNDEF) undef_idxs.insert(i);
        const ssize_t iter_max = (1U << undef_idxs.size());
#ifdef DEBUG
        assert(iter_max >= 0);
#endif
        for (size_t i = 0; i < ((size_t)iter_max); ++i)
        {
            size_t undef_idx = 0;
            std::map<z3::expr, SatResult, Z3ExprComp> vals;
            for (size_t j = 0; j < vars.size(); ++j)
            {
                if (undef_idxs.find(j) == undef_idxs.end()) {
                    vals.emplace(vars[j], result.get_value(vars[j]));
                }
                else
                {
                    const bool is_true_val = (i & (1U << undef_idx)) > 0;
                    undef_idx++;
                    vals.emplace(vars[j], is_true_val ? SatResult::TRUE : SatResult::FALSE);
                }
            }
            assignemnts.emplace_back(std::move(vals));
        }
    }
}

std::pair<int, SatSolverResult> Z3SatSolver::inc_solve_sat(const PropFormula& formula, const std::vector<z3::expr>& may_flags, const std::vector<z3::expr>& must_flags)
{

    const z3::expr &raw_formula = formula.get_raw_formula();
    _solver.add(raw_formula);

    z3::expr_vector assumptions(raw_formula.ctx());
    for (const auto& must_flag : must_flags) assumptions.push_back(must_flag);

    size_t may_flag_number = 0;
    bool found = false;
    SatSolverResult sat_solver_result;

    const auto all_vars = formula.get_all_variables();
    while (may_flag_number < may_flags.size())
    {
        assumptions.push_back(may_flags[may_flag_number]);
        auto sat_res = _solver.check(assumptions);
        assumptions.pop_back();
        if (sat_res == z3::sat)
        {
            sat_solver_result = SatSolverResult(_solver.get_model(), all_vars);
            found = true;
            break;
        }
        else
            {
            ++may_flag_number;
        }
    }

    for (const auto& may_flag : may_flags) _solver.add(!may_flag);
    for (const auto& must_flag : must_flags)  _solver.add(!must_flag);

    return {(found ? may_flag_number : -1), sat_solver_result};
}

z3::expr_vector Z3SatSolver::get_unsat_core(const PropFormula& formula, z3::expr_vector& assumptions)
{
    AVY_MEASURE_FN;

    const z3::expr& raw_formula = formula.get_raw_formula();
    _solver.add(raw_formula);
    const z3::check_result sat_res = _solver.check(assumptions);
    assert(sat_res == z3::check_result::unsat);

    //   std::cout << _solver.check(assumptions) << std::endl;
    z3::expr_vector unsat_core = _solver.unsat_core(); // TODO go over literals and see what we can kick out
    // TODO check if it acutally removes somethings
    return unsat_core;
}

bool Z3SatSolver::is_sat(const z3::expr &raw_formula) {
    _solver.add(raw_formula);
    const z3::check_result sat_res = _solver.check();
    if (sat_res == z3::unsat) return false;
    else if (sat_res == z3::sat) return true;
    else { assert(sat_res == z3::unknown); throw SatSolverResultException("SAT result is unknown"); }
}

void Z3SatSolver::add(const z3::expr &expr)
{
    _solver.add(expr);
}

std::pair<int, SatSolverResult>
Z3SatSolver::inc_solve_sat_flagged(const PropFormula &formula, const std::vector<z3::expr> &may_flags,
                                   const std::vector<z3::expr> &must_flags)
{
    // TODO remove this function after making sure it's identical to the prev one
    const z3::expr &raw_formula = formula.get_raw_formula();
    _solver.add(raw_formula);

    z3::expr_vector assumptions(raw_formula.ctx());
    for (const auto& must_flag : must_flags) assumptions.push_back(must_flag);

    size_t may_flag_number = 0;
    bool found = false;
    SatSolverResult sat_solver_result;

    const auto all_vars = formula.get_all_variables();
    while (may_flag_number < may_flags.size())
    {
        assumptions.push_back(may_flags[may_flag_number]);
        const auto sat_res = _solver.check(assumptions);
        assumptions.pop_back();
        if (sat_res == z3::sat)
        {
            sat_solver_result = SatSolverResult(_solver.get_model(), all_vars);
            found = true;
            break;
        }
        else
            {
            ++may_flag_number;
        }
    }

    for (const auto& may_flag : may_flags) _solver.add(!may_flag);
    for (const auto& must_flag : must_flags)  _solver.add(!must_flag);

    return {(found ? may_flag_number : -1), sat_solver_result};
}


SatSolverResult::SatSolverResult() : _is_sat(false) { }

SatSolverResult::SatSolverResult(const z3::model& model, const std::vector<z3::expr>& vars) : _is_sat(true)
{
    for (const auto& var : vars)
    {
        SatResult var_value = Z3_val_to_sat_result(model.eval(var).bool_value());
        _values.emplace(var, var_value);
    }
}

SatSolverResult::SatSolverResult(const std::map<z3::expr, Z3_lbool> &values) : _is_sat(true)
{
    for (const auto& it : values)
        _values.emplace(it.first, Z3_val_to_sat_result(it.second));
}


SatResult SatSolverResult::get_value(const z3::expr& var ) const {
    if (!_is_sat) throw SatSolverResultException("Formula is unsat");
    const auto res = _values.find(var);
    if (res == _values.end())
    {
        throw SatSolverResultException("Variables not in assignment");
    }
    return res->second;
}

z3::expr SatSolverResult::to_conjunct(const Z3ExprSet& to_flip) const {
    z3::context& ctx = _values.begin()->first.ctx();
    z3::expr_vector lits(ctx);
    for (const auto & value : _values) {
        if (value.second != SatResult::UNDEF) {
            const bool is_to_flip = to_flip.find(value.first) != to_flip.end();
            lits.push_back((value.second == (is_to_flip ? SatResult::FALSE : SatResult::TRUE))
                                    ? (value.first) : (!value.first));
        }
    }
    return z3::mk_and(lits);
}

SatSolverResult::SatSolverResult(std::map<z3::expr, SatResult, Z3ExprComp> values) : _is_sat(true), _values(std::move(values)) {}

void SatSolverResult::generalize_assignment(const z3::expr_vector& assertions) {
    z3::expr united_assertions = z3::mk_and(assertions);
    auto &ctx = assertions.ctx();

#ifdef DEBUG
    z3::solver assert_solver(ctx);
        assert_solver.add(united_assertions);
        assert_solver.add(to_conjunct());
        assert(assert_solver.check() == z3::sat);
#endif

    z3::solver solver(ctx);
    solver.add(united_assertions);

    unsigned flipped = 0;
    for (auto& var_it : _values) {
        if (var_it.second == SatResult::UNDEF) continue;

        z3::expr_vector flipped_conj_literals(ctx);

        for (const auto &var_assignment : _values) {
            if (z3::eq(var_assignment.first, var_it.first)) {
                flipped_conj_literals.push_back(
                        var_assignment.second == SatResult::FALSE ? var_assignment.first : (!var_assignment.first));
            } else {
                flipped_conj_literals.push_back(
                        var_assignment.second == SatResult::TRUE ? var_assignment.first : (!var_assignment.first));
            }
        }

        const auto sat_res = solver.check(flipped_conj_literals);
        if (sat_res == z3::sat) {
            const auto& model = solver.get_model();
            bool can_flip = true;
            for (const auto& it_yakir : _values)
            {
                if (it_yakir.second == SatResult::UNDEF && model.eval(it_yakir.first).bool_value() != Z3_L_UNDEF )
                {
                    can_flip = false; break;
                }
            }
            if (can_flip) {
                flipped++;
                //        std::cout << "GEN CONDUCTED" << std::endl;
                var_it.second = SatResult::UNDEF;
            }
        }
    }
//    if (flipped) std::cout << "Flipped: " << flipped << std::endl;
}

const std::map<std::string, SatSolverFactory> ISatSolver::s_solvers =
        {
                {"z3", [](z3::context& ctx) { return std::make_unique<Z3SatSolver>(ctx); }},
                {"bdd", [](z3::context& ctx) { return std::make_unique<BddSatSolver>(ctx); }}

        };

SatSolverResult BddSatSolver::solve_sat(const PropFormula &formula) {
    return _z3_solver.solve_sat(formula);

}

bool BddSatSolver::is_sat(const z3::expr &formula) {
    return _z3_solver.is_sat(formula);
}

std::pair<int, SatSolverResult>
BddSatSolver::inc_solve_sat(const PropFormula &formula, const std::vector<z3::expr> &may_flags, const std::vector<z3::expr>& must_flags) {
    return _z3_solver.inc_solve_sat_flagged(formula, may_flags, must_flags);

}

z3::expr_vector BddSatSolver::get_unsat_core(const PropFormula &formula, z3::expr_vector &assumptions) {
    return _z3_solver.get_unsat_core(formula, assumptions);

}

std::vector<SatSolverResult>
BddSatSolver::all_sat(const PropFormula &formula, const std::vector<z3::expr> &vars, bool complete_assignments) {

    AVY_MEASURE_FN;

    std::vector<SatSolverResult> uncompleted_assignments;

    std::map<z3::expr, size_t, Z3ExprComp> var_index_mapping;

    const auto& all_vars = formula.get_all_variables();

    for (size_t i = 0; i < all_vars.size(); ++i)
    {
        const auto& var = all_vars[i];
        var_index_mapping[var] = i+1;
    }

    std::vector<size_t> important_var_indices;
    important_var_indices.reserve(vars.size());

    for (const auto& important_var : vars)
    {
        important_var_indices.push_back(var_index_mapping[important_var]);
    }


    const auto res_bdd = BddUtils::expr_to_bdd(_mgr, formula.get_raw_formula(), var_index_mapping);
 //   BddUtils::bdd_to_dot(_mgr, res_bdd, "initial_states.dot", 1, NULL);
    const auto paths = BddUtils::all_sat(_mgr, res_bdd);

    for (const auto& path : paths)
    {
        std::map<z3::expr, SatResult, Z3ExprComp > values;
        for (const auto& v : vars) values[v] = SatResult::UNDEF;

        for (int16_t literal : path)
        {
            const size_t abs_literal = std::abs(literal);

            const auto literal_it = std::find(important_var_indices.begin(), important_var_indices.end(), abs_literal);
            if (literal_it == important_var_indices.end()) continue;

            const auto& var = all_vars[abs_literal - 1];
            values[var] = literal > 0 ? SatResult::TRUE : SatResult::FALSE;
        }

        uncompleted_assignments.emplace_back(std::move(values));
    }

    if (!complete_assignments) return uncompleted_assignments;

    std::vector<SatSolverResult> completed_assignments;
    for (const auto& uncompleted_assignment : uncompleted_assignments)
    {
        Z3SatSolver::add_assignments(completed_assignments ,uncompleted_assignment, vars, true);
    }

    return completed_assignments;
}

void BddSatSolver::add(const z3::expr &expr)
{
    _z3_solver.add(expr);
}


