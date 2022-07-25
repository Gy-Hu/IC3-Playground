//
// Created by galls2 on 17/04/20.
//

#include "epr_solver.h"
#include "prop_formula.h"



const std::map<std::string, EprSolverFactory> IEprSolver::s_solvers =
        {
                {"z3", [](z3::context& ctx) { return std::make_unique<Z3EprSolver>(ctx); }}
        };

SatSolverResult Z3EprSolver::solve_sat(const PropFormula &formula) {
    const z3::expr& raw_formula = formula.get_raw_formula();
    _solver.add(raw_formula);
    z3::check_result sat_res = _solver.check();
    if (sat_res == z3::unsat) return SatSolverResult();
    else if (sat_res == z3::sat) return SatSolverResult(_solver.get_model(), formula.get_all_variables());
    else { assert(sat_res == z3::unknown); throw SatSolverResultException("EPR result is unknown"); }
}
