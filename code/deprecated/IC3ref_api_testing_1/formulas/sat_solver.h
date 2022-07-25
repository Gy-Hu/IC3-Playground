#pragma once
//
// Created by galls2 on 05/10/19.
//
#include <memory>
#include <set>
#include <boost/variant.hpp>
#include "../utils/omg_exception.h"
#include <functional>
#include <map>
#include <z3++.h>
//#include "../../cudd_install/include/cudd.h"
//#include "../../cudd-3.0.0/cplusplus/cuddObj.hh"

class PropFormula;

//DECLARE_OMG_EXCEPTION(SatSolverResultException)

enum class SatResult {
    FALSE, UNDEF, TRUE
};


struct Z3ExprComp
{
    bool operator()(const z3::expr& a, const z3::expr& b) const
    {
        return a.id() < b.id();
    }

};

typedef std::set<z3::expr, Z3ExprComp> Z3ExprSet;

struct SatSolverResult
{
public:
    SatSolverResult();
    SatSolverResult(const z3::model& model, const std::vector<z3::expr>& vars);
    explicit SatSolverResult(const std::map<z3::expr, Z3_lbool >& values);
    explicit SatSolverResult(std::map<z3::expr, SatResult, Z3ExprComp > values);

    SatResult get_value(const z3::expr& var) const;
    bool get_is_sat() const { return _is_sat; }
    z3::expr to_conjunct(const Z3ExprSet& to_flip = {}) const;

    void generalize_assignment(const z3::expr_vector& assertions);
private:
    bool _is_sat;
    std::map<z3::expr, SatResult, Z3ExprComp> _values;

};

class ISatSolver;
typedef std::function<std::unique_ptr<ISatSolver>(z3::context&)> SatSolverFactory;

class ISatSolver
{
public:
    virtual SatSolverResult solve_sat(const PropFormula& formula) = 0;
    virtual bool is_sat(const z3::expr& formula) = 0;

    virtual std::pair<int, SatSolverResult> inc_solve_sat(const PropFormula& formula, const std::vector<z3::expr>& may_flags, const std::vector<z3::expr>& must_flags) = 0;
    virtual std::vector<SatSolverResult> all_sat(const PropFormula& formula, const std::vector<z3::expr> &vars, bool complete_assignments=false) = 0;
    virtual z3::expr_vector get_unsat_core(const PropFormula& formula, z3::expr_vector& assumptions) = 0;
    static const std::map<std::string, SatSolverFactory> s_solvers;
    virtual void add(const z3::expr& expr) = 0;
    virtual ~ISatSolver() = default;
};

class Z3SatSolver : public ISatSolver
{
public:
    explicit Z3SatSolver(z3::context& context) : _solver(context) {}
    SatSolverResult solve_sat(const PropFormula& formula) override;
    bool is_sat(const z3::expr& formula) override;

    std::vector<SatSolverResult> all_sat(const PropFormula& formula, const std::vector<z3::expr> &vars, bool complete_assignments) override;
    std::pair<int, SatSolverResult> inc_solve_sat(const PropFormula& formula, const std::vector<z3::expr>& may_flags, const std::vector<z3::expr>& must_flags) override;
    std::pair<int, SatSolverResult> inc_solve_sat_flagged(const PropFormula& formula, const std::vector<z3::expr>& may_flags, const std::vector<z3::expr>& must_flags);

    z3::expr_vector get_unsat_core(const PropFormula& formula, z3::expr_vector& assumptions) override;
    virtual ~Z3SatSolver() override = default;
    virtual void add(const z3::expr& expr) override;
    static void add_assignments(std::vector<SatSolverResult> &assignments, const SatSolverResult& result, const std::vector<z3::expr> &vars, bool complete_assignments);

private:
    z3::solver _solver;

    static z3::expr get_blocking_clause(const SatSolverResult& model, const std::vector<z3::expr> &vector);


};

// class BddSatSolver : public ISatSolver
// {
// public:
//     explicit BddSatSolver(z3::context& ctx) : _z3_solver(ctx) { };
//     virtual SatSolverResult solve_sat(const PropFormula& formula) override;
//     virtual bool is_sat(const z3::expr& formula) override;

//     virtual std::pair<int, SatSolverResult> inc_solve_sat(const PropFormula& formula, const std::vector<z3::expr>& may_flags, const std::vector<z3::expr>& must_flags) override;
//     virtual std::vector<SatSolverResult> all_sat(const PropFormula& formula, const std::vector<z3::expr> &vars, bool complete_assignments=false) override;
//     virtual z3::expr_vector get_unsat_core(const PropFormula& formula, z3::expr_vector& assumptions) override;
//     virtual void add(const z3::expr& expr) override;
//     virtual ~BddSatSolver() = default;
// private:
//     Cudd _mgr;
//     Z3SatSolver _z3_solver;
// };