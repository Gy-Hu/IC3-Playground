#pragma once

#include <memory>
#include <functional>
#include <z3++.h>
#include "sat_solver.h"

class PropFormula;

class IEprSolver;
typedef std::function<std::unique_ptr<IEprSolver>(z3::context&)> EprSolverFactory;

class IEprSolver
{
public:
    virtual SatSolverResult solve_sat(const PropFormula& formula) = 0;

    static const std::map<std::string, EprSolverFactory> s_solvers;
    virtual ~IEprSolver() = default;
};

class Z3EprSolver : public IEprSolver
{
public:
    explicit Z3EprSolver(z3::context& context) : _solver(context) {}
    SatSolverResult solve_sat(const PropFormula& formula) override;

    ~Z3EprSolver() override = default;

private:
    z3::solver _solver;
};

