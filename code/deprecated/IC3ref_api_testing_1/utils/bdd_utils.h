//
// Created by galls2 on 29.7.2020.
//

#ifndef OMG_CPP_BDD_UTILS_H
#define OMG_CPP_BDD_UTILS_H


#include <z3++.h>
#include <formulas/sat_solver.h>
#include "../../cudd-3.0.0/cplusplus/cuddObj.hh"


DECLARE_OMG_EXCEPTION(BddException)

struct BddCubeRep
{

};

class BddUtils {
public:
    typedef std::vector<int16_t> CubeRep;
    static BDD expr_to_bdd(Cudd& mgr, const z3::expr& expr, const std::map<z3::expr, size_t, Z3ExprComp>& var_mapping);
    static void bdd_to_dot(Cudd& mgr, const BDD& bdd, const std::string& write_path, size_t num_vars, char** names);
    static std::vector<CubeRep> all_sat(Cudd& mgr, const BDD& bdd);

private:
    static void all_sat(Cudd& mgr, const BDD& bdd, std::map<DdNode*, std::vector<CubeRep>>& node_cube_reps, const bool is_negate);

};


#endif //OMG_CPP_BDD_UTILS_H
