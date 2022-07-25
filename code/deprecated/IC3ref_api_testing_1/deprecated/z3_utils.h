#pragma once

#include <z3++.h>
#include <vector>
#include <set>
// #include <formulas/sat_solver.h>
// #include <abstraction/abstract_structure.h>
// #include "omg_utils.h"

class AbstractState;
class UnwindingTree;
class ConcretizationResult;


//DECLARE_OMG_EXCEPTION(Z3UtilException)

class FormulaUtils
{
public:
    static z3::expr negate(const z3::expr& expr);

    static z3::expr get_conj_from_sat_result(z3::context &ctx, const z3::expr_vector &conj_vars,
                                                     const SatSolverResult &sat_result);

    static std::vector<z3::expr> get_vars_in_formula(z3::expr const & e);

    static bool is_cstate_conjunct(const z3::expr& f);
    static bool is_conj_contained(const z3::expr& big_conj, const z3::expr& small_conj);
    static bool is_lit_agrees_with_conj(const z3::expr& conj, const z3::expr& var);
    static z3::expr_vector conjunct_to_literals(const z3::expr& expr);
    static bool are_two_conj_sat(const z3::expr& small_conj, const z3::expr& big_conj);
};

z3::expr to_var(z3::context& ctx, size_t val);

template <typename T>
z3::expr_vector iterable_to_expr_vec(z3::context& ctx, const T& iterable);

z3::expr_vector vec_to_expr_vec(z3::context& ctx, const std::vector<z3::expr>& vec);

template <typename IterableType1, typename IterableType2>
bool is_contained_z3_containers(const IterableType1& iter1, const IterableType2& iter2)
{
    return std::all_of(iter1.begin(), iter1.end(), [&iter2] (const z3::expr& it1)
    {
        return std::any_of(iter2.begin(), iter2.end(), [it1] (const z3::expr& it2)
        {
            return z3::eq(it1, it2);
        });

    });
}

template <typename T>
std::set<T> vector_to_set_debug(std::vector<T> vec);


template <typename VectorType>
Z3ExprSet expr_vector_to_set(const VectorType& expr_vec)
{
    Z3ExprSet s;
    for (size_t i = 0;i<expr_vec.size(); ++i) s.insert(expr_vec[i]);
    return s;
}

std::vector<z3::expr> expr_vector_to_vector(const z3::expr_vector& expr_vec);

std::string expr_vector_to_string(const z3::expr_vector& expr_vec);

SatResult Z3_val_to_sat_result(Z3_lbool v);


struct EEClosureResult;
struct AEClosureResult;

class FormulaInductiveUtils
{
public:
    static EEClosureResult is_EE_inductive(AbstractState& to_close, const ConstAbsStateSet& close_with);
    static EEClosureResult is_EE_inductive_inc(const PropFormula& skeleton, AbstractState& to_close, ISatSolver& solver, const std::map<const AbstractState*, z3::expr>& astate_flags);

    static PropFormula create_EE_inductive_formula_skeleton(AbsStateSet abs_lead, const std::set<ConstAStateRef> &close_with, std::map<const AbstractState*, z3::expr>& astate_flags);
    static AEClosureResult is_AE_inductive(AbstractState& to_close, const ConstAbsStateSet& close_with);

    static ConcretizationResult concrete_transition_to_abs(const std::unordered_set<UnwindingTree*>& src_nodes, const AbstractState& astate, ISatSolver& sat_solver);
};

struct SplitFormulas
{
    PropFormula query;
    PropFormula generalized_formula;
    PropFormula remainder_formula;
};

class FormulaSplitUtils
{
public:
    static SplitFormulas ex_pos(const z3::expr& state_conj, const PropFormula& src_astate_f,
            const std::set<const PropFormula*>& dsts_astates_f, const KripkeStructure& kripke, ISatSolver& sat_solver);
    static SplitFormulas ex_neg(const z3::expr& state_conj, const PropFormula& src_astate_f,
          const std::set<const PropFormula*>& dsts_astates_f, const KripkeStructure& kripke, const bool is_negate_dsts, ISatSolver& sat_solver);
private:
    static void add_flags_to_conj(const z3::expr &conj, z3::expr_vector &assumptions,
                      z3::expr_vector &assertions,
                      std::map<z3::expr, unsigned int, Z3ExprComp> &assumptions_map,
                      const std::string &assumption_prefix);

    static z3::expr_vector get_assertions_from_unsat_core(const z3::expr &state_conj, z3::context &ctx,
                                                          std::map<z3::expr, unsigned int, Z3ExprComp> &assumptions_map,
                                                          const z3::expr_vector &unsat_core);

    static z3::expr merge_dst_astate_formulas(const std::set<const PropFormula *> &dsts_astates_f, const PropFormula& tr);
    static void find_proving_inputs(const z3::expr& state_conj, const PropFormula& tr, z3::expr& dst, z3::expr_vector& input_values);

    static SplitFormulas
    get_split_formulas(const z3::expr &state_conj, const PropFormula &src_astate_formula, const PropFormula &tr,
                       z3::expr_vector &assumptions,
                       std::map<z3::expr, unsigned int, Z3ExprComp> &assumptions_map, const z3::expr &final_assumption,
                       const PropFormula &formula_to_check, ISatSolver& sat_solver);


    static constexpr char s_ex_neg_state_conj_str[] = "EX_NEG_STATE_CONJ";
    static constexpr char s_ex_neg_fin_flag_str[] = "EX_NEG_FIN";
    static constexpr char s_ex_pos_state_conj_str[] = "EX_POS_STATE_CONJ";
    static constexpr char s_ex_pos_input_conj_str[] = "EX_POS_INPUT_CONJ";
    static constexpr char s_ex_pos_fin_flag_str[] = "EX_POS_FIN";


};