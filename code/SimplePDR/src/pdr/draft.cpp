
#include <pdr/IC3.h>

#include <memory>
#include <set>

namespace IC3 {

IC3::IC3(std::shared_ptr<Model::Model> M) {

    solver = new Solver::Solver();

    map1 = M->get_var_map1();
    map2 = M->get_var_map2();
    nmap = M->get_var_rel_map();

    for (unsigned int i = 0; i < (M->get_variables()).size(); ++i) {
        solver->add_symbol((M->get_variables())[i], Solver::Boolean);
    }

    // get pointer to initial states
    init = M->get_init();
    generate_string(init_str, init);
    init_str = "(assert " + init_str + ")";

    // get pointer to transition relation
    trans = M->get_trans();
    generate_string(trans_str, trans);
    trans_str = "(assert " + trans_str + ")";

    // get pointer to safety property
    prop = M->get_prop();
    generate_string(invar_str, prop);
    invar_str = "(assert " + invar_str + ")";
    generate_string(neg_invar_str, prop);
    neg_invar_str = "(assert (not " + neg_invar_str + "))";
}

bool IC3::prove() {

    std::vector<std::string> cnf_smt2;

    /***************** find 0-step counterexample ******************
     ************************ starts here **************************/

    solver->push(); // create solver stack

    // add init to solver
    solver->add_assertion(init_str);


    // add (not prop) to solver
    solver->add_assertion(neg_invar_str);

    // checks satisfiability of (I \wedge \not P)
    if (solver->check_sat() == Solver::sat)
        // TODO: extract witness when 0-step cex exists
        return false;
    solver->pop();  // destroy solver stack

    /***************** find 0-step counterexample ******************
     ************************* ends here ***************************/

    // first element of frame is init formula
    std::vector<std::shared_ptr<Clause>> temp;
    frames.push_back(temp); // adding dummy node

    unsigned int k = 1; // active frame number
    std::vector<std::shared_ptr<Clause>> m;
    frames.push_back(m); // add a new frame to the trace

    while (true) {

        /*********************** blocking phase **************************
         ************************* starts here ***************************/

        solver->push(); // create solver stack

        // get SMT2 string corresponding to frames[k]
        SMTLIB2::generate_smtlib2_from_clause(frames[k], cnf_smt2, map2,
                SMTLIB2::uncomp, NULL);


        // iterate over the SMT2 strings for each clause
        for (unsigned int i = 0; i < cnf_smt2.size(); ++i) {

            solver->add_assertion(cnf_smt2[i]); // add clause to solver
        }
        cnf_smt2.clear(); // clear strings

        // add (not prop) to solver
        solver->add_assertion(neg_invar_str);

        // checks satisfiability of (and frames[k] (not prop))
        while (solver->check_sat() == Solver::sat) {

            // get model corresponding to bad cube c
            std::vector<std::string> bad_cube = solver->get_model();
            solver->pop(); // destroy solver stack

            // convert bad cube to multiple clauses
            std::vector<std::shared_ptr<Clause>> c;
            //add generalized predecessor here to shrink the cube size
            /*
            WIP: Using unsat core and ternary simulation to shrink the cube size
            */
            SMTLIB2::generate_clause_from_smtlib2(c, bad_cube, map1, nmap->size());

            if (!check_proof_obligation(c, k)) {
                return false;
            }

            solver->push(); // create solver stack

            // get SMT2 string corresponding to frames[k]
            SMTLIB2::generate_smtlib2_from_clause(frames[k], cnf_smt2, map2,
                    SMTLIB2::uncomp, NULL);

            // iterate over the SMT2 strings for each clause
            for (unsigned int i = 0; i < cnf_smt2.size(); ++i) {

                solver->add_assertion(cnf_smt2[i]); // add clause to solver
            }
            cnf_smt2.clear(); // clear strings

            // add (not prop) to solver
            solver->add_assertion(neg_invar_str);
        }
        solver->pop();

        /*********************** blocking phase **************************
         ************************** ends here ****************************/

        /********************** propagation phase ************************
         ************************* starts here ***************************/

        k = k + 1;
        std::vector<std::shared_ptr<Clause>> n;
        frames.push_back(n); // add a new frame to the trace

        /* New solver stack created since trans is always present
         * in subsequent calls to Z3 (next for loop) */
        solver->push(); // create solver stack

        // add trans to solver
        solver->add_assertion(trans_str);

        // iterate over frames
        for (unsigned int i = 1; i < k; ++i) {
            std::vector<std::shared_ptr<Clause>> cl = frames[i];

            /* New solver stack created since frames[i] is present
             * in all iterations of the next for loop */
            solver->push(); // create solver stack

            // get SMT2 string corresponding to frames[i] = cl
            SMTLIB2::generate_smtlib2_from_clause(cl, cnf_smt2, map2,
                    SMTLIB2::uncomp, NULL);


            // iterate over the SMT2 strings for each clause
            for (unsigned int i = 0; i < cnf_smt2.size(); ++i) {
                solver->add_assertion(cnf_smt2[i]); // add clause to solver
            }
            cnf_smt2.clear(); // clear strings

            // Iterate over all clauses in frames[i];
            for (unsigned j = 0; j < cl.size(); ++j) {
                /* New solver stack created for adding cl[i] to solver */
                solver->push(); // create solver stack

                // get SMT2 string corresponding to cl[j]
                std::vector<std::shared_ptr<Clause>> m; // = new std::vector<Clause *>;
                m.push_back(cl[j]);
                SMTLIB2::generate_smtlib2_from_clause(m, cnf_smt2, map2,
                        SMTLIB2::uncomp, NULL);

                // iterate over the SMT2 strings for each clause
                for (unsigned int i = 0; i < cnf_smt2.size(); ++i) {
                    solver->add_assertion(cnf_smt2[i]); // add clause to solver
                }
                cnf_smt2.clear(); // clear strings

                // get SMT2 string corresponding to (not cl[j]')
                SMTLIB2::generate_smtlib2_from_clause(m, cnf_smt2, map2,
                        SMTLIB2::comp, nmap);

                // iterate over the SMT2 strings for each clause
                for (unsigned int i = 0; i < cnf_smt2.size(); ++i) {
                    solver->add_assertion(cnf_smt2[i]); // add clause to solver
                }
                cnf_smt2.clear(); // clear strings

                // propagate forward from frames[i] to frames[i+1]
                if (solver->check_sat() == Solver::unsat) {
                    frames[i + 1].push_back(m[0]);
                }

                /* Solver stack destroyed to remove cl[i] */
                solver->pop(); // destroy solver stack
            }
            /* Solver stack destroyed to remove frame[i] */
            solver->pop(); // destroy solver stack

            std::set<std::shared_ptr<Clause>> myset1;
            std::set<unsigned long> myset2;
            for (unsigned int j = 0; j < frames[i].size(); ++j) {
//                std::cout << "Frame " << i << ": " << frames[i][j] << std::endl;
                myset1.insert(frames[i][j]);
            }

            for (unsigned int j = 0; j < frames[i + 1].size(); ++j) {
//                std::cout <<  "Frame " << i+1 << ": " << frames[i + 1][j] << std::endl;
                myset1.erase(frames[i+1][j]);
            }
//            std::cout << myset1.size() << std::endl;
            if(myset1.size() == 0)
                return true;

        }
        /* Solver stack destroyed to remove trans */
        solver->pop(); // destroy solver stack

        /********************** propagation phase ************************
         ************************** ends here ****************************/
    }
    return true;
}

bool IC3::check_proof_obligation(std::vector<std::shared_ptr<Clause>> s,
        unsigned int k) {

    if (k == 0)
        return false; // reached initial state

    std::vector<std::string> cnf_smt2; // helper string vector to hold SMTLIB2 formulas

    solver->push(); // create solver stack

    // add trans to solver
    solver->add_assertion(trans_str);

    if(k - 1 == 0) {
        solver->add_assertion(init_str);
    }
    else {
        std::vector<std::shared_ptr<Clause>> cl = frames[k - 1];

        // get SMT2 string corresponding to frames[k-1]
        SMTLIB2::generate_smtlib2_from_clause(cl, cnf_smt2, map2, SMTLIB2::uncomp,
        NULL);

        // iterate over the SMT2 strings for each clause
        for (unsigned int i = 0; i < cnf_smt2.size(); ++i) {

            solver->add_assertion(cnf_smt2[i]); // add clause to solver
        }
        cnf_smt2.clear(); // clear strings
    }

    // get SMT2 string corresponding to (not s)
    SMTLIB2::generate_smtlib2_from_clause(s, cnf_smt2, map2, SMTLIB2::comp,
    NULL);

    // iterate over the SMT2 strings for each clause
    for (unsigned int i = 0; i < cnf_smt2.size(); ++i) {

        solver->add_assertion(cnf_smt2[i]); // add clause to solver
    }
    cnf_smt2.clear(); // clear strings

    // get SMT2 string corresponding to (s')
    SMTLIB2::generate_smtlib2_from_clause(s, cnf_smt2, map2, SMTLIB2::uncomp,
            nmap);

    // iterate over the SMT2 strings for each clause
    for (unsigned int i = 0; i < cnf_smt2.size(); ++i) {
        solver->add_assertion(cnf_smt2[i]); // add clause to solver
    }
    cnf_smt2.clear(); // clear strings

    while (solver->check_sat() == Solver::sat) {

        // get model corresponding to bad cube t
        std::vector<std::string> bad_cube = solver->get_model();

        solver->pop(); // destroy solver stack

        // convert bad cube to multiple clauses (containing curr states only)
        std::vector<std::shared_ptr<Clause>> t;
        SMTLIB2::generate_clause_from_smtlib2(t, bad_cube, map1, nmap->size());

        if (!check_proof_obligation(t, k - 1)) {
            return false;
        }

        solver->push();

        // add trans to solver
        solver->add_assertion(trans_str);

        std::vector<std::shared_ptr<Clause>> cl = frames[k - 1];

        // get SMT2 string corresponding to frames[k-1]
        SMTLIB2::generate_smtlib2_from_clause(cl, cnf_smt2, map2,
                SMTLIB2::uncomp,
                NULL);

        // iterate over the SMT2 strings for each clause
        for (unsigned int i = 0; i < cnf_smt2.size(); ++i) {

            solver->add_assertion(cnf_smt2[i]); // add clause to solver
        }
        cnf_smt2.clear(); // clear strings

        // get SMT2 string corresponding to (not s)
        SMTLIB2::generate_smtlib2_from_clause(s, cnf_smt2, map2, SMTLIB2::comp,
        NULL);
        // iterate over the SMT2 strings for each clause
        for (unsigned int i = 0; i < cnf_smt2.size(); ++i) {

            solver->add_assertion(cnf_smt2[i]); // add clause to solver
        }
        cnf_smt2.clear(); // clear strings

        // get SMT2 string corresponding to (s')
        SMTLIB2::generate_smtlib2_from_clause(s, cnf_smt2, map2,
                SMTLIB2::uncomp, nmap);


        // iterate over the SMT2 strings for each clause
        for (unsigned int i = 0; i < cnf_smt2.size(); ++i) {

            solver->add_assertion(cnf_smt2[i]); // add clause to solver
        }
        cnf_smt2.clear(); // clear strings

    }

    solver->pop();

    std::shared_ptr<Clause> b(SMTLIB2::cube_to_clause(s));

    /*
    WIP: Using inductive generalization to reduce the size of the proof obligation b
    */

    for (unsigned int i = 1; i <= k; ++i) {
        frames[i].push_back(b);
    }
    return true;
}

bool IC3::shrink_cube(std::vector<std::shared_ptr<Clause>>& clauses, std::vector<std::string>& unsat_core, std::shared_ptr<Clause>& bad_cube, unsigned int k) {
    bool changed = false;
    std::vector<std::shared_ptr<Clause>> unsat_clauses;
    std::vector<std::shared_ptr<Clause>> new_clauses;

    // Create a mapping of clause to index in clauses
    std::unordered_map<std::shared_ptr<Clause>, size_t> clause_index;
    for (size_t i = 0; i < clauses.size(); ++i) {
        clause_index.emplace(clauses[i], i);
    }

    // Create a mapping of variable to index in the bitset
    std::unordered_map<std::string, size_t> var_index;
    for (const auto& var : map1) {
        var_index.emplace(var.first, var_index.size());
    }

    // Create a bitset representing the bad cube
    std::bitset<MAX_VAR> bad_cube_bs;
    for (const auto& lit : bad_cube->lits) {
        std::string var = lit.var;
        bool neg = (lit.phase == Solver::False);
        auto it = var_index.find(var);
        if (it == var_index.end()) {
            std::cerr << "Variable " << var << " not found in the variable map." << std::endl;
            return false;
        }
        size_t index = it->second;
        if (neg) {
            bad_cube_bs.set(index, false);
        } else {
            bad_cube_bs.set(index, true);
        }
    }

    // Compute the ternary simulation table
    std::vector<std::bitset<MAX_VAR>> sim_table;
    for (const auto& clause : clauses) {
        std::bitset<MAX_VAR> sim_row;
        for (const auto& lit : clause->lits) {
            std::string var = lit.var;
            bool neg = (lit.phase == Solver::False);
            auto it = var_index.find(var);
            if (it == var_index.end()) {
                std::cerr << "Variable " << var << " not found in the variable map." << std::endl;
                return false;
            }
            size_t index = it->second;
            if (neg) {
                sim_row.set(index, false);
            } else {
                sim_row.set(index, true);
            }
        }
        sim_table.push_back(sim_row);
    }

    // Iterate over the unsat core and try to remove literals from the clauses
    for (const auto& uc : unsat_core) {
        // Find the clause corresponding to the unsat core literal
        Solver::Literal uc_lit;
        if (!SMTLIB2::parse_literal(uc, uc_lit)) {
            std::cerr << "Failed to parse unsat core literal " << uc << std::endl;
            return false;
        }
        std::shared_ptr<Clause> uc_clause;
        if (uc_lit.phase == Solver::False) {
            uc_clause = std::make_shared<Clause>(Clause({Solver::Literal(uc_lit.var, Solver::True)}));
        } else {
            uc_clause = std::make_shared<Clause>(Clause({Solver::Literal(uc_lit.var, Solver::False)}));
        }
        auto it = clause


IC3::~IC3() {
    delete solver;
}

} /* namespace IC3 */
