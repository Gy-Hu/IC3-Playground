/*************************************************************************
 * Copyright (C) 2017 by Rohit Dureja                                    *
 *                                                                       *
 * This file is part of SimplePDR.                                       *
 *                                                                       *
 *  SimplePDR is free software: you can redistribute it and/or modify    *
 *  it under the terms of the GNU General Public License as published by *
 *  the Free Software Foundation, either version 3 of the License, or    *
 *  (at your option) any later version.                                  *
 *                                                                       *
 *  SimplePDR is distributed in the hope that it will be useful,         *
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of       *
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the        *
 *  GNU General Public License for more details.                         *
 *                                                                       *
 *  You should have received a copy of the GNU General Public License    *
 *  along with SimplePDR.  If not, see <http://www.gnu.org/licenses/>.   *
 *************************************************************************/

#ifndef INCLUDE_PDR_IC3_H_
#define INCLUDE_PDR_IC3_H_

#include <vector>
#include <memory>
#include <model/model.h>
#include <solver/solver.h>
#include <utils/utils.h>
#include <utils/ast.h>

namespace IC3 {

class IC3 {
private:
    // Z3 solver instance
    Solver::Solver * solver;

    /* Keep track of IC3 frames:
     * Data structure is a vector of vectors of smart pointers
     * to clauses.
     *
     * Reference use:
     * frames.push_back(M->get_init());         // push init to frame[0]
     *
     * std::vector<Clause *> * c = frames[0];   // get vector containing
     * 									   	    // pointers to clauses of
     * 									   	    // frame[0]
     *
     * std::cout << c->size() << std::endl;
     * for (unsigned int j = 0 ; j <c->size() ; ++j) {
     * 	Clause * f = (*c)[j];                   // get j-th of clause of
     * 	                                        // frame[0]
     *
     * 	std::vector<signed char> * lit;         // pointer to a vector of
     * 	                                        // literals.
     *
     * 	lit = f->get_literals();                // make lit point to literals in
     * 	                                        // j-th clause of frame[0]
     *
     * 	for (unsigned int i = 0 ; i < lit->size() ; ++i)
     * 	std::cout << (*lit)[i] << std::endl;
     * }
     */
    std::vector<std::vector<std::shared_ptr<Clause>>>frames;
    AST::ast_node * init;
    AST::ast_node * trans;
    AST::ast_node * prop;
    std::map<std::string, unsigned char> * map1;
    std::map<unsigned char, std::string> * map2;
    std::map<std::string, std::string> * nmap;

    std::string init_str;
    std::string invar_str;
    std::string neg_invar_str;
    std::string trans_str;

    bool check_proof_obligation(std::vector<std::shared_ptr<Clause>>, unsigned int);

public:
    IC3(std::shared_ptr<Model::Model>);
    bool prove();
    virtual ~IC3();
};

}
/* namespace IC3 */

#endif /* INCLUDE_PDR_IC3_H_ */
