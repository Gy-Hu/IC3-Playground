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

#ifndef INCLUDE_UTILS_UTILS_H_
#define INCLUDE_UTILS_UTILS_H_
#include <cstring>
#include <string>
#include <vector>
#include <map>
#include <memory>
#include <utils/ast.h>


void generate_string(std::string &, AST::ast_node*);

void split(const std::string &s, const char* delim,
        std::vector<std::string> & v);

/*
 * Clause class to maintain a vector of encoded literals.
 * Note: Negative values in the vector denote a negated literal.
 */
class Clause {
    /*
     * Vector containing signed values for literals
     */
    std::vector<signed char> literals;
public:
    // default constructor
    Clause();
    // copy constructor
    Clause(Clause *);
    // desttructor
    ~Clause();
    /*
     * Member function to add a literal to a clause
     * \param t The value to write
     */
    void add_literal(signed char);
    /*
     * Member function to return a pointer to the vector containing
     * literals in the clause.
     * \return a pointer to the literals vectors
     */
    std::vector<signed char> get_literals();
};

namespace SMTLIB2 {
enum smt_str_type {
    comp, uncomp
};
// generate SMT string from a passed pointer vector of clause pointers
void generate_smtlib2_from_clause(const std::vector<std::shared_ptr<Clause>>,
        std::vector<std::string> &, std::map<unsigned char, std::string> *,
        smt_str_type type, std::map<std::string, std::string> * nmap);

// generate vector of clause pointers from SMT string
void generate_clause_from_smtlib2(std::vector<std::shared_ptr<Clause>> &,
        std::vector<std::string>, std::map<std::string, unsigned char> *,
        unsigned int);

std::shared_ptr<Clause> cube_to_clause(std::vector<std::shared_ptr<Clause>>);
}

typedef Clause Cube;
#endif /* INCLUDE_UTILS_UTILS_H_ */
