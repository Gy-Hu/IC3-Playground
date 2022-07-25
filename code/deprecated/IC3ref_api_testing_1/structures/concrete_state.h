//#pragma once
#include <utility>

//
// Created by galls2 on 04/10/19.
//

#include <experimental/optional>
#include <vector>
#include "kripke_structure.h"
#include "../temporal/ctl_formula.h"

class KripkeStructure;


class ConcreteState {
public:
    ConcreteState(const KripkeStructure& kripke, const z3::expr& conjunct);

    std::vector<ConcreteState>& get_successors();

    void aps_by_sat(CtlFormula::PropertySet& pos, CtlFormula::PropertySet& neg) const;
    std::set<std::string> string_sat_aps() const;
    PropFormula get_bis0_formula() const;
    bool operator==(const ConcreteState& other) const;
    bool operator!=(const ConcreteState& other) const;

    const z3::expr& get_conjunct() const;
#ifdef DEBUG
    std::vector<bool> to_bitvec() const;
    std::string to_bitvec_str() const;
#endif
    friend std::ostream& operator<< (std::ostream& stream, const ConcreteState& concrete_state);

private:
    const KripkeStructure& _kripke;
    const z3::expr _conjunct;
    std::experimental::optional<std::vector<ConcreteState>> _successors;

    void compute_successors() ;
};

