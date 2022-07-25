#pragma once
//
// Created by galls2 on 12/10/19.
//

#include "../structures/kripke_structure.h"


class AbstractClassificationNode;

class AbstractState {
public:
    AbstractState(const KripkeStructure& kripke, CtlFormula::PropertySet pos_labels, CtlFormula::PropertySet neg_labels, CtlFormula::PropertySet atomic_labels, PropFormula sym_rep);
    bool is_pos_labeled(const CtlFormula& spec) const;
    bool is_neg_labeled(const CtlFormula& spec) const;
    void add_label(const bool positivity, const CtlFormula& spec);
    bool is_final_classification() const;
    void set_cl_node(AbstractClassificationNode* cl_node);
    AbstractClassificationNode* get_cl_node() const;
    const KripkeStructure& get_kripke() const;
    const PropFormula& get_formula() const;
    const CtlFormula::PropertySet& get_pos_labels() const;
    const CtlFormula::PropertySet& get_neg_labels() const;

    size_t get_abs_idx() const;
#ifdef DEBUG
    std::string _debug_name;
#endif
private:
    const size_t _abs_idx;
    const KripkeStructure& _kripke;
    CtlFormula::PropertySet _pos_labels;
    CtlFormula::PropertySet _neg_labels;
    CtlFormula::PropertySet _atomic_labels;
    AbstractClassificationNode* _cl_node;
    const PropFormula _sym_rep;

};

bool operator<(const AbstractState& lhs, const AbstractState& rhs);
bool operator==(const AbstractState& lhs, const AbstractState& rhs);
