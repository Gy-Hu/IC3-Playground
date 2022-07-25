//
// Created by galls2 on 29/09/19.
//

#include <queue>
#include <cassert>
#include <set>
#include "ctl_formula.h"

std::string CtlFormula::to_string() const {
    std::string to_return = _data;

    for (const auto& op : _operands)
        to_return += " (" + op->to_string() + ") ";
    return to_return;
}

CtlFormula::CtlFormula(std::string data, std::vector<std::unique_ptr<CtlFormula>> operands) :
    _data(std::move(data)), _operands(std::move(operands)) {}

bool CtlFormula::operator==(const CtlFormula &other) const {
    if (_data != other._data || _operands.size() != other._operands.size()) return false;
    for (size_t i = 0; i < _operands.size(); ++i)
    {
        if (!(_operands[i] == other._operands[i])) return false;
    }
    return true;
}

const CtlFormula::PropertySet CtlFormula::get_aps() const {
    CtlFormula::PropertySet pset;

    std::vector<const CtlFormula*> queue;
    queue.insert(queue.begin(), this);

    while (!queue.empty())
    {
        const CtlFormula* current = queue.back();
        queue.pop_back();

        if (current->_operands.empty() && !current->is_boolean())
        {
            pset.emplace(current);
        }
        else
        {
            for (const auto& it : current->_operands)
            {
                queue.insert(queue.begin(), it.get());
            }
        }
    }
    return pset;
}

std::string CtlFormula::get_data() const {
    return _data;
}

bool CtlFormula::is_boolean() const {
    return ((_data == "true") || (_data == "false"));
}

bool CtlFormula::get_boolean_value() const {
    assert(is_boolean());
    return _data == "true";
}

const std::vector<std::unique_ptr<CtlFormula>> &CtlFormula::get_operands() const {
    return _operands;
}

bool CtlFormula::operator<(const CtlFormula &other) const {
    return _data < other._data;

}

std::unique_ptr<CtlFormula> CtlFormula::clone() const {
    std::vector<std::unique_ptr<CtlFormula>> cloned_ops;
    for (const auto& op : _operands)
        cloned_ops.emplace_back(op->clone());
    return std::make_unique<CtlFormula>(_data, std::move(cloned_ops));
}

