#pragma once
#include <vector>
#include <string>
#include <set>
#include <memory>
#include <utility>
#include <unordered_set>

class CtlFormula
{
public:

    struct CtlFormulaPtrHasher
    {
        size_t operator()(const CtlFormula* const& a) const
        {
            std::hash<std::string> hasher;
            return hasher(a->to_string());
        }
    };
    struct CtlFormulaPtrComp
    {
        bool operator()(const CtlFormula* const& obj1, const CtlFormula* const& obj2) const
        {
            return (obj1 == obj2) || ((*obj1) == (*obj2));
        }
    };

    typedef std::unordered_set<const CtlFormula*, CtlFormulaPtrHasher, CtlFormulaPtrComp> PropertySet;

    explicit CtlFormula(std::string data, std::vector<std::unique_ptr<CtlFormula>> operands = {});

    std::string get_data() const;
    std::string to_string() const;
    bool operator==(const CtlFormula& other) const;
    const CtlFormula::PropertySet get_aps() const;
    bool is_boolean() const;
    bool get_boolean_value() const;
    const std::vector<std::unique_ptr<CtlFormula>>& get_operands() const;
    std::unique_ptr<CtlFormula> clone() const;
    bool operator<(const CtlFormula& other) const;

private:
  std::string _data;
  std::vector<std::unique_ptr<CtlFormula>> _operands;
};



