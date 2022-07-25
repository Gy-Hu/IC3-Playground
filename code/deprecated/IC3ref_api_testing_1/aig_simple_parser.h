//
// Created by galls2 on 07/09/19.
//
#include <unordered_map>
#include <map>
#include <vector>
#include <string>
#include <memory>
#include <experimental/optional>
#include <z3++.h>
#include <bits/unordered_map.h>

enum AigMetadata{
    M = 0, I = 1, L = 2, O = 3, A = 4
};


class AigParser {
public:

    explicit AigParser(const std::string& aig_path);
    const std::unordered_map<AigMetadata, size_t, std::hash<size_t>>& get_aig_metadata();

// private:
//     void extract_metadata(const std::string& first_aag_line);
};
