#include "aig_simple_parser.h"
extern "C" {
#include "aiger.h"
}
#include <iostream>
//#include "aig_to_aag.h"
#include "string_utils.h"

AigParser::AigParser(const std::string &aig_path)
{
    //std::vector<std::string> file_lines = aig_to_aag_lines(aig_path);
    aiger * aig = aiger_init();
    freopen(aig_path.c_str(), "r", stdin);
    const char * msg = aiger_read_from_file(aig, stdin);
    std::cout<< msg <<std::endl;

    //extract_metadata(file_lines[0]);
}


// void AigParser::extract_metadata(const std::string &first_aag_line)
// {
//     std::array<std::string, 6> components = split_to<6>(first_aag_line, ' ');
//     assert(components[0] == std::string("aag"));
//     _metadata[M] = std::stoul(components[1]);
//     _metadata[I] = std::stoul(components[2]);
//     _metadata[L] = std::stoul(components[3]);
//     _metadata[O] = std::stoul(components[4]);
//     _metadata[A] = std::stoul(components[5]);

//     _first_and_literal = (_metadata.at(AigMetadata::I) + _metadata.at(L) + 1) * 2;
// }

