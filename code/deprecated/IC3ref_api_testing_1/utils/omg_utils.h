#pragma once
#include <map>
#include <functional>
#include <memory>
#include <array>
#include "../formulas/sat_solver.h"
//
// Created by galls2 on 20/10/19.
//

#ifdef DEBUG
#include <cstdio>
#include <set>

#define DEBUG_PRINT(fmt, args...) fprintf(stderr, fmt, ## args)
#define DEBUG_PRINT_SEP DEBUG_PRINT("------------------------------------------\n")

#else
#define DEBUG_PRINT(fmt, args...)
#define DEBUG_PRINT_SEP
#endif

template< typename T, typename ...Ts>
constexpr std::array<T, 1 + sizeof...(Ts)> make_array(T arg, Ts... args)
{
    return std::array<T, 1 + sizeof...(Ts)>({arg, args...});
}

template <typename T>
void print_vec(const std::vector<T>& vec)
{
    for (const auto& it : vec)
        std::cout << it << " ";
    std::cout << std::endl;
}

class AbstractState;
typedef std::set<AbstractState*> AbsStateSet;
typedef std::reference_wrapper<AbstractState> AStateRef;
typedef std::reference_wrapper<const AbstractState> ConstAStateRef;
typedef std::set<const AbstractState*> ConstAbsStateSet;

typedef std::pair<AStateRef, AStateRef> AStateRefPair;