#include <sstream>
#include <vector>
#include <array>
#include <cassert>
#include <string>

template <size_t MAX_SIZE>
size_t split(const std::string &s, char delim, std::array<std::string, MAX_SIZE> &elems)
{
    static_assert(MAX_SIZE > 0, "Size must be positive");
    
    std::stringstream ss(s);
    std::string item;
    size_t count = 0;

    while(std::getline(ss, item, delim))
    {
#ifdef DEBUG
        assert(count < MAX_SIZE);
#endif
        elems[count++] = item;
    }
    return count;
}

template <size_t N>
std::array<std::string, N> split_to(const std::string& s, char delim)
{
    std::array<std::string, N> arr_to_ret;
    size_t elements_inserted = 0;

    std::stringstream ss(s);
    std::string item;

    while(std::getline(ss, item, delim) && elements_inserted < N) {
        arr_to_ret[elements_inserted++] = item;
    }
    assert(elements_inserted == N);
    return arr_to_ret;
}
