/** @file */
#include "singular.hpp"


// For brevity
using namespace Expression;
template <typename T> using Ret = typename Hash::SingularRetMap<T>::RetType;


/** A specialization for T = char * */
template <> Ret<char *> Hash::singular<char *>(char *const &c) {
    return c;
}
