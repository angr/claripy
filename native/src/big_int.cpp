/** @file */
#include "big_int.hpp"

using BIM = BigInt::Mode;
std::atomic<BIM> BigInt::mode_ { BIM::Str };