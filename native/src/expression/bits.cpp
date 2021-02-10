/** @file */
#include "bits.hpp"

#include "../op.hpp"


void Expression::Bits::ctor_debug_checks() const {
    if (const auto cast { dynamic_cast<Constants::CTSC<CSized>>(op.get()) }; cast) {
        using Err = Error::Expression::Size;
        Utils::affirm<Err>(cast->size == this->size, "CSized Op size and Bits size mismatch");
    }
}
