/**
 * @file
 * @brief The OP representing addition
 */
#ifndef __OP_ADD_HPP__
#define __OP_ADD_HPP__

#include "flat.hpp"

#include <memory>


namespace Op {

    /** The op class: Add */
    class Add final : public Flat {
        OP_FINAL_INIT(Eq)
      private:
        /** Private constructor */
        explicit inline Eq(const Hash::Hash &h, OpContainer &&input)
            : Flat { h, static_cuid, input } {}
    };

} // namespace Op

#endif
