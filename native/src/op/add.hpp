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
    class Add final : public Flat<> {
        OP_FINAL_INIT(Add)
      private:
        /** Private constructor */
        explicit inline Add(const Hash::Hash &h, OpContainer &&input)
            : Flat { h, static_cuid, std::forward<OpContainer>(input) } {}
    };

} // namespace Op

#endif
