/**
 * @file
 * @brief This file defines the base expression
 */
#ifndef __EXPRESSION_BOOL_HPP__
#define __EXPRESSION_BOOL_HPP__

#include "base.hpp"

#include "../dummy.hpp"


namespace Expression {

    /** The base Expression type
     *  All expressions must subclass this
     */
    class Bool final : public Base {
        FACTORY_ENABLE_CONSTRUCTION_FROM_BASE(Base)
      public:
        /** Default destructor */
        inline ~Bool() noexcept override final = default;

        /** Check to see if this evaluates to true */
        inline bool is_true() const { return is_X<true>(); }

        /** Check to see if this evaluates to true */
        inline bool is_false() const { return is_X<false>(); }

      private:
        /** Private Constructor */
        explicit inline Bool(const Hash::Hash h, const bool sym, Factory::Ptr<Op::Base> &&op_,
                             AnnotationVec &&annotations_) noexcept
            : Base { h, static_cuid, sym, std::forward<Factory::Ptr<Op::Base>>(op_),
                     std::forward<AnnotationVec>(annotations_) } {}

        /** Check to see if this evaluates to X */
        template <bool X> inline bool is_X() const {
            for (auto &&backend : Dummy::quick_backends) {
                // Will probably have to emulate try / catch later on
                if constexpr (X) {
                    if (backend.is_true(this)) {
                        return true;
                    }
                }
                else {
                    if (backend.is_false(this)) {
                        return true;
                    }
                }
            }
            Utils::Log::debug("Unable to tell the truth-value of this expression");
            return false;
        }

        /* Disable other methods of construction */
        SET_IMPLICITS_CONST_MEMBERS(Bool, delete)
    };


} // namespace Expression

#endif
