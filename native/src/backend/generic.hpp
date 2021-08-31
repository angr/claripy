/**
 * @file
 * @brief This file defines templated method and variables backends should rely on for consistency
 */
#ifndef R_BACKEND_GENERIC_HPP_
#define R_BACKEND_GENERIC_HPP_

#include "base.hpp"

#include "../op.hpp"
#include "../simplification.hpp"

#include <stack>
#include <variant>


/** The abstraction cache is currently disabled */
#define BACKEND_DISABLE_ABSTRACTION_CACHE

namespace Backend {

    /** A subclass of Backend::Base which other backends should derive from for consistency
     *  If ApplyAnnotations, convert will invoke apply_annotations() on newly converted backend
     *  objects, passing the expressions' annotation vector to the function as it does
     */
    template <typename BackendObj, bool ApplyAnnotations> class Generic : public Base {
        /** A raw pointer to a backend object */
        using BORCPtr = const BackendObj *;

      public:
        // Define implicits
        DEFINE_IMPLICITS_ALL_NOEXCEPT(Generic);
        /** Destructor */
        ~Generic() noexcept override = default;

        /** The types sub-classes may extract backend objects into */
        using AbstractionVariant = std::variant<Expression::BasePtr, Mode::FP::Rounding>;

        // Virtual and Concrete Functions

        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        void downsize() override {
            Utils::Log::info("Z3 backend downsizing...");
            errored_cache.scoped_unique().first.clear();
            // Thread locals
            conversion_cache.clear();
#ifndef BACKEND_DISABLE_ABSTRACTION_CACHE
            abstraction_cache.clear();
#endif
        }

        /** Checks whether this backend can handle the expression
         *  @todo Make this better than this simplistic way
         *  expr may not be nullptr
         */
        bool handles(const Expression::RawPtr expr) override {
            UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
            try {
                (void) convert(expr);
                return true;
            }
            catch (Error::Backend::Unsupported &) {
                return false;
            }
        }

        /** Convert a claricpp Expression to a backend object
         *  This function does not deal with the lifetimes of Expressions
         *  This function does deal with the lifetimes of backend objects
         *  This is a worklist algorithm instead of recursion
         *  input may not be nullptr
         */
        BackendObj convert(const Expression::RawPtr input) {
#ifdef DEBUG
            using UnknownErr = Utils::Error::Unexpected::Unknown;
            UTILS_AFFIRM_NOT_NULL_DEBUG(input);
#endif

            // Functionally a stack of lists of expressions to be converted
            // We flatten and reverse this list for performance reasons
            // To denote the end of a list we prefix its elements with a nullptr
            // Note prefix because we reversed the list, thus the 'end' must come first
            // Each list represents the arguments of an expression
            Op::Base::Stack expr_stack { std::vector<Expression::RawPtr> { nullptr, input } };
            Op::Base::Stack op_stack;       // Expressions to give to the conversion dispatcher
                                            // We leave this as a vector for performance
                                            // reasons within the dispatcher
            std::vector<BORCPtr> arg_stack; // Converted backend objects

            // For the next element in our expr_stack
            for (const auto *expr = expr_stack.top(); !expr_stack.empty();) {
                expr = expr_stack.top();
                expr_stack.pop();

                // If the expression does not represent the end of a list
                if (expr != nullptr) {
                    const auto *const op { expr->op.get() };
                    UTILS_AFFIRM_NOT_NULL_DEBUG(op);

                    // Cache lookups
                    if (const auto lookup = conversion_cache.find(expr->hash);
                        lookup != conversion_cache.end()) {
                        arg_stack.emplace_back(&(lookup->second));
                        continue;
                    }
                    else if (const auto [map, _] = errored_cache.scoped_shared();
                             map.find(expr->hash) != map.end()) {
                        using Unsupported = Error::Backend::Unsupported;
                        throw Unsupported(name(), " cannot handle operation: ", op->op_name());
                    }

                    // Update stacks
                    op_stack.push(expr);
                    expr_stack.push(nullptr);
                    op->add_reversed_children(expr_stack);
                }

                // If the expression represents the end of a list
                // All arguments of expr_stack.top() have been converted
                else if (!expr_stack.empty()) {
                    expr = op_stack.top();
                    op_stack.pop();

                    // Convert the expression to a backend object
                    // Note: No need for a cache lookup, op_stack contains only cache misses
                    BackendObj obj { dispatch_conversion(expr, arg_stack) };
#ifdef DEBUG
                    if (UNLIKELY(!bool(obj))) {
                        Utils::Log::warning(
                            "Backend returned a nullptr as an expression when converting: ", expr);
                    }
#endif
                    if constexpr (ApplyAnnotations) {
                        obj = std::move(apply_annotations(obj, expr->annotations));
                    }

                    // Store the result in the arg stack and in the cache
                    const auto iter { Utils::map_emplace(conversion_cache, expr->hash,
                                                         std::move(obj)) };
                    arg_stack.emplace_back(&(iter->second));
                }
            }
#ifdef DEBUG
            // Sanity checks
            constexpr auto chk { [](const auto &...x) { Utils::affirm<UnknownErr>(x...); } };
            chk(op_stack.empty(), WHOAMI_WITH_SOURCE "op_stack should be empty");
            chk(expr_stack.empty(), WHOAMI_WITH_SOURCE "expr_stack should be empty");
            chk(arg_stack.size() == 1, WHOAMI_WITH_SOURCE "arg_stack should be of size: 1");
            const auto lookup { conversion_cache.find(input->hash) };
            chk(lookup != conversion_cache.end(),
                WHOAMI_WITH_SOURCE "conversion_cache does not contain expr hash");
            chk(&lookup->second == arg_stack.back(),
                WHOAMI_WITH_SOURCE "conversion_cache lookup does not match arg_stack back()");
            chk(arg_stack.back() == &conversion_cache.find(input->hash)->second,
                WHOAMI_WITH_SOURCE "arg_stack / conversion_cache mismatch at end of convert");
            UTILS_AFFIRM_NOT_NULL_DEBUG(arg_stack.back());
#endif
            // Return result
            return *arg_stack.back(); // shortcut for conversion_cache.find(input->hash)->second;
        }

        /** Abstract a backend object into a claricpp Expression */
        Expression::BasePtr abstract(const BackendObj &b_obj) {
            const auto variant { abstract_helper(b_obj) };
            try {
                return std::get<Expression::BasePtr>(variant);
            }
            catch (std::bad_variant_access &) {
                throw Utils::Error::Unexpected::Unknown(
                    WHOAMI_WITH_SOURCE,
                    "Abstraction culminated in a non-Expression object.\nVariant index: ",
                    variant.index(), "\nPlease report this.");
            }
        }

      private:
        /** Abstract a backend object into a type claricpp understands
         *  @todo: Enable abstraction cache-ing
         */
        AbstractionVariant abstract_helper(const BackendObj &b_obj) {
            const unsigned n = { b_obj.num_args() };

#ifndef BACKEND_DISABLE_ABSTRACTION_CACHE
            static_assert(false, "Better hashing needed");
            // Cache lookup
            const auto hash { b_obj.hash() };
            if (const auto lookup { abstraction_cache.find(hash) };
                lookup != abstraction_cache.end()) {
                return lookup->second;
            }
#endif

            // Convert b_obj args
            std::vector<AbstractionVariant> args;
            for (unsigned i { 0 }; i < n; ++i) {
                args.emplace_back(abstract_helper(b_obj.arg(i)));
            }

            // Convert b_obj then update various caches and return
            auto ret { dispatch_abstraction(b_obj, args) }; // Not const for move ret purposes
#ifndef BACKEND_DISABLE_ABSTRACTION_CACHE
            Utils::map_add(abstraction_cache, hash, ret);
#endif
            if (LIKELY(std::holds_alternative<Expression::BasePtr>(ret))) {
                const auto &tmp { std::get<Expression::BasePtr>(ret) };
                Simplification::cache(tmp->hash, tmp);
            }
            return ret;
        }

      protected:
        /** Allow subclasses access to the apply_annotations template parameter */
        static UTILS_ICCBOOL use_apply_annotations { ApplyAnnotations };

        // Pure Virtual Functions

        /** This dynamic dispatcher converts an expression into a backend object
         *  All arguments of expr that are not primitives have
         *  been pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         *  expr may not be nullptr
         *  Note: We use a raw vector instead of a stack for efficiency
         */
        virtual BackendObj dispatch_conversion(const Expression::RawPtr expr,
                                               std::vector<BORCPtr> &args) = 0;

        /** This dynamic dispatcher converts a backend object into an expression
         *  All arguments of b_obj that are not primitives have
         *  been pre-converted into expressions and are in args
         *  Arguments must be popped off the args stack if used
         *  Note: We use a raw vector instead of a stack for efficiency
         *  Note: This function should not edit the Simplification cache
         */
        virtual AbstractionVariant dispatch_abstraction(const BackendObj &b_obj,
                                                        std::vector<AbstractionVariant> &args) = 0;

        // Virtual Functions

        /** This applies the given annotations to the backend object
         *  If the given backend does not support this, this function will never be called
         */
        BackendObj apply_annotations(const BackendObj &o, Expression::Base::SPAV &&sp) const {
            static_assert(ApplyAnnotations, "ApplyAnnotations is not enabled");
            return apply_annotations_helper(o, std::move(sp));
        }

        /** This applies the given annotations to the backend object
         *  If the given backend does not support this, this function will never be called
         */
        virtual BackendObj apply_annotations_helper(const BackendObj &,
                                                    Expression::Base::SPAV &&) const {
            throw Utils::Error::Unexpected::NotSupported(
                "The backend has failed to implement this method. Please report this");
        }

        // Caches

        /** Errored cache
         *  Functionally this is a set of expression hashes that this backend is known
         *  to be incapable of handling. Technically it is a map to weak pointers
         *  of expressions so we don't need to store information about dead expressions
         */
        inline static Utils::ThreadSafe::Mutable<std::set<Hash::Hash>> errored_cache {};

        /** Thread local conversion cache
         *  Map an expression hash to a backend object representing it
         */
        inline static thread_local std::map<Hash::Hash, const BackendObj> conversion_cache {};

#ifndef BACKEND_DISABLE_ABSTRACTION_CACHE
        /** Thread local abstraction cache
         *  Map a backend object hash to an expression base pointer
         */
        inline static thread_local std::map<Hash::Hash, const AbstractionVariant>
            abstraction_cache {};
#endif
    };

} // namespace Backend

#endif
