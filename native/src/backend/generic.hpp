/**
 * @file
 * @brief This file defines templated method and variables backends should rely on for consistency
 */
#ifndef R_SRC_BACKEND_GENERIC_HPP_
#define R_SRC_BACKEND_GENERIC_HPP_

#include "base.hpp"

#include "../op.hpp"
#include "../simplify.hpp"

#include <stack>
#include <variant>


/** The abstraction cache is currently disabled */
#define BACKEND_DISABLE_ABSTRACTION_CACHE

namespace Backend {

    /** A subclass of Backend::Base which other backends should derive from for consistency
     *  If apply_annotations, convert will invoke apply_annotations() on newly converted backend
     *  objects, passing the exprs' annotation vector to the function as it does
     */
    template <typename Derived, typename BackendObj> class Generic : public Base {
        ENABLE_UNITTEST_FRIEND_ACCESS;
        // Disable implicits
        SET_IMPLICITS_EXCLUDE_DEFAULT_CTOR(Generic, delete);

      public:
        /** Constructor */
        inline Generic() noexcept = default;
        /** Destructor */
        ~Generic() noexcept override = default;

        /** The types sub-classes may extract backend objects into */
        using AbstractionVariant = std::variant<Expr::BasePtr, Mode::FP::Rounding>;

        // Virtual and Concrete Functions

        /** Checks whether this backend can handle the expr
         *  Note: If the backend will not simplify the expr, but will accept it, returns true
         *  @todo Make this better than this simplistic way
         *  expr may not be nullptr
         */
        bool handles(const Expr::RawPtr expr) override {
            UTIL_ASSERT_NOT_NULL_DEBUG(expr);
            try {
                (void) convert(expr);
                return true;
            }
            catch (Error::Backend::Unsupported &) {
                return false;
            }
        }

        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        void downsize() override {
            Util::Log::info("Z3 backend downsizing...");
            // Thread locals
            conversion_cache_g().clear();
#ifndef BACKEND_DISABLE_ABSTRACTION_CACHE
            abstraction_cache_g().clear();
#endif
            // Globals
            auto [ec, _] { errored_cache.unique() };
            ec.clear();
        }

      protected:
        /** Convert a claricpp Expr to a backend object
         *  This function does not deal with the lifetimes of Exprs
         *  This function does deal with the lifetimes of backend objects
         *  This is a worklist algorithm instead of recursion
         *  input may not be nullptr
         */
        BackendObj convert(const Expr::RawPtr input) {
            auto &conversion_cache { conversion_cache_g() };
            UTIL_ASSERT_NOT_NULL_DEBUG(input);

            // Functionally a stack of lists of exprs to be converted
            // We flatten and reverse this list for performance reasons
            // To denote the end of a list we prefix its elements with a nullptr
            // Note prefix because we reversed the list, thus the 'end' must come first
            // Each list represents the arguments of an expr
            Op::Stack expr_stack { std::vector<Expr::RawPtr> { nullptr, input } };
            Op::Stack op_stack;                        // Exprs to give to the conversion dispatcher
                                                       // We leave this as a vector for performance
                                                       // reasons within the dispatcher
            std::vector<const BackendObj *> arg_stack; // Converted backend objects

            // For the next element in our expr_stack
            for (const auto *expr = expr_stack.top(); not expr_stack.empty();) {
                expr = expr_stack.top();
                expr_stack.pop();

                // If the expr does not represent the end of a list
                if (expr) {
                    const auto *const op { expr->op.get() };
                    UTIL_ASSERT_NOT_NULL_DEBUG(op);

                    // Cache lookups
                    if (const auto lookup = conversion_cache.find(expr->hash);
                        lookup != conversion_cache.end()) {
                        arg_stack.emplace_back(&(lookup->second));
                        continue;
                    }
                    else if (const auto [map, _] = errored_cache.shared();
                             map.find(expr->hash) != map.end()) {
                        UTIL_THROW(Error::Backend::Unsupported, name(),
                                   " cannot handle operation: ", op->op_name());
                    }

                    // Update stacks
                    op_stack.push(expr);
                    expr_stack.push(nullptr);
                    Op::unsafe_add_reversed_children(*op, expr_stack);
                }

                // If the expr represents the end of a list
                // All arguments of expr_stack.top() have been converted
                else if (not expr_stack.empty()) {
                    expr = op_stack.top();
                    op_stack.pop();

                    // Convert the expr to a backend object
                    // Note: No need for a cache lookup, op_stack contains only cache misses
                    BackendObj obj { dispatch_conversion(expr, arg_stack) };
                    if constexpr (Derived::apply_annotations) {
                        auto ans { expr->annotations() };
                        if (ans) {
                            obj = std::move(apply_annotations(obj, std::move(ans.value())));
                        }
                    }

                    // Store the result in the arg stack and in the cache
                    const auto iter { Util::map_emplace(conversion_cache, expr->hash,
                                                        std::move(obj)) };
                    arg_stack.emplace_back(&(iter->second));
                }
            }
#ifdef DEBUG
            // Sanity checks
            constexpr auto chk { [](const bool b, const auto &...x) {
                UTIL_ASSERT(Util::Err::Unknown, b, x...);
            } };
            chk(op_stack.empty(), "op_stack should be empty");
            chk(expr_stack.empty(), "expr_stack should be empty");
            chk(arg_stack.size() == 1, "arg_stack should be of size: 1");
            const auto lookup { conversion_cache.find(input->hash) };
            chk(lookup != conversion_cache.end(), "conversion_cache does not contain expr hash");
            chk(&lookup->second == arg_stack.back(),
                "conversion_cache lookup does not match arg_stack back()");
            chk(arg_stack.back() == &conversion_cache.find(input->hash)->second,
                "arg_stack / conversion_cache mismatch at end of convert");
            UTIL_ASSERT_NOT_NULL_DEBUG(arg_stack.back());
#endif
            // Return result
            return *arg_stack.back(); // shortcut for conversion_cache.find(input->hash)->second;
        }

        /** Abstract a backend object into a claricpp Expr */
        Expr::BasePtr abstract(const BackendObj &b_obj) {
            const auto variant { abstract_helper(b_obj) };
            try {
                return std::get<Expr::BasePtr>(variant);
            }
            catch (std::bad_variant_access &) {
                UTIL_THROW(Util::Err::Unknown,
                           "Abstraction culminated in a non-Expr object.\nVariant index: ",
                           variant.index(), "\nPlease report this.");
            }
        }

        // Pure Virtual Functions

        /** This dynamic dispatcher converts an expr into a backend object
         *  All arguments of expr that are not primitives have
         *  been pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         *  expr may not be nullptr
         *  Note: We use a raw vector instead of a stack for efficiency
         */
        virtual BackendObj dispatch_conversion(const Expr::RawPtr expr,
                                               std::vector<const BackendObj *> &args) = 0;

        /** This dynamic dispatcher converts a backend object into an expr
         *  All arguments of b_obj that are not primitives have
         *  been pre-converted into exprs and are in args
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
        BackendObj apply_annotations(const BackendObj &o, pybind11::dict &&annotations) const {
            static_assert(Derived::apply_annotations, "Derived::apply_annotations is not enabled");
            return apply_annotations_helper(o, std::move(annotations));
        }

        /** This applies the given annotations to the backend object
         *  If the given backend does not support this, this function will never be called
         */
        virtual BackendObj apply_annotations_helper(const BackendObj &, pybind11::dict &&) const {
            UTIL_THROW(Util::Err::NotSupported,
                       "The backend has failed to implement this method. Please report this");
        }

        // Caches

        /** Errored cache
         *  Functionally this is a set of expr hashes that this backend is known
         *  to be incapable of handling. Technically it is a map to weak pointers
         *  of exprs so we don't need to store information about dead exprs
         */
        inline static Util::ThreadSafe::Mutable<std::set<Hash::Hash>> errored_cache {};

        /** Thread local conversion cache
         *  Map an expr hash to a backend object representing it
         *  A function because of this bug: https://gcc.gnu.org/bugzilla/show_bug.cgi?id=66944
         */
        inline static auto &conversion_cache_g() noexcept {
            static thread_local std::map<Hash::Hash, const BackendObj> conversion_cache {};
            return conversion_cache;
        }

#ifndef BACKEND_DISABLE_ABSTRACTION_CACHE
        /** Thread local abstraction cache
         *  Map a backend object hash to an expr base pointer
         *  A function because of this bug: https://gcc.gnu.org/bugzilla/show_bug.cgi?id=66944
         */
        inline static auto &abstraction_cache_g() noexcept {
            static thread_local std::map<Hash::Hash, const AbstractionVariant> abstraction_cache {};
            return abstraction_cache;
        }
#endif
      private:
        /** Abstract a backend object into a type claricpp understands
         *  @todo: Enable abstraction cache-ing
         */
        AbstractionVariant abstract_helper(const BackendObj &b_obj) {
            const unsigned n = { b_obj.num_args() };

#ifndef BACKEND_DISABLE_ABSTRACTION_CACHE
            auto &abstraction_cache { abstraction_cache_g() };
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
            Util::map_add(abstraction_cache, hash, ret);
#endif
            if (LIKELY(std::holds_alternative<Expr::BasePtr>(ret))) {
                const auto &tmp { std::get<Expr::BasePtr>(ret) };
                Simplify::cache(tmp->hash, tmp);
            }
            return ret;
        }
    };

} // namespace Backend

#endif
