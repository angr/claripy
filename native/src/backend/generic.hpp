/**
 * @file
 * @brief This file defines templated method and variables backends should rely on for consistency
 */
#ifndef R_BACKEND_GENERIC_HPP_
#define R_BACKEND_GENERIC_HPP_

#include "base.hpp"

#include "../op.hpp"
#include "../simplification.hpp"

#include <memory>
#include <stack>


namespace Backend {

    /** A subclass of Backend::Base which other backends should derive from for consistency
     *  If ApplyAnnotations, convert will invoke apply_annotations() on newly converted backend
     *  objects, passing the expressions's annotation vector to the function as it does
     */
    template <typename BackendObj, bool ApplyAnnotations> class Generic : public Base {
        /** A raw pointer to a backend object */
        using BORCPtr = const BackendObj *;

      public:
        // Define implicits
        DEFINE_IMPLICITS_ALL_NOEXCEPT(Generic);
        /** Destructor */
        ~Generic() noexcept override = default;

        // Pure Virtual Functions

        /** Create a new thread local solver and return an opaque shared pointer to it
         *  When this opaque shared pointer dies, the solver may also die as well
         *  Warning: Do *not* share solvers between threads
         */
        [[nodiscard]] virtual std::shared_ptr<void> new_tls_solver() const = 0;

        // Virtual and Concrete Functions

        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        void downsize() override {
            errored_cache.scoped_unique().first.clear();
            // Thread locals
            conversion_cache.clear();
        }

        /** Checks whether this backend can handle the expression
         *  @todo Make this better than this simplistic way
         *  expr may not be nullptr
         */
        bool handles(const Expression::RawPtr expr) override {
            UTILS_AFFIRM_NOT_NULL_DEBUG(expr);
            try {
                (void) convert(expr);
            }
            catch (Error::Backend::Unsupported &) {
                return false;
            }
            return true;
        }

        /** Convert a claricpp Expression to a backend object
         *  This function does not deal with the lifetimes of Expressions
         *  This function does deal with the lifetimes of backend objects
         *  This is a worklist algorithm instead of recusion
         *  input may not be nullptr
         */
        BackendObj convert(const Expression::RawPtr input) {
#ifdef DEBUG
            using UnknownErr = Utils::Error::Unexpected::Unknown;
            UTILS_AFFIRM_NOT_NULL_DEBUG(input);
#endif

            // Functionally a stack of lists of expressions to be converted
            // We flatten and reverse this list for preformance reasons
            // To denote the end of a list we prefix its elements with a nullptr
            // Note prefix because we reversed the list, thus the 'end' must come first
            // Each list represents the arguments of an expression
            Op::Base::Stack expr_stack { std::vector<Expression::RawPtr> { nullptr, input } };
            Op::Base::Stack op_stack;       // Expressions to give to the conversion dispatcher
                                            // We leave this as a vector for preformance
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

                    // TODO: Should this be cached? I think it is above though
                    // Convert the expression to a backend object
                    BackendObj obj { dispatch_conversion(expr, arg_stack) };
                    if constexpr (ApplyAnnotations) {
                        apply_annotations(obj, expr->annotations);
                    }

                    // Store the result in the arg stack and in the cache
                    auto &&[iter, success] = conversion_cache.emplace(expr->hash, std::move(obj));
#ifdef DEBUG
                    Utils::affirm<UnknownErr>(success, WHOAMI_WITH_SOURCE
                                              "Cache update failed for some reason.");
#else
                    (void) success;
#endif
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

        /** Abstract a backend object into a claricpp Expression
         *  b_obj may not nullptr
         */
        Expression::BasePtr abstract(Constants::CTSC<BackendObj> b_obj) {
            UTILS_AFFIRM_NOT_NULL_DEBUG(b_obj);
            /* inline static thread_local std::map<Hash::Hash, const Expression::BasePtr>
             * abstraction_cache {}; */
            /* Hash */

            // result = dispatch_abstraction
            // Simplification::cache(result->hash, result);

            (void) b_obj;
            return { nullptr };
        }

      protected:
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
         *  b_obj may not be nullptr
         *  Note: We use a raw vector instead of a stack for efficiency
         *  Note: This function should not edit the Simplification cache
         */
        virtual Expression::BasePtr
        dispatch_abstraction(Constants::CTSC<BackendObj> b_obj,
                             std::vector<Expression::BasePtr> &args) = 0;

        // Virtual Functions

        /** This applies the given annotations to the backend object
         *  \todo Implement this function
         */
        virtual void apply_annotations(BackendObj &o, Expression::Base::SPAV &&sp) {
            (void) o;
            (void) sp;
#ifdef DEBUG
            Utils::affirm<Utils::Error::Unexpected::MissingVirtualFunction>(
                ApplyAnnotations, WHOAMI_WITH_SOURCE,
                "subclass failed to override apply_annotations"
                " despite setting ApplyAnnotations to true");
#endif
        }

        // Caches

        /** Errored cache
         *  Functionally this is a set of expression hashes that this backend is known
         *  to be incapable of handling. Technically it is a map to weak pointers
         *  of expressions so we don't need to store information about dead expressions
         */
        inline static Utils::ThreadSafe::Mutable<std::set<Hash::Hash>> errored_cache {};

        /** Thread local converstion cache
         *  Map an expression hash to a backend object representing it
         */
        inline static thread_local std::map<Hash::Hash, const BackendObj> conversion_cache {};

        /** Thread local abstraction cache
         *  Map a backend object's hash to an expression base pointer
         */
        inline static thread_local std::map<Hash::Hash, const Expression::BasePtr>
            abstraction_cache {};
    };

} // namespace Backend

#endif
