/**
 * @file
 * @brief This file defines templated method and variables backends should rely on for consistency
 */
#ifndef __BACKEND_GENERIC_HPP__
#define __BACKEND_GENERIC_HPP__

#include "base.hpp"

#include "../op.hpp"

#include <memory>
#include <stack>


namespace Backend {

    /** A subclass of Backend::Base which other backends should derive from for consistency
     *  If ApplyAnnotations, convert will invoke apply_annotations() on newly converted backend
     *  objects, passing the expressions's annotation vector to the function as it does
     */
    template <typename BackendObj, bool ApplyAnnotations> class Generic : public Base {
        /** A raw pointer to a backend object */
        using BORCPtr = Constants::CTS<BackendObj>;

      public:
        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        void downsize() override {
            Base::downsize(); // Super downsize
            errored_cache.unique().first.clear();
            // Thread locals
            object_cache.clear();
        }

        /** Checks whether this backend can handle the expression
         *  @todo Make this better than this simplistic way
         */
        bool handles(const Expression::RawPtr expr) override {
            try {
                (void) convert(expr);
            }
            catch (Error::Backend::Base &) {
                return false;
            }
            return true;
        }

      protected:
        /** A vector based stack */
        template <typename T> using Stack = std::stack<T, std::vector<T>>;

        // Pure Virtual Functions

        /** This dynamic dispatcher converts expr into a backend object
         *  All arguments of expr that are not primitives have been
         *  pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         *  Note that we use a raw vector instead of a stack for efficiency
         */
        virtual BackendObj dispatch_conversion(const Expression::RawPtr expr,
                                               std::vector<BORCPtr> &args) = 0;

        // Virtual Functions

        /** This applies the given annotations to the backend object */
        virtual void apply_annotations(BackendObj &o, Expression::Base::AnVec &&ans) {
            (void) o;
            (void) ans;
#ifdef DEBUG
            Utils::affirm<Utils::Error::Unexpected::MissingVirtualFunction>(
                ApplyAnnotations, WHOAMI_WITH_SOURCE,
                "subclass failed to override apply_annotations"
                " despite setting ApplyAnnotations to true");
#endif
        }

        // Concrete functions

        /** Convert a claricpp Expression to a backend object
         *  This function does not deal with the lifetimes of expressions
         *  This function does deal with the lifetimes of backend objects
         */
        BackendObj convert(const Expression::RawPtr input) {
            using BackendError = Error::Backend::Base;

            // Functionally a stack of lists of expression to be converted
            // We flatten and reverse this list for preformance reasons
            // To denote the end of a list we prefix its elements with a nullptr
            // Note prefix because we reversed the list, thus the 'end' must come first
            // Each list represents the arguments of an expression
            Op::Base::Stack expr_stack { std::vector<Expression::RawPtr> { nullptr, input } };
            Op::Base::Stack op_stack;       // Expressions to give to the conversion dispatcher
                                            // We leave this as a vector for preformance reasons
                                            // within the dispatcher
            std::vector<BORCPtr> arg_stack; // Converted backend objects

            // For the next element in our expr_stack
            for (const auto *expr = expr_stack.top(); !expr_stack.empty();
                 expr = expr_stack.top()) {
                const auto *const op { expr->op.get() };
                expr_stack.pop();

                // If the expression does not represent the end of a list
                if (expr != nullptr) {

                    // Cache lookups
                    if (const auto [map, _] = errored_cache.shared();
                        map.find(expr->hash) == map.end()) {
                        throw BackendError(name(), " cannot handle operation: ", op->op_name());
                    }
                    else if (const auto lookup = object_cache.find(expr->hash);
                             lookup != object_cache.end()) {
                        arg_stack.emplace_back(&(lookup->second));
                    }

                    // Update stacks
                    op_stack.push(expr);
                    op->add_reversed_children(expr_stack);
                }

                // If the expression represents the end of a list
                // All arguments of expr_stack.top() have been converted
                else if (!expr_stack.empty()) {
                    expr = op_stack.top();
                    op_stack.pop();

                    // Convert the expression to a backend object
                    BackendObj obj { dispatch_conversion(expr, arg_stack) };
                    if constexpr (ApplyAnnotations) {
                        apply_annotations(obj, expr->annotations);
                    }

                    // Store the result in the arg stack and in the cache
                    auto &&[iter, success] = object_cache.emplace(expr->hash, std::move(obj));
#ifdef DEBUG
                    Utils::affirm<Utils::Error::Unexpected::Unknown>(
                        success, WHOAMI_WITH_SOURCE "Cache update failed for some reason.");
#else
                    Utils::sink(success);
#endif
                    arg_stack.emplace_back(&(iter->second));
                }
            }
#ifdef DEBUG
            // Sanity checks
            using UnknownErr = Utils::Error::Unexpected::Unknown;
            Utils::affirm<UnknownErr>(op_stack.empty(), WHOAMI "op_stack should be empty");
            Utils::affirm<UnknownErr>(expr_stack.empty(), WHOAMI "expr_stack should be empty");
            Utils::affirm<UnknownErr>(arg_stack.size() == 1,
                                      WHOAMI "arg_stack should be of size: 1");
            const auto lookup { object_cache.find(input->hash) };
            Utils::affirm<UnknownErr>(lookup != object_cache.end(),
                                      WHOAMI "object_cache does not contain expr hash");
            Utils::affirm<UnknownErr>(&lookup->second == arg_stack.back(), WHOAMI
                                      "object_cache lookup does not match arg_stack back()");
#endif
            // Return result
            return *arg_stack.back(); // shortcut for object_cache.find(input->hash)->second;
        }

        // Caches

        /** Errored cache
         *  Functionally this is a set of expression hashes that this backend is known
         *  to be incapable of handling. Technically it is a map to weak pointers
         *  of expressions so we don't need to store information about dead expressions
         */
        inline static Utils::ThreadSafe::Mutable<std::set<Hash::Hash>> errored_cache {};

        /** Thread local object cache
         *  Map an expression hash to a backend object representing it
         */
        inline static thread_local std::map<Hash::Hash, const BackendObj> object_cache {};
    };

} // namespace Backend

#endif
