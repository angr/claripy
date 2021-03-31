/**
 * @file
 * @brief This file defines templated method and variables backends should rely on for consistency
 */
#ifndef __BACKEND_GENERIC_HPP__
#define __BACKEND_GENERIC_HPP__

#include "base.hpp"

#include <memory>


namespace Backend {

    /** A subclass of Backend::Base which other backends should derive from for consistency */
    template <typename BackendObj, typename Solver> class Generic : public Base {
      public:
        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        virtual void downsize() override {
            Base::downsize(); // Super downsize
            errored_cache.unique().first.clear();
            // Thread locals
            object_cache.clear();
        }

        /** Checks whether this backend can handle the expression
         *  @todo Make this better than this simplistic way
         */
        bool handles(const ExprRawPtr expr) {
            try {
                (void) convert(expr);
            }
            catch (Error::Backend::Base &) {
                return false;
            }
            return true;
        }

      protected:
        /** A shared pointer to a constant backend object */
        using BOCPtr = std::shared_ptr<const BackendObj>;

        /** A vector based stack */
        template <typename T> using VStack = std::stack<T, std::vector>;

        // Pure Virtual Functions

        /** This dynamic dispatcher converts expr into a backend object
         *  All arguments of expr that are not primitives have been
         *  pre-converted into backend objects and are in args
         *  Arguments must be popped off the args stack if used
         */
        virtual BOCPtr dispatch_conversion(const ExprRawPtr expr, VStack<BOCPtr> &args) = 0;

        // Concrete functions

        /** Convert a claricpp Expression to a backend object
         *  This function does not deal with the lifetimes of expressions
         *  This function does deal with the lifetimes of backend objects
         */
        BOCPtr convert(Constants::CTSC<Expression::Base> input) {
            using BackendError = Error::Backend::Base;

            // Functionally a stack of lists of expression to be converted
            // We flatten and reverse this list for preformance reasons
            // To denote the end of a list we prefix its elements with a nullptr
            // Note prefix because we reversed the list, thus the 'end' must come first
            // Each list represents the arguments of an expression
            VStack<ExprRawPtr> expr_stack { nullptr, input };
            VStack<ExprRawPtr> op_stack;   // Expressions to give to the conversion dispatcher
                                           // We leave this as a vector for preformance reasons
                                           // within the dispatcher
            std::vector<BOCPtr> arg_stack; // Converted backend objects

            // For the next element in our expr_stack
            for (const auto expr = expr_stack.top(); expr_stack.size() > 0;
                 expr = expr_stack.top()) {
                expr_stack.pop();

                // If the expression does not represent the end of a list
                if (expr != nullptr) {

                    // Cache lookups
                    if (errored.find(expr->hash) == errored.end()) {
                        throw BackendError(name(), " cannot handle operation: ", expr->op->name());
                    }
                    else if (const auto lookup = object_cache.find(expr->hash);
                             lookup != object_cache.end()) {
                        arg_stack.push_back(lookup->second.second);
                    }

                    // Update stacks
                    op_stack.push(expr);
                    expr->add_reversed_children(expr_stack);
                }

                // If the expression represents the end of a list
                // All arguments of expr_stack.top() have been converted
                else if (expr_stack.size() != 0) {
                    expr = op_stack.top();
                    op_stack.pop();

                    // Convert the expression to a backend object
                    BOCPtr obj; // NOLINT
                    const auto op_id = expr->op->cuid;
                    if (auto func = ctors.find(op_id); func != ctors.end()) {
                        obj = std::move(func(expr));
                    }
                    else {
                        obj = std::move(dispatch_conversion(expr, arg_stack));
                    }

                    // Apply annotations
                    for (const auto a : expr->annotations) {
                        obj = std::move(apply_annotation(obj, a));
                    }

                    // Store the result in the arg stack and in the cache
                    arg_stack.push_back(obj);
                    object_cache.emplace(op_id, std::move(expr),
                                         std::move(obj)); // This moves its arguments
                }
            }
#ifdef DEBUG
            // Sanity checks
            using UnknownErr = Utils::Error::Unexpected::Unknown;
            Utils::affirm<UnknownErr>(op_stack.size() == 0, WHOAMI "op_stack should be empty");
            Utils::affirm<UnknownErr>(expr_stack.size() == 0, WHOAMI "expr_stack should be empty");
            Utils::affirm<UnknownErr>(arg_stack.size() == 1,
                                      WHOAMI "arg_stack should be of size: 1");
#endif
            // Return result
            return arg_stack.top();
        }

        // Constant variables

        /** Ctor map
         *  This maps, via cuid, an Expression Type T to a function which produces a backend
         *  object. This function takes as its sole argument a const Expression, E, of type T.
         *  E must be an expression that has either no children, or children of exclusively
         *  primtives, Symbols, and / or Literals.
         *  In otherwords, E must be directly convertible to a backend object without needing
         *  to recurse to convert any of E's children first.
         */
        static const std::map<CUID::CUID, BackendObj(const ExprRawPtr)> ctors;

        // Caches

        /** Errored cache
         *  Functionally this is a set of expression hashes that this backend is known
         *  to be incapable of handling. Technically it is a map to weak pointers
         *  of expressions so we don't need to store information about dead expressions
         */
        static Utils::ThreadSafe::Mutable<std::map<Hash::Hash, const WPtr>> errored_cache;

        /** Thread local object cache
         *  Map an expression hash to a backend object representing it
         */
        static thread_local WeapExpressionMap<BackendObj> object_cache;
    };

} // namespace Backend

#endif
