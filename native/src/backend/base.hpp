/**
 * @file
 * @brief This file defines the base expression
 */
#ifndef __BACKEND_BASE_HPP__
#define __BACKEND_BASE_HPP__

#include "../expression.hpp"

#include <memory>


namespace Backend {

    /** The base Backend type
     *  All backends must subclass this
     */
    class Base {
      public:
        // Define implicits
        SET_IMPLICITS(Base, default)

        /** Default destructor */
        virtual ~Base() = default;

        // Pure virtual functions

        /** Check whether the backend can handle the given expression */
        virtual bool handles(const Expression::BasePtr &expr) = 0;

        /** Simplify the given expression */
        virtual Expression::BasePtr simplify(const Expression::BasePtr &expr) = 0;

        // Virtual functions

        /** Clear caches to decrease memory pressure
         *  Note: if overriding this, it is advised to call this function from the derived version
         */
        virtual void downsize() {
            object_cache.clear();
            is_true_cache.clear();
            is_false_cache.clear();
        }

        // true / false ones here


      private:
        /** A weak pointer to the expression base type */
        using WPtr = std::weak_ptr<Utils::InternalType<Expression::BasePtr>>;

        /** object cache
         *  Map an expression hash to the result of is_true and to a weak pointer
         *  that points to the expression that has the key as a hash value
         */
        static thread_local std::map<Hash::Hash, const std::pair<WPtr, bool>> is_true_cache;

        /** is_true cache
         *  Map an expression hash to the result of is_true and to a weak pointer
         *  that points to the expression that has the key as a hash value
         */
        static thread_local std::map<Hash::Hash, const std::pair<WPtr, bool>> is_true_cache;

        /** is_false cache
         *  Map an expression hash to the result of is_false and to a weak pointer
         *  that points to the expression that has the key as a hash value
         */
        static thread_local std::map<Hash::Hash, const std::pair<WPtr, bool>> is_false_cache;
    };

} // namespace Backend

#endif
