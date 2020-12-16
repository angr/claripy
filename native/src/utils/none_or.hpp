/**
 * @file none_or.hpp
   @brief This file defines the NoneOr class
 */
#ifndef __UTILS_NONE_OR_HPP__
#define __UTILS_NONE_OR_HPP__

#include <utility>


/** A namespace used for the utils directory */
namespace Utils {

    /** A class that represents either an object or None
     *  For example, a NoneOr<int> can have a value of None or 1,2,3...
     */
    template <typename T> class NoneOr {

        /************************************************/
        /*                  Factories                   */
        /************************************************/

        /** Construction factory that utilizes T's copy constructor */
        static NoneOr<T> from_copy(const T &v, const bool is_none = false) {
            return NoneOr<T>(v, is_none);
        }

        /** Construction factory that utilizes T's move constructor */
        static NoneOr<T> from_move(T &&v, const bool is_none = false) {
            return NoneOr<T>(v, is_none);
        }

        /** Construction factory that utilizes T's default constructor */
        static NoneOr<T> from_default(const bool is_none = true) { return NoneOr<T>(is_none); }

        /************************************************/
        /*                   Getters                    */
        /************************************************/

        /** Return true if None */
        bool is_none() const { return is_none_v; }

        /** Return val */
        bool val() const { return val_v; }

        /************************************************/
        /*                   Setters                    */
        /************************************************/

        /** Set is_none_v */
        void set_none(const bool b) { this->is_none_v = b; }

        /** Set val_v via assignment*/
        void set_val_by_copy(const T &v) { this->val_v = v; }

        /** Set val_v via move*/
        void set_val_by_move(T &&v) { this->val_v = v; }

      private:
        /************************************************/
        /*                 Constructors                 */
        /************************************************/

        /** Private copy constructor
         *  Named factories will clearly explain how input is accepted by name */
        explicit NoneOr(const T &val, const bool is_none) : is_none_v(is_none), val_v(val) {}

        /** Private move constructor
         *  Named factories will clearly explain how input is accepted by name */
        explicit NoneOr(T &&val, const bool is_none) : is_none_v(is_none), val_v(val) {}

        /** Private default constructor
         *  Named factories will clearly explain how input is accepted by name */
        explicit NoneOr(const bool is_none) : is_none_v(is_none), val_v(val) {}

        /************************************************/
        /*                Representation                */
        /************************************************/

        /** true if none, false otherwise */
        bool is_none_v;

        /** the value if this represents if is_none_v is false */
        T val_v;
    };

}; // namespace Utils

#endif
