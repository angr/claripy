/**
 * @file
 * @brief This defines big integer types
 */
#ifndef R_SRC_BIGINT_HPP_
#define R_SRC_BIGINT_HPP_

#include "mode.hpp"

#include <ostream>

#include <boost/multiprecision/gmp.hpp>


/** The arbitrary precision type claricpp uses */
struct BigInt {
    /** The type of the value when represented as an int */
    using Int = boost::multiprecision::mpz_int;
    /** The type of the value when represented as a string */
    using Str = std::string;
    /** The type of the value */
    using Value = std::variant<Int, Str>;
    /** The Mode type */
    using Mode = ::Mode::BigInt;

    // Constructors

    /** Convert the input to a BigInt using the mode Mod */
    template <Mode Mod> static inline BigInt from_c_str(CCSC s, const U64 bit_length) {
        assert_valid<Mod>();
        return (Mod == Mode::Str) ? BigInt { Str { s }, bit_length }
                                  : BigInt { Int { s }, bit_length };
    }

    /** Convert the input to a BigInt using the default mode */
    static inline BigInt from_c_str(CCSC s, const U64 bit_length) {
        return (mode_ == Mode::Str) ? from_c_str<Mode::Str>(s, bit_length)
                                    : from_c_str<Mode::Int>(s, bit_length);
    }

    /** Convert the input to a BigInt using the default Mod */
    template <Mode Mod> static inline BigInt from_str(Str &&s, const U64 bit_length) {
        return (Mod == Mode::Str) ? BigInt { std::move(s), bit_length }
                                  : BigInt { Int { std::move(s) }, bit_length };
    }

    /** Convert the input to a BigInt using the default mode */
    static inline BigInt from_str(Str &&s, const U64 bit_length) {
        return (mode_ == Mode::Str) ? from_str<Mode::Str>(std::move(s), bit_length)
                                    : from_str<Mode::Int>(std::move(s), bit_length);
    }

    /** Convert the input to a BigInt using the default Mod */
    template <Mode Mod> static inline BigInt from_int(Int &&i, const U64 bit_length) {
        return (Mod == Mode::Str) ? BigInt { i.str(), bit_length }
                                  : BigInt { std::move(i), bit_length };
    }

    /** Convert the input to a BigInt using the default mode */
    static inline BigInt from_int(Int &&i, const U64 bit_length) {
        return (mode_ == Mode::Str) ? from_int<Mode::Str>(std::move(i), bit_length)
                                    : from_int<Mode::Int>(std::move(i), bit_length);
    }

    /** Set the default BigInt mode to m */
    static inline Mode mode(const Mode m) noexcept {
        Util::Log::info("Setting BitInt mode to ", m);
        return mode_.exchange(m);
    }

    // Mode methods

    /** Get the default mode */
    static inline Mode mode() noexcept { return mode_; }

    // Modifiers

    /** Converts the BigInt to the given mode */
    template <Mode Mod> void convert() {
        assert_valid<Mod>();
        using CMode = std::conditional_t<Mod == Mode::Str, Str, Int>;
        if (std::holds_alternative<CMode>(value)) {
            return;
        }
        if constexpr (std::is_same_v<CMode, Int>) {
            value = Int { std::move(std::get<Str>(value)) };
        }
        else {
            value = std::get<Int>(value).str();
        }
    }

    /** The value */
    Value value;
    /** The bit length */
    U64 bit_length;

  private:
    /** Assert that Mod is a valid Mode */
    template <Mode Mod> static inline void assert_valid() {
        static_assert(Mod == Mode::Int || Mod == Mode::Str, "Mode may only be Int or Str");
    }

    /** The default mode */
    static std::atomic<Mode> mode_;
};

// Checks
static_assert(std::is_copy_constructible_v<BigInt>, "Fix me");

/** Ostream overload for BigInt::Value */
inline std::ostream &operator<<(std::ostream &os, const BigInt::Value &v) {
    if (std::holds_alternative<BigInt::Int>(v)) {
        return os << std::get<BigInt::Int>(v);
    }
    else {
        return os << std::get<BigInt::Str>(v);
    }
}

/** Ostream overload for BigInt */
inline std::ostream &operator<<(std::ostream &os, const BigInt &b) {
    CCSC q { (b.mode() == BigInt::Mode::Str) ? "\"" : "" };
    return os << R"({ "value" : )" << q << b.value << q << R"(, "bit_length" : )" << b.bit_length
              << " }";
}

/** Equality operator */
inline bool operator==(const BigInt &a, const BigInt &b) {
    return (a.bit_length == b.bit_length) && (a.value == b.value);
}


#endif
