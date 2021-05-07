/**
 * @file
 * \ingroup utils
 * @brief This file defines the function norm_path_hash
 */
#ifndef __UTILS_NORMPATHHASH_HPP__
#define __UTILS_NORMPATHHASH_HPP__

#include "pow.hpp"
#include "strlen.hpp"
#include "str_prefix.hpp"
#include "fnv1a.hpp"
#include "error.hpp"
#include "affirm.hpp"
#include "unconstructable.hpp"
#include "../constants.hpp"

#include <cstdint>
#include <type_traits>


namespace Utils {

	/** Return the FNV1a of the normal path of s */
	constexpr auto norm_path_hash(Constants::CCS s) noexcept {

		// Trivial case
		auto len { Utils::strlen(s) };
		if (len == 0) {
			return 0UL;
		}

/** A local macro used to advance s */
#define ADVANCE(X) { s+= (X); len -= (X);  }

		// Determine if absolute or relative path
		const bool absolute { s[0] == '/' };
		if (absolute) {
			while(len && s[0] == '/') {
				ADVANCE(1);
			};
		}

		// Store path segments
		Constants::CCS segments[len] {};
		Constants::UInt segment_lengths[len] {};
		Constants::UInt n_seg { 0 };

		// Current segment info
		Constants::UInt offset { 0 };
		Constants::UInt current_seg_length { 0 };

		// Repeat for all of s
		while(len) {
			// Handle './' and '//'
			if (str_prefix(s, "./") || str_prefix(s, "//")) { ADVANCE(1); ++offset; }
			// Segment update
			if (s[0] == '/') {
				// Skip empty segments
				if (current_seg_length) {
					segments[n_seg] = s - offset - current_seg_length;
					segment_lengths[n_seg] = current_seg_length;
					++n_seg;
				}
				// Reset current segment data
				current_seg_length = 0;
				offset = 0;
				ADVANCE(1);
				continue;
			}
			// Handle '../'
			if (str_prefix(s, "../")) {
				ADVANCE(3)
				// Rewinding segments
				affirm<Error::Unexpected::BadPath>(n_seg > 0, WHOAMI_WITH_SOURCE,
					"given path that goes outside of / or ./"
				);
				n_seg -= 1;
				continue;
			}
			// Normal character
			ADVANCE(1)
			++current_seg_length;
		}

// Cleanup
#undef ADVANCE

		// Record last segment
		segments[n_seg] = s - current_seg_length;
		segment_lengths[n_seg] = current_seg_length;
		++n_seg;

		// Norm path length
		Constants::UInt total_n_len { (absolute ? 1_ui : 2_ui) - 1_ui };
		for(Constants::UInt i = 0; i < n_seg; ++i) {
			total_n_len += 1 + segment_lengths[i];
		}

		// Construct norm path
		char norm[total_n_len + 1] {};
		Constants::UInt n_len { 0 };
		if (!absolute) { norm[n_len++] = '.'; }
		norm[n_len++] = '/';
		for(Constants::UInt i { 0 }; i < n_seg; ++i) {
			for(Constants::UInt k { 0 }; k < segment_lengths[i]; ++k) {
				norm[n_len++] = segments[i][k];
			}
			norm[n_len++] = '/';
		}
		norm[--n_len] = 0;
		affirm<Error::Unexpected::Unknown>(n_len == total_n_len,
			WHOAMI_WITH_SOURCE "internal error detected");

		// Hash
		return FNV1a<char>::hash(norm, n_len);
	}

} // namespace Utils

#endif
