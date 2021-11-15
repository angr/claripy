/**
 * @file
 * @brief This header defines the C API for Annotation
 * \ingroup api
 */
#ifndef R_API_ANNOTATION_H_
#define R_API_ANNOTATION_H_

#include "constants.h"


/** Return a new Annotation::Base
 *  @return A ClaricppAnnotation of type Base
 */
ClaricppAnnotation claricpp_annotation_new_base();

/** Return a new Annotation::SimplificationAvoidance
 *  @return A ClaricppAnnotation of type SimplificationAvoidance
 */
ClaricppAnnotation claricpp_annotation_new_simplification_avoidance();

/** Create an Annotation::SPAV from a list of annotations
 *  @param list An array of ClaricppAnnotation pointers
 *  @param len The length of list
 *  @return A ClaricppSPAV constructed from list and len
 */
ClaricppSPAV claricpp_annotation_create_spav(ARRAY_IN(ClaricppAnnotation) list, const SIZE_T len);

/** Converts an SPAV to a list of ClaricppAnnotations
 *  @param spav The SPAV to get the annotations of, .ptr may be nullptr
 *  @return The annotations held by spav, .arr will be nullptr if .ptr is nullptr
 */
ARRAY_OUT(ClaricppAnnotation) claricpp_annotation_spav_to_array(const ClaricppSPAV spav);

/** Get the length of spav
 *  @param spav The SPAV to get the length of, .ptr may be nullptr
 *  @return The length of spav
 */
SIZE_T claricpp_annotation_spav_len(const ClaricppSPAV spav);

/** Get the i'th entry of spav
 *  @param spav The SPAV to get the i'th entry of, .ptr may *not* be nullptr
 *  @param i The index to access spav with, i must be less than spav's length
 *  @return The i'th entry of spav
 */
ClaricppAnnotation claricpp_annotation_spav_get(const ClaricppSPAV spav, const SIZE_T i);

#endif
