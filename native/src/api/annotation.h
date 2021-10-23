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

#endif
