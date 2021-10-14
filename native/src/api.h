/**
 * @file
 * @brief This header exposes the C API for claricpp
 */
#ifndef R_API_H_
#define R_API_H_

/********************************************************************/
/*                    Forward Type Declarations                     */
/********************************************************************/

/** Holds an Annotation::BasePtr reference */
struct ClaricppAnnotation;

/** Holds an Annotation::SPAV reference */
struct ClaricppSPAV;

/** Define size_t without polluting the global namespace */
#define SIZE_T unsigned long long

/********************************************************************/
/*                            Annotation                            */
/********************************************************************/

/** Return a new Annotation::Base */
ClaricppAnnotation * claricpp_annotation_new_base();

/** Return a new Annotation::SimplificationAvoidance */
ClaricppAnnotation * claricpp_annotation_new_simplification_avoicance();

/** Create an Annotation::SPAV from a list of annotations
 *  @param list An array of ClaricppAnnotation pointers
 *  @param len The length of list
 */
ClaricppSPAV * claricpp_annotation_create_spav(const ClaricppAnnotation * const * const list, const SIZE_T len);

/********************************************************************/
/*                            Expression                            */
/********************************************************************/

/********************************************************************/
/*                              Create                              */
/********************************************************************/

/********************************************************************/
/*                             Backend                              */
/********************************************************************/



#endif