class Annotation:
    """
    Annotations are used to achieve claripy's goal of being an arithmetic instrumentation engine.
    They provide a means to pass extra information to the claripy backends.
    """

    @property
    def eliminatable(self):  # pylint:disable=no-self-use
        """
        Returns whether this annotation can be eliminated in a simplification.

        :return: True if eliminatable, False otherwise
        """
        return True

    @property
    def relocatable(self):  # pylint:disable=no-self-use
        """
        Returns whether this annotation can be relocated in a simplification.

        :return: True if it can be relocated, false otherwise.
        """
        return False

    def relocate(self, src, dst):  # pylint:disable=no-self-use,unused-argument
        """
        This is called when an annotation has to be relocated because of simplifications.

        Consider the following case:

            x = claripy.BVS('x', 32)
            zero = claripy.BVV(0, 32).add_annotation(your_annotation)
            y = x + zero

        Here, one of three things can happen:

            1. if your_annotation.eliminatable is True, the simplifiers will simply
               eliminate your_annotation along with `zero` and `y is x` will hold
            2. elif your_annotation.relocatable is False, the simplifier will abort
               and y will never be simplified
            3. elif your_annotation.relocatable is True, the simplifier will run,
               determine that the simplified result of `x + zero` will be `x`. It
               will then call your_annotation.relocate(zero, x) to move the annotation
               away from the AST that is about to be eliminated.

        :param src: the old AST that was eliminated in the simplification
        :param dst: the new AST (the result of a simplification)
        :return: the annotation that will be applied to `dst`
        """
        return self


#
# Some built-in annotations
#


class SimplificationAvoidanceAnnotation(Annotation):
    @property
    def eliminatable(self):
        return False

    @property
    def relocatable(self):
        return False
