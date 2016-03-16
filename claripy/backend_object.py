class BackendObject(object):
    """
    This is a base class for custom backend objects to implement.

    It lets Claripy know that how to deal with those objects, in case they're directly used in operations.

    Backend objects that *don't* derive from this class need to be wrapped in a type-I claripy.ast.Base.
    """

    def to_claripy(self):
        """
        Claripy calls this to retrieve something that it can directly reason about.
        """

        return self

