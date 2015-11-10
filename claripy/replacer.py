import weakref

class Replacer(object):
    def __init__(self, replacements=None, replacement_cache=None):
        self._replacements = { } if replacements is None else replacements
        self._replacement_cache = weakref.WeakKeyDictionary() if replacement_cache is None else replacement_cache

    def add_replacement(self, old, new, invalidate_cache=False):
        if invalidate_cache:
            self._replacements = dict(self._replacements)
            self._replacement_cache = weakref.WeakKeyDictionary(self._replacement_cache)

        self._replacements[old.cache_key] = new
        self._replacement_cache[old.cache_key] = new

    def replacement(self, old):
        if not isinstance(old, Base):
            return old

        if old.cache_key in self._replacement_cache:
            return self._replacement_cache[old.cache_key]
        else:
            new = old.replace_dict(self._replacement_cache)
            self._replacement_cache[old.cache_key] = new
            return new

    def branch(self):
        return Replacer(replacements=self._replacements, replacement_cache=self._replacement_cache)

    def __getstate__(self):
        return self._replacements

    def __setstate__(self, s):
        self._replacements = s
        self._replacement_cache = weakref.WeakKeyDictionary()

from .ast.base import Base
