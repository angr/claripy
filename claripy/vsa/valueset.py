
class ValueSet(object):
    def __init__(self):
        self._si_dict = {}

    def set_si(self, region, si):
        self._si_dict[region] = si

    def merge_si(self, region, si):
        if region not in self._si_dict:
            self.set_si(region, si)
        else:
            self._si_dict[region] = self._si_dict[region].union(si)

    def remove_si(self, region, si):
        raise NotImplementedError()

    def __repr__(self):
        for region, si in self._si_dict.items():
            s = "%s: %s" % (region, si)
        return "(" + s + ")"

    def __len__(self):
        if self.is_empty():
            return 0
        return len(self._si_dict.items()[0][0])

    def is_empty(self):
        return (len(self._si_dict) == 0)