from .base import Base, I

class Bool(Base):
    pass

class BoolI(Bool, I):
    @staticmethod
    def _check_model_type(model):
        if not isinstance(model, bool):
            raise ClaripyTypeError("BoolI model must be a bool")
