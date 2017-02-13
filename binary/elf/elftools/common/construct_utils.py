#-------------------------------------------------------------------------------
# elftools: common/construct_utils.py
#
# Some complementary construct utilities
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
from ..construct import Subconstruct, ConstructError, ArrayError


class RepeatUntilExcluding(Subconstruct):
    """ A version of construct's RepeatUntil that doesn't include the last 
        element (which casued the repeat to exit) in the return value.
        
        Only parsing is currently implemented.
        
        P.S. removed some code duplication
    """
    __slots__ = ["predicate"]
    def __init__(self, predicate, subcon):
        Subconstruct.__init__(self, subcon)
        self.predicate = predicate
        self._clear_flag(self.FLAG_COPY_CONTEXT)
        self._set_flag(self.FLAG_DYNAMIC)
    def _parse(self, stream, context):
        obj = []
        try:
            context_for_subcon = context
            if self.subcon.conflags & self.FLAG_COPY_CONTEXT:
                context_for_subcon = context.__copy__()
            
            while True:
                subobj = self.subcon._parse(stream, context_for_subcon)
                if self.predicate(subobj, context):
                    break
                obj.append(subobj)
        except ConstructError as ex:
            raise ArrayError("missing terminator", ex)
        return obj
    def _build(self, obj, stream, context):
        raise NotImplementedError('no building')
    def _sizeof(self, context):
        raise SizeofError("can't calculate size")

