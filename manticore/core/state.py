from collections import OrderedDict

from .executor import manager
from .smtlib import solver
from ..utils.helpers import issymbolic

class AbandonState(Exception):
    pass


class State(object):
    '''
    Representation of a unique program state/path.

    :param ConstraintSet constraints: Initial constraints on state
    :param model: Initial constraints on state
    :type model: Decree or Linux or Windows
    '''

    # Class global counter
    _state_count = manager.Value('i', 0)
    _lock = manager.Lock()

    @staticmethod
    def get_new_id():
        with State._lock:
            ret = State._state_count.value
            State._state_count.value += 1
        return ret

    def __init__(self, constraints, model):
        self.model = model
        self.forks = 0
        self.co = self.get_new_id()
        self.constraints = constraints
        self.model._constraints = constraints
        for proc in self.model.procs:
            proc._constraints = constraints
            proc.memory._constraints = constraints

        self.input_symbols = list()
        # Stats I'm not sure we need in general
        self.last_pc = (None, None)
        self.visited = set()
        self.branches = OrderedDict()
        self._child = None

    def __reduce__(self):
        return (self.__class__, (self.constraints, self.model),
                {'visited': self.visited, 'last_pc': self.last_pc, 'forks': self.forks,
                 'co': self.co, 'input_symbols': self.input_symbols,
                 'branches': self.branches})

    @staticmethod
    def state_count():
        return State._state_count.value

    @property
    def cpu(self):
        return self.model.current

    @property
    def mem(self):
        return self.model.current.memory

    @property
    def name(self):
        return 'state_%06d.pkl' % (self.co)

    def __enter__(self):
        assert self._child is None
        new_state = State(self.constraints.__enter__(), self.model)
        new_state.visited = set(self.visited)
        new_state.forks = self.forks + 1
        new_state.co = State.get_new_id()
        new_state.input_symbols = self.input_symbols
        new_state.branches = self.branches
        self._child = new_state
        return new_state

    def __exit__(self, ty, value, traceback):
        self.constraints.__exit__(ty, value, traceback)
        self._child = None

    def execute(self):
        trace_item = (self.model._current, self.cpu.PC)
        try:
            result = self.model.execute()
        except:
            trace_item = None
            raise
        assert self.model.constraints is self.constraints
        assert self.mem.constraints is self.constraints
        self.visited.add(trace_item)
        self.last_pc = trace_item
        return result

    def add(self, constraint, check=False):
        self.constraints.add(constraint)

    def abandon(self):
        '''Abandon the currently-active state.

        Note: This must be called from the Executor loop, or a :func:`~manticore.Manticore.hook`.
        '''
        raise AbandonState

    def new_symbolic_buffer(self, nbytes, **options):
        '''Create and return a symbolic buffer of length `nbytes`. The buffer is
        not written into State's memory; write it to the state's memory to
        introduce it into the program state.

        :param int nbytes: Length of the new buffer
        :param str name: (keyword arg only) The name to assign to the buffer
        :param bool cstring: (keyword arg only) Whether or not to enforce that the buffer is a cstring
                 (i.e. no \0 bytes, except for the last byte). (bool)

        :return: :class:`~manticore.core.smtlib.expression.Expression` representing the buffer.
        '''
        name = options.get('name', 'buffer')
        expr = self.constraints.new_array(name=name, index_max=nbytes)
        self.input_symbols.append(expr)

        if options.get('cstring', False):
            for i in range(nbytes - 1):
                self.constraints.add(expr[i] != 0)

        return expr

    def new_symbolic_value(self, nbits, label='val', taint=frozenset()):
        '''Create and return a symbolic value that is `nbits` bits wide. Assign
        the value to a register or write it into the address space to introduce
        it into the program state.

        :param int nbits: The bitwidth of the value returned
        :param str label: The label to assign to the value
        :param taint: Taint identifier of this value
        :type taint: tuple or frozenset
        :return: :class:`~manticore.core.smtlib.expression.Expression` representing the value
        '''
        assert nbits in (1, 4, 8, 16, 32, 64, 128, 256)
        expr = self.constraints.new_bitvec(nbits, name=label, taint=taint)
        self.input_symbols.append(expr)
        return expr

    def symbolicate_buffer(self, data, label='INPUT', wildcard='+', string=False):
        '''Mark parts of a buffer as symbolic (demarked by the wildcard byte)

        :param str data: The string to symbolicate. If no wildcard bytes are provided,
                this is the identity function on the first argument.
        :param str label: The label to assign to the value
        :param str wildcard: The byte that is considered a wildcard
        :param bool string: Ensure bytes returned can not be \0

        :return: If data does not contain any wildcard bytes, data itself. Otherwise,
            a list of values derived from data. Non-wildcard bytes are kept as
            is, wildcard bytes are replaced by Expression objects.
        '''
        if wildcard in data:
            size = len(data)
            symb = self.constraints.new_array(name=label, index_max=size)
            self.input_symbols.append(symb)
            for j in xrange(size):
                if data[j] != wildcard:
                    symb[j] = data[j]
            data = [symb[i] for i in range(size)]

        if string:
            for b in data:
                if issymbolic(b):
                    self.constraints.add(b != 0)
                else:
                    assert b != 0
        return data

    def concretize(self, symbolic, policy, maxcount=100):
        vals = []
        if policy == 'MINMAX':
            vals = solver.minmax(self.constraints, symbolic)
        elif policy == 'SAMPLED':
            m, M = solver.minmax(self.constraints, symbolic)
            vals += [m, M]
            if M - m > 3:
                if solver.can_be_true(self.constraints, symbolic == (m + M) / 2):
                    vals.append((m + M) / 2)
            if M - m > 100:
                vals += solver.get_all_values(self.constraints, symbolic, maxcnt=maxcount,
                                              silent=True)
        else:
            assert policy == 'ALL'
            vals = solver.get_all_values(self.constraints, symbolic, maxcnt=maxcount,
                                         silent=False)

        return list(set(vals))

    @property
    def _solver(self):
        from .smtlib import solver
        return solver

    def solve_one(self, expr):
        '''
        Concretize a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        one solution.

        :param manticore.core.smtlib.Expression expr: Symbolic value to concretize
        :return: Concrete value
        :rtype: int
        '''
        return self._solver.get_value(self.constraints, expr)

    def solve_n(self, expr, nsolves=1, policy='minmax'):
        '''
        Concretize a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        `nsolves` solutions.

        :param manticore.core.smtlib.Expression expr: Symbolic value to concretize
        :return: Concrete value
        :rtype: list[int]
        '''
        return self._solver.get_all_values(self.constraints, expr, nsolves, silent=True)

    def record_branches(self, targets):
        _, branch = self.last_pc
        for target in targets:
            key = (branch, target)
            try:
                self.branches[key] += 1
            except KeyError:
                self.branches[key] = 1
