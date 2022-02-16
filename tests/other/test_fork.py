import unittest
import tempfile
from manticore.native import Manticore
from manticore.core.state import Concretize
from pathlib import Path
from glob import glob


class TestFork(unittest.TestCase):
    def test_fork_unique_solution(self):
        binary = str(
            Path(__file__).parent.parent.parent.joinpath(
                "tests", "native", "binaries", "hello_world"
            )
        )
        tmp_dir = tempfile.TemporaryDirectory(prefix="mcore_test_fork_")
        m = Manticore(binary, stdin_size=10, workspace_url=str(tmp_dir.name))

        @m.hook(0x3E50)  # Entrypoint
        def concretize_var(state):
            # Concretize symbolic var that has only 1 solution
            var = BitVecVariable(size=32, name="bar")
            state.constrain(var == 5)
            raise Concretize(var)

        m.run()
        m.finalize()

        # Check that no additional state was created when forking
        states = f"{str(m.workspace)}/test_*.pkl"
        self.assertEqual(len(glob(states)), 1)


if __name__ == "__main__":
    unittest.main()
