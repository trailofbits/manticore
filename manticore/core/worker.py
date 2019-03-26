from ..utils.nointerrupt import WithKeyboardInterruptAs
from .state import Concretize, TerminateState
import logging
import multiprocessing
import threading
import os


logger = logging.getLogger(__name__)


# Workers
# There are 4 types of Workers
# WorkerSingle: run over main process and will not provide any concurrency
# WorkerThread: runs on a different thread
# WorkerProcess: runs on a different process - Full multiprocessing
# WorkerMultiprocessing: --planned-- runs on a different computer

class Worker:
    """
        A Manticore Worker.
        This will run forever potentially in a different process. Normally it
        will be spawned at Manticore constructor and will stay alive until killed.
        A Worker can be in 3 phases: STANDBY, RUNNING, KILLED. And will react to
        different events: start, stop, kill.
        The events are transmitted via 2 conditional variable: m._killed and
        m._started.

            STANDBY:   Waiting for the start event
            RUNNING:   Exploring and spawning states until no more READY states or
                       the cancel event is received
            KIlLED:    This is the end. No more manticoring in this worker process

                         +---------+     +---------+
                    +--->+ STANDBY +<--->+ RUNNING |
                         +-+-------+     +-------+-+
                           |                     |
                           |      +--------+     |
                           +----->+ KILLED <-----+
                                  +----+---+
                                       |
                                       #
    """

    def __init__(self, *, id, manticore, single=False):
        self.manticore = manticore
        self.id = id
        self.single = single

    def start(self):
        raise NotImplementedError

    def join(self):
        raise NotImplementedError

    def run(self, *args):
        # This controls the main symbolic execution loop of one of the workers
        logger.debug("Starting Manticore Symbolic Emulator Worker %d. Pid %d Tid %d).", self.id, os.getpid(), threading.get_ident())

        m = self.manticore
        current_state = None
        m._publish("will_start_worker", self.id)

        # If CTRL+C is received at any worker lets abort exploration via m.kill()
        # kill will set m._killed flag to true and then each worker will slowly
        # get out of its mainloop and quit.
        with WithKeyboardInterruptAs(m.kill):

            # The worker runs until the manticore is killed
            while not m._killed.value:

                # STARTED - Will try to consume states until a STOP event is received
                # Outer loop, Keep getting states until someone request us to STOP
                try:  # handle fatal errors even exceptions in the exception handlers
                    try:  # handle Concretize and TerminateState

                        # At RUNNING
                        # The START has been requested, we operate with under the assumption
                        # that manticore we will let us stay at this phase for a _while_
                        # Requests to STOP will we honored ASAP (i.e. Not immediately)

                        # Select a single state
                        # wait for other worker to add states to the READY list
                        # This momentarily get the main lock and then releases
                        # it while waiting for changes
                        # Raises an Exception if manticore gets cancelled
                        # while waiting or if there are no more potential states
                        logger.debug("[%r] Waiting for states", self.id)
                        # If at STANDBY wait for any change
                        with m._lock:
                            # If not started and not killed it means we need to wait
                            while not m._started.value and not m._killed.value:
                                logger.debug("[%r] Standing by", self.id)
                                m._lock.wait()  # Wait until something changes
                            if not m._started.value or m._killed.value:
                                current_state = None
                            else:
                                current_state = m._get_state(wait=True)

                        # there are no more states to process
                        # states can come from the ready list or by forking
                        # states currently being analyzed in the busy list
                        if current_state is None:
                            logger.debug("[%r] No more states", self.id)
                            if self.single:
                                # at single it will run in place. No need to wait.
                                break
                            else:
                                continue

                        # assert current_state is not None
                        # Allows to terminate manticore worker on user request
                        # even in the middle of an execution
                        logger.debug("[%r] Running", self.id)
                        assert current_state.id in m._busy_states and current_state.id not in m._ready_states

                        # This does not hold the lock so we may loss some event
                        # flickering
                        while m._started.value and not m._killed.value:
                            current_state.execute()
                        else:
                            logger.debug("[%r] Stopped and/or Killed", self.id)
                            # On going execution was stopped or killed. Lets
                            # save any progress on the current state
                            m._save(current_state, state_id=current_state.id)
                            m._revive(current_state.id)
                            current_state = None

                        assert current_state is None
                    # Handling Forking and terminating exceptions
                    except Concretize as exc:
                        logger.debug("[%r] Debug %r", self.id, exc)
                        # The fork() method can decides which state to keep
                        # exploring. For example when the fork results in a
                        # single state it is better to just keep going.
                        # Though, normally fork() saves the spawned childs,
                        # returns a None and let _get_state choose what to explore
                        # next
                        m._fork(current_state, exc.expression, exc.policy, exc.setstate)
                        current_state = None

                    except TerminateState as exc:
                        logger.debug("[%r] Debug State %r %r", self.id, current_state, exc)
                        # Notify this state is done
                        m._publish('will_terminate_state', current_state, exc)
                        # Update the stored version of the current state
                        m._save(current_state, state_id=current_state.id)
                        # Add the state to the terminated state list
                        m._terminate(current_state.id)
                        m._publish('did_terminate_state', current_state, exc)
                        current_state = None

                except (Exception, AssertionError) as exc:
                    logger.error("[%r] Exception %r. Current State %r", self.id, exc, current_state)
                    # Internal Exception
                    # Add the state to the terminated state list
                    if current_state is not None:
                        # Drop any work on this state in case it is inconsistent
                        with m._lock:
                            m._busy_states.remove(current_state.id)
                            m._killed_states.append(current_state.id)
                        current_state = None
                    break

            # Getting out.
            # At KILLED
            logger.debug("[%r] Getting out of the mainloop %r %r", self.id, m._started.value, m._killed.value)
            m._publish("did_terminate_worker", self.id)


class WorkerSingle(Worker):
    """ A single worker that will run in the current process and current thread.
        As this will not provide any concurrency is normally only used for
        profiling underlying arch emulation and debugging."""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, single=True, **kwargs)

    def start(self):
        pass

    def join(self):
        pass


class WorkerThread(Worker):
    """ A worker thread """
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._t = threading.Thread(target=self.run)

    def start(self):
        self._t.start()

    def join(self):
        self._t.join()


class WorkerProcess(Worker):
    """ A worker process """
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._p = multiprocessing.Process(target=self.run)

    def start(self):
        self._p.start()

    def join(self):
        self._p.join()
