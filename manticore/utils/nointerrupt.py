import signal
import logging


class WithKeyboardInterruptAs:
    def __init__(self, callback):
        if callback is None:
            callback = lambda *args, **kwargs: None
        self.callback = callback

    def __enter__(self):
        self.signal_received = 0
        self.old_handler = signal.getsignal(signal.SIGINT)
        try:
            signal.signal(signal.SIGINT, self.handler)
        except ValueError as e:
            logging.debug(e)

    def handler(self, sig, frame):
        self.signal_received += 1
        if self.signal_received > 3:
            self.old_handler(sig, frame)
        else:
            self.callback()
            logging.debug("SIGINT received. Supressing KeyboardInterrupt.")

    def __exit__(self, type, value, traceback):
        try:
            signal.signal(signal.SIGINT, self.old_handler)
        except ValueError as e:
            logging.debug(e)
