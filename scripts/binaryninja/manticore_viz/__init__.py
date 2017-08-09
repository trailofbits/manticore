import fcntl
import os
import time
import threading

from binaryninja import PluginCommand, HighlightStandardColor
from binaryninja.interaction import (
    get_open_filename_input, get_directory_name_input, get_choice_input
)

blue = HighlightStandardColor.BlueHighlightColor
black = HighlightStandardColor.BlackHighlightColor
white = HighlightStandardColor.WhiteHighlightColor
clear = HighlightStandardColor.NoHighlightColor
# renew interval
interval = 1

class Singleton(type):
    _instances = {}
    def __call__(cls, *args, **kwargs):
        if cls not in cls._instances:
            cls._instances[cls] = super(Singleton, cls).__call__(*args, **kwargs)
        return cls._instances[cls]

class TraceVisualizer(object):
    __metaclass__ = Singleton
    def __init__(self, view, workspace, base=0x0, live=False):
        self.view = view
        self.workspace = workspace
        self.base = base
        self.highlighted = set()
        self.current_function = None
        self.live_update = live

    def visualize(self):
        """
        Given a Manticore workspace, or trace file, highlight the basic blocks.
        """
        if os.path.isfile(self.workspace):
            t = threading.Thread(target=self.highlight_from_file,
                                 args=(self.workspace,))
        elif os.path.isdir(self.workspace):
            t = threading.Thread(target=self.highlight_from_dir,
                                 args=(self.workspace,))
        t.start()

    def highlight_from_file(self, tracefile):
        while True:
            time.sleep(interval)
            self.highlight_trace(tracefile)
            if not self.live_update:
                break

    def highlight_from_dir(self, workspace_dir):
        while True:
            time.sleep(interval)
            for f in os.listdir(workspace_dir):
                if f.endswith('trace'):
                    self.highlight_trace(os.path.join(workspace_dir, f))
            if not self.live_update:
                break

    def highlight_trace(self, tracefile):
        f = open(tracefile, "r")
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        trace_addr = set()
        for line in f:
            trace_addr.add(int(line.strip(), 0) - self.base)

        for addr in trace_addr - self.highlighted:
            self.highlight_addr(addr, blue)
        fcntl.flock(f, fcntl.LOCK_UN)
        f.close()

    def highlight_addr(self, addr, hl):
        blocks = self.view.get_basic_blocks_at(addr)
        if blocks:
            blocks[0].set_user_highlight(hl)
            if self.live_update and blocks[0].function != self.current_function:
                self.current_function = blocks[0].function
                self.view.file.navigate(self.view.file.view, blocks[0].start)
            self.highlighted.add(addr)
            if self.live_update:
                blocks[0].function.set_auto_instr_highlight(addr, white)
                time.sleep(0.1)
                blocks[0].function.set_auto_instr_highlight(addr, clear)

    def highlight_block(self, addr, hl):
        blocks = self.view.get_basic_blocks_at(addr)
        for b in blocks:
            b.set_user_highlight(hl)

def get_workspace():
    choice = get_choice_input("Select Trace Type",
                              "Input",
                              ["Trace File", "Manticore Workspace"])
    if choice == 0:
        workspace = get_open_filename_input('Trace File')
    else:
        workspace = get_directory_name_input('Workspace Directory')
    return workspace

def viz_trace(view):
    """
    Given a Manticore trace file, highlight the basic blocks.
    """
    tv = TraceVisualizer(view, None)
    if tv.workspace is None:
        tv.workspace = get_workspace()
    tv.visualize()

def viz_live_trace(view):
    """
    Given a Manticore trace file, highlight the basic blocks.
    """
    tv = TraceVisualizer(view, None, live=True)
    if tv.workspace is None:
        tv.workspace = get_workspace()
    # update due to singleton in case we are called after a clear
    tv.live_update = True
    tv.visualize()

def clear_all(view):
    tv = TraceVisualizer(view, None)
    for addr in tv.highlighted:
        tv.highlight_block(addr, clear)
    tv.live_update = False
    tv.highlighted.clear()

PluginCommand.register("ManticoreTrace: Highlight",
                       "Highlight Manticore Execution Trace",
                       viz_trace)
PluginCommand.register("ManticoreTrace: Live Highlight",
                       "Highlight Manticore Execution Trace at Real-Time",
                       viz_live_trace)
PluginCommand.register("ManticoreTrace: Clear",
                       "Clear Manticore Trace Highlight",
                       clear_all)
