import os
import threading

from binaryninja import PluginCommand, HighlightStandardColor
from binaryninja.interaction import (
    get_open_filename_input, get_directory_name_input, get_choice_input
)

blue = HighlightStandardColor.BlueHighlightColor
black = HighlightStandardColor.BlackHighlightColor
white = HighlightStandardColor.WhiteHighlightColor
clear = HighlightStandardColor.NoHighlightColor

class TraceVisualizer(object):
    def __init__(self, view, workspace, base=0x0007fffffdb7000):
        self.view = view
        self.workspace = workspace
        self.base = base

    def visualize(self):
        """
        Given a Manticore workspace, or trace file, highlight the basic blocks.
        """
        if os.path.isfile(self.workspace):
            t = threading.Thread(target=self._highlight_from_file,
                                 args=(self.workspace,))
        elif os.path.isdir(self.workspace):
            t = threading.Thread(target=self._highlight_from_dir,
                                 args=(self.workspace,))
        t.start()

    def _highlight_from_file(self, tracefile):
        self._highlight_trace(tracefile)

    def _highlight_from_dir(self, workspace_dir):
        for f in os.listdir(workspace_dir):
            if f.endswith('trace'):
                self._highlight_trace(os.path.join(workspace_dir, f))

    def _highlight_trace(self, tracefile):
        with open(tracefile, "r") as f:
            for line in f:
                addr = int(line.strip(), 0) - self.base
                self._highlight_addr(addr, blue)

    def _highlight_addr(self, addr, hl):
        blocks = self.view.get_basic_blocks_at(addr)
        if blocks:
            blocks[0].function.set_auto_instr_highlight(addr, hl)

    def _higlight_block(self, addr, hl):
        blocks = self.view.get_basic_blocks_at(addr)
        for b in blocks:
            b.set_user_highlight(hl)

def viz_trace(view):
    """
    Given a Manticore trace file, highlight the basic blocks.
    """
    choice = get_choice_input("Select Trace Type",
                              "Input",
                              ["Trace File", "Manticore Workspace"])
    if choice == 0:
        workspace = get_open_filename_input('Trace File')
    else:
        workspace = get_directory_name_input('Workspace Directory')
    tv = TraceVisualizer(view, workspace)
    tv.visualize()

def clear_all(view):
    for f in view.functions:
        for bb in f.basic_blocks:
            bb.set_user_highlight(clear)

PluginCommand.register("Highlight Manticore Trace", "Highlight Manticore Execution Trace", viz_trace)
PluginCommand.register("Clear Manticore Trace", "Clear Manticore Trace Highlight", clear_all)
