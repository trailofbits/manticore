import fcntl
import os
import time
import threading

from binaryninja import PluginCommand, HighlightStandardColor, log
from binaryninja.interaction import (
    get_open_filename_input, get_directory_name_input, get_choice_input
)
import binaryninja.enums as enums

blue = HighlightStandardColor.BlueHighlightColor
black = HighlightStandardColor.BlackHighlightColor
white = HighlightStandardColor.WhiteHighlightColor
clear = HighlightStandardColor.NoHighlightColor
# renew interval
interval = 1.5

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
        # highlighted addresses
        self.highlighted = set()
        # covered basic blocks
        self.cov_bb = set()
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
            self.compute_coverage()
            if not self.live_update:
                break

    def highlight_from_dir(self, workspace_dir):
        while True:
            time.sleep(interval)
            for f in os.listdir(workspace_dir):
                if f.endswith('trace'):
                    self.highlight_trace(os.path.join(workspace_dir, f))
            self.compute_coverage()
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
            self.cov_bb.add(blocks[0].start)
            if self.live_update:
                blocks[0].function.set_auto_instr_highlight(addr, white)
                time.sleep(0.1)
                blocks[0].function.set_auto_instr_highlight(addr, clear)

    def highlight_block(self, addr, hl):
        blocks = self.view.get_basic_blocks_at(addr)
        for b in blocks:
            b.set_user_highlight(hl)

    def set_comment_at_xref(self, xref, comment):
        try:
            op = xref.function.get_lifted_il_at(xref.address).operation
        except IndexError:
            w = "ManticoreTrace: Could not lookup " + hex(xref.address)
            w += " address for funciton " + str(xref.function)
            log.log_warn(w)
            return
        if not (op == enums.LowLevelILOperation.LLIL_CALL or
                op == enums.LowLevelILOperation.LLIL_JUMP or
                op == enums.LowLevelILOperation.LLIL_JUMP_TO or
                op == enums.LowLevelILOperation.LLIL_SYSCALL or
                op == enums.LowLevelILOperation.LLIL_GOTO):
            return
        xref.function.set_comment_at(xref.address, comment)


    def compute_coverage(self):
        # function cumulative bb coverage
        # key: function address
        # values: [total basic blocks covered, xrefs to function]
        fun_cov = {f.start : [0, 0] for f in self.view.functions}
        fun_xrefs = sorted([(f, self.view.get_code_refs(f.start))
                            for f in self.view.functions],
                           key=lambda x: len(x[1]))

        for f, xrefs in fun_xrefs:
            if not f.basic_blocks:
                continue
            cov = (len(
                (set([b.start for b in f.basic_blocks])
                 .intersection(self.cov_bb))
            ) / float(len(set(f.basic_blocks))))
            fun_cov[f.start][0] += cov
            for xref_f in xrefs:
                fun_cov[xref_f.function.start][0] += cov
                fun_cov[xref_f.function.start][1] += 1

        for f, xrefs in fun_xrefs:
            cov = str((fun_cov[f.start][0] * 100.0) / (fun_cov[f.start][1] + 1))
            cov += "% cumulative BB coverage"
            f.set_comment(f.start, "Function Stats: \n" + cov)
            for xref in xrefs:
                self.set_comment_at_xref(xref, cov)

    def clear_stats(self):
        self.highlighted.clear()
        self.cov_bb.clear()
        fun_xrefs = sorted([(f, self.view.get_code_refs(f.start))
                            for f in self.view.functions],
                           key=lambda x: len(x[1]))
        for f, xrefs in fun_xrefs:
            f.set_comment(f.start, None)
            for xref in xrefs:
                self.set_comment_at_xref(xref, None)

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
    tv.clear_stats()

PluginCommand.register("ManticoreTrace: Highlight",
                       "Highlight Manticore Execution Trace",
                       viz_trace)
PluginCommand.register("ManticoreTrace: Live Highlight",
                       "Highlight Manticore Execution Trace at Real-Time",
                       viz_live_trace)
PluginCommand.register("ManticoreTrace: Clear",
                       "Clear Manticore Trace Highlight",
                       clear_all)
