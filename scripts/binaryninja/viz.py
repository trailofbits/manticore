from binaryninja import *
import os.path

blue = HighlightStandardColor.BlueHighlightColor
black = HighlightStandardColor.BlackHighlightColor
white = HighlightStandardColor.WhiteHighlightColor
clear = HighlightStandardColor.NoHighlightColor


MBASE = 0x0007fffffdb7000


def viz(view, fname, base=0):
    """
    Given a Manticore workspace, or trace file, highlight the basic blocks.
    """
    fname = fname.replace('/mnt/hgfs', '~')
    fname = os.path.expanduser(fname)
    log_info('got: {}'.format(fname))
    if os.path.isdir(fname):
        for f in os.listdir(fname):
            if f.endswith('trace'):
                fullpath = os.path.join(fname, f)
                viz_trace(view, fullpath, base)
    else:
        viz_trace(view, fname, base)


def viz_trace(view, fname, base=0):
    """
    Given a Manticore trace file, highlight the basic blocks.
    """
    with open(os.path.expanduser(fname)) as f:
        addrs = [int(x.strip(), 0) for x in f.readlines()]
        _viz_addrs(view, addrs, base, blue)


def clear_all(view, fname, base=0):
    with open(os.path.expanduser(fname)) as f:
        addrs = [int(x.strip(), 0) for x in f.readlines()]
        _viz_addrs(view, addrs, base, white)


def _viz_addrs(view, addrs, base, hl):
    for addr in addrs:
        if base:
            addr -= base
        _highlight_block(view, addr, hl)

def _highlight_block(view, addr, hl):
    blocks = view.get_basic_blocks_at(addr)
    for b in blocks:
        b.set_user_highlight(hl)

