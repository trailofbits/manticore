#!/usr/bin/env python

import sys
from manticore.native import Manticore

# This example demonstrates loading a simple binary in Manticore,
# running it to completion without any callbacks or instrumentation
# and producing basic information about the paths explored


if __name__ == "__main__":
    path = sys.argv[1]
    # Create a new Manticore object
    m = Manticore(path)
    m.run()
