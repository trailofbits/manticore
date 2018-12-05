#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import doctest

from manticore.utils import rlp


def load_tests(loader, tests, ignore):
    tests.addTests(doctest.DocTestSuite(rlp))
    return tests    


if __name__ == '__main__':
    import unittest
    unittest.main()
