#!/usr/bin/env python
# -*- coding: utf-8 -*-
import os
import unittest

import shutil
from manticore.ethereum.plugins import VerboseTrace

from manticore.ethereum import ManticoreEVM


class EthPluginsTests(unittest.TestCase):
    def setUp(self):
        self.mevm = ManticoreEVM()

    def tearDown(self):
        shutil.rmtree(self.mevm.workspace)
        del self.mevm

    def test_verbose_trace(self):
        source_code = '''contract X {}'''
        self.mevm.register_plugin(VerboseTrace())

        owner = self.mevm.create_account(balance=1000)
        contract = self.mevm.solidity_create_contract(source_code, owner=owner)

        files = set(os.listdir(self.mevm.workspace))

        # self.assertEqual()

        # Shall produce a verbose trace file
        self.mevm.finalize()
