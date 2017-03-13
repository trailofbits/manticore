# Copyright (c) 2013, Felipe Andres Manzano
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#     * Redistributions of source code must retain the above copyright notice,
#       this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice,this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#     * Neither the name of the copyright holder nor the names of its
#       contributors may be used to endorse or promote products derived from
#       this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.

import unittest
import sys
import shutil
import tempfile
import os
import hashlib
import subprocess
import json
import time

#logging.basicConfig(filename = "test.log",
#                format = "%(asctime)s: %(name)s:%(levelname)s: %(message)s",
#                level = logging.DEBUG)

class IntegrationTest(unittest.TestCase):
    def setUp(self):
        # Create a temporary directory
        self.test_dir = tempfile.mkdtemp()

    def tearDown(self):
        # Remove the directory after the test
        shutil.rmtree(self.test_dir)
        
    def _getDumpParams(self, jsonf):
        self.assertTrue(os.path.exists(jsonf))

        c = open(jsonf, 'r').read()
        return json.loads(c)

    def _loadVisitedSet(self, visited):

        self.assertTrue(os.path.exists(visited))
        vitems = open(visited, 'r').read().splitlines()

        vitems = map(lambda x: int(x[2:], 16), vitems)

        return set(vitems)

    def _runWithTimeout(self, procargs, timeout=600):

        po = subprocess.Popen(procargs)
        secs_used = 0

        while po.poll() is None and secs_used < timeout:
            time.sleep(1)
            sys.stderr.write("~")
            secs_used += 1

        self.assertTrue(secs_used < timeout)
        sys.stderr.write("\n")

    def _runManticore(self, dumpname):

        dirname = os.path.dirname(__file__)
        dumpdir = os.path.abspath(os.path.join(dirname, 'memdumps', dumpname))

        self.assertTrue(os.path.exists(dumpdir))

        jsonfile = os.path.join(dumpdir, 'args.json')

        params = self._getDumpParams(jsonfile)

        workspace = os.path.join(self.test_dir, 'ws_{}'.format(dumpname))
        logfile = os.path.join(workspace, "output.log")

        dumpfile = os.path.join(dumpdir, params['dump'])

        args = ['manticore', '--workspace', workspace, '--log', logfile, dumpfile]

        for k,v in params.iteritems():
            if k.startswith("--"):
                args.extend([k, v.format(dumpdir=dumpdir, workspace=workspace)])
        self._runWithTimeout(args)

        efile = os.path.join(dumpdir, params['expected'])
        expected = self._loadVisitedSet(efile)

        afile = os.path.join(workspace, params['actual'])
        actual = self._loadVisitedSet(afile)

        self.assertEqual(actual, expected)

    def testSimpleParse(self):
        self._runManticore("simple_parse")

    def testSimpleDeref(self):
        self._runManticore("simple_bad_deref")

    def testSimpleBufferOverflow(self):
        self._runManticore("simple_buffer_overflow")

    # generate too many states on memory concretization
    #def testSimpleFpu(self):
    #    self._runManticore("simple_fpu")

    # too slow processing REP SCASD
    @unittest.skip('TODO(mark); skipping so we can move on with our lives and merge x86_new. ask felipe to fix later.')
    def testWin32API(self):
        self._runManticore("win32_api_test")

    def testAPIInterception(self):
        self._runManticore("api_interception")

if __name__ == '__main__':
    unittest.main()

