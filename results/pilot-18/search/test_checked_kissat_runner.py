"""Small controls only; no assigned search instances or lease calls."""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

ROOT=Path('/tmp/oec/pequalnp-pilot-18/lean-setup')
SCRIPT=ROOT/'run_checked_kissat.py'
KISSAT=Path('/tmp/oec/pequalnp-pilot-18/solver/kissat-4.0.4-linux-amd64')
CHECKER=Path('/tmp/oec/pequalnp-pilot-18/solver/dsr-trim/bin/dsr-trim')
CHECKER_SHA='e6894b5b74ac2c09b494344f397ec5111547aaa782cdb399f1a8b6835ecef84b'
CONTROL_ROOT=ROOT/'streaming-controls'
CONTROL_ROOT.mkdir(exist_ok=True)
RECORDS=[]


class RunnerControls(unittest.TestCase):
    def setUp(self):
        self.directory=Path(tempfile.mkdtemp(prefix=self._testMethodName+'-',dir=CONTROL_ROOT))
        self.unsat=self.directory/'unsat.cnf'
        self.sat=self.directory/'sat.cnf'
        self.unsat.write_text('p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n')
        self.sat.write_text('p cnf 2 3\n1 2 0\n1 -2 0\n-1 2 0\n')

    def helper(self,body,name='producer.py'):
        p=self.directory/name
        p.write_text('#!'+sys.executable+'\nimport os,sys,time,signal\n'+body)
        p.chmod(0o700)
        return p

    def command(self,cnf=None,solver=KISSAT,extra=(),checker=CHECKER,checksum=CHECKER_SHA):
        return [sys.executable,str(SCRIPT),str(cnf or self.unsat),str(self.directory/'run'),
                '--solver',str(solver),'--checker',str(checker),'--checker-sha256',checksum,
                '--max-seconds','15','--kill-grace-seconds','0.15',*extra]

    def finish(self,command,expected,status):
        with (self.directory/'runner.stdout.txt').open('wb') as out, (self.directory/'runner.stderr.txt').open('wb') as err:
            p=subprocess.run(command,cwd=ROOT,stdout=out,stderr=err,timeout=25)
        self.assertEqual(p.returncode,expected,(self.directory/'runner.stderr.txt').read_text())
        report=json.loads((self.directory/'run/result.json').read_text())
        self.assertEqual(report['status'],status,report)
        self.assertFalse((self.directory/'run/proof.fifo').exists())
        self.assertLessEqual(report['max_pending_bytes'],1048576)
        self.assertEqual(report['accepted_CNF_UNSAT'],status=='VERIFIED_UNSAT')
        RECORDS.append({'test':self._testMethodName,'path':str(self.directory),'report':report})
        return report

    def test_real_kissat_unsat(self):
        r=self.finish(self.command(),0,'VERIFIED_UNSAT')
        self.assertEqual((r['solver_exit'],r['checker_exit']),(20,0))
        self.assertEqual(r['checker_verdicts'],['s VERIFIED UNSAT'])
        self.assertTrue(r['proof_stream_complete'])
        self.assertGreater(r['proof_bytes_read'],0)

    def test_real_kissat_sat(self):
        r=self.finish(self.command(cnf=self.sat),10,'SAT_UNVALIDATED')
        self.assertEqual(r['solver_verdicts'],['s SATISFIABLE'])
        self.assertEqual(r['checker_verdicts'],['s VALID'])

    def test_invalid_empty_clause_rejected_by_real_checker(self):
        solver=self.helper("with open(sys.argv[-1],'wb') as f: f.write(b'a\\0')\nprint('s UNSATISFIABLE',flush=True)\nsys.exit(20)\n")
        r=self.finish(self.command(cnf=self.sat,solver=solver),1,'FAILED')
        self.assertEqual(r['checker_exit'],1)
        self.assertIn('empty clause',(self.directory/'run/checker.stderr.txt').read_text())

    def test_valid_without_empty_clause_never_accepted(self):
        solver=self.helper("open(sys.argv[-1],'wb').close()\nprint('s UNSATISFIABLE',flush=True)\nsys.exit(20)\n")
        r=self.finish(self.command(cnf=self.sat,solver=solver),1,'FAILED')
        self.assertEqual(r['checker_exit'],0)
        self.assertEqual(r['checker_verdicts'],['s VALID'])

    def test_unknown(self):
        solver=self.helper("open(sys.argv[-1],'wb').close()\nprint('s UNKNOWN',flush=True)\nsys.exit(0)\n")
        self.finish(self.command(cnf=self.sat,solver=solver),2,'UNKNOWN')

    def test_zero_exit_with_valid_proof_is_not_solver_unsat20(self):
        solver=self.helper("with open(sys.argv[-1],'wb') as f: f.write(b'a\\x02\\0a\\0')\nprint('s UNSATISFIABLE',flush=True)\nsys.exit(0)\n")
        r=self.finish(self.command(solver=solver),1,'FAILED')
        self.assertEqual(r['checker_verdicts'],['s VERIFIED UNSAT'])

    def test_checker_failure_before_fifo_producer_opens(self):
        checker=self.helper("sys.exit(7)\n",'checker.py')
        solver=self.helper("time.sleep(10)\nwith open(sys.argv[-1],'wb') as f: f.write(b'a\\0')\n")
        r=self.finish(self.command(solver=solver,checker=checker,checksum=hashlib.sha256(checker.read_bytes()).hexdigest()),1,'FAILED')
        self.assertEqual(r['checker_exit'],7)
        self.assertLess(r['elapsed_seconds'],3)

    def test_timeout_escalates_and_cleans_fifo(self):
        solver=self.helper("signal.signal(signal.SIGTERM,signal.SIG_IGN)\nf=open(sys.argv[-1],'wb')\ntime.sleep(10)\n")
        r=self.finish(self.command(solver=solver,extra=['--max-seconds','0.4']),3,'ABORTED')
        self.assertEqual(r['reason'],'wall_time_limit')
        self.assertEqual(r['solver_exit'],-signal.SIGKILL)

    def test_preexisting_abort_file_starts_no_worker(self):
        abort=self.directory/'abort.request'
        abort.touch()
        r=self.finish(self.command(extra=['--abort-file',str(abort)]),3,'ABORTED')
        self.assertIsNone(r['solver_pid'])
        self.assertIsNone(r['checker_pid'])

    def test_lease_loss_sentinel_and_sigterm_shutdown(self):
        # Only the sentinel's existence is observed; it contains no lease data.
        for mechanism in ('sentinel','sigterm'):
            with self.subTest(mechanism=mechanism):
                sub=self.directory/mechanism; sub.mkdir()
                abort=sub/'abort.request'
                solver=self.helper("f=open(sys.argv[-1],'wb')\nf.write(b'a\\x02\\x04\\0');f.flush()\ntime.sleep(10)\n",mechanism+'.py')
                command=self.command(solver=solver,extra=['--abort-file',str(abort)])
                command[3]=str(sub/'run')
                with (sub/'runner.stdout.txt').open('wb') as out,(sub/'runner.stderr.txt').open('wb') as err:
                    p=subprocess.Popen(command,cwd=ROOT,stdout=out,stderr=err)
                    deadline=time.monotonic()+4
                    while not (sub/'run/progress.json').exists() and p.poll() is None and time.monotonic()<deadline:
                        time.sleep(.02)
                    self.assertTrue((sub/'run/progress.json').exists())
                    if mechanism=='sentinel':abort.touch()
                    else:p.send_signal(signal.SIGTERM)
                    self.assertEqual(p.wait(timeout=4),3)
                r=json.loads((sub/'run/result.json').read_text())
                self.assertFalse(r['accepted_CNF_UNSAT'])
                self.assertFalse((sub/'run/proof.fifo').exists())
                self.assertIn(r['reason'],('external_abort_file','signal_SIGTERM'))
                RECORDS.append({'test':self._testMethodName+'_'+mechanism,'path':str(sub),'report':r})

    def test_proof_record_guard(self):
        solver=self.helper("with open(sys.argv[-1],'wb') as f: f.write(b'a\\x02\\x04\\0'*100)\nprint('s UNKNOWN',flush=True)\n")
        r=self.finish(self.command(solver=solver,extra=['--max-proof-records','10']),3,'ABORTED')
        self.assertEqual(r['reason'],'proof_record_safety_limit')

    @unittest.skipUnless(sys.platform.startswith('linux'), 'Linux parent-death signal')
    def test_supervisor_sigkill_stops_direct_workers(self):
        solver=self.helper("f=open(sys.argv[-1],'wb')\nf.write(b'a\\x02\\x04\\0');f.flush()\ntime.sleep(10)\n")
        with (self.directory/'runner.stdout.txt').open('wb') as out,(self.directory/'runner.stderr.txt').open('wb') as err:
            p=subprocess.Popen(self.command(solver=solver),cwd=ROOT,stdout=out,stderr=err)
            progress=self.directory/'run/progress.json'
            deadline=time.monotonic()+4
            while not progress.exists() and p.poll() is None and time.monotonic()<deadline:
                time.sleep(.02)
            self.assertTrue(progress.exists())
            state=json.loads(progress.read_text())
            p.kill()
            self.assertEqual(p.wait(timeout=4),-signal.SIGKILL)
        def running(pid):
            try:
                with open(f'/proc/{pid}/status') as stream:
                    for line in stream:
                        if line.startswith('State:'):
                            return line.split()[1] not in ('Z','X')
            except FileNotFoundError:
                return False
            return True
        deadline=time.monotonic()+3
        while any(running(state[k]) for k in ('solver_pid','checker_pid')) and time.monotonic()<deadline:
            time.sleep(.02)
        self.assertFalse(any(running(state[k]) for k in ('solver_pid','checker_pid')))
        self.assertFalse((self.directory/'run/result.json').exists())
        RECORDS.append({'test':self._testMethodName,'path':str(self.directory),
                        'workers_stopped':True,'no_final_acceptance_record':True})

    def test_checker_hash_mismatch_starts_no_worker(self):
        r=self.finish(self.command(checksum='0'*64),1,'FAILED')
        self.assertIsNone(r['solver_pid'])

    def test_early_verified_checker_drains_and_hashes_all_bytes(self):
        # A valid UNSAT prefix followed by redundant data tests DSR's legitimate
        # early exit and bounded draining after it has verified the empty clause.
        count=262144
        solver=self.helper("with open(sys.argv[-1],'wb') as f:\n f.write(b'a\\x02\\0a\\0');f.flush()\n time.sleep(.15)\n for _ in range(16): f.write(b'a\\x02\\x04\\0'*16384)\nprint('s UNSATISFIABLE',flush=True)\nsys.exit(20)\n")
        r=self.finish(self.command(solver=solver),0,'VERIFIED_UNSAT')
        proof=b'a\x02\0a\0'+b'a\x02\x04\0'*count
        self.assertEqual(r['proof_bytes_read'],len(proof))
        self.assertEqual(r['proof_sha256'],hashlib.sha256(proof).hexdigest())
        self.assertTrue(r['proof_stream_complete'])
        self.assertGreater(r['proof_bytes_not_forwarded'],0)

    def test_eight_megabyte_transport_and_duplicate_clause_control(self):
        solver=self.helper("with open(sys.argv[-1],'wb') as f:\n for _ in range(128):f.write(b'a\\x02\\x04\\0'*16384)\n f.write(b'a\\x02\\0a\\0')\nprint('s UNSATISFIABLE',flush=True)\nsys.exit(20)\n")
        r=self.finish(self.command(solver=solver),0,'VERIFIED_UNSAT')
        h=hashlib.sha256()
        for _ in range(128):h.update(b'a\x02\x04\0'*16384)
        h.update(b'a\x02\0a\0')
        self.assertEqual(r['proof_bytes_read'],8388613)
        self.assertEqual(r['proof_sha256'],h.hexdigest())
        self.assertEqual(r['zero_bytes_counted'],2097154)


if __name__=='__main__':
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(RunnerControls))
    (ROOT/'streaming-controls.json').write_text(json.dumps({'status':'PASS' if result.wasSuccessful() else 'FAIL',
        'tests_run':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),
        'runner_sha256':hashlib.sha256(SCRIPT.read_bytes()).hexdigest(),
        'checker_sha256':CHECKER_SHA,'controls':RECORDS},indent=2)+'\n')
    sys.exit(0 if result.wasSuccessful() else 1)
