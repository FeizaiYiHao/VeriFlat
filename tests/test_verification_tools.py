"""Exercise reporting failures and independent captures without running Verus."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class TimingToolsTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name in ['smt_times.sh', 'module_times.sh', 'verification_times.sh', 'smt_parse.py']:
            shutil.copy2(ROOT / name, self.root / name)
        row = {'function': 'example::work', 'time-micros': 150000, 'rlimit': 80,
               'mode:': 'exec', 'success': True}
        module = {'module': 'example', 'time-micros': 150000, 'rlimit': 80,
                  'function-breakdown': [row]}
        self.data = {'times-ms': {'total': 200, 'num-threads': 2, 'rust': {'total': 20},
            'verification': {'total': 170, 'vir': {'total': 15}},
            'smt': {'smt-run': 150, 'rlimit-run': 80, 'smt-run-module-times': [module]}},
            'verification-results': {'success': True, 'verified': 1, 'errors': 0,
                                     'is-verifying-entire-crate': True}}
        self.save()
        stub = self.root / 'verify.sh'
        stub.write_text('#!/usr/bin/env python3\nimport os, pathlib, sys\n'
                        'print("verification run #123", file=sys.stderr)\n'
                        'print("diagnostic retained", file=sys.stderr)\n'
                        'print(pathlib.Path(__file__).with_name("fixture.json").read_text())\n'
                        'sys.exit(int(os.environ.get("TEST_VERIFY_EXIT", "0")))\n')
        stub.chmod(0o755)

    def save(self):
        (self.root / 'fixture.json').write_text(json.dumps(self.data))

    def run_report(self, script='smt_times.sh', status=0):
        return subprocess.run([str(self.root / script), '-n', '2'], text=True,
                              capture_output=True, env={**os.environ, 'TEST_VERIFY_EXIT': str(status)})

    def test_success_and_module_report(self):
        for script in ['smt_times.sh', 'module_times.sh']:
            result = self.run_report(script)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('SMT run 150 ms', result.stdout)
            self.assertIn('Rust 20 ms; VIR 15 ms', result.stdout)
            self.assertIn('verification run #123', result.stderr)

    def test_verifier_exit_takes_precedence(self):
        result = self.run_report(status=7)
        self.assertEqual(result.returncode, 7)
        self.assertIn('diagnostic retained', result.stderr)
        self.assertTrue(next((self.root / '.verus-log').glob('timings.*/stderr.log')).exists())

    def test_missing_malformed_and_empty_measurements_fail(self):
        for payload in ['', '{}', '{broken']:
            (self.root / 'fixture.json').write_text(payload)
            result = self.run_report()
            self.assertEqual(result.returncode, 2)
            self.assertNotIn('TOTAL', result.stdout)
        self.data['times-ms']['smt']['smt-run-module-times'] = []
        self.save()
        self.assertEqual(self.run_report().returncode, 2)

    def test_verification_failure_in_json_fails(self):
        self.data['verification-results'].update(success=False, errors=1)
        self.save()
        self.assertEqual(self.run_report().returncode, 1)

    def test_concurrent_captures_are_independent(self):
        runs = [subprocess.Popen([str(self.root / 'smt_times.sh')], stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True) for _ in range(2)]
        for run in runs:
            _, stderr = run.communicate(timeout=15)
            self.assertEqual(run.returncode, 0, stderr)
        captures = list((self.root / '.verus-log').glob('timings.*'))
        self.assertEqual(len(captures), 2)
        for capture in captures:
            self.assertEqual(json.loads((capture / 'verus.json').read_text()), self.data)

    def test_pipeline_forwards_arguments_status_and_records_runs(self):
        shutil.copy2(ROOT / 'verify-pipeline.sh', self.root / 'verify-pipeline.sh')
        backend = self.root / 'verus/source/target-verus/release/cargo-verus'
        backend.parent.mkdir(parents=True)
        backend.write_text('#!/usr/bin/env python3\nimport json, os, sys\n'
                           'print(json.dumps(sys.argv[1:]))\n'
                           'sys.exit(int(os.environ.get("TEST_VERIFY_EXIT", "0")))\n')
        backend.chmod(0o755)
        for status in [0, 7]:
            result = subprocess.run([str(self.root / 'verify-pipeline.sh'), '--', '--output-json'],
                                    text=True, capture_output=True,
                                    env={**os.environ, 'TEST_VERIFY_EXIT': str(status)})
            self.assertEqual(result.returncode, status, result.stderr)
            self.assertEqual(json.loads(result.stdout), ['verify', '--workspace', '--exclude',
                'VeriFlat', '--', '--num-threads', '32', '--time', '--output-json'])
        self.assertEqual((self.root / '.verus-log/verify-count').read_text(), '2\n')
        self.assertEqual(len((self.root / '.verus-log/verify-runs.log').read_text().splitlines()), 2)


if __name__ == '__main__':
    unittest.main()
