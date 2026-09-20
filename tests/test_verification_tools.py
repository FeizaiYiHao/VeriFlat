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
        self.captures = self.root / 'captures'
        self.captures.mkdir()
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
                              capture_output=True, env={**os.environ, 'TEST_VERIFY_EXIT': str(status),
                                                        'TMPDIR': str(self.captures)})

    def test_success_and_module_report(self):
        for script in ['smt_times.sh', 'module_times.sh']:
            result = self.run_report(script)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('SMT run 150 ms', result.stdout)
            self.assertIn('Rust 20 ms; VIR 15 ms', result.stdout)
            self.assertIn('verification run #123', result.stderr)
            self.assertEqual(list(self.captures.iterdir()), [])

    def test_verifier_exit_takes_precedence(self):
        result = self.run_report(status=7)
        self.assertEqual(result.returncode, 7)
        self.assertIn('diagnostic retained', result.stderr)
        self.assertEqual(list(self.captures.iterdir()), [])

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
                                 stderr=subprocess.PIPE, text=True,
                                 env={**os.environ, 'TMPDIR': str(self.captures)}) for _ in range(2)]
        for run in runs:
            stdout, stderr = run.communicate(timeout=15)
            self.assertEqual(run.returncode, 0, stderr)
            self.assertIn('SMT run 150 ms', stdout)
        self.assertEqual(list(self.captures.iterdir()), [])

    def test_pipeline_forwards_arguments_status_and_counts_runs_without_logs(self):
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
        result = subprocess.run([str(self.root / 'verify-pipeline.sh')],
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), ['verify', '--workspace', '--exclude',
            'VeriFlat', '--', '--num-threads', '32', '--time'])
        result = subprocess.run([str(self.root / 'verify-pipeline.sh'), '--',
                                 '--time', '--output-json', '--time'],
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), ['verify', '--workspace', '--exclude',
            'VeriFlat', '--', '--num-threads', '32', '--time', '--output-json'])
        result = subprocess.run([str(self.root / 'verify-pipeline.sh'), '--',
                                 '--num-threads', '4'],
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 2)
        self.assertEqual((self.root / '.verus-log/verify-count').read_text(), '4\n')
        self.assertFalse((self.root / '.verus-log/verify-runs.log').exists())

    def test_workspace_empty_args_dedupes_time_and_rejects_thread_override(self):
        shutil.copy2(ROOT / 'verify-workspace.sh', self.root / 'verify-workspace.sh')
        backend = self.root / 'verus/source/target-verus/release/cargo-verus'
        backend.parent.mkdir(parents=True)
        backend.write_text('#!/usr/bin/env python3\nimport json, sys\n'
                           'print(json.dumps(sys.argv[1:]))\n')
        backend.chmod(0o755)
        fake_home = self.root / 'home'
        cargo = fake_home / '.cargo/bin/cargo'
        cargo.parent.mkdir(parents=True)
        package_id = 'path+file:///tmp/veriflat_kernel_core#0.1.0'
        metadata = {'workspace_members': [package_id], 'packages': [{
            'id': package_id, 'name': 'veriflat_kernel_core', 'dependencies': [],
        }]}
        cargo.write_text('#!/usr/bin/env python3\nimport json, sys\n'
                         f'metadata = {metadata!r}\n'
                         'if sys.argv[1] == "metadata":\n'
                         '    print(json.dumps(metadata))\n'
                         'elif sys.argv[1] != "clean":\n'
                         '    raise SystemExit(2)\n')
        cargo.chmod(0o755)
        env = {**os.environ, 'HOME': str(fake_home)}

        result = subprocess.run([str(self.root / 'verify-workspace.sh')],
                                text=True, capture_output=True, env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), ['focus', '--workspace', '--exclude',
            'VeriFlat', '-j', '8', '--', '--num-threads', '32', '--time'])

        result = subprocess.run([str(self.root / 'verify-workspace.sh'), '--package',
                                 'veriflat_kernel_core', '--',
                                 '--time', '--output-json', '--time'],
                                text=True, capture_output=True, env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), ['focus', '-p', 'veriflat_kernel_core',
            '-j', '1', '--', '--num-threads', '32', '--time', '--output-json'])

        result = subprocess.run([str(self.root / 'verify-workspace.sh'), '--',
                                 '--num-threads=4'],
                                text=True, capture_output=True, env=env)
        self.assertEqual(result.returncode, 2)
        self.assertEqual((self.root / '.verus-log/verify-count').read_text(), '2\n')

    def test_workspace_cache_roles_hot_runs_and_failed_state(self):
        shutil.copy2(ROOT / 'verify-workspace.sh', self.root / 'verify-workspace.sh')
        backend_log = self.root / 'backend.jsonl'
        backend = self.root / 'verus/source/target-verus/release/cargo-verus'
        backend.parent.mkdir(parents=True)
        backend.write_text(
            '#!/usr/bin/env python3\n'
            'import json, os, pathlib, sys\n'
            'with pathlib.Path(os.environ["TEST_BACKEND_LOG"]).open("a") as log:\n'
            '    print(json.dumps(sys.argv[1:]), file=log)\n'
            'sys.exit(int(os.environ.get("TEST_VERIFY_EXIT", "0")))\n'
        )
        backend.chmod(0o755)

        fake_home = self.root / 'home'
        cargo_log = self.root / 'cargo-clean.jsonl'
        cargo = fake_home / '.cargo/bin/cargo'
        cargo.parent.mkdir(parents=True)
        core_id = 'path+file:///tmp/veriflat_kernel_core#0.1.0'
        map_id = 'path+file:///tmp/veriflat_map_4k#0.1.0'
        metadata = {
            'workspace_members': [core_id, map_id],
            'packages': [
                {'id': core_id, 'name': 'veriflat_kernel_core', 'dependencies': []},
                {'id': map_id, 'name': 'veriflat_map_4k',
                 'dependencies': [{'name': 'veriflat_kernel_core'}]},
            ],
        }
        cargo.write_text(
            '#!/usr/bin/env python3\n'
            'import json, os, pathlib, sys\n'
            f'metadata = {metadata!r}\n'
            'if sys.argv[1] == "metadata":\n'
            '    print(json.dumps(metadata))\n'
            'elif sys.argv[1] == "clean":\n'
            '    with pathlib.Path(os.environ["TEST_CARGO_LOG"]).open("a") as log:\n'
            '        print(json.dumps(sys.argv[1:]), file=log)\n'
            'else:\n'
            '    raise SystemExit(2)\n'
        )
        cargo.chmod(0o755)
        env = {
            **os.environ,
            'HOME': str(fake_home),
            'TEST_BACKEND_LOG': str(backend_log),
            'TEST_CARGO_LOG': str(cargo_log),
        }
        script = self.root / 'verify-workspace.sh'

        def run(package, status=0):
            return subprocess.run(
                [str(script), '--package', package],
                text=True,
                capture_output=True,
                env={**env, 'TEST_VERIFY_EXIT': str(status)},
            )

        def clean_calls():
            if not cargo_log.exists():
                return []
            return [json.loads(line) for line in cargo_log.read_text().splitlines()]

        state_dir = self.root / 'target/verus-partial/.veriflat-focus-state'
        result = run('veriflat_map_4k')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(clean_calls()), 1)
        self.assertIn('-p', clean_calls()[0])
        self.assertEqual(
            (state_dir / 'veriflat_kernel_core').read_text(), 'dependency\n')
        self.assertTrue(
            (state_dir / 'veriflat_map_4k').read_text().startswith('root:'))

        result = run('veriflat_map_4k')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(clean_calls()), 1, 'hot run unexpectedly cleaned artifacts')

        result = run('veriflat_kernel_core')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(clean_calls()), 2)
        self.assertEqual(clean_calls()[-1][0:3],
                         ['clean', '-p', 'veriflat_kernel_core'])
        states_before_failure = {
            path.name: path.read_text()
            for path in state_dir.iterdir()
            if path.is_file()
        }

        result = run('veriflat_map_4k', status=7)
        self.assertEqual(result.returncode, 7, result.stderr)
        self.assertEqual(
            {
                path.name: path.read_text()
                for path in state_dir.iterdir()
                if path.is_file()
            },
            states_before_failure,
            'failed verification updated cache state',
        )
        failed_clean_count = len(clean_calls())

        result = run('veriflat_map_4k')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(clean_calls()), failed_clean_count + 1)
        self.assertEqual(
            (state_dir / 'veriflat_kernel_core').read_text(), 'dependency\n')
        self.assertEqual(len(backend_log.read_text().splitlines()), 5)

    def test_verification_times_reports_wall_and_preserves_status(self):
        script = self.root / 'verification_times.sh'
        for status in [0, 7]:
            result = subprocess.run(
                [str(script), 'functions', '-n', '2'],
                text=True,
                capture_output=True,
                env={
                    **os.environ,
                    'TEST_VERIFY_EXIT': str(status),
                    'TMPDIR': str(self.captures),
                },
            )
            self.assertEqual(result.returncode, status, result.stderr)
            self.assertIn('External wall (seconds):', result.stderr)
            self.assertIn('Scope: monolith all modules;', result.stderr)
            self.assertIn('diagnostic retained', result.stderr)
            self.assertEqual(list(self.captures.iterdir()), [])

    def test_verification_times_requires_a_valid_mode(self):
        script = self.root / 'verification_times.sh'
        env = {**os.environ, 'TMPDIR': str(self.captures)}

        for args in [[], ['unknown']]:
            result = subprocess.run(
                [str(script), *args],
                text=True,
                capture_output=True,
                env=env,
            )
            self.assertEqual(result.returncode, 2)
            self.assertIn('Usage:', result.stderr)
            self.assertNotIn('verification run #123', result.stderr)

        result = subprocess.run(
            [str(script), '--help'],
            text=True,
            capture_output=True,
            env=env,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('Usage:', result.stdout)
        self.assertNotIn('verification run #123', result.stderr)
        self.assertEqual(list(self.captures.iterdir()), [])

    def test_quant_profile_empty_args_cleanup_and_status(self):
        shutil.copy2(ROOT / 'quant_profile.sh', self.root / 'quant_profile.sh')
        verify_log = self.root / 'quant-verify.jsonl'
        verify = self.root / 'verify.sh'
        verify.write_text(
            '#!/usr/bin/env python3\n'
            'import json, os, pathlib, sys\n'
            'with pathlib.Path(os.environ["TEST_VERIFY_LOG"]).open("a") as log:\n'
            '    print(json.dumps(sys.argv[1:]), file=log)\n'
            'print("[quantifier_instances] example.q : 3 : 0 : 0 : 4 : 0")\n'
            'sys.exit(int(os.environ.get("TEST_VERIFY_EXIT", "0")))\n'
        )
        verify.chmod(0o755)
        env = {**os.environ, 'TEST_VERIFY_LOG': str(verify_log)}

        result = subprocess.run(
            [str(self.root / 'quant_profile.sh')],
            text=True,
            capture_output=True,
            env=env,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('example.q', result.stdout)
        self.assertEqual(
            json.loads(verify_log.read_text().splitlines()[0]),
            ['--smt-option', 'smt.qi.profile=true'],
        )
        self.assertEqual(
            list((self.root / '.verus-log').glob('quant-profile.*')), [])

        result = subprocess.run(
            [str(self.root / 'quant_profile.sh'), '--',
             '--verify-only-module', 'example'],
            text=True,
            capture_output=True,
            env={**env, 'TEST_VERIFY_EXIT': '7'},
        )
        self.assertEqual(result.returncode, 7)
        self.assertIn('verification exited with status 7', result.stderr)
        self.assertEqual(
            json.loads(verify_log.read_text().splitlines()[1]),
            ['--smt-option', 'smt.qi.profile=true',
             '--verify-only-module', 'example'],
        )
        self.assertEqual(
            list((self.root / '.verus-log').glob('quant-profile.*')), [])


if __name__ == '__main__':
    unittest.main()
