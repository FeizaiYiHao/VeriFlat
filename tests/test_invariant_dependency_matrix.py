import json
from pathlib import Path
import subprocess
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "invariant_dependency_matrix.py"


class InvariantDependencyMatrixTest(unittest.TestCase):
    def test_live_matrix_is_complete(self):
        result = subprocess.run(
            ["python3", str(SCRIPT), "--check"],
            cwd=ROOT,
            text=True,
            capture_output=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("68 invariant leaves", result.stdout)

    def test_json_rows_use_kernel_fields(self):
        result = subprocess.run(
            ["python3", str(SCRIPT), "--json"],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=True,
        )
        report = json.loads(result.stdout)
        self.assertEqual(len(report["rows"]), 68)
        self.assertEqual(report["errors"], [])
        self.assertEqual(report["helper-count"], 89)
        self.assertEqual(report["classified-helper-count"], 89)
        self.assertEqual(report["unclassified-helpers"], [])
        self.assertTrue(all(row["fields"] for row in report["rows"]))


if __name__ == "__main__":
    unittest.main()
