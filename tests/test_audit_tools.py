"""Regression cases for the verification tools; no Lean proof is mocked."""
from contextlib import redirect_stdout
import io
from pathlib import Path
import sys
import tempfile
import unittest
import subprocess

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import check_axioms
import check_proof_holes
from lean_sources import imports
from check_sources import require


class AxiomLogs(unittest.TestCase):
    def run_check(self, text, expect=None):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "audit.log"
            path.write_text(text)
            args = [str(path)] + ([] if expect is None else ["--expect", str(expect)])
            with redirect_stdout(io.StringIO()):
                return check_axioms.main(args)

    def test_empty_log_fails(self):
        self.assertEqual(self.run_check(""), 1)

    def test_standard_and_empty_closures_count(self):
        self.assertEqual(self.run_check(
            "'A' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            "'B' does not depend on any axioms\n", 2), 0)

    def test_custom_axiom_and_proof_hole_fail(self):
        for axiom in ("sorryAx", "Project.assumption"):
            with self.subTest(axiom=axiom):
                self.assertEqual(self.run_check(f"'A' depends on axioms: [{axiom}]\n"), 1)

    def test_missing_report_fails(self):
        self.assertEqual(self.run_check("'A' does not depend on any axioms\n", 2), 1)


class ProofHoleScan(unittest.TestCase):
    def check(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Example.lean"
            path.write_text(text)
            stream = io.StringIO()
            with redirect_stdout(stream):
                count = check_proof_holes.check(path)
            return count, stream.getvalue()

    def test_nested_comments_and_line_numbers(self):
        count, log = self.check("/- outer\n /- sorry -/\n-/\n-- admit\nexample : False := by sorry\n")
        self.assertEqual(count, 1)
        self.assertIn(":5:sorry:", log)

    def test_axiom_modifiers_and_compiler_trust_fail(self):
        for code in ("@[simp] axiom A : False", "private axiom A : False",
                     "example : True := by native_decide", "#check Lean.ofReduceBool"):
            with self.subTest(code=code):
                self.assertGreater(self.check(code)[0], 0)

    def test_literals_do_not_hide_following_code(self):
        for literal in ('"/-"', '"--"', 'r#"/-"#', 's!"{let x := "/-"; x}"'):
            with self.subTest(literal=literal):
                self.assertEqual(self.check(f'def marker := {literal}\nexample : False := by sorry\n')[0], 1)

    def test_interpolation_code_is_scanned(self):
        self.assertGreater(self.check('def marker := s!"{(by sorry : Nat)}"\n')[0], 0)


class SourceGuards(unittest.TestCase):
    def test_all_imports_are_recorded(self):
        self.assertEqual(imports('  import Swarm.A Mathlib.B -- comment\n'), ['Swarm.A', 'Mathlib.B'])
        with self.assertRaises(ValueError):
            imports('public import Swarm.A\n')

    def test_optimized_python_keeps_guards(self):
        with self.assertRaises(ValueError):
            require(False, 'failure')
        proc = subprocess.run([sys.executable, '-O', '-c',
            'from check_sources import require; require(False, "failure")'],
            env={**__import__('os').environ, 'PYTHONPATH': str(Path(__file__).resolve().parents[1] / 'scripts')},
            capture_output=True)
        self.assertNotEqual(proc.returncode, 0)


if __name__ == "__main__":
    unittest.main()
