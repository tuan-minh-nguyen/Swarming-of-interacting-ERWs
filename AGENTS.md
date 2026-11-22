# Working on the formalisation

- Preserve the manuscript's model, parameter range, quantifier order, and
  dependence of constants. The main lower bound is chosen before the population
  size. Do not replace intermediate proof obligations with main-theorem premises.
- Do not add proof holes, custom axioms, or compiler-trust shortcuts to proofs.
  A release must have a complete proof and pass the full checks.
- Keep the toolchain and dependency revisions pinned. Never remove dependency
  artifacts or run `lake clean` to invalidate project files.
- Import specific Mathlib modules; keep the umbrella `import Mathlib` out of
  project sources. Verify every import change by compilation.
- Keep proof diagnostics in `audit/`. Check every project declaration's transitive
  axiom dependencies, not only a selection of theorem names.
- Run `python3 scripts/check_sources.py` and the tool regression tests for edits.
  A complete release check is `bash scripts/verify.sh`; it builds only project
  modules in a new directory before checking the exported statements and axioms.
- Use fresh build directories for release measurements. Development resumes must
  validate source and artifact hashes and invalidate changed dependency closures.
- Measure elaboration changes with serial, interleaved comparisons. Do not raise
  resource limits and describe that as a speed improvement.
- The source inventory records the supplied proof text. An intentional proof
  revision requires an explicit record of the change, a check of the unchanged
  mathematical statement, and updated verification evidence.
