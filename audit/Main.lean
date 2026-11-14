/-
Axiom dependencies of the main proof and exact consumer checks for Theorem 1.1.
The positive lower bound is chosen before the population size. Both proof routes
refer to the actual trajectory under the product uniform measure.
-/
import Swarm.BlkMeasure
import Lean

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

#print axioms M4Blk.blkEps
#print axioms M4Blk.blkEps_tendsto
#print axioms M4Blk.blkEps_spec
#print axioms M4Blk.badBlk_ae_subset
#print axioms M4Blk.paperBadBlockProfile
#print axioms M4Blk.main_claim
#print axioms M4Blk.dT_tight
#print axioms M4Blk.main_claim_direct

/-! ## The manuscript statement -/

/-- The paper's Theorem 1.1, transcribed by hand from `main_1d_revised.tex`
(`\label{main}`): `κ(m,p) > 0` is chosen **before** `N`; for every `N ≥ 2` one deterministic
speed `v ∈ [κ, 2p-1]` works for **every** walker of the actual trajectory under the actual
array measure. -/
def M5PaperTarget (m : ℕ) (p : ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
    ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N,
      Tendsto (fun n : ℕ =>
          ((Swarming.Trajectory.trajectory p m U n).pos i : ℝ) / (n : ℝ)) atTop (𝓝 v)

/-- The capstone states exactly the paper's theorem. -/
theorem main_claim_is_paper_target :
    ∀ (p : ℝ) (m : ℕ), (1 : ℝ) / 2 < p → p < 1 → 2 ≤ m → M5PaperTarget m p :=
  @M4Blk.main_claim

/-- The second route states exactly the same theorem. -/
theorem main_claim_direct_is_paper_target :
    ∀ (p : ℝ) (m : ℕ), (1 : ℝ) / 2 < p → p < 1 → 2 ≤ m → M5PaperTarget m p :=
  @M4Blk.main_claim_direct

#print axioms main_claim_is_paper_target
#print axioms main_claim_direct_is_paper_target

open Lean Elab Command in
/-- Check that the exported constants have exactly the five explicit source binders. -/
elab "#check_main_binders" : command => do
  for name in #[`M4Blk.main_claim, `M4Blk.main_claim_direct] do
    let info ← getConstInfo name
    unless info.levelParams.isEmpty do
      throwError "Unexpected universe parameters in {name}"
    let mut type := info.type
    for expected in #[`p, `m, `hp0, `hp1, `hm] do
      match type with
      | .forallE binder _ body binderInfo =>
        unless binder == expected && binderInfo == .default do
          throwError "Unexpected binder in {name}: {binder}"
        type := body
      | _ => throwError "Missing source binder in {name}: {expected}"
    match type with
    | .forallE .. => throwError "Additional binder in {name}"
    | _ => pure ()
  logInfo "MAIN BINDERS OK: five explicit source binders in each export"

#check_main_binders
