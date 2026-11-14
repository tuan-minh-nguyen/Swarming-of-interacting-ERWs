/-
# M4 / direction D: the paper's block probability `(blkprob)` implies Theorem 1.1

This file is the measured-to-tightness *terminal adapter*.  It contains no stochastic estimate:
the only premise is the paper's own block estimate `(blkprob)`, stated at the paper's index
shapes, and the conclusion is the literal theorem for `Swarming.Trajectory.trajectory` under
`Swarming.Uniform.arrayMeasure N` with `κ(m,p)` chosen before `N`.

## The chain, with every step proved here

1. `exists_cubic_majorant` — the paper's `(blkprob)` holds "for all sufficiently large integers
   `L`".  `SourceTightAvail` consumes a *cubic* profile valid at every `ℓ ≥ 1`.  Below `L₀` the
   event has probability at most one, which the constant `max K₀ ((L₀+1)^3)` absorbs.
2. `badTime_subset_badBlk`, `badHalf_subset_badBlk` — the paper states **one** bad event
   `(d_r ≤ L, at least one inequality in (block) fails)` with **one** profile
   `C_T exp (-c_T L^(1/16))`.  The two formal clauses `BadTime` and `BadHalf` are each
   contained in that single event, so one paper bound gives both.
3. `advanceClauseAt_mono_T`, `M3Advance.advanceClauseAt_mono_C₀`, `M3Advance.halfClauseAt_mono_C₀`
   — raising the window parameter `T` shrinks the bad-time event, and raising `C₀` shrinks the
   range of admissible starting records.  This is the bookkeeping that lets a clause proved at
   the paper's `(BTchoice)` constants be consumed at the tightness engine's own `T` and `C₀`.
4. `cubicBlockClauses_of_paper` — the paper's `(blkprob)` yields the exact hypotheses of
   `SourceTightAvail.record_tightness_of_block_clauses_at`.
5. `main_claim_of_cubic_block_clauses` — those hypotheses yield genuine `d_T` tightness at the
   actual zero-state Dirac start, and `SwarmDTR.main_claim_of_dT_tight` converts it into the
   literal theorem.

## What is *not* claimed

The paper's `(blkprob)` is **not** proved here, nor is any substitute for it assumed silently:
`PaperBadBlockProfile` is exactly that estimate, with the paper's `C_T`, `c_T`, `L^{1/16}`
profile, its chosen `B`, `T`, `C₀` and its "sufficiently large `L`" restriction.  Everything
else in the chain is a theorem.  In particular this file does not prove the paper's theorem
unconditionally.
-/
import Swarm.SourceTightAvail
import Swarm.ConditionalVelocity
import Swarm.M3Advance

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace M4Term

/-! ## Profiles -/

/-- The cubic profile of `SourceTightAvail`, written with the same parenthesisation. -/
noncomputable def cubicProfile (K : ℝ) (ℓ : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (K * (((ℓ : ℝ) + 1))⁻¹ ^ 3)

theorem cubicProfile_mono {K K' : ℝ} (h : K ≤ K') (ℓ : ℕ) :
    cubicProfile K ℓ ≤ cubicProfile K' ℓ := by
  unfold cubicProfile
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h (by positivity))

variable {N : ℕ}

/-- Any set has array measure at most one. -/
theorem arrayMeasure_le_one (s : Set (Swarming.Uniform.Array N)) :
    (Swarming.Uniform.arrayMeasure N) s ≤ 1 := by
  calc (Swarming.Uniform.arrayMeasure N) s ≤ (Swarming.Uniform.arrayMeasure N) Set.univ :=
        measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

variable [Nonempty (Fin N)]

/-- **The paper's "for all sufficiently large `L`" restriction costs only a larger constant.**

If a family of events has probability at most `C exp (-c ℓ^(1/16))` for every `ℓ ≥ L₀`, `ℓ ≥ 1`,
then it is bounded by a cubic profile for *every* `ℓ ≥ 1`: below `L₀` the probability is at most
one, and `(ℓ+1)^{-3} ≥ (L₀+1)^{-3}` there, so `K = max K₀ (L₀+1)^3` suffices. -/
theorem exists_cubic_majorant
    {g : ℕ → ℕ → ℝ≥0∞} {C cc : ℝ} {C₀ L₀ : ℕ} (hC : 0 ≤ C) (hc : 0 < cc)
    (hg1 : ∀ (ℓ r : ℕ), g r ℓ ≤ 1)
    (h : ∀ (ℓ : ℕ), 1 ≤ ℓ → L₀ ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      g r ℓ ≤ TightAvail.paperProfile C cc ℓ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ℓ : ℕ), 1 ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      g r ℓ ≤ cubicProfile K ℓ := by
  obtain ⟨K₀, hK₀, hdec⟩ := TightAvail.paperProfile_le_cubic hC hc
  refine ⟨max K₀ (((L₀ : ℝ) + 1) ^ 3), le_trans hK₀ (le_max_left _ _), fun ℓ hℓ r _ => ?_⟩
  rcases Nat.lt_or_ge ℓ L₀ with hlt | hge
  · have hℓpos : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
    have hLpos : (0 : ℝ) < (L₀ : ℝ) + 1 := by positivity
    have hℓL : (ℓ : ℝ) + 1 ≤ (L₀ : ℝ) + 1 := by
      have : (ℓ : ℝ) < (L₀ : ℝ) := by exact_mod_cast hlt
      linarith
    have hinv : (((L₀ : ℝ) + 1))⁻¹ ≤ (((ℓ : ℝ) + 1))⁻¹ := inv_anti₀ hℓpos hℓL
    have hpow : (((L₀ : ℝ) + 1))⁻¹ ^ 3 ≤ (((ℓ : ℝ) + 1))⁻¹ ^ 3 :=
      pow_le_pow_left₀ (by positivity) hinv 3
    have hKle : ((L₀ : ℝ) + 1) ^ 3 ≤ max K₀ (((L₀ : ℝ) + 1) ^ 3) := le_max_right _ _
    have hca : (0 : ℝ) ≤ (((L₀ : ℝ) + 1))⁻¹ ^ 3 := by positivity
    have hcb : (0 : ℝ) ≤ max K₀ (((L₀ : ℝ) + 1) ^ 3) := by positivity
    have hone : (1 : ℝ) ≤ max K₀ (((L₀ : ℝ) + 1) ^ 3) * (((ℓ : ℝ) + 1))⁻¹ ^ 3 := by
      calc (1 : ℝ) = ((L₀ : ℝ) + 1) ^ 3 * (((L₀ : ℝ) + 1))⁻¹ ^ 3 := by
            rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hLpos), one_pow]
        _ ≤ max K₀ (((L₀ : ℝ) + 1) ^ 3) * (((ℓ : ℝ) + 1))⁻¹ ^ 3 :=
            mul_le_mul hKle hpow hca hcb
    calc g r ℓ ≤ 1 := hg1 ℓ r
      _ = ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (max K₀ (((L₀ : ℝ) + 1) ^ 3) * (((ℓ : ℝ) + 1))⁻¹ ^ 3) :=
            ENNReal.ofReal_le_ofReal hone
      _ = cubicProfile (max K₀ (((L₀ : ℝ) + 1) ^ 3)) ℓ := rfl
  · refine le_trans (h ℓ hℓ hge r ‹C₀ * ℓ ≤ r›)
      (le_trans (by simpa [cubicProfile] using hdec ℓ) (cubicProfile_mono (le_max_left _ _) ℓ))

/-! ## From the paper's single bad event to the two formal clauses -/

/-- The time-clause failure is contained in the paper's bad block event. -/
theorem badTime_subset_badBlk {B T C₀ r L : ℕ} {q : (ℕ → ℕ) × (ℕ → ℕ)} :
    HblkTwo.BadTime B T q r L → HblkTwo.BadBlk B C₀ T q r L := by
  rintro ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  intro hG
  exact absurd hG.1 (not_le_of_gt h2)

/-- The halving-clause failure is contained in the paper's bad block event (for every `T`). -/
theorem badHalf_subset_badBlk {B T C₀ r L : ℕ} {q : (ℕ → ℕ) × (ℕ → ℕ)} :
    HblkTwo.BadHalf B q r L → HblkTwo.BadBlk B C₀ T q r L := by
  rintro ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  intro hG
  exact absurd hG.2.1 (not_le_of_gt h2)

/-- **`BadTime` is antitone in the window parameter `T`.**  A larger allowance `T` makes the
time clause easier to satisfy, hence the failure event smaller.  Together with the `C₀`
monotonicity of `M3Advance` this lets a clause proved at the paper's `(BTchoice)` constants be
consumed at the tightness engine's own `T` and `C₀`. -/
theorem advanceClauseAt_mono_T {p : ℝ} {m B T T' C₀ : ℕ} (hT : T ≤ T')
    {p₁ : ℕ → ℝ≥0∞}
    (h : SourceTightAvail.AdvanceClauseAt (N := N) p m B T C₀ p₁) :
    SourceTightAvail.AdvanceClauseAt (N := N) p m B T' C₀ p₁ := by
  intro ℓ hℓ r hr
  refine le_trans (measure_mono ?_) (h ℓ hℓ r hr)
  intro U hU
  exact ⟨hU.1, lt_of_le_of_lt
    (Nat.add_le_add_left (Nat.mul_le_mul_right ℓ hT) ((HblkFinal.arrQ p m U).2 r)) hU.2⟩

/-! ## The two explicit interfaces -/

/-- **The exact hypotheses of `SourceTightAvail.record_tightness_of_block_clauses_at`**, bundled
per `N`.  The block size `B`, the window `T` and the record offset `C₀` are existential: this is
weaker (and more faithful to the source) than demanding the clauses for every `T`.  The proof
below raises `T` and `C₀` to the engine's own values by monotonicity. -/
def CubicBlockClauses (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N →
    ∃ (B T C₀ : ℕ), 1 ≤ B ∧
      ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
        SourceTightAvail.AdvanceClauseAt (N := N) p m B T C₀ (cubicProfile K₁) ∧
        SourceTightAvail.HalfClauseAt (N := N) p m B C₀ (cubicProfile K₂)

/-- **The paper's `(blkprob)`, verbatim in index shape.**

For every `N ≥ 2` there are a block size `B ≥ 1` and integers `T, C₀` (the source's
`(BTchoice)`: `T` above `4B/κ(m,p)`, `C₀ > B + T + 3`), constants `C_T`, `c_T > 0` and a
threshold `L₀` such that for all `ℓ ≥ max 1 L₀` and all record starting levels `r ≥ C₀ ℓ` the
paper's single bad block event has array probability at most `C_T exp (-c_T ℓ^(1/16))`.

Constants may depend on `N` and `T` (the local-good constant `C` and hence `B` come from the
`N`-dependent compactness proposition); `c_T > 0` is the paper's rate.  This is exactly the
source's `(blkprob)` with its "for all sufficiently large `L`" restriction. -/
def PaperBadBlockProfile (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N →
    ∃ (B T C₀ : ℕ), 1 ≤ B ∧
      ∃ (C_T c_T : ℝ) (L₀ : ℕ), 0 ≤ C_T ∧ 0 < c_T ∧
        ∀ (ℓ : ℕ), 1 ≤ ℓ → L₀ ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
          (Swarming.Uniform.arrayMeasure N)
            {U : Swarming.Uniform.Array N |
              HblkTwo.BadBlk B C₀ T (HblkFinal.arrQ p m U) r ℓ}
          ≤ TightAvail.paperProfile C_T c_T ℓ

/-- **The paper's `(blkprob)` gives the bundled cubic clauses.**  This is steps 1–2 of the chain:
split off the threshold `L₀`, absorb it into the cubic constant, and use that one bad block
event dominates each of the two formal clauses. -/
theorem cubicBlockClauses_of_paper {p : ℝ} {m : ℕ} (h : PaperBadBlockProfile p m) :
    CubicBlockClauses p m := by
  intro N inst hN
  letI : Nonempty (Fin N) := inst
  obtain ⟨B, T, C₀, hB, C_T, c_T, L₀, hC, hc, hb⟩ := h N hN
  have hTime : ∀ (ℓ : ℕ), 1 ≤ ℓ → L₀ ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N |
          HblkTwo.BadTime B T (HblkFinal.arrQ p m U) r ℓ}
      ≤ TightAvail.paperProfile C_T c_T ℓ := by
    intro ℓ hℓ hL r hr
    refine le_trans (measure_mono ?_) (hb ℓ hℓ hL r hr)
    intro U hU
    exact badTime_subset_badBlk hU
  have hHalf : ∀ (ℓ : ℕ), 1 ≤ ℓ → L₀ ≤ ℓ → ∀ r : ℕ, C₀ * ℓ ≤ r →
      (Swarming.Uniform.arrayMeasure N)
        {U : Swarming.Uniform.Array N |
          HblkTwo.BadHalf B (HblkFinal.arrQ p m U) r ℓ}
      ≤ TightAvail.paperProfile C_T c_T ℓ := by
    intro ℓ hℓ hL r hr
    refine le_trans (measure_mono ?_) (hb ℓ hℓ hL r hr)
    intro U hU
    exact badHalf_subset_badBlk hU
  obtain ⟨K₁, hK₁, h₁⟩ := exists_cubic_majorant
    (g := fun r ℓ => (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        HblkTwo.BadTime B T (HblkFinal.arrQ p m U) r ℓ})
    (C := C_T) (cc := c_T) (C₀ := C₀) (L₀ := L₀) hC hc
    (fun ℓ r => arrayMeasure_le_one _) hTime
  obtain ⟨K₂, hK₂, h₂⟩ := exists_cubic_majorant
    (g := fun r ℓ => (Swarming.Uniform.arrayMeasure N)
      {U : Swarming.Uniform.Array N |
        HblkTwo.BadHalf B (HblkFinal.arrQ p m U) r ℓ})
    (C := C_T) (cc := c_T) (C₀ := C₀) (L₀ := L₀) hC hc
    (fun ℓ r => arrayMeasure_le_one _) hHalf
  exact ⟨B, T, C₀, hB, K₁, K₂, hK₁, hK₂, h₁, h₂⟩

/-! ## Terminal composition -/

/-- **Theorem 1.1 for the literal array, from the bundled cubic block clauses.**

For every `1/2 < p < 1` and `m ≥ 2`, the cubic block clauses produce a single
`κ > 0` (chosen before `N`) such that for every `N ≥ 2` there is one deterministic speed
`v ∈ [κ, 2p-1]` with almost-sure convergence of every walker's normalised position.

The proof raises the clause's `T` and `C₀` to the tightness engine's own values — using the
monotonicity lemmas of step 3 — obtains `d_T` tightness at the actual zero-state Dirac start
from `SourceTightAvail.record_tightness_of_block_clauses_at`, and hands it to
`SwarmDTR.main_claim_of_dT_tight`; no other input is used. -/
theorem main_claim_of_cubic_block_clauses
    {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hcl : CubicBlockClauses p m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((Swarming.Trajectory.trajectory p m U n).pos i : ℝ) / (n : ℝ))
          atTop (𝓝 v) := by
  refine SwarmDTR.main_claim_of_dT_tight (p := p) hp0 hp1 hm ?_
  intro N inst hN ε hε
  letI : Nonempty (Fin N) := inst
  obtain ⟨B, T₀, C₀, hB, K₁, K₂, hK₁, hK₂, h₁, h₂⟩ := hcl N hN
  obtain ⟨κ, hκ, H⟩ :=
    SourceTightAvail.record_tightness_of_block_clauses_at (N := N) (m := m) hp0 hp1 hm hN B hB
  let T : ℕ := max T₀ (⌈2 * (B : ℝ) / κ⌉₊ + 2)
  let C : ℕ := max C₀ (B + T + 1)
  have hT : ⌈2 * (B : ℝ) / κ⌉₊ + 2 ≤ T := le_max_right _ _
  have hTB : T₀ ≤ T := le_max_left _ _
  have hC : B + T + 1 ≤ C := le_max_right _ _
  have hCC : C₀ ≤ C := le_max_left _ _
  have h₁' : SourceTightAvail.AdvanceClauseAt (N := N) p m B T C (cubicProfile K₁) :=
    M3Advance.advanceClauseAt_mono_C₀ hCC (advanceClauseAt_mono_T (N := N) hTB h₁)
  have h₂' : SourceTightAvail.HalfClauseAt (N := N) p m B C (cubicProfile K₂) :=
    M3Advance.halfClauseAt_mono_C₀ hCC h₂
  exact H T C hT hC _ _ K₁ K₂ hK₁ hK₂ (fun ℓ => le_rfl) (fun ℓ => le_rfl) h₁' h₂' ε hε


/-- **The hardwired-clause ledger of `TightAvail` is a special case.**  A caller that has proved
the paper's clauses at the engine's own constants `T = ⌈2B/κ⌉₊ + 2`, `C₀ = B + T + 1`
(`TightAvail.AdvanceClause`, `TightAvail.HalfClause`) for some positive `κ` gets the bundled
hypotheses, for free. -/
def HardwiredBlockClauses (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N →
    ∃ (B : ℕ) (κ : ℝ) (K₁ K₂ : ℝ), 1 ≤ B ∧ 0 < κ ∧ 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      TightAvail.AdvanceClause (N := N) p m B κ (cubicProfile K₁) ∧
      TightAvail.HalfClause (N := N) p m B κ (cubicProfile K₂)

theorem cubicBlockClauses_of_hardwired {p : ℝ} {m : ℕ} (h : HardwiredBlockClauses p m) :
    CubicBlockClauses p m := by
  intro N inst hN
  letI : Nonempty (Fin N) := inst
  obtain ⟨B, κ, K₁, K₂, hB, hκ, hK₁, hK₂, h₁, h₂⟩ := h N hN
  refine ⟨B, ⌈2 * (B : ℝ) / κ⌉₊ + 2, B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1, hB,
    K₁, K₂, hK₁, hK₂, ?_, ?_⟩
  · simpa [TightAvail.AdvanceClause, SourceTightAvail.AdvanceClauseAt] using h₁
  · simpa [TightAvail.HalfClause, SourceTightAvail.HalfClauseAt] using h₂

/-- **Theorem 1.1 for the literal array, from the paper's `(blkprob)` in its own profile.** -/
theorem main_claim_of_paper_badblock_profile
    {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (h : PaperBadBlockProfile p m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((Swarming.Trajectory.trajectory p m U n).pos i : ℝ) / (n : ℝ))
          atTop (𝓝 v) :=
  main_claim_of_cubic_block_clauses hp0 hp1 hm (cubicBlockClauses_of_paper h)


/-- A stronger, `∀ T C₀` form of the ledger.  It implies `CubicBlockClauses` by taking the
smallest admissible `T` and `C₀`; it is kept because a producer who has the clauses uniformly in
the window parameter may find this easier to establish. -/
def CubicBlockClausesAllT (p : ℝ) (m : ℕ) : Prop :=
  ∀ (N : ℕ) [Nonempty (Fin N)], 2 ≤ N →
    ∃ B : ℕ, 1 ≤ B ∧
      ∀ T C₀ : ℕ, B + T + 1 ≤ C₀ →
        ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
          SourceTightAvail.AdvanceClauseAt (N := N) p m B T C₀ (cubicProfile K₁) ∧
          SourceTightAvail.HalfClauseAt (N := N) p m B C₀ (cubicProfile K₂)

theorem cubicBlockClauses_of_allT {p : ℝ} {m : ℕ} (h : CubicBlockClausesAllT p m) :
    CubicBlockClauses p m := by
  intro N inst hN
  letI : Nonempty (Fin N) := inst
  obtain ⟨B, hB, hT⟩ := h N hN
  obtain ⟨K₁, K₂, hK₁, hK₂, h₁, h₂⟩ := hT 0 (B + 0 + 1) (le_refl _)
  exact ⟨B, 0, B + 0 + 1, hB, K₁, K₂, hK₁, hK₂, h₁, h₂⟩

theorem main_claim_of_cubic_block_clauses_allT
    {p : ℝ} (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (h : CubicBlockClausesAllT p m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 2 ≤ N → ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
      ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure N), ∀ i : Fin N,
        Tendsto (fun n : ℕ => ((Swarming.Trajectory.trajectory p m U n).pos i : ℝ) / (n : ℝ))
          atTop (𝓝 v) :=
  main_claim_of_cubic_block_clauses hp0 hp1 hm (cubicBlockClauses_of_allT h)

end M4Term
