/-
# The exact residual of the halving clause: one small-spread time

`JoinSub.halving_of_coalesce` proves: a single integer time `s ∈ [τ_r, τ_{r+BL}]` with
whole-pack spread `≤ ε₀ L`, a lag bound `≤ ε₁ L` on `[s, τ_r+TL]`, `C_T L^{3/4} ≤ ε₂ L`,
`τ_{r+BL} ≤ τ_r+TL` and two explicit numerical thresholds imply the paper's second block
inequality `2 d_{r+BL} ≤ L`.  This file packages that into the measure-level shape the
tightness engine consumes, and names the residual.

* `HalfCoeff`, `HalfEps`, `HalfLmin` — the explicit constants: with `N = |ι|`,
  `ε = 1/(16 (1+2C)^N (1+N(4C+4)))` and `L ≥ 4 (1+2C)^N N(1+4C)`, the two thresholds of
  `betaOf_le_half` hold with `ε₀ = ε₁ = ε₂ = ε` (`halfEps_threshold`, `halfLmin_threshold`).
  So "for all sufficiently large `L`" is an explicit finite threshold in `N` and `C` only.
* `GoodHalf` — the good event at scale `(B,T,r,L)`: the carrier `{d_r ≤ L}`, a local-good
  field `LocalField` at *some* compatible constants, and **one coalescence time** `s` with
  `spread(s) ≤ εL`, lag `≤ εL` on `[s, τ_r+TL]`, and `C_T L^{3/4} ≤ εL`.
* `not_badHalf_of_goodHalf` — `GoodHalf` and the first block inequality `¬ BadTime` imply
  `¬ BadHalf` (deterministic, over an arbitrary nearest-neighbour family with record times).
* `measure_badHalf_le` — measure level:
  `μ {BadHalf} ≤ μ {BadTime} + μ {¬ GoodHalf}`.  So the halving clause is paid for by the
  **advance clause** (already needed) plus the complement of the good event; no other input.
* `halfClauseAt_of_goodHalf` — the array-level corollary: a profile bound on
  `BadTime ∪ (GoodHalf)ᶜ` for the literal `actX`/`recTimeA`/`arrayMeasure N` at the source
  constants gives a literal `SourceTightAvail.HalfClauseAt`.

The residual quantified here is exactly `(GoodHalf)ᶜ`: the source's `𝒢_{r,L,T}` supplies the
local-good field but **not** the coalescence time (that is obtained in the source only after
Arzelà–Ascoli).  Nothing in this file assumes stationarity, invariance, a start law or a
`dT` bound, and no `η = 0` is used.
-/
import Swarm.JoinSub

open Finset MeasureTheory
open scoped BigOperators ENNReal

namespace JoinStep

open RecordDefect LocalFluid Glue

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The explicit constants -/

/-- `(1+2C)^N (1 + N(4C+4))`, the factor of the entry-spread threshold. -/
noncomputable def HalfCoeff (C : ℝ) (N : ℕ) : ℝ := (1 + 2 * C) ^ N * (1 + (N : ℝ) * (4 * C + 4))

/-- The uniform `ε` of the halving threshold: `1/(16 (1+2C)^N (1+N(4C+4)))`. -/
noncomputable def HalfEps (C : ℝ) (N : ℕ) : ℝ := 1 / (16 * HalfCoeff C N)

/-- The explicit "sufficiently large `L`" threshold `4 (1+2C)^N N (1+4C)`. -/
noncomputable def HalfLmin (C : ℝ) (N : ℕ) : ℝ := 4 * ((1 + 2 * C) ^ N * ((N : ℝ) * (1 + 4 * C)))

theorem HalfCoeff_pos {C : ℝ} (hC : 0 < C) (N : ℕ) : 0 < HalfCoeff C N := by
  unfold HalfCoeff
  have h1 : (0 : ℝ) < 1 + 2 * C := by linarith
  have h2 : (0 : ℝ) < 1 + (N : ℝ) * (4 * C + 4) := by
    have : (0 : ℝ) ≤ (N : ℝ) * (4 * C + 4) := by positivity
    linarith
  exact mul_pos (pow_pos h1 N) h2

theorem HalfEps_pos {C : ℝ} (hC : 0 < C) (N : ℕ) : 0 < HalfEps C N := by
  unfold HalfEps
  have := HalfCoeff_pos hC N
  positivity

theorem HalfEps_nonneg {C : ℝ} (hC : 0 < C) (N : ℕ) : 0 ≤ HalfEps C N :=
  le_of_lt (HalfEps_pos hC N)

/-- The threshold `(1+2C)^N (1+N(4C+4)) (ε+ε+ε) ≤ 1/4` at `ε = HalfEps C N`. -/
theorem halfEps_threshold {C : ℝ} (hC : 0 < C) (N : ℕ) :
    (1 + 2 * C) ^ N * ((1 + (N : ℝ) * (4 * C + 4)) * (HalfEps C N + HalfEps C N + HalfEps C N))
      ≤ 1 / 4 := by
  have hpos := HalfCoeff_pos hC N
  have hε := HalfEps_pos hC N
  have heq : HalfCoeff C N * (HalfEps C N + HalfEps C N + HalfEps C N) = 3 / 16 := by
    unfold HalfEps
    field_simp
    ring
  have hre : (1 + 2 * C) ^ N * ((1 + (N : ℝ) * (4 * C + 4)) * (HalfEps C N + HalfEps C N + HalfEps C N))
      = HalfCoeff C N * (HalfEps C N + HalfEps C N + HalfEps C N) := by
    unfold HalfCoeff
    ring
  rw [hre, heq]
  norm_num

/-- The threshold `(1+2C)^N N (1+4C) ≤ L/4` from `HalfLmin C N ≤ L`. -/
theorem halfLmin_threshold {C : ℝ} {N : ℕ} {L : ℝ} (hC : 0 < C) (h : HalfLmin C N ≤ L) :
    (1 + 2 * C) ^ N * ((N : ℝ) * (1 + 4 * C)) ≤ L / 4 := by
  unfold HalfLmin at h
  have h1 : (0 : ℝ) < 1 + 2 * C := by linarith
  have h2 : (0 : ℝ) ≤ (1 + 2 * C) ^ N * ((N : ℝ) * (1 + 4 * C)) := by
    have : (0 : ℝ) ≤ (N : ℝ) * (1 + 4 * C) := by
      have : (0 : ℝ) ≤ (N : ℝ) := by positivity
      have : (0 : ℝ) ≤ 1 + 4 * C := by linarith
      positivity
    positivity
  linarith

/-! ## 2. The good event -/

/-- **The good event of the halving clause** at scale `(B,T,r,L)` on a nearest-neighbour
family with record times.  It contains

* the paper's carrier `{d_r ≤ L}`;
* *some* local-good field `LocalField X τ H C CT T L r η` at compatible constants
  (`0 < C`, `0 ≤ C_T`) with the explicit size condition `HalfLmin C |ι| ≤ L`;
* **one coalescence time** `s ∈ [τ_r, τ_{r+BL}]` with `spread(s) ≤ εL`, lag `≤ εL` on
  `[s, τ_r+TL]`, and `C_T L^{3/4} ≤ εL`, where `ε = HalfEps C |ι|`.

The failure of the *first* block inequality is **not** part of it: that is charged separately
as `HblkTwo.BadTime`. -/
def GoodHalf (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (B T L r : ℕ) : Prop :=
  defect X τ r ≤ (L : ℤ) ∧
    ∃ (H : Finset ι → ℕ → ℤ → ℤ) (C CT : ℝ) (η : ℕ),
      0 < C ∧ 0 ≤ CT ∧ HalfLmin C (Finset.univ : Finset ι).card ≤ (L : ℝ) ∧
        LocalField X τ H C CT T L r η ∧
        ∃ s : ℕ, τ r ≤ s ∧ s ≤ τ (r + B * L) ∧
          (spreadS X (Finset.univ : Finset ι) s : ℝ)
            ≤ HalfEps C (Finset.univ : Finset ι).card * (L : ℝ) ∧
          (∀ (i : ι) (m : ℕ), s ≤ m → m ≤ τ r + T * L → runMaxI X i m - X i m ≤ (η : ℤ)) ∧
          ((η : ℝ) ≤ HalfEps C (Finset.univ : Finset ι).card * (L : ℝ)) ∧
          (CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ HalfEps C (Finset.univ : Finset ι).card * (L : ℝ))

/-- **The deterministic core.**  `GoodHalf` plus the first block inequality implies the second:
`¬ BadHalf`.  This is `halving_of_coalesce` with the constants packaged by
`halfEps_threshold` and `halfLmin_threshold`. -/
theorem not_badHalf_of_goodHalf {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {B T L r : ℕ}
    (hτ : IsRecord X τ) (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (hr : (T + 3) * L ≤ r) (hgood : GoodHalf (ι := ι) X τ B T L r)
    (hadv : ¬ HblkTwo.BadTime B T (fun u => (defect X τ u).toNat, τ) r L) :
    ¬ HblkTwo.BadHalf B (fun u => (defect X τ u).toNat, τ) r L := by
  obtain ⟨hdr, H, C, CT, η, hC, hCT, hLmin, hLF, s, hs₀, hsB, hspread, hlag, hη, hL3⟩ := hgood
  have hdef : 2 * defect X τ (r + B * L) ≤ (L : ℤ) :=
    halving_of_coalesce hτ hne hLF hC hCT (HalfEps_nonneg hC _) hdr hr hs₀ hspread hlag hη hL3
      (HalfEps_nonneg hC _) (HalfEps_nonneg hC _)
      (halfEps_threshold hC _) (halfLmin_threshold hC hLmin) ?_ hsB
  · exact Glue.not_badHalf_of_defect_le hτ hdef
  · -- the first block inequality, from `¬ BadTime` and the carrier
    by_contra hcon
    push_neg at hcon
    exact hadv ⟨Int.toNat_le.mpr hdr, hcon⟩

/-! ## 3. The measure decomposition -/

/-- **Measure level.**  The halving bad event is contained in the advance bad event
(`BadTime`) together with the complement of `GoodHalf`, hence its mass is at most the sum of
the two.  No measurability, stationarity, independence or start-law assumption enters. -/
theorem measure_badHalf_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ι → ℕ → ℤ) (τ : Ω → ℕ → ℕ)
    (hne : ∀ (ω : Ω) (i : ι) (n : ℕ), |X ω i (n + 1) - X ω i n| = 1)
    (hτ : ∀ ω : Ω, IsRecord (X ω) (τ ω)) {B T L r : ℕ} (hr : (T + 3) * L ≤ r) :
    μ {ω | HblkTwo.BadHalf B (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} ≤
      μ {ω | HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L} +
        μ {ω | ¬ GoodHalf (ι := ι) (X ω) (τ ω) B T L r} := by
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  by_cases hb : HblkTwo.BadTime B T (fun u => (defect (X ω) (τ ω) u).toNat, τ ω) r L
  · exact Or.inl hb
  · refine Or.inr ?_
    intro hg
    exact not_badHalf_of_goodHalf (hτ ω) (hne ω) hr hg hb hω

end JoinStep

/-! ## Axiom audit (source order) -/


