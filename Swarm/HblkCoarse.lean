/-
# The halving clause of `(blkprob)` at scales comparable with the record level

`HblkTwo` shows that the paper's block estimate `(blkprob)` has exactly two stochastic clauses:
the record-advance clause
  `(time)`  `τ (r + B ℓ) - τ r ≤ T ℓ`
and the defect-halving clause
  `(half)`  `2 d (r + B ℓ) ≤ ℓ`  on `{d r ≤ ℓ}`.

The paper proves both through the one-sided fluid limit: a compactness/contradiction argument on the
rescaled paths, uniform in `r ≥ C₀ ℓ`, which is far beyond the reach of a formalisation in this
development.  The point of this file is that **(half) does not need the fluid limit when the block
scale `ℓ` is a nonvanishing fraction of the record level `r`**, which is precisely the diagonal
`ℓ = λ(r) ≈ r / (2 C₀)` that the paper's Borel–Cantelli step uses:

* `d_r = spread(τ_r)` exactly (`RecordDefect.defect_eq_spread`), the raw defect at a record time
  *is* the diameter of the configuration;
* `spread(n) / n → 0` is the paper's `(diam)`, now unconditional at the actual array
  (`M7Block.diam_actual_recordo`);
* `τ_y ≤ N₀ + (2/κ) y` is the record-time bound from the ballistic lower bound
  (`SwarmM4C.FixedConst.tau_le_threshold`).

Hence `d_{r+Bℓ} ≤ ε·τ_{r+Bℓ} ≤ ε (N₀ + (2/κ)(r + Bℓ))`, and the right-hand side is at most `ℓ/2`
as soon as `ℓ ≥ θ r` for a constant `θ` determined by `κ, B` alone.  So the `(diam)` estimate,
applied at the record time `τ_{r+Bℓ}`, already gives the halving at coarse scales; the fluid-limit
contraction is needed **only** for scales `ℓ = o(r)`.

Main declarations.

* `tau_ge` — `r ≤ τ r` for a unit-step family started at the origin.
* `coarse_halving` — the deterministic statement: for a nearest-neighbour family with first-hitting
  record times, `spread(n)/n → 0` and a ballistic lower bound, almost every level `r` satisfies
  `(half)` for all `ℓ ≥ θ r`.
* `coarse_halving_actual` — the unconditional almost-sure form at the canonical array.

No proof holes.  Nothing here proves `(time)`, `hblk`, tightness, invariant measures, regeneration
or the main theorem; the residual content of `(blkprob)` after this file is `(time)` at all scales
plus `(half)` at scales `ℓ = o(r)`.
-/
import Swarm.HblkTwo

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace HblkCoarse

open RecordDefect RecordoSupply SwarmM4C.FixedConst SwarmM4C.LawBridge
  SwarmRecordMeas SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw Swarming Swarming.Uniform
  SimJump.RecKernel

/-! ### The record time dominates the level -/

section Geometry

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}

/-- A unit-step walker started at the origin is never above the time. -/
theorem step_upper (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1)
    (h0 : ∀ i, X i 0 = 0) (i : ι) : ∀ n : ℕ, X i n ≤ (n : ℤ) := by
  intro n
  induction n with
  | zero => simp [h0 i]
  | succ n ih =>
      have h1 : X i (n + 1) ≤ X i n + 1 := by
        have := (abs_le.1 (le_of_eq (hne i n))).2
        linarith
      push_cast
      linarith

/-- **The record time dominates the level**: `r ≤ τ r`. -/
theorem tau_ge (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0) :
    ∀ r : ℕ, r ≤ τ r := by
  intro r
  by_contra hlt
  rw [not_le] at hlt
  have hmax : runMax X (τ r) = ((r : ℕ) : ℤ) := (hτ r).2
  obtain ⟨i, -, hval⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty (fun i => X i (τ r))
  have hupper := step_upper hne h0 i (τ r)
  have hlt' : ((τ r : ℕ) : ℤ) < ((r : ℕ) : ℤ) := by exact_mod_cast hlt
  have hEq : X i (τ r) = ((r : ℕ) : ℤ) := by
    have h1 : X i (τ r) = runMax X (τ r) := hval.symm
    rw [h1, hmax]
  linarith

end Geometry

/-! ### The coarse-scale halving -/

section Coarse

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {X : ι → ℕ → ℤ} {τ : ℕ → ℕ}

/-- **The halving clause holds at every scale comparable with the level.**

Let `X` be a nearest-neighbour family with first-hitting record times `τ`, sublinear spread
(`(diam)`: `spread(n)/n → 0`) and a ballistic lower bound `X i n ≥ (κ/2) n` for `n ≥ N₀` on one
walker.  Then for every `θ > 0`, for all sufficiently large levels `r`, the defect is halved over a
block of `B ℓ` levels as soon as `ℓ ≥ θ r` and the block starts below `ℓ`.

Equivalently: the fluid-limit contraction of `(blkprob)` is only needed for block scales
`ℓ = o(r)`. -/
theorem coarse_halving (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0)
    {B : ℕ} {θ : ℝ} (hθ : 0 < θ)
    {i : ι} {κ : ℝ} (hκ : 0 < κ) {N₀ : ℕ}
    (hspd : ∀ n : ℕ, N₀ ≤ n → (κ / 2) * (n : ℝ) ≤ (X i n : ℝ))
    (hlim : Tendsto (fun n : ℕ => spread X n / (n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ r : ℕ in atTop, ∀ ℓ : ℕ, θ * (r : ℝ) ≤ (ℓ : ℝ) →
      defect X τ r ≤ (ℓ : ℤ) → 2 * defect X τ (r + B * ℓ) ≤ (ℓ : ℤ) := by
  classical
  -- the sublinear-spread rate we may spend
  set ε : ℝ := κ * θ / (8 * (1 + (B : ℝ) * θ)) with hεdef
  have hBθ : (0 : ℝ) < 1 + (B : ℝ) * θ := by positivity
  have hε : 0 < ε := by
    rw [hεdef]; positivity
  -- the two identities that make the constants work
  have hident : ε * (2 / κ) * (1 / θ + (B : ℝ)) = 1 / 4 := by
    rw [hεdef]
    field_simp
    ring
  -- eventual sublinearity of the spread at rate `ε`
  have hev : ∀ᶠ n : ℕ in atTop, spread X n / (n : ℝ) < ε :=
    (tendsto_order.1 hlim).2 ε hε
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hev
  -- the level threshold forced by `ε N₀ ≤ ℓ / 4`
  obtain ⟨R₀, hR₀⟩ : ∃ R : ℕ, 4 * ε * (N₀ : ℝ) / θ ≤ (R : ℝ) :=
    ⟨⌈4 * ε * (N₀ : ℝ) / θ⌉₊, Nat.le_ceil _⟩
  have hτge := tau_ge hτ hne h0
  filter_upwards [eventually_ge_atTop (max (max n₁ 1) R₀)] with r hr
  intro ℓ hℓr hdr
  have hA : max n₁ 1 ≤ r := le_trans (le_max_left (max n₁ 1) R₀) hr
  have hr1 : 1 ≤ r := le_trans (le_max_right n₁ 1) hA
  have hrn₁ : n₁ ≤ r := le_trans (le_max_left n₁ 1) hA
  have hrR₀ : R₀ ≤ r := le_trans (le_max_right (max n₁ 1) R₀) hr
  -- the record time at the end of the block is past the spread threshold
  have hy : n₁ ≤ τ (r + B * ℓ) :=
    le_trans (le_trans hrn₁ (Nat.le_add_right r (B * ℓ))) (hτge _)
  have hy0 : 0 < τ (r + B * ℓ) := lt_of_lt_of_le hr1 (le_trans (Nat.le_add_right r (B * ℓ)) (hτge _))
  have hy0' : (0 : ℝ) < ((τ (r + B * ℓ) : ℕ) : ℝ) := by exact_mod_cast hy0
  -- the spread bound at the record time
  have hsp := hn₁ _ hy
  rw [div_lt_iff₀ hy0'] at hsp
  -- the record time is at most `N₀ + (2/κ) y`
  have hτle := tau_le_threshold hτ hκ hspd (r + B * ℓ)
  -- the defect at the end of the block is the spread there
  have hdefeq : ((defect X τ (r + B * ℓ) : ℤ) : ℝ) = spread X (τ (r + B * ℓ)) :=
    defect_eq_spread hτ _
  have hcast : (((r + B * ℓ : ℕ)) : ℝ) = (r : ℝ) + (B : ℝ) * (ℓ : ℝ) := by push_cast; ring
  -- `r ≤ ℓ/θ`, and the chosen `ε` spends the budget
  have hle_r : (r : ℝ) ≤ (ℓ : ℝ) / θ := by
    rw [le_div_iff₀ hθ]
    linarith [hℓr]
  have h4 : 4 * ε * (N₀ : ℝ) / θ ≤ (r : ℝ) := hR₀.trans (by exact_mod_cast hrR₀)
  have h6 : ε * (N₀ : ℝ) ≤ (ℓ : ℝ) / 4 := by
    have hmul := mul_le_mul_of_nonneg_left h4 (le_of_lt hθ)
    have hsimp : θ * (4 * ε * (N₀ : ℝ) / θ) = 4 * ε * (N₀ : ℝ) := by
      field_simp
    linarith [hmul, hℓr, hsimp]
  have hbig : ε * ((N₀ : ℝ) + (2 / κ) * ((r : ℝ) + (B : ℝ) * (ℓ : ℝ))) ≤ (ℓ : ℝ) / 2 := by
    have h1 : (r : ℝ) + (B : ℝ) * (ℓ : ℝ) ≤ (ℓ : ℝ) * (1 / θ + (B : ℝ)) := by
      have hcol : (ℓ : ℝ) * (1 / θ + (B : ℝ)) = (ℓ : ℝ) / θ + (B : ℝ) * (ℓ : ℝ) := by
        field_simp
      linarith [hle_r]
    have h2 : (2 / κ) * ((r : ℝ) + (B : ℝ) * (ℓ : ℝ))
        ≤ (2 / κ) * ((ℓ : ℝ) * (1 / θ + (B : ℝ))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : ε * ((2 / κ) * ((ℓ : ℝ) * (1 / θ + (B : ℝ)))) = (ℓ : ℝ) / 4 := by
      nlinarith [hident]
    have h4' := mul_le_mul_of_nonneg_left h2 (le_of_lt hε)
    nlinarith [h3, h4', h6]
  -- assemble
  have hmain : ((defect X τ (r + B * ℓ) : ℤ) : ℝ) ≤ (ℓ : ℝ) / 2 := by
    rw [hdefeq]
    have h1 : spread X (τ (r + B * ℓ)) ≤ ε * ((τ (r + B * ℓ) : ℕ) : ℝ) := le_of_lt hsp
    have h2 : ε * ((τ (r + B * ℓ) : ℕ) : ℝ)
        ≤ ε * ((N₀ : ℝ) + (2 / κ) * ((r : ℝ) + (B : ℝ) * (ℓ : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hε)
      calc ((τ (r + B * ℓ) : ℕ) : ℝ) ≤ (N₀ : ℝ) + (2 / κ) * (((r + B * ℓ : ℕ)) : ℝ) := hτle
        _ = (N₀ : ℝ) + (2 / κ) * ((r : ℝ) + (B : ℝ) * (ℓ : ℝ)) := by rw [hcast]
    linarith
  have h2 : ((2 * defect X τ (r + B * ℓ) : ℤ) : ℝ) ≤ ((ℓ : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h2

end Coarse

/-! ### The unconditional almost-sure form at the canonical array -/

/-- **Almost surely, at every coarse scale the defect is halved over a block.**

At the canonical actual array, for every `θ > 0`, almost surely for all sufficiently large levels
`r` the halving clause of the paper's block holds for every block scale `ℓ ≥ θ r`, provided the
block starts with `d r ≤ ℓ`.  No fluid-limit input is used: only `(diam)`
(`M7Block.diam_actual_recordo`) and the record-time bound from the ballistic lower bound. -/
theorem coarse_halving_actual {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ r : ℕ in atTop, ∀ ℓ : ℕ, θ * (r : ℝ) ≤ (ℓ : ℝ) →
      defect (actX p m U) (recTimeA p m U) r ≤ (ℓ : ℤ) →
      2 * defect (actX p m U) (recTimeA p m U) (r + B * ℓ) ≤ (ℓ : ℤ) := by
  classical
  obtain ⟨κ, hκ, hspeed⟩ := speed_actual hp0 hp1 hm
  have hspd := hspeed N hN
  have hrec := ae_isRecord_recTimeA (N := N) (m := m) hp0 hp1 hm hN
  have hdiam := M7Block.diam_actual_recordo (N := N) hp0 hp1 hm hN
  filter_upwards [hspd, hrec, hdiam] with U hU hτ hd
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hU (Classical.arbitrary (Fin N)))
  exact coarse_halving (X := actX p m U) (τ := recTimeA p m U) hτ (actX_step p m U)
    (actX_zero p m U) hθ hκ hN₀ hd

end HblkCoarse


/-! ### At coarse scales the `(blkprob)` bad event *is* the record-advance failure -/

namespace HblkCoarse

open RecordDefect RecordoSupply HblkTwo SwarmM4C.LawBridge SwarmRecordMeas
  SwarmRecordMeas.Actual SwarmRecordMeas.StartLaw Swarming Swarming.Uniform

/-- **The residual content of `(blkprob)` at coarse scales.**

For every `θ > 0`, almost surely for all sufficiently large levels `r` and every block scale
`ℓ ≥ θ r`, the paper's `(blkprob)` bad event on `{d r ≤ ℓ}` coincides exactly with the failure of
the record-advance clause `τ (r + B ℓ) - τ r ≤ T ℓ`: the halving clause cannot fail there.

So the halving clause `(half)` of `hblk` needs the paper's fluid-limit contraction only at scales
`ℓ = o(r)`; at every scale comparable with `r` — in particular on the diagonal
`ℓ = λ(r) ≈ r/(2 C₀)` used in the paper's Borel–Cantelli step — the sole remaining analytic input
is the ballistic advance of the record. -/
theorem badBlk_iff_badTime_coarse_actual {N : ℕ} [Nonempty (Fin N)] {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N)
    (B C₀ T : ℕ) (hC₀ : B + T + 1 ≤ C₀) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ r : ℕ in atTop, ∀ ℓ : ℕ, θ * (r : ℝ) ≤ (ℓ : ℝ) →
      (HblkTwo.BadBlk B C₀ T
          (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
            fun r => recTimeA p m U r) r ℓ
        ↔ HblkTwo.BadTime B T
          (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
            fun r => recTimeA p m U r) r ℓ) := by
  classical
  have hhalf := coarse_halving_actual (N := N) hp0 hp1 hm hN B hθ
  have hrec := ae_isRecord_recTimeA (N := N) (m := m) hp0 hp1 hm hN
  filter_upwards [hhalf, hrec] with U hU hτ
  filter_upwards [hU] with r hr
  intro ℓ hℓ
  set q : (ℕ → ℕ) × (ℕ → ℕ) :=
    (((fun r => (defect (actX p m U) (recTimeA p m U) r).toNat) : ℕ → ℕ),
      fun r => recTimeA p m U r) with hq
  have hnoHalf : ¬ HblkTwo.BadHalf B q r ℓ := by
    rintro ⟨hd, hgt⟩
    have hd' : defect (actX p m U) (recTimeA p m U) r ≤ (ℓ : ℤ) := by
      have h1 : ((defect (actX p m U) (recTimeA p m U) r).toNat : ℤ) ≤ (ℓ : ℤ) := by
        exact_mod_cast hd
      rwa [Int.toNat_of_nonneg (defect_nonneg hτ r)] at h1
    have h2 : 2 * defect (actX p m U) (recTimeA p m U) (r + B * ℓ) ≤ (ℓ : ℤ) :=
      hr ℓ hℓ hd'
    have h3 : (defect (actX p m U) (recTimeA p m U) (r + B * ℓ)).toNat ≤ ℓ / 2 := by
      have hcast2 : (((defect (actX p m U) (recTimeA p m U) (r + B * ℓ)).toNat : ℕ) : ℤ)
          = defect (actX p m U) (recTimeA p m U) (r + B * ℓ) :=
        Int.toNat_of_nonneg (defect_nonneg hτ _)
      have h4 : 2 * (defect (actX p m U) (recTimeA p m U) (r + B * ℓ)).toNat ≤ ℓ := by
        have h5 : ((2 * (defect (actX p m U) (recTimeA p m U) (r + B * ℓ)).toNat : ℕ) : ℤ) ≤ (ℓ : ℤ) := by
          push_cast
          linarith [h2, hcast2]
        exact_mod_cast h5
      omega
    have h6 : (defect (actX p m U) (recTimeA p m U) (r + B * ℓ)).toNat ≤ ℓ / 2 := h3
    have : ¬ (ℓ / 2 < (defect (actX p m U) (recTimeA p m U) (r + B * ℓ)).toNat) := not_lt.2 h6
    exact this (by simpa [hq] using hgt)
  constructor
  · intro hb
    by_contra ht
    exact hnoHalf (Or.resolve_left (HblkTwo.badBlk_subset
      (himpl_of_record (X := actX p m U) (τ := recTimeA p m U) hτ (actX_step p m U) hC₀) hb) ht)
  · rintro ⟨hd, ht⟩
    refine ⟨hd, fun hgood => ?_⟩
    exact absurd hgood.1 (not_le.2 ht)

end HblkCoarse

