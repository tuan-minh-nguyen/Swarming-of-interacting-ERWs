/-
# The initial class spread at a grid time, from grid convergence

`CoincideClass.classSpread_tendsto` needs one input beyond the per-scale local-good field: at
the grid time of the fluid time `s`, the spread of the coincidence class must be `ε₀·L`.  This
module derives that input from grid convergence alone, so it is not an extra stochastic
premise: if the scaled positions of all members of `D` converge to one common value `c`, then

  `spread_D(m n) ≤ 2 L_n · Σ_{k∈D} |scaled_k(m n) − c|`,

and the right-hand side is `ε n L_n` with `ε n → 0`.

This is the "one small-spread grid time per scale" residual listed in
`COALESCE_WITNESS.md` (and identified there as the same one that `HalvingResidual` isolates),
in the form supplied by `FluidJoinHcoal.gridSample_tendsto` from the compactness output.
-/
import Swarm.CoincideClass
import Swarm.FluidLimitLight

open Finset Filter Topology
open scoped BigOperators

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace M4Coincide

open Glue RecordDefect LocalFluid

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **Spread against a common reference point.**  If every member of `D` is within `S` of the
reference `m₀`, then the spread of `D` is at most `2S`; the sum of the absolute deviations is
one such `S`. -/
theorem spreadS_le_two_mul_sum_abs {X : ι → ℕ → ℤ} {D : Finset ι} (hD : D.Nonempty)
    {m : ℕ} {m₀ : ℝ} :
    ((spreadS X D m : ℤ) : ℝ) ≤ 2 * ∑ k ∈ D, |((X k m : ℝ) - m₀)| := by
  have hsum : ∀ k ∈ D, |((X k m : ℝ) - m₀)| ≤ ∑ j ∈ D, |((X j m : ℝ) - m₀)| :=
    fun k hk => Finset.single_le_sum (f := fun j => |((X j m : ℝ) - m₀)|)
      (fun j _ => abs_nonneg _) hk
  have hmax : ((sMax X D m : ℤ) : ℝ) ≤ m₀ + ∑ j ∈ D, |((X j m : ℝ) - m₀)| := by
    obtain ⟨k, hk, hval⟩ := exists_sMax (X := X) (S := D) (n := m) hD
    have h1 : ((X k m : ℝ) - m₀) ≤ ∑ j ∈ D, |((X j m : ℝ) - m₀)| :=
      le_trans (le_abs_self _) (hsum k hk)
    rw [hval]
    push_cast
    linarith
  have hmin : m₀ - ∑ j ∈ D, |((X j m : ℝ) - m₀)| ≤ ((sMin X D m : ℤ) : ℝ) := by
    obtain ⟨k, hk, hval⟩ := exists_sMin (X := X) (S := D) (n := m) hD
    have h1 : m₀ - (X k m : ℝ) ≤ ∑ j ∈ D, |((X j m : ℝ) - m₀)| := by
      refine le_trans ?_ (hsum k hk)
      simpa using neg_le_abs ((X k m : ℝ) - m₀)
    rw [hval]
    push_cast
    linarith
  unfold spreadS
  push_cast
  linarith

/-- **The initial class spread is `o(L)` under grid convergence.**  `ε` is explicit:
`ε n = 2 Σ_{k∈D} |y_k(n) − c|`, which vanishes because `D` is finite. -/
theorem exists_eps_spread_of_tendsto
    {X : ℕ → ι → ℕ → ℤ} {level scale mm : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) {D : Finset ι} (hD : D.Nonempty) {c : ℝ}
    (hdev : ∀ k ∈ D,
      Tendsto (fun n => ((X n k (mm n) : ℝ) - (level n : ℝ)) / (scale n : ℝ)) atTop (𝓝 c)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n,
      ((spreadS (X n) D (mm n) : ℤ) : ℝ) ≤ ε n * (scale n) := by
  classical
  refine ⟨fun n => 2 * ∑ k ∈ D, |((X n k (mm n) : ℝ) - (level n : ℝ)) / (scale n : ℝ) - c|,
    ?_, ?_⟩
  · have hsum : Tendsto
        (fun n => ∑ k ∈ D, |((X n k (mm n) : ℝ) - (level n : ℝ)) / (scale n : ℝ) - c|)
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => ∑ k ∈ D,
          |((X n k (mm n) : ℝ) - (level n : ℝ)) / (scale n : ℝ) - c|) atTop
          (𝓝 (∑ k ∈ D, 0)) := by
        refine tendsto_finsetSum D (fun k hk => ?_)
        have h1 : Tendsto (fun n => ((X n k (mm n) : ℝ) - (level n : ℝ)) / (scale n : ℝ) - c)
            atTop (𝓝 (c - c)) := (hdev k hk).sub tendsto_const_nhds
        have h2 := h1.abs
        simpa using h2
      simpa using h0
    simpa using hsum.const_mul 2
  · intro n
    have hLpos : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have hLne : (scale n : ℝ) ≠ 0 := ne_of_gt hLpos
    have hbase := spreadS_le_two_mul_sum_abs (X := X n) (D := D) hD (m := mm n)
      (m₀ := (level n : ℝ) + c * (scale n : ℝ))
    have hterm : ∀ k ∈ D,
        |((X n k (mm n) : ℝ) - ((level n : ℝ) + c * (scale n : ℝ)))|
          = |((X n k (mm n) : ℝ) - (level n : ℝ)) / (scale n : ℝ) - c| * (scale n : ℝ) := by
      intro k _
      have hid : (((X n k (mm n) : ℝ) - (level n : ℝ)) / (scale n : ℝ) - c) * (scale n : ℝ)
          = (X n k (mm n) : ℝ) - ((level n : ℝ) + c * (scale n : ℝ)) := by
        rw [sub_mul, div_mul_cancel₀ _ hLne]
        ring
      rw [← hid, abs_mul, abs_of_pos hLpos]
    have hstep1 : ∑ k ∈ D, |((X n k (mm n) : ℝ) - ((level n : ℝ) + c * (scale n : ℝ)))|
        = (∑ k ∈ D, |((X n k (mm n) : ℝ) - (level n : ℝ)) / (scale n : ℝ) - c|)
          * (scale n : ℝ) := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_mul]
    calc ((spreadS (X n) D (mm n) : ℤ) : ℝ)
        ≤ 2 * ∑ k ∈ D, |((X n k (mm n) : ℝ) - ((level n : ℝ) + c * (scale n : ℝ)))| := hbase
      _ = (2 * ∑ k ∈ D, |((X n k (mm n) : ℝ) - (level n : ℝ)) / (scale n : ℝ) - c|)
            * (scale n : ℝ) := by rw [hstep1]; ring

/-- The same statement in the exact shape of `classSpread_tendsto`'s `hstart`: the record
window of level `level n` and the grid knot `⌊L_n s⌋` of the fluid time `s`. -/
theorem classStart_tendsto
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) {D : Finset ι} (hD : D.Nonempty) {c : ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hconv : ∀ k ∈ D, Tendsto (fun n =>
      FluidLimit.scaledPosition (X n) (level n) (τ n (level n)) (scale n) k
        ⌊(scale n : ℝ) * s⌋₊) atTop (𝓝 c)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n,
      ((spreadS (X n) D (τ n (level n) + ⌊(scale n : ℝ) * s⌋₊) : ℤ) : ℝ)
        ≤ ε n * (scale n) := by
  refine exists_eps_spread_of_tendsto (level := level) (scale := scale)
    (mm := fun n => τ n (level n) + ⌊(scale n : ℝ) * s⌋₊) hscale hD (c := c) ?_
  intro k hk
  have h := hconv k hk
  refine h.congr (fun n => ?_)
  unfold FluidLimit.scaledPosition
  ring

/-- **The source's `(4.8)` for the coincidence class, from grid convergence.**  Per scale, the
local-good field (`loccoord`, the lag, `(Wpos)`'s ingredients via `LocalField`), `(locgroup)`,
the nearest-neighbour path, the carrier `d_r ≤ L` and `r ≥ (T+3)L`; plus convergence of the
scaled positions of `D` to one common fluid value at the single grid time `⌊L s⌋`.  Then one
vanishing `ε` bounds the class spread at every grid time `⌊L t⌋`, `s ≤ t ≤ T`.

Neither the initial small spread at the start time nor the final `o(L)` statement is an extra
premise: the first is derived from grid convergence (`classStart_tendsto`), the second is
`classSpread_tendsto`. -/
theorem classSpread_of_grid
    {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {C : ℝ} {CT : ℕ → ℝ} {T : ℕ} {r η : ℕ → ℕ}
    (hLF : ∀ n, LocalField (X n) (τ n) (H n) C (CT n) T (scale n) (r n) (η n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) (CT n) T (scale n) (r n))
    (hC1 : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (m : ℕ), |X n i (m + 1) - X n i m| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (r n) ≤ ((scale n : ℕ) : ℤ))
    (hrT : ∀ n, (T + 3) * scale n ≤ r n)
    {D : Finset ι} (hD : D.Nonempty)
    {ε1 ε2 : ℕ → ℝ} (hε1t : Tendsto ε1 atTop (𝓝 0)) (hε2t : Tendsto ε2 atTop (𝓝 0))
    {s Tn : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ Tn) (hTn : Tn ≤ (T : ℝ)) {c : ℝ}
    (hconv : ∀ k ∈ D, Tendsto (fun n =>
      FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) k
        ⌊(scale n : ℝ) * s⌋₊) atTop (𝓝 c))
    (hη : ∀ n, ((η n : ℕ) : ℝ) ≤ ε1 n * (scale n))
    (hct : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 n * (scale n)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (n : ℕ) (t : ℝ), s ≤ t → t ≤ Tn →
        ((spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ) ≤ ε n * (scale n) := by
  obtain ⟨ε0, hε0t, hstart⟩ :=
    classStart_tendsto (X := X) (τ := τ) (level := r) (scale := scale) hscale hD hs0 hconv
  exact classSpread_tendsto hscale hscaleTop hLF hgrow hC1 hCT hτ hne hdr hrT hD hε0t hε1t
    hε2t hs0 hsT hTn hstart hη hct

/-- **The paper's `(4.8)` in pairwise form, from grid convergence.**  Same hypotheses as
`classSpread_of_grid`; the conclusion is the literal pairwise statement consumed by
`Coalesce.hpair_of_class_spread`: two walkers of the coincidence class have scaled positions
within one vanishing `ε n` at every grid time `⌊L_n t⌋`, `s ≤ t ≤ T`. -/
theorem pairwise_of_grid
    {scale : ℕ → ℕ} (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {H : ℕ → Finset ι → ℕ → ℤ → ℤ}
    {C : ℝ} {CT : ℕ → ℝ} {T : ℕ} {r η : ℕ → ℕ}
    (hLF : ∀ n, LocalField (X n) (τ n) (H n) C (CT n) T (scale n) (r n) (η n))
    (hgrow : ∀ n, GroupGrow (H n) (X n) (τ n) (CT n) T (scale n) (r n))
    (hC1 : 1 ≤ C) (hCT : ∀ n, 0 ≤ CT n)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (m : ℕ), |X n i (m + 1) - X n i m| = 1)
    (hdr : ∀ n, defect (X n) (τ n) (r n) ≤ ((scale n : ℕ) : ℤ))
    (hrT : ∀ n, (T + 3) * scale n ≤ r n)
    {D : Finset ι} (hD : D.Nonempty)
    {ε1 ε2 : ℕ → ℝ} (hε1t : Tendsto ε1 atTop (𝓝 0)) (hε2t : Tendsto ε2 atTop (𝓝 0))
    {s Tn : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ Tn) (hTn : Tn ≤ (T : ℝ)) {c : ℝ}
    (hconv : ∀ k ∈ D, Tendsto (fun n =>
      FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) k
        ⌊(scale n : ℝ) * s⌋₊) atTop (𝓝 c))
    (hη : ∀ n, ((η n : ℕ) : ℝ) ≤ ε1 n * (scale n))
    (hct : ∀ n, CT n * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ ε2 n * (scale n)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (n : ℕ) (i j : ι) (t : ℝ), i ∈ D → j ∈ D → s ≤ t → t ≤ Tn →
        |FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) i ⌊(scale n : ℝ) * t⌋₊
          - FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) j
              ⌊(scale n : ℝ) * t⌋₊| ≤ ε n := by
  obtain ⟨ε, hεt, hspread⟩ := classSpread_of_grid hscale hscaleTop hLF hgrow hC1 hCT hτ hne
    hdr hrT hD hε1t hε2t hs0 hsT hTn hconv hη hct
  refine ⟨ε, hεt, ?_⟩
  intro n i j t hi hj hst htT
  have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  have hDne : D.Nonempty := ⟨i, hi⟩
  have hsp := hspread n t hst htT
  have hcast : FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) i ⌊(scale n : ℝ) * t⌋₊
      - FluidLimit.scaledPosition (X n) (r n) (τ n (r n)) (scale n) j ⌊(scale n : ℝ) * t⌋₊
      = ((X n i (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℝ) - (X n j (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℝ)) / (scale n : ℝ) := by
    unfold FluidLimit.scaledPosition
    ring
  have hsub1 : X n i (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) - X n j (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) ≤ spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) := sub_spreadS hDne hi hj
  have hsub2 : X n j (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) - X n i (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) ≤ spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) := sub_spreadS hDne hj hi
  rw [hcast, abs_div, abs_of_pos hL, div_le_iff₀ hL, abs_le]
  constructor
  · have h2 : ((X n j (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) - X n i (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ)
        ≤ ((spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ) := by exact_mod_cast hsub2
    push_cast at h2 ⊢
    linarith
  · have h1 : ((X n i (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) - X n j (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ)
        ≤ ((spreadS (X n) D (τ n (r n) + ⌊(scale n : ℝ) * t⌋₊) : ℤ) : ℝ) := by exact_mod_cast hsub1
    push_cast at h1 ⊢
    linarith
