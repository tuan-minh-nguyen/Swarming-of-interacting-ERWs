/-
# From the group potential at the reset time to the internal spread

`NestedLeader.lean` reduces `(diam)` to the drift residual `DriftInput X C`, which bounds the block
gap at time `n` by `C (spread_A(s) + deficit_s + 2) + o(n)` at the reset time `s`.  The present
file performs the last purely positional step, so that the residual can be supplied by the
paper's `hcomp`/`(compare)` chain in terms of the *positions* only:

* `potential_le_max_sub_max` — a group potential of the form
  `(|A|)⁻¹ ∑_{i∈A} H (X_s^i) - max_{j∉A} H (X_s^j)` with `H` nondecreasing and dominated above by
  `K (y - x) + η` (the paper's `(compare)`) is at most `K (max_A X_s - max_{A^c} X_s) + η`;
* `max_sub_max_eq_spread_add_gap` — for a leading block,
  `max_A X_s - max_{A^c} X_s = spread_A(s) + gap_A(s)` (exact, no estimate);
* `gapAt_reset_le_deficit` — at the reset time `s` of a separated block,
  `gap_A(s) ≤ 4 + deficit_s` (the reset descent `gapAt_reset_le` composed with the deficit);
* `driftInput_of_positional` — the composition: a positional bound
  `W_s ≤ K (max_A X_s - max_{A^c} X_s) + o(n)` implies `DriftInput X K`,
  hence `(diam)` through `spread_div_tendsto_zero_of_drift`.

No probability, no filtration: everything is a statement about one unit-step path array.
-/
import Swarm.NestedLeader

open Filter Finset Topology
open scoped BigOperators
open LeaderDescent
open NestedLeader

namespace NestedLeaderPot

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (X : ι → ℕ → ℤ) [Nonempty ι]

/-! ## Part A: positional identities -/

/-- For a nondecreasing `H` the maximum of `H ∘ X` over a block is `H` of the maximum. -/
theorem sup'_comp_mono {H : ℤ → ℝ} (hH : Monotone H) {A : Finset ι} (hA : A.Nonempty) (t : ℕ) :
    A.sup' hA (fun j => H (X j t)) = H (A.sup' hA (fun j => X j t)) := by
  obtain ⟨a, ha, hmax⟩ := exists_max_image A (fun j => X j t) hA
  have h1 : A.sup' hA (fun j => X j t) = X a t :=
    le_antisymm (sup'_le hA _ (fun j hj => hmax j hj)) (le_sup' (fun j => X j t) ha)
  have h2 : A.sup' hA (fun j => H (X j t)) = H (X a t) :=
    le_antisymm (sup'_le hA _ (fun j hj => hH (hmax j hj))) (le_sup' (fun j => H (X j t)) ha)
  rw [h1, h2]

/-- The mean of a nondecreasing function over a block is at most the function of the maximum. -/
theorem mean_le_sup {H : ℤ → ℝ} (hH : Monotone H) {A : Finset ι} (hA : A.Nonempty) (t : ℕ) :
    ((A.card : ℝ))⁻¹ * ∑ i ∈ A, H (X i t) ≤ H (A.sup' hA (fun j => X j t)) := by
  have hcard : (0 : ℝ) < (A.card : ℝ) := by
    have := Finset.card_pos.mpr hA
    exact_mod_cast this
  rw [← sup'_comp_mono X hH hA t]
  have hsum : ∑ i ∈ A, H (X i t) ≤ ∑ _i ∈ A, A.sup' hA (fun j => H (X j t)) :=
    Finset.sum_le_sum (fun i hi => le_sup' (fun j => H (X j t)) hi)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  rw [← div_eq_inv_mul, div_le_iff₀ hcard]
  linarith

/-- **The positional form of the group potential.**  For a leading block `A` and a nondecreasing
`H` whose increments are dominated by `K (y - x) + η` (the paper's `(compare)`), the potential
`(|A|)⁻¹ ∑_{i∈A} H(X_s^i) - max_{j∉A} H(X_s^j)` is at most
`K (max_A X_s - max_{A^c} X_s) + η`. -/
theorem potential_le_max_sub_max {H : ℤ → ℝ} (hH : Monotone H) {K η : ℝ}
    (hcmp : ∀ x y : ℤ, x ≤ y → H y - H x ≤ K * ((y : ℝ) - (x : ℝ)) + η)
    {A : Finset ι} (hA : A.Nonempty) (hAc : (univ \ A).Nonempty) (t : ℕ)
    (hlead : ∀ i ∈ A, ∀ j ∉ A, X j t ≤ X i t) :
    ((A.card : ℝ))⁻¹ * ∑ i ∈ A, H (X i t) - (univ \ A).sup' hAc (fun j => H (X j t))
      ≤ K * (((A.sup' hA (fun i => X i t) : ℤ) : ℝ)
          - (((univ \ A).sup' hAc (fun i => X i t) : ℤ) : ℝ)) + η := by
  rw [sup'_comp_mono X hH hAc t]
  have h1 := mean_le_sup X hH hA t
  have hle : (univ \ A).sup' hAc (fun i => X i t) ≤ A.sup' hA (fun i => X i t) := by
    refine sup'_le hAc _ (fun j hj => ?_)
    have hjA : j ∉ A := (mem_sdiff.mp hj).2
    have hA' := hA
    obtain ⟨a, ha⟩ := hA
    exact le_trans (hlead a ha j hjA) (le_sup' (fun i => X i t) ha)
  have hcomp := hcmp _ _ hle
  linarith

/-- For a leading block the difference of the block maximum and the complement maximum is exactly
the internal spread plus the block gap. -/
theorem max_sub_max_eq_spread_add_gap {A : Finset ι} (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (t : ℕ) :
    (((A.sup' hA (fun i => X i t) : ℤ) : ℝ)
        - (((univ \ A).sup' hAc (fun i => X i t) : ℤ) : ℝ))
      = ((blockSpread (fun i => X i t) A : ℤ) : ℝ) + ((gapAt (fun i => X i t) A : ℤ) : ℝ) := by
  rw [blockSpread_eq hA, gapAt, dif_pos ⟨hA, hAc⟩]
  push_cast
  ring

/-! ## Part B: the deficit at the reset time, without nonnegativity of the *gap* -/

/-- The deficit can drop by at most one in one step. -/
theorem deficit_pred_le (hX : UnitStep X) (s : ℕ) :
    deficit X (s - 1) ≤ deficit X s + 1 := by
  refine sup'_le univ_nonempty _ (fun j _ => ?_)
  have hmono : runMax X j (s - 1) ≤ runMax X j s := by
    refine runMax_mono X j (by omega)
  have hstep : X j s ≤ X j (s - 1) + 1 := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp
    · have h := step_le X hX j (s - 1)
      rwa [Nat.sub_add_cancel hs] at h
  have h := le_deficit X s j
  have h2 : runMax X j (s - 1) - X j (s - 1) ≤ runMax X j s - X j s + 1 := by omega
  omega

/-- **The reset-time gap is controlled by the deficit at the same time.**  This is
`LeaderDescent.gapAt_reset_le` composed with the deficit of the complement. -/
theorem gapAt_reset_le_deficit (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0)
    {A : Finset ι} (hA : A.Nonempty) (hAc : (univ \ A).Nonempty) {n : ℕ}
    (hnn : ∀ i, 0 ≤ X i (resetTime X A n - 1)) :
    gapAt (fun i => X i (resetTime X A n)) A ≤ 4 + deficit X (resetTime X A n) := by
  have h1 := gapAt_reset_le X hX h0 hA hAc hnn
  have h2 : ((univ \ A).sup' hAc
      (fun j => runMax X j (resetTime X A n - 1) - X j (resetTime X A n - 1)))
      ≤ deficit X (resetTime X A n - 1) := sup_compl_le_deficit X hAc _
  have h3 := deficit_pred_le X hX (resetTime X A n)
  omega

/-- The block gap is at most the total spread. -/
theorem gapAt_le_spreadZ {A : Finset ι} (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (t : ℕ) : gapAt (fun i => X i t) A ≤ spreadZ X t := by
  have hA' := hA
  have hAc' := hAc
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hAc
  have h1 : A.inf' hA' (fun i => X i t) ≤ univ.sup' univ_nonempty (fun i => X i t) :=
    le_trans (inf'_le _ ha) (le_sup' (fun i => X i t) (mem_univ a))
  have h2 : univ.inf' univ_nonempty (fun i => X i t)
      ≤ (univ \ A).sup' hAc' (fun i => X i t) :=
    le_trans (inf'_le _ (mem_univ b)) (le_sup' (fun i => X i t) hb)
  have h3 : spreadZ X t
      = univ.sup' univ_nonempty (fun i => X i t) - univ.inf' univ_nonempty (fun i => X i t) := rfl
  rw [gapAt, dif_pos ⟨hA', hAc'⟩, h3]
  linarith

/-- **The reset-time gap with a constant, from eventual nonnegativity.**  Either the reset time is
large enough for `gapAt_reset_le_deficit`, or it is bounded by the eventual-nonnegativity
threshold, in which case the gap is at most the total spread `2s`.  The constant `2T₀` is absorbed
into the `o(n)` term. -/
theorem gapAt_reset_le_deficit_const (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0)
    (hpos : ∀ᶠ t : ℕ in atTop, ∀ i, 0 ≤ X i t) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        ((gapAt (fun i => X i (resetTime X A n)) A : ℤ) : ℝ)
          ≤ 4 + ((deficit X (resetTime X A n) : ℤ) : ℝ) + ε * (n : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hpos
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * (T₀ : ℝ) / ε)
  filter_upwards [Filter.eventually_ge_atTop N₀] with n hn
  intro A hA hAc hlead hmax
  set s := resetTime X A n with hsdef
  have hspos : 1 ≤ s := resetTime_pos X h0 hA hAc n
  by_cases hcase : T₀ ≤ s - 1
  · have hnn : ∀ i, 0 ≤ X i (s - 1) := fun i => hT₀ (s - 1) hcase i
    have h1 : gapAt (fun i => X i s) A ≤ 4 + deficit X s :=
      gapAt_reset_le_deficit X hX h0 hA hAc hnn
    have h2 : ((gapAt (fun i => X i s) A : ℤ) : ℝ) ≤ ((4 + deficit X s : ℤ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    have h3 : (0:ℝ) ≤ ε * (n:ℝ) := by positivity
    linarith
  · have hsT : s ≤ T₀ := by omega
    have h1 : gapAt (fun i => X i s) A ≤ spreadZ X s := gapAt_le_spreadZ X hA hAc s
    have h2 : ((spreadZ X s : ℤ) : ℝ) ≤ 2 * (s : ℝ) := by
      have hb := blockSpread_le_two_mul X hX h0 (A := univ) univ_nonempty s
      rwa [blockSpread_eq univ_nonempty] at hb
    have h3 : ((gapAt (fun i => X i s) A : ℤ) : ℝ) ≤ 2 * (s : ℝ) := by
      exact le_trans (by exact_mod_cast h1) h2
    have hsR : (s : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast hsT
    have hN : 2 * (T₀ : ℝ) ≤ ε * (n : ℝ) := by
      have h1 : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h2 : 2 * (T₀ : ℝ) / ε < (N₀ : ℝ) := hN₀
      rw [div_lt_iff₀ hε] at h2
      nlinarith
    have hd : (0:ℝ) ≤ ((deficit X s : ℤ) : ℝ) := by
      have h := deficit_nonneg X s
      exact_mod_cast h
    linarith

/-- **From a positional bound on the potential to the drift residual.**  If, at the reset time `s`
of a separated leading block, the potential is bounded by `K (max_A X_s - max_{A^c} X_s) + o(n)` —
the paper's `hcomp` composed with `(compare)` — and the potential bounds the block gap from above
at time `n` (`hgap`) and does not increase along the separating run (`htel`, the telescoped
`(Wdrift)`), then `DriftInput X K` holds, hence `(diam)` through
`spread_div_tendsto_zero_of_drift`.  The reset-time gap bound `gapAt_reset_le_deficit_const` is
used here to replace `max_A X_s - max_{A^c} X_s` by `spread_A(s) + deficit_s`. -/
theorem driftInput_of_W_positional {K : ℝ} (hK : 0 ≤ K) (W : Finset ι → ℕ → ℝ)
    (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0)
    (hpos : ∀ᶠ t : ℕ in atTop, ∀ i, 0 ≤ X i t)
    (hgap : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        ((gapAt (fun i => X i n) A : ℤ) : ℝ) ≤ W A n + ε * (n : ℝ))
    (htel : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        W A n ≤ W A (resetTime X A n) + ε * (n : ℝ))
    (hpot : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        W A (resetTime X A n)
          ≤ K * (((A.sup' hA (fun i => X i (resetTime X A n)) : ℤ) : ℝ)
              - (((univ \ A).sup' hAc (fun i => X i (resetTime X A n)) : ℤ) : ℝ))
            + ε * (n : ℝ)) :
    DriftInput X K := by
  intro ε hε
  set η : ℝ := ε / (5 * (K + 1)) with hηdef
  have hK1 : (0:ℝ) < K + 1 := by linarith
  have hη : 0 < η := by rw [hηdef]; positivity
  have hηeq : η * (5 * (K + 1)) = ε := by rw [hηdef]; field_simp
  have hKη : (K + 1) * η ≤ ε / 5 := by nlinarith [hηeq, hη, hK]
  have hηle : η ≤ ε / 5 := by nlinarith [hηeq, hη, hK]
  have hKηle : K * η ≤ ε / 5 := by nlinarith [hKη, hK, hη]
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (gapAt_reset_le_deficit_const X hX h0 hpos η hη)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hgap η hη)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (htel η hη)
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp (hpot η hη)
  obtain ⟨N₄, hN₄⟩ := exists_nat_gt (2 * K / η)
  filter_upwards [Filter.eventually_ge_atTop N₀, Filter.eventually_ge_atTop N₁,
    Filter.eventually_ge_atTop N₂, Filter.eventually_ge_atTop N₃,
    Filter.eventually_ge_atTop N₄] with n hn0 hn1 hn2 hn3 hn4
  intro A hA hAc hlead hmax
  have h0' := hN₀ n hn0 A hA hAc hlead hmax
  have h1 := hN₁ n hn1 A hA hAc hlead hmax
  have h2 := hN₂ n hn2 A hA hAc hlead hmax
  have h3 := hN₃ n hn3 A hA hAc hlead hmax
  have hsplit := max_sub_max_eq_spread_add_gap X hA hAc (resetTime X A n)
  have hK2 : 2 * K ≤ η * (n : ℝ) := by
    have h1 : (N₄ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have h2 : 2 * K / η < (N₄ : ℝ) := hN₄
    rw [div_lt_iff₀ hη] at h2
    nlinarith
  have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hηn : (0:ℝ) ≤ η * (n : ℝ) := mul_nonneg (le_of_lt hη) hnn
  -- insert the positional identity into `h3`
  rw [hsplit] at h3
  -- `h3 : W_s ≤ K (spread_s + gap_s) + η n`
  have hgapK : K * (((gapAt (fun i => X i (resetTime X A n)) A : ℤ) : ℝ))
      ≤ K * (4 + ((deficit X (resetTime X A n) : ℤ) : ℝ) + η * (n:ℝ)) :=
    mul_le_mul_of_nonneg_left h0' hK
  have hKηn : K * η * (n:ℝ) ≤ ε / 5 * (n:ℝ) :=
    mul_le_mul_of_nonneg_right hKηle hnn
  have hK1ηn : (K + 1) * η * (n:ℝ) ≤ ε / 5 * (n:ℝ) :=
    mul_le_mul_of_nonneg_right hKη hnn
  have hηn5 : η * (n:ℝ) ≤ ε / 5 * (n:ℝ) :=
    mul_le_mul_of_nonneg_right hηle hnn
  nlinarith [h1, h2, h3, hgapK, hK, hK2, hηn, hKηn, hK1ηn, hηn5, hnn]

/-- **`(diam)` from the positional potential bound.** -/
theorem spread_div_tendsto_zero_of_positional {K : ℝ} (hK : 0 ≤ K) (W : Finset ι → ℕ → ℝ)
    (hgap : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        ((gapAt (fun i => X i n) A : ℤ) : ℝ) ≤ W A n + ε * (n : ℝ))
    (htel : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        W A n ≤ W A (resetTime X A n) + ε * (n : ℝ))
    (hpot : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        W A (resetTime X A n)
          ≤ K * (((A.sup' hA (fun i => X i (resetTime X A n)) : ℤ) : ℝ)
              - (((univ \ A).sup' hAc (fun i => X i (resetTime X A n)) : ℤ) : ℝ))
            + ε * (n : ℝ))
    (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0)
    (hdef : ∀ ε > 0, ∀ᶠ t : ℕ in atTop, ((deficit X t : ℤ) : ℝ) ≤ ε * (t : ℝ))
    (hpos : ∀ᶠ t : ℕ in atTop, ∀ i, 0 ≤ X i t) :
    Tendsto (fun n => ((spreadZ X n : ℤ) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
  spread_div_tendsto_zero_of_drift X hX h0 hK
    (driftInput_of_W_positional X hK W hX h0 hpos hgap htel hpot) hdef hpos

/-! ## Part C: the fixed-`H` group potential and the single drift residual -/

section FixedPotential

variable {H : ℤ → ℝ}

/-- The paper's group potential `W^{A,A^c}` built from a fixed potential `H`
(junk value `0` when the complement is empty). -/
noncomputable def Wpot (H : ℤ → ℝ) (A : Finset ι) (n : ℕ) : ℝ :=
  if h : (univ \ A).Nonempty then
    ((A.card : ℝ))⁻¹ * ∑ i ∈ A, H (X i n) - (univ \ A).sup' h (fun j => H (X j n))
  else 0

theorem Wpot_eq {H : ℤ → ℝ} {A : Finset ι} (hAc : (univ \ A).Nonempty) (n : ℕ) :
    Wpot X H A n = ((A.card : ℝ))⁻¹ * ∑ i ∈ A, H (X i n)
      - (univ \ A).sup' hAc (fun j => H (X j n)) := by
  rw [Wpot, dif_pos hAc]

/-- **`W ≥ gap` for the fixed potential.**  The block gap is dominated by the group potential,
which is `LeaderDescent.gapAt_le_potential_gap` restated for `Wpot`. -/
theorem Wpot_gap {H : ℤ → ℝ} (hH : Monotone H)
    (hslope : ∀ x y : ℤ, x ≤ y → ((y : ℝ) - (x : ℝ)) ≤ H y - H x)
    {A : Finset ι} (hA : A.Nonempty) (hAc : (univ \ A).Nonempty) {n : ℕ}
    (hlead : Leading (fun i => X i n) A) :
    ((gapAt (fun i => X i n) A : ℤ) : ℝ) ≤ Wpot X H A n := by
  rw [Wpot_eq X hAc n]
  exact gapAt_le_potential_gap X hH hslope hA hAc n
    (fun i hi j hj => hlead i hi j hj)

/-- **`(diam)` with a single residual.**  For a fixed potential `H` that is nondecreasing, whose
increments dominate the identity (`hslope`, as for `SepGroup.HZ` with `1/2 ≤ w ≤ 1`) and are
dominated above by `K` times the position difference (`hcmp`), the paper's `(diam)` follows from

* the telescoped `(Wdrift)` at separated leading blocks, `W_n ≤ W_s + o(n)` at the reset time `s`
  (this is what `WdriftJoint.telescope_of_sep` plus the `Q^{A,A^c}` martingale strong law supply),
* the deficit estimate `(prelim)` and eventual nonnegativity (transience).

Both the potential-to-gap bridge `W ≥ gap` and the positional comparison
`W_s ≤ K (max_A X_s - max_{A^c} X_s) + o(n)` are proved here, not assumed. -/
theorem spread_div_tendsto_zero_of_potential_telescope {K : ℝ} (hK : 0 ≤ K) {H : ℤ → ℝ}
    (hH : Monotone H)
    (hslope : ∀ x y : ℤ, x ≤ y → ((y : ℝ) - (x : ℝ)) ≤ H y - H x)
    (hcmp : ∀ x y : ℤ, x ≤ y → H y - H x ≤ K * ((y : ℝ) - (x : ℝ)))
    (htel : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset ι) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty),
        Leading (fun i => X i n) A → SepMax X A n →
        Wpot X H A n ≤ Wpot X H A (resetTime X A n) + ε * (n : ℝ))
    (hX : UnitStep X) (h0 : ∀ i, X i 0 = 0)
    (hdef : ∀ ε > 0, ∀ᶠ t : ℕ in atTop, ((deficit X t : ℤ) : ℝ) ≤ ε * (t : ℝ))
    (hpos : ∀ᶠ t : ℕ in atTop, ∀ i, 0 ≤ X i t) :
    Tendsto (fun n => ((spreadZ X n : ℤ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  refine spread_div_tendsto_zero_of_positional X hK (Wpot X H) ?_ ?_ ?_ hX h0 hdef hpos
  · intro ε hε
    filter_upwards with n A hA hAc hlead hmax
    have h := Wpot_gap X hH hslope hA hAc (n := n) hlead
    have h2 : (0:ℝ) ≤ ε * (n : ℝ) := by positivity
    linarith
  · exact htel
  · intro ε hε
    filter_upwards with n A hA hAc hlead hmax
    have hsle : resetTime X A n ≤ n := resetTime_minimal X A n (fun t h1 h2 => by
      have htn : t = n := le_antisymm h2 h1
      rw [htn]
      exact hmax)
    have hlead_s : Leading (fun i => X i (resetTime X A n)) A :=
      leading_of_sepGap X (resetTime_spec X A n (resetTime X A n) le_rfl hsle).2
    have h1 := potential_le_max_sub_max X hH (K := K) (η := 0)
      (fun x y hxy => by simpa using hcmp x y hxy) hA hAc (resetTime X A n)
      (fun i hi j hj => hlead_s i hi j hj)
    rw [Wpot_eq X hAc]
    have h2 : (0:ℝ) ≤ ε * (n:ℝ) := by positivity
    linarith

end FixedPotential

end NestedLeaderPot
