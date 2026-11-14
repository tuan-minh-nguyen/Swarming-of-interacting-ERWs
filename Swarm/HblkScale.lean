/-
# The repaired scale reduction `PCtxR.of_eventual` is vacuous at the paper's constants

`ScaleRepairReduce.PCtxR.of_eventual` ("the paper's Borel–Cantelli step") produces the repaired
tightness interface `SwarmM4.PCtxR` from `hterm`, `hblk`, the almost-sure defect bound `hdef` and
four hypotheses on the dyadic scale `g : ℕ → ℕ`:

  `hmono  : ∀ r r', r ≤ r' → g r ≤ g r'`
  `hbound : ∀ r, 2 C₀ ≤ r → 2 C₀ * 2 ^ (g r) ≤ r`
  `hgpow  : ∀ a, a ≤ g (2 ^ (a + 1))`
  `hsum   : ∑' r, p (2 ^ (g r)) ≠ ⊤`

**`hbound` and `hgpow` are jointly unsatisfiable as soon as `C₀ ≥ 2`** (`scale_hypotheses_incompatible`
below): at `r = 2 ^ (a+1)` they force `2 C₀ * 2 ^ a ≤ 2 ^ (a+1)`, i.e. `C₀ ≤ 1`.  Since the
tightness route fixes `C₀ = B + T + 1` with `T = ⌈2B/κ⌉₊ + 2 ≥ 3`, every instance of
`PCtxR.of_eventual` and of `tightness_of_eventual` used at the paper's constants is *vacuous*:
the reduction proves nothing about the actual model.

The defect is not the Borel–Cantelli argument, only the auxiliary power condition: `hgpow` pins the
scale at the index `2 ^ (a+1)`, whereas the proof only needs the level `a` to be below the scale at
the *start index* `R a ω`, which may be far larger than `2 ^ (a+1)`.  The repair used below is to
ask, for an explicit `k` with `2 C₀ ≤ 2 ^ (1+k)`,

  `hpowy : ∀ a r, 2 ^ (a + 1 + k) ≤ r → a ≤ g r`,

which is compatible with `hbound` and is satisfied by the concrete `g r = r.log2 - k` for every
`k ≥ log2 (2 C₀)`.  `PCtxR.of_eventual_pow` is the corrected constructor and
`tightness_of_eventual_pow` its tightness corollary.

Main declarations.

* `scale_hypotheses_incompatible` — `C₀ ≥ 2` makes `hbound ∧ hgpow` contradictory (no measure
  theory, no `Good`, no process: purely the arithmetic of the scale).
* `PCtxR.of_eventual_pow` — the corrected constructor with the satisfiable power condition.
* `tightness_of_eventual_pow` — the corresponding tightness conclusion.

No proof holes.  Nothing here proves `hblk`, `hdef`, invariant measures, regeneration or the main
theorem; the point is that the *reduction* is no longer vacuous, so `hblk` really is the residual
input.
-/
import Swarm.ScaleRepairReduce

open MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped ENNReal BigOperators

namespace HblkScale

open SwarmM4

/-! ### The scale arithmetic is contradictory -/

/-- **`hbound ∧ hgpow` force `C₀ ≤ 1`.**  Consequently every call of
`ScaleRepairReduce.PCtxR.of_eventual` (or of `tightness_of_eventual`) with `C₀ ≥ 2` — in particular
the paper's `C₀ = B + T + 1` — has unsatisfiable hypotheses. -/
theorem scale_hypotheses_incompatible {C₀ : ℕ} {g : ℕ → ℕ}
    (hbound : ∀ r, 2 * C₀ ≤ r → 2 * C₀ * 2 ^ g r ≤ r)
    (hgpow : ∀ a, a ≤ g (2 ^ (a + 1))) :
    C₀ ≤ 1 := by
  -- choose `a` with `2 C₀ ≤ 2 ^ (a+1)`
  have hpow : ∀ n : ℕ, 2 * n ≤ 2 ^ (n + 1) := by
    intro n
    induction n with
    | zero => norm_num
    | succ m ih =>
        have h2 : (2 : ℕ) ≤ 2 ^ (m + 1) := by
          have h1 : (2 : ℕ) = 2 ^ 1 := by norm_num
          rw [h1]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 : 2 * (m + 1) = 2 * m + 2 := by ring
        rw [show m + 1 + 1 = m + 1 + 1 from rfl, pow_succ, h3]
        nlinarith [ih, h2]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, 2 * C₀ ≤ 2 ^ (a + 1) := ⟨C₀, hpow C₀⟩
  have hb := hbound (2 ^ (a + 1)) ha
  have hp := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (hgpow a)
  -- `2 C₀ * 2 ^ a ≤ 2 C₀ * 2 ^ (g (2^(a+1))) ≤ 2^(a+1) = 2 * 2^a`
  have hsplit : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring
  have hchain : 2 * C₀ * 2 ^ a ≤ 2 * 2 ^ a := by
    calc 2 * C₀ * 2 ^ a ≤ 2 * C₀ * 2 ^ g (2 ^ (a + 1)) :=
          Nat.mul_le_mul_left (2 * C₀) hp
      _ ≤ 2 ^ (a + 1) := hb
      _ = 2 * 2 ^ a := hsplit
  have hpos : 0 < 2 ^ a := Nat.pos_of_ne_zero (pow_ne_zero a (by norm_num))
  have := Nat.le_of_mul_le_mul_right hchain hpos
  omega

/-! ### A concrete scale that satisfies the corrected hypotheses -/

/-- The concrete dyadic scale `g r = r.log2 - k`: the exponent of the largest power of two
at most `r / 2 ^ k`. -/
def g (k r : ℕ) : ℕ := r.log2 - k

theorem g_mono (k : ℕ) {r r' : ℕ} (h : r ≤ r') : g k r ≤ g k r' := by
  refine Nat.sub_le_sub_right ?_ k
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0; simp
  · have hr' : r' ≠ 0 := by omega
    exact (Nat.le_log2 hr').2 (le_trans ((Nat.le_log2 (by omega : r ≠ 0)).1 le_rfl) h)

theorem g_bound (k C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hk : 2 * C₀ ≤ 2 ^ k) {r : ℕ} (hr : 2 * C₀ ≤ r) :
    2 * C₀ * 2 ^ g k r ≤ r := by
  have hr0 : r ≠ 0 := by omega
  rcases Nat.lt_or_ge r.log2 k with hlt | hge
  · have hg0 : g k r = 0 := by
      rw [g, Nat.sub_eq_zero_of_le (le_of_lt hlt)]
    rw [hg0, pow_zero, Nat.mul_one]
    exact hr
  · have hsplit : 2 ^ g k r * 2 ^ k = 2 ^ r.log2 := by
      rw [g, ← pow_add, Nat.sub_add_cancel hge]
    have hlog : 2 ^ r.log2 ≤ r := (Nat.le_log2 hr0).1 le_rfl
    calc 2 * C₀ * 2 ^ g k r ≤ 2 ^ k * 2 ^ g k r := Nat.mul_le_mul_right _ hk
      _ = 2 ^ g k r * 2 ^ k := Nat.mul_comm _ _
      _ = 2 ^ r.log2 := hsplit
      _ ≤ r := hlog

theorem g_pow_le (k : ℕ) {a r : ℕ} (h : 2 ^ (a + 1 + k) ≤ r) : a ≤ g k r := by
  have hr0 : r ≠ 0 := by
    have : 0 < 2 ^ (a + 1 + k) := Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
    omega
  have hlog : a + 1 + k ≤ r.log2 := (Nat.le_log2 hr0).2 h
  have hkr : k ≤ r.log2 := by omega
  have : g k r = r.log2 - k := rfl
  omega

/-! ### The corrected reduction -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The corrected Borel–Cantelli reduction of the scale hypotheses.**

Identical to `ScaleRepairReduce.PCtxR.of_eventual` except that the unsatisfiable power condition
`∀ a, a ≤ g (2 ^ (a+1))` is replaced by
`∀ a r, 2 ^ (a + 1 + k) ≤ r → a ≤ g r`, which is compatible with the scale bound
`2 C₀ * 2 ^ (g r) ≤ r` (take `2 ^ k ≥ 2 C₀` and `g r = r.log2 - k`). -/
noncomputable def PCtxR.of_eventual_pow
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B C₀ : ℕ) (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀)
    (d : Ω → ℕ → ℕ) (Good : Ω → ℕ → ℕ → Prop) (p : ℕ → ℝ≥0∞) (g : ℕ → ℕ)
    (k : ℕ)
    (hd : Measurable d) (hG : ∀ r ℓ, MeasurableSet {ω | Good ω r ℓ})
    (hS : ∀ ω r L, Good ω r L → d ω r ≤ L →
      d ω (r + B * L) ≤ L / 2 ∧ ∀ u, r ≤ u → u ≤ r + B * L → d ω u ≤ C₀ * L)
    (hterm : ∀ r L, 1 ≤ L → ∀ᵐ ω ∂μ, ∃ j, Good ω r (2 ^ j * L))
    (hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      μ ({ω | d ω r ≤ ℓ} ∩ {ω | ¬ Good ω r ℓ}) ≤ p ℓ)
    (hmono : ∀ r r', r ≤ r' → g r ≤ g r')
    (hbound : ∀ r, 2 * C₀ ≤ r → 2 * C₀ * 2 ^ g r ≤ r)
    (hpowy : ∀ a r : ℕ, 2 ^ (a + 1 + k) ≤ r → a ≤ g r)
    (hsum : (∑' r : ℕ, p (2 ^ g r)) ≠ ⊤)
    (hdef : ∀ᵐ ω ∂μ, ∀ᶠ r in atTop, d ω r ≤ 2 ^ g r) :
    PCtxR Ω := by
  classical
  have hex₀ : ∃ R : Ω → ℕ, Measurable R ∧ ∀ᵐ ω ∂μ, ∀ n, R ω ≤ n → d ω n ≤ 2 ^ g n :=
    exists_measurable_threshold (P := fun ω n => d ω n ≤ 2 ^ g n) hdef
      (fun r => (measurable_pi_apply r).comp hd measurableSet_Iic)
  have hex₁ : ∃ R : Ω → ℕ, Measurable R ∧ ∀ᵐ ω ∂μ, ∀ n, R ω ≤ n → Good ω n (2 ^ g n) :=
    exists_measurable_threshold (P := fun ω n => Good ω n (2 ^ g n))
      (ae_eventually_good_of_blk hd hG hblk hbound hsum hdef) (fun r => hG r (2 ^ g r))
  set R₀ : Ω → ℕ := Classical.choose hex₀ with hR₀def
  have hR₀meas : Measurable R₀ := (Classical.choose_spec hex₀).1
  have hR₀ : ∀ᵐ ω ∂μ, ∀ n, R₀ ω ≤ n → d ω n ≤ 2 ^ g n := (Classical.choose_spec hex₀).2
  set R₁ : Ω → ℕ := Classical.choose hex₁ with hR₁def
  have hR₁meas : Measurable R₁ := (Classical.choose_spec hex₁).1
  have hR₁ : ∀ᵐ ω ∂μ, ∀ n, R₁ ω ≤ n → Good ω n (2 ^ g n) := (Classical.choose_spec hex₁).2
  refine
    { μ := μ, hprob := inferInstance, B := B, C₀ := C₀, d := d, Good := Good
      R := fun a ω => max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1 + k)))
      p := p, g := g, hB := hB, hC₀ := hC₀, hd := hd
      hdR := ?_, hg := hG, hRmeas := ?_, hRge := ?_, hS := hS, hterm := hterm, hblk := hblk
      hscale_mono := hmono, hscale_bound := hbound, hscale_good := ?_, hstart := ?_ }
  · intro a
    exact measurable_apply_comp hd (by
      exact ((hR₀meas.max hR₁meas).max (measurable_const.max measurable_const)))
  · intro a
    exact ((hR₀meas.max hR₁meas).max (measurable_const.max measurable_const))
  · intro a ω
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · intro a
    filter_upwards [hR₁] with ω hω r hr
    exact hω r (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr)
  · intro a
    filter_upwards [hR₀, hR₁] with ω h₀ h₁
    have hle₀ : R₀ ω ≤ max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1 + k))) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hpow : 2 ^ (a + 1 + k) ≤ max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1 + k))) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hd0 : d ω (max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1 + k)))) ≤ 2 ^ g _ := h₀ _ hle₀
    have hga : a ≤ g (max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1 + k)))) :=
      hpowy a _ hpow
    have h2a : 2 ^ a ≤ 2 ^ g (max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1 + k)))) :=
      Nat.pow_le_pow_right (by norm_num) hga
    exact max_le h2a hd0

/-- **Tightness from the corrected, satisfiable scale hypotheses.** -/
theorem tightness_of_eventual_pow
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B C₀ : ℕ) (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀)
    (d : Ω → ℕ → ℕ) (Good : Ω → ℕ → ℕ → Prop) (p : ℕ → ℝ≥0∞) (g : ℕ → ℕ) (k : ℕ)
    (hd : Measurable d) (hG : ∀ r ℓ, MeasurableSet {ω | Good ω r ℓ})
    (hS : ∀ ω r L, Good ω r L → d ω r ≤ L →
      d ω (r + B * L) ≤ L / 2 ∧ ∀ u, r ≤ u → u ≤ r + B * L → d ω u ≤ C₀ * L)
    (hterm : ∀ r L, 1 ≤ L → ∀ᵐ ω ∂μ, ∃ j, Good ω r (2 ^ j * L))
    (hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      μ ({ω | d ω r ≤ ℓ} ∩ {ω | ¬ Good ω r ℓ}) ≤ p ℓ)
    (hmono : ∀ r r', r ≤ r' → g r ≤ g r')
    (hbound : ∀ r, 2 * C₀ ≤ r → 2 * C₀ * 2 ^ g r ≤ r)
    (hpowy : ∀ a r : ℕ, 2 ^ (a + 1 + k) ≤ r → a ≤ g r)
    (hsum₂ : (∑' r : ℕ, p (2 ^ g r)) ≠ ⊤)
    (hdef : ∀ᵐ ω ∂μ, ∀ᶠ r in atTop, d ω r ≤ 2 ^ g r)
    (hcert : (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ) ≠ ⊤)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K' : ℕ, ∀ u : ℕ, μ {ω | K' < d ω u} ≤ ε := by
  classical
  let c : PCtxR Ω := PCtxR.of_eventual_pow μ B C₀ hB hC₀ d Good p g k hd hG hS hterm hblk hmono
    hbound hpowy hsum₂ hdef
  have hw : ∀ ℓ : ℕ, c.w ℓ = ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ := fun ℓ => rfl
  have hcert' : (∑' ℓ : ℕ, c.w ℓ) ≠ ⊤ := by
    have hEq : (∑' ℓ : ℕ, c.w ℓ) = ∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ := by
      simp only [hw]
    rw [hEq]
    exact hcert
  have hres := c.tightness hcert' ε hε
  simpa [c, PCtxR.of_eventual_pow] using hres

/-! ### Consistency of the corrected hypotheses -/

/-- **The corrected hypotheses are satisfiable at the paper's constants.**  For every `C₀ ≥ 1`
there is `k` with `2 C₀ ≤ 2 ^ (1 + k)`, and then the concrete scale `g r = r.log2 - k` satisfies
`hmono`, `hbound` and `hpowy` simultaneously.  (Contrast `scale_hypotheses_incompatible`: the
original `hgpow` cannot hold for any `C₀ ≥ 2`.) -/
theorem exists_compatible_scale (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    ∃ k : ℕ, 2 * C₀ ≤ 2 ^ k ∧
      (∀ r r' : ℕ, r ≤ r' → HblkScale.g k r ≤ HblkScale.g k r') ∧
      (∀ r : ℕ, 2 * C₀ ≤ r → 2 * C₀ * 2 ^ HblkScale.g k r ≤ r) ∧
      (∀ a r : ℕ, 2 ^ (a + 1 + k) ≤ r → a ≤ HblkScale.g k r) := by
  have hkey : ∀ n : ℕ, 1 ≤ n → 2 * n ≤ 2 ^ n := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm; norm_num
        · have ih' := ih (by omega)
          have h2 : (2 : ℕ) ≤ 2 ^ m := by
            calc (2 : ℕ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h3 : 2 * (m + 1) = 2 * m + 2 := by ring
          rw [pow_succ, h3]
          nlinarith [ih', h2]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * C₀ ≤ 2 ^ k := ⟨C₀, hkey C₀ hC₀⟩
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · intro r r' hr
    exact g_mono k hr
  · intro r hr
    exact g_bound k C₀ hC₀ hk hr
  · intro a r har
    exact g_pow_le k har

end HblkScale


