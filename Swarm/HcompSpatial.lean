/-
# `HcompA` (direction 1), part 1: the actual spatial comparison at the array

This module supplies the *positional comparison* `(compare)` of the paper
(`main_1d_revised.tex`, proof of `(diam)`) at the actual interacting array:

> for every walker `j`, `0 ≤ x ≤ y ≤ n` implies
> `H_j(y) - H_j(x) ≤ c (y - x) + o(n)`, with `c = (1+a)/(1-a)` depending only on `m,p`,

together with the group-level consequence that replaces the invalid fixed-`H` Lipschitz
step: at a site `i` of the leading block whose running maximum dominates the block,

> `H_s^{A}(y) - H_s^{A}(x) ≤ H_i(y) - H_i(x)` for `0 ≤ x ≤ y ≤ max_{k∈A} M_s^k`,

which is the paper's `(hcomp)` summed over the sites `x, …, y-1`.

Nothing here assumes anything beyond `1/2 < p < 1` and `2 ≤ m` (the range in which the
accepted spatial-average strong law `SwarmSpatial.spav_uniform` is unconditional).
-/
import Swarm.DiamAssemblyMain
import Swarm.S12
import Swarm.RawLogRatio

set_option linter.style.haveILetI false

open Filter Finset MeasureTheory Topology
open scoped BigOperators

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup SepGroup.Model Cookie

namespace DiamAssemblyHcomp

variable {N : ℕ}

/-! ## 1. The uniform spatial-average law at the actual array

`SwarmSpatial.spav_uniform` is the paper's `(spav)` first display in the *running-maximum*
form: almost surely, for every `ε > 0` and all large `n`, every prefix sum `t ≤ n` is within
`ε n` of `t c`.  We pull it back along the measure-preserving map that reads a walker's site
marks off the actual uniform array, and intersect the finitely many walkers. -/

/-- **`(spav)` uniform in `t ≤ n`, simultaneously for every actual walker.** -/
theorem spav_uniform_array (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ j : Fin N, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, t ≤ n →
      |∑ k ∈ Finset.range t, SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) k
          - (t : ℝ) * SwarmSpatial.targetParam p m| ≤ ε * (n : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ (1 - p) ^ (m - 1) := by positivity
  have hq1 : (1 - p) ^ (m - 1) ≤ 1 := by
    have h0 : 0 ≤ 1 - p := by linarith
    have h1 : 1 - p ≤ 1 := by linarith
    exact pow_le_one₀ h0 h1
  haveI : IsProbabilityMeasure (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1))) :=
    SwarmMarks.isProbabilityMeasure_boolMeasure hq0 hq1
  have hsingle := SwarmSpatial.spav_uniform (p := p) hp1 hp2 (m := m) hm
  have hall : ∀ᵐ ω ∂(SwarmMarks.markMeasureN N (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1)))),
      ∀ j : Fin N, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, t ≤ n →
        |∑ k ∈ Finset.range t, SwarmMarks.hof p (ω j) k
            - (t : ℝ) * SwarmSpatial.targetParam p m| ≤ ε * (n : ℝ) :=
    (MeasureTheory.ae_all_iff (μ :=
        SwarmMarks.markMeasureN N (SwarmMarks.boolMeasure ((1 - p) ^ (m - 1))))
      (ι := Fin N)).mpr (fun j => SwarmMarks.markMeasureN_ae N j hsingle)
  exact (SwarmLogRatio.measurePreserving_siteMarksN (N := N) hp0 hp2 m).quasiMeasurePreserving.ae
    hall

/-- The running-maximum form of `(spav)` in the quantifier order used below:
`∀ ε > 0, ∀ᶠ n, ∀ j, ∀ t ≤ n`. -/
theorem spav_uniform_array' (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ j : Fin N, ∀ t : ℕ, t ≤ n →
      |∑ k ∈ Finset.range t, SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) k
          - (t : ℝ) * SwarmSpatial.targetParam p m| ≤ ε * (n : ℝ) := by
  filter_upwards [spav_uniform_array (N := N) hp1 hp2 hm] with U hU ε hε
  exact Filter.eventually_all.mpr (fun j => hU j ε hε)

/-- The two ratio functions of the campaign agree on `Bool`. -/
theorem rhoOf_eq (p : ℝ) (b : Bool) :
    SwarmSpatial.rhoOf p b = SwarmMarks.rhoOf p b := by
  cases b
  · rw [SwarmSpatial.rhoOf_false, SwarmMarks.rhoOf_false]
  · rw [SwarmSpatial.rhoOf_true, SwarmMarks.rhoOf_true]

/-! ## 2. The individual potential `H_j` at nonnegative sites is the mark recursion `hof`

`hfix` is defined by `hfix w n = (1 + (1 - w n) hfix w (n-1))/w n`, while `hof` is defined by
`hof(n) = hstep (ω n) (hof(n-1))` with `hstep p b h = 1 + ρ_b (1+h)`, `ρ_b = (1-w_b)/w_b`.
The two recursions coincide because `1/w = 1 + (1-w)/w`. -/

/-- The `hfix` recursion written with the ratio `(1-w)/w`, i.e. the paper's `(hrec)`. -/
theorem hfix_eq_rho (w : ℕ → ℝ) (n : ℕ) (hw : w n ≠ 0) :
    hfix w n = 1 + ((1 - w n) / w n) * (1 + hprev w n) := by
  rw [hfix_eq]
  field_simp
  ring

/-- **`H_j` on nonnegative sites is the mark recursion of the actual site marks.** -/
theorem hfix_omegaN_eq_hof {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (U : Array N) (j : Fin N) :
    ∀ n : ℕ, hfix (omegaN p m U j) n = SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) n
  | 0 => by
      have hp0 : p ≠ 0 := by linarith
      have hw : omegaN p m U j 0 ≠ 0 :=
        ne_of_gt (omegaAt_pos p m U hp j (0 : ℤ))
      rw [hfix_eq_rho _ _ hw, hprev_zero, SwarmMarks.hof_zero,
        SwarmMarks.hstep_eq_rho hp0]
      have hrho : (1 - omegaN p m U j 0) / omegaN p m U j 0
          = SwarmMarks.rhoOf p (SwarmLogRatio.siteMarksN p m U j 0) := by
        rw [← rhoOf_eq]
        simpa [omegaN, SwarmLogRatio.siteMarksN] using SwarmLogRatio.rho_omegaAt p m U j 0
      rw [hrho]
  | n + 1 => by
      have hp0 : p ≠ 0 := by linarith
      have hw : omegaN p m U j (n + 1) ≠ 0 :=
        ne_of_gt (omegaAt_pos p m U hp j ((n + 1 : ℕ) : ℤ))
      rw [hfix_eq_rho _ _ hw, hprev_succ, hfix_omegaN_eq_hof hp hp1 m U j n,
        SwarmMarks.hof_succ, SwarmMarks.hstep_eq_rho hp0]
      have hrho : (1 - omegaN p m U j (n + 1)) / omegaN p m U j (n + 1)
          = SwarmMarks.rhoOf p (SwarmLogRatio.siteMarksN p m U j (n + 1)) := by
        rw [← rhoOf_eq]
        simpa [omegaN, SwarmLogRatio.siteMarksN] using SwarmLogRatio.rho_omegaAt p m U j (n + 1)
      rw [hrho]

/-- `Hfix` of the individual potential, as the partial sums of the mark recursion. -/
theorem Hfix_omegaN_eq_sum {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (U : Array N) (j : Fin N) (t : ℕ) :
    Hfix (omegaN p m U j) t
      = ∑ k ∈ Finset.range t, SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) k := by
  unfold Hfix
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact hfix_omegaN_eq_hof hp hp1 m U j k

/-! ## 3. Differences of `HZ` along the site axis -/

/-- `Hfix w b - Hfix w a` is the sum of `hfix w` over the sites `a, …, b-1`. -/
theorem Hfix_sub {w : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) :
    Hfix w b - Hfix w a = ∑ u ∈ Finset.Ico a b, hfix w u := by
  have h := Finset.sum_Ico_eq_sub (f := fun u => hfix w u) hab
  rw [h]
  rfl

/-- **The site difference of `H_j`.**  For `0 ≤ x ≤ y` the increment of the individual
potential between the two sites is the sum of `h_j` over `[x, y)`. -/
theorem HZ_sub_eq_sum {w : ℕ → ℝ} {x y : ℤ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    HZ w y - HZ w x = ∑ u ∈ Finset.Ico x.toNat y.toNat, hfix w u := by
  rw [HZ_nonneg hx, HZ_nonneg (le_trans hx hxy)]
  exact Hfix_sub (Int.toNat_le_toNat hxy)

/-- **The individual comparison `(compare)`, spatial part.**  If the running-maximum form of
`(spav)` holds with error `ε n`, then for every pair of sites `0 ≤ x ≤ y ≤ n` the individual
potential `H_j` grows by at most `c (y-x) + 2 ε n`. -/
theorem HZ_individual_diff_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    {m : ℕ} {c ε : ℝ} {n : ℕ} (U : Array N) (j : Fin N)
    (hspav : ∀ t : ℕ, t ≤ n →
      |∑ k ∈ Finset.range t, SwarmMarks.hof p (SwarmLogRatio.siteMarksN p m U j) k
          - (t : ℝ) * c| ≤ ε * (n : ℝ))
    {x y : ℤ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyn : y.toNat ≤ n) :
    HZ (omegaN p m U j) y - HZ (omegaN p m U j) x
      ≤ c * ((y : ℝ) - (x : ℝ)) + 2 * ε * (n : ℝ) := by
  have h0y : 0 ≤ y := le_trans hx hxy
  have hyR : ((y.toNat : ℕ) : ℝ) = (y : ℝ) := by
    have h : (y.toNat : ℤ) = y := Int.toNat_of_nonneg h0y
    calc ((y.toNat : ℕ) : ℝ) = ((y.toNat : ℤ) : ℝ) := by push_cast; ring
      _ = (y : ℝ) := by rw [h]
  have hxR : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
    have h : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx
    calc ((x.toNat : ℕ) : ℝ) = ((x.toNat : ℤ) : ℝ) := by push_cast; ring
      _ = (x : ℝ) := by rw [h]
  have h1 := hspav y.toNat hyn
  have h2 := hspav x.toNat (le_trans (Int.toNat_le_toNat hxy) hyn)
  simp only [← Hfix_omegaN_eq_sum hp hp1 m U j] at h1 h2
  rw [hyR] at h1
  rw [hxR] at h2
  have h1' : Hfix (omegaN p m U j) y.toNat ≤ (y : ℝ) * c + ε * (n : ℝ) := by
    rw [abs_le] at h1; linarith [h1.2]
  have h2' : (x : ℝ) * c - ε * (n : ℝ) ≤ Hfix (omegaN p m U j) x.toNat := by
    rw [abs_le] at h2; linarith [h2.1]
  have hsub := HZ_sub_eq_sum (w := omegaN p m U j) hx hxy
  rw [hsub, ← Hfix_sub (Int.toNat_le_toNat hxy)]
  nlinarith [h1', h2']

/-! ## 3'. The paper's `(compare)`, spatial half, as a standalone interface

The two statements below are the reusable form of the *actual* spatial comparison: the first is
the paper's `max_{j, 0 ≤ x ≤ n} |H_j(x) - c x| = o(n)` with the running-maximum uniformity, the
second is its difference form `H_j(y) - H_j(x) ≤ c (y-x) + o(n)`.  They are what any further
consumer of `(compare)` should use; `HcompA` above is one such consumer.
-/

/-- **`(spav)` for the individual potential `H_j` of the interacting array**, uniform in the site
and the walker: `|H_j(x) - c x| ≤ ε n` for all `x ≤ n` and all `j`. -/
theorem compare_absolute_array (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ j : Fin N, ∀ t : ℕ, t ≤ n →
      |Hfix (SepGroup.Model.omegaN p m U j) t
          - (t : ℝ) * SwarmSpatial.targetParam p m| ≤ ε * (n : ℝ) := by
  have hp : (1 / 2 : ℝ) ≤ p := le_of_lt hp1
  have hp1' : p ≤ 1 := le_of_lt hp2
  filter_upwards [spav_uniform_array' (N := N) hp1 hp2 hm] with U hU ε hε
  filter_upwards [hU ε hε] with n hn j t ht
  rw [Hfix_omegaN_eq_sum hp hp1' m U j t]
  exact hn j t ht

/-- **The paper's `(compare)`, spatial half, in difference form.** -/
theorem compare_diff_array (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ j : Fin N,
      ∀ x y : ℤ, 0 ≤ x → x ≤ y → y.toNat ≤ n →
        HZ (SepGroup.Model.omegaN p m U j) y - HZ (SepGroup.Model.omegaN p m U j) x
          ≤ SwarmSpatial.targetParam p m * ((y : ℝ) - (x : ℝ)) + 2 * ε * (n : ℝ) := by
  have hp : (1 / 2 : ℝ) ≤ p := le_of_lt hp1
  have hp1' : p ≤ 1 := le_of_lt hp2
  filter_upwards [spav_uniform_array' (N := N) hp1 hp2 hm] with U hU ε hε
  filter_upwards [hU ε hε] with n hn j x y hx hxy hyn
  exact HZ_individual_diff_le hp hp1' (m := m) (c := SwarmSpatial.targetParam p m) (ε := ε)
    (n := n) U j (fun t ht => hn j t ht) hx hxy hyn

end DiamAssemblyHcomp
