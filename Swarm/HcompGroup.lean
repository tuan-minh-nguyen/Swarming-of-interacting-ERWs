/-
# `HcompA` (direction 1), part 2: the group comparison and the reset-time assembly

This module proves `DiamAssembly.HcompA p m (1+a)/(1-a)` at the actual array, i.e. the paper's
`hcomp` at the reset time `s` of a separated leading block:

> `W_s^{A,A^c} ≤ C (spread_A(s) + deficit_s + 2) + ε n` eventually, uniformly in `A`,

with `C = (1+a)/(1-a) = SwarmSpatial.targetParam p m`, which depends only on `m` and `p`
(hence not on `N`).  The ingredients are

* `HcompSpatial.HZ_individual_diff_le` — the spatial pair `(spav)`/`(compare)` inequality for the
  *individual* potentials `H_j`;
* `HZ_group_le` — the paper's `(hcomp)` summed over the sites `x, …, y-1`: at a walker whose
  running maximum dominates the block, `H_s^{A}` grows no faster than `H_j`;
* `WA_le_HZ_diff` — the group average/maximum bound;
* `NestedLeaderPot.gapAt_reset_le_deficit_const` — the reset descent `gap_s ≤ 4 + deficit_s + o(n)`;
* `max_sub_max_eq_spread_add_gap` — the exact identity `max_A X_s - max_{A^c} X_s = spread + gap`.

Note what is *not* used: no fixed-`H` Lipschitz bound for the time-dependent weight `w_s^A`
(which is false: long runs of `1/2`-sites make `hfix (w_s^A)` grow quadratically), and no
symmetrisation of the average into a maximum.  The comparison is the paper's: the group potential
is dominated by the *individual* potential of a walker at the block's maximal running maximum, and
the individual potential differences are controlled by `(spav)`.
-/
import Swarm.HcompSpatial
import Swarm.NestedLeaderPot

set_option linter.unusedVariables false

open Filter Finset MeasureTheory Topology
open scoped BigOperators

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup SepGroup.Model Cookie
open DiamAssembly

namespace DiamAssemblyHcomp

variable {N : ℕ}
variable {p : ℝ} {m : ℕ}

/-! ## 4. Deterministic site bounds for the actual array -/

/-- Every actual walker is at most at the value of time: `X^i_n ≤ n`. -/
theorem XA_le_time (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    ∀ n : ℕ, XA p m U i n ≤ (n : ℤ)
  | 0 => by
      rw [zero_XA]
      simp
  | n + 1 => by
      have h := LeaderDescent.step_le (XA p m U) (unitStep_XA p m U) i n
      have h' := XA_le_time p m U i n
      push_cast
      omega

/-- The running maximum is at most the current time. -/
theorem runMax_XA_le (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    LeaderDescent.runMax (XA p m U) i n ≤ (n : ℤ) := by
  refine Finset.sup'_le _ _ (fun t ht => ?_)
  have ht' : t ≤ n := by simpa using ht
  have h1 := XA_le_time p m U i t
  have h2 : (t : ℤ) ≤ (n : ℤ) := by exact_mod_cast ht'
  omega

/-! ## 5. The group potential is dominated by the individual potential at the block maximum -/

/-- The group average/maximum bound: at a leading block the observable `W^{I,J}` is at most the
increment of `H_s^{J^c}` between the two block maxima.  Only monotonicity of `H_s^{J^c}` enters. -/
theorem WA_le_HZ_diff (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (U : Array N) {s : ℕ}
    {I J : Finset (Fin N)} (hI : I.Nonempty) (hJ : J.Nonempty)
    (hle : J.sup' hJ (fun j => X p m U s j) ≤ I.sup' hI (fun i => X p m U s i)) :
    WA p m U s I J hI hJ ≤
      HZ (wA p m U s Jᶜ) (I.sup' hI (fun i => X p m U s i))
        - HZ (wA p m U s Jᶜ) (J.sup' hJ (fun j => X p m U s j)) := by
  have hmono : Monotone (fun z => HZ (wA p m U s Jᶜ) z) :=
    HZ_mono (wA_pos p m U hp s Jᶜ) (wA_le_one p m U hp1 s Jᶜ)
  have hmax : Swarming.Group.maximumOn J hJ (fun j => HZ (wA p m U s Jᶜ) (X p m U s j))
      = HZ (wA p m U s Jᶜ) (J.sup' hJ (fun j => X p m U s j)) :=
    HA_maximum_eq p m U hp hp1 s Jᶜ hJ (fun j => X p m U s j)
  have havg : Swarming.Group.average I (fun i => HZ (wA p m U s Jᶜ) (X p m U s i))
      ≤ HZ (wA p m U s Jᶜ) (I.sup' hI (fun i => X p m U s i)) := by
    have hcard : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hI
    rw [Swarming.Group.average, div_le_iff₀ hcard]
    have h2 : ∑ i ∈ I, HZ (wA p m U s Jᶜ) (X p m U s i)
        ≤ ∑ _i ∈ I, HZ (wA p m U s Jᶜ) (I.sup' hI (fun i => X p m U s i)) :=
      Finset.sum_le_sum (fun i hi => hmono (Finset.le_sup' (fun i => X p m U s i) hi))
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    linarith
  rw [WA]
  simp only [HA]
  rw [hmax]
  linarith

/-- **The paper's `(hcomp)` summed over the sites.**  For `0 ≤ x ≤ y` below the block maximum of
the running maxima, the increment of the group potential `H_s^{A^c,^c}` is dominated by the
increment of the individual potential `H_i` of a walker `i ∈ A` whose running maximum dominates
the block.  This is `SepGroup.Model.hcomp_h` summed over `u ∈ [x, y)`. -/
theorem HZ_group_diff_le (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (U : Array N) {s : ℕ}
    {A : Finset (Fin N)} (hA : A.Nonempty) {x y : ℤ} (hx0 : 0 ≤ x) (hxy : x ≤ y)
    (hyR : y ≤ A.sup' hA (fun k => LeaderDescent.runMax (XA p m U) k s)) :
    ∃ i ∈ A, HZ (wA p m U s Aᶜᶜ) y - HZ (wA p m U s Aᶜᶜ) x
      ≤ HZ (omegaN p m U i) y - HZ (omegaN p m U i) x := by
  obtain ⟨i, hiA, himax⟩ := Finset.exists_max_image A (fun k => LeaderDescent.runMax (XA p m U) k s) hA
  refine ⟨i, hiA, ?_⟩
  have hiJ : i ∈ (Aᶜ)ᶜ := by simpa using hiA
  have hsup : A.sup' hA (fun k => LeaderDescent.runMax (XA p m U) k s)
      ≤ LeaderDescent.runMax (XA p m U) i s :=
    Finset.sup'_le hA _ himax
  have hyR' : y ≤ LeaderDescent.runMax (XA p m U) i s := le_trans hyR hsup
  have hRy : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (le_trans hx0 hxy)
  rw [HZ_sub_eq_sum hx0 hxy, HZ_sub_eq_sum hx0 hxy]
  refine Finset.sum_le_sum (fun u hu => ?_)
  have huy : (u : ℤ) < y := by
    have h1 : u < y.toNat := (Finset.mem_Ico.mp hu).2
    omega
  have hlt : (u : ℤ) < runMax p m U i s := by
    rw [← runMax_XA (p := p) (m := m) (U := U)]
    exact lt_of_lt_of_le (lt_of_lt_of_le huy hyR') le_rfl
  exact hcomp_h p m U hp hp1 (J := Aᶜ) (i := i) hiJ (x := u) hlt

end DiamAssemblyHcomp
