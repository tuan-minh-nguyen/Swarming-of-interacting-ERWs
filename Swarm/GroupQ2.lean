/-
The envelope on the paper's `(locmax)` event: the two truncated maxima `Efix` and `Esum` of
`GroupQ.lean` are bounded by the static objects `h_{i₀}` and `G_{i₀}` of the leader `i₀ ∈ I`,
through `(hcomp)`.
-/
import Swarm.GroupQ

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocGroupQ

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance

variable {N : ℕ}

theorem runMax_le_time (p : ℝ) (m n : ℕ) (i : Fin N) (U : Array N) :
    runMax p m U i n ≤ (n : ℤ) := by
  obtain ⟨t, ht, hte⟩ := exists_eq_runMax p m U i n
  have h3 := SwarmM3.abs_X_le p m U t i
  rw [abs_le] at h3
  have h4 : X p m U t i ≤ ((n : ℕ) : ℤ) := by
    have h5 : ((t : ℕ) : ℤ) ≤ ((n : ℕ) : ℤ) := by exact_mod_cast ht
    linarith [h3.2]
  rw [← hte]
  exact h4

theorem Rmax_le_n (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty) (U : Array N) :
    Rmax p m n K hK U ≤ n := by
  have hsup : K.sup' hK (fun k => runMax p m U k n) ≤ (n : ℤ) :=
    Finset.sup'_le hK _ (fun k _ => runMax_le_time p m n k U)
  have h1 : Rmax p m n K hK U = (K.sup' hK (fun k => runMax p m U k n)).toNat := rfl
  rw [h1]
  simpa using toNat_le_toNat hsup

/-- The leader's running maximum is at most the truncation site. -/
theorem toNat_runMax_le_xTop (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty)
    {i₀ : Fin N} (hi₀ : i₀ ∈ K) (U : Array N) :
    (runMax p m U i₀ n).toNat ≤ xTop p m n K hK U := by
  have h1 : (runMax p m U i₀ n).toNat ≤ n := by
    have h2 : ((runMax p m U i₀ n).toNat : ℤ) ≤ (n : ℤ) := by
      rw [Int.toNat_of_nonneg (runMax_nonneg_pos p m n i₀ U)]
      exact runMax_le_time p m n i₀ U
    exact_mod_cast h2
  have h2 : (runMax p m U i₀ n).toNat ≤ Rmax p m n K hK U + 1 := by
    have h3 := runMax_le_Rmax p m n K hK hi₀ U
    omega
  refine Nat.le_min.mpr ⟨?_, h2⟩
  omega

/-- If `i₀` maximises the running maximum over `K`, the truncation site is at most `R+1`. -/
theorem xTop_le_succ_of_max (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty)
    (U : Array N) {i₀ : Fin N} (hmax : Rmax p m n K hK U ≤ (runMax p m U i₀ n).toNat) :
    xTop p m n K hK U ≤ (runMax p m U i₀ n).toNat + 1 := by
  exact le_trans (Nat.min_le_right (n + 2) (Rmax p m n K hK U + 1)) (by omega)

/-- **`Efix` on `(locmax)`**: if the leader's static potential is at most `H` on the truncated
range, the actual predictable step envelope is at most `2H + 6`. -/
theorem Efix_le_of_locmax {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (U : Array N) {i₀ : Fin N} (hi₀K : i₀ ∈ K)
    (hi₀J : i₀ ∈ Jᶜ) (hmax : Rmax p m n K hK U ≤ (runMax p m U i₀ n).toNat)
    {H : ℝ} (hH1 : 1 ≤ H)
    (hH : ∀ u ≤ xTop p m n K hK U, hfix (omegaN p m U i₀) u ≤ H) :
    Efix p m n J K hK U ≤ 2 * H + 6 := by
  refine Finset.sup'_le _ _ fun u hu => ?_
  rw [Finset.mem_range] at hu
  by_cases hutop : u ≤ xTop p m n K hK U
  · rw [if_pos hutop]
    set R : ℕ := (runMax p m U i₀ n).toNat with hR
    have hRtop : R ≤ xTop p m n K hK U := toNat_runMax_le_xTop p m n K hK hi₀K U
    have htopR : xTop p m n K hK U ≤ R + 1 := xTop_le_succ_of_max p m n K hK U hmax
    have hRz : ((R : ℕ) : ℤ) = runMax p m U i₀ n :=
      Int.toNat_of_nonneg (runMax_nonneg_pos p m n i₀ U)
    have hR1 : hfix (wA p m U n Jᶜ) R ≤ H + 2 := by
      have h1 : hfix (wA p m U n Jᶜ) R ≤ hprev (omegaN p m U i₀) R + 2 :=
        hcomp_h_runMax (p := p) (m := m) (U := U) hp hp1 hi₀J
      have h2 : hprev (omegaN p m U i₀) R ≤ H := by
        rcases Nat.eq_zero_or_pos R with hR0 | hRpos
        · rw [hR0, hprev_zero]; exact hH1
        · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hRpos.ne'
          rw [hk, hprev_succ]
          exact hH k (by omega)
      linarith
    rcases lt_or_eq_of_le (show u ≤ R + 1 by omega) with hlt | heq
    · rcases lt_or_eq_of_le (show u ≤ R by omega) with hltR | heqR
      · have hz : (u : ℤ) < runMax p m U i₀ n := by
          rw [← hRz]
          exact_mod_cast hltR
        exact le_trans (hcomp_h (p := p) (m := m) (U := U) hp hp1 hi₀J hz)
          (le_trans (hH u hutop) (by linarith))
      · subst heqR
        linarith
    · subst heq
      have hw := wA_pos p m U hp n Jᶜ (R + 1)
      have hw1 := one_half_le_wA p m U hp n Jᶜ (R + 1)
      have hstep : hfix (wA p m U n Jᶜ) (R + 1)
          = (1 + (1 - wA p m U n Jᶜ (R + 1)) * hfix (wA p m U n Jᶜ) R)
            / wA p m U n Jᶜ (R + 1) := by
        rw [Cookie.hfix_eq, Cookie.hprev_succ]
      have hRnn : 0 ≤ hfix (wA p m U n Jᶜ) R :=
        le_trans zero_le_one (one_le_hfix _ (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) R)
      have hnum : 1 + (1 - wA p m U n Jᶜ (R + 1)) * hfix (wA p m U n Jᶜ) R
          ≤ 1 + hfix (wA p m U n Jᶜ) R := by
        have hle1 : wA p m U n Jᶜ (R + 1) ≤ 1 := wA_le_one p m U hp1 n Jᶜ (R + 1)
        have hle0 : 0 ≤ wA p m U n Jᶜ (R + 1) := le_of_lt hw
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - wA p m U n Jᶜ (R + 1)) hRnn]
      have hfin : (1 + (1 - wA p m U n Jᶜ (R + 1)) * hfix (wA p m U n Jᶜ) R)
            / wA p m U n Jᶜ (R + 1) ≤ 2 * (1 + hfix (wA p m U n Jᶜ) R) := by
        rw [div_le_iff₀ hw]
        nlinarith [hnum, hw, hw1, hRnn]
      rw [hstep]
      linarith
  · rw [if_neg hutop]
    linarith

end LocGroupQ
/-!
## 7. `Esum` on `(locmax)` and the predictable good event
-/
namespace LocGroupQ

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance

variable {N : ℕ}

/-- **`Esum` on `(locmax)`**: if the leader's static tail sum is at most `G` on the truncated
range, the predictable product sum is at most `2G`. -/
theorem Esum_le_of_locmax {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (U : Array N) {i₀ : Fin N} (hi₀K : i₀ ∈ K)
    (hi₀J : i₀ ∈ Jᶜ) (hmax : Rmax p m n K hK U ≤ (runMax p m U i₀ n).toNat) {G : ℝ}
    (hG : ∀ u ≤ xTop p m n K hK U, Gtail p m U i₀ u (n + 2) ≤ G) :
    Esum p m n J K hK U ≤ 2 * G := by
  set R : ℕ := (runMax p m U i₀ n).toNat with hR
  have hRz : ((R : ℕ) : ℤ) = runMax p m U i₀ n :=
    Int.toNat_of_nonneg (runMax_nonneg_pos p m n i₀ U)
  have hR1 : R + 1 ≤ n + 2 := by
    have h1 : runMax p m U i₀ n ≤ (n : ℤ) := runMax_le_time p m n i₀ U
    have h2 : R ≤ n := by
      have h3 : ((R : ℕ) : ℤ) ≤ (n : ℤ) := by rw [hRz]; exact h1
      exact_mod_cast h3
    omega
  have htopR : xTop p m n K hK U ≤ R + 1 := xTop_le_succ_of_max p m n K hK U hmax
  have hcomp : ∀ v : ℕ, v < R → omegaN p m U i₀ v ≤ wA p m U n Jᶜ v := by
    intro v hv
    refine omegaAt_le_wA p m U hp.le hi₀J (x := v) ?_
    rw [← hRz]
    exact_mod_cast hv
  refine Finset.sup'_le _ _ fun u hu => ?_
  rw [Finset.mem_range] at hu
  by_cases hutop : u ≤ xTop p m n K hK U
  · rw [if_pos hutop]
    rcases le_or_gt u R with huR | huR
    · have h1 : hSum (wA p m U n Jᶜ) u (xTop p m n K hK U)
          ≤ 2 * Gtail p m U i₀ u (n + 2) :=
        hSum_le_two_Gtail (p := p) hp hp1 (m := m) (n := n) (J := J) (i := i₀) (u := u)
          (x := xTop p m n K hK U) (R := R) (K := n + 2) huR htopR hcomp hR1
      have h2 : Gtail p m U i₀ u (n + 2) ≤ G := hG u hutop
      have h3 : hSum (wA p m U n Jᶜ) u (xTop p m n K hK U)
          = ∑ z ∈ Finset.Ico u (n + 2),
              (if z < xTop p m n K hK U then
                ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v else 0) :=
        hSum_eq_sum_indicator (u := u) (x := xTop p m n K hK U) (M := n + 2)
          (xTop_le p m n K hK U)
      rw [← h3]
      linarith
    · -- `u = R + 1`: the sum is empty
      have huEq : u = R + 1 := le_antisymm (le_trans hutop htopR) (by omega)
      have hempty : Finset.Ico u (xTop p m n K hK U) = ∅ := by
        rw [Finset.Ico_eq_empty_iff]
        omega
      have hzero : hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) = 0 := by
        rw [hSum, hempty, Finset.sum_empty]
      have hGpos : 0 ≤ 2 * G := by
        have h1 : (1 : ℝ) ≤ Gtail p m U i₀ u (n + 2) := by
          rw [Gtail]; linarith [Gsum_nonneg hp.le hp1 m U i₀ u (n + 2)]
        linarith [hG u hutop]
      have h3 : hSum (wA p m U n Jᶜ) u (xTop p m n K hK U)
          = ∑ z ∈ Finset.Ico u (n + 2),
              (if z < xTop p m n K hK U then
                ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v else 0) :=
        hSum_eq_sum_indicator (u := u) (x := xTop p m n K hK U) (M := n + 2)
          (xTop_le p m n K hK U)
      rw [← h3, hzero]
      exact hGpos
  · rw [if_neg hutop]
    have hGpos : 0 ≤ 2 * G := by
      have h1 : (1 : ℝ) ≤ Gtail p m U i₀ 0 (n + 2) := by
        rw [Gtail]; linarith [Gsum_nonneg hp.le hp1 m U i₀ 0 (n + 2)]
      have h2 := hG 0 (Nat.zero_le _)
      linarith
    exact hGpos

/-- The predictable good event of `(locgroup)`: separation together with the two envelope
bounds at time `n`. -/
def GoodW (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) (B : ℝ)
    (U : Array N) : Prop :=
  SepSet p m n I J U ∧
    Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U ≤ B ∧
    Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U ≤ B

theorem measurableSet_goodW (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (B : ℝ) : MeasurableSet {U : Array N | GoodW p m n I J hI B U} := by
  have h1 : MeasurableSet {U : Array N | SepSet p m n I J U} := measurableSet_sepSet_ambient p m n I J
  have h2 : MeasurableSet {U : Array N |
      Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U ≤ B} :=
    measurableSet_le ((measurable_Efix p m n J (I ∪ J) _).mono ((posFilt N p m).le n) le_rfl)
      measurable_const
  have h3 : MeasurableSet {U : Array N |
      Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U ≤ B} :=
    measurableSet_le ((measurable_Esum p m n J (I ∪ J) _).mono ((posFilt N p m).le n) le_rfl)
      measurable_const
  exact h1.inter (h2.inter h3)

/-- On the predictable good event the one-step change of `W^{I,J}` is at most `2B` times the
paper's quadratic factor. -/
theorem abs_WA_step_le_of_goodW {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} {U : Array N} (h : GoodW p m n I J hI B U) :
    |WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ|
      ≤ 2 * B + 2 * (((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * B)) := by
  obtain ⟨hsep, h1, h2⟩ := h
  have hmain := abs_WA_step_le_env hp0 hp1 I J hI hJ hid hsep
  have hE : (0 : ℝ) ≤ B :=
    le_trans (Efix_nonneg hp0.le hp1 m n J (I ∪ J) (hI.mono Finset.subset_union_left) U) h1
  have hkey : ((2 * p - 1) / p) * (N : ℝ) *
      ((1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
        * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
      ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * B) := by
    have hc : (0 : ℝ) ≤ (2 * p - 1) / p := by
      apply div_nonneg (by linarith) (by linarith)
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hE1 : (0 : ℝ) ≤ Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U :=
      Esum_nonneg hp0.le hp1 m n J (I ∪ J) (hI.mono Finset.subset_union_left) U
    have hmul : (1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
        * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U ≤ (1 + B) * B :=
      mul_le_mul (by linarith) h2 hE1 (by linarith)
    exact mul_le_mul_of_nonneg_left hmul (mul_nonneg hc hN)
  linarith [hmain, hkey]

end LocGroupQ
/-!
## 8. The paper's `L^{1/8}` step bound on `(locmax)`
-/
namespace LocGroupQ

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance

variable {N : ℕ}

/-- **The paper's one-step size bound at the local scale.**  On `(sep)`, if the leader's static
objects are bounded by `H` and `G` on the truncated range, then
`|W_{n+1}^{I,J} - W_n^{I,J}| ≤ 2(2H+6) + 2·((2p-1)/p)·N·(1+2H+6)(2G)`.  With `H = G = L^{1/16}`
(`(locmax)`, `array_locmax_hG`) this is the paper's `O(L^{1/8})` step. -/
theorem abs_WA_step_le_locmax {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) {i₀ : Fin N} (hi₀ : i₀ ∈ I)
    (hmax : Rmax p m n (I ∪ J) (hI.mono Finset.subset_union_left) U ≤ (runMax p m U i₀ n).toNat)
    {H G : ℝ} (hH1 : 1 ≤ H)
    (hH : ∀ u ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U,
      hfix (omegaN p m U i₀) u ≤ H)
    (hG : ∀ u ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U,
      Gtail p m U i₀ u (n + 2) ≤ G) :
    |WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ|
      ≤ 2 * (2 * H + 6) + 2 * (((2 * p - 1) / p) * (N : ℝ) * ((1 + (2 * H + 6)) * (2 * G))) := by
  have hi₀J : i₀ ∈ Jᶜ := Finset.mem_compl.mpr (Finset.disjoint_left.mp hid hi₀)
  have hmain := abs_WA_step_le_env hp0 hp1 I J hI hJ hid hsep
  have hE : Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U ≤ 2 * H + 6 :=
    Efix_le_of_locmax hp0.le hp1 (hI.mono Finset.subset_union_left) U
      (Finset.mem_union_left _ hi₀) hi₀J hmax hH1 hH
  have hS : Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U ≤ 2 * G :=
    Esum_le_of_locmax hp0 hp1 (hI.mono Finset.subset_union_left) U
      (Finset.mem_union_left _ hi₀) hi₀J hmax hG
  have hS0 : (0 : ℝ) ≤ Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U :=
    Esum_nonneg hp0.le hp1 m n J (I ∪ J) (hI.mono Finset.subset_union_left) U
  have hG1 : (1 : ℝ) ≤ G := by
    have h1 : (1 : ℝ) ≤ Gtail p m U i₀ 0 (n + 2) := by
      rw [Gtail]; linarith [Gsum_nonneg hp0.le hp1 m U i₀ 0 (n + 2)]
    linarith [hG 0 (Nat.zero_le _)]
  have hc : (0 : ℝ) ≤ (2 * p - 1) / p := by
    apply div_nonneg (by linarith) (by linarith)
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hmul : (1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
      * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U
      ≤ (1 + (2 * H + 6)) * (2 * G) :=
    mul_le_mul (by linarith) hS hS0 (by linarith)
  have h2 : 2 * (((2 * p - 1) / p) * (N : ℝ) *
      ((1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
        * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U))
      ≤ 2 * (((2 * p - 1) / p) * (N : ℝ) * ((1 + (2 * H + 6)) * (2 * G))) := by
    have := mul_le_mul_of_nonneg_left hmul (mul_nonneg hc hN)
    linarith
  linarith [hmain, hE, h2]

/-- The same bound in the form used by the martingale: the raw `(sep)`-increment of `Q^{I,J)`. -/
theorem abs_Qraw_le_locmax {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) {i₀ : Fin N} (hi₀ : i₀ ∈ I)
    (hmax : Rmax p m n (I ∪ J) (hI.mono Finset.subset_union_left) U ≤ (runMax p m U i₀ n).toNat)
    {H G : ℝ} (hH1 : 1 ≤ H)
    (hH : ∀ u ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U,
      hfix (omegaN p m U i₀) u ≤ H)
    (hG : ∀ u ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U,
      Gtail p m U i₀ u (n + 2) ≤ G) :
    |Qraw p m I J hI hJ n U|
      ≤ 2 * (2 * H + 6) + 2 * (((2 * p - 1) / p) * (N : ℝ) * ((1 + (2 * H + 6)) * (2 * G))) := by
  have h := abs_WA_step_le_locmax hp0 hp1 I J hI hJ hid hsep hi₀ hmax hH1 hH hG
  have hQ : Qraw p m I J hI hJ n U
      = WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ := by
    simp only [Qraw, Set.indicator_of_mem (s := {U : Array N | SepSet p m n I J U}) hsep]
  rw [hQ]
  exact h

end LocGroupQ
/-!
## 9. `GoodW` from `(sep)` and the uniform `(locmax)` bound
-/
namespace LocGroupQ

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance

variable {N : ℕ}

/-- **On `(sep)` the largest running maximum over `I ∪ J` is attained in `I`.** -/
theorem exists_leader_in_I {p : ℝ} {m n : ℕ} (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) {U : Array N} (hsep : SepSet p m n I J U) :
    ∃ i₀ ∈ I, ∀ k ∈ I ∪ J, runMax p m U k n ≤ runMax p m U i₀ n := by
  obtain ⟨i₀, hi₀, hsup⟩ := Finset.exists_mem_eq_sup' hI (fun i => runMax p m U i n)
  refine ⟨i₀, hi₀, ?_⟩
  intro k hk
  rcases Finset.mem_union.mp hk with hkI | hkJ
  · exact Finset.le_sup' (fun i => runMax p m U i n) hkI |>.trans_eq hsup
  · have h1 : runMax p m U k n + 2 ≤ X p m U n i₀ := hsep.2 i₀ hi₀ k hkJ
    have h2 : X p m U n i₀ ≤ runMax p m U i₀ n := le_runMax_pos p m U n i₀
    omega

/-- With the leader in `I`, the natural truncation equals the leader's running maximum plus one
level of slack. -/
theorem Rmax_le_leader {p : ℝ} {m n : ℕ} (I J : Finset (Fin N)) (hI : I.Nonempty)
    {U : Array N} {i₀ : Fin N} (hi₀ : i₀ ∈ I)
    (hlead : ∀ k ∈ I ∪ J, runMax p m U k n ≤ runMax p m U i₀ n) :
    Rmax p m n (I ∪ J) (hI.mono Finset.subset_union_left) U ≤ (runMax p m U i₀ n).toNat := by
  have h1 : RmaxZ p m n (I ∪ J) (hI.mono Finset.subset_union_left) U = runMax p m U i₀ n := by
    unfold RmaxZ
    exact le_antisymm (Finset.sup'_le _ _ hlead)
      (Finset.le_sup' (fun k => runMax p m U k n) (Finset.mem_union_left _ hi₀))
  unfold Rmax
  rw [h1]

/-- **The predictable good event from `(sep)` and `(locmax)`.**  If every walker of `I` has its
static potential and static tail sum bounded by `H` resp. `G` on the truncated range, then
`GoodW` holds with `B = max (2H+6) (2G)`.  No history below the running maximum is used. -/
theorem goodW_of_locmax {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) {H G : ℝ} (hH1 : 1 ≤ H)
    (hH : ∀ i ∈ I, ∀ u ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U,
      hfix (omegaN p m U i) u ≤ H)
    (hG : ∀ i ∈ I, ∀ u ≤ xTop p m n (I ∪ J) (hI.mono Finset.subset_union_left) U,
      Gtail p m U i u (n + 2) ≤ G) :
    GoodW p m n I J hI (max (2 * H + 6) (2 * G)) U := by
  obtain ⟨i₀, hi₀, hlead⟩ := exists_leader_in_I I J hI hJ hsep
  have hi₀J : i₀ ∈ Jᶜ := Finset.mem_compl.mpr (Finset.disjoint_left.mp hid hi₀)
  have hmax := Rmax_le_leader I J hI hi₀ hlead
  refine ⟨hsep, ?_, ?_⟩
  · exact (Efix_le_of_locmax hp0.le hp1 (hI.mono Finset.subset_union_left) U
      (Finset.mem_union_left _ hi₀) hi₀J hmax hH1 (hH i₀ hi₀)).trans (le_max_left _ _)
  · exact (Esum_le_of_locmax hp0 hp1 (hI.mono Finset.subset_union_left) U
      (Finset.mem_union_left _ hi₀) hi₀J hmax (hG i₀ hi₀)).trans (le_max_right _ _)

end LocGroupQ

namespace LocGroupQ

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance

variable {N : ℕ}

/-- Predicate-level predictability of `GoodW`, exposed explicitly for the later truncation. -/
theorem measurableSet_goodW_posFilt (p : ℝ) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (B : ℝ) :
    MeasurableSet[posFilt N p m n] {U : Array N | GoodW p m n I J hI B U} := by
  apply (measurableSet_sepSet p m n I J).inter
  apply MeasurableSet.inter
  · exact measurableSet_le (measurable_Efix p m n J (I ∪ J) _) measurable_const
  · exact measurableSet_le (measurable_Esum p m n J (I ∪ J) _) measurable_const

end LocGroupQ
