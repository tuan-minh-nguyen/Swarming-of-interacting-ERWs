/-
# The predictable increment envelope of the separated-group martingale `Q^{I,J}`

The paper's proof of `(locgroup)` (`main_1d_revised.tex`, Proposition `local`) needs the
one-step size bound of the group observable `W^{I,J}` *with a bound that is measurable with
respect to the position filtration at the start of the step*: it is this bound that is
compared with `L^{1/8}` on the good event `(locmax)` and that turns the raw martingale
`Q^{I,J}` of `WdriftJoint` into an Azuma martingale with predictable envelope.

`WdriftJoint.abs_WA_drift_le_staticMax` supplies the *size* of one step, but through
`staticMax`, which involves the unrevealed mark tail `Gtail` at sites above the running
maximum and is therefore **not** measurable for the position filtration.  This file replaces
it by a genuinely predictable envelope.
-/
import Swarm.SiteDiffStatic
import Swarm.LocMoveLocal

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocGroupQ

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance

variable {N : ℕ}

/-! ## 1. Natural-valued measurability of an integer-valued function -/

theorem measurable_int_toNat {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℤ} (hf : Measurable f) :
    Measurable fun ω => (f ω).toNat := by
  refine measurable_to_countable fun ω => ?_
  rcases Nat.eq_zero_or_pos ((f ω).toNat) with h0 | hpos
  · have hset : (fun ω' => (f ω').toNat) ⁻¹' {(fun ω' => (f ω').toNat) ω}
        = f ⁻¹' (Set.Iic 0) := by
      ext ω'
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Iic]
      constructor
      · intro h
        exact Int.toNat_eq_zero.mp (by rw [h, h0])
      · intro h
        rw [Int.toNat_eq_zero.mpr h, h0]
    rw [hset]
    exact hf measurableSet_Iic
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hset : (fun ω' => (f ω').toNat) ⁻¹' {(fun ω' => (f ω').toNat) ω}
        = f ⁻¹' {((k + 1 : ℕ) : ℤ)} := by
      ext ω'
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hk]
      constructor
      · intro h
        have h1 : ((f ω').toNat : ℤ) = ((k + 1 : ℕ) : ℤ) := by rw [h]
        have h2 : (f ω').toNat = k + 1 := by exact_mod_cast h1
        have hpos' : 0 ≤ f ω' := by
          by_contra hneg
          rw [Int.toNat_eq_zero.mpr (by omega)] at h2
          omega
        rw [← Int.toNat_of_nonneg hpos']
        exact_mod_cast h2
      · intro h
        rw [h]
        simp
    rw [hset]
    exact hf (measurableSet_singleton _)

/-! ## 2. The truncation site -/

/-- The largest running maximum over the walkers of `K`, as an integer. -/
noncomputable def RmaxZ (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty)
    (U : Array N) : ℤ :=
  K.sup' hK (fun k => runMax p m U k n)

/-- The same, as a site index. -/
noncomputable def Rmax (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty)
    (U : Array N) : ℕ :=
  (RmaxZ p m n K hK U).toNat

/-- The highest site at which the potential is evaluated at time `n+1`. -/
noncomputable def xTop (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty)
    (U : Array N) : ℕ :=
  min (n + 2) (Rmax p m n K hK U + 1)

theorem measurable_runMax_posFilt (p : ℝ) (m n : ℕ) (k : Fin N) :
    Measurable[posFilt N p m n] (fun U : Array N => runMax p m U k n) := by
  letI : MeasurableSpace (Array N) := posFilt N p m n
  have hne : (Finset.range (n + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
  have heq : (fun U : Array N => runMax p m U k n)
      = (Finset.range (n + 1)).sup' hne (fun t (U : Array N) => (trajectory p m U t).pos k) := by
    funext U
    exact (Finset.sup'_apply hne (fun t (U : Array N) => (trajectory p m U t).pos k) U).symm
  rw [heq]
  exact Finset.measurable_sup' hne
    (fun t ht => measurable_pos_posFilt p m k (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)))

theorem measurable_RmaxZ_posFilt (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty) :
    Measurable[posFilt N p m n] (fun U : Array N => RmaxZ p m n K hK U) := by
  letI : MeasurableSpace (Array N) := posFilt N p m n
  have heq : (fun U : Array N => RmaxZ p m n K hK U)
      = K.sup' hK (fun k (U : Array N) => runMax p m U k n) := by
    funext U
    exact (Finset.sup'_apply hK (fun k (U : Array N) => runMax p m U k n) U).symm
  rw [heq]
  exact Finset.measurable_sup' hK (fun k _ => measurable_runMax_posFilt p m n k)

theorem measurable_Rmax_posFilt (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty) :
    Measurable[posFilt N p m n] (fun U : Array N => Rmax p m n K hK U) := by
  letI : MeasurableSpace (Array N) := posFilt N p m n
  exact measurable_int_toNat (measurable_RmaxZ_posFilt p m n K hK)

theorem measurable_xTop_posFilt (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty) :
    Measurable[posFilt N p m n] (fun U : Array N => xTop p m n K hK U) := by
  letI : MeasurableSpace (Array N) := posFilt N p m n
  have h : Measurable (fun U : Array N => Rmax p m n K hK U + 1) :=
    (measurable_Rmax_posFilt p m n K hK).add measurable_const
  exact measurable_const.min h

theorem runMax_nonneg_pos (p : ℝ) (m n : ℕ) (k : Fin N) (U : Array N) :
    (0 : ℤ) ≤ runMax p m U k n := by
  have h1 : (trajectory p m U 0).pos k ≤ runMax p m U k n := le_runMax_of_le p m U n k (Nat.zero_le n)
  have h0 : (trajectory p m U 0).pos k = 0 := by rw [trajectory_zero]; rfl
  rw [h0] at h1
  exact h1

theorem runMax_le_RmaxZ (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty)
    {k : Fin N} (hk : k ∈ K) (U : Array N) :
    runMax p m U k n ≤ RmaxZ p m n K hK U :=
  Finset.le_sup' (fun k => runMax p m U k n) hk

theorem toNat_le_toNat {a b : ℤ} (hab : a ≤ b) : a.toNat ≤ b.toNat := by
  rcases lt_or_ge a 0 with ha | ha
  · rw [Int.toNat_eq_zero.mpr (by omega)]
    exact Nat.zero_le _
  · have h2 : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha
    have h3 : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg (le_trans ha hab)
    have : ((a.toNat : ℕ) : ℤ) ≤ ((b.toNat : ℕ) : ℤ) := by rw [h2, h3]; exact hab
    exact_mod_cast this

theorem runMax_le_Rmax (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty)
    {k : Fin N} (hk : k ∈ K) (U : Array N) :
    (runMax p m U k n).toNat ≤ Rmax p m n K hK U :=
  toNat_le_toNat (runMax_le_RmaxZ p m n K hK hk U)

theorem X_le_Rmax {p : ℝ} {m n : ℕ} {K : Finset (Fin N)} (hK : K.Nonempty)
    {k : Fin N} (hk : k ∈ K) (U : Array N) :
    X p m U n k ≤ ((Rmax p m n K hK U : ℕ) : ℤ) := by
  have h1 : X p m U n k ≤ runMax p m U k n := le_runMax_pos p m U n k
  have h3 : ((Rmax p m n K hK U : ℕ) : ℤ) = RmaxZ p m n K hK U :=
    Int.toNat_of_nonneg (le_trans (runMax_nonneg_pos p m n k U) (runMax_le_RmaxZ p m n K hK hk U))
  rw [h3]
  exact le_trans h1 (runMax_le_RmaxZ p m n K hK hk U)

theorem X_succ_le_xTop {p : ℝ} {m n : ℕ} {K : Finset (Fin N)} (hK : K.Nonempty)
    {k : Fin N} (hk : k ∈ K) (U : Array N) :
    X p m U (n + 1) k ≤ ((xTop p m n K hK U : ℕ) : ℤ) := by
  have h1 : X p m U (n + 1) k ≤ X p m U n k + 1 := X_succ_le_add_one p m U n k
  have h2 := X_le_Rmax (p := p) (m := m) (n := n) hK hk U
  have h3 : X p m U (n + 1) k ≤ ((Rmax p m n K hK U : ℕ) : ℤ) + 1 := by linarith
  have h4 : X p m U (n + 1) k ≤ ((n : ℕ) : ℤ) + 1 := by
    have := SwarmM3.abs_X_le p m U (n + 1) k
    rw [abs_le] at this
    push_cast at this ⊢
    omega
  have h5 : ((xTop p m n K hK U : ℕ) : ℤ)
      = min (((n + 2 : ℕ) : ℤ)) (((Rmax p m n K hK U : ℕ) : ℤ) + 1) := by
    rw [xTop, Nat.cast_min]
    push_cast
    ring_nf
  rw [h5]
  exact le_min (by omega) h3

theorem xTop_le_succ_Rmax (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty)
    (U : Array N) : xTop p m n K hK U ≤ Rmax p m n K hK U + 1 :=
  Nat.min_le_right _ _

theorem xTop_le (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty) (U : Array N) :
    xTop p m n K hK U ≤ n + 2 :=
  Nat.min_le_left _ _

theorem xTop_lt_range (p : ℝ) (m n : ℕ) (K : Finset (Fin N)) (hK : K.Nonempty) (U : Array N) :
    xTop p m n K hK U < n + 3 := by
  have := xTop_le p m n K hK U
  omega

end LocGroupQ

namespace LocGroupQ

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance

variable {N : ℕ}

/-! ## 3. The two truncated maxima defining the envelope -/

theorem measurable_rq_wA (p : ℝ) (m n : ℕ) (A : Finset (Fin N)) (v : ℕ) :
    Measurable[posFilt N p m n] (fun U : Array N => rq (wA p m U n A) v) := by
  have h : Measurable[posFilt N p m n] (fun U : Array N => wA p m U n A v) :=
    SwarmM3.measurable_wA_posFilt p m n A v
  have heq : (fun U : Array N => rq (wA p m U n A) v)
      = fun U => (1 - wA p m U n A v) / wA p m U n A v := rfl
  rw [heq]
  exact (measurable_const.sub h).div h

/-- The truncated maximum of the *actual* group potential step. -/
noncomputable def Efix (p : ℝ) (m n : ℕ) (J K : Finset (Fin N)) (hK : K.Nonempty)
    (U : Array N) : ℝ :=
  (Finset.range (n + 3)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun u => if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0)

/-- The truncated maximum of the paper's product sum, at the actual group weights. -/
noncomputable def Esum (p : ℝ) (m n : ℕ) (J K : Finset (Fin N)) (hK : K.Nonempty)
    (U : Array N) : ℝ :=
  (Finset.range (n + 3)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun u => if u ≤ xTop p m n K hK U then
      ∑ z ∈ Finset.Ico u (n + 2),
        (if z < xTop p m n K hK U then ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v
          else 0)
      else 0)

theorem measurable_Efix (p : ℝ) (m n : ℕ) (J K : Finset (Fin N)) (hK : K.Nonempty) :
    Measurable[posFilt N p m n] (fun U : Array N => Efix p m n J K hK U) := by
  letI : MeasurableSpace (Array N) := posFilt N p m n
  have htop := measurable_xTop_posFilt (N := N) p m n K hK
  have heq : (fun U : Array N => Efix p m n J K hK U)
      = (Finset.range (n + 3)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun u (U : Array N) => if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0) := by
    funext U
    exact (Finset.sup'_apply _ (fun u (U : Array N) =>
      if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0) U).symm
  rw [heq]
  refine Finset.measurable_sup' _ (fun u _ => ?_)
  exact (SwarmM3.measurable_hfix_wA_posFilt p m n Jᶜ u).ite
    (measurableSet_le measurable_const htop) measurable_const

theorem measurable_Esum (p : ℝ) (m n : ℕ) (J K : Finset (Fin N)) (hK : K.Nonempty) :
    Measurable[posFilt N p m n] (fun U : Array N => Esum p m n J K hK U) := by
  letI : MeasurableSpace (Array N) := posFilt N p m n
  have htop := measurable_xTop_posFilt (N := N) p m n K hK
  have hterm : ∀ (u z : ℕ),
      Measurable (fun U : Array N => if z < xTop p m n K hK U then
        ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v else 0) := by
    intro u z
    have hprod : Measurable (fun U : Array N =>
        ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v) :=
      Finset.measurable_prod _ (fun v _ => measurable_rq_wA p m n Jᶜ v)
    exact hprod.ite (measurableSet_lt measurable_const htop) measurable_const
  have hinner : ∀ u : ℕ, Measurable (fun U : Array N =>
      ∑ z ∈ Finset.Ico u (n + 2),
        (if z < xTop p m n K hK U then ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v
          else 0)) :=
    fun u => Finset.measurable_sum _ (fun z _ => hterm u z)
  have heq : (fun U : Array N => Esum p m n J K hK U)
      = (Finset.range (n + 3)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun u (U : Array N) => if u ≤ xTop p m n K hK U then
          ∑ z ∈ Finset.Ico u (n + 2),
            (if z < xTop p m n K hK U then
              ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v else 0)
          else 0) := by
    funext U
    exact (Finset.sup'_apply _ (fun u (U : Array N) => if u ≤ xTop p m n K hK U then
      ∑ z ∈ Finset.Ico u (n + 2),
        (if z < xTop p m n K hK U then
          ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v else 0)
      else 0) U).symm
  rw [heq]
  refine Finset.measurable_sup' _ (fun u _ => ?_)
  exact (hinner u).ite (measurableSet_le measurable_const htop) measurable_const

theorem hSum_eq_sum_indicator {w : ℕ → ℝ} {u x M : ℕ} (hx : x ≤ M) :
    hSum w u x
      = ∑ z ∈ Finset.Ico u M, (if z < x then ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq w v else 0) := by
  unfold hSum
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun z _ => rfl
  ext z
  simp only [Finset.mem_filter, Finset.mem_Ico]
  omega

theorem hSum_mono_upper {w : ℕ → ℝ} (hw0 : ∀ u, 0 < w u) (hw1 : ∀ u, w u ≤ 1)
    {u x y : ℕ} (hxy : x ≤ y) : hSum w u x ≤ hSum w u y := by
  unfold hSum
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hxy) ?_
  intro z _ _
  exact Finset.prod_nonneg fun v _ => rq_nonneg (hw0 v) (hw1 v)

theorem hfix_le_Efix {p : ℝ} {m n : ℕ} {J K : Finset (Fin N)} (hK : K.Nonempty)
    (U : Array N) {u : ℕ} (hu : u ≤ xTop p m n K hK U) :
    hfix (wA p m U n Jᶜ) u ≤ Efix p m n J K hK U := by
  have hmem : u ∈ Finset.range (n + 3) :=
    Finset.mem_range.mpr (lt_of_le_of_lt hu (xTop_lt_range p m n K hK U))
  have h1 := Finset.le_sup' (s := Finset.range (n + 3))
    (fun u => if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0) hmem
  have h2 : (if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0)
      = hfix (wA p m U n Jᶜ) u := by simp only [if_pos hu]
  rwa [h2] at h1

theorem hSum_le_Esum {p : ℝ} {m n : ℕ} {J K : Finset (Fin N)} (hK : K.Nonempty)
    (U : Array N) {u : ℕ} (hu : u ≤ xTop p m n K hK U) :
    hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) ≤ Esum p m n J K hK U := by
  have hmem : u ∈ Finset.range (n + 3) :=
    Finset.mem_range.mpr (lt_of_le_of_lt hu (xTop_lt_range p m n K hK U))
  have h1 := Finset.le_sup' (s := Finset.range (n + 3))
    (fun u => if u ≤ xTop p m n K hK U then
      ∑ z ∈ Finset.Ico u (n + 2),
        (if z < xTop p m n K hK U then ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v
          else 0)
      else 0) hmem
  have h2 : (if u ≤ xTop p m n K hK U then
      ∑ z ∈ Finset.Ico u (n + 2),
        (if z < xTop p m n K hK U then ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v
          else 0)
      else 0)
      = ∑ z ∈ Finset.Ico u (n + 2),
        (if z < xTop p m n K hK U then ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v
          else 0) := by simp only [if_pos hu]
  rw [h2] at h1
  refine le_trans ?_ h1
  rw [hSum_eq_sum_indicator (u := u) (x := xTop p m n K hK U) (M := n + 2)
    (xTop_le p m n K hK U)]

theorem Efix_nonneg {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (J K : Finset (Fin N))
    (hK : K.Nonempty) (U : Array N) : 0 ≤ Efix p m n J K hK U := by
  have h := Finset.le_sup' (s := Finset.range (n + 3))
    (fun u => if u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0)
    (Finset.mem_range.mpr (by omega) : (0 : ℕ) ∈ Finset.range (n + 3))
  have h0 : (if (0 : ℕ) ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) (0 : ℕ) else 0) ≤
      Efix p m n J K hK U := h
  split_ifs at h0
  · exact le_trans (zero_le_one.trans (one_le_hfix _ (wA_pos p m U hp n Jᶜ)
      (wA_le_one p m U hp1 n Jᶜ) 0)) h0
  · exact h0

theorem Esum_nonneg {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (J K : Finset (Fin N))
    (hK : K.Nonempty) (U : Array N) : 0 ≤ Esum p m n J K hK U := by
  have h := Finset.le_sup' (s := Finset.range (n + 3))
    (fun u => if u ≤ xTop p m n K hK U then
      ∑ z ∈ Finset.Ico u (n + 2),
        (if z < xTop p m n K hK U then ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v
          else 0)
      else 0)
    (Finset.mem_range.mpr (by omega) : (0 : ℕ) ∈ Finset.range (n + 3))
  refine le_trans (b := (if (0 : ℕ) ≤ xTop p m n K hK U then
      ∑ z ∈ Finset.Ico (0 : ℕ) (n + 2),
        (if z < xTop p m n K hK U then ∏ v ∈ Finset.Ico ((0 : ℕ) + 1) (z + 1), rq (wA p m U n Jᶜ) v
          else 0)
      else 0)) ?_ h
  split_ifs with hle
  · refine Finset.sum_nonneg fun z _ => ?_
    split_ifs
    · exact Finset.prod_nonneg fun v _ => rq_nonneg (wA_pos p m U hp n Jᶜ v)
        (wA_le_one p m U hp1 n Jᶜ v)
    · exact le_rfl
  · exact le_rfl

end LocGroupQ

namespace LocGroupQ

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance

variable {N : ℕ}

/-! ## 4. The paper's product-sum bound with the *actual* weights -/

theorem hSum_nonneg {w : ℕ → ℝ} (hw0 : ∀ u, 0 < w u) (hw1 : ∀ u, w u ≤ 1) (u x : ℕ) :
    0 ≤ hSum w u x :=
  Finset.sum_nonneg fun z _ => Finset.prod_nonneg fun v _ => rq_nonneg (hw0 v) (hw1 v)

theorem hprev_mono {w w' : ℕ → ℝ} (hw0 : ∀ u, 0 < w u) (hw1 : ∀ u, w u ≤ 1)
    (hw0' : ∀ u, 0 < w' u) (hw1' : ∀ u, w' u ≤ 1) (hle : ∀ u, w u ≤ w' u) (u : ℕ) :
    hprev w' u ≤ hprev w u := by
  match u with
  | 0 => simp
  | k + 1 => rw [hprev_succ, hprev_succ]; exact hfix_mono w w' hw0 hw1 hw0' hw1' hle k

/-- **The paper's one-step size bound, with a predictable right-hand side.**  For a site
`0 ≤ y` below the truncation site, the change of the group potential caused by the one-step
weight update at time `n` is bounded by `C · N · (1 + Efix) · Esum`. -/
theorem hBound_le_env {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ} {J K : Finset (Fin N)}
    (hK : K.Nonempty) (U : Array N) {s : ℕ} (hs : s ≤ xTop p m n K hK U) :
    hBound p (wA p m U n Jᶜ) (wA p m U (n + 1) Jᶜ) s
      ≤ ((2 * p - 1) / p) * (N : ℝ) *
          ((1 + Efix p m n J K hK U) * Esum p m n J K hK U) := by
  set M : ℝ := (1 + Efix p m n J K hK U) * Esum p m n J K hK U with hM
  have hEfix1 : (0 : ℝ) ≤ Efix p m n J K hK U := Efix_nonneg hp0.le hp1 m n J K hK U
  have hEsum0 : (0 : ℝ) ≤ Esum p m n J K hK U := Esum_nonneg hp0.le hp1 m n J K hK U
  have hM0 : (0 : ℝ) ≤ M := mul_nonneg (by linarith) hEsum0
  have hfix01 : (1 : ℝ) ≤ Efix p m n J K hK U := by
    have h0 : hfix (wA p m U n Jᶜ) 0 ≤ Efix p m n J K hK U :=
      hfix_le_Efix hK U (Nat.zero_le _)
    exact le_trans (one_le_hfix _ (wA_pos p m U hp0.le n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) 0) h0
  have hterm : ∀ u ∈ Finset.range (s + 1),
      (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then
          (1 + hprev (wA p m U (n + 1) Jᶜ) u) * hSum (wA p m U n Jᶜ) u s else 0)
        ≤ (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then M else 0) := by
    intro u hu
    by_cases h : wA p m U n Jᶜ u = wA p m U (n + 1) Jᶜ u
    · rw [if_neg (show ¬ (wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u) from fun h' => h' h),
        if_neg (show ¬ (wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u) from fun h' => h' h)]
    · rw [if_pos h, if_pos h]
      have hus : u ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
      have hu1 : 1 + hprev (wA p m U (n + 1) Jᶜ) u ≤ 1 + Efix p m n J K hK U := by
        have hmono : hprev (wA p m U (n + 1) Jᶜ) u ≤ hprev (wA p m U n Jᶜ) u :=
          hprev_mono (wA_pos p m U hp0.le n Jᶜ) (wA_le_one p m U hp1 n Jᶜ)
            (wA_pos p m U hp0.le (n + 1) Jᶜ) (wA_le_one p m U hp1 (n + 1) Jᶜ)
            (fun v => wA_le_succ p hp0.le m U n Jᶜ v) u
        have hle2 : hprev (wA p m U n Jᶜ) u ≤ Efix p m n J K hK U := by
          rcases Nat.eq_zero_or_pos u with hu0 | hupos
          · rw [hu0, hprev_zero]
            exact hfix01
          · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hupos.ne'
            rw [hk, hprev_succ]
            exact hfix_le_Efix hK U (le_trans (by omega) hs)
        linarith
      have hu2 : hSum (wA p m U n Jᶜ) u s ≤ Esum p m n J K hK U := by
        have h1 : hSum (wA p m U n Jᶜ) u s ≤ hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) :=
          hSum_mono_upper (wA_pos p m U hp0.le n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) hs
        exact le_trans h1 (hSum_le_Esum hK U (le_trans hus hs))
      have hsum0 : 0 ≤ hSum (wA p m U n Jᶜ) u s :=
        hSum_nonneg (wA_pos p m U hp0.le n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) u s
      have h1 : (1 + hprev (wA p m U (n + 1) Jᶜ) u) * hSum (wA p m U n Jᶜ) u s
          ≤ (1 + Efix p m n J K hK U) * Esum p m n J K hK U :=
        mul_le_mul hu1 hu2 hsum0 (by linarith)
      rw [hM]
      exact h1
  have hsub : Finset.range (s + 1) ⊆ Finset.range (xTop p m n K hK U + 1) := by
    intro u hu
    rw [Finset.mem_range] at hu ⊢
    omega
  have hsum1 : (∑ u ∈ Finset.range (s + 1),
      (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then
        (1 + hprev (wA p m U (n + 1) Jᶜ) u) * hSum (wA p m U n Jᶜ) u s else 0))
      ≤ ∑ u ∈ Finset.range (xTop p m n K hK U + 1),
        (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then M else 0) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro u _ _
    split_ifs
    · exact hM0
    · exact le_rfl
  have hsum2 : (∑ u ∈ Finset.range (xTop p m n K hK U + 1),
      (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then M else 0))
      = M * (((Finset.range (xTop p m n K hK U + 1)).filter
          (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  have hcard : ((((Finset.range (xTop p m n K hK U + 1)).filter
      (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card : ℕ) : ℝ) ≤ (N : ℝ) := by
    have h := card_cross_le (N := N) p hp0 m n J U (xTop p m n K hK U)
    have h' : ((Finset.range (xTop p m n K hK U + 1)).filter
        (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card ≤ N := h
    exact_mod_cast h'
  have hstep : (∑ u ∈ Finset.range (s + 1),
      (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then
        (1 + hprev (wA p m U (n + 1) Jᶜ) u) * hSum (wA p m U n Jᶜ) u s else 0))
      ≤ N * M := by
    refine le_trans (le_trans hsum1 (le_of_eq hsum2)) ?_
    calc M * ((((Finset.range (xTop p m n K hK U + 1)).filter
          (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card : ℕ) : ℝ)
        ≤ M * (N : ℝ) := mul_le_mul_of_nonneg_left hcard hM0
      _ = (N : ℝ) * M := by ring
  unfold hBound
  have hnp : 0 ≤ (2 * p - 1) / p := by
    apply div_nonneg (by linarith) (by linarith)
  calc ((2 * p - 1) / p) * (∑ u ∈ Finset.range (s + 1),
        (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then
          (1 + hprev (wA p m U (n + 1) Jᶜ) u) * hSum (wA p m U n Jᶜ) u s else 0))
      ≤ ((2 * p - 1) / p) * ((N : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hstep hnp
    _ = ((2 * p - 1) / p) * (N : ℝ) * M := by ring

end LocGroupQ

namespace LocGroupQ

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance

variable {N : ℕ}

/-! ## 5. Per-walker one-step bounds with the predictable envelope -/

/-- The weight-update part of one walker's potential change, bounded by the envelope. -/
theorem abs_HA_weight_step_le_env {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (U : Array N) {y : ℤ}
    (hy : y ≤ (xTop p m n K hK U : ℤ)) :
    |HA p m U (n + 1) Jᶜ y - HA p m U n Jᶜ y|
      ≤ ((2 * p - 1) / p) * (N : ℝ) *
          ((1 + Efix p m n J K hK U) * Esum p m n J K hK U) := by
  have hw0 : ∀ u, 0 < wA p m U n Jᶜ u := wA_pos p m U hp0.le n Jᶜ
  have hw1 : ∀ u, wA p m U n Jᶜ u ≤ 1 := wA_le_one p m U hp1 n Jᶜ
  have hw0' : ∀ u, 0 < wA p m U (n + 1) Jᶜ u := wA_pos p m U hp0.le (n + 1) Jᶜ
  have hw1' : ∀ u, wA p m U (n + 1) Jᶜ u ≤ 1 := wA_le_one p m U hp1 (n + 1) Jᶜ
  have hv : ∀ u, wA p m U n Jᶜ u = 1 / 2 ∨ wA p m U n Jᶜ u = p := wA_eq_half_or p m U n Jᶜ
  have hv' : ∀ u, wA p m U (n + 1) Jᶜ u = 1 / 2 ∨ wA p m U (n + 1) Jᶜ u = p :=
    wA_eq_half_or p m U (n + 1) Jᶜ
  have hle : ∀ u, wA p m U n Jᶜ u ≤ wA p m U (n + 1) Jᶜ u := fun v =>
    wA_le_succ p hp0.le m U n Jᶜ v
  by_cases hy0 : 0 ≤ y
  swap
  · have h1 : HA p m U (n + 1) Jᶜ y = (y : ℝ) := by
      show SepGroup.HZ (wA p m U (n + 1) Jᶜ) y = _
      rw [SepGroup.HZ_neg (by omega)]
    have h2 : HA p m U n Jᶜ y = (y : ℝ) := by
      show SepGroup.HZ (wA p m U n Jᶜ) y = _
      rw [SepGroup.HZ_neg (by omega)]
    rw [h1, h2, sub_self, abs_zero]
    have hEfix1 : (0 : ℝ) ≤ Efix p m n J K hK U := Efix_nonneg hp0.le hp1 m n J K hK U
    have hEsum0 : (0 : ℝ) ≤ Esum p m n J K hK U := Esum_nonneg hp0.le hp1 m n J K hK U
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hc : (0 : ℝ) ≤ (2 * p - 1) / p := by
      apply div_nonneg (by linarith) (by linarith)
    have : (0 : ℝ) ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + Efix p m n J K hK U) * Esum p m n J K hK U) :=
      mul_nonneg (mul_nonneg hc hN) (mul_nonneg (by linarith) hEsum0)
    exact this
  have hHA1 : HA p m U (n + 1) Jᶜ y = Hfix (wA p m U (n + 1) Jᶜ) y.toNat := by
    show SepGroup.HZ (wA p m U (n + 1) Jᶜ) y = _
    rw [SepGroup.HZ_nonneg hy0]
  have hHA2 : HA p m U n Jᶜ y = Hfix (wA p m U n Jᶜ) y.toNat := by
    show SepGroup.HZ (wA p m U n Jᶜ) y = _
    rw [SepGroup.HZ_nonneg hy0]
  rw [hHA1, hHA2]
  have hmono : Hfix (wA p m U (n + 1) Jᶜ) y.toNat ≤ Hfix (wA p m U n Jᶜ) y.toNat :=
    Hfix_mono _ _ hw0 hw1 hw0' hw1' hle y.toNat
  have hneg : Hfix (wA p m U (n + 1) Jᶜ) y.toNat - Hfix (wA p m U n Jᶜ) y.toNat ≤ 0 := by linarith
  rw [abs_of_nonpos hneg, neg_sub]
  have hm : y.toNat ≤ xTop p m n K hK U := by
    have h1 : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy0
    have h2 : ((y.toNat : ℕ) : ℤ) ≤ ((xTop p m n K hK U : ℕ) : ℤ) := by rw [h1]; exact hy
    exact_mod_cast h2
  have hp0ne : p ≠ 0 := by linarith
  refine le_trans (Hfix_diff_le_hBound (p := p) hp0 hp0ne hp1 hw0 hw1 hw0' hw1' hv hv'
    hle y.toNat) ?_
  exact hBound_le_env hp0 hp1 hK U hm

/-- The position-move part of one walker's potential change, bounded by `Efix`. -/
theorem abs_HA_pos_step_le_Efix {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (U : Array N) {k : Fin N} (hk : k ∈ K) :
    |HA p m U n Jᶜ (X p m U (n + 1) k) - HA p m U n Jᶜ (X p m U n k)|
      ≤ Efix p m n J K hK U := by
  have hd : X p m U (n + 1) k = X p m U n k + 1 ∨ X p m U (n + 1) k = X p m U n k - 1 ∨
      X p m U (n + 1) k = X p m U n k := by
    rcases X_succ_sub_X p m U n k with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have h := abs_HZ_step_le (w := wA p m U n Jᶜ) (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) hd
  have hx : X p m U n k ≤ ((xTop p m n K hK U : ℕ) : ℤ) := by
    have h1 : X p m U n k ≤ ((n : ℕ) : ℤ) := by
      have := SwarmM3.abs_X_le p m U n k
      rw [abs_le] at this
      omega
    have h2 : X p m U n k ≤ ((n + 2 : ℕ) : ℤ) := by push_cast; omega
    have h3 : ((xTop p m n K hK U : ℕ) : ℤ)
        = min (((n + 2 : ℕ) : ℤ)) (((Rmax p m n K hK U : ℕ) : ℤ) + 1) := by
      rw [xTop, Nat.cast_min]
      push_cast
      ring_nf
    rw [h3]
    exact le_min h2 (by linarith [X_le_Rmax (p := p) (m := m) (n := n) hK hk U])
  have hy : X p m U (n + 1) k ≤ ((xTop p m n K hK U : ℕ) : ℤ) := X_succ_le_xTop hK hk U
  have hx' : X p m U n k ≤ ((Rmax p m n K hK U : ℕ) : ℤ) := X_le_Rmax hK hk U
  refine le_trans h (max_le ?_ ?_)
  · exact hfix_le_Efix hK U (by omega)
  · exact hfix_le_Efix hK U (by omega)

end LocGroupQ

namespace LocGroupQ

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance

variable {N : ℕ}

/-- `|max' f| ≤ C` from a uniform bound on `|f|`. -/
theorem abs_maximumOn_le_of_bound {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → ℝ}
    {C : ℝ} (h : ∀ i ∈ s, |f i| ≤ C) :
    |Swarming.Group.maximumOn s hs f| ≤ C := by
  have h0 : s.sup' hs (fun _ => (0 : ℝ)) = 0 := by
    rw [Finset.sup'_const]
  have h1 := abs_sup'_sub_sup'_le (s := s) (hs := hs) (f := f) (g := fun _ => (0 : ℝ)) (C := C)
    (fun i hi => by simpa using h i hi)
  simpa [Swarming.Group.maximumOn, h0] using h1

/-- **The one-step size bound of `W^{I,J}` with a predictable right-hand side.**  On the
separated event, the change of the group observable in one step is bounded by the
`posFilt n`-measurable envelope
`2·Efix + 2·((2p-1)/p)·N·(1+Efix)·Esum`. -/
theorem abs_WA_step_le_env {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) :
    |WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ|
      ≤ 2 * Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U
        + 2 * (((2 * p - 1) / p) * (N : ℝ) *
            ((1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
              * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)) := by
  have hIK : ∀ k ∈ I, k ∈ I ∪ J := fun k hk => Finset.mem_union_left _ hk
  have hJK : ∀ k ∈ J, k ∈ I ∪ J := fun k hk => Finset.mem_union_right _ hk
  -- the three potential families
  set f : Fin N → ℝ := fun k => HA p m U (n + 1) Jᶜ (X p m U (n + 1) k) with hf
  set g : Fin N → ℝ := fun k => HA p m U n Jᶜ (X p m U n k) with hg
  set md : Fin N → ℝ := fun k => HA p m U n Jᶜ (X p m U (n + 1) k) with hmd
  -- the two per-walker bounds
  have hBp : ∀ k ∈ I ∪ J, |md k - g k| ≤ Efix p m n J (I ∪ J)
      (hI.mono Finset.subset_union_left) U := by
    intro k hk
    exact abs_HA_pos_step_le_Efix hp0.le hp1 (hI.mono Finset.subset_union_left) U hk
  have hBw : ∀ k ∈ I ∪ J, |f k - md k| ≤ ((2 * p - 1) / p) * (N : ℝ) *
      ((1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
        * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U) := by
    intro k hk
    exact abs_HA_weight_step_le_env hp0 hp1 (hI.mono Finset.subset_union_left) U
      (X_succ_le_xTop (hI.mono Finset.subset_union_left) hk U)
  -- the two differences
  have eA : Swarming.Group.average I f - Swarming.Group.average I g
      = Swarming.Group.average I (fun i => f i - md i)
        + Swarming.Group.average I (fun i => md i - g i) := by
    have h1 : Swarming.Group.average I (fun i => f i - md i)
        = Swarming.Group.average I f - Swarming.Group.average I md := average_sub_group _ _ _
    have h2 : Swarming.Group.average I (fun i => md i - g i)
        = Swarming.Group.average I md - Swarming.Group.average I g := average_sub_group _ _ _
    rw [h1, h2]; ring
  have hWA1 : WA p m U (n + 1) I J hI hJ = Swarming.Group.average I f
      - Swarming.Group.maximumOn J hJ f := rfl
  have hWA0 : WA p m U n I J hI hJ = Swarming.Group.average I g
      - Swarming.Group.maximumOn J hJ g := rfl
  -- bounds on the four pieces
  have b1 : |Swarming.Group.average I (fun i => f i - md i)| ≤ ((2 * p - 1) / p) * (N : ℝ) *
      ((1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
        * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U) :=
    abs_average_le_of_bound hI (fun i hi => hBw i (hIK i hi))
  have b2 : |Swarming.Group.maximumOn J hJ (fun j => f j - md j)| ≤ ((2 * p - 1) / p) * (N : ℝ) *
      ((1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
        * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U) :=
    abs_maximumOn_le_of_bound hJ (fun j hj => hBw j (hJK j hj))
  have b3 : |Swarming.Group.average I (fun i => md i - g i)|
      ≤ Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U :=
    abs_average_le_of_bound hI (fun i hi => hBp i (hIK i hi))
  have b4 : |Swarming.Group.maximumOn J hJ (fun j => md j - g j)|
      ≤ Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U :=
    abs_maximumOn_le_of_bound hJ (fun j hj => hBp j (hJK j hj))
  have b5 : |Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ md|
      ≤ ((2 * p - 1) / p) * (N : ℝ) *
        ((1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
          * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U) :=
    abs_sup'_sub_sup'_le (s := J) (hs := hJ) (fun j hj => hBw j (hJK j hj))
  have b6 : |Swarming.Group.maximumOn J hJ md - Swarming.Group.maximumOn J hJ g|
      ≤ Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U :=
    abs_sup'_sub_sup'_le (s := J) (hs := hJ) (fun j hj => hBp j (hJK j hj))
  rw [hWA1, hWA0]
  have key : (Swarming.Group.average I f - Swarming.Group.maximumOn J hJ f)
        - (Swarming.Group.average I g - Swarming.Group.maximumOn J hJ g)
      = (Swarming.Group.average I f - Swarming.Group.average I g)
        - (Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ g) := by ring
  rw [key, eA]
  have hA : |(Swarming.Group.average I (fun i => f i - md i)
        + Swarming.Group.average I (fun i => md i - g i))|
      ≤ ((2 * p - 1) / p) * (N : ℝ) *
          ((1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
            * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
        + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U :=
    le_trans (abs_add_le _ _) (add_le_add b1 b3)
  have hM : |(Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ g)|
      ≤ ((2 * p - 1) / p) * (N : ℝ) *
          ((1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
            * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
        + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U := by
    have hsplit : (Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ g)
        = (Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ md)
          + (Swarming.Group.maximumOn J hJ md - Swarming.Group.maximumOn J hJ g) := by ring
    rw [hsplit]
    exact le_trans (abs_add_le _ _) (add_le_add b5 b6)
  calc |(Swarming.Group.average I (fun i => f i - md i)
          + Swarming.Group.average I (fun i => md i - g i))
        - (Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ g)|
      ≤ |(Swarming.Group.average I (fun i => f i - md i)
          + Swarming.Group.average I (fun i => md i - g i))|
        + |(Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ g)| := abs_sub _ _
    _ ≤ 2 * Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U
        + 2 * (((2 * p - 1) / p) * (N : ℝ) *
            ((1 + Efix p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)
              * Esum p m n J (I ∪ J) (hI.mono Finset.subset_union_left) U)) := by
      linarith [hA, hM]

end LocGroupQ
