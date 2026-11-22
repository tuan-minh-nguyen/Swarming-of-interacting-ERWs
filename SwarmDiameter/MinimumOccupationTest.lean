import Swarm.Imports
import Mathlib.Analysis.SpecificLimits.Basic

open Finset

namespace Swarming.Diameter

set_option autoImplicit false

variable {N : ℕ}

private noncomputable def occupationWeight (a : ℝ) (N : ℕ) (z x : ℤ) : ℝ :=
  a ^ (z - x) / ((N : ℝ) + 1)

private noncomputable def occupationMass (a : ℝ) (J : Finset (Fin N)) (x : Fin N → ℤ) (z : ℤ) : ℝ :=
  ∑ j ∈ J, occupationWeight a N z (x j)

/-- Sum of the bounded tests for the sites of a finite set. -/
noncomputable def minimumOccupationTest (a : ℝ) (J : Finset (Fin N)) (S : Finset ℤ)
    (x : Fin N → ℤ) : ℝ :=
  ∑ z ∈ S, min 1 (occupationMass a J x z)

private noncomputable def activeSites (a : ℝ) (J : Finset (Fin N)) (S : Finset ℤ)
    (x : Fin N → ℤ) : Finset ℤ :=
  S.filter fun z => occupationMass a J x z ≤ 1

/-- Coefficient of a walker's compensated step in the occupation estimate. -/
noncomputable def minimumOccupationCoeff (a : ℝ) (J : Finset (Fin N)) (S : Finset ℤ)
    (x : Fin N → ℤ) (i : Fin N) : ℝ :=
  if i ∈ J then (a⁻¹ - a) / 2 * ∑ z ∈ activeSites a J S x, occupationWeight a N z (x i) else 0

private theorem occupationWeight_nonneg {a : ℝ} (ha : 0 < a) (z x : ℤ) :
    0 ≤ occupationWeight a N z x := by unfold occupationWeight; positivity

private theorem occupationMass_nonneg {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin N)) (x : Fin N → ℤ) (z : ℤ) : 0 ≤ occupationMass a J x z :=
  Finset.sum_nonneg (fun j _ => occupationWeight_nonneg ha z (x j))

theorem minimumOccupationTest_bounds {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin N)) (S : Finset ℤ) (x : Fin N → ℤ) :
    0 ≤ minimumOccupationTest a J S x ∧ minimumOccupationTest a J S x ≤ (S.card : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun z _ => le_min zero_le_one (occupationMass_nonneg ha J x z))
  · simpa [minimumOccupationTest] using Finset.sum_le_sum (s := S)
      (fun z _ => min_le_left (1 : ℝ) (occupationMass a J x z))

private theorem occupationWeight_shift {a : ℝ} (ha : 0 < a) {z b : ℤ} (hz : z ≤ b) (x : ℤ) :
    occupationWeight a N z x = (a⁻¹) ^ (b - z).toNat * occupationWeight a N b x := by
  have he : z - x = (b - x) - ((b - z).toNat : ℤ) := by omega
  unfold occupationWeight
  rw [he, zpow_sub₀ ha.ne', zpow_natCast, inv_pow]
  ring

private theorem sum_active_occupationMass_le {a : ℝ} (ha : 1 < a)
    (J : Finset (Fin N)) (S : Finset ℤ) (x : Fin N → ℤ) :
    (∑ z ∈ activeSites a J S x, occupationMass a J x z) ≤ (1 - a⁻¹)⁻¹ := by
  have ha₀ : 0 < a := zero_lt_one.trans ha
  have hinv : a⁻¹ < 1 := (inv_lt_one₀ ha₀).mpr ha
  let I := activeSites a J S x
  by_cases hI : I.Nonempty
  · let b := I.max' hI
    let g (z : ℤ) := (b - z).toNat
    have hb (z : ℤ) (hz : z ∈ I) : z ≤ b := Finset.le_max' I z hz
    have hb₀ : occupationMass a J x b ≤ 1 := (Finset.mem_filter.mp (Finset.max'_mem I hI)).2
    have hf (z : ℤ) (hz : z ∈ I) : occupationMass a J x z ≤ (a⁻¹) ^ g z := by
      change (∑ j ∈ J, occupationWeight a N z (x j)) ≤ _
      simp only [occupationWeight_shift ha₀ (hb z hz), ← Finset.mul_sum]
      exact mul_le_of_le_one_right (by positivity) hb₀
    have hinj : Set.InjOn g I := by
      intro z hz z' hz' he
      have hz₀ := hb z hz
      have hz₀' := hb z' hz'
      dsimp only [g] at he
      omega
    have hsum := (summable_geometric_of_lt_one (inv_nonneg.mpr ha₀.le) hinv).sum_le_tsum
      (I.image g) (fun n _ => pow_nonneg (inv_nonneg.mpr ha₀.le) n)
    calc
      _ ≤ ∑ z ∈ I, (a⁻¹) ^ g z := Finset.sum_le_sum hf
      _ = ∑ n ∈ I.image g, (a⁻¹) ^ n := (Finset.sum_image hinj).symm
      _ ≤ _ := by simpa only [tsum_geometric_of_lt_one (inv_nonneg.mpr ha₀.le) hinv] using hsum
  · have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    change (∑ z ∈ I, occupationMass a J x z) ≤ _
    rw [he, Finset.sum_empty]
    exact inv_nonneg.mpr (sub_nonneg.mpr hinv.le)

theorem abs_minimumOccupationCoeff_le {a : ℝ} (ha : 1 < a)
    (J : Finset (Fin N)) (S : Finset ℤ) (x : Fin N → ℤ) (i : Fin N) :
    |minimumOccupationCoeff a J S x i| ≤ (a - a⁻¹) / 2 * (1 - a⁻¹)⁻¹ := by
  have ha₀ : 0 < a := zero_lt_one.trans ha
  have hinv := (inv_lt_one₀ ha₀).mpr ha
  have hc : 0 ≤ (a - a⁻¹) / 2 := by linarith
  by_cases hi : i ∈ J
  · rw [minimumOccupationCoeff, if_pos hi, abs_mul, abs_of_nonneg
      (Finset.sum_nonneg (fun z _ => occupationWeight_nonneg ha₀ z (x i)))]
    rw [abs_of_nonpos (by linarith : (a⁻¹ - a) / 2 ≤ 0),
      show -((a⁻¹ - a) / 2) = (a - a⁻¹) / 2 by ring]
    refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum (s := activeSites a J S x)
      (fun z _ => Finset.single_le_sum (fun j _ => occupationWeight_nonneg ha₀ z (x j)) hi)).trans
        (sum_active_occupationMass_le ha J S x)) hc
  · rw [minimumOccupationCoeff, if_neg hi, abs_zero]
    exact mul_nonneg hc (inv_nonneg.mpr (sub_nonneg.mpr hinv.le))

private theorem occupationWeight_step {a : ℝ} (ha : 0 < a) {x y z : ℤ}
    (h : y = x + 1 ∨ y = x - 1) (α : ℝ) :
    occupationWeight a N z y - occupationWeight a N z x =
      (α * a⁻¹ + (1 - α) * a - 1) * occupationWeight a N z x +
        (a⁻¹ - a) / 2 * occupationWeight a N z x * (((y : ℝ) - x) - (2 * α - 1)) := by
  rcases h with rfl | rfl
  · unfold occupationWeight
    rw [show z - (x + 1) = z - x - 1 by omega, zpow_sub₀ ha.ne', zpow_one]
    push_cast
    ring
  · unfold occupationWeight
    rw [show z - (x - 1) = z - x + 1 by omega, zpow_add_one₀ ha.ne']
    push_cast
    ring

private theorem occupationMass_at_min_bounds {a : ℝ} (ha : 1 < a)
    {J : Finset (Fin N)} {j : Fin N} (hj : j ∈ J) {x : Fin N → ℤ}
    (hx : ∀ i ∈ J, x j ≤ x i) :
    1 / ((N : ℝ) + 1) ≤ occupationMass a J x (x j) ∧ occupationMass a J x (x j) ≤ 1 := by
  have ha₀ := zero_lt_one.trans ha
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hw : occupationWeight a N (x j) (x j) = 1 / ((N : ℝ) + 1) := by simp [occupationWeight]
  have he (i : Fin N) (hi : i ∈ J) :
      occupationWeight a N (x j) (x i) ≤ 1 / ((N : ℝ) + 1) := by
    rw [← hw]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact zpow_le_zpow_right₀ ha.le (by linarith only [hx i hi])
  constructor
  · rw [← hw]
    exact Finset.single_le_sum (fun i _ => occupationWeight_nonneg ha₀ (x j) (x i)) hj
  · calc
      _ ≤ ∑ _i ∈ J, 1 / ((N : ℝ) + 1) := Finset.sum_le_sum he
      _ = (J.card : ℝ) / ((N : ℝ) + 1) := by simp [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr (by
        have hcard : (J.card : ℝ) ≤ N := by exact_mod_cast (Finset.card_le_univ J).trans_eq (Fintype.card_fin N)
        linarith only [hcard])

/-- The tilt `a = 1 + (p - 1/2) / N` has strictly negative drift when the
minimum is excited. -/
theorem minimumOccupation_tilt_drift_pos {p : ℝ} (hp : (1 : ℝ) / 2 < p) {N : ℕ} (hN : 0 < N) :
    let b := (p - 1 / 2) / (N : ℝ)
    let a := 1 + b
    0 < 1 - (a + a⁻¹) / 2 + b * (a - a⁻¹) := by
  intro b a
  have hb : 0 < b := div_pos (by linarith) (by exact_mod_cast hN)
  have ha : 0 < a := by dsimp only [a]; positivity
  have he : 1 - (a + a⁻¹) / 2 + b * (a - a⁻¹) = b ^ 2 * (2 * a + 1) / (2 * a) := by
    field_simp
    dsimp only [a]
    ring
  rw [he]
  positivity

/-- A one-step bound for the occupation test at a configuration with an
excited minimizer. The random part is a predictable linear combination of
the compensated steps. -/
theorem minimumOccupationTest_sub_le {a p : ℝ} (ha : 1 < a) (hp : (1 : ℝ) / 2 ≤ p)
    {J : Finset (Fin N)} {j : Fin N} (hj : j ∈ J) (S : Finset ℤ)
    {x y : Fin N → ℤ} (hmin : ∀ i ∈ J, x j ≤ x i)
    (hstep : ∀ i, y i = x i + 1 ∨ y i = x i - 1) {α : Fin N → ℝ}
    (hα : ∀ i, 1 / 2 ≤ α i) (hαj : α j = p)
    (hd : 0 ≤ 1 - (a + a⁻¹) / 2 + (p - 1 / 2) / (N : ℝ) * (a - a⁻¹)) :
    minimumOccupationTest a J S y - minimumOccupationTest a J S x ≤
      (∑ i, minimumOccupationCoeff a J S x i * (((y i : ℝ) - x i) - (2 * α i - 1))) -
        (1 - (a + a⁻¹) / 2 + (p - 1 / 2) / (N : ℝ) * (a - a⁻¹)) /
          ((N : ℝ) + 1) * (if x j ∈ S then 1 else 0) := by
  let d := 1 - (a + a⁻¹) / 2 + (p - 1 / 2) / (N : ℝ) * (a - a⁻¹)
  let q := occupationMass a J x
  let q' := occupationMass a J y
  let M (i : Fin N) := ((y i : ℝ) - x i) - (2 * α i - 1)
  let I := activeSites a J S x
  have ha₀ := zero_lt_one.trans ha
  have haGap : 0 ≤ a - a⁻¹ := by linarith [(inv_lt_one₀ ha₀).mpr ha]
  have hN : (0 : ℝ) < N := by
    have hjN := Fin.isLt j
    exact_mod_cast (show 0 < N by omega)
  have hdrift (z : ℤ) : (p - 1 / 2) / (N : ℝ) * q z ≤
      ∑ i ∈ J, (α i - 1 / 2) * occupationWeight a N z (x i) := by
    let w := occupationWeight a N z (x j)
    have hw : 0 ≤ w := occupationWeight_nonneg ha₀ z (x j)
    have hq : q z ≤ (N : ℝ) * w := calc
      _ ≤ ∑ _i ∈ J, w := Finset.sum_le_sum fun i hi =>
        div_le_div_of_nonneg_right (zpow_le_zpow_right₀ ha.le (by linarith only [hmin i hi])) (by positivity)
      _ = (J.card : ℝ) * w := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Finset.card_le_univ J).trans_eq (Fintype.card_fin N)) hw
    have hq' : q z / (N : ℝ) ≤ w := (div_le_iff₀ hN).mpr (hq.trans_eq (mul_comm _ _))
    calc
      _ = (p - 1 / 2) * (q z / (N : ℝ)) := by ring
      _ ≤ (p - 1 / 2) * w := mul_le_mul_of_nonneg_left hq' (sub_nonneg.mpr hp)
      _ ≤ _ := by
        rw [← hαj]
        exact Finset.single_le_sum (fun i _ => mul_nonneg (sub_nonneg.mpr (hα i))
          (occupationWeight_nonneg ha₀ z (x i))) hj
  have hstep' (z : ℤ) : q' z - q z ≤ -d * q z +
      ∑ i ∈ J, (a⁻¹ - a) / 2 * occupationWeight a N z (x i) * M i := by
    have he : q' z - q z = ((a + a⁻¹) / 2 - 1) * q z -
        (a - a⁻¹) * (∑ i ∈ J, (α i - 1 / 2) * occupationWeight a N z (x i)) +
        ∑ i ∈ J, (a⁻¹ - a) / 2 * occupationWeight a N z (x i) * M i := by
      dsimp only [q, q', occupationMass]
      rw [← Finset.sum_sub_distrib]
      calc
        _ = ∑ i ∈ J, ((((a + a⁻¹) / 2 - 1) * occupationWeight a N z (x i)) -
            (a - a⁻¹) * ((α i - 1 / 2) * occupationWeight a N z (x i)) +
            (a⁻¹ - a) / 2 * occupationWeight a N z (x i) * M i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [occupationWeight_step ha₀ (hstep i) (α i)]
          ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [he]
    dsimp only [d]
    linarith only [mul_le_mul_of_nonneg_left (hdrift z) haGap]
  have htest : minimumOccupationTest a J S y - minimumOccupationTest a J S x ≤
      ∑ z ∈ I, (q' z - q z) := by
    change (∑ z ∈ S, min 1 (q' z)) - (∑ z ∈ S, min 1 (q z)) ≤ _
    rw [← Finset.sum_sub_distrib]
    dsimp only [I, activeSites]
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : q z ≤ 1
    · rw [if_pos hz, min_eq_right hz]
      linarith only [min_le_right (1 : ℝ) (q' z)]
    · rw [if_neg hz, min_eq_left (le_of_lt (lt_of_not_ge hz))]
      linarith only [min_le_left (1 : ℝ) (q' z)]
  have hminI : (if x j ∈ S then 1 / ((N : ℝ) + 1) else 0) ≤ ∑ z ∈ I, q z := by
    have hmin' := occupationMass_at_min_bounds ha hj hmin
    by_cases hz : x j ∈ S
    · rw [if_pos hz]
      exact hmin'.1.trans (Finset.single_le_sum (fun z _ => occupationMass_nonneg ha₀ J x z)
        (Finset.mem_filter.mpr ⟨hz, hmin'.2⟩))
    · rw [if_neg hz]
      exact Finset.sum_nonneg (fun z _ => occupationMass_nonneg ha₀ J x z)
  have hM : (∑ z ∈ I, ∑ i ∈ J, (a⁻¹ - a) / 2 * occupationWeight a N z (x i) * M i) =
      ∑ i, minimumOccupationCoeff a J S x i * M i := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ i ∈ (Finset.univ.filter fun i => i ∈ J),
          ∑ z ∈ I, (a⁻¹ - a) / 2 * occupationWeight a N z (x i) * M i := by simp
      _ = _ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ J
        · rw [if_pos hi, minimumOccupationCoeff, if_pos hi, ← Finset.sum_mul, ← Finset.mul_sum]
        · rw [if_neg hi, minimumOccupationCoeff, if_neg hi, zero_mul]
  have hsum := Finset.sum_le_sum (s := I) (fun z _ => hstep' z)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hM] at hsum
  change _ ≤ (∑ i, minimumOccupationCoeff a J S x i * M i) -
    d / ((N : ℝ) + 1) * (if x j ∈ S then 1 else 0)
  have hprod : d * (if x j ∈ S then 1 / ((N : ℝ) + 1) else 0) ≤
      d * ∑ z ∈ I, q z := mul_le_mul_of_nonneg_left hminI hd
  have he : d * (if x j ∈ S then 1 / ((N : ℝ) + 1) else 0) =
      d / ((N : ℝ) + 1) * (if x j ∈ S then 1 else 0) := by
    split_ifs <;> simp [div_eq_mul_inv]
  rw [he] at hprod
  linarith only [htest, hsum, hprod]

end Swarming.Diameter
