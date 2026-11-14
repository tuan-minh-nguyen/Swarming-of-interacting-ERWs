/-
# Maximal profile of the predictably truncated max-`H` martingale

The centred increment in `LocMoveLocal` has a uniform a.e. envelope `2B`.  Thus the
arbitrary-envelope Azuma engine gives an informative fixed-window profile at the local scale
`B = L^(1/16)`, unlike the crude `4n+10` profile in `LocMaxProfile`.
-/
import Swarm.LocMoveLocal
import Swarm.LocMaxProfile

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocMoveLocal

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocMoveMart

variable {N : ℕ}

/-- The local martingale increment shifted to a deterministic window start. -/
noncomputable def winLInc (p : ℝ) (m s : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (B : ℝ) : ℕ → Array N → ℝ :=
  fun k => LdM p m (s + k) J hJ B

lemma psum_winLInc (p : ℝ) (m s : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ) :
    ∀ k : ℕ, LocMart.psum (winLInc p m s J hJ B) k =
      fun U => Lcum p m (s + k) J hJ B U - Lcum p m s J hJ B U := by
  intro k
  induction k with
  | zero =>
    funext U
    simp [LocMart.psum_zero, Lcum]
  | succ k ih =>
    funext U
    rw [LocMart.psum_succ]
    have hstep : Lcum p m (s + (k + 1)) J hJ B U =
        Lcum p m (s + k) J hJ B U + LdM p m (s + k) J hJ B U := by
      simp only [Lcum]
      rw [show s + (k + 1) = (s + k) + 1 from rfl, Finset.sum_range_succ]
    have hpt := congrFun ih U
    rw [hpt, hstep]
    simp only [winLInc]
    ring

/-- A window sum of local martingale differences as a difference of cumulative sums. -/
lemma sum_Ico_LdM_eq (p : ℝ) (m s t : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (B : ℝ) (hst : s ≤ t) (U : Array N) :
    ∑ k ∈ Finset.Ico s t, LdM p m k J hJ B U =
      Lcum p m t J hJ B U - Lcum p m s J hJ B U := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hsum : (∑ k ∈ Finset.range (t - s), LdM p m (s + k) J hJ B U) =
      LocMart.psum (winLInc p m s J hJ B) (t - s) U := by
    simp only [LocMart.psum, winLInc]
  rw [hsum, psum_winLInc, Nat.add_sub_cancel' hst]

/-- Maximal deviation of the predictably truncated martingale over `[s,s+K]`.
The side condition is `ε ≤ 4KB`, and the variance proxy is `K(2B)^2`. -/
theorem measure_max_abs_Lcum_window_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) {B : ℝ} (hB : 0 < B)
    {s K : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) (hεB : ε ≤ 4 * (K : ℝ) * B) :
    (arrayMeasure N).real
        {U | ∃ k ≤ K, ε ≤ |Lcum p m (s + k) J hJ B U - Lcum p m s J hJ B U|}
      ≤ 2 * ((K : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (2 * B) ^ 2)) := by
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hS : 0 < (K : ℝ) * (2 * B) ^ 2 := by positivity
  have hprox : LocMax.proxy (fun _ : ℕ => 2 * B) K ≤ (K : ℝ) * (2 * B) ^ 2 := by
    simp only [LocMax.proxy, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact le_rfl
  have hεc : ∀ k < K, ε * (2 * B) ≤ 2 * ((K : ℝ) * (2 * B) ^ 2) := by
    intro k hk
    calc
      ε * (2 * B) ≤ (4 * (K : ℝ) * B) * (2 * B) :=
        mul_le_mul_of_nonneg_right hεB (by positivity)
      _ = 2 * ((K : ℝ) * (2 * B) ^ 2) := by ring
  have hmain := LocMax.measure_max_abs_psum_ge_le_ae (μ := arrayMeasure N)
    (ℱ := LocMax.shiftFilt N p m s) (ξ := winLInc p m s J hJ B)
    (c := fun _ : ℕ => 2 * B) (ε := ε) (n := K) (S := (K : ℝ) * (2 * B) ^ 2)
    hK hS hprox ?_ ?_ ?_ ?_ hε hεc
  · have hset : {U : Array N | ∃ k ≤ K, ε ≤ |LocMart.psum (winLInc p m s J hJ B) k U|} =
        {U : Array N | ∃ k ≤ K,
          ε ≤ |Lcum p m (s + k) J hJ B U - Lcum p m s J hJ B U|} := by
      ext U
      constructor
      · rintro ⟨k, hk, hdev⟩
        exact ⟨k, hk, by rwa [psum_winLInc] at hdev⟩
      · rintro ⟨k, hk, hdev⟩
        exact ⟨k, hk, by rwa [psum_winLInc]⟩
    rw [hset] at hmain
    convert hmain using 1 <;> ring
  · intro k hk
    exact stronglyMeasurable_LdM p m (s + k) J hJ B
  · intro k hk
    positivity
  · intro k hk
    filter_upwards [abs_LdM_le (p := p) (m := m) (n := s + k) hp hp1 hJ hB.le] with U hU
    exact hU
  · intro k hk
    exact condExp_LdM hp hp1 m (s + k) J hJ B

/-- The good separated window's drift failure has the same maximal-deviation bound. -/
theorem measure_good_window_dev_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) {B : ℝ} (hB : 0 < B)
    {s t : ℕ} (hst : s ≤ t) (hK : 1 ≤ t - s) {ε : ℝ} (hε : 0 < ε)
    (hεB : ε ≤ 4 * ((t - s : ℕ) : ℝ) * B) :
    (arrayMeasure N).real
        {U | (∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J B U}) ∧
          Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε}
      ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * ((t - s : ℕ) : ℝ) * (2 * B) ^ 2)) := by
  set K : ℕ := t - s with hKdef
  set A : Set (Array N) :=
    {U | (∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J B U}) ∧
      Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε} with hA
  set D : Set (Array N) :=
    {U | ∃ k ≤ K, ε ≤ |Lcum p m (s + k) J hJ B U - Lcum p m s J hJ B U|} with hD
  have hae := Mnow_good_window_ge (p := p) hp0 hp1 (m := m) J hJ B (s := s) (t := t) hst
  have hnull : (arrayMeasure N) {U | ¬
      ((∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J B U}) →
        ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, LdM p m k J hJ B U ≤
          Mnow p m t J hJ U - Mnow p m s J hJ U)} = 0 :=
    (MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hae
  have hsub : A ⊆ D ∪ {U | ¬
      ((∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J B U}) →
        ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, LdM p m k J hJ B U ≤
          Mnow p m t J hJ U - Mnow p m s J hJ U)} := by
    intro U hU
    by_cases hP : ((∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J B U}) →
      ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, LdM p m k J hJ B U ≤
        Mnow p m t J hJ U - Mnow p m s J hJ U)
    · refine Or.inl ?_
      have hineq := hP hU.1
      have hsum := sum_Ico_LdM_eq p m s t J hJ B hst U
      have hdev := hU.2
      rw [hsum] at hineq
      refine ⟨t - s, le_rfl, ?_⟩
      have hsk : s + (t - s) = t := Nat.add_sub_cancel' hst
      rw [hsk, abs_of_neg (show Lcum p m t J hJ B U - Lcum p m s J hJ B U < 0 by linarith [hdev])]
      linarith [hdev]
    · exact Or.inr hP
  calc
    (arrayMeasure N).real A ≤ (arrayMeasure N).real (D ∪ {U | ¬
      ((∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J B U}) →
        ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, LdM p m k J hJ B U ≤
          Mnow p m t J hJ U - Mnow p m s J hJ U)}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real D + (arrayMeasure N).real {U | ¬
      ((∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J B U}) →
        ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, LdM p m k J hJ B U ≤
          Mnow p m t J hJ U - Mnow p m s J hJ U)} := measureReal_union_le _ _
    _ = (arrayMeasure N).real D := by
      have hz : (arrayMeasure N).real {U | ¬
        ((∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J B U}) →
          ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, LdM p m k J hJ B U ≤
            Mnow p m t J hJ U - Mnow p m s J hJ U)} = 0 := by
        rw [measureReal_def, hnull]
        simp
      rw [hz, add_zero]
    _ ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * ((t - s : ℕ) : ℝ) * (2 * B) ^ 2)) := by
      simpa only [hKdef] using measure_max_abs_Lcum_window_le (p := p) hp0.le hp1.le m J hJ hB
        (s := s) (K := K) hK hε (by simpa only [hKdef] using hεB)

end LocMoveLocal
