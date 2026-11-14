/-
# Predictable local truncation of the separated maximum increment

The ordinary max-`H` martingale in `LocMoveMart` has the crude envelope `4n+10`.
This module replaces it on a good window by a position-filtration predictable step event.
The event asks for separation and for the two possible frozen-potential steps of every
walker in the separated group to have size at most `B`.  Truncating before centring makes
both the raw increment and its conditional compensator bounded by `B`, so the centred
increment has envelope `2B`.
-/
import Swarm.LocMoveMart
import Mathlib.MeasureTheory.Order.Group.Lattice
import Swarm.LocMaxVar

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocMoveLocal

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocMoveMart

variable {N : ℕ}

/-- The two possible steps of the frozen group potential at every walker of `J` are bounded. -/
def StepOk (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (B : ℝ) (U : Array N) : Prop :=
  ∀ j ∈ J,
    |HA p m U n Jᶜ (X p m U n j + 1) - HA p m U n Jᶜ (X p m U n j)| ≤ B ∧
    |HA p m U n Jᶜ (X p m U n j - 1) - HA p m U n Jᶜ (X p m U n j)| ≤ B

/-- Separation together with the predictable local step bound. -/
def GoodStep (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (B : ℝ) (U : Array N) : Prop :=
  SepSet p m n Jᶜ J U ∧ StepOk p m n J B U

/-- The frozen potential at a current position plus one is position-filtration measurable. -/
theorem measurable_HA_X_add_one_posFilt (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (j : Fin N) :
    Measurable[posFilt N p m n]
      (fun U : Array N => HA p m U n Jᶜ (X p m U n j + 1)) := by
  refine measurable_HA_random_site' p m n Jᶜ (fun U => X p m U n j + 1) ?_ ?_ (n + 1) ?_
  · exact (measurable_pos_posFilt p m j le_rfl).add measurable_const
  · exact fun u => SwarmM3.measurable_hfix_wA_posFilt p m n Jᶜ u
  · intro U
    have h := SwarmM3.abs_X_le p m U n j
    rw [abs_le] at h ⊢
    push_cast
    omega

/-- The frozen potential at a current position minus one is position-filtration measurable. -/
theorem measurable_HA_X_sub_one_posFilt (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (j : Fin N) :
    Measurable[posFilt N p m n]
      (fun U : Array N => HA p m U n Jᶜ (X p m U n j - 1)) := by
  refine measurable_HA_random_site' p m n Jᶜ (fun U => X p m U n j - 1) ?_ ?_ (n + 1) ?_
  · exact (measurable_pos_posFilt p m j le_rfl).sub measurable_const
  · exact fun u => SwarmM3.measurable_hfix_wA_posFilt p m n Jᶜ u
  · intro U
    have h := SwarmM3.abs_X_le p m U n j
    rw [abs_le] at h ⊢
    push_cast
    omega

/-- The local step event is measurable before the next transition. -/
theorem measurableSet_goodStep (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (B : ℝ) :
    MeasurableSet[posFilt N p m n] {U : Array N | GoodStep p m n J B U} := by
  have hplus : ∀ j : Fin N, MeasurableSet[posFilt N p m n]
      {U : Array N |
        |HA p m U n Jᶜ (X p m U n j + 1) - HA p m U n Jᶜ (X p m U n j)| ≤ B} := by
    intro j
    letI : MeasurableSpace (Array N) := posFilt N p m n
    exact measurableSet_le
      ((measurable_HA_X_add_one_posFilt p m n J j).sub
        (measurable_HA_X_posFilt p m n Jᶜ j)).abs measurable_const
  have hminus : ∀ j : Fin N, MeasurableSet[posFilt N p m n]
      {U : Array N |
        |HA p m U n Jᶜ (X p m U n j - 1) - HA p m U n Jᶜ (X p m U n j)| ≤ B} := by
    intro j
    letI : MeasurableSpace (Array N) := posFilt N p m n
    exact measurableSet_le
      ((measurable_HA_X_sub_one_posFilt p m n J j).sub
        (measurable_HA_X_posFilt p m n Jᶜ j)).abs measurable_const
  have hsteps : MeasurableSet[posFilt N p m n] {U : Array N | StepOk p m n J B U} := by
    have heq : {U : Array N | StepOk p m n J B U} =
        ⋂ j ∈ J, {U : Array N |
          |HA p m U n Jᶜ (X p m U n j + 1) - HA p m U n Jᶜ (X p m U n j)| ≤ B} ∩
          {U : Array N |
            |HA p m U n Jᶜ (X p m U n j - 1) - HA p m U n Jᶜ (X p m U n j)| ≤ B} := by
      ext U
      simp only [StepOk, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [heq]
    exact Finset.measurableSet_biInter _ (fun j _ => (hplus j).inter (hminus j))
  exact (measurableSet_sepSet p m n Jᶜ J).inter hsteps

/-- On the good step event the maximum increment has the local bound `B`. -/
theorem abs_Mdiff_of_goodStep {p : ℝ} {m n : ℕ} {J : Finset (Fin N)}
    (hJ : J.Nonempty) {B : ℝ} {U : Array N} (hU : GoodStep p m n J B U) :
    |Mdiff p m n J hJ U| ≤ B := by
  change |Mnext p m n J hJ U - Mnow p m n J hJ U| ≤ B
  apply SwarmQVariance.abs_sup'_sub_sup'_le hJ
  intro j hj
  rcases SwarmQVariance.X_succ_sub_X p m U n j with h | h
  · rw [h]
    exact (hU.2 j hj).1
  · rw [h]
    exact (hU.2 j hj).2

/-- `(hcomp)` turns a leader bound at the current and neighbouring sites into `GoodStep`. -/
theorem goodStep_of_sep_of_leader_bound {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    {m n : ℕ} {J : Finset (Fin N)} (hJ : J.Nonempty) {i : Fin N} (hi : i ∈ Jᶜ)
    {B : ℝ} {U : Array N} (hsep : SepSet p m n Jᶜ J U)
    (hleader : ∀ j ∈ J, ∀ z ∈
      ({X p m U n j, X p m U n j + 1, X p m U n j - 1} : Finset ℤ),
      hfix (omegaN p m U i) z.toNat ≤ B) :
    GoodStep p m n J B U := by
  refine ⟨hsep, ?_⟩
  have hbelow : ∀ j ∈ J, ∀ z ∈ ({X p m U n j, X p m U n j + 1, X p m U n j - 1} : Finset ℤ),
      ((z.toNat : ℕ) : ℤ) < runMax p m U i n := by
    intro j hj z hz
    have hsepj := hsep.2 i hi j hj
    have hcur : X p m U n j ≤ runMax p m U j n := le_runMax_pos p m U n j
    have hile : X p m U n i ≤ runMax p m U i n := le_runMax_pos p m U n i
    have hzle : z ≤ X p m U n j + 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> omega
    have hznonneg : 0 ≤ z → ((z.toNat : ℕ) : ℤ) < runMax p m U i n := by
      intro hz0
      rw [Int.toNat_of_nonneg hz0]
      omega
    by_cases hz0 : 0 ≤ z
    · exact hznonneg hz0
    · rw [Int.toNat_eq_zero.mpr (by omega)]
      simp only [Nat.cast_zero]
      have hRj : 0 ≤ runMax p m U j n := SwarmQVariance.runMax_nonneg' p m U j n
      omega
  have hone : ∀ j ∈ J, ∀ z ∈ ({X p m U n j, X p m U n j + 1, X p m U n j - 1} : Finset ℤ),
      hfix (wA p m U n Jᶜ) z.toNat ≤ B := by
    intro j hj z hz
    have hlt := hbelow j hj z hz
    exact (hcomp_h p m U hp hp1 hi hlt).trans (hleader j hj z hz)
  intro j hj
  constructor
  · apply (SwarmQVariance.abs_HZ_step_le (wA_pos p m U hp n Jᶜ)
      (wA_le_one p m U hp1 n Jᶜ) (show X p m U n j + 1 = X p m U n j + 1 ∨
        X p m U n j + 1 = X p m U n j - 1 ∨ X p m U n j + 1 = X p m U n j from Or.inl rfl)).trans
    exact max_le (hone j hj _ (by simp)) (hone j hj _ (by simp))
  · apply (SwarmQVariance.abs_HZ_step_le (wA_pos p m U hp n Jᶜ)
      (wA_le_one p m U hp1 n Jᶜ) (show X p m U n j - 1 = X p m U n j + 1 ∨
        X p m U n j - 1 = X p m U n j - 1 ∨ X p m U n j - 1 = X p m U n j from
          Or.inr (Or.inl rfl))).trans
    exact max_le (hone j hj _ (by simp)) (hone j hj _ (by simp))

/-- The raw increment truncated by the predictable good-step event. -/
noncomputable def Lraw (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (B : ℝ) (U : Array N) : ℝ :=
  {U | GoodStep p m n J B U}.indicator (Mdiff p m n J hJ) U

/-- Its compensator. -/
noncomputable def Lcomp (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (B : ℝ) (U : Array N) : ℝ :=
  condExp (posFilt N p m n) (arrayMeasure N) (Lraw p m n J hJ B) U

/-- The centred truncated increment. -/
noncomputable def LdM (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (B : ℝ) (U : Array N) : ℝ :=
  Lraw p m n J hJ B U - Lcomp p m n J hJ B U

/-- The cumulative centred truncated increments. -/
noncomputable def Lcum (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (B : ℝ) (U : Array N) : ℝ :=
  ∑ k ∈ Finset.range n, LdM p m k J hJ B U

theorem abs_Lraw_le {p : ℝ} {m n : ℕ} {J : Finset (Fin N)} (hJ : J.Nonempty)
    {B : ℝ} (hB : 0 ≤ B) (U : Array N) :
    |Lraw p m n J hJ B U| ≤ B := by
  by_cases hU : U ∈ {U : Array N | GoodStep p m n J B U}
  · rw [Lraw, Set.indicator_of_mem hU]
    exact abs_Mdiff_of_goodStep hJ hU
  · rw [Lraw, Set.indicator_of_notMem hU, abs_zero]
    exact hB

theorem stronglyMeasurable_Lraw_succ (p : ℝ) (m n : ℕ) (J : Finset (Fin N))
    (hJ : J.Nonempty) (B : ℝ) :
    StronglyMeasurable[posFilt N p m (n + 1)] (Lraw p m n J hJ B) := by
  have hdiff : StronglyMeasurable[posFilt N p m (n + 1)] (Mdiff p m n J hJ) :=
    stronglyMeasurable_Mdiff_succ p m n J hJ
  exact hdiff.indicator (((posFilt N p m).mono (Nat.le_succ n)) _
    (measurableSet_goodStep p m n J B))

theorem integrable_Lraw {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ) :
    Integrable (Lraw p m n J hJ B) (arrayMeasure N) := by
  have hdiff : Integrable (Mdiff p m n J hJ) (arrayMeasure N) :=
    (integrable_Mnext hp hp1 m n J hJ).sub (integrable_Mnow hp hp1 m n J hJ)
  exact hdiff.indicator (((posFilt N p m).le n) _ (measurableSet_goodStep p m n J B))

theorem integrable_Lcomp {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ) :
    Integrable (Lcomp p m n J hJ B) (arrayMeasure N) := by
  have hint := integrable_Lraw hp hp1 m n J hJ B
  exact integrable_condExp (μ := arrayMeasure N) (m := posFilt N p m n)

theorem integrable_LdM {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ) :
    Integrable (LdM p m n J hJ B) (arrayMeasure N) :=
  (integrable_Lraw hp hp1 m n J hJ B).sub (integrable_Lcomp hp hp1 m n J hJ B)

/-- The compensator has the same global bound, by conditional Jensen. -/
theorem abs_Lcomp_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    {m n : ℕ} {J : Finset (Fin N)} (hJ : J.Nonempty) {B : ℝ} (hB : 0 ≤ B) :
    ∀ᵐ U ∂(arrayMeasure N), |Lcomp p m n J hJ B U| ≤ B := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have habs : |condExp (posFilt N p m n) (arrayMeasure N) (Lraw p m n J hJ B)|
      ≤ᵐ[arrayMeasure N]
      condExp (posFilt N p m n) (arrayMeasure N) (fun U => |Lraw p m n J hJ B U|) :=
    abs_condExp_ae_le_condExp_abs _
  have hcint : Integrable (fun _ : Array N => B) (arrayMeasure N) := integrable_const _
  have hconst : condExp (posFilt N p m n) (arrayMeasure N) (fun _ : Array N => B) =
      fun _ => B := condExp_const ((posFilt N p m).le n) B
  have hbound : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => |Lraw p m n J hJ B U|) ≤ᵐ[arrayMeasure N] fun _ => B := by
    have hmono := condExp_mono (μ := arrayMeasure N) (m := posFilt N p m n)
      (f := fun U => |Lraw p m n J hJ B U|) (g := fun _ => B)
      (integrable_Lraw hp hp1 m n J hJ B).abs hcint
      (Filter.Eventually.of_forall (abs_Lraw_le hJ hB))
    rw [hconst] at hmono
    exact hmono
  exact habs.trans hbound

/-- Predictable truncation gives the centred envelope `2B`. -/
theorem abs_LdM_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    {m n : ℕ} {J : Finset (Fin N)} (hJ : J.Nonempty) {B : ℝ} (hB : 0 ≤ B) :
    ∀ᵐ U ∂(arrayMeasure N), |LdM p m n J hJ B U| ≤ 2 * B := by
  filter_upwards [abs_Lcomp_le (p := p) (m := m) (n := n) hp hp1 hJ hB] with U hU
  have hraw : |Lraw p m n J hJ B U| ≤ B := abs_Lraw_le hJ hB U
  have htri : |Lraw p m n J hJ B U - Lcomp p m n J hJ B U| ≤
      |Lraw p m n J hJ B U| + |Lcomp p m n J hJ B U| := abs_sub _ _
  exact htri.trans (by linarith)

/-- The compensator is at least one throughout the predictable good-step event. -/
theorem Lcomp_ge_good {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ) :
    (fun U => {U : Array N | GoodStep p m n J B U}.indicator (fun _ => (1 : ℝ)) U)
      ≤ᵐ[arrayMeasure N] Lcomp p m n J hJ B :=
  LocMove.condExp_indicator_Mnext_sub_Mnow_ge_one hp0 hp1 m n J hJ
    (measurableSet_goodStep p m n J B) (fun _ h => h.1)

/-- The good-step drift inequality holds simultaneously at all times, almost surely. -/
theorem Lcomp_ge_good_all {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ n : ℕ,
      {U : Array N | GoodStep p m n J B U}.indicator (fun _ => (1 : ℝ)) U ≤
        Lcomp p m n J hJ B U :=
  MeasureTheory.ae_all_iff.2 fun n => Lcomp_ge_good hp0 hp1 m n J hJ B

/-- The truncated centred increment is adapted at the next time. -/
theorem stronglyMeasurable_LdM (p : ℝ) (m n : ℕ) (J : Finset (Fin N))
    (hJ : J.Nonempty) (B : ℝ) :
    StronglyMeasurable[posFilt N p m (n + 1)] (LdM p m n J hJ B) := by
  letI : MeasurableSpace (Array N) := posFilt N p m (n + 1)
  have hraw := stronglyMeasurable_Lraw_succ p m n J hJ B
  have hce : StronglyMeasurable[posFilt N p m n] (Lcomp p m n J hJ B) :=
    stronglyMeasurable_condExp
  exact hraw.sub (SwarmJointDrift.stronglyMeasurable_mono_filt hce
    ((posFilt N p m).mono (Nat.le_succ n)))

/-- The truncated increment is centred. -/
theorem condExp_LdM {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ) :
    condExp (posFilt N p m n) (arrayMeasure N) (LdM p m n J hJ B) =ᵐ[arrayMeasure N] 0 := by
  have hraw := integrable_Lraw hp hp1 m n J hJ B
  have hcomp := integrable_Lcomp hp hp1 m n J hJ B
  have hsub : condExp (posFilt N p m n) (arrayMeasure N) (LdM p m n J hJ B) =ᵐ[arrayMeasure N]
      condExp (posFilt N p m n) (arrayMeasure N) (Lraw p m n J hJ B) -
        condExp (posFilt N p m n) (arrayMeasure N)
          (fun U => condExp (posFilt N p m n) (arrayMeasure N) (Lraw p m n J hJ B) U) :=
    condExp_sub hraw hcomp _
  have hpull : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => condExp (posFilt N p m n) (arrayMeasure N) (Lraw p m n J hJ B) U) =
      fun U => condExp (posFilt N p m n) (arrayMeasure N) (Lraw p m n J hJ B) U :=
    condExp_of_stronglyMeasurable ((posFilt N p m).le n) stronglyMeasurable_condExp hcomp
  refine hsub.trans ?_
  rw [hpull]
  filter_upwards with U
  simp

/-- The cumulative truncated process is adapted. -/
theorem stronglyAdapted_Lcum (p : ℝ) (m : ℕ) (J : Finset (Fin N))
    (hJ : J.Nonempty) (B : ℝ) :
    StronglyAdapted (posFilt N p m) (fun n U => Lcum p m n J hJ B U) := by
  intro n
  show StronglyMeasurable[posFilt N p m n]
    (fun U => ∑ k ∈ Finset.range n, LdM p m k J hJ B U)
  have hsum : (fun U : Array N => ∑ k ∈ Finset.range n, LdM p m k J hJ B U) =
      ∑ k ∈ Finset.range n, fun U => LdM p m k J hJ B U := by
    funext U
    rw [Finset.sum_apply]
  rw [hsum]
  refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
  exact SwarmJointDrift.stronglyMeasurable_mono_filt (stronglyMeasurable_LdM p m k J hJ B)
    ((posFilt N p m).mono (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))

/-- The cumulative truncated process is integrable. -/
theorem integrable_Lcum {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ) :
    Integrable (Lcum p m n J hJ B) (arrayMeasure N) := by
  exact integrable_finsetSum _ fun k _ => integrable_LdM hp hp1 m k J hJ B

/-- The cumulative process satisfies the martingale recursion. -/
theorem condExp_Lcum_succ {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ) :
    condExp (posFilt N p m n) (arrayMeasure N) (Lcum p m (n + 1) J hJ B) =ᵐ[arrayMeasure N]
      Lcum p m n J hJ B := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have heq : Lcum p m (n + 1) J hJ B = fun U => Lcum p m n J hJ B U + LdM p m n J hJ B U := by
    funext U
    simp only [Lcum, Finset.sum_range_succ]
  have hQ : condExp (posFilt N p m n) (arrayMeasure N) (Lcum p m (n + 1) J hJ B) =ᵐ[arrayMeasure N]
      condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => Lcum p m n J hJ B U + LdM p m n J hJ B U) :=
    condExp_congr_ae (Filter.EventuallyEq.of_eq heq)
  have h1 : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => Lcum p m n J hJ B U + LdM p m n J hJ B U) =ᵐ[arrayMeasure N]
      condExp (posFilt N p m n) (arrayMeasure N) (Lcum p m n J hJ B) +
        condExp (posFilt N p m n) (arrayMeasure N) (LdM p m n J hJ B) :=
    condExp_add (integrable_Lcum hp hp1 m n J hJ B) (integrable_LdM hp hp1 m n J hJ B) _
  have h2 : condExp (posFilt N p m n) (arrayMeasure N) (Lcum p m n J hJ B) =
      Lcum p m n J hJ B :=
    condExp_of_stronglyMeasurable ((posFilt N p m).le n) (stronglyAdapted_Lcum p m J hJ B n)
      (integrable_Lcum hp hp1 m n J hJ B)
  have h3 := condExp_LdM hp hp1 m n J hJ B
  refine hQ.trans (h1.trans ?_)
  rw [h2]
  filter_upwards [h3] with U hU
  simp only [Pi.add_apply, hU, Pi.zero_apply, add_zero]

/-- The predictably truncated maximum process is a genuine martingale after centring. -/
theorem martingale_Lcum {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ) :
    Martingale (fun n U => Lcum p m n J hJ B U) (posFilt N p m) (arrayMeasure N) :=
  martingale_nat (stronglyAdapted_Lcum p m J hJ B)
    (fun n => integrable_Lcum hp hp1 m n J hJ B)
    (fun n => (condExp_Lcum_succ hp hp1 m n J hJ B).symm)

/-- On a wholly good separated window, the literal maximum grows by the window length plus the
truncated martingale sum.  There is no off-separation remainder. -/
theorem Mnow_good_window_ge {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) (B : ℝ) {s t : ℕ} (hst : s ≤ t) :
    ∀ᵐ U ∂(arrayMeasure N),
      (∀ k ∈ Finset.Ico s t, U ∈ {U : Array N | GoodStep p m k J B U}) →
      ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, LdM p m k J hJ B U ≤
        Mnow p m t J hJ U - Mnow p m s J hJ U := by
  filter_upwards [Lcomp_ge_good_all hp0 hp1 m J hJ B] with U hU hgood
  have hterm : ∀ k ∈ Finset.Ico s t,
      Mnow p m (k + 1) J hJ U - Mnow p m k J hJ U =
        LdM p m k J hJ B U + Lcomp p m k J hJ B U := by
    intro k hk
    have hmem := hgood k hk
    rw [Mnow_succ_eq_Mnext_of_sep hp0.le hp1.le (m := m) (n := k) J hJ hmem.1]
    change Mnext p m k J hJ U - Mnow p m k J hJ U = _
    rw [LdM, Lraw, Set.indicator_of_mem (s := {U : Array N | GoodStep p m k J B U}) hmem]
    rw [Mdiff]
    ring
  have hsum : (∑ k ∈ Finset.Ico s t, LdM p m k J hJ B U) +
      ∑ k ∈ Finset.Ico s t, Lcomp p m k J hJ B U =
        Mnow p m t J hJ U - Mnow p m s J hJ U := by
    rw [← Finset.sum_add_distrib, ← Mnow_telescope m J hJ hst U]
    exact (Finset.sum_congr rfl hterm).symm
  have hdrift : ((t - s : ℕ) : ℝ) ≤ ∑ k ∈ Finset.Ico s t, Lcomp p m k J hJ B U := by
    have hle : (∑ k ∈ Finset.Ico s t, (1 : ℝ)) ≤
        ∑ k ∈ Finset.Ico s t, Lcomp p m k J hJ B U := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hmem := hgood k hk
      simpa only [Set.indicator_of_mem (s := {U : Array N | GoodStep p m k J B U}) hmem] using hU k
    rwa [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one] at hle
  linarith

end LocMoveLocal
