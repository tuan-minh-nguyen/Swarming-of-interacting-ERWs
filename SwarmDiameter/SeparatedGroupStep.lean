import Swarm.WindowIncrement
import Swarm.RecClockLocgroup
import Swarm.QplOsc

open Filter Finset MeasureTheory Set
open Swarming.Uniform Swarming.Trajectory SwarmJointDrift SwarmQVariance SepGroup.Model
open Swarming.Group SiteWindow
open scoped ENNReal

set_option autoImplicit false

namespace Swarming.Diameter

variable {N : ℕ}

/-- Changing the positions by one step while keeping the group potential
fixed at time `n` costs at most twice the bound on its local increments. -/
theorem abs_group_step_fixed_potential_le
    {p : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    {A : ℕ} {B : ℝ} {U : Array N}
    (hpos : ∀ k ∈ I ∪ J, A + 1 ≤ (X p m U n k).toNat)
    (hB : EfixWin p m n J (I ∪ J) (hI.mono Finset.subset_union_left) A U ≤ B) :
    |Anext p m n I J U - Mnext p m n J hJ U - WA p m U n I J hI hJ| ≤ 2 * B := by
  let f (k : Fin N) := HA p m U n Jᶜ (X p m U (n + 1) k)
  let g (k : Fin N) := HA p m U n Jᶜ (X p m U n k)
  have hstep (k : Fin N) (hk : k ∈ I ∪ J) : |f k - g k| ≤ B := by
    have hlo := hpos k hk
    have hsucc : A ≤ (X p m U (n + 1) k).toNat + 1 := by
      have h := pos_sub_one_le_succ p m U n k
      change X p m U n k - 1 ≤ X p m U (n + 1) k at h
      omega
    exact (abs_HA_pos_step_le_EfixWin hp₀ hp₁ (hI.mono Finset.subset_union_left) U hk
      (by omega) hsucc).trans hB
  have ha : |average I f - average I g| ≤ B := by
    rw [← average_sub_group]
    exact abs_average_le_of_bound hI (fun k hk => hstep k (Finset.mem_union_left _ hk))
  have hm : |maximumOn J hJ f - maximumOn J hJ g| ≤ B :=
    abs_sup'_sub_sup'_le (s := J) (hs := hJ) (fun k hk => hstep k (Finset.mem_union_right _ hk))
  change |average I f - maximumOn J hJ f - (average I g - maximumOn J hJ g)| ≤ 2 * B
  rw [show average I f - maximumOn J hJ f - (average I g - maximumOn J hJ g) =
    (average I f - average I g) - (maximumOn J hJ f - maximumOn J hJ g) by ring]
  exact (abs_sub _ _).trans (by linarith)

/-- The centred increment with the weights fixed at time `n`, restricted
before centring to a predictable subset of the separation event. -/
noncomputable def centeredGroupStep (p : ℝ) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (S : Set (Array N)) :
    Array N → ℝ :=
  let ξ := S.indicator (fun U =>
    Anext p m n I J U - Mnext p m n J hJ U - WA p m U n I J hI hJ)
  ξ - condExp (posFilt N p m n) (arrayMeasure N) ξ

/-- The centred increment has a linear bound in the maximum local
potential increment. Its sum, with the conditional drift term, bounds
the change of the group observable on separated intervals. -/
theorem ae_centeredGroupStep_bounds
    {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    {S : Set (Array N)} (hS : MeasurableSet[posFilt N p m n] S)
    (hsep : S ⊆ {U | SepSet p m n I J U})
    {A : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hpos : ∀ U ∈ S, ∀ k ∈ I ∪ J, A + 1 ≤ (X p m U n k).toNat)
    (hfix : ∀ U ∈ S, EfixWin p m n J (I ∪ J) (hI.mono Finset.subset_union_left) A U ≤ B) :
    ∀ᵐ U ∂(arrayMeasure N), |centeredGroupStep p m n I J hI hJ S U| ≤ 4 * B ∧
      (U ∈ S → WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ
        ≤ centeredGroupStep p m n I J hI hJ S U + Cavg p m n I J U) := by
  let ξ := S.indicator (fun U =>
    Anext p m n I J U - Mnext p m n J hJ U - WA p m U n I J hI hJ)
  let μ := arrayMeasure N
  let F := posFilt N p m
  have hSi : MeasurableSet S := F.le n S hS
  have hξi : Integrable ξ μ :=
    (((integrable_Anext hp₀.le hp₁.le m n I J).sub
      (integrable_Mnext hp₀.le hp₁.le m n J hJ)).sub
      (integrable_WA hp₀.le hp₁.le m n I J hI hJ)).indicator hSi
  have hξ (U : Array N) : |ξ U| ≤ 2 * B := by
    by_cases hU : U ∈ S
    · dsimp only [ξ]
      rw [Set.indicator_of_mem hU]
      exact abs_group_step_fixed_potential_le hp₀.le hp₁.le I J hI hJ (hpos U hU) (hfix U hU)
    · dsimp only [ξ]
      rw [Set.indicator_of_notMem hU, abs_zero]
      positivity
  have he := abs_condExp_ae_le_condExp_abs (μ := μ) (m := F n) (f := ξ)
  have hμ : condExp (F n) μ (|ξ|) ≤ᵐ[μ] fun _ => 2 * B := by
    have h := condExp_mono (m := F n) hξi.abs
      (integrable_const (μ := μ) (2 * B)) (Filter.Eventually.of_forall hξ)
    rwa [condExp_const (F.le n)] at h
  have hd := condExp_indicator_drift_le_cavg hp₀ hp₁ m n I J hI hJ hS hsep
  filter_upwards [he, hμ, hd] with U h₁ h₂ h₃
  have hb := h₁.trans h₂
  change |condExp (F n) μ ξ U| ≤ 2 * B at hb
  change |ξ U - condExp (F n) μ ξ U| ≤ 4 * B ∧ _
  constructor
  · exact (abs_sub _ _).trans (by linarith [hξ U])
  · intro hU
    have hstep := WA_step p m U hp₀.le hp₁.le hI hJ (hsep hU)
    change WA p m U (n + 1) I J hI hJ ≤ Anext p m n I J U - Mnext p m n J hJ U at hstep
    change condExp (F n) μ ξ U ≤ S.indicator (Cavg p m n I J) U at h₃
    rw [Set.indicator_of_mem hU] at h₃
    change _ ≤ ξ U - condExp (F n) μ ξ U + _
    have hξU : ξ U = Anext p m n I J U - Mnext p m n J hJ U - WA p m U n I J hI hJ :=
      Set.indicator_of_mem hU _
    rw [hξU]
    linarith

private theorem centeredGroupStep_martingaleDifference
    {p : ℝ} (hp₀ : (1 : ℝ) / 2 ≤ p) (hp₁ : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    {S : Set (Array N)} (hS : MeasurableSet[posFilt N p m n] S) :
    StronglyMeasurable[posFilt N p m (n + 1)] (centeredGroupStep p m n I J hI hJ S) ∧
      Integrable (centeredGroupStep p m n I J hI hJ S) (arrayMeasure N) ∧
      (arrayMeasure N)[centeredGroupStep p m n I J hI hJ S | posFilt N p m n]
        =ᵐ[arrayMeasure N] 0 := by
  let ξ := S.indicator (fun U =>
    Anext p m n I J U - Mnext p m n J hJ U - WA p m U n I J hI hJ)
  let μ := arrayMeasure N
  let F := posFilt N p m
  have hξi : Integrable ξ μ :=
    (((integrable_Anext hp₀ hp₁ m n I J).sub
      (integrable_Mnext hp₀ hp₁ m n J hJ)).sub
      (integrable_WA hp₀ hp₁ m n I J hI hJ)).indicator (F.le n S hS)
  have hmono := F.mono (Nat.le_succ n)
  have hnext (i : Fin N) :
      Measurable[F (n + 1)] (fun U => HA p m U n Jᶜ (X p m U (n + 1) i)) :=
    measurable_HA_random_site' p m n Jᶜ (fun U => X p m U (n + 1) i)
      (measurable_pos_posFilt p m i le_rfl)
      (fun u => (SwarmM3.measurable_hfix_wA_posFilt (N := N) p m n Jᶜ u).mono hmono le_rfl)
      (n + 1) (fun U => SwarmM3.abs_X_le p m U (n + 1) i)
  have hA : Measurable[F (n + 1)] (Anext p m n I J) := by
    unfold Anext Swarming.Group.average
    exact (Finset.measurable_sum I (fun i _ => hnext i)).div_const _
  have hM : Measurable[F (n + 1)] (Mnext p m n J hJ) := by
    rw [show Mnext p m n J hJ = J.sup' hJ
        (fun j U => HA p m U n Jᶜ (X p m U (n + 1) j)) by
      funext U
      rw [Finset.sup'_apply]
      rfl]
    exact @Finset.measurable_sup' ℝ _ (Array N) (F (n + 1)) _ _ (Fin N) J hJ _ (fun i _ => hnext i)
  have hW := (measurable_WA_posFilt p m n I J hI hJ).mono hmono le_rfl
  have hξm : StronglyMeasurable[F (n + 1)] ξ :=
    (((hA.sub hM).sub hW).indicator (hmono S hS)).stronglyMeasurable
  have hce : StronglyMeasurable[F n] (μ[ξ | F n]) := stronglyMeasurable_condExp
  have hcei : Integrable (μ[ξ | F n]) μ := integrable_condExp
  refine ⟨hξm.sub (hce.mono hmono), hξi.sub hcei, ?_⟩
  change μ[ξ - μ[ξ | F n] | F n] =ᵐ[μ] 0
  refine (condExp_sub hξi hcei (F n)).trans ?_
  rw [condExp_of_stronglyMeasurable (F.le n) hce hcei, sub_self]

/-- A maximal deviation bound for the accumulated centred group increments.
Each predictable event restricts the increment to separated groups with a
local potential bound. The factor depends on the length of the record interval. -/
theorem measureReal_record_centeredGroupStep_le
    {p : ℝ} (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) {m : ℕ}
    [Nonempty (Fin N)] (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (r L : ℕ) {S : ℕ → Set (Array N)}
    (hS : ∀ t, MeasurableSet[posFilt N p m t] (S t))
    (hsep : ∀ t, S t ⊆ {U | SepSet p m t I J U})
    {A : ℕ} {B : ℝ} (hB : 0 < B)
    (hpos : ∀ t, ∀ U ∈ S t, ∀ k ∈ I ∪ J, A + 1 ≤ (X p m U t k).toNat)
    (hfix : ∀ t, ∀ U ∈ S t, EfixWin p m t J (I ∪ J) (hI.mono Finset.subset_union_left) A U ≤ B)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real (RecClockLG.recordCarrier p m r L ∩
      StoppedWindow.stoppedMax (LocMart.psum (fun t => centeredGroupStep p m t I J hI hJ (S t)))
        (fun U => SwarmRecordMeas.Actual.recTimeA p m U r) n ε)
      ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (n : ℝ) * (4 * B) ^ 2)) := by
  let μ := arrayMeasure N
  let F := posFilt N p m
  let ξ (t : ℕ) := centeredGroupStep p m t I J hI hJ (S t)
  let η := QplOsc.ptruncAe (fun _ => (Set.univ : Set (Array N))) (4 * B) ξ
  have hξ (t : ℕ) := centeredGroupStep_martingaleDifference hp₀.le hp₁.le m t I J hI hJ (hS t)
  have hG (t : ℕ) : MeasurableSet[F t] (Set.univ : Set (Array N)) := MeasurableSet.univ
  have hηm (t : ℕ) : StronglyMeasurable[F (t + 1)] (η t) :=
    QplOsc.stronglyMeasurable_ptruncAe hG (fun k => (hξ k).1) t
  have hηi (t : ℕ) : Integrable (η t) μ :=
    QplOsc.integrable_ptruncAe hG (fun k => (hξ k).1) (fun k => (hξ k).2.1) t
  have hη (t : ℕ) : η t =ᵐ[μ] ξ t := by
    have h := ae_centeredGroupStep_bounds hp₀ hp₁ I J hI hJ (hS t) (hsep t)
      hB.le (hpos t) (hfix t)
    have hbd : ∀ᵐ U ∂μ, U ∈ (Set.univ : Set (Array N)) → |ξ t U| ≤ 4 * B :=
      h.mono fun _ hU _ => hU.1
    simpa only [η, QplOsc.ptrunc, Set.indicator_univ] using QplOsc.ae_ptruncAe_eq_ptrunc (G := fun _ => Set.univ) (ξ := ξ) (k := t) hbd
  let Q := LocMart.psum η
  have hstep (t : ℕ) : StoppedWindow.increments Q t = η t := by
    funext U
    change Q (t + 1) U - Q t U = η t U
    dsimp only [Q]
    rw [LocMart.psum_succ, add_sub_cancel_left]
  have hQi (t : ℕ) : Integrable (Q t) μ := by
    change Integrable (fun U => ∑ k ∈ Finset.range t, η k U) μ
    exact integrable_finsetSum _ (fun k _ => hηi k)
  have htail := StoppedWindow.measureReal_band_stoppedMax_le
    (μ := μ) (ℱ := F) (Q := Q)
    (σ := fun U => SwarmRecordMeas.Actual.recTimeA p m U r)
    (B := fun s => RecClockLG.recordBand (N := N) p m r L s)
    (G := RecClockLG.recordCarrier p m r L)
    (LocMart.stronglyMeasurable_psum hηm) hQi
    (fun t => by rw [hstep]; exact (condExp_congr_ae (hη t)).trans (hξ t).2.2)
    (show 0 < 4 * B by positivity)
    (fun t U => by
      have he := congrFun (hstep t) U
      change Q (t + 1) U - Q t U = η t U at he
      rw [he]
      exact QplOsc.abs_ptruncAe_le (by positivity) t U)
    (RecClockLG.measurableSet_recordBand p m r L)
    (fun _ _ h => RecClockLG.disjoint_recordBand h)
    (RecClockLG.subset_iUnion_recordBand p m r L)
    (RecClockLG.carrier_inter_band_subset_clock_eq p m r L) hn hε
  have hηall : ∀ᵐ U ∂μ, ∀ t, η t U = ξ t U := ae_all_iff.mpr hη
  have heq : (RecClockLG.recordCarrier p m r L ∩
      StoppedWindow.stoppedMax (LocMart.psum ξ)
        (fun U => SwarmRecordMeas.Actual.recTimeA p m U r) n ε : Set (Array N))
      =ᵐ[μ] (RecClockLG.recordCarrier p m r L ∩
        StoppedWindow.stoppedMax Q (fun U => SwarmRecordMeas.Actual.recTimeA p m U r) n ε : Set (Array N)) := by
    filter_upwards [hηall] with U hU
    have hps (t : ℕ) : Q t U = LocMart.psum ξ t U :=
      Finset.sum_congr rfl fun k _ => hU k
    apply propext
    let σ := SwarmRecordMeas.Actual.recTimeA p m U r
    change (U ∈ RecClockLG.recordCarrier p m r L ∧
        ∃ k ≤ n, ε ≤ |LocMart.psum ξ (σ + k) U - LocMart.psum ξ σ U|) ↔
      (U ∈ RecClockLG.recordCarrier p m r L ∧ ∃ k ≤ n, ε ≤ |Q (σ + k) U - Q σ U|)
    simp only [hps]
  change μ.real _ ≤ _
  rw [measureReal_congr heq]
  exact htail

end Swarming.Diameter
