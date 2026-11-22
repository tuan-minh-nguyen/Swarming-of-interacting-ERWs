import Swarm.FrozenBadTime
import Swarm.ClockFibreAzuma
import Swarm.RawLogRatio
import Swarm.R2LocMax
import Mathlib.Probability.Independence.Integration

open Filter MeasureTheory ProbabilityTheory Set
open Swarming.Uniform Swarming.Trajectory Swarming.Enl
open SwarmRecordMeas.Actual SwarmStop SwarmCross SwarmSpeed SwarmSpeed.Frozen
open SwarmDischarge SwarmBad SwarmLogRatio SwarmSpatial SwarmMarks
open scoped ENNReal Function

set_option autoImplicit false

namespace Swarming.Diameter

private theorem integral_windowPotential {N : ℕ} {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (j : Fin N) (a b : ℕ) :
    ∫ U, R (windowWeight p m j U) a b ∂arrayMeasure N = aParam p m ^ (b - a) := by
  classical
  let q := (1 - p) ^ (m - 1)
  let μ := markMeasure (boolMeasure q)
  let S := Finset.Icc (a + 1) b
  have hm₁ : 1 ≤ m := by omega
  let : IsProbabilityMeasure (boolMeasure q) :=
    isProbabilityMeasure_boolMeasure (by positivity) (qle_one hp₀ hp₁ hm₁)
  have hmap := measurePreserving_siteMarks (show 0 < p by linarith) hp₁ m j
  have hφ : (fun U => R (windowWeight p m j U) a b) =
      (fun ω : ℕ → Bool => ∏ z ∈ S, xi p ω z) ∘ (fun U => siteMarks p m U j) := by
    funext U
    apply Finset.prod_congr rfl
    intro z _
    by_cases hz : SiteMark p m U j (z : ℤ)
    · simp only [rat, windowWeight, omegaAt, if_pos hz,
        xi_of_marked (show siteMarks p m U j z = true by simp [siteMarks, hz])]
    · have h := xi_of_unmarked (p := p) (show siteMarks p m U j z = false by simp [siteMarks, hz])
      change (1 - omegaAt p m U j (z : ℤ)) / omegaAt p m U j (z : ℤ) = xi p (siteMarks p m U j) z
      rw [h]
      simp only [omegaAt, if_neg hz]
      norm_num
  rw [hφ]
  change (∫ U, (∏ z ∈ S, xi p (siteMarks p m U j) z) ∂arrayMeasure N) = _
  rw [← integral_map (f := fun ω : ℕ → Bool => ∏ z ∈ S, xi p ω z) hmap.measurable.aemeasurable]
  · rw [hmap.map_eq]
    change (∫ ω, ∏ z ∈ S, xi p ω z ∂μ) = _
    have hind := (iIndepFun_eval (μB := boolMeasure q)).comp
      (fun _ => SwarmMarks.rhoOf p) (fun _ => SwarmMarks.measurable_rhoOf p)
    have hf : (∫ ω, ∏ z : S, xi p ω (z : ℕ) ∂μ) =
        ∏ z : S, ∫ ω, xi p ω (z : ℕ) ∂μ :=
      (hind.precomp (g := fun z : S => (z : ℕ)) Subtype.val_injective).integral_fun_prod_eq_prod_integral
        (fun z => (measurable_xi p (z : ℕ)).aestronglyMeasurable)
    calc
      _ = ∫ ω, ∏ z : S, xi p ω (z : ℕ) ∂μ := by
        simp only [Finset.prod_coe_sort]
      _ = ∏ z : S, ∫ ω, xi p ω (z : ℕ) ∂μ := hf
      _ = ∏ _ : S, aParam p m := Finset.prod_congr rfl
        (fun z _ => integral_xi_eq_aParam hp₀ hp₁ hm₁ (z : ℕ))
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe, S, Nat.card_Icc]
        congr 1
        omega
  · exact (Finset.measurable_fun_prod S (fun z _ => measurable_xi p z)).aestronglyMeasurable

/-- The walker leaves the open interval `(a, b + 1)` through `a` at or after time `s`. -/
def crossesDown {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (a b s : ℕ) : Prop :=
  ∃ t : ℕ, s ≤ t ∧ (trajectory p m U t).pos i = (a : ℤ) ∧
    ∀ u : ℕ, s ≤ u → u < t →
      (a : ℤ) < (trajectory p m U u).pos i ∧ (trajectory p m U u).pos i ≤ (b : ℤ)

private theorem crossesDown_subset_frozen {N : ℕ} (p : ℝ) (m : ℕ) (i : Fin N)
    {a b s : ℕ} {A : Set (Array N)} :
    {U | crossesDown p m U i a b s} ∩ A ⊆
      hitsBefore (shiftX (Xtil p m i a b s A) s) a (b + 1) ∩ A := by
  rintro U ⟨⟨t, hst, ht, hbetween⟩, hU⟩
  have hexit : exitAfterStart p m i a b s U = (t : WithTop ℕ) := by
    apply (trajExit_eq_coe_iff p m).mpr
    refine ⟨by exact_mod_cast hst, Or.inl ht.le, ?_⟩
    intro u hu hut
    obtain ⟨hlo, hhi⟩ := hbetween u (by exact_mod_cast hu) hut
    refine ⟨hlo, ?_⟩
    push_cast
    omega
  have heq (u : ℕ) (hsu : s ≤ u) (hut : u ≤ t) :
      Xtil p m i a b s A u U = ((trajectory p m U u).pos i).toNat := by
    have h := (show (u : WithTop ℕ) ≤ exitAfterStart p m i a b s U by rw [hexit]; exact_mod_cast hut)
    rw [Xtil_of_mem hsu hU]
    exact congrArg Int.toNat (stoppedProcess_eq_of_le h)
  refine ⟨⟨t - s, ?_, ?_⟩, hU⟩
  · change Xtil p m i a b s A (s + (t - s)) U = a
    rw [Nat.add_sub_of_le hst, heq t hst le_rfl, ht, Int.toNat_natCast]
  · intro u hu
    have hut : s + u < t := by omega
    change Xtil p m i a b s A (s + u) U ≠ b + 1
    rw [heq (s + u) (Nat.le_add_right _ _) hut.le]
    exact ne_of_lt (Nat.lt_succ_of_le (Int.toNat_le.mpr (hbetween _ (Nat.le_add_right _ _) hut).2))

/-- At a fixed offset after reaching a record, the probability of exiting
downward from \((a,b+1)\), starting at \(b\) with the other walker already past
\(b\), is bounded by the annealed product of the site ratios. -/
theorem record_downward_crossing_prob_le {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) (i j : Fin N) (hij : i ≠ j)
    (r v : ℕ) {a b : ℕ} (hab : a < b) :
    (arrayMeasure N).real {U | U ∈ ReachAll p m ∧
      badPos p m U i j (b : ℤ) (recTimeA p m U r + v) ∧
      crossesDown p m U i a b (recTimeA p m U r + v)} ≤ aParam p m ^ (b - a) := by
  classical
  let μ := arrayMeasure N
  let f (U : Array N) := R (windowWeight p m j U) a b
  let ν := μ.withDensity (fun U => ENNReal.ofReal (f U))
  let A (n : ℕ) := ClockFibre.clockFibre (N := N) p m r n ∩
    {U | badPos p m U i j (b : ℤ) (n + v)}
  let E (n : ℕ) := {U | crossesDown p m U i a b (n + v)} ∩ A n
  have hA (n : ℕ) : MeasurableSet[enlFilt p m (n + v)] (A n) :=
    ((enlFilt p m).mono (Nat.le_add_right n v) _ (ClockFibre.measurableSet_clockFibre p m r n)).inter
      (measurableSet_badPos p m (n + v) le_rfl i j (b : ℤ))
  have hAm (n : ℕ) : MeasurableSet (A n) := (enlFilt p m).le _ _ (hA n)
  have hf₀ (U : Array N) : 0 ≤ f U := (windowPotential_bounds hp₀.le hp₁ j a b U).1
  have hf₁ (U : Array N) : f U ≤ 1 := (windowPotential_bounds hp₀.le hp₁ j a b U).2
  have hfi : Integrable f μ := Integrable.of_bound
    (measurable_windowPotential p m j a b).aestronglyMeasurable 1
    (Eventually.of_forall fun U => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf₀ U)] using hf₁ U)
  have hbound (n : ℕ) : μ (E n) ≤ ν (A n) := by
    have hsub : A n ⊆ {U | badPos p m U i j (b : ℤ) (n + v)} := inter_subset_right
    have h := (measureReal_mono (crossesDown_subset_frozen p m i) (measure_ne_top μ _)).trans
      (subset_frozen_cross_prob_hitsBefore_le_R p m hp₀ hp₁ i j (hA n) hsub hab hij)
    have hEq : (∫ U in A n, R (revealedWF p m j (n + v) U) a b ∂μ) = ∫ U in A n, f U ∂μ :=
      setIntegral_congr_fun (hAm n) (fun U hU => (windowPotential_eq_revealed_nat hp₀.le m
        (n + v) a b (hsub hU)).symm)
    have hh : μ.real (E n) ≤ ∫ U in A n, f U ∂μ := h.trans_eq hEq
    rw [withDensity_apply _ (hAm n), ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
      (Eventually.of_forall hf₀)]
    exact measure_le_ofReal_of_real_le hh
  have hd : Pairwise (Disjoint on A) := fun n n' h =>
    (ClockFibre.disjoint_clockFibre p m r n n' h).mono inter_subset_left inter_subset_left
  have hcover : {U | U ∈ ReachAll p m ∧
        badPos p m U i j (b : ℤ) (recTimeA p m U r + v) ∧
        crossesDown p m U i a b (recTimeA p m U r + v)} ⊆ ⋃ n, E n := by
    rintro U ⟨hU, hbad, hcross⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp (ClockFibre.reachAll_subset_iUnion_clockFibre p m r hU)
    rw [ClockFibre.recTimeA_eq_of_mem_clockFibre hU hn] at hbad hcross
    exact mem_iUnion.mpr ⟨n, hcross, hn, hbad⟩
  have hmass : μ {U | U ∈ ReachAll p m ∧ badPos p m U i j (b : ℤ) (recTimeA p m U r + v) ∧
      crossesDown p m U i a b (recTimeA p m U r + v)} ≤ ν univ := by
    calc
      _ ≤ μ (⋃ n, E n) := measure_mono hcover
      _ ≤ ∑' n, μ (E n) := measure_iUnion_le E
      _ ≤ ∑' n, ν (A n) := ENNReal.tsum_le_tsum hbound
      _ = ν (⋃ n, A n) := (measure_iUnion hd hAm).symm
      _ ≤ ν univ := measure_mono (subset_univ _)
  have hfint : ν univ = ENNReal.ofReal (aParam p m ^ (b - a)) := by
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hf₀)]
    congr 1
    exact integral_windowPotential hp₀ hp₁ hm j a b
  rw [hfint] at hmass
  exact ENNReal.toReal_le_of_le_ofReal
    (pow_nonneg (SwarmSpatial.aParam_nonneg hp₀ hp₁ (by omega : 1 ≤ m)) _) hmass

private theorem exists_crossesDown_of_drop {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N)
    (i j : Fin N) {z k s t : ℕ} (hk : 2 ≤ k) (hz : k ≤ z) (hst : s ≤ t)
    (hs : (z : ℤ) ≤ (trajectory p m U s).pos i)
    (hj : (z : ℤ) ≤ runMax p m U j s)
    (ht : (trajectory p m U t).pos i < (z : ℤ) - (k : ℤ)) :
    ∃ u : ℕ, s ≤ u ∧ u ≤ t ∧ badPos p m U i j ((z - 1 : ℕ) : ℤ) u ∧
      crossesDown p m U i (z - k) (z - 1) u := by
  classical
  let X (u : ℕ) := (trajectory p m U u).pos i
  change X t < (z : ℤ) - (k : ℤ) at ht
  have hstep (u : ℕ) : X u - 1 ≤ X (u + 1) := by
    rcases pos_succ_eq_add_one_or_sub_one p m U i u with h | h
    · change X (u + 1) = X u + 1 at h
      omega
    · change X (u + 1) + 1 = X u at h
      omega
  let A := (Finset.Icc s t).filter (fun u => (z : ℤ) ≤ X u)
  have hA : A.Nonempty := ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hst⟩, hs⟩⟩
  let v := A.max' hA
  obtain ⟨hvI, hv⟩ := Finset.mem_filter.mp (A.max'_mem hA)
  obtain ⟨hsv, hvt⟩ := Finset.mem_Icc.mp hvI
  change s ≤ v at hsv
  change v ≤ t at hvt
  change (z : ℤ) ≤ X v at hv
  have hvt' : v < t := by
    refine lt_of_le_of_ne hvt (fun h => ?_)
    rw [h] at hv
    omega
  have habove (u : ℕ) (hvu : v < u) (hut : u ≤ t) : X u < (z : ℤ) := by
    by_contra! h
    have hu : u ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hsv.trans hvu.le, hut⟩, h⟩
    exact (not_le_of_gt hvu) (Finset.le_max' A u hu)
  have hstart : X (v + 1) = ((z - 1 : ℕ) : ℤ) := by
    have hlu := habove (v + 1) (by omega) (by omega)
    rw [Nat.cast_sub (by omega : 1 ≤ z)]
    push_cast
    have hd := hstep v
    omega
  have hzc : ((z - k : ℕ) : ℤ) = (z : ℤ) - (k : ℤ) := Nat.cast_sub hz
  have hhit : ∃ w : ℕ, v + 1 ≤ w ∧ X w ≤ ((z - k : ℕ) : ℤ) :=
    ⟨t, by omega, ht.le.trans_eq hzc.symm⟩
  let w := Nat.find hhit
  have hw : v + 1 ≤ w ∧ X w ≤ ((z - k : ℕ) : ℤ) := Nat.find_spec hhit
  have hwt : w ≤ t := Nat.find_min' hhit ⟨by omega, ht.le.trans_eq hzc.symm⟩
  have hbelow (u : ℕ) (hvu : v + 1 ≤ u) (huw : u < w) : ((z - k : ℕ) : ℤ) < X u :=
    lt_of_not_ge (fun hu => Nat.find_min hhit huw ⟨hvu, hu⟩)
  have hwgt : v + 1 < w := by
    have h := hw.2.trans_eq hzc
    have hstart' : X (v + 1) = (z : ℤ) - 1 := by
      rw [hstart, Nat.cast_sub (by omega : 1 ≤ z), Nat.cast_one]
    exact lt_of_le_of_ne hw.1 (fun heq => by rw [← heq, hstart'] at h; omega)
  have hstop : X w = ((z - k : ℕ) : ℤ) := by
    have h := hbelow (w - 1) (by omega) (by omega)
    have hsuc : w - 1 + 1 = w := by omega
    have h' := hstep (w - 1)
    rw [hsuc] at h'
    exact le_antisymm hw.2 (by omega)
  refine ⟨v + 1, by omega, by omega, ⟨hstart, ?_⟩, w, hw.1, hstop, ?_⟩
  · have hj' := hj.trans (runMax_mono p m U j (by omega : s ≤ v + 1))
    rw [Nat.cast_sub (by omega : 1 ≤ z)]
    push_cast
    omega
  · intro u hu huw
    refine ⟨hbelow u hu huw, ?_⟩
    have h := habove u (by omega) (huw.le.trans hwt)
    change X u ≤ ((z - 1 : ℕ) : ℤ)
    rw [Nat.cast_sub (by omega : 1 ≤ z)]
    push_cast
    omega

/-- After a swarm record, a walker drops by more than \(k\) below a level
already reached by another walker. Both times lie within the horizon \(H\). -/
def recordDownwardExcursion {N : ℕ} [Nonempty (Fin N)] (p : ℝ) (m r lo hi H k : ℕ) :
    Set (Array N) :=
  {U | U ∈ ReachAll p m ∧
    ∃ i j : Fin N, i ≠ j ∧ ∃ z ∈ Finset.Icc lo hi, ∃ s t : ℕ,
      recTimeA p m U r ≤ s ∧ s ≤ t ∧ t ≤ recTimeA p m U r + H ∧
      (z : ℤ) ≤ (trajectory p m U s).pos i ∧ (z : ℤ) ≤ runMax p m U j s ∧
      (trajectory p m U t).pos i < (z : ℤ) - (k : ℤ)}

/-- A union bound for downward crossings at all levels and times in the
record interval. -/
theorem record_downward_excursion_prob_le {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m)
    (r lo hi H k : ℕ) (hk : 2 ≤ k) (hlo : k ≤ lo) :
    (arrayMeasure N).real (recordDownwardExcursion p m r lo hi H k) ≤
      (N : ℝ) ^ 2 * ((hi + 1 - lo : ℕ) : ℝ) * ((H + 1 : ℕ) : ℝ) * aParam p m ^ (k - 1) := by
  classical
  let P := {ij : Fin N × Fin N // ij.1 ≠ ij.2}
  let Z := Finset.Icc lo hi
  let μ := arrayMeasure N
  let E (a : (P × ↥Z) × Fin (H + 1)) : Set (Array N) := {U | U ∈ ReachAll p m ∧
    badPos p m U a.1.1.1.1 a.1.1.1.2 (((a.1.2 : ℕ) - 1 : ℕ) : ℤ)
        (recTimeA p m U r + a.2) ∧
      crossesDown p m U a.1.1.1.1 ((a.1.2 : ℕ) - k) ((a.1.2 : ℕ) - 1)
        (recTimeA p m U r + a.2)}
  have hincl : recordDownwardExcursion p m r lo hi H k ⊆ ⋃ a, E a := by
    rintro U ⟨hU, i, j, hij, z, hz, s, t, hs, hst, ht, hpos, hmax, hdrop⟩
    have hkz := hlo.trans (Finset.mem_Icc.mp hz).1
    obtain ⟨u, hsu, hut, hsite, hcross⟩ := exists_crossesDown_of_drop p m U i j hk hkz
      hst hpos hmax hdrop
    let v : Fin (H + 1) := ⟨u - recTimeA p m U r, by omega⟩
    have hv : recTimeA p m U r + (v : ℕ) = u := by dsimp only [v]; omega
    refine mem_iUnion.mpr ⟨((⟨(i, j), hij⟩, ⟨z, hz⟩), v), hU, ?_⟩
    change badPos p m U i j ((z - 1 : ℕ) : ℤ) (recTimeA p m U r + (v : ℕ)) ∧
      crossesDown p m U i (z - k) (z - 1) (recTimeA p m U r + (v : ℕ))
    rw [hv]
    exact ⟨hsite, hcross⟩
  have hprob (a : (P × ↥Z) × Fin (H + 1)) : μ.real (E a) ≤ aParam p m ^ (k - 1) := by
    obtain ⟨⟨⟨⟨i, j⟩, hij⟩, ⟨z, hz⟩⟩, v⟩ := a
    have hkz := hlo.trans (Finset.mem_Icc.mp hz).1
    have h := record_downward_crossing_prob_le hp₀ hp₁ hm i j hij r v
      (a := z - k) (b := z - 1) (by omega)
    rwa [show z - 1 - (z - k) = k - 1 by omega] at h
  have hP : (Fintype.card P : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h := Fintype.card_le_of_injective (fun q : P => q.1) Subtype.val_injective
    rw [Fintype.card_prod, Fintype.card_fin, ← pow_two] at h
    exact_mod_cast h
  calc
    μ.real (recordDownwardExcursion p m r lo hi H k) ≤ μ.real (⋃ a, E a) :=
      measureReal_mono hincl (measure_ne_top μ _)
    _ ≤ ∑ a, μ.real (E a) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _ : (P × ↥Z) × Fin (H + 1), aParam p m ^ (k - 1) :=
      Finset.sum_le_sum (fun a _ => hprob a)
    _ = (Fintype.card P : ℝ) * ((hi + 1 - lo : ℕ) : ℝ) * ((H + 1 : ℕ) : ℝ) *
        aParam p m ^ (k - 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_coe, Z, Nat.card_Icc, Nat.cast_mul]
    _ ≤ _ := by
      gcongr
      exact pow_nonneg (aParam_nonneg hp₀ hp₁ (by omega : 1 ≤ m)) _

/-- The downward-crossing event in the two-walker estimate has probability at
most \(\exp(-c\sqrt L)\). The bound is uniform over the record level. -/
theorem record_downward_excursion_failure_le_sqrt {N : ℕ} [Nonempty (Fin N)] {p : ℝ} {m : ℕ}
    (hp₀ : (1 : ℝ) / 2 < p) (hp₁ : p < 1) (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in atTop, ∀ r ≥ 10 * L, ∀ x ≤ L,
      (arrayMeasure N).real (recordDownwardExcursion p m r (r - x) (r + 2 * L ^ 3)
        (2 * L ^ 3) ⌈Real.sqrt (L : ℝ)⌉₊) ≤ Real.exp (-c * Real.sqrt (L : ℝ)) := by
  let q := max (1 / 2 : ℝ) (aParam p m)
  have hq₀ : 0 < q := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_left _ _)
  have hq₁ : q < 1 := max_lt (by norm_num) (aParam_lt_one hp₀ hp₁ (by omega))
  have hlog := Real.log_neg hq₀ hq₁
  let c := -Real.log q / 2
  have hc : 0 < c := by dsimp only [c]; linarith
  let V (L : ℕ) := Real.sqrt (L : ℝ)
  have hV : Tendsto V atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hpoly := LocSumR1.eventually_poly_mul_exp_le (C := 12 * (N : ℝ) ^ 2)
    (by positivity) hc 12
  refine ⟨c / 2, half_pos hc, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hV.eventually_ge_atTop 2, hV.eventually hpoly]
    with L hL hV₀ hPoly
  intro r hr x hx
  let k := ⌈V L⌉₊
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hkL : k ≤ L := Nat.ceil_le.mpr (Real.sqrt_le_self_iff.mpr (Or.inr hLr))
  have hVk : V L ≤ (k : ℝ) := Nat.le_ceil _
  have hk : 2 ≤ k := by exact_mod_cast hV₀.trans hVk
  have hkr : k ≤ r - x := by omega
  have hV₂ : (V L) ^ 2 = (L : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hL₃ : L ≤ L ^ 3 := le_self_pow₀ hL (by decide)
  have hlen : r + 2 * L ^ 3 + 1 - (r - x) ≤ 4 * L ^ 3 := by omega
  have hH : 2 * L ^ 3 + 1 ≤ 3 * L ^ 3 := by omega
  have hprod : aParam p m ^ (k - 1) ≤ Real.exp (-c * V L) := by
    have hq : aParam p m ≤ q := le_max_right _ _
    have hq := pow_le_pow_left₀ (aParam_nonneg hp₀ hp₁ (by omega : 1 ≤ m)) hq (k - 1)
    refine hq.trans ?_
    rw [← Real.exp_log hq₀, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hhalf : V L / 2 ≤ ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      linarith only [hV₀, hVk]
    have h := mul_le_mul_of_nonpos_right hhalf hlog.le
    dsimp only [c]
    linarith only [h]
  refine (record_downward_excursion_prob_le hp₀ hp₁ hm r (r - x) (r + 2 * L ^ 3)
    (2 * L ^ 3) k hk hkr).trans ?_
  calc
    _ ≤ (N : ℝ) ^ 2 * (4 * (L : ℝ) ^ 3) * (3 * (L : ℝ) ^ 3) * Real.exp (-c * V L) := by
      gcongr
      · exact pow_nonneg (aParam_nonneg hp₀ hp₁ (by omega : 1 ≤ m)) _
      · exact_mod_cast hlen
      · exact_mod_cast hH
    _ = 12 * (N : ℝ) ^ 2 * (V L) ^ 12 * Real.exp (-c * V L) := by rw [← hV₂]; ring
    _ ≤ _ := hPoly

end Swarming.Diameter
