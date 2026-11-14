/-
  **The probability that `L` consecutive sites of one row are unmarked.**

  For the actual i.i.d.-uniform array of `Swarming.Uniform.arrayMeasure`, the site marks
  `B_i(x) = 1{∀ k ∈ [1,m-1], U(i,x,k) > p}` of `Swarm/Reveal.lean` are Bernoulli`(q)`,
  `q = (1-p)^(m-1)`, and distinct sites of a row are independent.  Consequently, for every
  row `i`, every `a` and every `L`,

      `P(all of a, …, a+L-1 unmarked) = (1 - q)^L`.

  The proof is exact: the finite-family mark law `Swarming.Marks.reveal_familyMark_measure`
  (already verified in `Swarm/BridgeReveal.lean`) gives the mass `q^{|S|}` of every
  intersection of `|S|` mark events, and inclusion–exclusion converts it into the mass of the
  intersection of the complements.
-/
import Swarm.QVarBound
import Swarm.BridgeReveal
import Swarm.MpotRun

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BigOperators

namespace SwarmMpot

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmQVariance

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### 1. `omegaN` takes the value `p` exactly at marked sites -/

theorem omegaN_eq_p_iff (hp : 1 / 2 < p) (U : Array N) (i : Fin N) (u : ℕ) :
    omegaN p m U i u = p ↔ SiteMark p m U i (u : ℤ) := by
  classical
  constructor
  · intro hcon
    by_contra hc
    have h2 : omegaN p m U i u = 1 / 2 := by
      unfold SepGroup.Model.omegaN Swarming.Trajectory.omegaAt
      simp [hc]
    rw [h2] at hcon
    linarith
  · intro hc
    unfold SepGroup.Model.omegaN Swarming.Trajectory.omegaAt
    simp [hc]

theorem omegaN_eq_half_or (U : Array N) (i : Fin N) (u : ℕ) :
    omegaN p m U i u = p ∨ omegaN p m U i u = 1 / 2 := by
  have h := SepGroup.Model.omegaAt_eq_half_or (p := p) (m := m) (U := U) i (u : ℤ)
  exact h.symm

/-! ### 2. Inclusion–exclusion for intersections of complements -/

theorem ie_iInter_compl_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {ι : Type*} (t : Finset ι) (s : ι → Set α)
    (hs : ∀ i ∈ t, MeasurableSet (s i)) :
    μ.real (⋂ i ∈ t, (s i)ᶜ)
      = ∑ u ∈ t.powerset, (-1 : ℝ) ^ u.card * μ.real (⋂ i ∈ u, s i) := by
  classical
  have hUn : (⋂ i ∈ t, (s i)ᶜ) = (⋃ i ∈ t, s i)ᶜ := by
    ext U
    simp [Set.mem_iInter]
  have hmeasU : MeasurableSet (⋃ i ∈ t, s i) := Finset.measurableSet_biUnion t hs
  have huniv : μ.real (Set.univ : Set α) = 1 := by simp [Measure.real]
  rw [hUn, measureReal_compl hmeasU, huniv]
  rw [MeasureTheory.measureReal_biUnion_eq_sum_powerset hs (by intro i hi; finiteness)]
  have hF : (t.powerset.filter (fun u : Finset ι => ¬ u.Nonempty)) = {∅} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
      Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro rfl; exact ⟨Finset.empty_subset t, by simp⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := t.powerset)
    (p := fun u : Finset ι => u.Nonempty)
    (f := fun u => (-1 : ℝ) ^ u.card * μ.real (⋂ i ∈ u, s i))
  rw [hF, Finset.sum_singleton] at hsplit
  have hempty : (-1 : ℝ) ^ ((∅ : Finset ι)).card * μ.real (⋂ i ∈ (∅ : Finset ι), s i) = 1 := by
    simp
  rw [hempty, add_comm] at hsplit
  have hneg : ∑ u ∈ t.powerset.filter (fun u : Finset ι => u.Nonempty),
      (-1 : ℝ) ^ u.card * μ.real (⋂ i ∈ u, s i)
      = - ∑ u ∈ t.powerset.filter (fun u : Finset ι => u.Nonempty),
          (-1 : ℝ) ^ (u.card + 1) * μ.real (⋂ i ∈ u, s i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [pow_succ]
    ring
  rw [hneg] at hsplit
  linarith [hsplit]

/-! ### 3. The mark family mass -/

theorem marked_family_real (hp0 : 0 < p) (hp1 : p < 1) (i : Fin N) (s : Finset ℤ) :
    (arrayMeasure N).real {U : Array N | ∀ x ∈ s, SiteMark p m U i x}
      = ((1 - p) ^ (m - 1)) ^ s.card := by
  have h := Swarming.Marks.reveal_familyMark_measure (N := N) hp0 hp1 m s
    (fun x : ℤ => (i, x)) (by
      intro a _ b _ hab
      simpa using hab)
  have hreal : (arrayMeasure N).real {U : Array N | ∀ x ∈ s, SiteMark p m U i x}
      = ((ENNReal.ofReal (1 - p)) ^ (s.card * (m - 1))).toReal := by
    rw [Measure.real, h]
  rw [hreal, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith),
    mul_comm (s.card : ℕ) (m - 1), pow_mul]

theorem marked_family_measurable (i : Fin N) (s : Finset ℤ) :
    ∀ x ∈ s, MeasurableSet {U : Array N | SiteMark p m U i x} :=
  fun x _ => measurableSet_siteMark_v p m i x

/-! ### 4. The probability of an unmarked run -/

/-- The event that the sites `a, a+1, …, a+L-1` of row `i` are all unmarked. -/
def RunEvent (p : ℝ) (m : ℕ) (i : Fin N) (a L : ℕ) : Set (Array N) :=
  {U | ∀ x ∈ (Finset.range L).image (fun j : ℕ => ((a + j : ℕ) : ℤ)),
      ¬ SiteMark p m U i x}

theorem runEvent_eq_compl (i : Fin N) (a L : ℕ) :
    RunEvent p m i a L
      = ⋂ x ∈ (Finset.range L).image (fun j : ℕ => ((a + j : ℕ) : ℤ)),
          ({U : Array N | SiteMark p m U i x})ᶜ := by
  ext U
  simp [RunEvent, Set.mem_iInter]

/-- **The run probability.**  `L` consecutive sites of row `i` are unmarked with probability
`(1-q)^L`, `q = (1-p)^(m-1)`. -/
theorem runEvent_real (hp0 : 0 < p) (hp1 : p < 1) (i : Fin N) (a L : ℕ) :
    (arrayMeasure N).real (RunEvent p m i a L) = (1 - (1 - p) ^ (m - 1)) ^ L := by
  classical
  set sf : Finset ℤ := (Finset.range L).image (fun j : ℕ => ((a + j : ℕ) : ℤ)) with hsf
  have hcard : sf.card = L := by
    rw [hsf, Finset.card_image_of_injOn]
    · exact Finset.card_range L
    · intro x _ y _ hxy
      simp only at hxy
      omega
  have hmeas : ∀ x ∈ sf, MeasurableSet ({U : Array N | SiteMark p m U i x} : Set (Array N)) :=
    marked_family_measurable i sf
  have hval : ∀ u, u ∈ sf.powerset →
      (arrayMeasure N).real (⋂ x ∈ u, {U : Array N | SiteMark p m U i x})
        = ((1 - p) ^ (m - 1)) ^ u.card := by
    intro u _
    have hset : (⋂ x ∈ u, {U : Array N | SiteMark p m U i x})
        = {U : Array N | ∀ x ∈ u, SiteMark p m U i x} := by
      ext U
      simp [Set.mem_iInter]
    rw [hset]
    exact marked_family_real hp0 hp1 i u
  have hie := ie_iInter_compl_eq (μ := arrayMeasure N) sf
    (fun x => {U : Array N | SiteMark p m U i x}) hmeas
  rw [runEvent_eq_compl, ← hsf, hie, ← hcard]
  have hstep : ∑ u ∈ sf.powerset, (-1 : ℝ) ^ u.card * (arrayMeasure N).real
        (⋂ x ∈ u, {U : Array N | SiteMark p m U i x})
      = ∑ u ∈ sf.powerset, (-1 : ℝ) ^ u.card * ((1 - p) ^ (m - 1)) ^ u.card :=
    Finset.sum_congr rfl fun u hu => by rw [hval u hu]
  rw [hstep]
  calc ∑ u ∈ sf.powerset, (-1 : ℝ) ^ u.card * ((1 - p) ^ (m - 1)) ^ u.card
      = ∑ u ∈ sf.powerset, (-(1 - p) ^ (m - 1)) ^ u.card := by
        refine Finset.sum_congr rfl fun u _ => ?_
        have hneg : (-(1 - p) ^ (m - 1) : ℝ) = (-1) * ((1 - p) ^ (m - 1)) := by ring
        rw [hneg, mul_pow]
    _ = ∑ u ∈ sf.powerset, ∏ _x ∈ u, (-(1 - p) ^ (m - 1)) := by
        simp
    _ = ∏ _x ∈ sf, ((-(1 - p) ^ (m - 1)) + 1) := (Finset.prod_add_one sf).symm
    _ = ∏ _x ∈ sf, (1 - (1 - p) ^ (m - 1)) := by
        refine Finset.prod_congr rfl fun x _ => ?_
        ring
    _ = (1 - (1 - p) ^ (m - 1)) ^ sf.card := by
        rw [Finset.prod_const]

end SwarmMpot
