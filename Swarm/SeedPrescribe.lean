/-
# A prescribed finite path has a positive-probability cylinder

For a deterministic nearest-neighbour path `η` in the `N`-walker position space, started at the
origin, let `follows p m η L` be the event that, at every time `n < L` and for every walker `i`,
the array coordinate read at the departure from `η n i` — namely
`(i, η n i, L_n^i(η n i))` with `L_n^i` the visit count along `η` — lies on the side of the
right-jump probability that forces the prescribed step.

This file proves:
* `follows` is *exactly* the event "the actual trajectory follows `η` up to time `L`"
  (`trajectory_eq_of_follows`), because at each step the local-time field of the actual
  trajectory agrees with the visit counts along `η`;
* the departure coordinates of a deterministic nearest-neighbour path are pairwise distinct
  (`dcoord_inj`), by the strict increase of the visit count at a revisit;
* consequently the cylinder has the product of the one-coordinate uniform masses
  (`measure_follows_ne_zero`), which is nonzero as soon as `1/2 < p < 1`.

This is the "each prescribed jump has probability at least `1-p`" step of the proof of
`P(V) > 0` in Proposition `regen` of `main_1d_revised.tex`, in the exact form needed for
the actual i.i.d. array law.
-/
import Swarm.SeedTransplant
import Swarm.SeedBlock
import Swarm.LocalTime

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmRestart

namespace SwarmSeed

variable {N : ℕ}

/-! ### The deterministic path, its visit counts, and its departure coordinates -/

/-- The local-time field along a deterministic path `η`. -/
noncomputable def dt (η : ℕ → Fin N → ℤ) (n : ℕ) : LocalTimes N :=
  fun i x => localTime (fun k => η k i) n x

/-- The array coordinate read at step `n` of the deterministic path `η`. -/
noncomputable def dcoord (η : ℕ → Fin N → ℤ) (n : ℕ) (i : Fin N) : Fin N × ℤ × ℕ :=
  (i, η n i, dt η n i (η n i))

/-- The right-jump probability at step `n` of the deterministic path `η`. -/
noncomputable def dalpha (p : ℝ) (m : ℕ) (η : ℕ → Fin N → ℤ) (n : ℕ) (i : Fin N) : ℝ :=
  rightProbability p m (dt η n) i (η n i)

/-- The half-line of array values that forces the prescribed step. -/
noncomputable def dcond (p : ℝ) (m : ℕ) (η : ℕ → Fin N → ℤ) (n : ℕ) (i : Fin N) : Set ℝ :=
  if η (n + 1) i = η n i + 1 then Iic (dalpha p m η n i) else Ioi (dalpha p m η n i)

theorem drivenStep_one_of_le {u α : ℝ} (h : u ≤ α) : drivenStep u α = 1 := by
  simp [drivenStep, h]

theorem drivenStep_neg_of_not_le {u α : ℝ} (h : ¬ u ≤ α) : drivenStep u α = -1 := by
  simp [drivenStep, h]

/-- The event that the trajectory follows the prescribed path `η` up to time `L`. -/
noncomputable def follows (p : ℝ) (m : ℕ) (η : ℕ → Fin N → ℤ) (L : ℕ) : Set (Array N) :=
  {U | ∀ n, n < L → ∀ i : Fin N, U (dcoord η n i) ∈ dcond p m η n i}

/-! ### The trajectory follows `η` exactly on the cylinder -/

/-- At time `n`, if the actual positions up to `n` agree with the deterministic path, then the
local-time field of the trajectory agrees with the visit counts of the deterministic path. -/
theorem ell_eq_dt {p : ℝ} {m : ℕ} {η : ℕ → Fin N → ℤ} {U : Array N} {n : ℕ}
    (h : ∀ k, k ≤ n → ∀ i, (trajectory p m U k).pos i = η k i) :
    ∀ (i : Fin N) (x : ℤ), (trajectory p m U n).ell i x = dt η n i x := by
  intro i x
  have hfil : (Finset.range (n + 1)).filter (fun k => (trajectory p m U k).pos i = x)
      = (Finset.range (n + 1)).filter (fun k => η k i = x) := by
    apply Finset.filter_congr
    intro k hk
    rw [Finset.mem_range] at hk
    rw [h k (by omega) i]
  rw [ell_eq_localTime, dt, localTime, localTime, hfil]

/-- **The cylinder is exactly the set of arrays whose trajectory follows `η`.** -/
theorem trajectory_eq_of_follows {p : ℝ} {m : ℕ} {η : ℕ → Fin N → ℤ} {L : ℕ}
    (hη0 : ∀ i, η 0 i = 0)
    (hηstep : ∀ (n : ℕ), n < L → ∀ (i : Fin N), η (n + 1) i = η n i + 1 ∨ η (n + 1) i = η n i - 1) :
    follows p m η L = {U : Array N | ∀ n, n ≤ L → ∀ i, (trajectory p m U n).pos i = η n i} := by
  ext U
  constructor
  · intro hU
    have key : ∀ n, n ≤ L → ∀ k, k ≤ n → ∀ i, (trajectory p m U k).pos i = η k i := by
      intro n
      induction n with
      | zero =>
          intro _ k hk i
          have hk0 : k = 0 := Nat.le_zero.mp hk
          subst hk0
          rw [trajectory_zero]
          exact (hη0 i).symm
      | succ n ih =>
          intro hn k hk i
          rcases Nat.lt_or_ge k (n + 1) with hlt | hge
          · exact ih (by omega) k (by omega) i
          · have hk' : k = n + 1 := by omega
            subst hk'
            have hprev : ∀ k, k ≤ n → ∀ j, (trajectory p m U k).pos j = η k j :=
              fun k hk j => ih (by omega) k hk j
            have hell := ell_eq_dt (p := p) (m := m) (η := η) (U := U) hprev
            have hellfun : (trajectory p m U n).ell = dt η n :=
              funext fun i => funext fun x => hell i x
            have htriple : (i, (trajectory p m U n).pos i,
                (trajectory p m U n).ell i ((trajectory p m U n).pos i)) = dcoord η n i := by
              rw [hprev n le_rfl i, hellfun]
              rfl
            have hstepEq : (trajectory p m U (n + 1)).pos i
                = (trajectory p m U n).pos i
                  + drivenStep (U (dcoord η n i)) (dalpha p m η n i) := by
              rw [trajectory_succ, nextWalkState_pos, nextPos, htriple]
              rw [hprev n le_rfl i, hellfun]
              rfl
            have hcond := hU n (by omega) i
            have hstepDir : drivenStep (U (dcoord η n i)) (dalpha p m η n i)
                = η (n + 1) i - η n i := by
              rcases hηstep n (by omega) i with hstep | hstep
              · have hcc : dcond p m η n i = Iic (dalpha p m η n i) := by
                  simp only [dcond, hstep, if_true]
                rw [hstep, drivenStep_one_of_le (by rw [hcc] at hcond; exact hcond)]
                ring
              · have hne : ¬ (η (n + 1) i = η n i + 1) := by omega
                have hcc : dcond p m η n i = Ioi (dalpha p m η n i) := by
                  simp only [dcond, hne, if_false]
                rw [hstep,
                  drivenStep_neg_of_not_le (not_le.mpr (by rw [hcc] at hcond; exact hcond))]
                ring
            rw [hstepEq, hprev n le_rfl i, hstepDir]
            ring
    exact fun n hn i => key n hn n le_rfl i
  · intro hU
    intro n hn i
    have hprev : ∀ k, k ≤ n → ∀ j, (trajectory p m U k).pos j = η k j :=
      fun k hk j => hU k (by omega) j
    have hell := ell_eq_dt (p := p) (m := m) (η := η) (U := U) hprev
    have hellfun : (trajectory p m U n).ell = dt η n :=
      funext fun i => funext fun x => hell i x
    have halpha : rightProbability p m (trajectory p m U n).ell i (η n i) = dalpha p m η n i := by
      rw [hellfun]
      rfl
    have hnext := hU (n + 1) hn i
    rw [trajectory_succ, nextWalkState_pos, nextPos, hprev n le_rfl i, halpha] at hnext
    have hcoord : (i, η n i, (trajectory p m U n).ell i (η n i)) = dcoord η n i := by
      rw [hellfun]
      rfl
    by_cases hup : U (i, η n i, (trajectory p m U n).ell i (η n i)) ≤ dalpha p m η n i
    · rw [hcoord] at hup hnext
      rw [drivenStep_one_of_le hup] at hnext
      have hdir : η (n + 1) i = η n i + 1 := by omega
      simp only [dcond, hdir, if_true]
      exact hup
    · rw [hcoord] at hup hnext
      rw [drivenStep_neg_of_not_le hup] at hnext
      have hdir : ¬ (η (n + 1) i = η n i + 1) := by omega
      simp only [dcond, hdir, if_false]
      exact not_le.mp hup

/-! ### Distinctness of the departure coordinates -/

theorem dt_lt_of_revisit {η : ℕ → Fin N → ℤ} {i : Fin N} {a b : ℕ} (hab : a < b)
    (hx : η a i = η b i) : dt η a i (η a i) < dt η b i (η b i) := by
  simp only [dt, hx]
  exact localTime_lt_of_visit (X := fun k => η k i) hab (x := η b i) rfl

/-- **Departure coordinates along a deterministic path are pairwise distinct.** -/
theorem dcoord_inj {η : ℕ → Fin N → ℤ} {n n' : ℕ} {i i' : Fin N}
    (h : dcoord η n i = dcoord η n' i') : n = n' ∧ i = i' := by
  have hi : i = i' := by
    have := congrArg (fun c : Fin N × ℤ × ℕ => c.1) h
    simpa [dcoord] using this
  subst hi
  have hpos : η n i = η n' i := by
    have := congrArg (fun c : Fin N × ℤ × ℕ => c.2.1) h
    simpa [dcoord] using this
  have hell : dt η n i (η n i) = dt η n' i (η n' i) := by
    have := congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) h
    simpa [dcoord] using this
  refine ⟨?_, rfl⟩
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · exact absurd hell (ne_of_lt (dt_lt_of_revisit hlt hpos))
  · exact heq
  · exact absurd hell.symm (ne_of_lt (dt_lt_of_revisit hgt hpos.symm))

/-! ### The cylinder mass -/

/-- The product formula for a finite family of distinct coordinates. -/
theorem arrayMeasure_cylinder_fintype {ι : Type*} [Fintype ι]
    (c : ι → Fin N × ℤ × ℕ) (hc : Function.Injective c) (C : ι → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i)) :
    (arrayMeasure N) (⋂ i, (fun U : Array N => U (c i)) ⁻¹' C i) = ∏ i, uniform01 (C i) := by
  have hInd : iIndepFun (fun i (U : Array N) => U (c i)) (arrayMeasure N) :=
    (array_independent N).precomp hc
  have h := iIndepFun_iff_measure_inter_preimage_eq_mul.mp hInd (Finset.univ : Finset ι)
    (sets := C) (fun i _ => hC i)
  rw [show (⋂ i, (fun U : Array N => U (c i)) ⁻¹' C i)
      = ⋂ i ∈ (Finset.univ : Finset ι), (fun U : Array N => U (c i)) ⁻¹' C i from by simp]
  rw [h]
  exact Finset.prod_congr rfl fun i _ => arrayMeasure_preimage_set N (c i) (C i) (hC i)

theorem measurableSet_dcond (p : ℝ) (m : ℕ) (η : ℕ → Fin N → ℤ) (n : ℕ) (i : Fin N) :
    MeasurableSet (dcond p m η n i) := by
  unfold dcond
  split_ifs
  · exact measurableSet_Iic
  · exact measurableSet_Ioi

theorem follows_eq_cylinder (p : ℝ) (m : ℕ) (η : ℕ → Fin N → ℤ) (L : ℕ) :
    follows p m η L = ⋂ (q : Fin L × Fin N),
      (fun U : Array N => U (dcoord η q.1 q.2)) ⁻¹' dcond p m η q.1 q.2 := by
  ext U
  simp only [follows, mem_ofPred_eq, mem_iInter, mem_preimage]
  constructor
  · intro hU q
    exact hU q.1 q.1.isLt q.2
  · intro hU n hn i
    exact hU (⟨n, hn⟩, i)

theorem measurableSet_follows (p : ℝ) (m : ℕ) (η : ℕ → Fin N → ℤ) (L : ℕ) :
    MeasurableSet (follows p m η L) := by
  rw [follows_eq_cylinder]
  exact MeasurableSet.iInter fun q =>
    (measurable_pi_apply _) (measurableSet_dcond p m η q.1 q.2)

theorem dcoord_fin_injective {η : ℕ → Fin N → ℤ} {L : ℕ} :
    Function.Injective (fun q : Fin L × Fin N => dcoord η q.1 q.2) := by
  intro a b hab
  obtain ⟨h1, h2⟩ := dcoord_inj (η := η) hab
  exact Prod.ext (Fin.ext h1) h2

/-- The uniform mass of a single constraint is nonzero. -/
theorem uniform01_dcond_ne_zero {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (η : ℕ → Fin N → ℤ) (n : ℕ) (i : Fin N) :
    uniform01 (dcond p m η n i) ≠ 0 := by
  have hα0 : 0 < dalpha p m η n i :=
    lt_of_lt_of_le (by norm_num) (one_half_le_rightProbability hp0.le m _ i _)
  have hα1 : dalpha p m η n i < 1 :=
    lt_of_le_of_lt (rightProbability_le_p hp0.le m _ i _) hp1
  unfold dcond
  split_ifs
  · rw [uniform01_Iic hα0 hα1]
    exact (ENNReal.ofReal_pos.mpr hα0).ne'
  · rw [uniform01_Ioi hα0 hα1]
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'

/-- **The prescribed cylinder has positive mass.** -/
theorem measure_follows_ne_zero {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (η : ℕ → Fin N → ℤ) (L : ℕ) :
    (arrayMeasure N) (follows p m η L) ≠ 0 := by
  rw [follows_eq_cylinder]
  rw [arrayMeasure_cylinder_fintype (fun q : Fin L × Fin N => dcoord η q.1 q.2)
    (dcoord_fin_injective (η := η)) (fun q => dcond p m η q.1 q.2)
    (fun q => measurableSet_dcond p m η q.1 q.2)]
  exact Finset.prod_ne_zero_iff.mpr
    (fun q _ => uniform01_dcond_ne_zero hp0 hp1 m η q.1 q.2)

/-- The coordinate set read by the prescribed cylinder. -/
noncomputable def dcoordSet (η : ℕ → Fin N → ℤ) (L : ℕ) : Finset (Fin N × ℤ × ℕ) :=
  Finset.univ.image (fun q : Fin L × Fin N => dcoord η q.1 q.2)

theorem mem_dcoordSet {η : ℕ → Fin N → ℤ} {L n : ℕ} {i : Fin N} (hn : n < L) :
    dcoord η n i ∈ dcoordSet η L :=
  Finset.mem_image.mpr ⟨(⟨n, hn⟩, i), Finset.mem_univ _, rfl⟩

/-- **`follows` depends only on the coordinates in `dcoordSet`.** -/
theorem follows_determined {p : ℝ} {m : ℕ} {η : ℕ → Fin N → ℤ} {L : ℕ} {U U' : Array N}
    (h : ∀ q ∈ dcoordSet η L, U q = U' q) : (follows p m η L U ↔ follows p m η L U') := by
  constructor
  · intro hU n hn i
    rw [← h _ (mem_dcoordSet hn)]
    exact hU n hn i
  · intro hU n hn i
    rw [h _ (mem_dcoordSet hn)]
    exact hU n hn i

end SwarmSeed
