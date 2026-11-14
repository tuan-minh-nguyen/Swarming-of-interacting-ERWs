/-
  **The shifted site potential above the running record.**

  `(projh)` of the paper is `e_{g+1} = 1 + a (1 + e_g)` for `e_g = E[h_j(M_n^j + g) | F_n]`.
  `areas/spatialavg/S14.lean` proves it for a *deterministic* record and the σ-algebra `Gfilt r`
  of the site marks, and records as its remaining gap the freshness above the *running* record
  under the enlarged filtration.  This file supplies the objects for that step on the
  record-enlarged σ-algebra of `RecEnv.lean` / `RecFresh.lean`:

  * `markB`, `markSeq`, `shiftH`, `rhoStep` — the mark at a site as a `Bool`, the mark sequence of
    the sites `M_n^j, M_n^j+1, …`, the shifted potential `h_j(M_n^j + g)`, and the one-site
    multiplier at the `k`-th site above the record;
  * `shiftH_succ` — `h(M+g+1) = 1 + rho(M+g+1) · (1 + h(M+g))`, the two-branch step in the
    multiplicative form of `SwarmMarks.hstep_eq_rho`;
  * `aRec` — the paper's `a = 1 - (2p-1)(1-p)^{m-1}/p`, and `aRec_eq`;
  * deterministic bounds `abs_shiftH_le`, `abs_rhoStep_le` and the integrability of `shiftH`,
    `rhoStep`, `rhoStep · (1 + shiftH)`;
  * `measurable_shiftH` — `h_j(M_n^j+g)` is measurable for `infoPiece p m n j g`, the `g`-th
    record information; `measurable_rhoStep` — the multiplier is ambient measurable.  The random
    shift `M_n^j` is handled by the countable-piece argument, never by a static injection.
-/
import Swarm.RecFresh
import Swarm.MarkMoments

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Swarming.Enl

open Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-! ### The mark at a site, the shifted mark sequence and the shifted potential -/

/-- The site mark `B_j(x)` of `Swarm/Reveal.lean` as a `Bool`. -/
noncomputable def markB (p : ℝ) (m : ℕ) (j : Fin N) (x : ℤ) (U : Array N) : Bool := by
  classical
  exact if SiteMark p m U j x then true else false

lemma markB_pos {p : ℝ} {m : ℕ} {j : Fin N} {x : ℤ} {U : Array N}
    (h : SiteMark p m U j x) : markB p m j x U = true := by
  classical
  simp only [markB]
  exact if_pos h

lemma markB_neg {p : ℝ} {m : ℕ} {j : Fin N} {x : ℤ} {U : Array N}
    (h : ¬ SiteMark p m U j x) : markB p m j x U = false := by
  classical
  simp only [markB]
  exact if_neg h

lemma rhoOf_markB_pos {p : ℝ} {m : ℕ} {j : Fin N} {x : ℤ} {U : Array N}
    (h : SiteMark p m U j x) :
    SwarmMarks.rhoOf p (markB p m j x U) = SwarmMarks.rhoOf p true := by
  rw [markB_pos h]

lemma rhoOf_markB_neg {p : ℝ} {m : ℕ} {j : Fin N} {x : ℤ} {U : Array N}
    (h : ¬ SiteMark p m U j x) : SwarmMarks.rhoOf p (markB p m j x U) = 1 := by
  rw [markB_neg h, SwarmMarks.rhoOf_false]

/-- The site marks at the sites `M_n^j, M_n^j + 1, …` above the running record. -/
noncomputable def markSeq (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) (U : Array N) : ℕ → Bool :=
  fun k => markB p m j (recVal j (prefOf p m n U) + (k : ℤ)) U

/-- The site potential `h_j(M_n^j + g)`, as a function of the array. -/
noncomputable def shiftH (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) (g : ℕ) (U : Array N) : ℝ :=
  SwarmMarks.hof p (markSeq p m n j U) g

/-- The one-site multiplier at the `k`-th site above the record. -/
noncomputable def rhoStep (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) (k : ℕ) (U : Array N) : ℝ :=
  SwarmMarks.rhoOf p (markSeq p m n j U k)

lemma shiftH_zero_val {p : ℝ} (m n : ℕ) (j : Fin N) (U : Array N) :
    shiftH p m n j 0 U = SwarmMarks.hstep p (markSeq p m n j U 0) 1 := rfl

/-- **The two-branch step in multiplicative form**, from `SwarmMarks.hstep_eq_rho`. -/
theorem shiftH_succ {p : ℝ} (hp0 : p ≠ 0) (m n : ℕ) (j : Fin N) (g : ℕ) (U : Array N) :
    shiftH p m n j (g + 1) U =
      1 + rhoStep p m n j (g + 1) U * (1 + shiftH p m n j g U) := by
  simp only [shiftH, rhoStep, SwarmMarks.hof_succ, SwarmMarks.hstep_eq_rho hp0]

/-! ### The paper's constant `a` -/

/-- The paper's `a = 1 - (2p-1)(1-p)^{m-1}/p`. -/
noncomputable def aRec (p : ℝ) (m : ℕ) : ℝ := ExcitedEnv.aConst p ((1 - p) ^ (m - 1))

lemma aRec_eq {p : ℝ} (hp0 : p ≠ 0) (m : ℕ) :
    aRec p m = 1 + (SwarmMarks.rhoOf p true - 1) * (1 - p) ^ (m - 1) := by
  unfold aRec ExcitedEnv.aConst
  rw [SwarmMarks.rhoOf_true]
  field_simp
  ring

lemma one_sub_le_aRec {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ) :
    1 - (1 - p) ^ (m - 1) ≤ aRec p m := by
  have hp0 : p ≠ 0 := by linarith
  rw [aRec_eq hp0]
  have hq : (0 : ℝ) ≤ (1 - p) ^ (m - 1) := pow_nonneg (by linarith) _
  have hr : 0 ≤ SwarmMarks.rhoOf p true := by
    rw [SwarmMarks.rhoOf_true]
    exact div_nonneg (by linarith) (by linarith)
  nlinarith

/-! ### Deterministic bounds -/

lemma abs_rhoOf_le_one {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (b : Bool) :
    |SwarmMarks.rhoOf p b| ≤ 1 := by
  cases b with
  | false => simp [SwarmMarks.rhoOf]
  | true =>
      rw [SwarmMarks.rhoOf_true, abs_of_nonneg (by positivity), div_le_one (by linarith)]
      linarith

lemma hstep_abs_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    (b : Bool) (h : ℝ) : |SwarmMarks.hstep p b h| ≤ |h| + 2 := by
  rw [SwarmMarks.hstep_eq_rho hp0]
  have hr : |SwarmMarks.rhoOf p b| ≤ 1 := abs_rhoOf_le_one hp1 hp2 b
  calc |1 + SwarmMarks.rhoOf p b * (1 + h)| ≤ 1 + |SwarmMarks.rhoOf p b * (1 + h)| := by
        simpa using abs_add_le (1 : ℝ) (SwarmMarks.rhoOf p b * (1 + h))
    _ = 1 + |SwarmMarks.rhoOf p b| * |1 + h| := by rw [abs_mul]
    _ ≤ 1 + 1 * (1 + |h|) := by
        have h1 : |1 + h| ≤ 1 + |h| := by simpa using abs_add_le (1 : ℝ) h
        have h0 : (0 : ℝ) ≤ |SwarmMarks.rhoOf p b| := abs_nonneg _
        have h0' : (0 : ℝ) ≤ |1 + h| := abs_nonneg _
        nlinarith [mul_le_mul hr h1 h0' zero_le_one]
    _ = |h| + 2 := by ring

lemma abs_shiftH_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    (m n : ℕ) (j : Fin N) (g : ℕ) (U : Array N) :
    |shiftH p m n j g U| ≤ 2 * (g : ℝ) + 3 := by
  simp only [shiftH]
  induction g with
  | zero =>
      have h := hstep_abs_le hp1 hp2 hp0 (markSeq p m n j U 0) (1 : ℝ)
      rw [abs_one] at h
      rw [SwarmMarks.hof_zero]
      push_cast
      linarith
  | succ k ih =>
      rw [SwarmMarks.hof_succ]
      have h := hstep_abs_le hp1 hp2 hp0 (markSeq p m n j U (k + 1))
        (SwarmMarks.hof p (markSeq p m n j U) k)
      push_cast
      linarith

lemma abs_rhoStep_le {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) (j : Fin N)
    (k : ℕ) (U : Array N) : |rhoStep p m n j k U| ≤ 1 :=
  abs_rhoOf_le_one hp1 hp2 _

/-! ### Measurability of the shifted potential and of the multiplier -/

lemma siteMark_iff_of_agree {p : ℝ} {m : ℕ} {U U' : Array N} {j : Fin N} {x : ℤ}
    (h : ∀ k ∈ Finset.Icc 1 (m - 1), U (j, x, k) = U' (j, x, k)) :
    SiteMark p m U j x ↔ SiteMark p m U' j x := by
  simp only [SiteMark]
  exact ⟨fun hh k hk => by rw [← h k hk]; exact hh k hk,
         fun hh k hk => by rw [h k hk]; exact hh k hk⟩

/-- A `Bool`-valued function is measurable as soon as the preimage of `true` is measurable
(the σ-algebra of `Bool` is discrete and generated by `{true}`). -/
lemma measurable_to_bool {α : Type*} [MeasurableSpace α] {f : α → Bool}
    (h : MeasurableSet {a | f a = true}) : Measurable f := by
  classical
  have hfalse : MeasurableSet {a | f a = false} := by
    rw [show {a | f a = false} = {a | f a = true}ᶜ by
      ext a; cases hfa : f a <;> simp [hfa]]
    exact h.compl
  have hb : ∀ b : Bool, MeasurableSet {a | f a = b} := by
    intro b; cases b
    · exact hfalse
    · exact h
  intro s _
  have hset : f ⁻¹' s = ⋃ b : Bool, (if b ∈ s then {a | f a = b} else (∅ : Set α)) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro ha
      exact ⟨f a, by rw [if_pos ha]; rfl⟩
    · rintro ⟨b, hbm⟩
      by_cases hbs : b ∈ s
      · rw [if_pos hbs] at hbm
        simp only [Set.mem_ofPred_eq] at hbm
        rw [hbm]; exact hbs
      · rw [if_neg hbs] at hbm
        exact absurd hbm (Set.notMem_empty a)
  rw [hset]
  refine MeasurableSet.iUnion fun b => ?_
  by_cases hbs : b ∈ s
  · rw [if_pos hbs]; exact hb b
  · rw [if_neg hbs]; exact MeasurableSet.empty

/-- The multiplier at a *fixed* site is ambient measurable. -/
lemma measurable_markB_fixed (p : ℝ) (m : ℕ) (j : Fin N) (y : ℤ) :
    Measurable fun U : Array N => markB p m j y U := by
  refine measurable_to_bool ?_
  have hset : {U : Array N | markB p m j y U = true} = {U : Array N | SiteMark p m U j y} := by
    ext U
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun hh => ?_, fun hh => markB_pos hh⟩
    by_contra hc
    rw [markB_neg hc] at hh
    exact Bool.false_ne_true hh
  rw [hset]
  exact measurableSet_siteMark_array p m j y

lemma measurable_rhoOf_markB_fixed (p : ℝ) (m : ℕ) (j : Fin N) (y : ℤ) :
    Measurable fun U : Array N => SwarmMarks.rhoOf p (markB p m j y U) :=
  (SwarmMarks.measurable_rhoOf p).comp (measurable_markB_fixed p m j y)

/-- The record value is ambient measurable, as a set-level statement. -/
lemma measurableSet_recVal_eq_ambient (p : ℝ) (m n : ℕ) (j : Fin N) (y : ℤ) :
    MeasurableSet {U : Array N | recVal j (prefOf p m n U) = y} :=
  enlRecMeas_le p m n j _ (measurableSet_recVal_eq p m n j y)

/-- **The multiplier at the random site `M_n^j + k` is ambient measurable.**  This is the point
where a static injection would fail: the site moves with the path, so measurability is obtained
by the countable-piece argument on the record value. -/
lemma measurable_rhoStep (p : ℝ) (m : ℕ) (n : ℕ) (j : Fin N) (k : ℕ) :
    Measurable (rhoStep p m n j k) := by
  have hfib : ∀ y : ℤ,
      MeasurableSet {U : Array N | recVal j (prefOf p m n U) + (k : ℤ) = y} := by
    intro y
    have hset : {U : Array N | recVal j (prefOf p m n U) + (k : ℤ) = y} =
        {U : Array N | recVal j (prefOf p m n U) = y - (k : ℤ)} := by
      ext U
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> omega
    rw [hset]
    exact measurableSet_recVal_eq_ambient p m n j (y - (k : ℤ))
  have h := SwarmIID.measurable_of_countable_pieces (Ω := Array N)
    (U := fun y : ℤ => fun U : Array N => SwarmMarks.rhoOf p (markB p m j y U))
    (fun y => measurable_rhoOf_markB_fixed p m j y)
    (fun U : Array N => recVal j (prefOf p m n U) + (k : ℤ)) hfib
  exact h

/-- **Measurability at a fixed site.**  If the read set `S` contains the whole row at each of the
sites `y, …, y+g`, then the potential evaluated at the shifted marks is `cylAt S`-measurable. -/
lemma measurable_hof_shiftAt {p : ℝ} (hp0 : p ≠ 0) (m : ℕ) (j : Fin N) (g : ℕ) (y : ℤ)
    (S : Finset (Fin N × ℤ × ℕ))
    (hrow : ∀ k ≤ g, ∀ k' ∈ Finset.Icc 1 (m - 1), (j, y + (k : ℤ), k') ∈ S) :
    Measurable[cylAt (N := N) S]
      (fun U : Array N => SwarmMarks.hof p (fun k : ℕ => markB p m j (y + (k : ℤ)) U) g) := by
  classical
  have hrowAgree : ∀ (U : Array N) (k : ℕ) (hk : k ≤ g),
      SiteMark p m U j (y + (k : ℤ)) ↔
        SiteMark p m (extendArr (S := S) fun c : ↥S => U (c : Fin N × ℤ × ℕ)) j (y + (k : ℤ)) := by
    intro U k hk
    refine siteMark_iff_of_agree (fun k' hk' => ?_)
    exact (extendArr_of_mem (S := S) (g := fun c : ↥S => U (c : Fin N × ℤ × ℕ))
      (hrow k hk k' hk')).symm
  have hagree : ∀ U : Array N,
      SwarmMarks.hof p (fun k : ℕ => markB p m j (y + (k : ℤ)) U) g =
        SwarmMarks.hof p (fun k : ℕ => markB p m j (y + (k : ℤ))
          (extendArr (S := S) fun c : ↥S => U (c : Fin N × ℤ × ℕ))) g := by
    intro U
    refine SwarmMarks.hof_congr g (fun k hk => ?_)
    by_cases h : SiteMark p m U j (y + (k : ℤ))
    · rw [markB_pos h, markB_pos ((hrowAgree U k hk).mp h)]
    · rw [markB_neg h, markB_neg (fun hh => h ((hrowAgree U k hk).mpr hh))]
  set F : (↥S → ℝ) → ℝ := fun gvec =>
    SwarmMarks.hof p (fun k : ℕ => markB p m j (y + (k : ℤ)) (extendArr gvec)) g with hFdef
  have hmark : ∀ k : ℕ, Measurable fun gvec : ↥S → ℝ =>
      markB p m j (y + (k : ℤ)) (extendArr (S := S) gvec) := by
    intro k
    refine measurable_to_bool ?_
    have hEq : {gvec : ↥S → ℝ | markB p m j (y + (k : ℤ)) (extendArr (S := S) gvec) = true} =
        {gvec : ↥S → ℝ | SiteMark p m (extendArr (S := S) gvec) j (y + (k : ℤ))} := by
      ext gvec
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hh
        by_contra hc
        rw [markB_neg hc] at hh
        exact Bool.false_ne_true hh
      · intro hh
        exact markB_pos hh
    rw [hEq]
    have hEq2 : {gvec : ↥S → ℝ | SiteMark p m (extendArr (S := S) gvec) j (y + (k : ℤ))} =
        ⋂ k' ∈ Finset.Icc 1 (m - 1),
          {gvec : ↥S → ℝ | p < extendArr (S := S) gvec (j, y + (k : ℤ), k')} := by
      ext gvec
      simp only [SiteMark, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hEq2]
    exact Finset.measurableSet_biInter _ (fun k' _ =>
      measurableSet_Ioi.preimage (measurable_extendArr (S := S) (j, y + (k : ℤ), k')))
  have hF : Measurable F :=
    (SwarmMarks.measurable_hof hp0 g).comp (measurable_pi_iff.2 hmark)
  have hproj : Measurable[cylAt (N := N) S]
      (fun U : Array N => (fun c : ↥S => U (c : Fin N × ℤ × ℕ))) := by
    intro T hT
    exact MeasurableSpace.measurableSet_comap.2 ⟨T, hT, rfl⟩
  have heq : (fun U : Array N => F (fun c : ↥S => U (c : Fin N × ℤ × ℕ))) =
      fun U : Array N => SwarmMarks.hof p (fun k : ℕ => markB p m j (y + (k : ℤ)) U) g := by
    funext U
    exact (hagree U).symm
  rw [← heq]
  exact hF.comp hproj

/-- **The `g`-th record information contains the whole row at every site `M, M+1, …, M+g`.** -/
lemma recInfo_row_mem {m : ℕ} (j : Fin N) (g : ℕ) {n : ℕ} (γ : Pref N n) {k : ℕ}
    (hk : k ≤ g) {k' : ℕ} (hk' : k' ∈ Finset.Icc 1 (m - 1)) :
    (j, recVal j γ + (k : ℤ), k') ∈ recInfo (N := N) m j g γ := by
  rcases Nat.eq_zero_or_pos k with hk0 | hpos
  · subst hk0
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (mem_recRow.mpr ⟨k', hk', by simp⟩))
  · refine Finset.mem_union_right _ ?_
    rw [Finset.mem_biUnion]
    exact ⟨k, Finset.mem_Icc.mpr ⟨hpos, hk⟩, mem_recRow.mpr ⟨k', hk', rfl⟩⟩

/-- **The shifted potential is measurable for the `g`-th record information.** -/
theorem measurable_shiftH {p : ℝ} (hp0 : p ≠ 0) (m n : ℕ) (j : Fin N) (g : ℕ) :
    Measurable[infoPiece p m n j g] (shiftH p m n j g) := by
  refine measurable_pieceMeas (f' := fun γ U =>
    SwarmMarks.hof p (fun k : ℕ => markB p m j (recVal j γ + (k : ℤ)) U) g) (fun γ => ?_) ?_
  · exact measurable_hof_shiftAt (N := N) hp0 m j g (recVal j γ) (recInfo (N := N) m j g γ)
      (fun k hk k' hk' => recInfo_row_mem j g γ hk hk')
  · intro γ U hU
    show SwarmMarks.hof p (markSeq p m n j U) g =
      SwarmMarks.hof p (fun k : ℕ => markB p m j (recVal j γ + (k : ℤ)) U) g
    have hseq : markSeq p m n j U = fun k : ℕ => markB p m j (recVal j γ + (k : ℤ)) U := by
      funext k
      rw [show markSeq p m n j U k
        = markB p m j (recVal j (prefOf p m n U) + (k : ℤ)) U from rfl,
        recVal_prefOf_of_mem hU j]
    rw [hseq]

lemma stronglyMeasurable_shiftH {p : ℝ} (hp0 : p ≠ 0) (m n : ℕ) (j : Fin N) (g : ℕ) :
    StronglyMeasurable[infoPiece p m n j g] (fun U => 1 + shiftH p m n j g U) :=
  (measurable_const.add (measurable_shiftH hp0 m n j g)).stronglyMeasurable

lemma measurable_shiftH_ambient {p : ℝ} (hp0 : p ≠ 0) (m n : ℕ) (j : Fin N) (g : ℕ) :
    Measurable (shiftH p m n j g) := by
  have hle : infoPiece p m n j g ≤ (inferInstance : MeasurableSpace (Array N)) :=
    infoPiece_le p m n j g
  have hmeas : Measurable[infoPiece p m n j g] (shiftH p m n j g) := measurable_shiftH hp0 m n j g
  intro s hs
  exact hle ((shiftH p m n j g) ⁻¹' s) (hmeas hs)

lemma integrable_shiftH {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    (m n : ℕ) (j : Fin N) (g : ℕ) : Integrable (shiftH p m n j g) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.mono' (integrable_const (2 * (g : ℝ) + 3))
    (measurable_shiftH_ambient hp0 m n j g).aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs]
  exact abs_shiftH_le hp1 hp2 hp0 m n j g U

lemma integrable_rhoStep {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m n : ℕ) (j : Fin N)
    (k : ℕ) : Integrable (rhoStep p m n j k) (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_rhoStep p m n j k).aestronglyMeasurable (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs]
  exact abs_rhoStep_le hp1 hp2 m n j k U

lemma integrable_rhoStep_mul_shiftH {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (hp0 : p ≠ 0)
    (m n : ℕ) (j : Fin N) (g : ℕ) :
    Integrable (fun U => rhoStep p m n j (g + 1) U * (1 + shiftH p m n j g U))
      (arrayMeasure N) := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  refine Integrable.mono' (integrable_const (2 * (g : ℝ) + 5))
    (((measurable_rhoStep p m n j (g + 1)).mul
      (measurable_const.add (measurable_shiftH_ambient hp0 m n j g)))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |rhoStep p m n j (g + 1) U| ≤ 1 := abs_rhoStep_le hp1 hp2 m n j (g + 1) U
  have h2 : |1 + shiftH p m n j g U| ≤ 2 * (g : ℝ) + 4 := by
    have h3 := abs_shiftH_le hp1 hp2 hp0 m n j g U
    have h4 : |1 + shiftH p m n j g U| ≤ 1 + |shiftH p m n j g U| := by
      simpa using abs_add_le (1 : ℝ) (shiftH p m n j g U)
    linarith
  calc |rhoStep p m n j (g + 1) U| * |1 + shiftH p m n j g U| ≤ 1 * (2 * (g : ℝ) + 4) :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ ≤ 2 * (g : ℝ) + 5 := by linarith

end Swarming.Enl
