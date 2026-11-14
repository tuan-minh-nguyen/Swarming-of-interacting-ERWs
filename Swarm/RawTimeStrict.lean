/-
Measurable raw-time events for the strict first-regeneration decomposition.

This file uses only the concrete path predicates from `RegenPath` and the
actual array factorisation from `LowEvent`. It does not use finite-horizon
families, stationarity, or an enriched-chain law assumption.
-/
import Swarm.LowEvent

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SwarmRawTimeStrict

variable {N : ℕ}

/-- A finite value of the first hitting time is a measurable path event. -/
theorem measurableSet_tau_eq (r : ℤ) (t : ℕ) :
    MeasurableSet {X : RegenPath.Path N | RegenPath.tau X r = (t : ℕ∞)} := by
  have hmeas (n : ℕ) (i : Fin N) :
      MeasurableSet {X : RegenPath.Path N | X n i = r} :=
    by
      have hn : Measurable (fun X : RegenPath.Path N => X n) := measurable_pi_apply n
      have hni : Measurable (fun X : RegenPath.Path N => X n i) :=
        (measurable_pi_apply i).comp hn
      exact hni (measurableSet_singleton r)
  have hne (n : ℕ) (i : Fin N) :
      MeasurableSet {X : RegenPath.Path N | X n i ≠ r} := by
    simpa only [Set.compl_setOf] using (hmeas n i).compl
  have heq : {X : RegenPath.Path N | RegenPath.tau X r = (t : ℕ∞)} =
      (⋃ i : Fin N, {X : RegenPath.Path N | X t i = r}) ∩
        ⋂ n : ℕ, ⋂ (_ : n < t), ⋂ i : Fin N,
          {X : RegenPath.Path N | X n i ≠ r} := by
    ext X
    simp only [RegenPath.tau_eq_iff, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iUnion, Set.mem_iInter]
  rw [heq]
  exact (MeasurableSet.iUnion fun i => hmeas t i).inter
    (MeasurableSet.iInter fun n => MeasurableSet.iInter fun _hn =>
      MeasurableSet.iInter fun i => hne n i)

/-- A regeneration at a specified integer level is measurable. -/
theorem measurableSet_reg (r : ℤ) :
    MeasurableSet {X : RegenPath.Path N | RegenPath.Reg X r} := by
  have heval (n : ℕ) (i : Fin N) : Measurable (fun X : RegenPath.Path N => X n i) := by
    have hn : Measurable (fun X : RegenPath.Path N => X n) := measurable_pi_apply n
    exact (measurable_pi_apply i).comp hn
  have heq (n : ℕ) (i : Fin N) :
      MeasurableSet {X : RegenPath.Path N | X n i = r} :=
    heval n i (measurableSet_singleton r)
  have hgt (n : ℕ) (i : Fin N) :
      MeasurableSet {X : RegenPath.Path N | r < X n i} :=
    heval n i measurableSet_Ioi
  have hset : {X : RegenPath.Path N | RegenPath.Reg X r} =
      ⋃ t : ℕ, {X : RegenPath.Path N | RegenPath.tau X r = (t : ℕ∞)} ∩
        ((⋂ i : Fin N, {X : RegenPath.Path N | X t i = r}) ∩
          ⋂ n : ℕ, ⋂ (_ : t < n), ⋂ i : Fin N,
            {X : RegenPath.Path N | r < X n i}) := by
    ext X
    simp only [RegenPath.Reg, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter]
  rw [hset]
  refine MeasurableSet.iUnion fun t => (measurableSet_tau_eq r t).inter ?_
  exact (MeasurableSet.iInter fun i => heq t i).inter
    (MeasurableSet.iInter fun n => MeasurableSet.iInter fun _hn =>
      MeasurableSet.iInter fun i => hgt n i)

/-- A finite value of the first positive regeneration level is characterized by
regeneration at that level and failure at every earlier positive level. -/
theorem D_eq_iff (X : RegenPath.Path N) (d : ℕ) (hd : 1 ≤ d) :
    RegenPath.D X = (d : ℕ∞) ↔
      RegenPath.Reg X (d : ℤ) ∧
        ∀ e : ℕ, 1 ≤ e → e < d → ¬ RegenPath.Reg X (e : ℤ) := by
  classical
  constructor
  · intro hD
    have hex : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ) := by
      by_contra hcon
      unfold RegenPath.D at hD
      rw [dif_neg hcon] at hD
      simp at hD
    have hfind : Nat.find hex = d := by
      unfold RegenPath.D at hD
      rw [dif_pos hex] at hD
      exact_mod_cast hD
    refine ⟨?_, ?_⟩
    · have h := (Nat.find_spec hex).2
      rwa [hfind] at h
    · intro e he1 hed hreg
      have hle : Nat.find hex ≤ e := Nat.find_min' hex ⟨he1, hreg⟩
      omega
  · rintro ⟨hreg, hmin⟩
    have hex : ∃ r : ℕ, 1 ≤ r ∧ RegenPath.Reg X (r : ℤ) := ⟨d, hd, hreg⟩
    have hge : d ≤ Nat.find hex := by
      by_contra hcon
      push Not at hcon
      exact hmin (Nat.find hex) (Nat.find_spec hex).1 hcon (Nat.find_spec hex).2
    have hfind : Nat.find hex = d :=
      le_antisymm (Nat.find_min' hex ⟨hd, hreg⟩) hge
    unfold RegenPath.D
    rw [dif_pos hex, hfind]

/-- Finite values of the first positive regeneration level are measurable. -/
theorem measurableSet_D_eq (d : ℕ) (hd : 1 ≤ d) :
    MeasurableSet {X : RegenPath.Path N | RegenPath.D X = (d : ℕ∞)} := by
  have hreg (e : ℕ) : MeasurableSet {X : RegenPath.Path N |
      RegenPath.Reg X ((e : ℤ))} := measurableSet_reg (e : ℤ)
  have hnot (e : ℕ) : MeasurableSet {X : RegenPath.Path N |
      ¬ RegenPath.Reg X ((e : ℤ))} := by
    simpa only [Set.compl_setOf] using (hreg e).compl
  have hset : {X : RegenPath.Path N | RegenPath.D X = (d : ℕ∞)} =
      {X : RegenPath.Path N | RegenPath.Reg X (d : ℤ)} ∩
        ⋂ e : ℕ, ⋂ (_ : 1 ≤ e), ⋂ (_ : e < d),
          {X : RegenPath.Path N | ¬ RegenPath.Reg X (e : ℤ)} := by
    ext X
    simp only [D_eq_iff X d hd, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter]
  rw [hset]
  exact (measurableSet_reg (d : ℤ)).inter
    (MeasurableSet.iInter fun e => MeasurableSet.iInter fun _he1 =>
      MeasurableSet.iInter fun _hed => hnot e)

/-- Every concrete first-block event `Cdt` is measurable in path space. -/
theorem measurableSet_Cdt (d t : ℕ) :
    MeasurableSet {X : RegenPath.Path N | RegenPath.Cdt X d t} := by
  have heval (n : ℕ) (i : Fin N) : Measurable (fun X : RegenPath.Path N => X n i) := by
    have hn : Measurable (fun X : RegenPath.Path N => X n) := measurable_pi_apply n
    exact (measurable_pi_apply i).comp hn
  have heq (n : ℕ) (i : Fin N) (r : ℤ) :
      MeasurableSet {X : RegenPath.Path N | X n i = r} :=
    heval n i (measurableSet_singleton r)
  have hpos (n : ℕ) (i : Fin N) :
      MeasurableSet {X : RegenPath.Path N | 0 < X n i} :=
    heval n i measurableSet_Ioi
  have hlt (n : ℕ) (i : Fin N) (r : ℤ) :
      MeasurableSet {X : RegenPath.Path N | X n i < r} :=
    heval n i measurableSet_Iio
  have hle (n : ℕ) (i : Fin N) (r : ℤ) :
      MeasurableSet {X : RegenPath.Path N | X n i ≤ r} :=
    heval n i measurableSet_Iic
  have hset : {X : RegenPath.Path N | RegenPath.Cdt X d t} =
      {X : RegenPath.Path N | RegenPath.tau X (d : ℤ) = (t : ℕ∞)} ∩
        ((⋂ i : Fin N, {X : RegenPath.Path N | X t i = (d : ℤ)}) ∩
          ((⋂ n : ℕ, ⋂ (_ : 0 < n), ⋂ (_ : n ≤ t), ⋂ i : Fin N,
              {X : RegenPath.Path N | 0 < X n i}) ∩
            ⋂ e : ℕ, ⋂ (_ : 1 ≤ e), ⋂ (_ : e < d), ⋃ te : ℕ,
              {X : RegenPath.Path N | RegenPath.tau X (e : ℤ) = (te : ℕ∞)} ∩
                ((⋃ i : Fin N, {X : RegenPath.Path N | X te i < (e : ℤ)}) ∪
                  ⋃ n : ℕ, ⋃ (_ : te < n), ⋃ (_ : n ≤ t), ⋃ i : Fin N,
                    {X : RegenPath.Path N | X n i ≤ (e : ℤ)}))) := by
    ext X
    simp only [RegenPath.Cdt, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_iUnion, Set.mem_union, exists_prop]
  rw [hset]
  refine (measurableSet_tau_eq (d : ℤ) t).inter ((MeasurableSet.iInter fun i =>
    heq t i (d : ℤ)).inter ?_)
  refine (MeasurableSet.iInter fun n => MeasurableSet.iInter fun _hn =>
    MeasurableSet.iInter fun _hnt => MeasurableSet.iInter fun i => hpos n i).inter ?_
  refine MeasurableSet.iInter fun e => MeasurableSet.iInter fun _he1 =>
    MeasurableSet.iInter fun _hed => MeasurableSet.iUnion fun te =>
      (measurableSet_tau_eq (e : ℤ) te).inter ((MeasurableSet.iUnion fun i =>
        hlt te i (e : ℤ)).union ?_)
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _hten =>
    MeasurableSet.iUnion fun _hnt => MeasurableSet.iUnion fun i => hle n i (e : ℤ)

/-- The strict first-block identity transported to the actual array path, with an
arbitrary event on the relative future. -/
theorem array_firstBlock_future_set (p : ℝ) (m d t : ℕ) (hd : 1 ≤ d)
    (B : Set (ℕ → Fin N → ℤ)) :
    {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∧
          RegenPath.D (SwarmRestart.posPath p m U) = (d : ℕ∞) ∧
          RegenPath.tau (SwarmRestart.posPath p m U) (d : ℤ) = (t : ℕ∞) ∧
          SwarmFresh.relFuture p m U t (d : ℤ) ∈ B} =
      {U : Swarming.Uniform.Array N |
        RegenPath.Cdt (SwarmRestart.posPath p m U) d t ∧
          SwarmFresh.relFuture p m U t (d : ℤ) ∈
            SwarmFresh.strictPos (N := N) ∩ B} := by
  ext U
  change (SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∧
      RegenPath.D (SwarmRestart.posPath p m U) = (d : ℕ∞) ∧
      RegenPath.tau (SwarmRestart.posPath p m U) (d : ℤ) = (t : ℕ∞) ∧
      SwarmFresh.relFuture p m U t (d : ℤ) ∈ B) ↔
    (RegenPath.Cdt (SwarmRestart.posPath p m U) d t ∧
      SwarmFresh.relFuture p m U t (d : ℤ) ∈ SwarmFresh.strictPos (N := N) ∧
      SwarmFresh.relFuture p m U t (d : ℤ) ∈ B)
  have hfirst := RegenPath.first_block_identity (SwarmRestart.posPath p m U)
    (SwarmFresh.posPath_zero p m U) (SwarmFresh.posPath_step p m U) d t hd
  constructor
  · rintro ⟨hS, hD, htau, hB⟩
    have hb := hfirst.mp ⟨(SwarmFresh.strictPos_iff_V p m U).mp hS, hD, htau⟩
    have hv := (SwarmFresh.Vdt_iff_relFuture
      (SwarmFresh.Cdt_recordAt p m U hb.1)).mp hb.2
    exact ⟨hb.1, hv, hB⟩
  · rintro ⟨hC, hV, hB⟩
    have hvdt := (SwarmFresh.Vdt_iff_relFuture
      (SwarmFresh.Cdt_recordAt p m U hC)).mpr hV
    have hb := hfirst.mpr ⟨hC, hvdt⟩
    exact ⟨(SwarmFresh.strictPos_iff_V p m U).mpr hb.1, hb.2.1, hb.2.2, hB⟩

/-- The strict first-block path event is measurable on the actual array. -/
theorem measurableSet_arrayFirstBlock (p : ℝ) (m d t : ℕ) (hd : 1 ≤ d) :
    MeasurableSet {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∧
        RegenPath.D (SwarmRestart.posPath p m U) = (d : ℕ∞) ∧
        RegenPath.tau (SwarmRestart.posPath p m U) (d : ℤ) = (t : ℕ∞)} := by
  have hS : MeasurableSet {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} :=
    (SwarmRestart.measurable_posPath p m N) SwarmFresh.measurableSet_strictPos
  have hD : MeasurableSet {U : Swarming.Uniform.Array N |
      RegenPath.D (SwarmRestart.posPath p m U) = (d : ℕ∞)} :=
    (SwarmRestart.measurable_posPath p m N) (measurableSet_D_eq d hd)
  have htau : MeasurableSet {U : Swarming.Uniform.Array N |
      RegenPath.tau (SwarmRestart.posPath p m U) (d : ℤ) = (t : ℕ∞)} :=
    (SwarmRestart.measurable_posPath p m N) (measurableSet_tau_eq (d : ℤ) t)
  exact hS.inter (hD.inter htau)

/-- The first-block event with a measurable relative-future condition is measurable. -/
theorem measurableSet_arrayFirstBlock_future (p : ℝ) (m d t : ℕ) (hd : 1 ≤ d)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    MeasurableSet {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∧
        RegenPath.D (SwarmRestart.posPath p m U) = (d : ℕ∞) ∧
        RegenPath.tau (SwarmRestart.posPath p m U) (d : ℤ) = (t : ℕ∞) ∧
        SwarmFresh.relFuture p m U t (d : ℤ) ∈ B} := by
  rw [array_firstBlock_future_set p m d t hd B]
  have hC : MeasurableSet {U : Swarming.Uniform.Array N |
      RegenPath.Cdt (SwarmRestart.posPath p m U) d t} :=
    (SwarmRestart.measurable_posPath p m N) (measurableSet_Cdt d t)
  have hrel (S : Set (ℕ → Fin N → ℤ)) (hS : MeasurableSet S) :
      MeasurableSet {U : Swarming.Uniform.Array N |
        SwarmFresh.relFuture p m U t (d : ℤ) ∈ S} :=
    (SwarmFresh.measurable_relFuture p m t (d : ℤ) N) hS
  exact hC.inter (hrel _ (SwarmFresh.measurableSet_strictPos.inter hB))

/-- `Cdt` depends only on the path through its own horizon `t`.  The explicit
nearest-neighbour hypotheses are used to bound every earlier-level hitting
witness by `t`. -/
theorem Cdt_congr_of_eq_upto {X Y : RegenPath.Path N} (d t : ℕ)
    (hXY : ∀ n, n ≤ t → ∀ i, X n i = Y n i)
    (hX0 : ∀ i, X 0 i = 0)
    (hXNN : ∀ n i, |X (n + 1) i - X n i| = 1)
    (hC : RegenPath.Cdt X d t) : RegenPath.Cdt Y d t := by
  have htau (r : ℤ) (s : ℕ) (hs : s ≤ t) (hrs : RegenPath.tau X r = (s : ℕ∞)) :
      RegenPath.tau Y r = (s : ℕ∞) := by
    rw [RegenPath.tau_eq_iff] at hrs ⊢
    obtain ⟨⟨i, hi⟩, hmin⟩ := hrs
    refine ⟨⟨i, ?_⟩, ?_⟩
    · rw [← hXY s hs i]
      exact hi
    · intro n hn i hYi
      apply hmin n hn i
      rw [hXY n ((Nat.le_of_lt hn).trans hs) i]
      exact hYi
  refine ⟨htau (d : ℤ) t le_rfl hC.1, ?_, ?_, ?_⟩
  · intro i
    rw [← hXY t le_rfl i]
    exact hC.2.1 i
  · intro n hn hnt i
    rw [← hXY n hnt i]
    exact hC.2.2.1 n hn hnt i
  · intro e he1 hed
    obtain ⟨te, hte, hfail⟩ := hC.2.2.2 e he1 hed
    have he0 : (0 : ℤ) ≤ (e : ℤ) := by exact_mod_cast Nat.zero_le e
    have hedZ : (e : ℤ) < (d : ℤ) := by exact_mod_cast hed
    have htelt : te < t := by
      have hlt := RegenPath.tau_lt_of_lt hX0 hXNN hC.1 he0 hedZ
      rw [hte] at hlt
      exact_mod_cast hlt
    refine ⟨te, htau (e : ℤ) te (Nat.le_of_lt htelt) hte, ?_⟩
    rcases hfail with ⟨i, hi⟩ | ⟨n, hten, hnt, i, hi⟩
    · left
      refine ⟨i, ?_⟩
      rw [← hXY te (Nat.le_of_lt htelt) i]
      exact hi
    · right
      refine ⟨n, hten, hnt, i, ?_⟩
      rw [← hXY n hnt i]
      exact hi

/-- The actual-array `Cdt` event reads only array coordinates below its level. -/
theorem Cdt_array_congr_of_agree {p : ℝ} {m d t : ℕ}
    {U V : Swarming.Uniform.Array N}
    (harr : ∀ (i : Fin N) (x : ℤ) (k : ℕ), x < (d : ℤ) →
      U (i, x, k) = V (i, x, k))
    (hC : RegenPath.Cdt (SwarmRestart.posPath p m U) d t) :
    RegenPath.Cdt (SwarmRestart.posPath p m V) d t := by
  apply Cdt_congr_of_eq_upto d t ?_ (SwarmFresh.posPath_zero p m U)
    (SwarmFresh.posPath_step p m U) hC
  intro n hn i
  have hlt : ∀ k, k < n → ∀ j, (Swarming.Trajectory.trajectory p m U k).pos j < (d : ℤ) :=
    fun k hk => SwarmFresh.Cdt_pos_lt p m U hC k (by omega)
  exact (SwarmFresh.agreeBelow_traj (p := p) (m := m) harr n hlt).1 i

/-- The exact low-block representation of a concrete first-block event. -/
def CdtLow (p : ℝ) (m d t : ℕ) :
    Set (SwarmFresh.lowSet (N := N) (d : ℤ) → ℝ) :=
  {V | RegenPath.Cdt
    (SwarmRestart.posPath p m (SwarmFresh.lowExtend (N := N) (d : ℤ) V)) d t}

/-- Restricting an array to its low block and extending it with junk recovers
exactly the same `Cdt` event. -/
theorem mem_CdtLow_iff (p : ℝ) (m d t : ℕ) (U : Swarming.Uniform.Array N) :
    (SwarmFresh.lowSet (N := N) (d : ℤ)).domRestrict U ∈ CdtLow p m d t ↔
      RegenPath.Cdt (SwarmRestart.posPath p m U) d t := by
  change RegenPath.Cdt (SwarmRestart.posPath p m
    (SwarmFresh.lowExtend (N := N) (d : ℤ)
      ((SwarmFresh.lowSet (N := N) (d : ℤ)).domRestrict U))) d t ↔ _
  constructor
  · intro h
    exact Cdt_array_congr_of_agree
      (SwarmFresh.lowExtend_domRestrict_agree (N := N) (d : ℤ) U) h
  · intro h
    apply Cdt_array_congr_of_agree (U := U)
      (V := SwarmFresh.lowExtend (N := N) (d : ℤ)
        ((SwarmFresh.lowSet (N := N) (d : ℤ)).domRestrict U)) ?_ h
    intro i x k hx
    exact (SwarmFresh.lowExtend_domRestrict_agree (N := N) (d : ℤ) U i x k hx).symm

/-- The low-block representation of `Cdt` is measurable. -/
theorem measurableSet_CdtLow (p : ℝ) (m d t : ℕ) :
    MeasurableSet (CdtLow (N := N) p m d t) := by
  have hpath : Measurable (fun V : SwarmFresh.lowSet (N := N) (d : ℤ) → ℝ =>
      SwarmRestart.posPath p m (SwarmFresh.lowExtend (N := N) (d : ℤ) V)) :=
    (SwarmRestart.measurable_posPath p m N).comp
      (SwarmFresh.measurable_lowExtend (N := N) (d : ℤ))
  exact hpath (measurableSet_Cdt d t)

/-- Exact factorisation of a concrete first-block low event against an arbitrary
measurable strict relative-future event. -/
theorem array_cdt_future_mass (p : ℝ) (m d t : ℕ)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
      RegenPath.Cdt (SwarmRestart.posPath p m U) d t ∧
        SwarmFresh.relFuture p m U t (d : ℤ) ∈
          SwarmFresh.strictPos (N := N) ∩ B} =
      (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
        RegenPath.Cdt (SwarmRestart.posPath p m U) d t} *
      (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B} := by
  have hsub (U : Swarming.Uniform.Array N)
      (hU : (SwarmFresh.lowSet (N := N) (d : ℤ)).domRestrict U ∈ CdtLow p m d t) :
      SwarmRestart.RecordAt p m U t (d : ℤ) :=
    SwarmFresh.Cdt_recordAt p m U ((mem_CdtLow_iff p m d t U).mp hU)
  have hfactor := SwarmFresh.freshlaw_lowEvent (N := N) p m t (d : ℤ)
    (measurableSet_CdtLow p m d t) hsub SwarmFresh.measurableSet_strictPos
    SwarmFresh.strictPos_subset_nonnegPath hB
  have hset : {U : Swarming.Uniform.Array N |
      (SwarmFresh.lowSet (N := N) (d : ℤ)).domRestrict U ∈ CdtLow p m d t} =
      {U : Swarming.Uniform.Array N |
        RegenPath.Cdt (SwarmRestart.posPath p m U) d t} := by
    ext U
    exact mem_CdtLow_iff p m d t U
  change (Swarming.Uniform.arrayMeasure N)
    (({U : Swarming.Uniform.Array N | RegenPath.Cdt (SwarmRestart.posPath p m U) d t} :
      Set (Swarming.Uniform.Array N)) ∩
      {U | SwarmFresh.relFuture p m U t (d : ℤ) ∈
        SwarmFresh.strictPos (N := N) ∩ B}) = _
  rw [← hset]
  exact hfactor

/-- Actual strict first-block mass, factorised into its concrete low event and
an arbitrary canonical fresh strict future event. -/
theorem array_firstBlock_future_mass (p : ℝ) (m d t : ℕ) (hd : 1 ≤ d)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
      SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∧
        RegenPath.D (SwarmRestart.posPath p m U) = (d : ℕ∞) ∧
        RegenPath.tau (SwarmRestart.posPath p m U) (d : ℤ) = (t : ℕ∞) ∧
        SwarmFresh.relFuture p m U t (d : ℤ) ∈ B} =
      (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
        RegenPath.Cdt (SwarmRestart.posPath p m U) d t} *
      (Swarming.Uniform.arrayMeasure N) {U : Swarming.Uniform.Array N |
        SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N) ∩ B} := by
  rw [array_firstBlock_future_set p m d t hd B, array_cdt_future_mass p m d t hB]

end SwarmRawTimeStrict
