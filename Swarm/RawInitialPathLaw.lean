/-
Raw arbitrary-start first positive regeneration cells and their path law.

The original path is NOT assumed to be strictly positive.  Removing that clause
from `SwarmSel.Cpath` leaves a genuine finite-prefix first-regeneration event.
`freshlawStrict_past` then supplies the exact fresh future factorisation.  The
result is scoped to the union of completed raw regeneration cells; exhaustiveness
of that union is a separate stochastic input, not an assertion made here.
-/
import Swarm.RawStrictTransport
import Swarm.SegmentStrict
import Swarm.FreshPast
import Swarm.Selection
import Swarm.BlockLevelKac

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace RawInitialPathLaw

open Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh SwarmSeg
open RawStrictTransport SwarmRawTimeStrictSum

variable {N : ℕ}

/-- Record events through a common finite horizon depend only on values there. -/
theorem pathRec_congr_of_eq_upto {X Y : ℕ → Fin N → ℤ} {u : ℕ × ℤ} {T : ℕ}
    (hu : u.1 ≤ T) (hXY : ∀ n, n ≤ T → ∀ i, X n i = Y n i) :
    SwarmChain.pathRec u.1 u.2 X ↔ SwarmChain.pathRec u.1 u.2 Y := by
  constructor
  · rintro ⟨hlt, hat⟩
    refine ⟨?_, ?_⟩
    · intro n hn i
      rw [← hXY n (hn.le.trans hu) i]
      exact hlt n hn i
    · intro i
      rw [← hXY u.1 hu i]
      exact hat i
  · rintro ⟨hlt, hat⟩
    refine ⟨?_, ?_⟩
    · intro n hn i
      rw [hXY n (hn.le.trans hu) i]
      exact hlt n hn i
    · intro i
      rw [hXY u.1 hu i]
      exact hat i

/-- The no-earlier-positive-regeneration prefix condition has the same finitary
semantics; in particular it does not include the original-path `V` clause. -/
theorem noEarlyRegen_congr_of_eq_upto {X Y : ℕ → Fin N → ℤ} {t : ℕ} {d : ℤ}
    (hXY : ∀ n, n ≤ t → ∀ i, X n i = Y n i) :
    SwarmSel.noEarlyRegen t d X ↔ SwarmSel.noEarlyRegen t d Y := by
  constructor <;> intro h e he1 hed u hu hrec
  · obtain ⟨n, hun, hnt, i, hi⟩ := h e he1 hed u hu
      ((pathRec_congr_of_eq_upto (u := (u, e)) (T := t) hu.le hXY).mpr hrec)
    exact ⟨n, hun, hnt, i, by rwa [hXY n hnt i] at hi⟩
  · obtain ⟨n, hun, hnt, i, hi⟩ := h e he1 hed u hu
      ((pathRec_congr_of_eq_upto (u := (u, e)) (T := t) hu.le hXY).mp hrec)
    exact ⟨n, hun, hnt, i, by rwa [← hXY n hnt i] at hi⟩

/-- The finite prefix carrying the record and no-earlier-positive-regeneration
conditions, with no assumption that the original path is in `V`. -/
def rawPrefix (t : ℕ) (d : ℤ) : Set (Fin (t + 1) → Fin N → ℤ) :=
  {Y | SwarmChain.pathRec t d (SwarmSeg.pastExtend t Y) ∧
    SwarmSel.noEarlyRegen t d (SwarmSeg.pastExtend t Y)}

@[simp] theorem measurableSet_rawPrefix (t : ℕ) (d : ℤ) :
    MeasurableSet (rawPrefix (N := N) t d) := MeasurableSet.of_discrete

/-- On the actual trajectory this is exactly the raw record/no-earlier pair. -/
theorem mem_rawPrefix (p : ℝ) (m t : ℕ) (d : ℤ) (U : Array N) :
    pastProj p m t U ∈ rawPrefix t d ↔
      SwarmChain.pathRec t d (posPath p m U) ∧ SwarmSel.noEarlyRegen t d (posPath p m U) := by
  have hXY : ∀ n, n ≤ t → ∀ i,
      pastExtend t (pastProj p m t U) n i = posPath p m U n i :=
    fun n hn i => pastExtend_pastProj p m t U hn i
  rw [rawPrefix, Set.mem_ofPred_eq, pathRec_congr_of_eq_upto (u := (t, d)) (T := t) le_rfl hXY,
    noEarlyRegen_congr_of_eq_upto hXY]

/-- A concrete first positive regeneration cell on an arbitrary raw array.
The future is conditioned on strict positivity and `B`; the prefix is not. -/
def rawFirstCell (p : ℝ) (m : ℕ) (q : LevelTime)
    (B : Set (ℕ → Fin N → ℤ)) : Set (Array N) :=
  {U | RecordAt p m U q.1.2 (q.1.1 : ℤ) ∧
    pastProj p m q.1.2 U ∈ rawPrefix q.1.2 (q.1.1 : ℤ) ∧
    relFuture p m U q.1.2 (q.1.1 : ℤ) ∈ strictPos (N := N) ∩ B}

/-- The cell in the genuine selector language. -/
theorem mem_rawFirstCell (p : ℝ) (m : ℕ) (q : LevelTime)
    (B : Set (ℕ → Fin N → ℤ)) (U : Array N) :
    U ∈ rawFirstCell p m q B ↔
      SwarmSel.isRegen q.1.2 (q.1.1 : ℤ) (posPath p m U) ∧
        SwarmSel.noEarlyRegen q.1.2 (q.1.1 : ℤ) (posPath p m U) ∧
        relFuture p m U q.1.2 (q.1.1 : ℤ) ∈ B := by
  rw [rawFirstCell, Set.mem_ofPred_eq, mem_rawPrefix]
  change (SwarmChain.pathRec q.1.2 (q.1.1 : ℤ) (posPath p m U) ∧
    (SwarmChain.pathRec q.1.2 (q.1.1 : ℤ) (posPath p m U) ∧ _) ∧ _) ↔ _
  rw [SwarmSel.isRegen_iff_relFuture]
  simp only [Set.mem_inter_iff]
  tauto

/-- Every raw cell with a measurable future condition is measurable. -/
theorem measurableSet_rawFirstCell (p : ℝ) (m : ℕ) (q : LevelTime)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    MeasurableSet (rawFirstCell (N := N) p m q B) := by
  exact (measurableSet_recordSet p m q.1.2 (q.1.1 : ℤ)).inter
    (((measurable_pastProj p m q.1.2 N) (measurableSet_rawPrefix q.1.2 (q.1.1 : ℤ))).inter
      ((measurable_relFuture p m q.1.2 (q.1.1 : ℤ) N)
        (measurableSet_strictPos.inter hB)))

/-- Exact fixed-cell factorisation from the actual arbitrary raw prefix. -/
theorem rawFirstCell_mass (p : ℝ) (m : ℕ) (q : LevelTime)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) (rawFirstCell p m q B) =
      (arrayMeasure N) (recordPastSet p m q.1.2 (q.1.1 : ℤ)
        (rawPrefix q.1.2 (q.1.1 : ℤ))) *
      (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B} := by
  exact freshlawStrict_past p m q.1.2 (q.1.1 : ℤ)
    (measurableSet_rawPrefix q.1.2 (q.1.1 : ℤ)) hB

/-- The same factorisation, divided by the strict seed mass. -/
theorem rawFirstCell_normalized_mass (p : ℝ) (m N : ℕ) (q : LevelTime)
    (hV : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0)
    (hVtop : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ ⊤)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) (rawFirstCell p m q B) =
      (arrayMeasure N) (rawFirstCell p m q Set.univ) * normalizedStrictLaw p m N B := by
  let V : ℝ≥0∞ := (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)}
  let A : ℝ≥0∞ := (arrayMeasure N) (recordPastSet p m q.1.2 (q.1.1 : ℤ)
    (rawPrefix q.1.2 (q.1.1 : ℤ)))
  let X : ℝ≥0∞ := (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N) ∩ B}
  have htotal : (arrayMeasure N) (rawFirstCell p m q Set.univ) = A * V := by
    simpa [A, V] using rawFirstCell_mass (N := N) p m q (B := Set.univ) MeasurableSet.univ
  have hfactor : (A * V) * (V⁻¹ * X) = A * X := by
    calc
      (A * V) * (V⁻¹ * X) = A * ((V * V⁻¹) * X) := by simp only [mul_assoc]
      _ = A * (1 * X) := by rw [ENNReal.mul_inv_cancel hV hVtop]
      _ = A * X := by rw [one_mul]
  rw [normalizedStrictLaw_apply p m N hB]
  calc
    (arrayMeasure N) (rawFirstCell p m q B) = A * X := by
      simpa [A, X] using rawFirstCell_mass (N := N) p m q hB
    _ = (A * V) * (V⁻¹ * X) := hfactor.symm
    _ = (arrayMeasure N) (rawFirstCell p m q Set.univ) * (V⁻¹ * X) := by
      rw [← htotal]


/-- On any nearest-neighbour path started at zero, the raw no-earlier cells are
exactly the finite values of the source's `D` and `tau_D`.  No original `V`
hypothesis is needed. -/
theorem isRegen_noEarlyRegen_iff_D_tau [Nonempty (Fin N)] (X : RegenPath.Path N)
    (hX0 : ∀ i, X 0 i = 0) (hNN : ∀ n i, |X (n + 1) i - X n i| = 1)
    {t d : ℕ} (hd : 1 ≤ d) :
    (SwarmSel.isRegen t (d : ℤ) X ∧ SwarmSel.noEarlyRegen t (d : ℤ) X) ↔
      RegenPath.D X = (d : ℕ∞) ∧ RegenPath.tau X (d : ℤ) = (t : ℕ∞) := by
  constructor
  · rintro ⟨hreg, hno⟩
    have htau : RegenPath.tau X (d : ℤ) = (t : ℕ∞) := by
      apply RegenPath.tau_eq_iff.mpr
      refine ⟨⟨Classical.choice inferInstance, hreg.1.2 _⟩, ?_⟩
      intro n hn i
      exact ne_of_lt (hreg.1.1 n hn i)
    have hregRaw : RegenPath.Reg X (d : ℤ) := ⟨t, htau, hreg.1.2, hreg.2⟩
    have hD : RegenPath.D X = (d : ℕ∞) := (SwarmRawTimeStrict.D_eq_iff X d hd).mpr
      ⟨hregRaw, ?_⟩
    · exact ⟨hD, htau⟩
    · intro e he1 hed hregE
      obtain ⟨u, hregE'⟩ := BlockLevelKac.exists_isRegen_of_reg X hX0 hNN he1 hregE
      have hut : u < t := by
        by_contra hnot
        obtain ⟨i⟩ := (inferInstance : Nonempty (Fin N))
        rcases Nat.eq_or_lt_of_le (show t ≤ u by omega) with heq | hlt
        · subst u
          have h1 := hreg.1.2 i
          have h2 := hregE'.1.2 i
          omega
        · have h1 := hreg.2 u hlt i
          have h2 := hregE'.1.2 i
          omega
      obtain ⟨n, hun, hnt, i, hi⟩ := hno (e : ℤ) (by exact_mod_cast he1)
        (by exact_mod_cast hed) u hut hregE'.1
      have hgt := hregE'.2 n hun i
      omega
  · rintro ⟨hD, htau⟩
    have hspec := (SwarmRawTimeStrict.D_eq_iff X d hd).mp hD
    obtain ⟨u, hutau, hat, hstay⟩ := hspec.1
    have hut : u = t := by exact_mod_cast hutau.symm.trans htau
    subst u
    have ht := RegenPath.tau_eq_iff.mp htau
    have hrec : SwarmChain.pathRec t (d : ℤ) X := by
      refine ⟨?_, hat⟩
      intro s hs i
      by_contra hnot
      have hne := ht.2 s hs i
      have hgt : (d : ℤ) < X s i := by omega
      obtain ⟨n, hn, hhit⟩ := RegenPath.exists_lt_of_reaches
        (f := fun v => X v i) (hX0 i) (fun v => hNN v i) (s := s)
        (d := X s i) rfl (by exact_mod_cast (show 0 ≤ d by omega)) hgt
      exact ht.2 n (lt_trans hn hs) i hhit
    have hreg : SwarmSel.isRegen t (d : ℤ) X := ⟨hrec, hstay⟩
    refine ⟨hreg, ?_⟩
    intro e he1 hed u hu hrecU
    by_contra hnone
    push Not at hnone
    have hregU : SwarmSel.isRegen u e X := by
      refine ⟨hrecU, ?_⟩
      intro n hun i
      by_cases hnt : n ≤ t
      · exact hnone n hun hnt i
      · have hgt := hreg.2 n (by omega) i
        omega
    apply hspec.2 e.toNat (by omega) (by omega)
    have hecast : (e.toNat : ℤ) = e := by omega
    rw [hecast]
    exact BlockLevelKac.reg_of_isRegen hregU

/-- The concrete raw cell is the actual `D=d, tau_D=t` event. -/
theorem rawFirstCell_univ_iff_D_tau (p : ℝ) (m : ℕ) (q : LevelTime)
    (hN : 0 < N) (U : Array N) :
    U ∈ rawFirstCell p m q Set.univ ↔
      RegenPath.D (posPath p m U) = (q.1.1 : ℕ∞) ∧
        RegenPath.tau (posPath p m U) (q.1.1 : ℤ) = (q.1.2 : ℕ∞) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  rw [mem_rawFirstCell]
  simp only [Set.mem_univ, and_true]
  exact isRegen_noEarlyRegen_iff_D_tau (posPath p m U)
    (posPath_zero p m U) (posPath_step p m U) q.2

/-- The actual selector's level on a raw first-regeneration cell. -/
theorem firstLevel_eq_of_rawFirstCell (p : ℝ) (m : ℕ) (q : LevelTime)
    {U : Array N} (hN : 0 < N) (hU : U ∈ rawFirstCell p m q Set.univ) :
    firstLevel p m U = q.1.1 := by
  have hD := ((rawFirstCell_univ_iff_D_tau p m q hN U).mp hU).1
  exact (SwarmChainRegen.firstRegenLevel_eq_iff (posPath p m U) q.1.1 q.2).mpr (Or.inl hD)

/-- The actual selector's time on a raw first-regeneration cell. -/
theorem firstTime_eq_of_rawFirstCell (p : ℝ) (m : ℕ) (q : LevelTime)
    {U : Array N} (hN : 0 < N) (hU : U ∈ rawFirstCell p m q Set.univ) :
    firstTime p m U = q.1.2 := by
  have hD := ((rawFirstCell_univ_iff_D_tau p m q hN U).mp hU).1
  have htau := ((rawFirstCell_univ_iff_D_tau p m q hN U).mp hU).2
  have hlevel : firstLevel p m U = q.1.1 :=
    (SwarmChainRegen.firstRegenLevel_eq_iff (posPath p m U) q.1.1 q.2).mpr (Or.inl hD)
  simp [firstTime, firstTau, hlevel, htau]

/-- The selected integer future agrees with the concrete cell future. -/
theorem firstFutureZ_eq_of_rawFirstCell (p : ℝ) (m : ℕ) (q : LevelTime)
    {U : Array N} (hN : 0 < N) (hU : U ∈ rawFirstCell p m q Set.univ) :
    firstFutureZ p m U = relFuture p m U q.1.2 (q.1.1 : ℤ) := by
  simp [firstFutureZ, firstTime_eq_of_rawFirstCell p m q hN hU,
    firstLevel_eq_of_rawFirstCell p m q hN hU]

/-- Raw first cells with one common future condition are pairwise disjoint. -/
theorem pairwise_disjoint_rawFirstCell (p : ℝ) (m : ℕ)
    (B : Set (ℕ → Fin N → ℤ)) (hN : 0 < N) :
    Pairwise (Function.onFun Disjoint fun q : LevelTime => rawFirstCell (N := N) p m q B) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  intro q r hqr
  change Disjoint (rawFirstCell p m q B) (rawFirstCell p m r B)
  rw [Set.disjoint_left]
  intro U hq hr
  apply hqr
  have hq' := (mem_rawFirstCell p m q B U).mp hq
  have hr' := (mem_rawFirstCell p m r B U).mp hr
  have hQ := (isRegen_noEarlyRegen_iff_D_tau (posPath p m U)
    (posPath_zero p m U) (posPath_step p m U) q.2).mp ⟨hq'.1, hq'.2.1⟩
  have hR := (isRegen_noEarlyRegen_iff_D_tau (posPath p m U)
    (posPath_zero p m U) (posPath_step p m U) r.2).mp ⟨hr'.1, hr'.2.1⟩
  have hde : q.1.1 = r.1.1 := by
    have h : (q.1.1 : ℕ∞) = (r.1.1 : ℕ∞) := hQ.1.symm.trans hR.1
    exact_mod_cast h
  have hts : q.1.2 = r.1.2 := by
    have h : (q.1.2 : ℕ∞) = (r.1.2 : ℕ∞) := by
      rw [hde] at hQ
      exact hQ.2.symm.trans hR.2
    exact_mod_cast h
  exact Subtype.ext (Prod.ext hde hts)

/-- The completed raw cells exhaust exactly `D != top`; no mass-one assertion is
made here. -/
theorem iUnion_rawFirstCell_univ (p : ℝ) (m : ℕ) (hN : 0 < N) :
    (⋃ q : LevelTime, rawFirstCell (N := N) p m q Set.univ) =
      {U : Array N | RegenPath.D (posPath p m U) ≠ ⊤} := by
  ext U
  constructor
  · intro hU
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hU
    rw [rawFirstCell_univ_iff_D_tau p m q hN U] at hq
    change RegenPath.D (posPath p m U) ≠ ⊤
    rw [hq.1]
    simp
  · intro hU
    obtain ⟨d, t, hd, hD, htau⟩ :=
      (D_ne_top_iff_exists_firstBlock (posPath p m U)).mp hU
    apply Set.mem_iUnion.mpr
    refine ⟨ ⟨(d, t), hd⟩, ?_⟩
    exact (rawFirstCell_univ_iff_D_tau p m ⟨(d, t), hd⟩ hN U).mpr ⟨hD, htau⟩


/-- Exact countable mass sum on the raw completed cells. -/
theorem array_iUnion_rawFirstCell_mass (p : ℝ) (m : ℕ) (hN : 0 < N)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) (⋃ q : LevelTime, rawFirstCell p m q B) =
      ∑' q : LevelTime, (arrayMeasure N) (rawFirstCell p m q B) := by
  exact measure_iUnion (pairwise_disjoint_rawFirstCell p m B hN)
    (fun q => measurableSet_rawFirstCell p m q hB)

/-- The joint raw-cell/future mass is total raw completed mass times the
normalized strict law. -/
theorem array_iUnion_rawFirstCell_normalized_mass (p : ℝ) (m N : ℕ) (hN : 0 < N)
    (hV : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0)
    (hVtop : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ ⊤)
    {B : Set (ℕ → Fin N → ℤ)} (hB : MeasurableSet B) :
    (arrayMeasure N) (⋃ q : LevelTime, rawFirstCell p m q B) =
      (arrayMeasure N) (⋃ q : LevelTime, rawFirstCell p m q Set.univ) *
        normalizedStrictLaw p m N B := by
  rw [array_iUnion_rawFirstCell_mass p m hN hB,
    array_iUnion_rawFirstCell_mass p m hN MeasurableSet.univ]
  calc
    (∑' q : LevelTime, (arrayMeasure N) (rawFirstCell p m q B)) =
        ∑' q : LevelTime, (arrayMeasure N) (rawFirstCell p m q Set.univ) *
          normalizedStrictLaw p m N B := by
      apply tsum_congr
      intro q
      exact rawFirstCell_normalized_mass p m N q hV hVtop hB
    _ = _ := ENNReal.tsum_mul_right

/-- **Raw arbitrary-start completed-cell integer path law.**  The source measure
is restricted to the exact `D != top` union; no assertion is made about the
mass of its complement. -/
theorem restrict_rawCompleted_map_firstFutureZ (p : ℝ) (m N : ℕ) (hN : 0 < N)
    (hV : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0)
    (hVtop : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ ⊤) :
    ((arrayMeasure N).restrict
      (⋃ q : LevelTime, rawFirstCell p m q Set.univ)).map (firstFutureZ p m) =
      (arrayMeasure N) (⋃ q : LevelTime, rawFirstCell p m q Set.univ) •
        normalizedStrictLaw p m N := by
  ext B hB
  have hset : firstFutureZ (N := N) p m ⁻¹' B ∩
      (⋃ q : LevelTime, rawFirstCell p m q Set.univ) =
      ⋃ q : LevelTime, rawFirstCell p m q B := by
    ext U
    constructor
    · rintro ⟨hB', hU⟩
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hU
      have hq' := (mem_rawFirstCell p m q Set.univ U).mp hq
      have heq := firstFutureZ_eq_of_rawFirstCell p m q hN hq
      apply Set.mem_iUnion.mpr
      refine ⟨q, (mem_rawFirstCell p m q B U).mpr ⟨hq'.1, hq'.2.1, ?_⟩⟩
      change firstFutureZ p m U ∈ B at hB'
      rwa [heq] at hB'
    · intro hU
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hU
      have hq' := (mem_rawFirstCell p m q B U).mp hq
      have hu : U ∈ rawFirstCell p m q Set.univ :=
        (mem_rawFirstCell p m q Set.univ U).mpr ⟨hq'.1, hq'.2.1, Set.mem_univ _⟩
      refine ⟨?_, Set.mem_iUnion.mpr ⟨q, hu⟩⟩
      change firstFutureZ p m U ∈ B
      rw [firstFutureZ_eq_of_rawFirstCell p m q hN hu]
      exact hq'.2.2
  rw [Measure.map_apply (measurable_firstFutureZ p m) hB,
    Measure.restrict_apply ((measurable_firstFutureZ p m) hB), hset,
    Measure.smul_apply, smul_eq_mul,
    array_iUnion_rawFirstCell_normalized_mass p m N hN hV hVtop hB]

/-- Real-path form consumed by the literal neutral `hpath`, restricted to the
actual raw completed cells. -/
theorem restrict_rawCompleted_map_firstFutureR (p : ℝ) (m N : ℕ) (hN : 0 < N)
    (hV : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0)
    (hVtop : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ ⊤) :
    ((arrayMeasure N).restrict
      (⋃ q : LevelTime, rawFirstCell p m q Set.univ)).map (firstFutureR p m) =
      (arrayMeasure N) (⋃ q : LevelTime, rawFirstCell p m q Set.univ) •
        ((SwarmFB.seedCond (p := p) (m := m) (N := N)).map
          (M6Star.actPath (N := N) p m)) := by
  have hz := restrict_rawCompleted_map_firstFutureZ (N := N) p m hN hV hVtop
  have hreal := congrArg (fun μ : Measure (RegenPath.Path N) => μ.map (castPath (N := N))) hz
  rw [Measure.map_map measurable_castPath (measurable_firstFutureZ p m),
    Measure.map_smul, normalizedStrictLaw_eq_seedCond_map,
    Measure.map_map measurable_castPath (SwarmRestart.measurable_posPath p m N)] at hreal
  have hleft : (castPath (N := N) ∘ firstFutureZ p m) = firstFutureR p m := by
    rw [Function.comp_def, firstFutureR_eq_cast]
  have hright : (castPath (N := N) ∘ SwarmRestart.posPath p m) =
      M6Star.actPath (N := N) p m := by
    rw [Function.comp_def, actPath_eq_castPath_posPath]
  rwa [hleft, hright] at hreal


/-- Direct actual-model form: on `{D != top}`, the literal real translated path
has total-success-mass times the source's strict seed-conditioned path law.
This is unconditional as a restricted-measure theorem in the paper parameter
range; it is not an assertion that the success event has mass one. -/
theorem restrict_D_ne_top_map_firstFutureR {p : ℝ}
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    ((arrayMeasure N).restrict {U : Array N |
      RegenPath.D (posPath p m U) ≠ ⊤}).map (firstFutureR p m) =
      (arrayMeasure N) {U : Array N | RegenPath.D (posPath p m U) ≠ ⊤} •
        ((SwarmFB.seedCond (p := p) (m := m) (N := N)).map
          (M6Star.actPath (N := N) p m)) := by
  have hV : (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0 :=
    SwarmSeed.strictPos_measure_ne_zero hp0 hp1 hm hN
  rw [← iUnion_rawFirstCell_univ p m (by omega : 0 < N)]
  exact restrict_rawCompleted_map_firstFutureR (N := N) p m (by omega) hV
    (measure_ne_top _ _)

end RawInitialPathLaw
