/-The paper (`main_1d_revised.tex`, proof of Proposition `regen`) sets

  `A = {Y_0 ∈ F,  X_n^i > 0 for every i and every n ≥ 1}`,

where `Y_0` is the record state at the current level and `X` is the concatenated path of the
stationary sequence of record segments.  `Swarm/FreshCompose.lean`'s `record_ED_of_fresh`
consumes exactly the structural display

  `hstruct : μ (A ∩ Φ ⁻¹' B) = ∫⁻ y in F, P_y (V ∩ B) ∂π`,

and `FreshState.fresh_mass_strictPos` evaluates the right-hand side as `π(F) · P(V ∩ B)`.  What is
missing is the *model-side* identification on the chain side.  This file does four things.

* **§1. The enriched record step is almost surely level-additive.**  `asegK`'s atoms are
  `(segOf y k q, out k q y)` weighted by the model's own first-record weights `hitW`; on the
  first-record branch `segOfFirst_p_dur` computes the segment end, and off that branch `hitW = 0`.
  This is `Chain.compat` for one step, in the almost-sure form `Chain.compat` needs along the
  chain.  (`SEG_KERNEL.md` lists the a.e. compatibility as its residual (2).)

* **§2. `V` forces the first two steps of the actual model.**  From a simultaneous record
  (`y ∈ srSet`) the event `V` (= `strictPos`) forces every walker to be at `1` at time `1` and at
  `2` at time `2`.  This is a theorem about the actual array model; it is transferred from the
  canonical start with `FreshState.fresh_set_eq_srSet`.

* **§3. On the paper's `A`, the first two record segments are deterministic.**  `Chain.A` is
  proved to be *literally* the `strictPos` event of the concatenated path (`A = Φ ⁻¹' strictPos`),
  and then `A` forces `dur 0 = dur 1 = 1`, both segments to start at `0` in every coordinate,
  `X 1 ≡ 1` and `X 2 ≡ 2` — the exact chain-level counterpart of §2.

* **§4. `hstruct` is exactly one path-mass identity.**  Because `A = Φ ⁻¹' strictPos`, `hstruct`
  is *equivalent* to: for every measurable `B`, the mass under `μ` of "the concatenated path lies
  in `strictPos ∩ B`" is `π(F)` times the model's fresh mass of `strictPos ∩ B`.  Nothing else is
  in the premise, and — as noted in `DHSTRUCT.md` — the equivalence cannot be reduced to finite
  time horizons, because `A` itself contains the infinite-horizon event.

Everything here is unconditional in the model parameters (no invariant law, no tightness,
no stationarity hypothesis); the residual premises are listed in `DHSTRUCT.md`.
-/
import Swarm.SegKernel
import Swarm.FreshState
import Swarm.FreshCompose

open MeasureTheory Set
open Classical
open scoped ENNReal
open SimJump ProbabilityTheory
open Swarming.Uniform

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SwarmDHStruct

variable {N m : ℕ}

/-! ## 1. The enriched record step is almost surely level-additive -/

/-- The pairs `(segment, endpoint state)` whose segment ends exactly one level above the endpoint
state's own position array.  This is `SwarmConcat.Chain.compat` for one record step, read at the
segment's end (`k + p_k(dur_k) = (k+1) + p_{k+1}(0)`). -/
def CompatSet (N m : ℕ) : Set (SwarmConcat.Seg N × SwarmRec.RecState N m) :=
  {a | ∀ i, a.1.p a.1.dur i = 1 + (Record.ofRecState a.2).pos i}

theorem compatSet_eq (N m : ℕ) :
    CompatSet N m = ⋂ i : Fin N, ⋃ k : ℕ,
      ({a : SwarmConcat.Seg N × SwarmRec.RecState N m | a.1.dur = k} ∩
        {a | a.1.p k i = 1 + (Record.ofRecState a.2).pos i}) := by
  ext a
  simp only [CompatSet, Set.mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
  constructor
  · intro h i
    exact ⟨a.1.dur, rfl, h i⟩
  · rintro h i
    obtain ⟨k, hk, hp⟩ := h i
    rw [hk]
    exact hp

theorem measurable_ofRecState_pos (N m : ℕ) (i : Fin N) :
    Measurable fun y : SwarmRec.RecState N m => (Record.ofRecState y).pos i := by
  have hd : Measurable fun y : SwarmRec.RecState N m => ((y.val.1 i : ℕ) : ℤ) :=
    (measurable_of_countable (fun n : ℕ => ((n : ℤ)))).comp
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_subtype_coe))
  have heq : (fun y : SwarmRec.RecState N m => (Record.ofRecState y).pos i)
      = fun y => -((2:ℤ) * ((y.val.1 i : ℕ) : ℤ)) := by
    funext y
    rw [SwarmSegKernel.ofRecState_pos]
    try push_cast
    try ring
  rw [heq]
  simpa [mul_comm] using hd.const_mul (-2)

theorem measurableSet_compatSet (N m : ℕ) : MeasurableSet (CompatSet N m) := by
  rw [compatSet_eq]
  refine MeasurableSet.iInter fun i => MeasurableSet.iUnion fun k => ?_
  have h1 : Measurable fun a : SwarmConcat.Seg N × SwarmRec.RecState N m => a.1.p k i :=
    (SwarmConcat.measurable_seg_p (N := N) k i).comp measurable_fst
  have h2 : Measurable fun a : SwarmConcat.Seg N × SwarmRec.RecState N m =>
      1 + (Record.ofRecState a.2).pos i :=
    measurable_const.add ((measurable_ofRecState_pos N m i).comp measurable_snd)
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.preimage (measurableSet_singleton k)
      (SwarmConcat.measurable_seg_dur.comp measurable_fst)
  · exact measurableSet_eq_fun h1 h2

/-- A first-record path cannot have length zero: at time `0` every walker of a record state is at
or below the record level, so nobody sits at level `1`. -/
theorem firstRecord_ne_zero {y : SwarmRec.RecState N m} {k : ℕ} {q : Fin k → JumpVec N}
    (h : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exfalso
    subst hk
    obtain ⟨i, hi⟩ := h.1
    have hle := SwarmSegKernel.ofRecState_pos_nonpos y i
    have hpos : (Record.ofRecState y).pos i = 1 := hi
    omega
  · exact hk

/-- On the first-record branch `segOf` is the model's segment. -/
theorem segOf_of_firstRecord {y : SwarmRec.RecState N m} {k : ℕ} {q : Fin k → JumpVec N}
    (hk : 0 < k) (h : Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)) :
    SwarmSegKernel.segOf y k q = SwarmSegKernel.segOfFirst y k q hk h := by
  unfold SwarmSegKernel.segOf
  exact dif_pos ⟨hk, h⟩

/-- **The enriched record step is almost surely level-additive.**  Every atom of `asegK` that
carries mass ends the segment exactly one level above the endpoint record state. -/
theorem ae_compat_step (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (y : SwarmRec.RecState N m) :
    SwarmSegKernel.asegK (N := N) (m := m) p hm y (CompatSet N m) = 1 := by
  classical
  have hmeas := measurableSet_compatSet (N := N) (m := m)
  rw [SwarmSegKernel.asegK_apply (N := N) (m := m) p hm y hmeas]
  have hterm : ∀ pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (RecKernel.hitW p pq.2 y) *
        (if (SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) ∈ CompatSet N m
          then 1 else 0) = ENNReal.ofReal (RecKernel.hitW p pq.2 y) := by
    intro pq
    by_cases hfr : Record.FirstRecord (Record.extendPath pq.2) pq.1 (Record.ofRecState y)
    · have hk0 : 0 < pq.1 := firstRecord_ne_zero hfr
      have hmem : (SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) ∈ CompatSet N m := by
        intro i
        show (SwarmSegKernel.segOf y pq.1 pq.2).p (SwarmSegKernel.segOf y pq.1 pq.2).dur i
          = 1 + (Record.ofRecState (RecKernel.out hm pq.2 y)).pos i
        rw [segOf_of_firstRecord hk0 hfr]
        exact SwarmSegKernel.segOfFirst_p_dur y hm pq.2 hk0 hfr i
      rw [if_pos hmem, mul_one]
    · rw [RecKernel.hitW_of_not_firstRecord p pq.2 y hfr]
      simp
  simp_rw [hterm]
  have htsum : (∑' pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (RecKernel.hitW p pq.2 y)) = RecKernel.hitKInf p hm y Set.univ := by
    rw [RecKernel.hitKInf_apply (N := N) (m := m) p hm y
      (A := (Set.univ : Set (SwarmRec.RecState N m))) MeasurableSet.univ]
    simp
  rw [htsum, RecKernel.hitKInf_univ p hp hp1 hm y]

/-! ## 2. The fresh event `V` forces the first two steps of the actual model -/

/-- **`V` forces the first step.**  A path of the actual model that is strictly positive at every
positive time has every walker at `1` at time `1`. -/
theorem strictPos_one {p : ℝ} {m : ℕ} {U : Array N}
    (hX : SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)) (i : Fin N) :
    SwarmRestart.posPath p m U 1 i = 1 := by
  obtain ⟨h0, hpos⟩ := SwarmFresh.mem_strictPos.mp hX
  have hstep := SwarmFresh.posPath_step p m U 0 i
  have hz : SwarmRestart.posPath p m U 0 i = 0 := SwarmFresh.posPath_zero p m U i
  rw [show ((0:ℕ)+1) = 1 from rfl] at hstep
  rw [hz, sub_zero] at hstep
  have hgt : (0:ℤ) < SwarmRestart.posPath p m U 1 i := hpos 1 (by norm_num) i
  rcases (abs_eq (show (0:ℤ) ≤ 1 by norm_num)).mp hstep with h | h <;> omega

/-- **`V` forces the second step.** -/
theorem strictPos_two {p : ℝ} {m : ℕ} {U : Array N}
    (hX : SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)) (i : Fin N) :
    SwarmRestart.posPath p m U 2 i = 2 := by
  have h1 : SwarmRestart.posPath p m U 1 i = 1 := strictPos_one hX i
  have hpos := (SwarmFresh.mem_strictPos.mp hX).2 2 (by norm_num) i
  have hstep := SwarmFresh.posPath_step p m U 1 i
  rw [show ((1:ℕ)+1) = 2 from rfl] at hstep
  rw [h1] at hstep
  rcases (abs_eq (show (0:ℤ) ≤ 1 by norm_num)).mp hstep with h | h <;> omega

/-- **`V` forces the first step, for a trajectory started from an arbitrary simultaneous
record.**  This is the source-faithful form: the trajectory is the actual model's, started from
the record state `y ∈ F = srSet`. -/
theorem fromV_one {p : ℝ} {m : ℕ} (hm : 1 ≤ m) {y : SwarmRec.RecState N m}
    (hy : y ∈ SwarmRec.srSet N m) {U : Array N}
    (hV : SwarmFreshState.FromV p m U (SwarmFreshState.walkStateOf y)) (i : Fin N) :
    (SwarmRestart.trajFrom p m U (SwarmFreshState.walkStateOf y) 1).pos i = 1 := by
  by_contra hne
  have hb : U ∈ {U : Array N | SwarmFreshState.FromV p m U (SwarmFreshState.walkStateOf y) ∧
      (fun n i => (SwarmRestart.trajFrom p m U (SwarmFreshState.walkStateOf y) n).pos i)
        ∈ {X : ℕ → Fin N → ℤ | X 1 i ≠ 1}} := ⟨hV, hne⟩
  rw [SwarmFreshState.fresh_set_eq_srSet (N := N) hm p hy
    (B := {X : ℕ → Fin N → ℤ | X 1 i ≠ 1})] at hb
  exact hb.2 (strictPos_one hb.1 i)

/-- **`V` forces the second step, from an arbitrary simultaneous record.** -/
theorem fromV_two {p : ℝ} {m : ℕ} (hm : 1 ≤ m) {y : SwarmRec.RecState N m}
    (hy : y ∈ SwarmRec.srSet N m) {U : Array N}
    (hV : SwarmFreshState.FromV p m U (SwarmFreshState.walkStateOf y)) (i : Fin N) :
    (SwarmRestart.trajFrom p m U (SwarmFreshState.walkStateOf y) 2).pos i = 2 := by
  by_contra hne
  have hb : U ∈ {U : Array N | SwarmFreshState.FromV p m U (SwarmFreshState.walkStateOf y) ∧
      (fun n i => (SwarmRestart.trajFrom p m U (SwarmFreshState.walkStateOf y) n).pos i)
        ∈ {X : ℕ → Fin N → ℤ | X 2 i ≠ 2}} := ⟨hV, hne⟩
  rw [SwarmFreshState.fresh_set_eq_srSet (N := N) hm p hy
    (B := {X : ℕ → Fin N → ℤ | X 2 i ≠ 2})] at hb
  exact hb.2 (strictPos_two hb.1 i)

/-! ## 3. On the paper's `A` the first two record segments are deterministic -/

namespace ChainStep

variable (c : SwarmConcat.Chain N)

/-- **`Chain.A` is the `strictPos` event of the concatenated path.**  The paper's
`A = {Y_0 ∈ F, X_n^i > 0 for every i, n ≥ 1}` is exactly `Regen 0` in block form
(`RegenPath 0` in path form), and `strictPos` is `X_0 ≡ 0` together with positivity at positive
times. -/
theorem A_eq_strictPos :
    (SwarmConcat.Chain.A : Set (SwarmConcat.Chain N))
      = {c : SwarmConcat.Chain N |
          (fun n i => c.X n i) ∈ SwarmFresh.strictPos (N := N)} := by
  ext c
  rw [SwarmConcat.Chain.mem_A_iff, SwarmConcat.Chain.regen_iff (k := 0)]
  show c.RegenPath 0 ↔ (fun n i => c.X n i) ∈ SwarmFresh.strictPos
  rw [SwarmFresh.mem_strictPos]
  simp only [SwarmConcat.Chain.RegenPath, SwarmConcat.Chain.cum_zero, Nat.cast_zero]

/-- **`A` is exactly `Φ ⁻¹' strictPos`** for the concatenation map. -/
theorem A_eq_preimage :
    (SwarmConcat.Chain.A : Set (SwarmConcat.Chain N))
      = (fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹'
          SwarmFresh.strictPos (N := N) := by
  rw [A_eq_strictPos]
  rfl

/-- The concatenated path starts at the record level on `A`. -/
theorem regen_zero_start (hc : c ∈ SwarmConcat.Chain.A) (i : Fin N) :
    (c.seg 0).p 0 i = 0 := ((SwarmConcat.Chain.mem_A_iff c).mp hc).1 i

/-- The no-return clause of `Regen 0`, at level `j` and local time `m`. -/
theorem regen_zero_pos (hc : c ∈ SwarmConcat.Chain.A) {j : ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hmd : m ≤ (c.seg j).dur) (i : Fin N) :
    (0:ℤ) < (j : ℤ) + (c.seg j).p m i :=
  ((SwarmConcat.Chain.mem_A_iff c).mp hc).2 j (Nat.zero_le j) m hm hmd i

/-- **On `A` the first segment has duration one.**  A positive local time strictly before the end
of segment `0` would have to be both positive and `< 1`. -/
theorem A_dur_zero (hN : 0 < N) (hc : c ∈ SwarmConcat.Chain.A) :
    (c.seg 0).dur = 1 := by
  refine le_antisymm ?_ (c.seg 0).dur_pos
  by_contra hcon
  push Not at hcon
  have hp1 : (0:ℤ) < (c.seg 0).p 1 ⟨0, hN⟩ := by
    have h := regen_zero_pos c hc (j := 0) (m := 1) (by norm_num) (by omega) ⟨0, hN⟩
    simpa using h
  have hlt : (c.seg 0).p 1 ⟨0, hN⟩ < 1 := (c.seg 0).lt_one 1 hcon ⟨0, hN⟩
  omega

/-- On `A` the first segment ends with every walker exactly one level up. -/
theorem A_seg_zero_end (hN : 0 < N) (hc : c ∈ SwarmConcat.Chain.A) (i : Fin N) :
    (c.seg 0).p 1 i = 1 := by
  have hdur := A_dur_zero c hN hc
  have hstart := regen_zero_start c hc i
  have hstep : (c.seg 0).p 1 i = (c.seg 0).p 0 i + 1 ∨ (c.seg 0).p 1 i = (c.seg 0).p 0 i - 1 :=
    (c.seg 0).step 0 (by omega) i
  have hp1 : (0:ℤ) < (c.seg 0).p 1 i := by
    have h := regen_zero_pos c hc (j := 0) (m := 1) (by norm_num) (by omega) i
    simpa using h
  rw [hstart] at hstep
  rcases hstep with h | h <;> omega

/-- On `A` the first record is at time `1`. -/
theorem A_X_one (hN : 0 < N) (hc : c ∈ SwarmConcat.Chain.A) (i : Fin N) : c.X 1 i = 1 := by
  have hdur := A_dur_zero c hN hc
  have hc1 : c.cum 1 = 1 := by
    rw [SwarmConcat.Chain.cum_succ, SwarmConcat.Chain.cum_zero, hdur]
  have hX : c.X 1 i = (1:ℤ) + (c.seg 1).p 0 i := by
    have h := SwarmConcat.Chain.X_record c 1 i
    rwa [hc1] at h
  have hcpt := c.compat 0 i
  rw [hdur] at hcpt
  push_cast at hcpt
  rw [hX, ← hcpt]
  simpa using A_seg_zero_end c hN hc i

/-- On `A` the second segment also starts at the record level in every coordinate: the next
record state is again a simultaneous record. -/
theorem A_seg_one_start (hN : 0 < N) (hc : c ∈ SwarmConcat.Chain.A) (i : Fin N) :
    (c.seg 1).p 0 i = 0 := by
  have hcpt := c.compat 0 i
  rw [A_dur_zero c hN hc] at hcpt
  push_cast at hcpt
  have h := A_seg_zero_end c hN hc i
  omega

/-- **On `A` the second segment also has duration one.** -/
theorem A_dur_one (hN : 0 < N) (hc : c ∈ SwarmConcat.Chain.A) :
    (c.seg 1).dur = 1 := by
  refine le_antisymm ?_ (c.seg 1).dur_pos
  by_contra hcon
  push Not at hcon
  have hp1 : (0:ℤ) < (1:ℤ) + (c.seg 1).p 1 ⟨0, hN⟩ :=
    regen_zero_pos c hc (j := 1) (m := 1) (by norm_num) (by omega) ⟨0, hN⟩
  have hlt : (c.seg 1).p 1 ⟨0, hN⟩ < 1 := (c.seg 1).lt_one 1 hcon ⟨0, hN⟩
  have hstep : (c.seg 1).p 1 ⟨0, hN⟩ = (c.seg 1).p 0 ⟨0, hN⟩ + 1 ∨
      (c.seg 1).p 1 ⟨0, hN⟩ = (c.seg 1).p 0 ⟨0, hN⟩ - 1 :=
    (c.seg 1).step 0 (by omega) ⟨0, hN⟩
  have hstart := A_seg_one_start c hN hc ⟨0, hN⟩
  rw [hstart] at hstep
  rcases hstep with h | h <;> omega

/-- On `A` the second record is at time `2`. -/
theorem A_X_two (hN : 0 < N) (hc : c ∈ SwarmConcat.Chain.A) (i : Fin N) : c.X 2 i = 2 := by
  have hdur0 := A_dur_zero c hN hc
  have hdur1 := A_dur_one c hN hc
  have hc2 : c.cum 2 = 2 := by
    rw [SwarmConcat.Chain.cum_succ, SwarmConcat.Chain.cum_succ,
      SwarmConcat.Chain.cum_zero, hdur0, hdur1]
  have hX : c.X 2 i = (2:ℤ) + (c.seg 2).p 0 i := by
    have h := SwarmConcat.Chain.X_record c 2 i
    rwa [hc2] at h
  have hcpt := c.compat 1 i
  rw [hdur1] at hcpt
  push_cast at hcpt
  have hstart1 := A_seg_one_start c hN hc i
  have hend : (c.seg 1).p 1 i = 1 := by
    have hstep : (c.seg 1).p 1 i = (c.seg 1).p 0 i + 1 ∨ (c.seg 1).p 1 i = (c.seg 1).p 0 i - 1 :=
      (c.seg 1).step 0 (by omega) i
    have hp1 : (0:ℤ) < (1:ℤ) + (c.seg 1).p 1 i :=
      regen_zero_pos c hc (j := 1) (m := 1) (by norm_num) (by omega) i
    rw [hstart1] at hstep
    rcases hstep with h | h <;> omega
  have hseg2 : (c.seg 2).p 0 i = 0 := by omega
  rw [hX, hseg2]
  norm_num

end ChainStep

/-! ## 4. `hstruct` is exactly one path-mass identity -/

/-- **`hstruct` with the set `A = Φ ⁻¹' strictPos`, in the form `Φ ⁻¹' (strictPos ∩ B)`.**  The
left-hand side of the paper's structural display only sees the path through `Φ`; the two forms
below differ only by `Set.preimage_inter`. -/
theorem hstruct_iff_pathMass {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Φ : Ω → (ℕ → Fin N → ℤ)) (π : Measure (SwarmRec.RecState N m)) (p : ℝ) :
    (∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
        μ (Φ ⁻¹' SwarmFresh.strictPos (N := N) ∩ Φ ⁻¹' B)
          = π (SwarmRec.srSet N m) *
            (arrayMeasure N) {U : Array N |
              SwarmRestart.posPath p m U ∈
                SwarmFresh.strictPos (N := N) ∩ B})
      ↔ ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
          μ (Φ ⁻¹' (SwarmFresh.strictPos (N := N) ∩ B))
            = π (SwarmRec.srSet N m) *
              (arrayMeasure N) {U : Array N |
                SwarmRestart.posPath p m U ∈
                  SwarmFresh.strictPos (N := N) ∩ B} := by
  constructor
  · intro h B hB
    rw [Set.preimage_inter]
    exact h B hB
  · intro h B hB
    rw [← Set.preimage_inter]
    exact h B hB

/-- **The paper's `hstruct` for the segment chain is exactly the path-mass identity.**  With
`Φ` the concatenation `c ↦ (n ↦ i ↦ c.X n i)` and `A` the paper's regeneration event, the
right-hand side below is `π(F) · P(V ∩ B)` (`FreshState.fresh_mass_strictPos`), and the left-hand
side does not depend on the record states at all. -/
theorem chain_hstruct_iff (p : ℝ) (π : Measure (SwarmRec.RecState N m))
    (μ : Measure (SwarmConcat.Chain N)) :
    (∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
        μ (SwarmConcat.Chain.A ∩
            ((fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹' B))
          = π (SwarmRec.srSet N m) *
            (arrayMeasure N) {U : Array N |
              SwarmRestart.posPath p m U ∈
                SwarmFresh.strictPos (N := N) ∩ B})
      ↔ ∀ B : Set (ℕ → Fin N → ℤ), MeasurableSet B →
          μ ((fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹'
              (SwarmFresh.strictPos (N := N) ∩ B))
            = π (SwarmRec.srSet N m) *
              (arrayMeasure N) {U : Array N |
                SwarmRestart.posPath p m U ∈
                  SwarmFresh.strictPos (N := N) ∩ B} := by
  have hA : (SwarmConcat.Chain.A : Set (SwarmConcat.Chain N))
      = (fun c : SwarmConcat.Chain N => (fun n i => c.X n i)) ⁻¹'
          SwarmFresh.strictPos (N := N) := ChainStep.A_eq_preimage
  constructor
  · intro h B hB
    rw [Set.preimage_inter, ← hA]
    exact h B hB
  · intro h B hB
    rw [hA, ← Set.preimage_inter]
    exact h B hB

end SwarmDHStruct
