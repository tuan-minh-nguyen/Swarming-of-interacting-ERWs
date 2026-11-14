/-
# the two-step a.e. compatibility and the chain parity

Companion of `DHStruct.lean`.

* `tsum_hitW`: the model's first-record weights sum to one (the `hitKInf` mass, read as a plain
  `tsum`); `ae_compat_step` is re-derived from it.
* `ae_start_step`: `asegK y`-almost every segment *starts* at the current record state's own
  position array (true for **every** atom, first-record branch and junk branch alike).
* `compat_step_ae`: **two consecutive enriched record steps are almost surely compatible**, in
  exactly the form `SwarmConcat.Chain.compat` needs at `k = 0`.  This is the finite-horizon part
  of `SEG_KERNEL.md`'s residual (2).
* `X_parity`, `A_X_parity`: the paper's "`X_n^i ≡ n (mod 2)`", now for the *concatenated* path of
  an abstract segment chain (with an even start array, which every atom of `asegK` has).
* `strictLaw_two_steps`: **`P^*(X_1 ≡ 1, X_2 ≡ 2) = 1`** for the paper's fresh law, i.e. the model
  statement of `DHStruct` §2 in the normalised form `FreshCompose` uses.
-/
import Swarm.DHStruct

open MeasureTheory Set
open Classical
open scoped ENNReal
open SimJump ProbabilityTheory
open Swarming.Uniform

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SwarmDHStruct

variable {N m : ℕ}

/-! ## 1. The weights sum to one, and the start of the step -/

/-- **The model's first-record weights sum to one.** -/
theorem tsum_hitW (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (y : SwarmRec.RecState N m) :
    (∑' pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (RecKernel.hitW p pq.2 y)) = 1 := by
  have h := RecKernel.hitKInf_apply (N := N) (m := m) p hm y
    (A := (Set.univ : Set (SwarmRec.RecState N m))) MeasurableSet.univ
  simp only [mem_univ, if_true, mul_one] at h
  exact h.symm.trans (RecKernel.hitKInf_univ p hp hp1 hm y)

/-- The set on which the segment starts at a fixed position array. -/
def StartSet (N m : ℕ) (y : SwarmRec.RecState N m) :
    Set (SwarmConcat.Seg N × SwarmRec.RecState N m) :=
  {a | ∀ i, a.1.p 0 i = (Record.ofRecState y).pos i}

theorem measurableSet_startSet (N m : ℕ) (y : SwarmRec.RecState N m) :
    MeasurableSet (StartSet N m y) := by
  rw [show StartSet N m y = ⋂ (i : Fin N),
      {a : SwarmConcat.Seg N × SwarmRec.RecState N m |
        a.1.p 0 i = (Record.ofRecState y).pos i} from by ext a; simp [StartSet]]
  refine MeasurableSet.iInter (fun (i : Fin N) => ?_)
  exact measurableSet_eq_fun ((SwarmConcat.measurable_seg_p (N := N) 0 i).comp measurable_fst)
    measurable_const

/-- **Every step of `asegK` starts at the current record state's position array** — almost surely,
and in fact on every atom: `segOf_p_zero` holds for the first-record branch and for the junk
branch `dummySeg` alike. -/
theorem ae_start_step (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (y : SwarmRec.RecState N m) :
    SwarmSegKernel.asegK (N := N) (m := m) p hm y (StartSet N m y) = 1 := by
  classical
  have hmeas := measurableSet_startSet (N := N) (m := m) y
  rw [SwarmSegKernel.asegK_apply (N := N) (m := m) p hm y hmeas]
  have hterm : ∀ pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (RecKernel.hitW p pq.2 y) *
        (if (SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) ∈ StartSet N m y
          then 1 else 0) = ENNReal.ofReal (RecKernel.hitW p pq.2 y) := by
    intro pq
    have hm : (SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) ∈ StartSet N m y := by
      intro i
      exact SwarmSegKernel.segOf_p_zero y pq.1 pq.2 i
    rw [if_pos hm, mul_one]
  have hsum : (∑' pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (RecKernel.hitW p pq.2 y) *
        (if (SwarmSegKernel.segOf y pq.1 pq.2, RecKernel.out hm pq.2 y) ∈ StartSet N m y
          then 1 else 0)) = ∑' pq : (k : ℕ) × (Fin k → JumpVec N),
      ENNReal.ofReal (RecKernel.hitW p pq.2 y) := by
    apply tsum_congr
    exact hterm
  rw [hsum]
  exact tsum_hitW p hm hp hp1 y

/-! ## 2. Two-step compatibility, almost surely -/

/-- A set of full measure is an almost-everywhere event. -/
theorem ae_of_measure_eq_one {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hmeas : MeasurableSet s) (hs : μ s = 1) (hμ : μ Set.univ = 1) : ∀ᵐ a ∂μ, a ∈ s := by
  letI : IsFiniteMeasure μ := ⟨by rw [hμ]; norm_num⟩
  rw [MeasureTheory.ae_iff]
  have hcompl : {a | a ∉ s} = sᶜ := rfl
  rw [hcompl, measure_compl hmeas (measure_ne_top μ s), hs, hμ]
  simp

/-- **Two consecutive enriched record steps are almost surely level-compatible.**  For
`asegK`-almost every first step `a` and `asegK a.2`-almost every second step `b`,

  `0 + p_{a}(dur_a) = 1 + p_{b}(0)`,

which is `SwarmConcat.Chain.compat` at `k = 0` for the record chain driven by `asegK`. -/
theorem compat_step_ae (p : ℝ) (hm : 1 ≤ m) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (y : SwarmRec.RecState N m) :
    ∀ᵐ a ∂(SwarmSegKernel.asegK (N := N) (m := m) p hm y),
      ∀ᵐ b ∂(SwarmSegKernel.asegK (N := N) (m := m) p hm a.2),
        ∀ i, (0:ℤ) + a.1.p a.1.dur i = (1:ℤ) + b.1.p 0 i := by
  have huniv : ∀ z : SwarmRec.RecState N m,
      SwarmSegKernel.asegK (N := N) (m := m) p hm z Set.univ = 1 :=
    fun z => SwarmSegKernel.asegK_univ p hm hp hp1 z
  have hae := ae_of_measure_eq_one
    (μ := SwarmSegKernel.asegK (N := N) (m := m) p hm y)
    (measurableSet_compatSet (N := N) (m := m))
    (ae_compat_step p hm hp hp1 y) (huniv y)
  refine Filter.Eventually.mono hae ?_
  intro a ha
  refine Filter.Eventually.mono
    (ae_of_measure_eq_one (μ := SwarmSegKernel.asegK (N := N) (m := m) p hm a.2)
      (measurableSet_startSet (N := N) (m := m) a.2) (ae_start_step p hm hp hp1 a.2)
      (huniv a.2)) ?_
  intro b hb i
  have h1 : a.1.p a.1.dur i = 1 + (Record.ofRecState a.2).pos i := ha i
  have h2 : b.1.p 0 i = (Record.ofRecState a.2).pos i := hb i
  omega

/-! ## 3. The parity of the concatenated path -/

namespace ChainStep

variable (c : SwarmConcat.Chain N)

/-- **`X_n^i ≡ n (mod 2)`** for the concatenated path of a segment chain whose level-`0` start
positions are even (which holds for every atom of `asegK`: `segOf_p_zero` gives `-2 d_i`). -/
theorem X_parity (h0 : ∀ i, Even ((c.seg 0).p 0 i)) (n : ℕ) (i : Fin N) :
    Even (c.X n i + (n : ℤ)) := by
  induction n with
  | zero =>
      have h := SwarmConcat.Chain.X_record c 0 i
      rw [SwarmConcat.Chain.cum_zero] at h
      simp only [Nat.cast_zero, zero_add] at h
      rw [h]
      simpa using h0 i
  | succ n ih =>
      rcases SwarmConcat.Chain.X_step c n i with h | h
      · rw [h]
        obtain ⟨a, ha⟩ := ih
        exact ⟨a + 1, by push_cast at ha ⊢; omega⟩
      · rw [h]
        obtain ⟨a, ha⟩ := ih
        exact ⟨a, by push_cast at ha ⊢; omega⟩

/-- **Parity on the regeneration event**: on `A` the concatenated path has the parity of the time
index, the paper's "`X_n^i ≡ n (mod 2)`". -/
theorem A_X_parity (hc : c ∈ SwarmConcat.Chain.A) (n : ℕ) (i : Fin N) :
    Even (c.X n i + (n : ℤ)) := by
  refine X_parity c (fun i => ?_) n i
  rw [regen_zero_start c hc i]
  exact ⟨0, rfl⟩

end ChainStep

/-! ## 4. The fresh law is supported on the two forced steps -/

/-- **`P^*(X_1 ≡ 1, X_2 ≡ 2) = 1`.**  The paper's fresh law `P^* = P(· | V)` is concentrated on the
event that every walker jumps right at times `1` and `2`; equivalently `P(V ∩ {X_1 ≡ 1, X_2 ≡ 2})
= P(V)`.  This is the model-level statement behind `DHStruct` §2 in the normalised form that
`FreshCompose.strictLaw` uses. -/
theorem strictLaw_two_steps (p : ℝ) (m N : ℕ) :
    SwarmFreshCompose.strictLaw p m N
        {X : ℕ → Fin N → ℤ | ∀ i, X 1 i = 1 ∧ X 2 i = 2}
      = SwarmFreshCompose.strictLaw p m N Set.univ := by
  have hB : MeasurableSet {X : ℕ → Fin N → ℤ | ∀ i, X 1 i = 1 ∧ X 2 i = 2} := by
    rw [show {X : ℕ → Fin N → ℤ | ∀ i, X 1 i = 1 ∧ X 2 i = 2} =
      ⋂ i : Fin N, ({X : ℕ → Fin N → ℤ | X 1 i = 1} ∩
        {X : ℕ → Fin N → ℤ | X 2 i = 2}) from by ext X; simp]
    refine MeasurableSet.iInter (fun (i : Fin N) => MeasurableSet.inter ?_ ?_)
    · exact measurableSet_eq_fun
        ((measurable_pi_apply i).comp (measurable_pi_apply (1 : ℕ))) measurable_const
    · exact measurableSet_eq_fun
        ((measurable_pi_apply i).comp (measurable_pi_apply (2 : ℕ))) measurable_const
  rw [SwarmFreshCompose.strictLaw_apply p m N hB, SwarmFreshCompose.strictLaw_univ]
  have heq : {U : Array N | SwarmRestart.posPath p m U ∈
      SwarmFresh.strictPos (N := N) ∩
        {X : ℕ → Fin N → ℤ | ∀ i, X 1 i = 1 ∧ X 2 i = 2}} =
      {U : Array N | SwarmRestart.posPath p m U ∈ SwarmFresh.strictPos (N := N)} := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hV, _⟩
      exact hV
    · intro hV
      exact ⟨hV, fun i => ⟨strictPos_one hV i, strictPos_two hV i⟩⟩
  rw [heq]

end SwarmDHStruct
