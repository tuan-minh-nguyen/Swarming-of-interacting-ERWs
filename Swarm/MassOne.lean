/-
# The record time is almost surely finite: the stopped record kernel has mass one

`Swarm/StoppedKernel.lean` builds the horizon-`L` stopped record kernel `hitK` and
proves its total mass is `hitMass p L y` — the probability that the next record occurs by time
`L` — and records the residual input of Prop. "front" as the almost-sure finiteness of the
record time, `hitMass p L y → 1`.

This file proves that limit.  The argument is elementary and does not need recurrence of the
simple symmetric walk:

* the walker sitting at `0` in the record state walks with right probability `≥ 1/2` in every
  state of the capped chain (`one_half_le_rightProbability`);
* this gives a **stochastic domination** of the walker's own increment pattern over the fair
  coin pattern, in the form of an inequality for every *decreasing* function of the pattern:
  `∑_q h (pattern q) * pathW q ≤ 2^{-L} ∑_π h π` (lemma `patMass_le_half_pow_sum`);
* the paths that avoid a record are contained in those where that walker's pattern never rises
  above `0`, and the reflected count of such fair patterns is `O(1/√L)`
  (`SwarmReflect.card_rmax_lt_le_sqrt`).

Consequently `1 - hitMass p L y ≤ 3√2/√(L+1) → 0`, i.e. the record time is almost surely
finite and the horizon limit of the stopped kernel is a probability kernel.
-/
import Swarm.StoppedKernel
import Swarm.Reflect.SqrtBound

open MeasureTheory ProbabilityTheory Filter Topology
open Classical
open scoped ENNReal BigOperators

namespace SimJump
namespace RecKernel

open SwarmRec

variable {N m : ℕ}

/-! ### 1. The marginal one-step law of a single walker -/

/-- **Marginal one-step law.**  For any function `f` of a single walker's jump, the total
one-step mass is the two-point law of that walker: the other walkers sum out. -/
theorem stepW_marginal_fun (p : ℝ) (m : ℕ) (s : State N m) (i : Fin N) (f : Bool → ℝ) :
    ∑ v : JumpVec N, f (v i) * stepW p m s v
      = f true * qRight p m s i + f false * (1 - qRight p m s i) := by
  classical
  set g : Fin N → Bool → ℝ :=
    fun k b => if k = i then f b * stepFactor p m s k b else stepFactor p m s k b with hg
  have hpt : ∀ v : JumpVec N, f (v i) * stepW p m s v = ∏ k, g k (v k) := by
    intro v
    rw [stepW_eq_prod]
    have hgprod : ∏ k, g k (v k)
        = (f (v i) * stepFactor p m s i (v i))
            * ∏ k ∈ Finset.univ.erase i, stepFactor p m s k (v k) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun k => g k (v k)) (Finset.mem_univ i)]
      congr 1
      · simp only [hg, if_pos rfl]
      · exact Finset.prod_congr rfl fun k hk => by
          simp only [hg, if_neg (Finset.ne_of_mem_erase hk)]
    rw [hgprod, ← Finset.mul_prod_erase Finset.univ
      (fun k => stepFactor p m s k (v k)) (Finset.mem_univ i)]
    ring
  rw [show (∑ v : JumpVec N, f (v i) * stepW p m s v) = ∑ v : JumpVec N, ∏ k, g k (v k) from
    Finset.sum_congr rfl fun v _ => hpt v]
  rw [sum_prod_bool g, Finset.prod_eq_single i]
  · simp only [hg, if_pos rfl, stepFactor]
    simp [qRight]
  · intro b _ hb
    have h1 : g b true + g b false = stepFactor p m s b false + stepFactor p m s b true := by
      simp only [hg, if_neg hb]
      ring
    rw [h1, stepFactor_false_add_true]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- A `{±1}`-valued finite pattern. -/
abbrev Pattern (L : ℕ) := Fin L → Bool

/-- The pattern of walker `i`'s jumps along the finite path `q`. -/
def pattern (i : Fin N) {L : ℕ} (q : Fin L → JumpVec N) : Pattern L := fun t => q t i

/-- Pointwise `false ≤ true` order on patterns. -/
def PatLe {L : ℕ} (π π' : Pattern L) : Prop := ∀ t, π t ≤ π' t

theorem patLe_refl {L : ℕ} (π : Pattern L) : PatLe π π := fun _ => le_rfl

/-- Extending a pattern on the right keeps the pointwise order. -/
theorem patLe_snoc {L : ℕ} {π π' : Pattern L} (h : PatLe π π') (b : Bool) :
    PatLe (Fin.snoc (α := fun _ => Bool) π b) (Fin.snoc (α := fun _ => Bool) π' b) := by
  intro t
  refine Fin.lastCases ?_ ?_ t
  · simp
  · intro j
    simpa using h j

/-- The pattern of an extended path is the extension of the pattern. -/
theorem pattern_snoc (i : Fin N) {L : ℕ} (q : Fin L → JumpVec N) (v : JumpVec N) :
    pattern i (Fin.snoc (α := fun _ : Fin (L+1) => JumpVec N) q v)
      = Fin.snoc (α := fun _ => Bool) (pattern i q) (v i) := by
  funext t
  refine Fin.lastCases ?_ ?_ t
  · simp [pattern]
  · intro j
    simp [pattern]

/-! ### 2. Stochastic domination of the fair-coin pattern measure -/

/-- `(1/2)^L * ∑_π h π`, the fair-coin average of `h`, written in the form used by the
recursion. -/
noncomputable def halfAvg {L : ℕ} (h : Pattern L → ℝ) : ℝ := (1 / 2 : ℝ) ^ L * ∑ π : Pattern L, h π

theorem halfAvg_succ {L : ℕ} (h : Pattern (L + 1) → ℝ) :
    halfAvg h = (1 / 2 : ℝ) ^ L *
      ∑ π : Pattern L, ((h (Fin.snoc (α := fun _ => Bool) π false)
        + h (Fin.snoc (α := fun _ => Bool) π true)) / 2) := by
  unfold halfAvg
  have hsum : ∑ π' : Pattern (L + 1), h π'
      = ∑ π : Pattern L, ∑ b : Bool, h (Fin.snoc (α := fun _ => Bool) π b) := by
    rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (L + 1) => Bool))
      (fun p : Bool × Pattern L => h (Fin.snoc (α := fun _ => Bool) p.2 p.1))
      (fun π' : Pattern (L + 1) => h π') (fun p => by
        obtain ⟨b, π⟩ := p
        rfl)]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hstep : ∀ π : Pattern L, (1 / 2 : ℝ) *
      (∑ b : Bool, h (Fin.snoc (α := fun _ => Bool) π b))
        = (h (Fin.snoc (α := fun _ => Bool) π false)
          + h (Fin.snoc (α := fun _ => Bool) π true)) / 2 := by
    intro π
    rw [Fintype.sum_bool]
    ring
  calc (1 / 2 : ℝ) ^ (L + 1) * ∑ π' : Pattern (L + 1), h π'
      = (1 / 2 : ℝ) ^ L * ((1 / 2 : ℝ) *
          ∑ π : Pattern L, ∑ b : Bool, h (Fin.snoc (α := fun _ => Bool) π b)) := by
        rw [hsum, pow_succ, mul_assoc]
    _ = (1 / 2 : ℝ) ^ L * ∑ π : Pattern L,
          ((h (Fin.snoc (α := fun _ => Bool) π false)
            + h (Fin.snoc (α := fun _ => Bool) π true)) / 2) := by
        rw [Finset.mul_sum]
        exact congrArg _ (Finset.sum_congr rfl fun π _ => hstep π)

/-- The right probability of a walker is at least `1/2` in every state. -/
theorem qRight_ge_half (p : ℝ) (m : ℕ) (s : State N m) (i : Fin N) (hp : 1 / 2 ≤ p) :
    1 / 2 ≤ qRight p m s i := by
  unfold qRight
  split
  · exact hp
  · norm_num

/-- The last-coordinate splitting equivalence of the jump sequences. -/
theorem snocPair {L : ℕ} (q : Fin L → JumpVec N) (v : JumpVec N) :
    ((Equiv.prodComm (Fin L → JumpVec N) (JumpVec N)).trans
      (Fin.snocEquiv (fun _ : Fin (L + 1) => JumpVec N))) (q, v)
      = Fin.snoc (α := fun _ : Fin (L + 1) => JumpVec N) q v := by
  funext x
  rw [Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv_apply]
  simp

/-- Pointwise order between the two extensions of a pattern by `false` and by `true`. -/
theorem patLe_snoc_snoc {L : ℕ} (π : Pattern L) :
    PatLe (Fin.snoc (α := fun _ => Bool) π false) (Fin.snoc (α := fun _ => Bool) π true) := by
  intro t
  refine Fin.lastCases ?_ ?_ t <;> simp

/-- **Stochastic domination of the fair coin by the interacting increment pattern.**

For every function `h` of a finite pattern that is *decreasing* for the pointwise order, the
weighted average of `h` under the length-`L` path measure of the capped chain, viewed through
walkers `i`'s own increments, is at most its fair-coin average `2^{-L} ∑_π h π`.

The hypothesis is exactly `one_half_le_rightProbability`: at every state walker `i` jumps right
with probability at least `1/2`. -/
theorem patMass_le_halfAvg (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (i : Fin N) :
    ∀ (L : ℕ) (h : Pattern L → ℝ),
      (∀ π π' : Pattern L, PatLe π π' → h π' ≤ h π) →
      ∀ s : State N m,
        ∑ q : Fin L → JumpVec N, h (pattern i q) * pathW p L q s ≤ halfAvg h
  | 0, h, _, s => by
      have hL : ∑ q : Fin 0 → JumpVec N, h (pattern i q) * pathW p 0 q s = h default := by
        rw [Finset.sum_eq_single (default : Fin 0 → JumpVec N)]
        · have hp' : pattern i (default : Fin 0 → JumpVec N) = (default : Pattern 0) :=
            funext fun t => t.elim0
          rw [hp']
          simp [pathW]
        · intro b _ hb
          exact absurd (funext fun t => t.elim0) hb
        · intro h'
          exact absurd (Finset.mem_univ _) h'
      have hR : halfAvg h = h default := by
        unfold halfAvg
        rw [Finset.sum_eq_single (default : Pattern 0)]
        · simp
        · intro b _ hb
          exact absurd (funext fun t => t.elim0) hb
        · intro h'
          exact absurd (Finset.mem_univ _) h'
      rw [hL, hR]
  | (L + 1), h, hmono, s => by
      set e : ((Fin L → JumpVec N) × JumpVec N) ≃ (Fin (L + 1) → JumpVec N) :=
        (Equiv.prodComm (Fin L → JumpVec N) (JumpVec N)).trans
          (Fin.snocEquiv (fun _ : Fin (L + 1) => JumpVec N)) with he
      have he_apply : ∀ (q : Fin L → JumpVec N) (v : JumpVec N),
          e (q, v) = Fin.snoc (α := fun _ : Fin (L + 1) => JumpVec N) q v := by
        intro q v
        rw [he]
        exact snocPair q v
      have hsplit : ∑ q : Fin (L + 1) → JumpVec N, h (pattern i q) * pathW p (L + 1) q s
          = ∑ q' : Fin L → JumpVec N, ∑ v : JumpVec N,
              h (Fin.snoc (α := fun _ => Bool) (pattern i q') (v i))
                * (pathW p L q' s * stepW p m (evolve L q' s) v) := by
        rw [← Fintype.sum_equiv e
          (fun qv : (Fin L → JumpVec N) × JumpVec N =>
            h (pattern i (e qv)) * pathW p (L + 1) (e qv) s)
          (fun q : Fin (L + 1) → JumpVec N => h (pattern i q) * pathW p (L + 1) q s)
          (fun qv => rfl)]
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun v _ => by
          rw [he_apply, pattern_snoc]
          simp only [pathW, Fin.snoc_castSucc, Fin.snoc_last]
      have hstep : ∀ q' : Fin L → JumpVec N,
          ∑ v : JumpVec N, h (Fin.snoc (α := fun _ => Bool) (pattern i q') (v i))
              * (pathW p L q' s * stepW p m (evolve L q' s) v)
            ≤ pathW p L q' s *
              ((h (Fin.snoc (α := fun _ => Bool) (pattern i q') false)
                + h (Fin.snoc (α := fun _ => Bool) (pattern i q') true)) / 2) := by
        intro q'
        have hfac : ∑ v : JumpVec N, h (Fin.snoc (α := fun _ => Bool) (pattern i q') (v i))
              * (pathW p L q' s * stepW p m (evolve L q' s) v)
            = pathW p L q' s * ∑ v : JumpVec N,
                h (Fin.snoc (α := fun _ => Bool) (pattern i q') (v i))
                  * stepW p m (evolve L q' s) v := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
        rw [hfac]
        have hmarg := stepW_marginal_fun p m (evolve L q' s) i
          (fun b => h (Fin.snoc (α := fun _ => Bool) (pattern i q') b))
        have hmarg' : ∑ v : JumpVec N, h (Fin.snoc (α := fun _ => Bool) (pattern i q') (v i))
              * stepW p m (evolve L q' s) v
            = h (Fin.snoc (α := fun _ => Bool) (pattern i q') true)
                * qRight p m (evolve L q' s) i
              + h (Fin.snoc (α := fun _ => Bool) (pattern i q') false)
                * (1 - qRight p m (evolve L q' s) i) := by
          rw [← hmarg]
        rw [hmarg']
        have hQ : 1 / 2 ≤ qRight p m (evolve L q' s) i := qRight_ge_half p m _ i hp
        have hle : h (Fin.snoc (α := fun _ => Bool) (pattern i q') true)
            ≤ h (Fin.snoc (α := fun _ => Bool) (pattern i q') false) :=
          hmono _ _ (patLe_snoc_snoc (pattern i q'))
        have hw : 0 ≤ pathW p L q' s := pathW_nonneg p hp hp1 L q' s
        have hkey : h (Fin.snoc (α := fun _ => Bool) (pattern i q') true)
              * qRight p m (evolve L q' s) i
            + h (Fin.snoc (α := fun _ => Bool) (pattern i q') false)
              * (1 - qRight p m (evolve L q' s) i)
            ≤ (h (Fin.snoc (α := fun _ => Bool) (pattern i q') false)
              + h (Fin.snoc (α := fun _ => Bool) (pattern i q') true)) / 2 := by
          nlinarith [hQ, hle]
        exact mul_le_mul_of_nonneg_left hkey hw
      have hmonoG : ∀ π π' : Pattern L, PatLe π π' →
          ((h (Fin.snoc (α := fun _ => Bool) π' false)
            + h (Fin.snoc (α := fun _ => Bool) π' true)) / 2)
          ≤ ((h (Fin.snoc (α := fun _ => Bool) π false)
            + h (Fin.snoc (α := fun _ => Bool) π true)) / 2) := by
        intro π π' hle
        have h1 : h (Fin.snoc (α := fun _ => Bool) π' false)
            ≤ h (Fin.snoc (α := fun _ => Bool) π false) := hmono _ _ (patLe_snoc hle false)
        have h2 : h (Fin.snoc (α := fun _ => Bool) π' true)
            ≤ h (Fin.snoc (α := fun _ => Bool) π true) := hmono _ _ (patLe_snoc hle true)
        linarith
      calc ∑ q : Fin (L + 1) → JumpVec N, h (pattern i q) * pathW p (L + 1) q s
          = ∑ q' : Fin L → JumpVec N, ∑ v : JumpVec N,
              h (Fin.snoc (α := fun _ => Bool) (pattern i q') (v i))
                * (pathW p L q' s * stepW p m (evolve L q' s) v) := hsplit
        _ ≤ ∑ q' : Fin L → JumpVec N, pathW p L q' s *
              ((h (Fin.snoc (α := fun _ => Bool) (pattern i q') false)
                + h (Fin.snoc (α := fun _ => Bool) (pattern i q') true)) / 2) :=
              Finset.sum_le_sum fun q' _ => hstep q'
        _ = ∑ q' : Fin L → JumpVec N,
              ((h (Fin.snoc (α := fun _ => Bool) (pattern i q') false)
                + h (Fin.snoc (α := fun _ => Bool) (pattern i q') true)) / 2)
                * pathW p L q' s :=
              Finset.sum_congr rfl fun q' _ => by ring
        _ ≤ halfAvg (fun π => ((h (Fin.snoc (α := fun _ => Bool) π false)
                + h (Fin.snoc (α := fun _ => Bool) π true)) / 2)) :=
              patMass_le_halfAvg p hp hp1 i L _ hmonoG s
        _ = halfAvg h := (halfAvg_succ h).symm

/-! ### 3. The first-record decomposition of the stopped mass -/

/-- `stateAt` depends only on the first `n` jumps of the path. -/
theorem stateAt_congr {L L' : ℕ} {q : Fin L → JumpVec N} {q' : Fin L' → JumpVec N}
    (h : ∀ (t : ℕ) (ht : t < L) (ht' : t < L'), q ⟨t, ht⟩ = q' ⟨t, ht'⟩)
    (n : ℕ) (hn : n ≤ L) (hn' : n ≤ L') (s : State N m) :
    stateAt q n hn s = stateAt q' n hn' s := by
  unfold stateAt
  congr 1
  funext i
  exact h i.1 (lt_of_lt_of_le i.2 hn) (lt_of_lt_of_le i.2 hn')

/-- The state after `0` jumps is the starting state. -/
theorem stateAt_zero {L : ℕ} (q : Fin L → JumpVec N) (h : 0 ≤ L) (s : State N m) :
    stateAt q 0 h s = s := rfl

/-- The state after `n+1` jumps is the state after `n` jumps followed by the `n`-th jump. -/
theorem stateAt_succ {L : ℕ} (q : Fin L → JumpVec N) {n : ℕ} (hn : n + 1 ≤ L)
    (s : State N m) :
    stateAt q (n + 1) hn s
      = step m (stateAt q n (le_trans (Nat.le_succ n) hn) s) (q ⟨n, hn⟩) := rfl

/-- Some walker sits at the record level `1` after the first `n` jumps. -/
def RecAt {L : ℕ} (q : Fin L → JumpVec N) (n : ℕ) (hn : n ≤ L) (s : State N m) : Prop :=
  ∃ i, (stateAt q n hn s).pos i = 1

/-- Every walker is at `≤ 0` at every time `≤ J` along the path. -/
def NoRecUp {L : ℕ} (q : Fin L → JumpVec N) (J : ℕ) (hJ : J ≤ L) (s : State N m) : Prop :=
  ∀ (t : ℕ) (ht : t ≤ J) (i : Fin N), (stateAt q t (le_trans ht hJ) s).pos i ≤ 0

theorem noRecUp_of_le {L : ℕ} {q : Fin L → JumpVec N} {J J' : ℕ} (hJJ : J ≤ J')
    (hJ' : J' ≤ L) (h : NoRecUp q J' hJ' s) : NoRecUp q J (le_trans hJJ hJ') s :=
  fun t ht i => h t (le_trans ht hJJ) i

theorem noRecUp_succ {L : ℕ} {q : Fin L → JumpVec N} {J : ℕ} (hJ : J + 1 ≤ L)
    (s : State N m) :
    NoRecUp q (J + 1) hJ s ↔
      NoRecUp q J (le_trans (Nat.le_succ J) hJ) s ∧
        ∀ i, (stateAt q (J + 1) hJ s).pos i ≤ 0 := by
  constructor
  · intro h
    exact ⟨noRecUp_of_le (Nat.le_succ J) hJ h, fun i => h (J + 1) le_rfl i⟩
  · intro h t ht i
    rcases Nat.lt_or_ge t (J + 1) with hlt | hge
    · exact h.1 t (Nat.lt_succ_iff.mp hlt) i
    · have : t = J + 1 := by omega
      subst this
      exact h.2 i

/-- One step from a configuration with every walker at `≤ 0` cannot exceed `1`. -/
theorem pos_step_le_one {s : State N m} (v : JumpVec N) (i : Fin N) (h : s.pos i ≤ 0) :
    (step m s v).pos i ≤ 1 := by
  rw [step_pos, stepPos]
  split_ifs <;> omega

/-- **`FirstRecord` in terms of the state sequence.**  For a starting state with all walkers at
`≤ 0`, the first record at time `J+1` means: no walker was positive before, and some walker now
sits at `1`. -/
theorem firstRecord_iff_noRecUp {L : ℕ} {q : Fin L → JumpVec N} {J : ℕ} (hJ : J + 1 ≤ L)
    {s : State N m} :
    Record.FirstRecord (Record.extendPath q) (J + 1) s ↔
      NoRecUp q J (le_trans (Nat.le_succ J) hJ) s ∧ RecAt q (J + 1) hJ s := by
  unfold Record.FirstRecord
  constructor
  · rintro ⟨⟨i, hi⟩, hprev⟩
    refine ⟨fun t ht j => ?_, ⟨i, ?_⟩⟩
    · exact (Record.evolveFun_extendPath_le q s t
        (le_trans ht (le_trans (Nat.le_succ J) hJ))) ▸ hprev t (by omega) j
    · rw [← Record.evolveFun_extendPath_le q s (J + 1) hJ]
      exact hi
  · rintro ⟨hno, ⟨i, hi⟩⟩
    refine ⟨⟨i, ?_⟩, fun t ht j => ?_⟩
    · rw [Record.evolveFun_extendPath_le q s (J + 1) hJ]
      exact hi
    · exact (Record.evolveFun_extendPath_le q s t (le_trans (by omega) hJ)) ▸ hno t (by omega) j

/-- The key pointwise identity: a first record at `J+1` occurs exactly when nothing was recorded
before and something sits at `1` now. -/
theorem indicator_firstRecord {L : ℕ} {q : Fin L → JumpVec N} {J : ℕ} (hJ : J + 1 ≤ L)
    {s : State N m} (hs : ∀ i, s.pos i ≤ 0) :
    (if Record.FirstRecord (Record.extendPath q) (J + 1) s then (1 : ℝ) else 0)
        + (if NoRecUp q (J + 1) hJ s then (1 : ℝ) else 0)
      = (if NoRecUp q J (le_trans (Nat.le_succ J) hJ) s then (1 : ℝ) else 0) := by
  classical
  have hrec := firstRecord_iff_noRecUp (m := m) (q := q) hJ (s := s)
  have hsucc := noRecUp_succ (q := q) hJ s
  by_cases h1 : NoRecUp q J (le_trans (Nat.le_succ J) hJ) s
  · have hlt : ∀ i, (stateAt q J (le_trans (Nat.le_succ J) hJ) s).pos i ≤ 0 :=
      fun i => h1 J le_rfl i
    have hone : ∀ i, (stateAt q (J + 1) hJ s).pos i ≤ 1 := by
      intro i
      rw [stateAt_succ (q := q) hJ s]
      exact pos_step_le_one _ i (hlt i)
    have hkey : RecAt q (J + 1) hJ s ↔ ¬ NoRecUp q (J + 1) hJ s := by
      constructor
      · rintro ⟨i, hi⟩ hcon
        have := hcon (J + 1) le_rfl i
        omega
      · intro hcon
        have hnot : ¬ (∀ i, (stateAt q (J + 1) hJ s).pos i ≤ 0) := by
          intro h
          exact hcon (by rw [hsucc]; exact ⟨h1, h⟩)
        push Not at hnot
        obtain ⟨i, hi⟩ := hnot
        exact ⟨i, by have := hone i; omega⟩
    have hfr : Record.FirstRecord (Record.extendPath q) (J + 1) s
        ↔ ¬ NoRecUp q (J + 1) hJ s := by
      rw [hrec]
      exact ⟨fun h => hkey.mp h.2, fun h => ⟨h1, hkey.mpr h⟩⟩
    rw [if_pos h1]
    by_cases h2 : NoRecUp q (J + 1) hJ s
    · rw [if_neg (fun h => (hfr.mp h) h2), if_pos h2]
      norm_num
    · rw [if_pos (hfr.mpr h2), if_neg h2]
      norm_num
  · have h2 : ¬ NoRecUp q (J + 1) hJ s := fun h => h1 (noRecUp_of_le (Nat.le_succ J) hJ h)
    have hfr : ¬ Record.FirstRecord (Record.extendPath q) (J + 1) s := by
      rw [hrec]
      rintro ⟨h, -⟩
      exact h1 h
    rw [if_neg h1, if_neg h2, if_neg hfr]
    norm_num

/-! ### 4. The mass decomposition `hitMass + avoidMass = 1` -/

/-- The mass of the paths of length `L` that have not recorded by time `L`. -/
noncomputable def avoidMass (p : ℝ) (L : ℕ) (y : RecState N m) : ℝ :=
  ∑ q : Fin L → JumpVec N,
    (if NoRecUp q L le_rfl (Record.ofRecState y) then (1 : ℝ) else 0)
      * pathW p L q (Record.ofRecState y)

/-- The extended jump sequence agrees with the prefix on all indices below its length. -/
theorem snoc_apply_lt {L : ℕ} (q' : Fin L → JumpVec N) (v : JumpVec N)
    (t : ℕ) (ht : t < L + 1) (ht' : t < L) :
    Fin.snoc (α := fun _ : Fin (L + 1) => JumpVec N) q' v ⟨t, ht⟩ = q' ⟨t, ht'⟩ := by
  have h : (⟨t, ht⟩ : Fin (L + 1)) = (⟨t, ht'⟩ : Fin L).castSucc := Fin.eq_of_val_eq rfl
  rw [h, Fin.snoc_castSucc]

/-- Splitting the length-`L+1` sum at the last jump recovers the length-`L` sum. -/
theorem avoidMass_shift (p : ℝ) (L : ℕ) (y : RecState N m) :
    ∑ q : Fin (L + 1) → JumpVec N,
        (if NoRecUp q L (Nat.le_succ L) (Record.ofRecState y) then (1 : ℝ) else 0)
          * pathW p (L + 1) q (Record.ofRecState y)
      = avoidMass p L y := by
  classical
  set e : ((Fin L → JumpVec N) × JumpVec N) ≃ (Fin (L + 1) → JumpVec N) :=
    (Equiv.prodComm (Fin L → JumpVec N) (JumpVec N)).trans
      (Fin.snocEquiv (fun _ : Fin (L + 1) => JumpVec N)) with he
  have he_apply : ∀ (q : Fin L → JumpVec N) (v : JumpVec N),
      e (q, v) = Fin.snoc (α := fun _ : Fin (L + 1) => JumpVec N) q v := by
    intro q v
    rw [he]
    exact snocPair q v
  rw [← Fintype.sum_equiv e
    (fun qv : (Fin L → JumpVec N) × JumpVec N =>
      (if NoRecUp (e qv) L (Nat.le_succ L) (Record.ofRecState y) then (1 : ℝ) else 0)
        * pathW p (L + 1) (e qv) (Record.ofRecState y))
    (fun q : Fin (L + 1) → JumpVec N =>
      (if NoRecUp q L (Nat.le_succ L) (Record.ofRecState y) then (1 : ℝ) else 0)
        * pathW p (L + 1) q (Record.ofRecState y))
    (fun qv => rfl)]
  rw [Fintype.sum_prod_type, avoidMass]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have hiff : ∀ v : JumpVec N,
      NoRecUp (e (q', v)) L (Nat.le_succ L) (Record.ofRecState y)
        ↔ NoRecUp q' L le_rfl (Record.ofRecState y) := by
    intro v
    have hst : ∀ (t : ℕ) (ht : t ≤ L),
        stateAt (e (q', v)) t (le_trans ht (Nat.le_succ L)) (Record.ofRecState y)
          = stateAt q' t ht (Record.ofRecState y) := by
      intro t ht
      exact stateAt_congr (fun m hm hm' => by rw [he_apply]; exact snoc_apply_lt q' v m hm hm')
        t _ _ _
    constructor
    · intro h t ht i
      exact (hst t ht) ▸ h t ht i
    · intro h t ht i
      rw [hst t ht]
      exact h t ht i
  have hstep : ∀ v : JumpVec N,
      (if NoRecUp (e (q', v)) L (Nat.le_succ L) (Record.ofRecState y) then (1 : ℝ) else 0)
        * pathW p (L + 1) (e (q', v)) (Record.ofRecState y)
      = (if NoRecUp q' L le_rfl (Record.ofRecState y) then (1 : ℝ) else 0)
        * (pathW p L q' (Record.ofRecState y)
            * stepW p m (evolve L q' (Record.ofRecState y)) v) := by
    intro v
    have hif : (if NoRecUp (e (q', v)) L (Nat.le_succ L) (Record.ofRecState y)
          then (1 : ℝ) else 0)
        = (if NoRecUp q' L le_rfl (Record.ofRecState y) then (1 : ℝ) else 0) := by
      by_cases h : NoRecUp q' L le_rfl (Record.ofRecState y)
      · rw [if_pos ((hiff v).mpr h), if_pos h]
      · rw [if_neg (fun hc => h ((hiff v).mp hc)), if_neg h]
    rw [hif, he_apply]
    simp only [pathW, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.sum_congr rfl fun v _ => hstep v]
  rw [← Finset.mul_sum, ← Finset.mul_sum, stepW_sum_one]
  ring

/-- The `L+1` term of `hitMass` is the mass of the paths whose first record is at time `L+1`. -/
theorem hitMass_succ (p : ℝ) (L : ℕ) (y : RecState N m) :
    hitMass p (L + 1) y = hitMass p L y
      + ∑ q : Fin (L + 1) → JumpVec N,
          (if Record.FirstRecord (Record.extendPath q) (L + 1) (Record.ofRecState y)
            then (1 : ℝ) else 0) * pathW p (L + 1) q (Record.ofRecState y) := by
  classical
  rw [hitMass, Finset.sum_range_succ, hitMass]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hitW]
  split_ifs with h <;> simp

/-- **The stopped record mass plus the no-record mass is one.** -/
theorem hitMass_add_avoidMass (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) :
    ∀ (L : ℕ) (y : RecState N m), hitMass p L y + avoidMass p L y = 1 := by
  intro L
  induction L with
  | zero =>
    intro y
    have hs0 : ∀ i, (Record.ofRecState y).pos i ≤ 0 :=
      (Record.ofRecState_recordStart y hm).nonpos
    have hhit : hitMass p 0 y = 0 := by
      rw [hitMass, Finset.sum_range_one]
      have hzero : ∀ q : Fin 0 → JumpVec N, hitW p q y = 0 := by
        intro q
        rw [hitW_of_not_firstRecord p q y]
        intro hcon
        obtain ⟨i, hi⟩ := hcon.1
        have h0 : (evolveFun (Record.extendPath q) 0 (Record.ofRecState y)).pos i
            = (Record.ofRecState y).pos i := rfl
        rw [h0] at hi
        have := hs0 i
        omega
      simp only [hzero, Finset.sum_const_zero]
    have htrue : NoRecUp (default : Fin 0 → JumpVec N) 0 le_rfl (Record.ofRecState y) := by
      intro t ht i
      have ht0 : t = 0 := by omega
      subst ht0
      rw [stateAt_zero]
      exact hs0 i
    have havoid : avoidMass p 0 y = 1 := by
      rw [avoidMass, Finset.sum_eq_single (default : Fin 0 → JumpVec N)]
      · rw [if_pos htrue]
        simp [pathW]
      · intro b _ hb
        exact absurd (funext fun t => t.elim0) hb
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    rw [hhit, havoid]
    norm_num
  | succ L ih =>
    intro y
    have hcombine :
        ∑ q : Fin (L + 1) → JumpVec N,
            (if Record.FirstRecord (Record.extendPath q) (L + 1) (Record.ofRecState y)
              then (1 : ℝ) else 0) * pathW p (L + 1) q (Record.ofRecState y)
          + ∑ q : Fin (L + 1) → JumpVec N,
            (if NoRecUp q (L + 1) le_rfl (Record.ofRecState y) then (1 : ℝ) else 0)
              * pathW p (L + 1) q (Record.ofRecState y)
        = ∑ q : Fin (L + 1) → JumpVec N,
            (if NoRecUp q L (Nat.le_succ L) (Record.ofRecState y) then (1 : ℝ) else 0)
              * pathW p (L + 1) q (Record.ofRecState y) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← add_mul]
      congr 1
      exact indicator_firstRecord (le_rfl : L + 1 ≤ L + 1)
        (Record.ofRecState_recordStart y hm).nonpos
    rw [hitMass_succ, add_assoc,
      show avoidMass p (L + 1) y
        = ∑ q : Fin (L + 1) → JumpVec N,
            (if NoRecUp q (L + 1) le_rfl (Record.ofRecState y) then (1 : ℝ) else 0)
              * pathW p (L + 1) q (Record.ofRecState y) from rfl,
      hcombine, avoidMass_shift p L y, ← ih y]

/-! ### 5. The walker's own pattern never rises above `0` on a no-record path -/

/-- The position of walker `i` after `t` jumps is its starting position plus the partial sum of
its own jump pattern. -/
theorem pos_stateAt_eq {L : ℕ} (q : Fin L → JumpVec N) (s : State N m) (i : Fin N)
    {t : ℕ} (ht : t ≤ L) :
    (stateAt q t ht s).pos i = s.pos i + SwarmReflect.psum (pattern i q) t := by
  induction t with
  | zero => simp [stateAt_zero, SwarmReflect.psum]
  | succ t ih =>
      have ht' : t ≤ L := le_trans (Nat.le_succ t) ht
      have hlt : t < L := lt_of_lt_of_le (Nat.lt_succ_self t) ht
      rw [stateAt_succ (q := q) ht s, step_pos, stepPos, ih ht', SwarmReflect.psum_succ_of_lt
        (pattern i q) hlt]
      simp only [pattern]
      split_ifs with hv <;> simp [SwarmReflect.step, hv] <;> ring

/-- No-record state-level paths keep the chosen walker's own pattern below `1`. -/
theorem rmax_pattern_le_zero {L : ℕ} {q : Fin L → JumpVec N} {s : State N m}
    {i₀ : Fin N} (hpos0 : s.pos i₀ = 0) (hno : NoRecUp q L le_rfl s) :
    SwarmReflect.rmax (pattern i₀ q) L < 1 := by
  have hkey : ∀ t ≤ L, SwarmReflect.psum (pattern i₀ q) t ≤ 0 := by
    intro t ht
    have h := hno t ht i₀
    rw [pos_stateAt_eq q s i₀ ht, hpos0, zero_add] at h
    exact h
  have hrmax : ∀ t ≤ L, SwarmReflect.rmax (pattern i₀ q) t ≤ 0 := by
    intro t
    induction t with
    | zero => intro _; simpa [SwarmReflect.rmax] using hkey 0 (Nat.zero_le L)
    | succ t ih =>
        intro ht
        rw [SwarmReflect.rmax_succ]
        exact max_le (ih (by omega)) (hkey (t + 1) (by omega))
  have := hrmax L le_rfl
  omega

/-- Partial sums are monotone in the pattern. -/
theorem psum_mono_pat {L : ℕ} {π π' : Pattern L} (h : PatLe π π') (t : ℕ) :
    SwarmReflect.psum π t ≤ SwarmReflect.psum π' t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [SwarmReflect.psum_succ, SwarmReflect.psum_succ]
      rcases Nat.lt_or_ge t L with hlt | hge
      · rw [dif_pos hlt, dif_pos hlt]
        have hstep : SwarmReflect.step (π ⟨t, hlt⟩) ≤ SwarmReflect.step (π' ⟨t, hlt⟩) := by
          have hb := h ⟨t, hlt⟩
          cases h1 : π ⟨t, hlt⟩
          · cases h2 : π' ⟨t, hlt⟩ <;> simp [SwarmReflect.step, h1, h2]
          · have h2 : π' ⟨t, hlt⟩ = true := by
              rw [h1] at hb
              cases h3 : π' ⟨t, hlt⟩
              · rw [h3] at hb
                exact absurd hb (by decide)
              · rfl
            simp [SwarmReflect.step, h1, h2]
        linarith
      · rw [dif_neg (by omega), dif_neg (by omega)]
        simpa using ih

/-- The running maximum is monotone in the pattern. -/
theorem rmax_mono_pat {L : ℕ} {π π' : Pattern L} (h : PatLe π π') : ∀ t,
    SwarmReflect.rmax π t ≤ SwarmReflect.rmax π' t := by
  intro t
  induction t with
  | zero => simp [SwarmReflect.rmax]
  | succ t ih =>
      rw [SwarmReflect.rmax_succ, SwarmReflect.rmax_succ]
      exact max_le_max ih (psum_mono_pat h (t + 1))

/-- **The no-record mass is bounded by the fair running-maximum count.** -/
theorem avoidMass_le_count (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (L : ℕ) (y : RecState N m)
    {i₀ : Fin N} (hpos0 : (Record.ofRecState y).pos i₀ = 0) :
    avoidMass p L y ≤ (1 / 2 : ℝ) ^ L *
      ((Finset.univ.filter (fun π : Pattern L => SwarmReflect.rmax π L < 1)).card : ℝ) := by
  classical
  set s0 := Record.ofRecState y with hs0
  set D : Pattern L → Prop := fun π => SwarmReflect.rmax π L < 1 with hD
  have hmono : ∀ π π' : Pattern L, PatLe π π' → (if D π' then (1 : ℝ) else 0)
      ≤ (if D π then (1 : ℝ) else 0) := by
    intro π π' hle
    by_cases h : D π
    · rw [if_pos h]
      split_ifs <;> norm_num
    · have h' : ¬ D π' := by
        intro hc
        exact h (lt_of_le_of_lt (rmax_mono_pat hle L) hc)
      rw [if_neg h, if_neg h']
  have hdom := patMass_le_halfAvg p hp hp1 i₀ L (fun π => if D π then (1 : ℝ) else 0) hmono s0
  have hpt : ∀ q : Fin L → JumpVec N,
      (if NoRecUp q L le_rfl s0 then (1 : ℝ) else 0) * pathW p L q s0
        ≤ (if D (pattern i₀ q) then (1 : ℝ) else 0) * pathW p L q s0 := by
    intro q
    by_cases h : NoRecUp q L le_rfl s0
    · rw [if_pos h, if_pos (rmax_pattern_le_zero hpos0 h)]
    · rw [if_neg h]
      have hnn : (0 : ℝ) ≤ (if D (pattern i₀ q) then (1 : ℝ) else 0) := by
        by_cases hd : D (pattern i₀ q) <;> simp [hd]
      exact mul_le_mul_of_nonneg_right hnn (pathW_nonneg p hp hp1 L q s0)
  have hcard : ∑ π : Pattern L, (if D π then (1 : ℝ) else 0)
      = ((Finset.univ.filter D).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [avoidMass]
  refine le_trans (Finset.sum_le_sum fun q _ => hpt q) (le_trans hdom ?_)
  unfold halfAvg
  rw [hcard]

/-! ### 6. The record time is almost surely finite -/

/-- **Quantitative convergence**: the probability that no record occurs by time `L` is at most
`3√2/√(L+1)`. -/
theorem one_sub_hitMass_le (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (L : ℕ) (y : RecState N m) :
    1 - hitMass p L y ≤ 3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1) := by
  classical
  obtain ⟨i₀, hi₀⟩ := (Record.ofRecState_recordStart y hm).exists_zero
  have hdec : 1 - hitMass p L y = avoidMass p L y := by
    have h := hitMass_add_avoidMass p hp hp1 hm L y
    linarith
  rw [hdec]
  refine le_trans (avoidMass_le_count p hp hp1 L y hi₀) ?_
  have hcard := SwarmReflect.card_rmax_lt_le_sqrt (n := L) (b := 1) (by norm_num)
  have hnonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ L := by positivity
  have hcard' : ((Finset.univ.filter (fun π : Pattern L =>
      SwarmReflect.rmax π L < 1)).card : ℝ)
      ≤ (2 * 1 + 1) * Real.sqrt 2 * 2 ^ L / Real.sqrt ((L : ℝ) + 1) := by
    simpa using hcard
  refine le_trans (mul_le_mul_of_nonneg_left hcard' hnonneg) ?_
  have h2 : ((1 : ℝ) / 2) ^ L * 2 ^ L = 1 := by
    rw [← mul_pow]
    norm_num
  have heq : (1 / 2 : ℝ) ^ L * ((2 * 1 + 1) * Real.sqrt 2 * 2 ^ L / Real.sqrt ((L : ℝ) + 1))
      = (3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1)) * (((1 : ℝ) / 2) ^ L * 2 ^ L) := by
    ring
  rw [heq, h2, mul_one]

/-- **The record time is almost surely finite** (the residual input recorded in
`Swarm/StoppedKernel.lean`): the total mass of the horizon-`L` stopped record
kernel tends to `1`. -/
theorem tendsto_hitMass (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (y : RecState N m) :
    Tendsto (fun L : ℕ => hitMass p L y) atTop (𝓝 1) := by
  classical
  have hle_one : ∀ L : ℕ, hitMass p L y ≤ 1 := by
    intro L
    have h := hitMass_add_avoidMass p hp hp1 hm L y
    have hnn : 0 ≤ avoidMass p L y := by
      rw [avoidMass]
      exact Finset.sum_nonneg fun q _ =>
        mul_nonneg (by split_ifs <;> norm_num) (pathW_nonneg p hp hp1 L q _)
    linarith
  have hsq : Tendsto (fun L : ℕ => Real.sqrt ((L : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun L : ℕ => (Real.sqrt ((L : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    hsq.inv_tendsto_atTop
  have hbound : Tendsto (fun L : ℕ => 3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 3 * Real.sqrt 2) (f := (atTop : Filter ℕ))).mul hinv
    simpa [div_eq_mul_inv] using h
  have hzero : Tendsto (fun L : ℕ => 1 - hitMass p L y) atTop (𝓝 0) :=
    squeeze_zero (fun L => by have := hle_one L; linarith)
      (fun L => one_sub_hitMass_le p hp hp1 hm L y) hbound
  have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).sub hzero
  simpa using h

/-- The no-record mass is nonnegative. -/
theorem avoidMass_nonneg (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (L : ℕ) (y : RecState N m) :
    0 ≤ avoidMass p L y := by
  rw [avoidMass]
  exact Finset.sum_nonneg fun q _ =>
    mul_nonneg (by split_ifs <;> norm_num) (pathW_nonneg p hp hp1 L q _)

/-- The stopped record mass never exceeds one. -/
theorem hitMass_le_one (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (L : ℕ)
    (y : RecState N m) : hitMass p L y ≤ 1 := by
  have h := hitMass_add_avoidMass p hp hp1 hm L y
  have hnn := avoidMass_nonneg p hp hp1 L y
  linarith

/-- The stopped record mass is monotone in the horizon. -/
theorem hitMass_mono (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {L L' : ℕ} (hLL : L ≤ L')
    (y : RecState N m) : hitMass p L y ≤ hitMass p L' y := by
  classical
  rw [hitMass, hitMass]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega)) ?_
  intro k _ _
  exact Finset.sum_nonneg fun q _ => hitW_nonneg p hp hp1 q y

/-- **The rate is uniform in the record state**: eventually every starting state has recorded
with probability at least `1 - ε`. -/
theorem eventually_one_sub_hitMass_le (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop, ∀ y : RecState N m, 1 - hitMass p L y ≤ ε := by
  have hsq : Tendsto (fun L : ℕ => Real.sqrt ((L : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun L : ℕ => (Real.sqrt ((L : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    hsq.inv_tendsto_atTop
  have hbound : Tendsto (fun L : ℕ => 3 * Real.sqrt 2 / Real.sqrt ((L : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 3 * Real.sqrt 2) (f := (atTop : Filter ℕ))).mul hinv
    simpa [div_eq_mul_inv] using h
  filter_upwards [hbound.eventually_lt_const hε] with L hL
  intro y
  exact le_trans (one_sub_hitMass_le p hp hp1 hm L y) hL.le

/-- The record-at-`k` mass, i.e. the `k`-th term of the horizon sum. -/
noncomputable def recTerm (p : ℝ) (k : ℕ) (y : RecState N m) : ℝ :=
  ∑ q : Fin k → JumpVec N, hitW p q y

theorem recTerm_eq (p : ℝ) (k : ℕ) (y : RecState N m) :
    recTerm p k y = ∑ q : Fin k → JumpVec N,
      (if Record.FirstRecord (Record.extendPath q) k (Record.ofRecState y)
        then (1 : ℝ) else 0) * pathW p k q (Record.ofRecState y) := by
  classical
  rw [recTerm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hitW]
  split_ifs <;> simp

theorem hitMass_eq_sum_range (p : ℝ) (L : ℕ) (y : RecState N m) :
    hitMass p L y = ∑ k ∈ Finset.range (L + 1), recTerm p k y := rfl

theorem recTerm_nonneg (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (k : ℕ) (y : RecState N m) :
    0 ≤ recTerm p k y :=
  Finset.sum_nonneg fun q _ => hitW_nonneg p hp hp1 q y

/-- **The record time is a genuine `ℕ`-valued random variable**: the masses of the disjoint
events "the first record occurs at time `k`" form a probability mass function on `ℕ`. -/
theorem hasSum_recTerm (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m)
    (y : RecState N m) : HasSum (fun k => recTerm p k y) 1 := by
  have hnn : ∀ k, 0 ≤ recTerm p k y := fun k => recTerm_nonneg p hp hp1 k y
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hshift : Tendsto (fun L : ℕ => ∑ k ∈ Finset.range (L + 1), recTerm p k y) atTop (𝓝 1) := by
    simpa [hitMass_eq_sum_range] using tendsto_hitMass p hp hp1 hm y
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  simpa using hshift

end RecKernel
end SimJump
