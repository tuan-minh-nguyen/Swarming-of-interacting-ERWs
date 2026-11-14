/-
Finite-horizon path algebra for the simultaneous-jump chain of
`main_1d_revised.tex`, §3.1 (the record chain).

Main results of this file:

* `sum_pathW_one`  : paths of length `k` carry total mass `1`;
* `pathW_ge`       : the mass of one prescribed jump sequence is at least `(1-p)^(N k)`;
* `hitFMass_ge`    : starting from any state whose walkers are at most `K` below the
  record, the probability that the next record state is a simultaneous record
  (`d_i = 0` for all `i`, i.e. the paper's set `F`) is at least `(1-p)^(N(K+1))`.
  This is eq. (force) of Prop. (front), stated as a finite-horizon identity.

No measure theory, no stopping times: `hitFMass` is a finite sum over jump vectors.
-/
import Swarm.SimJumpCore

namespace SimJump

open Finset

variable {N m : ℕ}

/-! ### Paths of length `k` -/

/-- The state reached from `s` by following the path `q`. -/
noncomputable def evolve : ∀ k, (Fin k → JumpVec N) → State N m → State N m
  | 0, _, s => s
  | (k+1), q, s => step m (evolve k (fun i => q i.castSucc) s) (q (Fin.last k))

/-- The weight of the path `q` started from `s`: the product of the one-step joint laws. -/
noncomputable def pathW (p : ℝ) : ∀ k, (Fin k → JumpVec N) → State N m → ℝ
  | 0, _, _ => 1
  | (k+1), q, s =>
      pathW p k (fun i => q i.castSucc) s
        * stepW p m (evolve k (fun i => q i.castSucc) s) (q (Fin.last k))

theorem pathW_nonneg (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    ∀ k (q : Fin k → JumpVec N) (s : State N m), 0 ≤ pathW p k q s
  | 0, _, _ => by simp [pathW]
  | (k+1), q, s => by
      have h := pathW_nonneg p hp hp1 k (fun i => q i.castSucc) s
      have h2 := stepW_nonneg p m (evolve k (fun i => q i.castSucc) s) (q (Fin.last k)) hp hp1
      simpa [pathW] using mul_nonneg h h2

/-- **Total mass one**: the weights of the paths of length `k` form a probability law. -/
theorem sum_pathW_one (p : ℝ) :
    ∀ k (s : State N m), ∑ q : Fin k → JumpVec N, pathW (m := m) p k q s = 1
  | 0, s => by simp [pathW]
  | (k+1), s => by
      rw [← Fintype.sum_equiv
        ((Equiv.prodComm (Fin k → JumpVec N) (JumpVec N)).trans
          (Fin.snocEquiv (fun _ : Fin (k+1) => JumpVec N)))
        (fun qv : (Fin k → JumpVec N) × JumpVec N =>
          pathW (m := m) p k qv.1 s * stepW p m (evolve k qv.1 s) qv.2)
        (fun q => pathW (m := m) p (k+1) q s) (fun qv => by
          obtain ⟨q, v⟩ := qv
          simp only [Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv_apply, pathW,
            Fin.snoc_castSucc, Fin.snoc_last, Prod.fst_swap, Prod.snd_swap])]
      rw [Fintype.sum_prod_type]
      have hstep : ∀ q : Fin k → JumpVec N,
          ∑ v : JumpVec N, pathW (m := m) p k q s * stepW p m (evolve k q s) v
            = pathW (m := m) p k q s := by
        intro q
        rw [← Finset.mul_sum, stepW_sum_one, mul_one]
      rw [Finset.sum_congr rfl (fun q _ => hstep q)]
      exact sum_pathW_one p k s

/-! ### Paths given as jump sequences `ℕ → JumpVec N` -/

/-- The state reached from `s` after `k` jumps of the sequence `u`. -/
noncomputable def evolveFun (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) : State N m :=
  evolve k (fun i : Fin k => u i) s

/-- The weight of the first `k` jumps of the sequence `u`. -/
noncomputable def pathWFun (p : ℝ) (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) : ℝ :=
  pathW p k (fun i : Fin k => u i) s

lemma evolve_eq_evolveFun (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) :
    evolve k (fun i : Fin k => u i) s = evolveFun (m := m) u k s := rfl

lemma pathW_eq_pathWFun (p : ℝ) (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) :
    pathW p k (fun i : Fin k => u i) s = pathWFun p u k s := rfl

lemma evolveFun_succ (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) :
    evolveFun (m := m) u (k+1) s = step m (evolveFun (m := m) u k s) (u k) := rfl

lemma pathWFun_succ (p : ℝ) (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) :
    pathWFun p u (k+1) s
      = pathWFun p u k s * stepW p m (evolveFun (m := m) u k s) (u k) := rfl

theorem pathWFun_nonneg (p : ℝ) (u : ℕ → JumpVec N) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    ∀ k (s : State N m), 0 ≤ pathWFun p u k s
  | 0, s => by simp [pathWFun, pathW]
  | (k+1), s => by
      rw [pathWFun_succ]
      exact mul_nonneg (pathWFun_nonneg p u hp hp1 k s)
        (stepW_nonneg p m _ (u k) hp hp1)

/-- **Prescribed-path lower bound**: any fixed jump sequence of length `k` has mass at
least `(1-p)^(N k)`. -/
theorem pathWFun_ge (p : ℝ) (u : ℕ → JumpVec N) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    ∀ k (s : State N m), (1 - p) ^ (N * k) ≤ pathWFun p u k s
  | 0, s => by simp [pathWFun, pathW]
  | (k+1), s => by
      have hnn : (0 : ℝ) ≤ (1 - p) ^ (N * k) := by
        apply pow_nonneg; linarith
      have h1 := pathWFun_ge p u hp hp1 k s
      have h2 := stepW_ge p m (evolveFun (m := m) u k s) (u k) hp hp1
      have h3 := pathWFun_nonneg (m := m) p u hp hp1 k s
      have h4 : (0 : ℝ) ≤ (1 - p) ^ N := by apply pow_nonneg; linarith
      rw [pathWFun_succ, Nat.mul_succ, pow_add]
      exact mul_le_mul h1 h2 h4 h3

/-! ### The prescribed path of Prop. (front) -/

/-- The starting configuration of the record chain: walker `i` sits `d i` below the
record and the local times are `η`. -/
def startState (d : Fin N → ℕ) (η : Fin N → ℤ → ℕ) (hη : ∀ i x, η i x ≤ m) : State N m where
  pos i := -(d i : ℤ)
  eta := η
  hcap := hη

/-- The prescribed jump of walker `i` at time `n`: first `(K - d i)/2` steps left, then
right.  (This is the paper's "descend and then come back up" prescription, written with the
left steps first; it keeps walker `i` at or below `0` up to time `K` and puts it at `1` at
time `K+1`, and every prescribed jump has conditional probability at least `1-p`.) -/
def forcedJump (K : ℕ) (d : Fin N → ℕ) (n : ℕ) (i : Fin N) : Bool :=
  if n < (K - d i) / 2 then false else true

/-- Sum of `n` terms which are `-1` while the index is below `D` and `1` afterwards. -/
lemma sum_ite_lt (D n : ℕ) :
    ∑ k ∈ range n, (if k < D then (-1 : ℤ) else 1)
      = if n ≤ D then -(n : ℤ) else (n : ℤ) - 2 * (D : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases hlt : n < D
      · rw [if_pos (le_of_lt hlt)] at ih
        rw [if_pos hlt, ih, if_pos (show n + 1 ≤ D by omega)]
        push_cast
        ring
      · rw [if_neg hlt]
        by_cases heq : n = D
        · subst heq
          rw [if_pos (le_refl n)] at ih
          rw [ih, if_neg (by omega : ¬ n + 1 ≤ n)]
          push_cast
          ring
        · have hgt : D < n := by omega
          rw [if_neg (by omega : ¬ n ≤ D)] at ih
          rw [ih, if_neg (by omega : ¬ n + 1 ≤ D)]
          push_cast
          ring

/-- The position of walker `i` after `n` steps of the prescribed path. -/
lemma pos_evolveFun (u : ℕ → JumpVec N) (s : State N m) (i : Fin N) :
    ∀ n, (evolveFun (m := m) u n s).pos i
      = s.pos i + ∑ k ∈ range n, (if u k i = true then (1 : ℤ) else -1)
  | 0 => by simp [evolveFun, evolve]
  | (n+1) => by
      rw [evolveFun_succ, step_pos, stepPos, pos_evolveFun u s i n, Finset.sum_range_succ]
      ring

lemma pos_forced (K : ℕ) (d : Fin N → ℕ) (η : Fin N → ℤ → ℕ) (hη : ∀ i x, η i x ≤ m)
    (i : Fin N) (n : ℕ) :
    (evolveFun (m := m) (forcedJump K d) n (startState d η hη)).pos i
      = -(d i : ℤ)
        + (if n ≤ (K - d i) / 2 then -(n : ℤ) else (n : ℤ) - 2 * (((K - d i) / 2 : ℕ) : ℤ)) := by
  rw [pos_evolveFun]
  have hsum : ∀ k ∈ range n, (if forcedJump K d k i = true then (1 : ℤ) else -1)
      = (if k < (K - d i) / 2 then (-1 : ℤ) else 1) := by
    intro k _
    unfold forcedJump
    split <;> simp
  rw [Finset.sum_congr rfl hsum, sum_ite_lt]
  simp [startState]

/-- Parity: the number of left steps `(K - d i)/2` really is half of `K - d i`. -/
lemma two_mul_div_two {K : ℕ} (hK : Even K) {d : ℕ} (hd : Even d) (h : d ≤ K) :
    2 * ((K - d) / 2) = K - d := by
  obtain ⟨a, rfl⟩ := hK
  obtain ⟨b, rfl⟩ := hd
  have hdvd : 2 ∣ (a + a - (b + b)) := ⟨a - b, by omega⟩
  rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]

/-- Along the prescribed path no walker is above the level `0` before time `K`. -/
lemma pos_forced_nonpos (K : ℕ) (hK : Even K) (d : Fin N → ℕ) (hd : ∀ i, d i ≤ K)
    (hde : ∀ i, Even (d i)) (η : Fin N → ℤ → ℕ) (hη : ∀ i x, η i x ≤ m)
    (i : Fin N) {n : ℕ} (hn : n ≤ K) :
    (evolveFun (m := m) (forcedJump K d) n (startState d η hη)).pos i ≤ 0 := by
  rw [pos_forced]
  have hc : (((K - d i) / 2 : ℕ) : ℤ) * 2 = ((K - d i : ℕ) : ℤ) := by
    have h2 : ((K - d i) / 2) * 2 = K - d i := by
      rw [Nat.mul_comm]; exact two_mul_div_two hK (hde i) (hd i)
    exact_mod_cast h2
  have hcast : ((K - d i : ℕ) : ℤ) = (K : ℤ) - (d i : ℤ) := by
    push_cast [hd i]
    ring
  split_ifs with h1
  · omega
  · omega

/-- At time `K+1` every walker of the prescribed path is at the new record level `1`. -/
lemma pos_forced_record (K : ℕ) (hK : Even K) (d : Fin N → ℕ) (hd : ∀ i, d i ≤ K)
    (hde : ∀ i, Even (d i)) (η : Fin N → ℤ → ℕ) (hη : ∀ i x, η i x ≤ m) (i : Fin N) :
    (evolveFun (m := m) (forcedJump K d) (K + 1) (startState d η hη)).pos i = 1 := by
  rw [pos_forced]
  have hc : (((K - d i) / 2 : ℕ) : ℤ) * 2 = ((K - d i : ℕ) : ℤ) := by
    have h2 : ((K - d i) / 2) * 2 = K - d i := by
      rw [Nat.mul_comm]; exact two_mul_div_two hK (hde i) (hd i)
    exact_mod_cast h2
  have hcast : ((K - d i : ℕ) : ℤ) = (K : ℤ) - (d i : ℤ) := by
    push_cast [hd i]
    ring
  rw [if_neg (by omega : ¬ (K + 1 ≤ (K - d i) / 2))]
  omega

/-! ### The mass of the simultaneous-record event -/

/-- The state after following the first `n` jumps of the path `q`. -/
noncomputable def stateAt {k : ℕ} (q : Fin k → JumpVec N) (n : ℕ) (hn : n ≤ k)
    (s : State N m) : State N m :=
  evolve n (fun i : Fin n => q ⟨i.1, lt_of_lt_of_le i.2 hn⟩) s

/-- The event that, along the path `q` of length `k`, the record level `1` is reached for
the first time at time `k` and every walker is then at `1` — so the shifted record state has
`d_i = 0` for all `i`, i.e. lies in the set `F` of the paper. -/
def HitsFAt {k : ℕ} (q : Fin k → JumpVec N) (s : State N m) : Prop :=
  (∀ i, (stateAt q k le_rfl s).pos i = 1) ∧
    ∀ (n : ℕ) (hn : n < k) (i : Fin N), (stateAt q n (le_of_lt hn) s).pos i ≤ 0

/-- The mass, under the path measure of length `k`, of the event `HitsFAt`. -/
noncomputable def hitFMass (p : ℝ) (k : ℕ) (s : State N m) : ℝ := by
  classical
  exact ∑ q : Fin k → JumpVec N, (if HitsFAt q s then (1 : ℝ) else 0) * pathW p k q s

theorem hitFMass_le_one (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (k : ℕ) (s : State N m) :
    hitFMass p k s ≤ 1 := by
  classical
  rw [hitFMass]
  calc ∑ q : Fin k → JumpVec N, (if HitsFAt q s then (1 : ℝ) else 0) * pathW p k q s
      ≤ ∑ q : Fin k → JumpVec N, pathW p k q s := by
        refine Finset.sum_le_sum fun q _ => ?_
        split_ifs with h
        · simp
        · simp only [zero_mul]
          exact pathW_nonneg p hp hp1 k q s
    _ = 1 := sum_pathW_one p k s

/-- **Eq. (force)**: from any state in which all walkers are at most `K` below the record
(with `K` and the distances even, as at record times), the probability that the next record
state is a simultaneous record is at least `(1-p)^(N(K+1))`. -/
theorem hitFMass_ge (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (K : ℕ) (hK : Even K)
    (d : Fin N → ℕ) (hd : ∀ i, d i ≤ K) (hde : ∀ i, Even (d i))
    (η : Fin N → ℤ → ℕ) (hη : ∀ i x, η i x ≤ m) :
    (1 - p) ^ (N * (K + 1)) ≤ hitFMass (m := m) p (K + 1) (startState d η hη) := by
  classical
  -- the prescribed jump vector is a path of length `K+1`
  set qstar : Fin (K + 1) → JumpVec N := fun i => forcedJump K d (i : ℕ) with hqstar
  have hpath : (1 - p) ^ (N * (K + 1)) ≤ pathW (m := m) p (K + 1) qstar (startState d η hη) := by
    rw [show qstar = (fun i : Fin (K+1) => forcedJump K d (i : ℕ)) from rfl,
      pathW_eq_pathWFun]
    exact pathWFun_ge p (forcedJump K d) hp hp1 (K + 1) _
  have hhit : HitsFAt qstar (startState d η hη) := by
    constructor
    · intro i
      have h1 : stateAt qstar (K + 1) le_rfl (startState d η hη)
          = evolveFun (m := m) (forcedJump K d) (K + 1) (startState d η hη) := by
        rw [stateAt]
        exact evolve_eq_evolveFun (forcedJump K d) (K + 1) _
      rw [h1]
      exact pos_forced_record K hK d hd hde η hη i
    · intro n hn i
      have h1 : stateAt qstar n (le_of_lt hn) (startState d η hη)
          = evolveFun (m := m) (forcedJump K d) n (startState d η hη) := by
        rw [stateAt]
        exact evolve_eq_evolveFun (forcedJump K d) n _
      rw [h1]
      exact pos_forced_nonpos (n := n) K hK d hd hde η hη i (Nat.lt_succ_iff.mp hn)
  rw [hitFMass]
  refine le_trans hpath ?_
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun q : Fin (K+1) → JumpVec N =>
      (if HitsFAt q (startState d η hη) then (1 : ℝ) else 0)
        * pathW (m := m) p (K + 1) q (startState d η hη))
    (fun q _ => ?_) (Finset.mem_univ qstar))
  · rw [if_pos hhit, one_mul]
  · split_ifs with h
    · simp only [one_mul]
      exact pathW_nonneg p hp hp1 (K + 1) q _
    · simp only [zero_mul]
      exact le_refl 0

end SimJump
