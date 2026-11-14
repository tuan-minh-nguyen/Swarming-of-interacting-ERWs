/-
Finite-horizon force input in the compact record-state coordinates.
This is not yet the probability kernel of the stopped record chain.
-/
import Swarm.Bridge

namespace SimJump.Record

open SwarmRec

variable {N m : ℕ}

/-- An arbitrary continuation of a finite jump sequence. -/
def extendPath {k : ℕ} (q : Fin k → JumpVec N) : ℕ → JumpVec N := fun n =>
  if h : n < k then q ⟨n, h⟩ else fun _ => true

lemma evolveFun_extendPath_le {N m : ℕ} {k : ℕ} (q : Fin k → JumpVec N) (s : State N m)
    (n : ℕ) (hn : n ≤ k) :
    evolveFun (m := m) (extendPath q) n s = stateAt q n hn s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hk : n < k := by omega
      rw [evolveFun_succ, ih (Nat.le_of_lt hk)]
      simp only [extendPath, hk, ↓reduceIte]
      rfl

/-- A finite simultaneous-record path is a first-record path for its continuation. -/
lemma firstRecord_extendPath {N m : ℕ} (hN : 0 < N) {k : ℕ} (q : Fin k → JumpVec N)
    (s : State N m) (hq : HitsFAt q s) : FirstRecord (extendPath q) k s := by
  let i₀ : Fin N := ⟨0, hN⟩
  refine ⟨⟨i₀, ?_⟩, ?_⟩
  · rw [evolveFun_extendPath_le q s k le_rfl]
    exact hq.1 i₀
  · intro n hn i
    rw [evolveFun_extendPath_le q s n (Nat.le_of_lt hn)]
    exact hq.2 n hn i

/-- Every finite `HitsFAt` path reaches the simultaneous-record compact set. -/
lemma toRecState_mem_srSet_of_hits {N m : ℕ} (hN : 0 < N) {k : ℕ} (q : Fin k → JumpVec N)
    (y : RecState N m) (hm : 1 ≤ m) (hq : HitsFAt q (ofRecState y)) :
    toRecState (extendPath q) k (ofRecState y) hm
      (firstRecord_extendPath hN q (ofRecState y) hq) (ofRecState_recordStart y hm)
      ∈ srSet N m := by
  have hrec : FirstRecord (extendPath q) k (ofRecState y) :=
    firstRecord_extendPath hN q (ofRecState y) hq
  have hs : RecordStart (ofRecState y) := ofRecState_recordStart y hm
  let out := toRecState (extendPath q) k (ofRecState y) hm hrec hs
  change ∀ i, dist2 out i ≤ 0
  intro i
  change halfDist ((evolveFun (m := m) (extendPath q) k (ofRecState y)).pos i) ≤ 0
  rw [evolveFun_extendPath_le q (ofRecState y) k le_rfl, hq.1 i]
  simp [halfDist]

/-- A state is determined by its positions and capped local times; the cap proof is
irrelevant. -/
private lemma state_eq {s t : State N m} (hp : s.pos = t.pos) (he : s.eta = t.eta) : s = t := by
  cases s
  cases t
  simp_all

/-- `ofRecState` is `SimJump.startState` with full distances twice the stored
half-distances, including its capped local-time profile. -/
lemma ofRecState_eq_startState (y : RecState N m) :
    ofRecState y = startState (fun i => 2 * y.val.1 i)
      (fun i x => (y.val.2 i x).val)
      (fun i x => Nat.le_of_lt_succ (y.val.2 i x).isLt) := by
  apply state_eq
  · funext i
    simp [ofRecState, startState, Nat.cast_mul]
  · rfl

/-- Compact-coordinate finite-horizon force bound.  This is exactly the finite-horizon
version; instantiating the eventual stopped record kernel is a separate task. -/
theorem hitFMass_ge_recState {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (K : ℕ) (y : RecState N m) (hy : y ∈ exh N m K) :
    (1 - p) ^ (N * (2 * K + 1)) ≤ hitFMass p (2 * K + 1) (ofRecState y) := by
  have hy' : ∀ i, y.val.1 i ≤ K := hy
  have hd : ∀ i, 2 * y.val.1 i ≤ 2 * K := by
    intro i
    exact Nat.mul_le_mul_left 2 (hy' i)
  have hde : ∀ i, Even (2 * y.val.1 i) := fun i => ⟨y.val.1 i, by omega⟩
  have hη : ∀ (i : Fin N) (x : ℤ), (y.val.2 i x).val ≤ m := fun i x =>
    Nat.le_of_lt_succ (y.val.2 i x).isLt
  rw [ofRecState_eq_startState y]
  exact SimJump.hitFMass_ge p hp hp1 (2 * K) ⟨K, by omega⟩
    (fun i => 2 * y.val.1 i) hd hde (fun i x => (y.val.2 i x).val) hη

end SimJump.Record


