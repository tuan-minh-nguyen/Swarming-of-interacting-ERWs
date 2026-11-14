/-
Deterministic first-record facts for the independent capped-step chain.  This
isolates parity and first-crossing facts before normalising the record state.
-/
import Swarm.SimJumpPath

namespace SimJump.Record

open Finset

variable {N m : ℕ}

/-- At a first-record path, some walker reaches `1` and all earlier positions
are at most `0`. -/
def FirstRecord (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) : Prop :=
  (∃ i, (evolveFun (m := m) u k s).pos i = 1) ∧
    ∀ t < k, ∀ i, (evolveFun (m := m) u t s).pos i ≤ 0

/-- The strongest simultaneous-record event of `SimJumpPath` is a first-record
path, with every walker reaching `1` together. -/
theorem firstRecord_of_hitsFAt {N m : ℕ} [NeZero N] {k : ℕ} (u : ℕ → JumpVec N) (s : State N m)
    (h : ∀ i, (evolveFun (m := m) u k s).pos i = 1)
    (hprev : ∀ t < k, ∀ i, (evolveFun (m := m) u t s).pos i ≤ 0) :
    FirstRecord u k s := by
  exact ⟨⟨Classical.ofNonempty, h Classical.ofNonempty⟩, hprev⟩

lemma evolveFun_pos_parity (u : ℕ → JumpVec N) (s : State N m)
    (hs : ∀ i, Even (s.pos i)) : ∀ (k : ℕ) (i : Fin N),
      Even ((evolveFun (m := m) u k s).pos i + (k : ℤ)) := by
  intro k
  induction k with
  | zero =>
      intro i
      simpa [evolveFun, evolve] using hs i
  | succ k ih =>
      intro i
      obtain ⟨a, ha⟩ := ih i
      rw [evolveFun_succ]
      change Even ((evolveFun (m := m) u k s).pos i +
        (if u k i = true then (1 : ℤ) else -1) + ((k + 1 : ℕ) : ℤ))
      cases hv : u k i
      · refine ⟨a, ?_⟩
        simp only [Bool.false_eq_true, if_false]
        push_cast at ha ⊢
        linarith
      · refine ⟨a + 1, ?_⟩
        simp only [if_true]
        push_cast at ha ⊢
        linarith

/-- Every position at a first-record time is odd. -/
lemma firstRecord_odd (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hs : ∀ i, Even (s.pos i)) (hk : Odd k) (i : Fin N) :
    Odd ((evolveFun (m := m) u k s).pos i) := by
  obtain ⟨a, ha⟩ := evolveFun_pos_parity u s hs k i
  obtain ⟨b, hb⟩ := hk
  refine ⟨a - b - 1, ?_⟩
  omega

/-- The first-record time itself is odd, since an initially even coordinate
reaches `1`. -/
lemma firstRecord_time_odd (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hs : ∀ i, Even (s.pos i)) (h : FirstRecord u k s) : Odd k := by
  obtain ⟨i, hi⟩ := h.1
  obtain ⟨a, ha⟩ := evolveFun_pos_parity u s hs k i
  rw [hi] at ha
  have hnonneg : 0 ≤ a - 1 := by omega
  refine ⟨(a - 1).toNat, ?_⟩
  have hnat : ((a - 1).toNat : ℤ) = a - 1 := Int.toNat_of_nonneg hnonneg
  have heq : (k : ℤ) = 2 * ((a - 1).toNat : ℤ) + 1 := by
    rw [hnat]
    omega
  exact_mod_cast heq

/-- Before the first global record `1`, no walker can jump beyond it. -/
lemma firstRecord_pos_le_one (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hs : ∀ i, Even (s.pos i)) (h : FirstRecord u k s) (i : Fin N) :
    (evolveFun (m := m) u k s).pos i ≤ 1 := by
  by_cases hk0 : k = 0
  · subst k
    exfalso
    obtain ⟨j, hj⟩ := h.1
    have hj0 : s.pos j = 1 := by simpa [evolveFun, evolve] using hj
    have he := hs j
    rw [hj0] at he
    obtain ⟨a, ha⟩ := he
    omega
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have hp := h.2 t (Nat.lt_succ_self t) i
  have hu : (evolveFun (m := m) u (t + 1) s).pos i =
      (evolveFun (m := m) u t s).pos i +
        (if u t i = true then (1 : ℤ) else -1) := by
    rw [evolveFun_succ, step_pos, stepPos]
  cases hv : u t i <;> simp only [hv, Bool.false_eq_true, if_false, if_true] at hu <;> omega

/-- The normalized capped state obtained after moving the record origin to `1`. -/
def normalize (s : State N m) : State N m where
  pos i := s.pos i - 1
  eta i x := s.eta i (x + 1)
  hcap i x := s.hcap i (x + 1)

/-- The extra constraints on a genuine record state, before considering its
compact topological representation. -/
structure RecordStart (s : State N m) : Prop where
  nonpos : ∀ i, s.pos i ≤ 0
  exists_zero : ∃ i, s.pos i = 0
  even_pos : ∀ i, Even (s.pos i)
  eta_pos : ∀ i, 1 ≤ s.eta i (s.pos i)
  eta_above : ∀ i x, 0 < x → s.eta i x = 0
  eta_origin : ∀ i, s.eta i 0 = if s.pos i = 0 then 1 else 0

/-- Half of the distance from a position `z ≤ 1` to the new record at `1`. -/
def halfDist (z : ℤ) : ℕ := ((1 - z) / 2).toNat

lemma normalized_pos_le (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hs : ∀ i, Even (s.pos i)) (h : FirstRecord u k s) (i : Fin N) :
    (normalize (evolveFun (m := m) u k s)).pos i ≤ 0 := by
  change (evolveFun (m := m) u k s).pos i - 1 ≤ 0
  have hle := firstRecord_pos_le_one u k s hs h i
  omega

lemma normalized_pos_even (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hs : ∀ i, Even (s.pos i)) (h : FirstRecord u k s) (i : Fin N) :
    Even ((normalize (evolveFun (m := m) u k s)).pos i) := by
  have hodd := firstRecord_odd u k s hs (firstRecord_time_odd u k s hs h) i
  obtain ⟨a, ha⟩ := hodd
  refine ⟨a, ?_⟩
  change (evolveFun (m := m) u k s).pos i - 1 = a + a
  omega

lemma two_mul_halfDist_cast {z : ℤ} (hz : Odd z) (hzone : z ≤ 1) :
    (2 * halfDist z : ℕ) = (1 - z : ℤ) := by
  obtain ⟨a, ha⟩ := hz
  have hnonneg : 0 ≤ (1 - z) / 2 := by omega
  unfold halfDist
  have hhalf : (1 - z) / 2 = -a := by omega
  rw [hhalf]
  push_cast
  rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -a)]
  omega

lemma normalized_pos_halfDist (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hs : ∀ i, Even (s.pos i)) (h : FirstRecord u k s) (i : Fin N) :
    (normalize (evolveFun (m := m) u k s)).pos i =
      -((2 * halfDist ((evolveFun (m := m) u k s).pos i) : ℕ) : ℤ) := by
  have hodd := firstRecord_odd u k s hs (firstRecord_time_odd u k s hs h) i
  have hle := firstRecord_pos_le_one u k s hs h i
  have hd := two_mul_halfDist_cast hodd hle
  change (evolveFun (m := m) u k s).pos i - 1 = _
  omega

/-- A positive site remains unvisited if every position up to time `k` stays
below it, so its capped local time is unchanged. -/
lemma evolveFun_eta_of_above (u : ℕ → JumpVec N) (s : State N m)
    (hs : ∀ i x, 0 < x → s.eta i x = 0) (b : ℤ) (hb : 0 ≤ b) :
    ∀ (k : ℕ),
      (∀ t ≤ k, ∀ i, (evolveFun (m := m) u t s).pos i ≤ b) →
      ∀ (i : Fin N) (x : ℤ), b < x →
        (evolveFun (m := m) u k s).eta i x = 0 := by
  intro k
  induction k with
  | zero =>
      intro hbound i x hx
      exact hs i x (by omega)
  | succ k ih =>
      intro hbound i x hx
      have hcurrent : (step m (evolveFun (m := m) u k s) (u k)).pos i ≤ b := by
        simpa only [evolveFun_succ, step_pos] using hbound (k + 1) le_rfl i
      rw [evolveFun_succ]
      have hne : x ≠ stepPos (evolveFun (m := m) u k s) (u k) i := by
        intro heq
        have hxle : x ≤ b := by
          rw [heq, ← step_pos]
          exact hcurrent
        exact (not_le.mpr hx) hxle
      rw [step_eta_of_ne _ _ _ _ hne]
      exact ih (fun t ht j => hbound t (ht.trans (Nat.le_succ k)) j) i x hx

/-- A first-record path cannot already be at the new record initially. -/
lemma firstRecord_time_pos (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hs : ∀ i, Even (s.pos i)) (h : FirstRecord u k s) : 0 < k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  subst k
  obtain ⟨i, hi⟩ := h.1
  have hi0 : s.pos i = 1 := by simpa [evolveFun, evolve] using hi
  have he := hs i
  rw [hi0] at he
  obtain ⟨a, ha⟩ := he
  omega

/-- At time one beyond a record origin, everybody has either exactly one visit
(at their arrival) or no visit yet. -/
lemma eta_origin_of_firstRecord (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hs : RecordStart s) (hm : 1 ≤ m) (h : FirstRecord u k s) (i : Fin N) :
    (evolveFun (m := m) u k s).eta i 1 =
      if (evolveFun (m := m) u k s).pos i = 1 then 1 else 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by
    have := firstRecord_time_pos u k s hs.even_pos h
    omega⟩
  rw [evolveFun_succ]
  let prev := evolveFun (m := m) u t s
  have hpreveta : prev.eta i 1 = 0 := by
    have hb : ∀ a ≤ t, ∀ j, (evolveFun (m := m) u a s).pos j ≤ 0 := by
      intro a ha j
      exact h.2 a (by omega) j
    exact evolveFun_eta_of_above u s hs.eta_above 0 (by norm_num) t hb i 1 (by norm_num)
  rw [step_pos]
  by_cases hpos : stepPos prev (u t) i = 1
  · have hpreveta' : (evolveFun (m := m) u t s).eta i (stepPos prev (u t) i) = 0 := by
      rw [hpos]
      exact hpreveta
    rw [if_pos hpos, ← hpos, step_eta_of_eq, hpreveta']
    simpa [cap] using min_eq_left hm
  · rw [if_neg hpos, step_eta_of_ne _ _ _ _ (fun hx => hpos hx.symm)]
    exact hpreveta

/-- The new local time at the position occupied at the first record is positive. -/
lemma eta_current_of_firstRecord (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hs : RecordStart s) (hm : 1 ≤ m) (i : Fin N) :
    1 ≤ (evolveFun (m := m) u k s).eta i ((evolveFun (m := m) u k s).pos i) := by
  cases k with
  | zero => simpa [evolveFun, evolve] using hs.eta_pos i
  | succ k =>
      let prev := evolveFun (m := m) u k s
      let newPos := stepPos prev (u k) i
      have hc : 1 ≤ cap m (prev.eta i newPos + 1) := by
        unfold cap
        exact le_min (by omega) hm
      simpa only [evolveFun_succ, step_pos, step_eta_of_eq] using hc

/-- **The normalized first-record state satisfies all record constraints.** -/
theorem normalized_recordStart (u : ℕ → JumpVec N) (k : ℕ) (s : State N m)
    (hs : RecordStart s) (hm : 1 ≤ m) (hk : FirstRecord u k s) :
    RecordStart (normalize (evolveFun (m := m) u k s)) where
  nonpos := normalized_pos_le u k s hs.even_pos hk
  exists_zero := by
    obtain ⟨i, hi⟩ := hk.1
    exact ⟨i, by change (evolveFun (m := m) u k s).pos i - 1 = 0; omega⟩
  even_pos := normalized_pos_even u k s hs.even_pos hk
  eta_pos i := by
    change 1 ≤ (evolveFun (m := m) u k s).eta i
      ((evolveFun (m := m) u k s).pos i - 1 + 1)
    simpa using eta_current_of_firstRecord u k s hs hm i
  eta_above i x hx := by
    change (evolveFun (m := m) u k s).eta i (x + 1) = 0
    apply evolveFun_eta_of_above u s hs.eta_above 1 (by norm_num) k
    · intro t ht j
      rcases eq_or_lt_of_le ht with rfl | ht'
      · exact firstRecord_pos_le_one u t s hs.even_pos hk j
      · exact (hk.2 t ht' j).trans (by norm_num)
    · omega
  eta_origin i := by
    change (evolveFun (m := m) u k s).eta i 1 =
      if (evolveFun (m := m) u k s).pos i - 1 = 0 then 1 else 0
    rw [eta_origin_of_firstRecord u k s hs hm hk i]
    congr 1
    simp only [eq_iff_iff]
    omega

/-- A valid normalized state uses exactly the half-distances to its new record. -/
lemma normalized_pos_halfDist_of_valid (s : State N m) (hs : RecordStart (normalize s))
    (i : Fin N) :
    (normalize s).pos i = -((2 * halfDist (s.pos i) : ℕ) : ℤ) := by
  have hle := hs.nonpos i
  have heven := hs.even_pos i
  change s.pos i - 1 ≤ 0 at hle
  change Even (s.pos i - 1) at heven
  obtain ⟨a, ha⟩ := heven
  have hodd : Odd (s.pos i) := by
    refine ⟨a, ?_⟩
    omega
  have hd := two_mul_halfDist_cast hodd (by omega : s.pos i ≤ 1)
  change s.pos i - 1 = -((2 * halfDist (s.pos i) : ℕ) : ℤ)
  omega

end SimJump.Record


