/-
Interface between the compact record-state representation and the independent
capped-step chain used by SimJumpPath.
-/
import Swarm.RecordStop
import Swarm.RecordState

namespace SimJump.Record

open SwarmRec

variable {N m : ℕ}

/-- Expand a compact record state into the capped-step chain. -/
def ofRecState (y : RecState N m) : State N m where
  pos i := -(2 * (y.val.1 i : ℤ))
  eta i x := (y.val.2 i x).val
  hcap i x := Nat.le_of_lt_succ (y.val.2 i x).isLt

lemma one_val (hm : 1 ≤ m) : (1 : Fin (m + 1)).val = 1 := by
  simp [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < m + 1)]

/-- The compact state satisfies exactly the additional invariants needed by the
first-record calculations; positivity requires `m ≥ 1`, as in the paper. -/
theorem ofRecState_recordStart (y : RecState N m) (hm : 1 ≤ m) : RecordStart (ofRecState y) := by
  have hy := y.property
  change (∃ i, y.val.1 i = 0) ∧
    (∀ (i : Fin N) (x : ℤ), 0 < x → y.val.2 i x = 0) ∧
    (∀ i, (1 : Fin (m + 1)) ≤ y.val.2 i (-(2 * (y.val.1 i : ℤ)))) ∧
    (∀ i, y.val.2 i 0 = if y.val.1 i = 0 then 1 else 0) at hy
  obtain ⟨⟨ilead, hlead⟩, habove, hpos, horigin⟩ := hy
  refine
    { nonpos := ?_
      exists_zero := ?_
      even_pos := ?_
      eta_pos := ?_
      eta_above := ?_
      eta_origin := ?_ }
  · intro i
    change -(2 * (y.val.1 i : ℤ)) ≤ 0
    have hn : 0 ≤ (y.val.1 i : ℤ) := Int.ofNat_zero_le _
    omega
  · exact ⟨ilead, by change -(2 * (y.val.1 ilead : ℤ)) = 0; simp [hlead]⟩
  · intro i
    refine ⟨-(y.val.1 i : ℤ), ?_⟩
    change -(2 * (y.val.1 i : ℤ)) = -(y.val.1 i : ℤ) + -(y.val.1 i : ℤ)
    ring
  · intro i
    change 1 ≤ (y.val.2 i (-(2 * (y.val.1 i : ℤ)))).val
    have hx := hpos i
    simpa [Fin.le_def, Nat.mod_eq_of_lt (by omega : 1 < m + 1)] using hx
  · intro i x hx
    change (y.val.2 i x).val = 0
    exact congrArg Fin.val (habove i x hx)
  · intro i
    change (y.val.2 i 0).val = if -(2 * (y.val.1 i : ℤ)) = 0 then 1 else 0
    by_cases hv : y.val.1 i = 0
    · have hz : -(2 * (y.val.1 i : ℤ)) = 0 := by simp [hv]
      rw [if_pos hz]
      have h0 := horigin i
      rw [if_pos hv] at h0
      have h0' := congrArg Fin.val h0
      simpa [Nat.mod_eq_of_lt (by omega : 1 < m + 1)] using h0'
    · have hz : ¬-(2 * (y.val.1 i : ℤ)) = 0 := by omega
      rw [if_neg hz]
      have h0 := horigin i
      rw [if_neg hv] at h0
      exact congrArg Fin.val h0

/-- The normalized position inside the compact coordinates recovers the original
half-distance exactly. -/
lemma halfDist_ofRecState (y : RecState N m) (i : Fin N) :
    halfDist ((ofRecState y).pos i) = y.val.1 i := by
  have heq : (1 - (ofRecState y).pos i) / 2 = (y.val.1 i : ℤ) := by
    change (1 - -(2 * (y.val.1 i : ℤ))) / 2 = (y.val.1 i : ℤ)
    omega
  unfold halfDist
  rw [heq]
  simp

/-- The ambient normalized output: half-deficits to the new record and capped local
times shifted one site to the left. -/
def toRecordAmb (s : State N m) : Amb N m :=
  (fun i => halfDist (s.pos i),
    fun i x => ⟨(normalize s).eta i x, Nat.lt_succ_of_le ((normalize s).hcap i x)⟩)

/-- A valid normalized state gives a legal compact record state. -/
theorem toRecordAmb_mem (s : State N m) (hs : RecordStart (normalize s)) :
    toRecordAmb s ∈ recSet N m := by
  have hpos : ∀ i, (normalize s).pos i =
      -((2 * halfDist (s.pos i) : ℕ) : ℤ) := by
    intro i
    exact normalized_pos_halfDist_of_valid s hs i
  have hm : 1 ≤ m := by
    obtain ⟨i, _⟩ := hs.exists_zero
    have heta := hs.eta_pos i
    have hb := (normalize s).hcap i ((normalize s).pos i)
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := hs.exists_zero
    refine ⟨i, ?_⟩
    change halfDist (s.pos i) = 0
    have hp := hpos i
    have hz : -((2 * halfDist (s.pos i) : ℕ) : ℤ) = 0 := by
      rw [← hpos i]
      exact hi
    omega
  · refine ⟨?_, ?_⟩
    · intro i x hx
      apply Fin.ext
      change (normalize s).eta i x = 0
      exact hs.eta_above i x hx
    · refine ⟨?_, ?_⟩
      · intro i
        apply Fin.le_def.mpr
        rw [one_val hm]
        change 1 ≤ (normalize s).eta i (-(2 * ((halfDist (s.pos i) : ℕ) : ℤ)))
        have hidx : -(2 * ((halfDist (s.pos i) : ℕ) : ℤ)) = (normalize s).pos i := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hpos i).symm
        rw [hidx]
        exact hs.eta_pos i
      · intro i
        have horigin := hs.eta_origin i
        change (toRecordAmb s).2 i 0 = if halfDist (s.pos i) = 0 then 1 else 0
        change (normalize s).eta i 0 =
          if (normalize s).pos i = 0 then 1 else 0 at horigin
        by_cases hi : halfDist (s.pos i) = 0
        · have hz : halfDist (s.pos i) = 0 := hi
          have hz0 : (normalize s).pos i = 0 := by rw [hpos i]; simp [hz]
          rw [if_pos hi]
          apply Fin.ext
          rw [if_pos hz0] at horigin
          simp only [toRecordAmb, one_val hm]
          exact horigin
        · have hz0 : (normalize s).pos i ≠ 0 := by
            intro hz
            have hp := hpos i
            rw [hz] at hp
            have hzHalf : (2 : ℕ) * halfDist (s.pos i) = 0 := by
              exact_mod_cast (neg_eq_zero.mp hp.symm)
            exact hi (by omega)
          rw [if_neg hi]
          apply Fin.ext
          rw [if_neg hz0] at horigin
          exact horigin

/-- Every first-record evolution yields a state in the compact record-state space. -/
noncomputable def toRecState (u : ℕ → JumpVec N) (k : ℕ) (s : State N m) (hm : 1 ≤ m)
    (hk : FirstRecord u k s) (hs : RecordStart s) : RecState N m :=
  ⟨toRecordAmb (evolveFun (m := m) u k s),
    toRecordAmb_mem _ (normalized_recordStart u k s hs hm hk)⟩

end SimJump.Record


