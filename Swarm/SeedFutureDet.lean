/-
# The future of a state depends only on the coordinates not already consumed

The regeneration seed argument needs the independence of the "future stays above the record
level" event from the finite block of coordinates used by a prescribed prefix.  The
measure-theoretic content of that independence is the *determinacy* proved here: if two arrays
agree outside a finite set `Q` of coordinates that the prefix has already consumed — every
`(i, x, k) ∈ Q` at a nonnegative level `x` satisfies `k ≤ s.ell i x`, and `Q` misses the very
first departure coordinate of `s` — then the two futures started from `s` are identical as long
as the first one stays nonnegative.

The mechanism is the freshness of departure coordinates (`departureCoord` is injective along a
trajectory): a revisit to a level `x` after time `0` reads the coordinate at index at least
`s.ell i x + 1`, strictly above every index already consumed at that level.
-/
import Swarm.SeedTransplant
import Swarm.SeedPrescribe

open MeasureTheory Set ProbabilityTheory
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmRestart

namespace SwarmSeed

variable {N : ℕ}

/-- Two states with the same positions and the same local-time field are equal. -/
theorem walkState_ext {a b : WalkState N} (h1 : a.pos = b.pos) (h2 : a.ell = b.ell) : a = b := by
  obtain ⟨p1, e1⟩ := a
  obtain ⟨p2, e2⟩ := b
  simp only at h1 h2
  rw [h1, h2]

/-! ### Monotonicity of the local times of the iterated recursion -/

theorem ell_mono_trajFrom (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) (n : ℕ)
    (i : Fin N) (x : ℤ) : s.ell i x ≤ (trajFrom p m U s n).ell i x := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [trajFrom_succ, nextWalkState_ell]
      exact le_trans ih (Nat.le_add_right _ _)

/-- One step of the recursion increases the local time at the new position by one. -/
theorem ell_step (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) (n : ℕ) (i : Fin N) :
    (trajFrom p m U s (n + 1)).ell i ((trajFrom p m U s (n + 1)).pos i)
      = (trajFrom p m U s n).ell i ((trajFrom p m U s (n + 1)).pos i) + 1 := by
  rw [trajFrom_succ, nextWalkState_ell, nextWalkState_pos]
  simp

/-- At a positive time the local time at the current position is strictly above the initial
local time there: the arrival just increased it. -/
theorem ell_pos_add_one (p : ℝ) (m : ℕ) (U : Array N) (s : WalkState N) {n : ℕ} (hn : 1 ≤ n)
    (i : Fin N) :
    s.ell i ((trajFrom p m U s n).pos i) + 1
      ≤ (trajFrom p m U s n).ell i ((trajFrom p m U s n).pos i) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  calc s.ell i ((trajFrom p m U s (k + 1)).pos i) + 1
      ≤ (trajFrom p m U s k).ell i ((trajFrom p m U s (k + 1)).pos i) + 1 := by
        have hmono := ell_mono_trajFrom p m U s k i ((trajFrom p m U s (k + 1)).pos i)
        omega
    _ = (trajFrom p m U s (k + 1)).ell i ((trajFrom p m U s (k + 1)).pos i) := by
        rw [ell_step]

/-! ### Determinacy of the future -/

/-- **The future depends only on the coordinates not already consumed.**  Two arrays that agree
off a finite set `Q`, where `Q` only contains coordinates at nonnegative levels whose departure
index is at most the initial local time, and `Q` misses the first departure coordinate, drive
the same future from `s` as long as that future stays nonnegative. -/
theorem future_determined {p : ℝ} {m : ℕ} {s : WalkState N} {d : ℤ} (hd : 0 ≤ d)
    {Q : Finset (Fin N × ℤ × ℕ)}
    (hQ : ∀ (i : Fin N) (x : ℤ) (k : ℕ), (i, x, k) ∈ Q → 0 ≤ x → k ≤ s.ell i x)
    (hQ0 : ∀ i : Fin N, (i, s.pos i, s.ell i (s.pos i)) ∉ Q)
    {U U' : Array N} (hagree : ∀ q, q ∉ Q → U q = U' q) :
    (FutureGe p m s d U ↔ FutureGe p m s d U') := by
  have key : ∀ (A B : Array N), (∀ q, q ∉ Q → A q = B q) → ∀ n,
      (∀ k, k ≤ n → ∀ i, 0 ≤ (trajFrom p m A s k).pos i) →
      trajFrom p m A s n = trajFrom p m B s n := by
    intro A B hAB n
    induction n with
    | zero => intro _; rw [trajFrom_zero, trajFrom_zero]
    | succ n ih =>
        intro hnonneg
        have hprev : ∀ k, k ≤ n → ∀ i, 0 ≤ (trajFrom p m A s k).pos i :=
          fun k hk i => hnonneg k (by omega) i
        have heq := ih hprev
        have hfresh : ∀ i : Fin N,
            (i, (trajFrom p m A s n).pos i, (trajFrom p m A s n).ell i ((trajFrom p m A s n).pos i))
              ∉ Q := by
          intro i hmem
          have hx0 : 0 ≤ (trajFrom p m A s n).pos i := hnonneg n (Nat.le_succ n) i
          have hxk := hQ i ((trajFrom p m A s n).pos i)
            ((trajFrom p m A s n).ell i ((trajFrom p m A s n).pos i)) hmem hx0
          rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn
            exact hQ0 i hmem
          · have hlt := ell_pos_add_one p m A s hn i
            omega
        have hjump : ∀ i : Fin N,
            nextPos p m A (trajFrom p m A s n) i = nextPos p m B (trajFrom p m B s n) i := by
          intro i
          have hcoord : A (i, (trajFrom p m A s n).pos i,
              (trajFrom p m A s n).ell i ((trajFrom p m A s n).pos i))
              = B (i, (trajFrom p m A s n).pos i,
                (trajFrom p m A s n).ell i ((trajFrom p m A s n).pos i)) :=
            hAB _ (hfresh i)
          rw [nextPos, nextPos, ← heq, hcoord]
        rw [heq] at hjump
        rw [trajFrom_succ, trajFrom_succ, heq]
        refine walkState_ext ?_ ?_
        · funext i
          exact hjump i
        · funext i x
          rw [nextWalkState_ell, nextWalkState_ell, hjump i]
  constructor
  · intro hU
    have hstates : ∀ n, trajFrom p m U s n = trajFrom p m U' s n :=
      fun n => key U U' hagree n (fun k _ i => le_trans hd (hU k i))
    intro n i
    rw [← hstates n]
    exact hU n i
  · intro hU'
    have hstates : ∀ n, trajFrom p m U s n = trajFrom p m U' s n :=
      fun n => (key U' U (fun q hq => (hagree q hq).symm) n (fun k _ i => le_trans hd (hU' k i))).symm
    intro n i
    rw [hstates n]
    exact hU' n i

end SwarmSeed
