/-
  Discharging the pathwise hypotheses of Lemma `transience` for the **actual interacting
  trajectory** (`main_1d_revised.tex`, §2.2).

  `Swarm/Levels.lean` states the paper's Lemma `transience` with five pathwise
  hypotheses: unit steps, `u 0 = 0`, "every level is visited", a no-bad-time condition
  `hbad`, level `k+1` reached by time `(k+1)^4` (`hτk`), and the other walker's
  running-maximum domination `(b k)+1 <= M^j_s` on `[k, (k+1)^4]` (`hMv`).

  This file proves, for the actual trajectory and `p >= 1/2`, that all of them hold
  almost surely except `hbad`:
  * `trajectory_unitSteps`, `trajectory_zero_pos` — the recursion moves by `±1` (no
    probability involved);
  * `ae_all_levels_hit` — every nonnegative level is visited (from the verified
    `ae_unbounded_above` plus the discrete intermediate value property);
  * `ae_eventually_reach_succ` — `hτk`, from the verified running-maximum rate
    `floor(n^{1/4}) <= M_n` of `Rate.lean`;
  * `ae_eventually_runMax_ge_lvlB` — `hMv`.

  The remaining hypothesis `hbad` is exactly the Borel--Cantelli consequence of the
  crossing estimate eq. (cross); it is *not* assumed to be true, it is carried as an
  explicit hypothesis on the sample.
-/
import Swarm.PathNat
import Swarm.Rate
import Swarm.Levels

open MeasureTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators Topology

namespace SwarmDischarge

open SwarmSpeed

/-! ### The paper's level sequences -/

/-- `b_k + 1 = floor(k^{1/4})` for `k >= 1`. -/
theorem lvlB_add_one {k : ℕ} (hk : 1 ≤ k) : lvlB k + 1 = Nat.sqrt (Nat.sqrt k) := by
  have h1 : 1 ≤ Nat.sqrt (Nat.sqrt k) := by
    have h2 : Nat.sqrt 1 ≤ Nat.sqrt (Nat.sqrt k) :=
      Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk)
    simpa using h2
  unfold lvlB
  omega

/-! ### The paper-level form of the pathwise lemma -/

/-- **Lemma `transience`, pathwise part, with the paper's concrete levels**
(`b_k = floor(k^{1/4}) - 1`, `a_k = floor(b_k/2)`), nonnegative-level interface. -/
theorem transience_of_paper_levels_nat (u v : ℕ → ℤ) (hu : SwarmDeepNat.UnitSteps u) (hu0 : u 0 = 0)
    (h : ∀ z : ℕ, ∃ n, u n = (z : ℤ)) {K : ℕ}
    (hK : 2 ≤ K)
    (hbad : ∀ k ≥ K, ∀ s ≤ (k + 1) ^ 4, ¬ (u s = (lvlB k : ℤ) ∧ (lvlB k : ℤ) + 1 ≤ runMax v s ∧
      SwarmDeepNat.hitBefore u s ((lvlB k : ℤ) + 1) (lvlA k)))
    (hτk : ∀ k ≥ K, SwarmDeepNat.firstHit u h (k + 1) ≤ (k + 1) ^ 4)
    (hMv : ∀ k ≥ K, ∀ s, k ≤ s → s ≤ (k + 1) ^ 4 → (lvlB k : ℤ) + 1 ≤ runMax v s) :
    Tendsto u atTop atTop :=
  SwarmDeepNat.tendsto_atTop_of_no_deep_returns hu hu0 h (K := K) (b := lvlB) (a := lvlA)
    (fun k _ => lvlA_le_lvlB k) (fun k hk => lvlB_lt_self (le_trans hK hk))
    lvlA_mono tendsto_lvlA hbad hτk hMv

/-! ### The trajectory moves by unit steps -/

/-- The actual interacting trajectory takes nearest-neighbour steps. -/
theorem trajectory_unitSteps {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    SwarmDeepNat.UnitSteps (fun t => (trajectory p m U t).pos i) := by
  intro n
  show (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i + 1 ∨
    (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i - 1
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  unfold drivenStep
  split_ifs with h
  · left; ring
  · right; ring

/-- The actual interacting trajectory starts at `0`. -/
theorem trajectory_zero_pos {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) :
    (trajectory p m U 0).pos i = 0 := by
  simp

/-! ### Every nonnegative level is visited -/

/-- A unit-step path from `0` that is unbounded above visits every nonnegative level. -/
theorem exists_level_of_unbounded {u : ℕ → ℤ} (hu : SwarmDeepNat.UnitSteps u) (hu0 : u 0 = 0)
    (hub : ∀ B : ℕ, ∃ t, (B : ℤ) ≤ u t) : ∀ z : ℕ, ∃ n, u n = (z : ℤ) := by
  intro z
  rcases Nat.eq_zero_or_pos z with hz | hz
  · subst hz
    exact ⟨0, by simp [hu0]⟩
  · obtain ⟨t, ht⟩ := hub z
    have hex : ∃ n, (z : ℤ) ≤ u n := ⟨t, ht⟩
    refine ⟨Nat.find hex, ?_⟩
    have hspec : (z : ℤ) ≤ u (Nat.find hex) := Nat.find_spec hex
    have ht0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h, hu0] at hspec
      omega
    obtain ⟨t', ht'⟩ : ∃ t', Nat.find hex = t' + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin : ¬ ((z : ℤ) ≤ u t') := by
      intro hle
      exact Nat.find_min hex (by omega : t' < Nat.find hex) hle
    push Not at hmin
    rw [ht'] at hspec ⊢
    rcases hu t' with hh | hh <;> rw [hh] at hspec ⊢ <;> omega

/-- Every nonnegative level is visited by the actual interacting walker. -/
theorem ae_all_levels_hit {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ z : ℕ, ∃ n, (trajectory p m U n).pos i = (z : ℤ) := by
  filter_upwards [Swarming.Actual.ae_unbounded_above (N := N) hp m i] with U hU
  exact exists_level_of_unbounded (trajectory_unitSteps p m U i) (trajectory_zero_pos p m U i) hU

/-! ### Reading off a level from the running maximum -/

/-- `b <= runMax u n` iff the path reaches level `b` by time `n`. -/
theorem le_runMax_iff {u : ℕ → ℤ} {n : ℕ} {b : ℤ} :
    b ≤ runMax u n ↔ ∃ t ≤ n, b ≤ u t := by
  unfold runMax
  constructor
  · intro hb
    obtain ⟨t, ht, hle⟩ := (Finset.le_sup'_iff ⟨0, by simp⟩).mp hb
    simp only [Finset.mem_range] at ht
    exact ⟨t, by omega, hle⟩
  · rintro ⟨t, ht, hle⟩
    exact (Finset.le_sup'_iff ⟨0, by simp⟩).mpr ⟨t, Finset.mem_range.mpr (by omega), hle⟩

/-- The first time a unit-step path from `0` reaches level `z >= 0` hits `z` exactly. -/
theorem exists_hit_le_of_reach {u : ℕ → ℤ} (hu : SwarmDeepNat.UnitSteps u) (hu0 : u 0 = 0) {z : ℕ}
    {M : ℕ} (hM : ∃ k ≤ M, (z : ℤ) ≤ u k) : ∃ t ≤ M, u t = (z : ℤ) := by
  rcases Nat.eq_zero_or_pos z with hz | hz
  · subst hz
    exact ⟨0, Nat.zero_le M, by simp [hu0]⟩
  · obtain ⟨k, hk, hle⟩ := hM
    have hex : ∃ n, (z : ℤ) ≤ u n := ⟨k, hle⟩
    refine ⟨Nat.find hex, ?_, ?_⟩
    · exact le_trans (Nat.find_min' hex hle) hk
    · have hspec : (z : ℤ) ≤ u (Nat.find hex) := Nat.find_spec hex
      have ht0 : Nat.find hex ≠ 0 := by
        intro h
        rw [h, hu0] at hspec
        omega
      obtain ⟨t', ht'⟩ : ∃ t', Nat.find hex = t' + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hmin : ¬ ((z : ℤ) ≤ u t') := by
        intro hll
        exact Nat.find_min hex (by omega : t' < Nat.find hex) hll
      push Not at hmin
      rw [ht'] at hspec ⊢
      rcases hu t' with hh | hh <;> rw [hh] at hspec ⊢ <;> omega

/-- `floor(floor(((k+1)^2)^2)^{1/2})^{1/2}) = k+1`. -/
theorem sqrt_sqrt_fourth (k : ℕ) : Nat.sqrt (Nat.sqrt ((k + 1) ^ 4)) = k + 1 := by
  rw [show (k + 1) ^ 4 = ((k + 1) ^ 2) ^ 2 by ring, Nat.sqrt_eq', Nat.sqrt_eq']

/-! ### `hτk`: every level `k+1` is reached before time `(k+1)^4` -/

/-- **`hτk` for the actual trajectory** (level-reach form, which is proof-irrelevant).
Almost surely, for all large `k`, walker `i` is at level `k+1` at some time `<= (k+1)^4`. -/
theorem ae_eventually_reach_succ {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ K : ℕ, ∀ k ≥ K,
      ∃ t ≤ (k + 1) ^ 4, (trajectory p m U t).pos i = ((k + 1 : ℕ) : ℤ) := by
  filter_upwards [SwarmRate.ae_eventually_sqrt_sqrt_le_runMax (N := N) hp m i] with U hU
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hU
  refine ⟨N₀, fun k hk => ?_⟩
  have h1 : N₀ ≤ (k + 1) ^ 4 := by
    have : k + 1 ≤ (k + 1) ^ 4 := by
      have h0 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      calc k + 1 = (k + 1) ^ 1 := by ring
        _ ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right h0 (by norm_num)
    omega
  have hrate := hN₀ _ h1
  rw [sqrt_sqrt_fourth] at hrate
  have hreach : ∃ t ≤ (k + 1) ^ 4, ((k + 1 : ℕ) : ℤ) ≤ (trajectory p m U t).pos i :=
    (le_runMax_iff (u := fun t => (trajectory p m U t).pos i) (n := (k + 1) ^ 4)
      (b := ((k + 1 : ℕ) : ℤ))).mp hrate
  exact exists_hit_le_of_reach (trajectory_unitSteps p m U i) (trajectory_zero_pos p m U i) hreach

/-! ### `hMv`: the other walker's running maximum dominates `b_k + 1` -/

/-- **`hMv` for the actual trajectories.**  Almost surely, for all large `k` and every
`s` in `[k, (k+1)^4]`, the running maximum of walker `j` at time `s` is at least
`b_k + 1 = floor(k^{1/4})`. -/
theorem ae_eventually_runMax_ge_lvlB {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (j : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∃ K : ℕ, ∀ k ≥ K, ∀ s, k ≤ s → s ≤ (k + 1) ^ 4 →
      (lvlB k : ℤ) + 1 ≤ runMax (fun t => (trajectory p m U t).pos j) s := by
  filter_upwards [SwarmRate.ae_eventually_sqrt_sqrt_le_runMax (N := N) hp m j] with U hU
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hU
  refine ⟨max N₀ 1, fun k hk s hks _ => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right N₀ 1) hk
  have hs1 : N₀ ≤ s := le_trans (le_max_left N₀ 1) (le_trans hk hks)
  have hrate := hN₀ s hs1
  have hmono : Nat.sqrt (Nat.sqrt k) ≤ Nat.sqrt (Nat.sqrt s) :=
    Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hks)
  have hcast : ((Nat.sqrt (Nat.sqrt k) : ℕ) : ℤ) ≤ ((Nat.sqrt (Nat.sqrt s) : ℕ) : ℤ) := by
    exact_mod_cast hmono
  have hgoal : (lvlB k : ℤ) + 1 = ((Nat.sqrt (Nat.sqrt k) : ℕ) : ℤ) := by
    rw [← lvlB_add_one hk1]
    push_cast
    ring
  rw [hgoal]
  linarith

end SwarmDischarge


