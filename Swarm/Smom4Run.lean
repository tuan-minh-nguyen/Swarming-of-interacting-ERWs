/-
  **The static tail sum `G_j(x)` of the paper: a run of unmarked sites makes it `O(L)`.**

  The paper's Proposition `spatial` (display `maxmom`, `s ∈ {2,4}`) bounds
  `(1 + max_j max_{x ≤ n+1} (h_j(x) + G_j(x)))^s`, where `h_j = h^ω_j` is the static individual
  potential and

      `G_j(x) = 1 + ∑_{ℓ≥1} ∏_{u=1}^{ℓ} (1-ω_j(x+u))/ω_j(x+u)`

  is the paper's reciprocal tail.  The Lean object is
  `SwarmSiteDiff.Gtail p m U i x K = 1 + ∑_{z ∈ [x,K)} ∏_{v ∈ (x,z]} (1-ω_i(v))/ω_i(v)`
  (truncated at `K`, and defined through `SwarmSiteDiff.rq (omegaN p m U i)`).

  This file proves the *deterministic* half of `(Smom₄)` for `Gtail`, i.e. the exact analogue of
  `SwarmMpot.hfix_le_of_no_long_run` for `h_j`:

  **`Gtail_le_of_no_long_run`**: if every window of `L ≥ 1` consecutive sites in `[0,K)` contains a
  site marked with weight `p`, then `Gtail p m U i x K ≤ 1 + L·p/(2p-1)` for *every* `x`.

  The mechanism is the recursion `S(x) = 1 + rq(x+1)·S(x+1)` of the truncated tail (i.e. the
  substitution `z = x` split off, giving the empty product `1`), the exact one-site values
  `rq = 1` at an unmarked site and `rq = (1-p)/p < 1` at a marked one, and the observation that a
  marked site in every window of length `L` leaves `L` sites per contraction, so the geometric
  series `∑_t ((1-p)/p)^t` contributes the factor `p/(2p-1)` and the window length enters only
  through `L`.  Nothing here is probabilistic; `Smom4Moment.lean` integrates this against the
  exact run probability of `SwarmMpot.runEvent_real`.
-/
import Swarm.SiteDiffStatic
import Swarm.MpotMain

set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SwarmSmom4

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmQVariance SwarmJointDrift SwarmSiteDiff SwarmMpot

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-! ### 1. The truncated tail as a functional of a two-valued ratio sequence -/

/-- The truncated tail sum `∑_{z ∈ [x,K)} ∏_{v ∈ (x,z]} f v`, i.e. `Gsum` read as a functional of
the ratio sequence `f = rq (omegaN i)`. -/
noncomputable def GS (f : ℕ → ℝ) (x K : ℕ) : ℝ :=
  ∑ z ∈ Finset.Ico x K, ∏ v ∈ Finset.Ico (x + 1) (z + 1), f v

theorem Gsum_eq_GS (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (x K : ℕ) :
    Gsum p m U i x K = GS (rq (omegaN p m U i)) x K := rfl

/-- `Gtail` in terms of `GS`. -/
theorem Gtail_eq_one_add_GS (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (x K : ℕ) :
    Gtail p m U i x K = 1 + GS (rq (omegaN p m U i)) x K := by
  unfold Gtail
  rw [Gsum_eq_GS]

/-- Nonnegativity of `GS` from nonnegative ratios. -/
theorem GS_nonneg {f : ℕ → ℝ} (hf0 : ∀ u, 0 ≤ f u) (x K : ℕ) : 0 ≤ GS f x K := by
  unfold GS
  refine Finset.sum_nonneg fun z _ => Finset.prod_nonneg fun v _ => hf0 v

/-- Every term of the tail is at most `1` when the ratios lie in `[0,1]`. -/
theorem GS_term_le_one {f : ℕ → ℝ} (hf0 : ∀ u, 0 ≤ f u) (hf1 : ∀ u, f u ≤ 1)
    {x K z : ℕ} (hz : z ∈ Finset.Ico x K) : (∏ v ∈ Finset.Ico (x + 1) (z + 1), f v) ≤ 1 :=
  Finset.prod_le_one (fun v _ => hf0 v) (fun v _ => hf1 v)

/-- The number of terms bounds the tail when all ratios lie in `[0,1]`. -/
theorem GS_card_terms {f : ℕ → ℝ} (hf0 : ∀ u, 0 ≤ f u) (hf1 : ∀ u, f u ≤ 1)
    (x K : ℕ) : GS f x K ≤ ((Finset.Ico x K).card : ℝ) := by
  unfold GS
  calc (∑ z ∈ Finset.Ico x K, ∏ v ∈ Finset.Ico (x + 1) (z + 1), f v)
      ≤ ∑ _z ∈ Finset.Ico x K, (1 : ℝ) :=
        Finset.sum_le_sum fun z hz => GS_term_le_one hf0 hf1 hz
    _ = ((Finset.Ico x K).card : ℝ) := by simp

/-- **The one-step recursion of the truncated tail**: splitting off the `z = x` term (whose product
is empty, hence `1`) turns the sum into `1 + rq(x+1)·S(x+1)`. -/
theorem GS_succ (f : ℕ → ℝ) {x K : ℕ} (hx : x < K) :
    GS f x K = 1 + f (x + 1) * GS f (x + 1) K := by
  unfold GS
  rw [Finset.sum_eq_sum_Ico_succ_bot hx]
  have hbot : (∏ v ∈ Finset.Ico (x + 1) (x + 1), f v) = 1 := by simp
  rw [hbot]
  have hterm : ∀ z ∈ Finset.Ico (x + 1) K,
      (∏ v ∈ Finset.Ico (x + 1) (z + 1), f v)
        = f (x + 1) * ∏ v ∈ Finset.Ico (x + 1 + 1) (z + 1), f v := by
    intro z hz
    have hxz : x + 1 < z + 1 := by
      have := (Finset.mem_Ico.mp hz).1
      omega
    rw [Finset.prod_eq_prod_Ico_succ_bot hxz]
  rw [Finset.sum_congr rfl hterm, Finset.mul_sum]

/-- **A run of unmarked sites is purely additive**: if `f = 1` on `(x, x+j]`, then
`S(x) = j + S(x+j)`. -/
theorem GS_add_run {f : ℕ → ℝ} {K : ℕ} :
    ∀ (j x : ℕ), x + j ≤ K → (∀ u, x < u → u ≤ x + j → f u = 1) →
      GS f x K = (j : ℝ) + GS f (x + j) K := by
  intro j
  induction j with
  | zero => intro x _ _; simp
  | succ j ih =>
    intro x hxK hrun
    have hxK' : x < K := by omega
    rw [GS_succ f hxK']
    have h1 : f (x + 1) = 1 := hrun (x + 1) (by omega) (by omega)
    rw [h1, one_mul]
    have hunm : ∀ u, x + 1 < u → u ≤ x + 1 + j → f u = 1 := by
      intro u h1' h2'
      exact hrun u (by omega) (by omega)
    rw [ih (x + 1) (by omega) hunm]
    have hcast : (x + 1 + j) = (x + (j + 1)) := by omega
    rw [hcast]
    push_cast
    ring

/-! ### 2. The constants -/

theorem two_p_sub_one_pos {p : ℝ} (hp : 1 / 2 < p) : (0 : ℝ) < 2 * p - 1 := by linarith

/-- The contraction factor `α = (1-p)/p ∈ [0,1)`. -/
theorem alpha_nonneg {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) : 0 ≤ (1 - p) / p := by
  have : (0 : ℝ) < p := by linarith
  exact div_nonneg (by linarith) this.le

theorem alpha_le_one {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) : (1 - p) / p ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by linarith
  rw [div_le_one hp0]
  linarith

/-- `1 - α = (2p-1)/p`, the decrement of the tail sum per contraction. -/
theorem one_sub_alpha {p : ℝ} (hp : 1 / 2 < p) :
    1 - (1 - p) / p = (2 * p - 1) / p := by
  have hp0 : (0 : ℝ) < p := by linarith
  field_simp
  ring

/-- The coefficient `p/(2p-1) = 1/(1-α)` of the window length in the tail bound. -/
noncomputable def Kp (p : ℝ) : ℝ := p / (2 * p - 1)

theorem Kp_pos {p : ℝ} (hp : 1 / 2 < p) : 0 < Kp p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have h := two_p_sub_one_pos hp
  unfold Kp
  positivity

theorem one_le_Kp {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) : 1 ≤ Kp p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have h2 := two_p_sub_one_pos hp
  unfold Kp
  rw [le_div_iff₀ h2]
  linarith

/-- The exact decrement identity `α · (L·p/(2p-1)) = L·p/(2p-1) - L`. -/
theorem alpha_mul_Kp_mul (hp : 1 / 2 < p) {L : ℕ} :
    ((1 - p) / p) * ((L : ℝ) * Kp p) = (L : ℝ) * Kp p - (L : ℝ) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have h2 := two_p_sub_one_pos hp
  have hα : (1 - p) / p = 1 - (2 * p - 1) / p := by
    rw [← one_sub_alpha hp]
    ring
  have hdec : ((2 * p - 1) / p) * Kp p = 1 := by
    unfold Kp
    field_simp
  calc ((1 - p) / p) * ((L : ℝ) * Kp p)
      = (1 - (2 * p - 1) / p) * ((L : ℝ) * Kp p) := by rw [hα]
    _ = (L : ℝ) * Kp p - ((2 * p - 1) / p) * ((L : ℝ) * Kp p) := by ring
    _ = (L : ℝ) * Kp p - (L : ℝ) * (((2 * p - 1) / p) * Kp p) := by ring
    _ = (L : ℝ) * Kp p - (L : ℝ) := by rw [hdec]; ring

/-! ### 3. The main deterministic bound -/

/-- **The run bound for the paper's tail `G_j`.**  Let `f` be a `{1, (1-p)/p}`-valued ratio
sequence and suppose that every window of `L ≥ 1` consecutive sites inside `[0,K)` contains a site
with `f = (1-p)/p`.  Then the truncated tail is at most `1 + L·p/(2p-1)` at every starting site. -/
theorem GS_le_of_no_long_run {f : ℕ → ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (hf0 : ∀ u, 0 ≤ f u) (hf1 : ∀ u, f u ≤ 1)
    (hval : ∀ u, f u = 1 ∨ f u = (1 - p) / p)
    {L : ℕ} (hL : 1 ≤ L) {K : ℕ}
    (hwin : ∀ a, a + L ≤ K → ∃ j, j < L ∧ f (a + j) = (1 - p) / p) :
    ∀ x, GS f x K ≤ (L : ℝ) * Kp p := by
  have hc0 : (0 : ℝ) ≤ (L : ℝ) * Kp p := by
    have := Kp_pos hp
    positivity
  have hLc : (L : ℝ) ≤ (L : ℝ) * Kp p := by
    have h1 := one_le_Kp hp hp1
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    nlinarith
  have hα0 : (0 : ℝ) ≤ (1 - p) / p := alpha_nonneg hp hp1
  have hα1 : (1 - p) / p ≤ 1 := alpha_le_one hp hp1
  -- strong induction on the remaining length `K - x`
  have key : ∀ n x, K - x ≤ n → GS f x K ≤ (L : ℝ) * Kp p := by
    intro n
    induction n with
    | zero =>
      intro x hx
      have hxK : K ≤ x := by omega
      have hempty : Finset.Ico x K = ∅ := Finset.Ico_eq_empty (by omega)
      have hzero : GS f x K = 0 := by
        unfold GS
        rw [hempty]
        simp
      rw [hzero]
      exact hc0
    | succ n ih =>
      intro x hxn
      by_cases hxK : K ≤ x
      · have hempty : Finset.Ico x K = ∅ := Finset.Ico_eq_empty (by omega)
        have hzero : GS f x K = 0 := by
          unfold GS
          rw [hempty]
          simp
        rw [hzero]
        exact hc0
      push_neg at hxK
      by_cases hsmall : K - x ≤ L
      · -- crude bound: at most `K - x ≤ L` terms, each at most `1`
        refine le_trans (GS_card_terms hf0 hf1 x K) ?_
        have hcard : ((Finset.Ico x K).card : ℝ) = ((K - x : ℕ) : ℝ) := by
          rw [Nat.card_Ico]
        rw [hcard]
        have h1 : ((K - x : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hsmall
        linarith
      push Not at hsmall
      -- the first marked site in the window starting at `x+1`
      have hwindow : x + 1 + L ≤ K := by omega
      obtain ⟨j, hjL, hjf⟩ := hwin (x + 1) hwindow
      -- the first marked site exists and is `< L`
      have hfirst : ∃ j0, j0 < L ∧ f (x + 1 + j0) = (1 - p) / p
          ∧ ∀ i < j0, f (x + 1 + i) ≠ (1 - p) / p := by
        classical
        set P : ℕ → Prop := fun i => f (x + 1 + i) = (1 - p) / p with hP
        have hex : ∃ i, P i := ⟨j, hjf⟩
        refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
        exact lt_of_le_of_lt (Nat.find_min' hex hjf) hjL
      obtain ⟨j0, hj0L, hj0mark, hj0min⟩ := hfirst
      -- the sites `x+1, …, x+j0` are unmarked
      have hunmarked : ∀ u, x < u → u ≤ x + j0 → f u = 1 := by
        intro u h1 h2
        have hlt : u - x - 1 < j0 := by omega
        have hnot : ¬ (f (x + 1 + (u - x - 1)) = (1 - p) / p) := hj0min _ hlt
        rw [show x + 1 + (u - x - 1) = u by omega] at hnot
        rcases hval u with h | h
        · exact h
        · exact absurd h hnot
      have hxj0K : x + j0 ≤ K := by omega
      rw [GS_add_run j0 x hxj0K hunmarked]
      -- one contraction step at the marked site `x+j0+1`
      have hstep : x + j0 < K := by omega
      rw [GS_succ f hstep]
      have hj0mark' : f (x + j0 + 1) = (1 - p) / p := by
        have heq : x + 1 + j0 = x + j0 + 1 := by omega
        rw [← heq]
        exact hj0mark
      rw [hj0mark']
      -- the induction hypothesis at `x + j0 + 1`
      have hIH : GS f (x + j0 + 1) K ≤ (L : ℝ) * Kp p :=
        ih (x + j0 + 1) (by omega)
      have hGSnn : 0 ≤ GS f (x + j0 + 1) K := GS_nonneg hf0 _ _
      have hmul : ((1 - p) / p) * GS f (x + j0 + 1) K ≤ ((1 - p) / p) * ((L : ℝ) * Kp p) :=
        mul_le_mul_of_nonneg_left hIH hα0
      rw [alpha_mul_Kp_mul hp] at hmul
      have hj0cast : ((j0 : ℝ) + 1 ≤ (L : ℝ)) := by
        have : j0 + 1 ≤ L := by omega
        exact_mod_cast this
      nlinarith [hmul, hj0cast]
  intro x
  exact key (K - x) x le_rfl

end SwarmSmom4
