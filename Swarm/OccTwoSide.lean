/-
  **Fidelity audit of the occupation chain, and the repair of a concrete missing
  ingredient: the two-sided (paper `(Vdrift)`) to one-sided (`OccupationPieces`)
  transfer.**

  `main_1d_revised.tex` proves the occupation estimate from a one-step
  drift inequality for the *two-sided* indicator.  In the paper's notation
  (`(Vdrift)`, and in the formal files `Zdrift.lean`/`Vdrift.lean`
  `Fcorr_coin_drift`, whose `ind` is `SwarmOcc.occInd`):

      E[Z_{n+1} - Z_n + J_{n+1} | F_n] >= 1{0 <= X^i_n <= M^j_n} - eps.

  Consequently the summed inequality `SwarmOcc.sum_drift_bound` — and hence
  `SwarmOcc.occbnd_one_eighth` — concerns the two-sided count
  `occTwo u v n = #{t < n : 0 <= u t <= v t}`.

  `SwarmHosc.OccupationPieces` instead demands the drift inequality with the
  **one-sided** count `SwarmSpeed.occ u v n = #{t < n : u t <= v t}`, which is what
  `SwarmSpeed.speed_lower_bound` consumes.  The two differ exactly on the times with
  `u t < 0`, and the difference is *not* absorbable by the drift budget: at a negative
  position the paper's own one-step bound is `2 alpha - 1 >= 0`, never `>= 1`.  So
  `(Vdrift)` cannot yield the one-sided form, and the four components
  `(Vdrift)`, `(Vbound)`, `(Jbound)`, `Q_n/n -> 0` — even all together — do not imply
  `OccupationPieces` as it is currently stated.  `twoSided_not_oneSided` below is a
  machine-checked witness of that mismatch.

  This file supplies the paper's own repair, which uses transience: both walkers are
  eventually nonnegative (Lemma `transience`, formalised as
  `SwarmBad.ae_transience_actual`), so the number of negative visits is eventually
  constant and the gap between the two counts is a bound `K(omega) < infinity` that the
  paper absorbs into the eventual onset (`n_0` is "absorbed in the o(n) term").  The
  lemmas below perform that absorption with explicit constants:

  * `occ_le_occTwo_add` : `occ u v n <= occTwo u v n + negCount u n`;
  * `negCount_le_of_eventually_nonneg` : `u` eventually `>= 0` after `N` implies
    `negCount u n <= N` for every `n`;
  * `occbnd_slack` / `occbnd_slack_one_eighth` : the final summation of
    `OccAssemble.lean` with the additive correction `K` and the constant
    `max 0 (K - Z 0)` in place of `max 0 (-(Z 0))`;
  * `occbnd_of_twoSided` : the paper's two-sided drift inequality plus the three
    two-sided bounds give exactly the shape `Occ n <= 2 M_n + n/8` consumed by
    `SwarmSpeed.speed_lower_bound`.

  Everything here is deterministic: no probability, no filtration and no walker count
  is mentioned, so no constant depends on `N`.
-/
import Swarm.Imports
import Swarm.Speed
import Swarm.OccAssemble

open Finset Filter
open scoped BigOperators Topology

namespace SwarmOccTwo

/-! ### The two occupation counts -/

/-- The number of times `t < n` at which `u t < 0`, as a real number. -/
noncomputable def negCount (u : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, if u t < 0 then (1 : ℝ) else 0

/-- The paper's two-sided occupation count `#{t < n : 0 <= u t <= v t}`. -/
noncomputable def occTwo (u v : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, SwarmOcc.occInd u v t

lemma negCount_nonneg (u : ℕ → ℤ) (n : ℕ) : 0 ≤ negCount u n :=
  Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num

lemma negCount_mono (u : ℕ → ℤ) : Monotone (negCount u) := by
  intro m n hmn
  unfold negCount
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmn)
    (fun t _ _ => by split_ifs <;> norm_num)

lemma occTwo_nonneg (u v : ℕ → ℤ) (n : ℕ) : 0 ≤ occTwo u v n :=
  Finset.sum_nonneg fun t _ => SwarmOcc.occInd_nonneg u v t

/-! ### The two-sided/one-sided comparison -/

/-- Termwise: the one-sided indicator is dominated by the two-sided indicator plus the
"negative position" indicator.  For `u t < 0` the right side is `1`; for `0 <= u t` the
two indicators agree. -/
lemma ind_le_occInd_add (u v : ℕ → ℤ) (t : ℕ) :
    (if u t ≤ v t then (1 : ℝ) else 0) ≤
      SwarmOcc.occInd u v t + (if u t < 0 then 1 else 0) := by
  unfold SwarmOcc.occInd
  by_cases h : u t < 0
  · rw [if_pos h]
    split_ifs <;> norm_num
  · rw [if_neg h]
    have h0 : 0 ≤ u t := not_lt.mp h
    by_cases h2 : u t ≤ v t
    · rw [if_pos h2, if_pos ⟨h0, h2⟩]; norm_num
    · rw [if_neg h2, if_neg]; norm_num
      tauto

/-- **The one-sided count is the two-sided count plus at most the negative visits.** -/
theorem occ_le_occTwo_add (u v : ℕ → ℤ) (n : ℕ) :
    SwarmSpeed.occ u v n ≤ occTwo u v n + negCount u n := by
  unfold SwarmSpeed.occ occTwo negCount
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun t _ => ind_le_occInd_add u v t

/-- **Bounded negative visits.**  If `u` is nonnegative from time `N` on, then before any
time `n` there are at most `N` negative visits.  This is the quantitative form of "both
positions are eventually nonnegative" used in the paper. -/
theorem negCount_le_of_eventually_nonneg {u : ℕ → ℤ} {N : ℕ}
    (h : ∀ t, N ≤ t → 0 ≤ u t) (n : ℕ) : negCount u n ≤ (N : ℝ) := by
  have hterm : ∀ t ∈ Finset.range n,
      (if u t < 0 then (1 : ℝ) else 0) ≤ (if t < N then (1 : ℝ) else 0) := by
    intro t _
    by_cases hneg : u t < 0
    · have htN : t < N := Nat.lt_of_not_le fun hN => absurd (h t hN) (not_le.mpr hneg)
      rw [if_pos hneg, if_pos htN]
    · rw [if_neg hneg]
      split_ifs <;> norm_num
  have hsum : negCount u n ≤
      ∑ t ∈ Finset.range n, (if t < N then (1 : ℝ) else 0) :=
    Finset.sum_le_sum hterm
  have hcard : ∑ t ∈ Finset.range n, (if t < N then (1 : ℝ) else 0) =
      (((Finset.range n).filter (fun t => t < N)).card : ℝ) := by
    rw [Finset.sum_boole]
  have hle : ((Finset.range n).filter (fun t => t < N)).card ≤ N := by
    have hsub : (Finset.range n).filter (fun t => t < N) ⊆ Finset.range N := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
      exact ht.2
    calc ((Finset.range n).filter (fun t => t < N)).card
        ≤ (Finset.range N).card := Finset.card_le_card hsub
      _ = N := Finset.card_range N
  calc negCount u n ≤ ∑ t ∈ Finset.range n, (if t < N then (1 : ℝ) else 0) := hsum
    _ = (((Finset.range n).filter (fun t => t < N)).card : ℝ) := hcard
    _ ≤ (N : ℝ) := by exact_mod_cast hle

/-- **The mismatch is genuine.**  There is a pair of `ℤ`-paths for which the two-sided
drift inequality `occTwo <= eps n + Z - Z 0 + J - Q` holds with `Z = J = Q = 0` and
`eps = 1/64`, while the one-sided count violates the *same* budget already at `n = 1`.
So no choice of the drift/potential/martingale components can replace the
negative-visit correction: transience, or the equivalent eventual-nonnegativity input,
is indispensable. -/
theorem twoSided_not_oneSided :
    ∃ u v : ℕ → ℤ,
      (∀ n, occTwo u v n ≤ (1 / 64 : ℝ) * n) ∧
        ¬ (∀ n, SwarmSpeed.occ u v n ≤ (1 / 64 : ℝ) * n) := by
  refine ⟨fun t => -(((t : ℕ) : ℤ) + 1), fun _ => 0, ?_, ?_⟩
  · intro n
    have hzero : ∀ t ∈ Finset.range n,
        SwarmOcc.occInd (fun t => -(((t : ℕ) : ℤ) + 1)) (fun _ => 0) t = 0 := by
      intro t _
      unfold SwarmOcc.occInd
      have hneg : ¬ (0 ≤ -(((t : ℕ) : ℤ) + 1)) := by
        have h2 : (0 : ℤ) ≤ ((t : ℕ) : ℤ) := Int.natCast_nonneg t
        intro hc
        linarith
      rw [if_neg (fun hc => hneg hc.1)]
    unfold occTwo
    rw [Finset.sum_eq_zero hzero]
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · intro h
    have h1 := h 1
    unfold SwarmSpeed.occ at h1
    have hsum : (∑ t ∈ Finset.range 1,
        (if -(((t : ℕ) : ℤ) + 1) ≤ 0 then (1 : ℝ) else 0)) = 1 := by
      simp
    rw [hsum] at h1
    norm_num at h1

/-! ### The final summation with an additive correction -/

/-- **`(occbnd)` final step, with a bounded additive correction `K`.**  This is
`SwarmOcc.occbnd_of_pieces` with `K` added to the drift inequality; the constant term of
the conclusion becomes `max 0 (K - Z 0)` instead of `max 0 (-(Z 0))`. -/
theorem occbnd_slack {Occ Z J Q M : ℕ → ℝ} {ε δ K : ℝ} {N : ℕ}
    (hdrift : ∀ n, Occ n ≤ ε * n + K + (Z n - Z 0) + J n - Q n)
    (hZ : ∀ n ≥ N, Z n ≤ M n + δ * n)
    (hJ : ∀ n ≥ N, J n ≤ M n + δ * n)
    (hQ : ∀ n ≥ N, -(δ * n) ≤ Q n) :
    ∀ n ≥ N, Occ n ≤ 2 * M n + (ε + 3 * δ) * n + max 0 (K - Z 0) := by
  intro n hn
  have h1 := hdrift n
  have h2 := hZ n hn
  have h3 := hJ n hn
  have h4 := hQ n hn
  have h5 : K - Z 0 ≤ max 0 (K - Z 0) := le_max_right _ _
  nlinarith

/-- **The paper's `eps = 1/8` shape with an additive correction.**  The drift inequality
runs with coefficient `1/64`, each of the three terms with budget `n/64`, and the
correction `max 0 (K - Z 0)` is absorbed at rate `n/64` from onset
`ceil (64 * max 0 (K - Z 0))` on. -/
theorem occbnd_slack_one_eighth {Occ Z J Q M : ℕ → ℝ} {N : ℕ} {K : ℝ}
    (hdrift : ∀ n, Occ n ≤ (1 / 64) * n + K + (Z n - Z 0) + J n - Q n)
    (hZ : ∀ n ≥ N, Z n ≤ M n + (1 / 64) * n)
    (hJ : ∀ n ≥ N, J n ≤ M n + (1 / 64) * n)
    (hQ : ∀ n ≥ N, -((1 / 64) * n) ≤ Q n) :
    ∀ n ≥ max N ⌈64 * max 0 (K - Z 0)⌉₊, Occ n ≤ 2 * M n + (1 / 8) * n := by
  intro n hn
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hK : max 0 (K - Z 0) ≤ (n : ℝ) / 64 := by
    have h1 : (⌈64 * max 0 (K - Z 0)⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hn
    have h2 : 64 * max 0 (K - Z 0) ≤ (⌈64 * max 0 (K - Z 0)⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have h := occbnd_slack (ε := 1 / 64) (δ := 1 / 64) (K := K) hdrift hZ hJ hQ n hN
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- **The paper's two-sided inputs imply the occupation estimate consumed by the covering
argument.**  `hdrift` is the summed two-sided `(Vdrift)` at `eps = 1/64` (the shape
produced by `SwarmOcc.sum_drift_bound`), `hZ`/`hJ`/`hQ` are the two-sided
`(Vbound)`/`(Jbound)`/`Q_n = o(n)` bounds with budget `n/64`, and `hneg` is the
eventual-nonnegativity output `negCount u n <= K` — which at the actual trajectory is
supplied by transience, with `K` the (random, finite) last negative time.  The conclusion
is exactly the hypothesis `hocc` of `SwarmSpeed.speed_lower_bound` with `C = 2`. -/
theorem occbnd_of_twoSided {u v : ℕ → ℤ} {Z J Q : ℕ → ℝ} {M : ℕ → ℝ} {N K : ℕ}
    (hdrift : ∀ n, occTwo u v n ≤ (1 / 64) * n + (Z n - Z 0) + J n - Q n)
    (hneg : ∀ n, negCount u n ≤ (K : ℝ))
    (hZ : ∀ n ≥ N, Z n ≤ M n + (1 / 64) * n)
    (hJ : ∀ n ≥ N, J n ≤ M n + (1 / 64) * n)
    (hQ : ∀ n ≥ N, -((1 / 64) * n) ≤ Q n) :
    ∀ n ≥ max N ⌈64 * max 0 ((K : ℝ) - Z 0)⌉₊,
      SwarmSpeed.occ u v n ≤ 2 * M n + (1 / 8) * n := by
  refine occbnd_slack_one_eighth (K := (K : ℝ)) (fun n => ?_) hZ hJ hQ
  have h1 := occ_le_occTwo_add u v n
  have h2 := hdrift n
  have h3 := hneg n
  linarith

/-- The same statement with `M` instantiated at the running maximum of `u`, i.e. literally
`(occbnd)` for a pair of `ℤ`-paths. -/
theorem occbnd_of_twoSided_runMax {u v : ℕ → ℤ} {Z J Q : ℕ → ℝ} {N K : ℕ}
    (hdrift : ∀ n, occTwo u (SwarmSpeed.runMax v) n ≤ (1 / 64) * n + (Z n - Z 0) + J n - Q n)
    (hneg : ∀ n, negCount u n ≤ (K : ℝ))
    (hZ : ∀ n ≥ N, Z n ≤ (SwarmSpeed.runMax u n : ℝ) + (1 / 64) * n)
    (hJ : ∀ n ≥ N, J n ≤ (SwarmSpeed.runMax u n : ℝ) + (1 / 64) * n)
    (hQ : ∀ n ≥ N, -((1 / 64) * n) ≤ Q n) :
    ∀ n ≥ max N ⌈64 * max 0 ((K : ℝ) - Z 0)⌉₊,
      SwarmSpeed.occ u (SwarmSpeed.runMax v) n
        ≤ 2 * (SwarmSpeed.runMax u n : ℝ) + (1 / 8) * n :=
  occbnd_of_twoSided (v := SwarmSpeed.runMax v) (M := fun n => (SwarmSpeed.runMax u n : ℝ))
    hdrift hneg hZ hJ hQ


/-! ### Composable forms: arbitrary constants, and the paper's per-step `(Vdrift)` -/

/-- **The transfer with arbitrary constants.**  The two-sided drift inequality with
coefficient `ε` and the three bounds with budget `δ n` produce the one-sided estimate
`Occ n <= 2 M_n + (ε + 3 δ) n + max 0 (K - Z 0)`.  Any `(ε, δ)` produced by the drift,
potential, record-cost and martingale components can be plugged in here. -/
theorem occbnd_of_twoSided_general {u v : ℕ → ℤ} {Z J Q M : ℕ → ℝ} {ε δ : ℝ}
    {N Knat : ℕ}
    (hdrift : ∀ n, occTwo u v n ≤ ε * n + (Z n - Z 0) + J n - Q n)
    (hneg : ∀ n, negCount u n ≤ (Knat : ℝ))
    (hZ : ∀ n ≥ N, Z n ≤ M n + δ * n)
    (hJ : ∀ n ≥ N, J n ≤ M n + δ * n)
    (hQ : ∀ n ≥ N, -(δ * n) ≤ Q n) :
    ∀ n ≥ N, SwarmSpeed.occ u v n ≤ 2 * M n + (ε + 3 * δ) * n + max 0 ((Knat : ℝ) - Z 0) := by
  have hdrift' : ∀ n, SwarmSpeed.occ u v n ≤ ε * n + (Knat : ℝ) + (Z n - Z 0) + J n - Q n := by
    intro n
    have h1 := occ_le_occTwo_add u v n
    have h2 := hdrift n
    have h3 := hneg n
    linarith
  exact occbnd_slack hdrift' hZ hJ hQ

/-- **The paper's route in one theorem.**  The per-step two-sided drift `(Vdrift)`
(`SwarmOcc.occInd u v t - eps <= E t`), the definition of the compensator
`Q_n = Z_n - Z_0 + sum_{t<n} J_{t+1} - sum_{t<n} E_t`, the bounded negative visits, and the
two-sided `(Vbound)`, `(Jbound)`, `Q_n = o(n)` bounds give the one-sided occupation estimate.
The summation of `(Vdrift)` is `SwarmOcc.sum_drift_bound`; the only addition is the
negative-visit correction, which is what the currently stated `OccupationPieces` is missing. -/
theorem occbnd_of_Vdrift {u v : ℕ → ℤ} {Z E J Q M : ℕ → ℝ} {ε δ : ℝ} {N Knat : ℕ}
    (hE : ∀ t, SwarmOcc.occInd u v t - ε ≤ E t)
    (hQdef : ∀ n, Q n = Z n - Z 0 + (∑ t ∈ Finset.range n, J (t + 1))
      - (∑ t ∈ Finset.range n, E t))
    (hneg : ∀ n, negCount u n ≤ (Knat : ℝ))
    (hZ : ∀ n ≥ N, Z n ≤ M n + δ * n)
    (hJ : ∀ n ≥ N, (∑ t ∈ Finset.range n, J (t + 1)) ≤ M n + δ * n)
    (hQ : ∀ n ≥ N, -(δ * n) ≤ Q n) :
    ∀ n ≥ N, SwarmSpeed.occ u v n ≤ 2 * M n + (ε + 3 * δ) * n + max 0 ((Knat : ℝ) - Z 0) := by
  refine occbnd_of_twoSided_general (J := fun n => ∑ t ∈ Finset.range n, J (t + 1))
    (fun n => ?_) hneg hZ hJ hQ
  exact SwarmOcc.sum_drift_bound hE hQdef n


/-! ### Consistency: when the walk never goes negative the two counts agree -/

/-- If `u` is nonnegative everywhere then there are no negative visits. -/
lemma negCount_eq_zero_of_nonneg {u : ℕ → ℤ} (h : ∀ t, 0 ≤ u t) (n : ℕ) :
    negCount u n = 0 := by
  unfold negCount
  refine Finset.sum_eq_zero fun t _ => ?_
  have h1 : ¬ u t < 0 := not_lt.mpr (h t)
  rw [if_neg h1]

/-- If `u` is nonnegative everywhere then the one- and two-sided occupation counts coincide;
so every statement in this file specialises to the existing `OccAssemble.lean` chain. -/
lemma occTwo_eq_occ_of_nonneg {u v : ℕ → ℤ} (h : ∀ t, 0 ≤ u t) (n : ℕ) :
    occTwo u v n = SwarmSpeed.occ u v n := by
  unfold occTwo SwarmSpeed.occ
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold SwarmOcc.occInd
  by_cases hle : u t ≤ v t
  · rw [if_pos hle, if_pos ⟨h t, hle⟩]
  · rw [if_neg hle, if_neg (fun hc => hle hc.2)]

/-- **No regression.**  If `u` never goes negative, the drift inequality may be assumed
directly for the one-sided count, and the conclusion is the paper's `(occbnd)` shape with the
onset `ceil (64 * max 0 (-(Z 0)))` of `occbnd_slack_one_eighth`. -/
theorem occbnd_of_oneSided {u v : ℕ → ℤ}
    {Z J Q M : ℕ → ℝ} {N : ℕ}
    (hdrift : ∀ n, SwarmSpeed.occ u v n ≤ (1 / 64) * n + (Z n - Z 0) + J n - Q n)
    (hZ : ∀ n ≥ N, Z n ≤ M n + (1 / 64) * n)
    (hJ : ∀ n ≥ N, J n ≤ M n + (1 / 64) * n)
    (hQ : ∀ n ≥ N, -((1 / 64) * n) ≤ Q n) :
    ∀ n ≥ max N ⌈64 * max 0 (-(Z 0))⌉₊, SwarmSpeed.occ u v n ≤ 2 * M n + (1 / 8) * n := by
  have hdrift' : ∀ n, SwarmSpeed.occ u v n
      ≤ (1 / 64) * n + (0 : ℝ) + (Z n - Z 0) + J n - Q n := by
    intro n
    have h := hdrift n
    linarith
  have h := occbnd_slack_one_eighth (Occ := fun n => SwarmSpeed.occ u v n) (K := (0 : ℝ))
    hdrift' hZ hJ hQ
  simpa using h

/-- **The two-sided hypothesis collapses to the existing chain when `u >= 0` everywhere.** -/
theorem occbnd_of_twoSided_nonneg {u v : ℕ → ℤ} (hpos : ∀ t, 0 ≤ u t)
    {Z J Q M : ℕ → ℝ} {N : ℕ}
    (hdrift : ∀ n, occTwo u v n ≤ (1 / 64) * n + (Z n - Z 0) + J n - Q n)
    (hZ : ∀ n ≥ N, Z n ≤ M n + (1 / 64) * n)
    (hJ : ∀ n ≥ N, J n ≤ M n + (1 / 64) * n)
    (hQ : ∀ n ≥ N, -((1 / 64) * n) ≤ Q n) :
    ∀ n ≥ max N ⌈64 * max 0 (-(Z 0))⌉₊, SwarmSpeed.occ u v n ≤ 2 * M n + (1 / 8) * n :=
  occbnd_of_oneSided (u := u) (v := v) (fun n => by
      rw [← occTwo_eq_occ_of_nonneg hpos n]; exact hdrift n) hZ hJ hQ


/-! ### Sharp obstruction: the four-piece form itself needs eventual nonnegativity -/

/-- The strictly negative path `u t = -(t + 1)`, whose one-sided occupation count against the
zero path is `n` while its running maximum is `-1`. -/
def negPath (t : ℕ) : ℤ := -(((t : ℕ) : ℤ) + 1)

lemma negPath_nonpos (t : ℕ) : negPath t ≤ 0 := by
  have h2 : (0 : ℤ) ≤ ((t : ℕ) : ℤ) := Int.natCast_nonneg t
  unfold negPath
  linarith

lemma negPath_le_neg_one (t : ℕ) : negPath t ≤ -1 := by
  have h2 : (0 : ℤ) ≤ ((t : ℕ) : ℤ) := Int.natCast_nonneg t
  unfold negPath
  linarith

lemma runMax_negPath (n : ℕ) : SwarmSpeed.runMax negPath n = -1 := by
  refine le_antisymm ?_ ?_
  · exact SwarmSpeed.runMax_le (fun t _ => negPath_le_neg_one t)
  · have h := SwarmSpeed.le_runMax (u := negPath) (t := 0) (n := n) (Nat.zero_le n)
    simpa [negPath] using h

lemma occ_negPath_zero (n : ℕ) : SwarmSpeed.occ negPath (fun _ => 0) n = (n : ℝ) := by
  have hterm : ∀ t ∈ Finset.range n,
      (if negPath t ≤ (fun _ => 0) t then (1 : ℝ) else 0) = 1 := by
    intro t _
    rw [if_pos (negPath_nonpos t)]
  unfold SwarmSpeed.occ
  rw [Finset.sum_congr rfl hterm]
  simp

/-- **The four-piece input is unsatisfiable on a path with bounded running maximum and a
positive density of negative visits.**  There are no real sequences `Z`, `J`, `Q` and no onset
`N` for which the one-sided drift inequality at `eps = 1/32` and the three bounds `(Vbound)`,
`(Jbound)`, `Q >= -n/64` all hold for the path `negPath` against the zero path.

Since the `Z`/`J`/`Q` components are free here, this is not a defect of a particular choice of
potential: the four pieces as they are currently stated in `SwarmHosc.OccupationPieces`
implicitly require that the walker's negative visits are eventually bounded, which is exactly
the input that transience supplies.  `SwarmBad.ae_transience_actual` supplies it for the actual
trajectory, and `OccTwoSide.lean`'s main theorems use it at the exact place it is needed. -/
theorem not_pieces_of_negative_walk :
    ¬ ∃ (Z J Q : ℕ → ℝ) (N : ℕ),
      (∀ n, SwarmSpeed.occ negPath (fun _ => 0) n
          ≤ (1 / 32) * n + (Z n - Z 0) + J n - Q n) ∧
      (∀ n ≥ N, Z n ≤ (SwarmSpeed.runMax negPath n : ℝ) + (1 / 64) * n) ∧
      (∀ n ≥ N, J n ≤ (SwarmSpeed.runMax negPath n : ℝ) + (1 / 64) * n) ∧
      (∀ n ≥ N, -((1 / 64) * n) ≤ Q n) := by
  rintro ⟨Z, J, Q, N, h1, h2, h3, h4⟩
  have hbnd : ∀ n ≥ N, SwarmSpeed.occ negPath (fun _ => 0) n
      ≤ 2 * (SwarmSpeed.runMax negPath n : ℝ) + (1 / 32 + 3 * (1 / 64)) * n
        + max 0 (-(Z 0)) :=
    SwarmOcc.occbnd_of_pieces (ε := 1 / 32) (δ := 1 / 64)
      (M := fun n => (SwarmSpeed.runMax negPath n : ℝ)) h1 h2 h3 h4
  obtain ⟨n, hn⟩ := exists_nat_gt ((64 / 59 : ℝ) * (max 0 (-(Z 0)) + 2))
  set n' : ℕ := max n (max N 1) with hn'
  have hnle : n ≤ n' := by rw [hn']; exact le_max_left n (max N 1)
  have hN : N ≤ n' := by
    rw [hn']
    exact le_trans (le_max_left N 1) (le_max_right n (max N 1))
  have hnr : ((64 / 59 : ℝ) * (max 0 (-(Z 0)) + 2)) < (n' : ℝ) :=
    lt_of_lt_of_le hn (by exact_mod_cast hnle)
  have hkey := hbnd n' hN
  rw [occ_negPath_zero, runMax_negPath] at hkey
  have hC : max 0 (-(Z 0)) + 2 < (59 / 64 : ℝ) * (n' : ℝ) := by
    have := mul_lt_mul_of_pos_left hnr (by norm_num : (0 : ℝ) < 59 / 64)
    have heq : (59 / 64 : ℝ) * ((64 / 59 : ℝ) * (max 0 (-(Z 0)) + 2)) =
        max 0 (-(Z 0)) + 2 := by
      field_simp
    linarith [this, heq]
  have hcast : (0 : ℝ) ≤ (n' : ℝ) := Nat.cast_nonneg n'
  nlinarith [hkey, hC]

end SwarmOccTwo
