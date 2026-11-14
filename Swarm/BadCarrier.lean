/-
  **The paper's bad-time event and the local-time revealed-weight carrier.**

  In `main_1d_revised.tex` (proof of Lemma `transience`), for a deterministic time
  `s`, integers `0 <= b0 < b1`, and walkers `i != j`, the argument is carried out on the event

      {X_s^i = b1, M_s^j >= b1 + 1},                                          (bad)

  and uses the sentence *"On this event, the variables `omega_j(x)` for `b0 < x <= b1` are
  `F_s`-measurable by (reveal)"*.  The verified deterministic revelation
  `Swarming.Trajectory.reveal_runMax` (`Swarm/Reveal.lean`) says that for `0 <= x`

      {M_s^j >= x + 1} ∩ {B_j(x) = 1}  ⊆  {L_s^j(x) >= m}.                    (carrier)

  This file makes the relation between (bad) and (carrier) exact.  It proves

  * `carrier_of_badPos`, `badPos_subset_forall_carrier`: (bad) implies (carrier) at *every*
    marked site `x` of the window `[0, b1]`, because `x <= b1` gives `x + 1 <= b1 + 1 <= M_s^j`;
  * `runMax_ge_of_carrier`: the carrier alone yields only `M_s^j >= x` (the walker has stood at
    `x`), i.e. it is exactly one level short of the running-maximum condition of (bad);
  * `revealedWeight`: the *revealed* weight at time `s`, namely `p` if the site mark is already
    determined at time `s` and the site is marked, and the safe fallback `1/2` otherwise
    (`revealedWeight_eq_half_or_p`, `one_half_le_revealedWeight`, `revealedWeight_le_p`).
    Determination is certified by the gate `m <= L_s^j(x)`: `L_s^j(x)` counts the visit at
    time `s` itself, whose departure has not been read, so `m` visits are needed to be sure
    that the coordinates `(j,x,k)`, `1 <= k <= m - 1`, have been consulted
    (`siteMark_coords_read`);
  * `revealedWeight_eq_omegaAt_iff`: the exact characterisation
    `revealedWeight = omega_j(x)` iff the mark of `x`, if present, has been revealed by time
    `s`; and `revealedWeight_eq_omegaAt_of_badPos`: **on (bad)** the revealed weight coincides
    with the paper's environment value `omega_j(x)` on the whole window `0 <= x <= b1`.  The
    proof is exactly the paper's use of (reveal): a marked site of the window has already been
    visited `m` times, so its mark is determined by time `s`;
  * `revealedWeight_le_rightProbability_of_badPos`: consequently, on (bad), the time-`s`
    revealed weight is dominated by walker `i`'s actual right probability at *every* later
    time `t >= s` and every site of the window interior `b0 < y <= b1`.  This is the
    window-wide domination that the conditional crossing estimate consumes;
  * `revealedWeight_stable`, `revealedWeight_eq_omegaAt_mono_time`,
    `revealedWeight_eq_omegaAt_of_badPos_le`: the revealed environment is *revealed once and
    for all* — once a mark is determined it stays determined and keeps contributing `p`, so the
    weights revealed at time `s` remain the environment on the window at every later time;
  * `badPos_iff_visit`, `carrier_of_visit`: for a unit-step walker started at `0` the
    running-maximum hypothesis `M_s^j >= b1+1` is *equivalent* to walker `j` having passed
    through the top level `b1+1` by time `s`; so `(bad)` is exactly "walker `i` sits at `b1` and
    walker `j` has already been above `b1`", and that passage alone reveals the window;
  * `revealedWeight_ne_omegaAt_of_not_bad` and `carrier_not_imp_runMax` (`Gaps.lean`): the two
    genuine gaps.  Off (bad) the revealed weight is *not* the environment (a marked site that
    walker `j` has not yet reached is weighted `1/2` rather than `p`), and the per-site
    local-time carrier (carrier) does *not* imply the running-maximum condition `x + 1 <= M_s^j`.
    So replacing the running-maximum event (bad) by the local-time carrier would be a genuine
    error: the carrier is a per-site statement, while the crossing estimate needs the *range*
    of sites `y < M_t^j` at all times `t >= s`.

  Nothing here is a filtration or conditional-expectation statement.  In particular the
  `F_s`-measurability of `revealedWeight` for a genuine time-`s` σ-algebra is **not** claimed:
  what is proved is `revealedWeight_congr`, that the revealed weight is a function of the
  trajectory state at time `s` and of the finitely many departure coordinates
  `U^j(x,k)`, `1 <= k <= m - 1`, `x` in the window.  Turning that into adaptedness needs the
  used-coordinate σ-algebra of the path filtration, which is separate work.
-/
import Swarm.Imports
import Swarm.Reveal

namespace Swarming.Trajectory

open Swarming Swarming.Model Swarming.Uniform
open Finset

noncomputable section

/-! ### The bad-time event and the carrier -/

/-- The paper's running-maximum bad-time event `{X_s^i = b1, M_s^j >= b1+1}`: walker `i` sits at
the top level `b1` of the crossing window while walker `j`'s running maximum has already reached
`b1 + 1`.  (The formalisation `SwarmRate.badTime` additionally carries a `hitBefore` conjunct;
it is not needed for the environment-revelation step and is dropped here.) -/
def badPos {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i j : Fin N) (b1 : ℤ) (s : ℕ) : Prop :=
  (trajectory p m U s).pos i = b1 ∧ b1 + 1 ≤ runMax p m U j s

/-- The local-time carrier of (reveal): walker `j` has already visited `x` at least `m` times
by time `s`. -/
def localTimeCarrier {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (s : ℕ) (x : ℤ) : Prop :=
  m ≤ (trajectory p m U s).ell j x

/-- **The revealed weight at time `s`.**  The paper's environment value `omega_j(x)` is `p` at a
marked site and `1/2` elsewhere.  At time `s` the mark of `x` is *known* only once the departure
coordinates `(j, x, k)`, `1 <= k <= m - 1`, have been consulted, which the gate `m <= L_s^j(x)`
certifies: `L_s^j(x)` counts the visit at time `s` itself, whose departure is read only at the
jump out of `s`, so `m - 1` visits do **not** suffice (`Gaps.gate_off_by_one`).  The revealed
weight uses the mark when the gate passes and the safe fallback `1/2` otherwise; by
`siteMark_coords_read` the gate places every coordinate of the mark at a departure strictly
before `s`, and by `revealedWeight_congr` the weight is a function of time-`s` data.  The gate is
sound but conservative: on the binding event of the crossing estimate it holds by
`carrier_of_badPos`, so nothing is lost where the weight is actually used, and the milder gate
`m - 1 <= L_s^j(x)` is certified by `siteMark_coords_read_of_ne` in every configuration except
the one where walker `j` still stands at `x` (`Gaps.gate_off_by_one`). -/
def revealedWeight {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (s : ℕ) (x : ℤ) : ℝ := by
  classical
  exact if m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x then p else 1 / 2

/-! ### The gate `m <= L_s^j(x)` certifies that the site mark has been read

`L_s^j(x)` counts the visits to `x` at times `0, ..., s`, including the visit at time `s`; the
departure from that visit is read only at the jump `s -> s+1`.  Hence the visit count certifies
one departure fewer than it counts, and the correct gate for "the mark `B_j(x)`, which needs the
departures `1, ..., m-1`, is known" is `m <= L_s^j(x)`.  The lemmas below make this precise: the
`k`-th visit exists whenever `k <= L_s^j(x)`, and for `k < L_s^j(x)` the coordinate `(j, x, k)`
is consulted at a departure time *strictly before* `s`. -/

/-- **Visit numbering.**  If `1 <= k <= L_n^j(x)`, walker `j`'s `k`-th visit to `x` occurs at some
time `t <= n`, and at that time the local time at `x` is exactly `k`. -/
theorem exists_visit_ell_eq {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℤ) (n : ℕ) :
    ∀ {k : ℕ}, 1 ≤ k → k ≤ (trajectory p m U n).ell j x →
      ∃ t ≤ n, (trajectory p m U t).pos j = x ∧ (trajectory p m U t).ell j x = k := by
  induction n with
  | zero =>
      intro k hk1 hk
      have hpos0 : (trajectory p m U 0).pos j = 0 := by
        rw [trajectory_zero]
        rfl
      have hell0 : (trajectory p m U 0).ell j x = if x = 0 then 1 else 0 := by
        rw [trajectory_zero]
        simp [initialWalkState]
      rw [hell0] at hk
      by_cases hx : x = 0
      · rw [if_pos hx] at hk
        refine ⟨0, le_rfl, ?_, ?_⟩
        · rw [hpos0, hx]
        · rw [hell0, if_pos hx]
          omega
      · rw [if_neg hx] at hk
        omega
  | succ n ih =>
      intro k hk1 hk
      by_cases hcase : k ≤ (trajectory p m U n).ell j x
      · obtain ⟨t, ht, hp, he⟩ := ih hk1 hcase
        exact ⟨t, le_trans ht (Nat.le_succ n), hp, he⟩
      · have hlt : (trajectory p m U n).ell j x < k := not_le.mp hcase
        have hell : (trajectory p m U (n + 1)).ell j x =
            (trajectory p m U n).ell j x +
              if x = (trajectory p m U (n + 1)).pos j then 1 else 0 := by
          rw [trajectory_succ, nextWalkState_ell, nextWalkState_pos]
        have hpos : (trajectory p m U (n + 1)).pos j = x := by
          by_contra hne
          rw [hell, if_neg (fun hc => hne hc.symm)] at hk
          omega
        refine ⟨n + 1, le_rfl, hpos, ?_⟩
        rw [hell, if_pos hpos.symm] at hk ⊢
        omega

/-- **Coordinates strictly below the visit count have been consulted.**  If `1 <= k < L_s^j(x)`
then the coordinate `(j, x, k)` is used at a departure occurring strictly before time `s`. -/
theorem exists_departure_lt_of_lt_ell {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) {s : ℕ}
    {x : ℤ} {k : ℕ} (hk1 : 1 ≤ k) (hk : k < (trajectory p m U s).ell j x) :
    ∃ t < s, departureCoord p m U t j = (j, x, k) := by
  obtain ⟨t, ht, hpos, hell⟩ := exists_visit_ell_eq p m U j x s hk1 (le_of_lt hk)
  have hts : t < s := by
    rcases lt_or_eq_of_le ht with h | h
    · exact h
    · exfalso
      rw [← h, hell] at hk
      omega
  refine ⟨t, hts, ?_⟩
  rw [departureCoord, hpos, hell]

/-- **The corrected gate certifies revelation.**  If `m <= L_s^j(x)` then every coordinate
`(j, x, k)` of the site mark, `1 <= k <= m - 1`, has been consulted at a departure time strictly
before `s`.  This is the formal content of "the mark `B_j(x)` is determined by time `s`"; the gate
cannot be weakened to `m - 1 <= L_s^j(x)` (`Gaps.gate_off_by_one`). -/
theorem siteMark_coords_read {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (s : ℕ) (x : ℤ)
    (h : m ≤ (trajectory p m U s).ell j x) {k : ℕ} (hk : k ∈ Finset.Icc 1 (m - 1)) :
    ∃ t < s, departureCoord p m U t j = (j, x, k) := by
  rw [Finset.mem_Icc] at hk
  exact exists_departure_lt_of_lt_ell p m U j hk.1 (by omega)

/-- **Coordinates at or below the visit count, when the walker has left the site.**  If walker
`j` is not at `x` at time `s` and `1 <= k <= L_s^j(x)`, then the coordinate `(j, x, k)` is
consulted at a departure strictly before `s`: the `k`-th visit to `x` ended before `s`. -/
theorem exists_departure_lt_of_le_ell_of_ne {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N)
    {s : ℕ} {x : ℤ} {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ (trajectory p m U s).ell j x)
    (hne : (trajectory p m U s).pos j ≠ x) :
    ∃ t < s, departureCoord p m U t j = (j, x, k) := by
  obtain ⟨t, ht, hpos, hell⟩ := exists_visit_ell_eq p m U j x s hk1 hk
  have hts : t < s := by
    rcases lt_or_eq_of_le ht with h | h
    · exact h
    · exfalso
      exact hne (h ▸ hpos)
  refine ⟨t, hts, ?_⟩
  rw [departureCoord, hpos, hell]

/-- **The weaker gate is exactly the case where the walker still stands at the site.**  If
`m - 1 <= L_s^j(x)` and walker `j` is *not* at `x` at time `s`, then every coordinate
`(j, x, k)`, `1 <= k <= m - 1`, of the site mark has been consulted strictly before `s`.  So the
gate `m - 1 <= L_s^j(x)` certifies revelation in every configuration except the one where the
walker still occupies `x` — which is exactly the configuration in which it fails
(`Gaps.gate_off_by_one`: `s = 0`, `x = 0`, `m = 2`, `L_0^j(0) = 1`, walker at `0`). -/
theorem siteMark_coords_read_of_ne {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (s : ℕ)
    (x : ℤ) (h : m - 1 ≤ (trajectory p m U s).ell j x)
    (hne : (trajectory p m U s).pos j ≠ x) {k : ℕ} (hk : k ∈ Finset.Icc 1 (m - 1)) :
    ∃ t < s, departureCoord p m U t j = (j, x, k) := by
  rw [Finset.mem_Icc] at hk
  exact exists_departure_lt_of_le_ell_of_ne p m U j hk.1 (le_trans hk.2 h) hne

/-! ### Elementary monotonicity of the running maximum -/

/-- The running maximum is monotone in time. -/
theorem runMax_mono {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) {s t : ℕ} (hst : s ≤ t) :
    runMax p m U j s ≤ runMax p m U j t := by
  have hsub : Finset.range (s + 1) ⊆ Finset.range (t + 1) :=
    Finset.range_subset_range.mpr (Nat.succ_le_succ hst)
  have h := Finset.sup'_mono (f := fun a : ℕ => (trajectory p m U a).pos j) hsub
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos s)⟩
  exact h

/-- Unfolding equation for the running maximum. -/
theorem runMax_eq_sup' {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    runMax p m U j n = (Finset.range (n + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩ (fun t => (trajectory p m U t).pos j) := rfl

/-! ### (bad) implies the local-time carrier on the whole window -/

/-- **The paper's use of (reveal) on the bad-time event.**  On `{X_s^i = b1, M_s^j >= b1+1}`
every marked site `x` with `0 <= x <= b1` has already been visited `m` times by walker `j` at
time `s`: the hypothesis `x + 1 <= M_s^j` of `reveal_runMax` follows from `x <= b1`. -/
theorem carrier_of_badPos {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) {U : Array N} {i j : Fin N}
    {b1 : ℤ} {s : ℕ} (hbad : badPos p m U i j b1 s) {x : ℤ}
    (hx0 : 0 ≤ x) (hxb : x ≤ b1) (hmark : SiteMark p m U j x) :
    localTimeCarrier p m U j s x := by
  have hmax : x + 1 ≤ runMax p m U j s := by
    have := hbad.2
    omega
  have h := reveal_runMax hp m U j hx0 hmark hmax
  rw [localTimeCarrier, ell_eq_localTime p m U s j x]
  exact h

/-- Set form of `carrier_of_badPos`: `{bad} ∩ {B_j(x) = 1} ⊆ {L_s^j(x) >= m}` on the window. -/
theorem badPos_inter_mark_subset_carrier {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    {i j : Fin N} {b1 : ℤ} {s : ℕ} {x : ℤ} (hx0 : 0 ≤ x) :
    {U : Array N | badPos p m U i j b1 s ∧ x ≤ b1 ∧ SiteMark p m U j x}
      ⊆ {U : Array N | localTimeCarrier p m U j s x} := by
  rintro U ⟨hbad, hxb, hmark⟩
  exact carrier_of_badPos hp m hbad hx0 hxb hmark

/-- **The window form**: on the bad-time event all marked window sites are carried at once. -/
theorem badPos_subset_forall_carrier {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) {i j : Fin N}
    {b1 : ℤ} {s : ℕ} :
    {U : Array N | badPos p m U i j b1 s} ⊆
      {U : Array N | ∀ x : ℤ, 0 ≤ x → x ≤ b1 → SiteMark p m U j x →
        localTimeCarrier p m U j s x} := by
  intro U hbad x hx0 hxb hmark
  exact carrier_of_badPos hp m hbad hx0 hxb hmark

/-! ### The revealed weight -/

theorem revealedWeight_eq_p {N : ℕ} {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N} {s : ℕ} {x : ℤ}
    (h : m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x) :
    revealedWeight p m U j s x = p := by
  classical
  rw [revealedWeight, if_pos h]

theorem revealedWeight_eq_half {N : ℕ} {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N} {s : ℕ} {x : ℤ}
    (h : ¬ (m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x)) :
    revealedWeight p m U j s x = 1 / 2 := by
  classical
  rw [revealedWeight, if_neg h]

/-- A site that walker `j` has visited fewer than `m` times is weighted `1/2`, whatever the
array does: the mark is not yet known. -/
theorem revealedWeight_eq_half_of_lt {N : ℕ} {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N}
    {s : ℕ} {x : ℤ} (h : (trajectory p m U s).ell j x < m) :
    revealedWeight p m U j s x = 1 / 2 :=
  revealedWeight_eq_half (fun hc => absurd hc.1 (not_le.mpr h))

/-- The revealed weight takes only the two values `1/2` and `p`. -/
theorem revealedWeight_eq_half_or_p {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (s : ℕ)
    (x : ℤ) : revealedWeight p m U j s x = 1 / 2 ∨ revealedWeight p m U j s x = p := by
  classical
  by_cases h : m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x
  · exact Or.inr (revealedWeight_eq_p h)
  · exact Or.inl (revealedWeight_eq_half h)

/-- The revealed weight is always at least `1/2`; at an unmarked or not-yet-revealed site the
fallback `1/2` is thus a valid lower bound for the right probability, which is always `>= 1/2`. -/
theorem one_half_le_revealedWeight {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (U : Array N)
    (j : Fin N) (s : ℕ) (x : ℤ) : 1 / 2 ≤ revealedWeight p m U j s x := by
  rcases revealedWeight_eq_half_or_p p m U j s x with h | h
  · rw [h]
  · rw [h]
    exact hp

/-- The revealed weight never exceeds the excitation probability `p`. -/
theorem revealedWeight_le_p {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) (U : Array N) (j : Fin N)
    (s : ℕ) (x : ℤ) : revealedWeight p m U j s x ≤ p := by
  rcases revealedWeight_eq_half_or_p p m U j s x with h | h
  · rw [h]
    exact hp
  · rw [h]

/-- **Exact characterisation of where the revealed weight is the environment.**  The revealed
weight at `(s, x)` equals the paper's `omega_j(x)` if and only if the mark of `x`, when it is
present, has already been revealed by time `s`.  In particular every marked site that walker `j`
has already reached `m` times is identified correctly, and the bad-time event supplies exactly
this condition on the whole window. -/
theorem revealedWeight_eq_omegaAt_iff {N : ℕ} {p : ℝ} (hp : 1 / 2 < p) (m : ℕ) (U : Array N)
    (j : Fin N) (s : ℕ) (x : ℤ) :
    revealedWeight p m U j s x = omegaAt p m U j x ↔
      (SiteMark p m U j x → m ≤ (trajectory p m U s).ell j x) := by
  classical
  constructor
  · intro heq hmark
    by_contra hlt
    have h1 : revealedWeight p m U j s x = 1 / 2 :=
      revealedWeight_eq_half (fun hc => hlt hc.1)
    have h2 : omegaAt p m U j x = p := by rw [omegaAt, if_pos hmark]
    rw [h1, h2] at heq
    linarith
  · intro h
    by_cases hmark : SiteMark p m U j x
    · rw [revealedWeight_eq_p ⟨h hmark, hmark⟩, omegaAt, if_pos hmark]
    · rw [revealedWeight_eq_half (fun hc => hmark hc.2), omegaAt, if_neg hmark]

/-- **The revealed weight at time `s` is a lower bound for the right probability at sites whose
mark is already revealed.**  If the mark at walker `i`'s position at time `t` has been revealed
by time `s`, and that position is nonnegative and strictly below walker `j`'s running maximum,
then the time-`s` revealed weight dominates walker `i`'s right probability there.  This is the
pointwise counterpart of `revealedWeight_le_rightProbability_of_badPos`; the running-maximum
hypothesis is still needed, which is exactly what (bad) supplies on the whole window. -/
theorem revealedWeight_le_rightProbability_of_revealed {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    {U : Array N} {i j : Fin N} (hij : i ≠ j) {s t : ℕ}
    (hrev : SiteMark p m U j ((trajectory p m U t).pos i) →
      m ≤ (trajectory p m U s).ell j ((trajectory p m U t).pos i))
    (hx0 : 0 ≤ (trajectory p m U t).pos i)
    (hdom : (trajectory p m U t).pos i < runMax p m U j t) :
    revealedWeight p m U j s ((trajectory p m U t).pos i) ≤
      rightProbability p m (trajectory p m U t).ell i ((trajectory p m U t).pos i) := by
  classical
  by_cases hmark : SiteMark p m U j ((trajectory p m U t).pos i)
  · have homega : omegaAt p m U j ((trajectory p m U t).pos i) = p := by
      rw [omegaAt, if_pos hmark]
    have hd := dominate hp m U hij t hx0 hdom
    rw [homega] at hd
    rwa [revealedWeight_eq_p ⟨hrev hmark, hmark⟩]
  · rw [revealedWeight_eq_half (fun hc => hmark hc.2)]
    exact one_half_le_rightProbability hp m _ i _

/-- **The paper's `F_s`-measurability sentence, in pointwise form.**  On the bad-time event the
revealed weight *is* the paper's environment value `omega_j(x)` for every site of the window
`0 <= x <= b1`.  The proof uses `carrier_of_badPos`, i.e. `reveal_runMax`: a marked window site
has been visited `m` times, which is exactly the gate `m <= L_s^j(x)`. -/
theorem revealedWeight_eq_omegaAt_of_badPos {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    {U : Array N} {i j : Fin N} {b1 : ℤ} {s : ℕ} (hbad : badPos p m U i j b1 s) {x : ℤ}
    (hx0 : 0 ≤ x) (hxb : x ≤ b1) :
    revealedWeight p m U j s x = omegaAt p m U j x := by
  classical
  by_cases hmark : SiteMark p m U j x
  · have hc := carrier_of_badPos hp m hbad hx0 hxb hmark
    rw [revealedWeight_eq_p ⟨hc, hmark⟩, omegaAt, if_pos hmark]
  · rw [revealedWeight_eq_half (fun hc => hmark hc.2), omegaAt, if_neg hmark]

/-- The window form of `revealedWeight_eq_omegaAt_of_badPos`: on the bad-time event the revealed
weight sequence agrees with the environment on all of `[0, b1]`. -/
theorem forall_revealedWeight_eq_omegaAt_of_badPos {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    {U : Array N} {i j : Fin N} {b1 : ℤ} {s : ℕ} (hbad : badPos p m U i j b1 s) :
    ∀ x : ℤ, 0 ≤ x → x ≤ b1 → revealedWeight p m U j s x = omegaAt p m U j x :=
  fun x hx0 hxb => revealedWeight_eq_omegaAt_of_badPos hp m hbad (x := x) hx0 hxb

/-! ### The window-wide domination consumed by the crossing estimate -/

/-- **The revealed weight dominates the actual right probability on the window, at all later
times.**  On the bad-time event and for `t >= s`, a site `y` of the window interior
`b0 < y <= b1` satisfies the hypothesis `0 <= y < M_t^j` of the paper's (dominate) — because
`y <= b1 < b1 + 1 <= M_s^j <= M_t^j` — so the revealed weight revealed at time `s` is a valid
lower bound for walker `i`'s actual right probability at time `t`, uniformly in `t >= s`.

This is precisely the deterministic content of the paper's *"the variables `omega_j(x)` for
`b0 < x <= b1` are `F_s`-measurable"*: the weight used for the crossing estimate in the window
is the one revealed at time `s`, and it dominates at every later time. -/
theorem revealedWeight_le_rightProbability_of_badPos {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    {U : Array N} {i j : Fin N} (hij : i ≠ j) {b1 : ℤ} {s : ℕ}
    (hbad : badPos p m U i j b1 s) {t : ℕ} (hst : s ≤ t) {b0 : ℤ} (hb0 : 0 ≤ b0)
    (hy0 : b0 < (trajectory p m U t).pos i) (hyb : (trajectory p m U t).pos i ≤ b1) :
    revealedWeight p m U j s ((trajectory p m U t).pos i) ≤
      rightProbability p m (trajectory p m U t).ell i ((trajectory p m U t).pos i) := by
  have hx0 : 0 ≤ (trajectory p m U t).pos i := le_trans hb0 (le_of_lt hy0)
  have hrun : (trajectory p m U t).pos i < runMax p m U j t := by
    have h1 : runMax p m U j s ≤ runMax p m U j t := runMax_mono p m U j hst
    have h2 : b1 + 1 ≤ runMax p m U j s := hbad.2
    have h3 : (trajectory p m U t).pos i ≤ b1 := hyb
    omega
  rw [revealedWeight_eq_omegaAt_of_badPos hp m hbad hx0 hyb]
  exact dominate hp m U hij t hx0 hrun

/-- The domination in the form the crossing estimate uses: on the bad-time event, the revealed
weight is a deterministic lower bound for the conditional right-jump probability of the *whole*
window interior, at once. -/
theorem forall_revealedWeight_le_rightProbability_of_badPos {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p)
    (m : ℕ) {U : Array N} {i j : Fin N} (hij : i ≠ j) {b1 : ℤ} {s : ℕ}
    (hbad : badPos p m U i j b1 s) {b0 : ℤ} (hb0 : 0 ≤ b0) :
    ∀ t : ℕ, s ≤ t → ∀ y : ℤ, b0 < y → y ≤ b1 → y = (trajectory p m U t).pos i →
      revealedWeight p m U j s y ≤ rightProbability p m (trajectory p m U t).ell i y := by
  intro t hst y hy0 hyb hy
  subst hy
  exact revealedWeight_le_rightProbability_of_badPos hp m hij hbad hst hb0 hy0 hyb

/-! ### The revealed environment is revealed once and for all -/

/-- Local times of the actual trajectory are monotone in time. -/
theorem ell_mono_time {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℤ) {s t : ℕ}
    (hst : s ≤ t) : (trajectory p m U s).ell j x ≤ (trajectory p m U t).ell j x := by
  rw [ell_eq_localTime p m U s j x, ell_eq_localTime p m U t j x]
  exact localTime_mono (fun k => (trajectory p m U k).pos j) hst x

/-- The local-time carrier grows with time. -/
theorem localTimeCarrier_mono {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℤ)
    {s t : ℕ} (hst : s ≤ t) (h : localTimeCarrier p m U j s x) :
    localTimeCarrier p m U j t x :=
  le_trans h (ell_mono_time p m U j x hst)

/-- **A mark that has been revealed stays revealed.**  If the gate `m <= L_s^j(x)` holds at time
`s` and the site is marked, then the revealed weight is `p` at `s` and at every later time: it
does not oscillate once determined. -/
theorem revealedWeight_stable {N : ℕ} {p : ℝ} {m : ℕ} {U : Array N} {j : Fin N} {s t : ℕ}
    {x : ℤ} (hst : s ≤ t)
    (h : m ≤ (trajectory p m U s).ell j x ∧ SiteMark p m U j x) :
    revealedWeight p m U j t x = p :=
  revealedWeight_eq_p ⟨le_trans h.1 (ell_mono_time p m U j x hst), h.2⟩

/-- **The set of sites where the revealed weight is the environment only grows in time.** -/
theorem revealedWeight_eq_omegaAt_mono_time {N : ℕ} {p : ℝ} (hp : 1 / 2 < p) (m : ℕ) (U : Array N)
    (j : Fin N) {s t : ℕ} (hst : s ≤ t) (x : ℤ)
    (h : revealedWeight p m U j s x = omegaAt p m U j x) :
    revealedWeight p m U j t x = omegaAt p m U j x := by
  rw [revealedWeight_eq_omegaAt_iff hp] at h ⊢
  intro hmark
  exact le_trans (h hmark) (ell_mono_time p m U j x hst)

/-- **The revealed environment of the bad-time event is stable for all later times.**  On
`{X_s^i = b1, M_s^j >= b1+1}` the revealed weight equals the paper's environment `omega_j(x)`
on the window `[0, b1]` at time `s` (`revealedWeight_eq_omegaAt_of_badPos`) *and* at every later
time `t >= s`.  This is what allows the time-`s` revealed weights to serve as the fixed
environment for the crossing estimate over the whole future of the window. -/
theorem revealedWeight_eq_omegaAt_of_badPos_le {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ)
    {U : Array N} {i j : Fin N} {b1 : ℤ} {s : ℕ} (hbad : badPos p m U i j b1 s) {t : ℕ}
    (hst : s ≤ t) {x : ℤ} (hx0 : 0 ≤ x) (hxb : x ≤ b1) :
    revealedWeight p m U j t x = omegaAt p m U j x := by
  classical
  by_cases hmark : SiteMark p m U j x
  · have hc : localTimeCarrier p m U j s x := carrier_of_badPos hp m hbad hx0 hxb hmark
    have hmono := localTimeCarrier_mono p m U j x hst hc
    rw [localTimeCarrier] at hmono
    rw [revealedWeight_eq_p ⟨hmono, hmark⟩, omegaAt, if_pos hmark]
  · rw [revealedWeight_eq_half (fun hc => hmark hc.2), omegaAt, if_neg hmark]

/-! ### The running-maximum condition is a passage through the top of the window

The bad-time event carries the hypothesis `M_s^j >= b1 + 1`.  For a unit-step walker started at
`0` this is *exactly* the statement that walker `j` has already passed through the level `b1 + 1`
of the window: it is the other walker's passage through the top of the window, and not the
per-site local-time carrier, that reveals the marks of the window. -/

/-- **Unit steps of the actual trajectory.**  Every step moves walker `j` by exactly one. -/
theorem pos_succ_eq_add_one_or_sub_one {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N)
    (n : ℕ) :
    (trajectory p m U (n + 1)).pos j = (trajectory p m U n).pos j + 1 ∨
      (trajectory p m U (n + 1)).pos j + 1 = (trajectory p m U n).pos j := by
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  by_cases h : U (j, (trajectory p m U n).pos j,
      (trajectory p m U n).ell j ((trajectory p m U n).pos j))
      ≤ rightProbability p m (trajectory p m U n).ell j ((trajectory p m U n).pos j)
  · rw [drivenStep_eq_one_of_le h]
    omega
  · rw [drivenStep_eq_neg_one_of_not_le h]
    omega

/-- **Discrete intermediate value along the actual trajectory.**  Walker `j` starts at `0` and
moves by unit steps; hence, if it is at or above a nonnegative level `z` at time `n`, it stands
exactly at `z` at some time `t <= n`. -/
theorem exists_pos_eq_of_le {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (n : ℕ) :
    ∀ {z : ℤ}, 0 ≤ z → z ≤ (trajectory p m U n).pos j →
      ∃ t ≤ n, (trajectory p m U t).pos j = z := by
  induction n with
  | zero =>
      intro z hz0 hz
      refine ⟨0, le_rfl, ?_⟩
      have h0 : (trajectory p m U 0).pos j = 0 := by
        rw [trajectory_zero]
        rfl
      omega
  | succ n ih =>
      intro z hz0 hz
      by_cases hcase : z ≤ (trajectory p m U n).pos j
      · obtain ⟨t, ht, hpe⟩ := ih hz0 hcase
        exact ⟨t, le_trans ht (Nat.le_succ n), hpe⟩
      · have hlt : (trajectory p m U n).pos j < z := not_le.mp hcase
        rcases pos_succ_eq_add_one_or_sub_one p m U j n with hs | hs
        · refine ⟨n + 1, le_rfl, ?_⟩
          omega
        · omega

/-- Reaching the running maximum means standing at or above it at some time. -/
theorem exists_pos_eq_of_runMax_le {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) {s : ℕ}
    {z : ℤ} (hz0 : 0 ≤ z) (h : z ≤ runMax p m U j s) :
    ∃ t ≤ s, (trajectory p m U t).pos j = z := by
  obtain ⟨t, ht, hte⟩ := exists_eq_runMax p m U j s
  have hz : z ≤ (trajectory p m U t).pos j := by
    rw [hte]
    exact h
  obtain ⟨t', ht', hpe⟩ := exists_pos_eq_of_le p m U j t hz0 hz
  exact ⟨t', le_trans ht' ht, hpe⟩

/-- Standing at a level puts it below the running maximum at every later time. -/
theorem le_runMax_of_pos_eq {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) {t s : ℕ}
    (hts : t ≤ s) {z : ℤ} (h : (trajectory p m U t).pos j = z) : z ≤ runMax p m U j s := by
  rw [← h]
  exact le_trans (le_runMax p m U j t) (runMax_mono p m U j hts)

/-- **The bad-time event in visit form.**  For `b1 >= -1` the running-maximum hypothesis
`M_s^j >= b1 + 1` is equivalent to walker `j` having passed through the top level `b1 + 1` of the
window at some time `t <= s`.  So the paper's event is exactly *"walker `i` sits at `b1` and
walker `j` has already been above `b1`"* — the passage, not the visit counts, is what reveals the
window. -/
theorem badPos_iff_visit {N : ℕ} (p : ℝ) (m : ℕ) (U : Array N) (i j : Fin N) {b1 : ℤ}
    (hb1 : -1 ≤ b1) (s : ℕ) :
    badPos p m U i j b1 s ↔
      (trajectory p m U s).pos i = b1 ∧ ∃ t ≤ s, (trajectory p m U t).pos j = b1 + 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, exists_pos_eq_of_runMax_le p m U j (by omega : (0 : ℤ) ≤ b1 + 1) h2⟩
  · rintro ⟨h1, t, ht, hpos⟩
    exact ⟨h1, le_runMax_of_pos_eq p m U j ht hpos⟩

/-- **The carrier from the passage through the top of the window.**  Walker `j`'s passage
through `b1 + 1` at some time `t <= s` reveals every marked site `x` of the window by time `s`,
without any reference to walker `i`. -/
theorem carrier_of_visit {N : ℕ} {p : ℝ} (hp : 1 / 2 ≤ p) (m : ℕ) {U : Array N} {j : Fin N}
    {b1 : ℤ} {s : ℕ} (hvisit : ∃ t ≤ s, (trajectory p m U t).pos j = b1 + 1) {x : ℤ}
    (hx0 : 0 ≤ x) (hxb : x ≤ b1) (hmark : SiteMark p m U j x) :
    localTimeCarrier p m U j s x := by
  have hmax : x + 1 ≤ runMax p m U j s := by
    obtain ⟨t, ht, hpos⟩ := hvisit
    have := le_runMax_of_pos_eq p m U j ht hpos
    omega
  have h := reveal_runMax hp m U j hx0 hmark hmax
  rw [localTimeCarrier, ell_eq_localTime p m U s j x]
  exact h

end

end Swarming.Trajectory


