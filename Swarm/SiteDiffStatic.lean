/-
  **The one-step group-weight update `siteDiff` of `Swarm/QVarBound.lean`,
  reduced to the paper's static objects `h_j` and `G_j`.**

  `Q_VARIANCE.md` records `(Mdiff)` as an open premise on the actual
  `siteDiff p m n I J hI U`.  This file proves the deterministic step of the paper's own
  argument (`main_1d_revised.tex`, proof of Proposition `group`, display (upd) and the
  subsequent bound) for the *actual* array:

  * §1 one-step local-time bookkeeping: `L` is nondecreasing in `n`, `wA` is nondecreasing in
    `n`, and the two values `1/2`, `p` are characterised by the threshold event;
  * §2 a site where `wA n Jᶜ` and `wA (n+1) Jᶜ` differ is occupied at time `n+1` by a walker
    of `Jᶜ` (`cross_site`);
  * §3 the exact one-site potential difference in the three possible cases, and the
    multi-site superposition bound `hfix_diff_le_prod` in product form (the paper's (upd)
    applied once per changed site, with the ratios of the *initial* weight);
  * §4 `siteDiff` on `(sep)` is bounded by `C(p) * N * (1 + max_{i∈I, x≤n+2} (h_i(x)+G_i(x)))^2`,
    where `h_i = hfix (omegaN i)` and `G_i` is the paper's static tail sum over the mark
    sequence of walker `i` only.  This is the `(Wdrift)` one-step size bound of the paper.

  No `sorry`, no custom axiom, no `native_decide`; §5 records the exact residual premise that
  turns the deterministic bound into `(Mdiff)`.
-/
import Swarm.QVarBound

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SwarmSiteDiff

open Classical

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup SepGroup.Model Cookie
open SwarmJointDrift SwarmQVariance

variable {N : ℕ}

/-! ### 1. One-step local-time bookkeeping -/

/-- The exact one-step local-time formula, in the notation of `SepGroup.Model`. -/
theorem L_succ (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) :
    L p m U (n + 1) i x = L p m U n i x + (if x = X p m U (n + 1) i then 1 else 0) := by
  rw [L_apply, L_apply, X_apply, trajectory_succ, nextWalkState_ell, nextWalkState_pos]

/-- Local times never decrease. -/
theorem L_le_succ (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) :
    L p m U n i x ≤ L p m U (n + 1) i x := by
  rw [L_succ]
  split_ifs <;> omega

/-- Total local time of a group never decreases. -/
theorem sumL_le_succ (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N)) (x : ℤ) :
    ∑ i ∈ A, L p m U n i x ≤ ∑ i ∈ A, L p m U (n + 1) i x :=
  Finset.sum_le_sum fun i _ => L_le_succ p m U n i x

/-- **(hmono) at the level of the weights**: `w_n^A ≤ w_{n+1}^A` pointwise. -/
theorem wA_le_succ (p : ℝ) (hp : 1 / 2 ≤ p) (m : ℕ) (U : Array N) (n : ℕ)
    (A : Finset (Fin N)) (x : ℕ) : wA p m U n A x ≤ wA p m U (n + 1) A x := by
  have hmono := sumL_le_succ p m U n A (x : ℤ)
  by_cases h : m ≤ ∑ i ∈ A, L p m U n i (x : ℤ)
  · have h2 : m ≤ ∑ i ∈ A, L p m U (n + 1) i (x : ℤ) := le_trans h hmono
    unfold wA
    rw [if_pos h, if_pos h2]
  · by_cases h2 : m ≤ ∑ i ∈ A, L p m U (n + 1) i (x : ℤ)
    · unfold wA
      rw [if_neg h, if_pos h2]
      linarith
    · unfold wA
      rw [if_neg h, if_neg h2]

/-- The weight is `1/2` exactly when the group local time is below the threshold. -/
theorem wA_eq_half_iff (p : ℝ) (hp : 1 / 2 < p) (m : ℕ) (U : Array N) (n : ℕ)
    (A : Finset (Fin N)) (x : ℕ) :
    wA p m U n A x = 1 / 2 ↔ ¬ (m ≤ ∑ i ∈ A, L p m U n i (x : ℤ)) := by
  unfold wA
  by_cases h : m ≤ ∑ i ∈ A, L p m U n i (x : ℤ)
  · rw [if_pos h]
    constructor
    · intro hh; linarith
    · intro hh; exact absurd h hh
  · rw [if_neg h]
    constructor
    · intro hh; exact h
    · intro hh; ring

/-- The weight is `p` exactly when the group local time reaches the threshold. -/
theorem wA_eq_p_iff (p : ℝ) (hp : 1 / 2 < p) (m : ℕ) (U : Array N) (n : ℕ)
    (A : Finset (Fin N)) (x : ℕ) :
    wA p m U n A x = p ↔ m ≤ ∑ i ∈ A, L p m U n i (x : ℤ) := by
  unfold wA
  by_cases h : m ≤ ∑ i ∈ A, L p m U n i (x : ℤ)
  · rw [if_pos h]
    constructor
    · intro hh; exact h
    · intro hh; ring
  · rw [if_neg h]
    constructor
    · intro hh; linarith
    · intro hh; exact absurd hh h

/-- **A changed site is occupied.**  If the group weight of `Jᶜ` changes between times `n` and
`n+1` at the site `u`, then some walker of `Jᶜ` sits at `u` at time `n+1`. -/
theorem cross_site (p : ℝ) (hp : 1 / 2 < p) (m : ℕ) (U : Array N) (n : ℕ)
    (J : Finset (Fin N)) (u : ℕ)
    (hu : wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u) :
    ∃ i ∈ Jᶜ, X p m U (n + 1) i = (u : ℤ) := by
  have hmono := sumL_le_succ p m U n Jᶜ (u : ℤ)
  have hlt : ¬ (m ≤ ∑ i ∈ Jᶜ, L p m U n i (u : ℤ)) := by
    intro h
    exact hu (by rw [wA_eq_p_iff p hp m U n Jᶜ u |>.2 h,
      wA_eq_p_iff p hp m U (n + 1) Jᶜ u |>.2 (le_trans h hmono)])
  have hge : m ≤ ∑ i ∈ Jᶜ, L p m U (n + 1) i (u : ℤ) := by
    by_contra h
    exact hu (by rw [wA_eq_half_iff p hp m U n Jᶜ u |>.2 hlt,
      wA_eq_half_iff p hp m U (n + 1) Jᶜ u |>.2 h])
  have hstrict : ∑ i ∈ Jᶜ, L p m U n i (u : ℤ) < ∑ i ∈ Jᶜ, L p m U (n + 1) i (u : ℤ) :=
    lt_of_lt_of_le (not_le.mp hlt) hge
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hle : ∑ i ∈ Jᶜ, L p m U (n + 1) i (u : ℤ) ≤ ∑ i ∈ Jᶜ, L p m U n i (u : ℤ) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have h := L_succ p m U n i (u : ℤ)
    have hne : (u : ℤ) ≠ X p m U (n + 1) i := by
      intro heq
      exact hno i hi heq.symm
    rw [h, if_neg hne, add_zero]
  omega

/-! ### 2. The potential difference caused by changing the weight at one site -/

/-- The backward ratio `(1-w)/w` of the recursion `hfix`; this is `Swarming.Update.ratio`. -/
noncomputable def rq (w : ℕ → ℝ) (v : ℕ) : ℝ := (1 - w v) / w v

theorem rq_eq_ratio (w : ℕ → ℝ) (v : ℕ) : rq w v = Swarming.Update.ratio w v := rfl

theorem rq_eq_one_of_half {w : ℕ → ℝ} {v : ℕ} (h : w v = 1 / 2) : rq w v = 1 := by
  rw [rq, h]; norm_num

theorem rq_eq_of_p {w : ℕ → ℝ} {p : ℝ} {v : ℕ} (h : w v = p) : rq w v = (1 - p) / p := by
  rw [rq, h]

theorem rq_nonneg {w : ℕ → ℝ} {v : ℕ} (h0 : 0 < w v) (h1 : w v ≤ 1) : 0 ≤ rq w v := by
  rw [rq]; exact div_nonneg (by linarith) (le_of_lt h0)

theorem one_le_hprev {w : ℕ → ℝ} (hw0 : ∀ u, 0 < w u) (hw1 : ∀ u, w u ≤ 1) (u : ℕ) :
    1 ≤ hprev w u := by
  cases u with
  | zero => simp
  | succ k => simpa using one_le_hfix w hw0 hw1 k

/-- `hfix` at a site of weight `p`, in the recursion form used by the paper. -/
theorem hfix_at_p {p : ℝ} (hp0 : p ≠ 0) {w : ℕ → ℝ} {u : ℕ} (h : w u = p) :
    hfix w u = 1 / p + ((1 - p) / p) * hprev w u := by
  rw [hfix_eq, h]
  field_simp

/-- Both weights `1/2` at the site: the difference of the potentials is unchanged. -/
theorem hfix_diff_half_half {w w' : ℕ → ℝ} {u : ℕ} (hw : w u = 1 / 2) (hw' : w' u = 1 / 2) :
    hfix w u - hfix w' u = hprev w u - hprev w' u := by
  rw [hfix_eq_two_add_hprev hw, hfix_eq_two_add_hprev hw']
  ring

/-- Both weights `p` at the site: the difference is contracted by `(1-p)/p`. -/
theorem hfix_diff_p_p {w w' : ℕ → ℝ} {p : ℝ} (hp0 : p ≠ 0) {u : ℕ}
    (hw : w u = p) (hw' : w' u = p) :
    hfix w u - hfix w' u = ((1 - p) / p) * (hprev w u - hprev w' u) := by
  rw [hfix_at_p hp0 hw, hfix_at_p hp0 hw']
  ring

/-- The paper's display (upd) at a single site: the weight rises from `1/2` to `p`. -/
theorem hfix_diff_half_p {w w' : ℕ → ℝ} {p : ℝ} (hp0 : p ≠ 0) {u : ℕ}
    (hw : w u = 1 / 2) (hw' : w' u = p) :
    hfix w u - hfix w' u
      = (hprev w u - hprev w' u) + ((2 * p - 1) / p) * (1 + hprev w' u) := by
  rw [hfix_eq_two_add_hprev hw, hfix_at_p hp0 hw']
  field_simp
  ring

/-- If two weights with values in `{1/2, p}` differ at a site and `w ≤ w'`, then `w = 1/2` and
`w' = p` there: the only possible change is a threshold crossing. -/
theorem cross_form {p : ℝ} (hp : 1 / 2 < p) {w w' : ℕ → ℝ} (hle : ∀ u, w u ≤ w' u)
    (hwv : ∀ u, w u = 1 / 2 ∨ w u = p) (hw'v : ∀ u, w' u = 1 / 2 ∨ w' u = p) {u : ℕ}
    (hne : w u ≠ w' u) : w u = 1 / 2 ∧ w' u = p := by
  rcases hwv u with h | h
  · rcases hw'v u with h' | h'
    · exact absurd (h.trans h'.symm) hne
    · exact ⟨h, h'⟩
  · rcases hw'v u with h' | h'
    · have hcontra := hle u
      rw [h, h'] at hcontra
      exact absurd hcontra (by linarith)
    · exact absurd (h.trans h'.symm) hne

/-- **The one-site step of the difference**, uniformly in the three possible cases. -/
theorem hfix_diff_step_le {p : ℝ} (hp : 1 / 2 < p) (hp0 : p ≠ 0) {w w' : ℕ → ℝ}
    (hw0 : ∀ u, 0 < w u) (hw1 : ∀ u, w u ≤ 1) (hw0' : ∀ u, 0 < w' u) (hw1' : ∀ u, w' u ≤ 1)
    (hle : ∀ u, w u ≤ w' u) (hwv : ∀ u, w u = 1 / 2 ∨ w u = p)
    (hw'v : ∀ u, w' u = 1 / 2 ∨ w' u = p) (u : ℕ) :
    hfix w u - hfix w' u ≤
      rq w u * (hprev w u - hprev w' u)
        + ((2 * p - 1) / p) * (if w u ≠ w' u then (1 + hprev w' u) else 0) := by
  have hpm : hprev w' u ≤ hprev w u := by
    rcases u with _ | k
    · simp
    · simpa using hfix_mono w w' hw0 hw1 hw0' hw1' hle k
  by_cases hne : w u = w' u
  · rw [if_neg (by simp [hne])]
    rcases hwv u with h | h
    · rw [hfix_diff_half_half h (hne.symm.trans h), rq_eq_one_of_half h]
      linarith
    · rw [hfix_diff_p_p hp0 h (hne.symm.trans h), rq_eq_of_p h]
      have hr : (1 - p) / p ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      nlinarith
  · obtain ⟨hw, hw'⟩ := cross_form hp hle hwv hw'v hne
    rw [hfix_diff_half_p hp0 hw hw', if_pos hne, rq_eq_one_of_half hw]
    linarith

/-- The right-hand side of the multi-site bound, as a function of the top site. -/
noncomputable def diffBound (p : ℝ) (w w' : ℕ → ℝ) (x : ℕ) : ℝ :=
  ((2 * p - 1) / p) * ∑ u ∈ Finset.range (x + 1),
    (if w u ≠ w' u then (1 + hprev w' u) * ∏ v ∈ Finset.Ico (u + 1) (x + 1), rq w v else 0)

theorem diffBound_nonneg {p : ℝ} (hp : 1 / 2 < p) {w w' : ℕ → ℝ}
    (hw0 : ∀ u, 0 < w u) (hw1 : ∀ u, w u ≤ 1) (hw0' : ∀ u, 0 < w' u) (hw1' : ∀ u, w' u ≤ 1)
    (x : ℕ) : 0 ≤ diffBound p w w' x := by
  have hc : 0 ≤ (2 * p - 1) / p := by
    apply div_nonneg <;> linarith
  refine mul_nonneg hc (Finset.sum_nonneg fun u _ => ?_)
  by_cases h : w u = w' u
  · rw [if_neg (by simp [h])]
  · rw [if_pos h]
    refine mul_nonneg (by linarith [one_le_hprev hw0' hw1' u]) (Finset.prod_nonneg fun v _ => ?_)
    exact rq_nonneg (hw0 v) (hw1 v)

/-- One step of `diffBound` at a site where the two weights agree. -/
theorem diffBound_mul_rq {p : ℝ} {w w' : ℕ → ℝ} {x : ℕ} (hx : w (x + 1) = w' (x + 1)) :
    diffBound p w w' x * rq w (x + 1) = diffBound p w w' (x + 1) := by
  have hterm : ∀ u ∈ Finset.range (x + 1),
      (if w u ≠ w' u then (1 + hprev w' u) * ∏ v ∈ Finset.Ico (u + 1) (x + 1), rq w v else 0)
        * rq w (x + 1)
      = (if w u ≠ w' u then (1 + hprev w' u) * ∏ v ∈ Finset.Ico (u + 1) (x + 1 + 1), rq w v
          else 0) := by
    intro u hu
    have hu' : u ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
    by_cases h : w u = w' u
    · rw [if_neg (by simp [h]), if_neg (by simp [h]), zero_mul]
    · rw [if_pos h, if_pos h, mul_assoc,
        ← Finset.prod_Ico_succ_top (a := u + 1) (b := x + 1) (Nat.add_le_add_right hu' 1)]
  have hmain : (∑ u ∈ Finset.range (x + 1),
      (if w u ≠ w' u then (1 + hprev w' u) * ∏ v ∈ Finset.Ico (u + 1) (x + 1), rq w v else 0))
        * rq w (x + 1)
      = ∑ u ∈ Finset.range (x + 1 + 1),
        (if w u ≠ w' u then (1 + hprev w' u) * ∏ v ∈ Finset.Ico (u + 1) (x + 1 + 1), rq w v
          else 0) := by
    rw [Finset.sum_mul, Finset.sum_congr rfl hterm]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [if_neg (by simp [hx]), add_zero]
  rw [diffBound, diffBound, mul_assoc, hmain]

/-- One step of `diffBound` at a site where the weight rises from `1/2` to `p`. -/
theorem diffBound_add_cross {p : ℝ} {w w' : ℕ → ℝ} {x : ℕ}
    (hx : w (x + 1) = 1 / 2) (hne : w (x + 1) ≠ w' (x + 1)) :
    diffBound p w w' x + ((2 * p - 1) / p) * (1 + hprev w' (x + 1))
      = diffBound p w w' (x + 1) := by
  have hterm : ∀ u ∈ Finset.range (x + 1),
      (if w u ≠ w' u then (1 + hprev w' u) * ∏ v ∈ Finset.Ico (u + 1) (x + 1), rq w v else 0)
      = (if w u ≠ w' u then (1 + hprev w' u) * ∏ v ∈ Finset.Ico (u + 1) (x + 1 + 1), rq w v
          else 0) := by
    intro u hu
    have hu' : u ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
    by_cases h : w u = w' u
    · rw [if_neg (by simp [h]), if_neg (by simp [h])]
    · rw [if_pos h, if_pos h,
        Finset.prod_Ico_succ_top (a := u + 1) (b := x + 1) (Nat.add_le_add_right hu' 1),
        rq_eq_one_of_half hx, mul_one]
  have hnew : (if w (x + 1) ≠ w' (x + 1) then
      (1 + hprev w' (x + 1)) * ∏ v ∈ Finset.Ico (x + 1 + 1) (x + 1 + 1), rq w v else 0)
      = (1 + hprev w' (x + 1)) := by
    rw [if_pos hne, Finset.Ico_self, Finset.prod_empty, mul_one]
  have hsum : ∑ u ∈ Finset.range (x + 1 + 1),
        (if w u ≠ w' u then (1 + hprev w' u) * ∏ v ∈ Finset.Ico (u + 1) (x + 1 + 1), rq w v
          else 0)
      = (∑ u ∈ Finset.range (x + 1),
          (if w u ≠ w' u then (1 + hprev w' u) * ∏ v ∈ Finset.Ico (u + 1) (x + 1), rq w v
            else 0)) + (1 + hprev w' (x + 1)) := by
    rw [Finset.sum_range_succ, hnew, ← Finset.sum_congr rfl hterm]
  rw [diffBound, diffBound, hsum]
  ring

/-- **Multi-site superposition bound**: applying (upd) once at every site where the group
weight changed, with the ratios of the *initial* weight, gives the bound below — the
paper's step from (upd) to the one-step size of `W`. -/
theorem hfix_diff_le_prod {p : ℝ} (hp : 1 / 2 < p) (hp0 : p ≠ 0) (hp1 : p ≤ 1)
    {w w' : ℕ → ℝ} (hw0 : ∀ u, 0 < w u) (hw1 : ∀ u, w u ≤ 1)
    (hw0' : ∀ u, 0 < w' u) (hw1' : ∀ u, w' u ≤ 1)
    (hwv : ∀ u, w u = 1 / 2 ∨ w u = p) (hw'v : ∀ u, w' u = 1 / 2 ∨ w' u = p)
    (hle : ∀ u, w u ≤ w' u) :
    ∀ x : ℕ, hfix w x - hfix w' x ≤ diffBound p w w' x := by
  intro x
  induction x with
  | zero =>
      rw [diffBound, Finset.sum_range_one]
      by_cases hne : w 0 = w' 0
      · have h : hfix w 0 = hfix w' 0 := by
          rw [hfix_eq, hfix_eq, hprev_zero, hprev_zero, hne]
        rw [h, if_neg (by simp [hne]), mul_zero]
        simp
      · obtain ⟨hw, hw'⟩ := cross_form hp hle hwv hw'v hne
        rw [hfix_diff_half_p hp0 hw hw', hprev_zero, hprev_zero, if_pos hne]
        norm_num
  | succ x ih =>
      have hstep := hfix_diff_step_le (p := p) hp hp0 hw0 hw1 hw0' hw1' hle hwv hw'v (x + 1)
      rw [hprev_succ, hprev_succ] at hstep
      have hrq : 0 ≤ rq w (x + 1) := rq_nonneg (hw0 (x + 1)) (hw1 (x + 1))
      have hmul := mul_le_mul_of_nonneg_left ih hrq
      by_cases hx : w (x + 1) = w' (x + 1)
      · rw [if_neg (by simp [hx])] at hstep
        have key : rq w (x + 1) * diffBound p w w' x = diffBound p w w' (x + 1) := by
          rw [mul_comm]
          exact diffBound_mul_rq (p := p) hx
        linarith
      · obtain ⟨hwh, _⟩ := cross_form hp hle hwv hw'v hx
        rw [if_pos hx] at hstep
        rw [rq_eq_one_of_half hwh, one_mul] at hmul hstep
        rw [one_mul] at hmul
        have key := diffBound_add_cross (p := p) (w := w) (w' := w') hwh hx
        rw [hprev_succ] at key
        linarith

/-! ### 3. The `Hfix` (not `hfix`) form: the paper's sum of partial products -/

/-- The inner sum of the paper's display (upd): `∑_{z=x}^{y-1} ∏_{u=x+1}^{z} (1-w(u))/w(u)`. -/
noncomputable def hSum (w : ℕ → ℝ) (u x : ℕ) : ℝ :=
  ∑ z ∈ Finset.Ico u x, ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq w v

theorem hSum_succ {w : ℕ → ℝ} {u x : ℕ} (hux : u ≤ x) :
    hSum w u (x + 1) = hSum w u x + ∏ v ∈ Finset.Ico (u + 1) (x + 1), rq w v := by
  unfold hSum
  rw [Finset.sum_Ico_succ_top hux]

/-- The `Hfix` form of the multi-site bound. -/
noncomputable def hBound (p : ℝ) (w w' : ℕ → ℝ) (x : ℕ) : ℝ :=
  ((2 * p - 1) / p) * ∑ u ∈ Finset.range (x + 1),
    (if w u ≠ w' u then (1 + hprev w' u) * hSum w u x else 0)

theorem hBound_succ {p : ℝ} {w w' : ℕ → ℝ} (x : ℕ) :
    hBound p w w' (x + 1) = hBound p w w' x + diffBound p w w' x := by
  have hterm : ∀ u ∈ Finset.range (x + 1),
      (if w u ≠ w' u then (1 + hprev w' u) * hSum w u (x + 1) else 0)
      = (if w u ≠ w' u then (1 + hprev w' u) * hSum w u x else 0)
        + (if w u ≠ w' u then (1 + hprev w' u) * ∏ v ∈ Finset.Ico (u + 1) (x + 1), rq w v
            else 0) := by
    intro u hu
    have hux : u ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
    by_cases h : w u = w' u
    · rw [if_neg (by simp [h]), if_neg (by simp [h]), if_neg (by simp [h]), add_zero]
    · rw [if_pos h, if_pos h, if_pos h, hSum_succ hux, mul_add]
  have hnew : (if w (x + 1) ≠ w' (x + 1) then (1 + hprev w' (x + 1)) * hSum w (x + 1) (x + 1)
      else 0) = 0 := by
    rw [hSum, Finset.Ico_self, Finset.sum_empty]
    by_cases h : w (x + 1) = w' (x + 1)
    · rw [if_neg (by simp [h])]
    · rw [if_pos h, mul_zero]
  have houter : (∑ u ∈ Finset.range (x + 1 + 1),
        (if w u ≠ w' u then (1 + hprev w' u) * hSum w u (x + 1) else 0))
      = ∑ u ∈ Finset.range (x + 1),
        (if w u ≠ w' u then (1 + hprev w' u) * hSum w u (x + 1) else 0) := by
    rw [Finset.sum_range_succ, hnew, add_zero]
  have hsplit : (∑ u ∈ Finset.range (x + 1),
        (if w u ≠ w' u then (1 + hprev w' u) * hSum w u (x + 1) else 0))
      = (∑ u ∈ Finset.range (x + 1),
          (if w u ≠ w' u then (1 + hprev w' u) * hSum w u x else 0))
        + (∑ u ∈ Finset.range (x + 1),
          (if w u ≠ w' u then (1 + hprev w' u) * ∏ v ∈ Finset.Ico (u + 1) (x + 1), rq w v
            else 0)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  unfold hBound diffBound
  rw [houter, hsplit]
  ring

/-- **The `Hfix` difference is bounded by the paper's static-shape expression.** -/
theorem Hfix_diff_le_hBound {p : ℝ} (hp : 1 / 2 < p) (hp0 : p ≠ 0) (hp1 : p ≤ 1)
    {w w' : ℕ → ℝ} (hw0 : ∀ u, 0 < w u) (hw1 : ∀ u, w u ≤ 1)
    (hw0' : ∀ u, 0 < w' u) (hw1' : ∀ u, w' u ≤ 1)
    (hwv : ∀ u, w u = 1 / 2 ∨ w u = p) (hw'v : ∀ u, w' u = 1 / 2 ∨ w' u = p)
    (hle : ∀ u, w u ≤ w' u) (x : ℕ) :
    Hfix w x - Hfix w' x ≤ hBound p w w' x := by
  induction x with
  | zero =>
      have h1 : hSum w 0 0 = 0 := by rw [hSum, Finset.Ico_self, Finset.sum_empty]
      simp [Hfix, hBound, h1]
  | succ x ih =>
      have h := hfix_diff_le_prod (p := p) hp hp0 hp1 hw0 hw1 hw0' hw1' hwv hw'v hle x
      rw [Hfix_succ, Hfix_succ, hBound_succ]
      linarith

/-! ### 4. The static objects `h_i` and `G_i` of the paper -/

/-- The paper's `G_j(x)`, truncated at `K`: `1 + ∑_{z=x}^{K-1} ∏_{u=x+1}^{z} (1-ω_j(u))/ω_j(u)`. -/
noncomputable def Gsum (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (x K : ℕ) : ℝ :=
  ∑ z ∈ Finset.Ico x K, ∏ v ∈ Finset.Ico (x + 1) (z + 1), rq (omegaN p m U i) v

noncomputable def Gtail (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (x K : ℕ) : ℝ :=
  1 + Gsum p m U i x K

theorem Gsum_nonneg {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (U : Array N)
    (i : Fin N) (x K : ℕ) : 0 ≤ Gsum p m U i x K := by
  refine Finset.sum_nonneg fun z _ => Finset.prod_nonneg fun v _ => ?_
  exact rq_nonneg (omegaAt_pos p m U hp i (v : ℤ)) (omegaAt_le_one p m U hp1 i (v : ℤ))

/-- The comparison of ratios: a smaller weight gives a larger ratio. -/
theorem rq_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : (1 - b) / b ≤ (1 - a) / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [div_le_div_iff₀ hb ha]
  nlinarith

theorem prod_rq_le {w v : ℕ → ℝ} (hw0 : ∀ u, 0 < w u) (hw1 : ∀ u, w u ≤ 1)
    (hv0 : ∀ u, 0 < v u) (s : Finset ℕ) (hle : ∀ u ∈ s, v u ≤ w u) :
    ∏ u ∈ s, rq w u ≤ ∏ u ∈ s, rq v u :=
  Finset.prod_le_prod (fun u _ => rq_nonneg (hw0 u) (hw1 u)) (fun u hu => rq_anti (hv0 u) (hle u hu))

theorem rq_le_one {w : ℕ → ℝ} {v : ℕ} (h0 : 0 < w v) (h1 : 1 / 2 ≤ w v) : rq w v ≤ 1 := by
  rw [rq, div_le_one h0]
  linarith

/-- The pointwise static comparison of the products below the running maximum. -/
theorem prod_rq_wA_le_omega {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {J : Finset (Fin N)} {i : Fin N} {u z R : ℕ} (hz : z < R)
    (hcomp : ∀ v : ℕ, v < R → omegaN p m U i v ≤ wA p m U n Jᶜ v) :
    (∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (wA p m U n Jᶜ) v)
      ≤ ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (omegaN p m U i) v :=
  prod_rq_le (fun v => wA_pos p m U (le_of_lt hp) n Jᶜ v) (fun v => wA_le_one p m U hp1 n Jᶜ v)
    (fun v => omegaAt_pos p m U (le_of_lt hp) i (v : ℤ)) _
    (fun v hv => hcomp v (lt_of_lt_of_le (Finset.mem_Ico.mp hv).2 hz))

/-- The part of the inner sum up to `R`, compared with the static sum. -/
theorem hSum_le_Gsum {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {J : Finset (Fin N)} {i : Fin N} {u R K : ℕ} (hRK : R ≤ K)
    (hcomp : ∀ v : ℕ, v < R → omegaN p m U i v ≤ wA p m U n Jᶜ v) :
    hSum (wA p m U n Jᶜ) u R ≤ Gsum p m U i u K := by
  have hstep : hSum (wA p m U n Jᶜ) u R
      ≤ ∑ z ∈ Finset.Ico u R, ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (omegaN p m U i) v := by
    unfold hSum
    exact Finset.sum_le_sum fun z hz => prod_rq_wA_le_omega hp hp1 (Finset.mem_Ico.mp hz).2 hcomp
  have hsub : Finset.Ico u R ⊆ Finset.Ico u K := Finset.Ico_subset_Ico_right hRK
  have hext : (∑ z ∈ Finset.Ico u R, ∏ v ∈ Finset.Ico (u + 1) (z + 1), rq (omegaN p m U i) v)
      ≤ Gsum p m U i u K := by
    unfold Gsum
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ =>
      Finset.prod_nonneg fun v _ => rq_nonneg (omegaAt_pos p m U (le_of_lt hp) i (v : ℤ))
        (omegaAt_le_one p m U hp1 i (v : ℤ))
  linarith

/-- The last possible term of the inner sum, compared with the static sum. -/
theorem prod_succ_le_Gsum {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {J : Finset (Fin N)} {i : Fin N} {u R K : ℕ} (huR : u < R) (hK : R + 1 ≤ K)
    (hcomp : ∀ v : ℕ, v < R → omegaN p m U i v ≤ wA p m U n Jᶜ v) :
    (∏ v ∈ Finset.Ico (u + 1) (R + 1), rq (wA p m U n Jᶜ) v) ≤ Gsum p m U i u K := by
  rw [Finset.prod_Ico_succ_top (by omega) (f := fun v => rq (wA p m U n Jᶜ) v)]
  have h1 : rq (wA p m U n Jᶜ) R ≤ 1 :=
    rq_le_one (wA_pos p m U (le_of_lt hp) n Jᶜ R) (one_half_le_wA p m U (le_of_lt hp) n Jᶜ R)
  have h2 : (∏ v ∈ Finset.Ico (u + 1) R, rq (wA p m U n Jᶜ) v)
      ≤ ∏ v ∈ Finset.Ico (u + 1) R, rq (omegaN p m U i) v := by
    refine prod_rq_le (fun v => wA_pos p m U (le_of_lt hp) n Jᶜ v)
      (fun v => wA_le_one p m U hp1 n Jᶜ v)
      (fun v => omegaAt_pos p m U (le_of_lt hp) i (v : ℤ)) _ (fun v hv => ?_)
    exact hcomp v (Finset.mem_Ico.mp hv).2
  have h3 : (∏ v ∈ Finset.Ico (u + 1) R, rq (omegaN p m U i) v) * 1 ≤ Gsum p m U i u K := by
    rw [mul_one]
    have hR1 : R = (R - 1) + 1 := by omega
    rw [hR1]
    unfold Gsum
    refine Finset.single_le_sum (f := fun z => ∏ v ∈ Finset.Ico (u + 1) (z + 1),
      rq (omegaN p m U i) v) (fun z _ => Finset.prod_nonneg fun v _ =>
      rq_nonneg (omegaAt_pos p m U (le_of_lt hp) i (v : ℤ))
        (omegaAt_le_one p m U hp1 i (v : ℤ))) ?_
    refine Finset.mem_Ico.mpr ⟨by omega, ?_⟩
    omega
  calc (∏ v ∈ Finset.Ico (u + 1) R, rq (wA p m U n Jᶜ) v) * rq (wA p m U n Jᶜ) R
      ≤ (∏ v ∈ Finset.Ico (u + 1) R, rq (wA p m U n Jᶜ) v) * 1 := by
        exact mul_le_mul_of_nonneg_left h1 (Finset.prod_nonneg fun v _ =>
          rq_nonneg (wA_pos p m U (le_of_lt hp) n Jᶜ v) (wA_le_one p m U hp1 n Jᶜ v))
    _ ≤ (∏ v ∈ Finset.Ico (u + 1) R, rq (omegaN p m U i) v) * 1 := by
        exact mul_le_mul_of_nonneg_right h2 (by norm_num)
    _ ≤ Gsum p m U i u K := h3

/-- **The static comparison of the inner sums.**  Below the running maximum `R = M_n^{i}` the
group weight dominates the mark weight `ω_i`, so every ratio can be replaced by the static one;
above `R` only one factor is lost, which is the factor `2` of the paper. -/
theorem hSum_le_two_Gtail {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {J : Finset (Fin N)} {i : Fin N} {u x R K : ℕ}
    (huR : u ≤ R) (hxR : x ≤ R + 1)
    (hcomp : ∀ v : ℕ, v < R → omegaN p m U i v ≤ wA p m U n Jᶜ v) (hK : R + 1 ≤ K) :
    hSum (wA p m U n Jᶜ) u x ≤ 2 * Gtail p m U i u K := by
  have hGnn : 0 ≤ Gsum p m U i u K := Gsum_nonneg (le_of_lt hp) hp1 m U i u K
  rcases Nat.lt_or_ge u R with hu | hu
  · have hstep1 : hSum (wA p m U n Jᶜ) u x ≤ hSum (wA p m U n Jᶜ) u (R + 1) := by
      unfold hSum
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hxR)
        fun z _ _ => ?_
      exact Finset.prod_nonneg fun v _ => rq_nonneg (wA_pos p m U (le_of_lt hp) n Jᶜ v)
        (wA_le_one p m U hp1 n Jᶜ v)
    have hstep2 : hSum (wA p m U n Jᶜ) u (R + 1)
        = hSum (wA p m U n Jᶜ) u R
          + ∏ v ∈ Finset.Ico (u + 1) (R + 1), rq (wA p m U n Jᶜ) v := hSum_succ huR
    have h3 := hSum_le_Gsum (p := p) hp hp1 (m := m) (n := n) (J := J) (i := i)
      (u := u) (R := R) (K := K) (by omega) hcomp
    have h4 := prod_succ_le_Gsum (p := p) hp hp1 (m := m) (n := n) (J := J) (i := i)
      (u := u) (R := R) (K := K) hu hK hcomp
    rw [hstep2] at hstep1
    unfold Gtail
    linarith
  · -- `u = R`: at most the single term `z = R`
    have huEq : u = R := le_antisymm huR hu
    have hsingle : hSum (wA p m U n Jᶜ) u x ≤ 1 := by
      have hsub : Finset.Ico u x ⊆ {R} := by
        intro z hz
        simp only [Finset.mem_singleton]
        have h1 := (Finset.mem_Ico.mp hz).1
        have h2 := (Finset.mem_Ico.mp hz).2
        omega
      have hle : hSum (wA p m U n Jᶜ) u x ≤ ∑ _z ∈ Finset.Ico u x, (1 : ℝ) := by
        unfold hSum
        refine Finset.sum_le_sum fun z _ => ?_
        refine Finset.prod_le_one (fun v _ => rq_nonneg (wA_pos p m U (le_of_lt hp) n Jᶜ v)
          (wA_le_one p m U hp1 n Jᶜ v)) (fun v _ => ?_)
        exact rq_le_one (wA_pos p m U (le_of_lt hp) n Jᶜ v)
          (one_half_le_wA p m U (le_of_lt hp) n Jᶜ v)
      have hcard : (∑ _z ∈ Finset.Ico u x, (1 : ℝ)) = ((Finset.Ico u x).card : ℝ) := by simp
      have hc : (Finset.Ico u x).card ≤ 1 := by
        simpa using Finset.card_le_card hsub
      have hcc : ((Finset.Ico u x).card : ℝ) ≤ 1 := by
        have : ((Finset.Ico u x).card : ℝ) ≤ ((1 : ℕ) : ℝ) := by exact_mod_cast hc
        simpa using this
      linarith
    have hG1 : 1 ≤ Gtail p m U i u K := by unfold Gtail; linarith
    linarith

/-! ### 5. The static maximum of `h_i + G_i` -/

/-- The paper's static object `max_{i∈I, 0≤x≤n+1} (h_i(x) + G_i(x))` (truncated at `n+2`). -/
noncomputable def staticMax (p : ℝ) (m n : ℕ) (I : Finset (Fin N)) (hI : I.Nonempty)
    (U : Array N) : ℝ :=
  Swarming.Group.maximumOn I hI (fun i =>
    (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
      (fun x => hfix (omegaN p m U i) x + Gtail p m U i x (n + 2)))

theorem le_staticMax {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {I : Finset (Fin N)} (hI : I.Nonempty) {U : Array N}
    {i : Fin N} (hi : i ∈ I) {x : ℕ} (hx : x < n + 2) :
    hfix (omegaN p m U i) x + Gtail p m U i x (n + 2) ≤ staticMax p m n I hI U := by
  have h1 : hfix (omegaN p m U i) x + Gtail p m U i x (n + 2)
      ≤ (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
          (fun y => hfix (omegaN p m U i) y + Gtail p m U i y (n + 2)) :=
    Finset.le_sup' (fun y => hfix (omegaN p m U i) y + Gtail p m U i y (n + 2))
      (Finset.mem_range.mpr hx)
  exact le_trans h1 (Finset.le_sup' (fun i => (Finset.range (n + 2)).sup'
    ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun x => hfix (omegaN p m U i) x + Gtail p m U i x (n + 2))) hi)

theorem hfix_le_staticMax {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {I : Finset (Fin N)} (hI : I.Nonempty) {U : Array N} {i : Fin N} (hi : i ∈ I) {x : ℕ}
    (hx : x < n + 2) :
    hfix (omegaN p m U i) x ≤ staticMax p m n I hI U := by
  have h := le_staticMax (p := p) hp hp1 (m := m) (n := n) (hI := hI) (U := U) hi hx
  unfold Gtail at h
  linarith [Gsum_nonneg hp hp1 m U i x (n + 2)]

theorem Gtail_le_staticMax {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {I : Finset (Fin N)} (hI : I.Nonempty) {U : Array N} {i : Fin N} (hi : i ∈ I) {x : ℕ}
    (hx : x < n + 2) :
    Gtail p m U i x (n + 2) ≤ staticMax p m n I hI U := by
  have h := le_staticMax (p := p) hp hp1 (m := m) (n := n) (hI := hI) (U := U) hi hx
  have h1 : (1 : ℝ) ≤ hfix (omegaN p m U i) x :=
    one_le_hfix (omegaN p m U i) (fun v => omegaAt_pos p m U hp i (v : ℤ))
      (fun v => omegaAt_le_one p m U hp1 i (v : ℤ)) x
  linarith

theorem one_le_staticMax {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {I : Finset (Fin N)} (hI : I.Nonempty) (U : Array N) :
    1 ≤ staticMax p m n I hI U := by
  have hI' : I.Nonempty := hI
  obtain ⟨i₀, hi₀⟩ := hI'
  have h := le_staticMax (p := p) hp hp1 (m := m) (n := n) (hI := hI) (U := U) hi₀
    (x := 0) (by omega)
  have h1 : (1 : ℝ) ≤ hfix (omegaN p m U i₀) 0 :=
    one_le_hfix (omegaN p m U i₀) (fun v => omegaAt_pos p m U hp i₀ (v : ℤ))
      (fun v => omegaAt_le_one p m U hp1 i₀ (v : ℤ)) 0
  unfold Gtail at h
  linarith [Gsum_nonneg hp hp1 m U i₀ 0 (n + 2)]

/-- The running maximum over `I` at time `n` bounds every position at time `n+1` on `(sep)`. -/
theorem X_succ_le_max {p : ℝ} {m n : ℕ} {I J : Finset (Fin N)} {U : Array N}
    (hsep : SepSet p m n I J U) {i₀ : Fin N} (hi₀ : i₀ ∈ I) {Rz : ℤ}
    (hRz : ∀ i ∈ I, runMax p m U i n ≤ Rz) {k : Fin N} (hk : k ∈ I ∪ J) :
    X p m U (n + 1) k ≤ Rz + 1 := by
  have h1 : X p m U (n + 1) k ≤ X p m U n k + 1 := X_succ_le_add_one p m U n k
  have h2 : X p m U n k ≤ runMax p m U k n := le_runMax_pos p m U n k
  have h5 : X p m U n i₀ ≤ runMax p m U i₀ n := le_runMax_pos p m U n i₀
  have h6 : runMax p m U i₀ n ≤ Rz := hRz i₀ hi₀
  rcases Finset.mem_union.mp hk with hkI | hkJ
  · have h3 := hRz k hkI
    omega
  · have h4 := hsep.2 i₀ hi₀ k hkJ
    omega

/-- The static bound for one term of `hBound`, on `(sep)`: the weight `hprev w' u` is
controlled by `(hcomp)` at the running maximum `R = M_n^{i_0}`. -/
theorem hprevu_le_static {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {I J : Finset (Fin N)} {hI : I.Nonempty} {U : Array N} (hid : Disjoint I J)
    {i₀ : Fin N} (hi₀ : i₀ ∈ I) {R : ℕ} (hR : (R : ℤ) = runMax p m U i₀ n) {x u : ℕ}
    (hxR : x ≤ R + 1) (hux : u ≤ x) :
    1 + hprev (wA p m U (n + 1) Jᶜ) u ≤ staticMax p m n I hI U + 3 := by
  have hi₀J : i₀ ∈ Jᶜ := Finset.mem_compl.mpr (Finset.disjoint_left.mp hid hi₀)
  have hRle : R ≤ n := by
    have h1 : runMax p m U i₀ n ≤ (n : ℤ) := runMax_le_time p m U i₀ n
    have h2 : (R : ℤ) ≤ (n : ℤ) := by rw [hR]; exact h1
    exact_mod_cast h2
  have hmono : hprev (wA p m U (n + 1) Jᶜ) u ≤ hprev (wA p m U n Jᶜ) u := by
    rcases u with _ | j
    · simp
    · simpa using hfix_mono (w := wA p m U n Jᶜ) (w' := wA p m U (n + 1) Jᶜ)
        (wA_pos p m U (le_of_lt hp) n Jᶜ) (wA_le_one p m U hp1 n Jᶜ)
        (wA_pos p m U (le_of_lt hp) (n + 1) Jᶜ) (wA_le_one p m U hp1 (n + 1) Jᶜ)
        (wA_le_succ p (le_of_lt hp) m U n Jᶜ) j
  rcases u with _ | j
  · simp only [hprev_zero]
    linarith [one_le_staticMax (p := p) (hp := le_of_lt hp) (hp1 := hp1) (m := m) (n := n)
      (hI := hI) U]
  · simp only [hprev_succ] at hmono
    simp only [hprev_succ]
    have hjR : j ≤ R := by omega
    rcases lt_or_eq_of_le hjR with hlt | heq
    · have hji : (j : ℤ) < runMax p m U i₀ n := by
        have h1 : (j : ℤ) < (R : ℤ) := by exact_mod_cast hlt
        rwa [hR] at h1
      have hc := hcomp_h p m U (le_of_lt hp) hp1 hi₀J (n := n) (x := j) hji
      have h2 := hfix_le_staticMax (p := p) (hp := le_of_lt hp) (hp1 := hp1) (m := m) (n := n)
        (hI := hI) (U := U) hi₀ (x := j) (by omega)
      linarith
    · -- `j = R`: the bound at the running maximum uses `hcomp_h_runMax`
      rw [heq] at hmono ⊢
      have hc := hcomp_h_runMax p m U (le_of_lt hp) hp1 hi₀J (n := n)
      have hRt : (runMax p m U i₀ n).toNat = R := by
        rw [hR.symm]; simp
      rw [hRt] at hc
      rcases Nat.eq_zero_or_pos R with h0 | hpos
      · rw [h0] at hc hmono ⊢
        simp only [hprev_zero] at hc
        have h1 := one_le_staticMax (p := p) (hp := le_of_lt hp) (hp1 := hp1) (m := m) (n := n)
          (hI := hI) U
        linarith
      · rw [hprev_eq_hfix_sub_one hpos] at hc
        have h2 := hfix_le_staticMax (p := p) (hp := le_of_lt hp) (hp1 := hp1) (m := m) (n := n)
          (hI := hI) (U := U) hi₀ (x := R - 1) (by omega)
        linarith

/-- At most `N` sites change their group weight in one step, below any level. -/
theorem card_cross_le (p : ℝ) (hp : 1 / 2 < p) (m n : ℕ) (J : Finset (Fin N))
    (U : Array N) (x : ℕ) :
    ((Finset.range (x + 1)).filter
      (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card ≤ N := by
  have hsub : (Finset.range (x + 1)).filter
        (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)
      ⊆ (Jᶜ).image (fun i => (X p m U (n + 1) i).toNat) := by
    intro u hu
    simp only [Finset.mem_filter] at hu
    obtain ⟨i, hi, hXi⟩ := cross_site p hp m U n J u hu.2
    refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
    rw [hXi, Int.toNat_natCast]
  calc ((Finset.range (x + 1)).filter
        (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card
      ≤ ((Jᶜ).image (fun i => (X p m U (n + 1) i).toNat)).card := Finset.card_le_card hsub
    _ ≤ (Jᶜ).card := Finset.card_image_le
    _ ≤ N := by
        have := Finset.card_le_univ (Jᶜ)
        simpa using this

/-- **The `hBound` of the actual group weights is controlled by the static maximum.** -/
theorem hBound_le_static {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {I J : Finset (Fin N)} {hI : I.Nonempty} {U : Array N} (hid : Disjoint I J)
    {i₀ : Fin N} (hi₀ : i₀ ∈ I) {R x : ℕ} (hR : (R : ℤ) = runMax p m U i₀ n)
    (hxR : x ≤ R + 1) :
    hBound p (wA p m U n Jᶜ) (wA p m U (n + 1) Jᶜ) x
      ≤ ((2 * p - 1) / p) * (N : ℝ) *
          (2 * staticMax p m n I hI U * (staticMax p m n I hI U + 3)) := by
  have hi₀J : i₀ ∈ Jᶜ := Finset.mem_compl.mpr (Finset.disjoint_left.mp hid hi₀)
  have hRle : R ≤ n := by
    have h1 : runMax p m U i₀ n ≤ (n : ℤ) := runMax_le_time p m U i₀ n
    have h2 : (R : ℤ) ≤ (n : ℤ) := by rw [hR]; exact h1
    exact_mod_cast h2
  have hcomp : ∀ v : ℕ, v < R → omegaN p m U i₀ v ≤ wA p m U n Jᶜ v := by
    intro v hv
    refine omegaAt_le_wA p m U (le_of_lt hp) hi₀J (x := v) ?_
    have h1 : (v : ℤ) < (R : ℤ) := by exact_mod_cast hv
    rwa [hR] at h1
  set M : ℝ := staticMax p m n I hI U with hMdef
  have hM1 : 1 ≤ M := one_le_staticMax (p := p) (hp := le_of_lt hp) (hp1 := hp1) (m := m) (n := n)
    (hI := hI) U
  have hM0 : 0 ≤ M := by linarith
  have hc : 0 ≤ (2 * p - 1) / p := by
    apply div_nonneg <;> linarith
  have hterm : ∀ u ∈ Finset.range (x + 1),
      (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then
        (1 + hprev (wA p m U (n + 1) Jᶜ) u) * hSum (wA p m U n Jᶜ) u x else 0)
      ≤ (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then
          (M + 3) * (2 * M) else 0) := by
    intro u hu
    have hux : u ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
    by_cases h : wA p m U n Jᶜ u = wA p m U (n + 1) Jᶜ u
    · rw [if_neg (by simp [h]), if_neg (by simp [h])]
    · rw [if_pos h, if_pos h]
      have h1 : 1 + hprev (wA p m U (n + 1) Jᶜ) u ≤ M + 3 :=
        hprevu_le_static hp hp1 hid hi₀ hR hxR hux
      have h2 : hSum (wA p m U n Jᶜ) u x ≤ 2 * M := by
        rcases Nat.lt_or_ge u R with huR | huR
        · refine le_trans (hSum_le_two_Gtail (p := p) hp hp1 (m := m) (n := n) (J := J)
            (i := i₀) (u := u) (x := x) (R := R) (K := n + 2) (le_of_lt huR) hxR hcomp
            (by omega : R + 1 ≤ n + 2)) ?_
          have hGt : Gtail p m U i₀ u (n + 2) ≤ M :=
            Gtail_le_staticMax (p := p) (hp := le_of_lt hp) (hp1 := hp1) (m := m) (n := n)
              (hI := hI) (U := U) hi₀ (x := u) (by omega)
          unfold Gtail at hGt ⊢
          linarith
        · -- `u ≥ R` and `u ≤ x ≤ R + 1`: the inner sum has at most one term
          have hsub : Finset.Ico u x ⊆ {R} := by
            intro z hz
            simp only [Finset.mem_singleton]
            have h1 := (Finset.mem_Ico.mp hz).1
            have h2 := (Finset.mem_Ico.mp hz).2
            omega
          have hle : hSum (wA p m U n Jᶜ) u x ≤ ∑ _z ∈ Finset.Ico u x, (1 : ℝ) := by
            unfold hSum
            refine Finset.sum_le_sum fun z _ => ?_
            refine Finset.prod_le_one (fun v _ => rq_nonneg (wA_pos p m U (le_of_lt hp) n Jᶜ v)
              (wA_le_one p m U hp1 n Jᶜ v)) (fun v _ => ?_)
            exact rq_le_one (wA_pos p m U (le_of_lt hp) n Jᶜ v)
              (one_half_le_wA p m U (le_of_lt hp) n Jᶜ v)
          have hcard : (∑ _z ∈ Finset.Ico u x, (1 : ℝ)) = ((Finset.Ico u x).card : ℝ) := by simp
          have hc1 : (Finset.Ico u x).card ≤ 1 := by
            simpa using Finset.card_le_card hsub
          have hcc : ((Finset.Ico u x).card : ℝ) ≤ 1 := by
            have h2 : ((Finset.Ico u x).card : ℝ) ≤ ((1 : ℕ) : ℝ) := by exact_mod_cast hc1
            simpa using h2
          have h1 := one_le_staticMax (p := p) (hp := le_of_lt hp) (hp1 := hp1) (m := m) (n := n)
            (hI := hI) U
          have : hSum (wA p m U n Jᶜ) u x ≤ 1 := by linarith
          linarith
      have h3 : 0 ≤ hSum (wA p m U n Jᶜ) u x := by
        unfold hSum
        exact Finset.sum_nonneg fun z _ => Finset.prod_nonneg fun v _ =>
          rq_nonneg (wA_pos p m U (le_of_lt hp) n Jᶜ v) (wA_le_one p m U hp1 n Jᶜ v)
      exact mul_le_mul h1 h2 h3 (by linarith)
  have hsum_le : (∑ u ∈ Finset.range (x + 1),
        (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then
          (1 + hprev (wA p m U (n + 1) Jᶜ) u) * hSum (wA p m U n Jᶜ) u x else 0))
      ≤ (M + 3) * (2 * M) * (N : ℝ) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_filter]
    have hM' : (0 : ℝ) ≤ (M + 3) * (2 * M) := by nlinarith
    have hcard : (((Finset.range (x + 1)).filter
        (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast card_cross_le p hp m n J U x
    calc (∑ _u ∈ (Finset.range (x + 1)).filter
          (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u), (M + 3) * (2 * M))
        = (((Finset.range (x + 1)).filter
            (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card : ℝ)
            * ((M + 3) * (2 * M)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * ((M + 3) * (2 * M)) := mul_le_mul_of_nonneg_right hcard hM'
      _ = (M + 3) * (2 * M) * (N : ℝ) := by ring
  unfold hBound
  calc ((2 * p - 1) / p) * (∑ u ∈ Finset.range (x + 1),
        (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then
          (1 + hprev (wA p m U (n + 1) Jᶜ) u) * hSum (wA p m U n Jᶜ) u x else 0))
      ≤ ((2 * p - 1) / p) * ((M + 3) * (2 * M) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_le hc
    _ = ((2 * p - 1) / p) * (N : ℝ) * (2 * staticMax p m n I hI U
          * (staticMax p m n I hI U + 3)) := by
        rw [hMdef]; ring

/-- **The one-step group-potential update is bounded by the static maximum.**  This is the
`siteDiff` term of `QVarBound.abs_WA_drift_le_potMax`, i.e. the paper's
`|W_{n+1}-W_n| ≤ C(1+max(h_j+G_j))^2`. -/
theorem HZ_diff_le_static {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {I J : Finset (Fin N)} (hI : I.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) {i₀ : Fin N} (hi₀ : i₀ ∈ I) {R : ℕ}
    (hRz : ∀ i ∈ I, runMax p m U i n ≤ (R : ℤ))
    (hR : (R : ℤ) = runMax p m U i₀ n) {k : Fin N} (hk : k ∈ I ∪ J) :
    HZ (wA p m U n Jᶜ) (X p m U (n + 1) k) - HZ (wA p m U (n + 1) Jᶜ) (X p m U (n + 1) k)
      ≤ ((2 * p - 1) / p) * (N : ℝ) *
          (2 * staticMax p m n I hI U * (staticMax p m n I hI U + 3)) := by
  have hkR : X p m U (n + 1) k ≤ (R : ℤ) + 1 := by
    have h1 := X_succ_le_max (p := p) (m := m) (n := n) (I := I) (J := J) (Rz := (R : ℤ))
      hsep hi₀ hRz hk
    exact h1
  have hM1 := one_le_staticMax (p := p) (hp := le_of_lt hp) (hp1 := hp1) (m := m) (n := n)
    (hI := hI) U
  by_cases hx : 0 ≤ X p m U (n + 1) k
  · rw [HZ_nonneg hx, HZ_nonneg hx]
    have hxle : (X p m U (n + 1) k).toNat ≤ R + 1 := by
      have h1 : ((X p m U (n + 1) k).toNat : ℤ) = X p m U (n + 1) k := Int.toNat_of_nonneg hx
      have h2 : ((X p m U (n + 1) k).toNat : ℤ) ≤ (R : ℤ) + 1 := by rw [h1]; exact hkR
      exact_mod_cast h2
    have hp0 : p ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < p)
    refine le_trans (Hfix_diff_le_hBound (p := p) hp hp0 hp1
      (fun v => wA_pos p m U (le_of_lt hp) n Jᶜ v) (fun v => wA_le_one p m U hp1 n Jᶜ v)
      (fun v => wA_pos p m U (le_of_lt hp) (n + 1) Jᶜ v)
      (fun v => wA_le_one p m U hp1 (n + 1) Jᶜ v)
      (fun v => wA_eq_half_or p m U n Jᶜ v) (fun v => wA_eq_half_or p m U (n + 1) Jᶜ v)
      (fun v => wA_le_succ p (le_of_lt hp) m U n Jᶜ v) _) ?_
    exact hBound_le_static (p := p) hp hp1 hid hi₀ hR hxle
  · rw [HZ_neg (by omega), HZ_neg (by omega), sub_self]
    have hc : 0 ≤ (2 * p - 1) / p := by
      apply div_nonneg <;> linarith
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have : (0 : ℝ) ≤ 2 * staticMax p m n I hI U * (staticMax p m n I hI U + 3) := by nlinarith
    exact mul_nonneg (mul_nonneg hc hN) this

/-- **`(Mdiff)`'s pointwise input, machine-checked for the actual array**: on the separated
event the group-weight update term of `QVarBound.lean` is bounded by the paper's static maximum
`max_{i∈I, x≤n+1} (h_i(x) + G_i(x))` alone. -/
theorem siteDiff_le_static {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) :
    siteDiff p m n I J hI U
      ≤ ((2 * p - 1) / p) * (N : ℝ) *
          (2 * staticMax p m n I hI U * (staticMax p m n I hI U + 3)) := by
  have hI' : I.Nonempty := hI
  set Ms : Finset ℤ := I.image (fun i => runMax p m U i n) with hMs
  have hMsne : Ms.Nonempty := Finset.image_nonempty.mpr hI'
  have hmem := Finset.max'_mem Ms hMsne
  obtain ⟨i₀, hi₀, heq⟩ := Finset.mem_image.mp hmem
  have hRz0 : (0 : ℤ) ≤ runMax p m U i₀ n := by
    have h2 : (trajectory p m U 0).pos i₀ ≤ runMax p m U i₀ n :=
      le_runMax_of_le p m U n i₀ (Nat.zero_le n)
    simpa using h2
  have hRz : ∀ i ∈ I, runMax p m U i n ≤ runMax p m U i₀ n := by
    intro i hi
    have hmem' : runMax p m U i n ∈ Ms := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    calc runMax p m U i n ≤ Ms.max' hMsne := Finset.le_max' Ms _ hmem'
      _ = runMax p m U i₀ n := heq.symm
  have hRz' : ∀ i ∈ I, runMax p m U i n ≤ (((runMax p m U i₀ n).toNat : ℕ) : ℤ) := by
    intro i hi
    rw [Int.toNat_of_nonneg hRz0]
    exact hRz i hi
  unfold siteDiff Swarming.Group.maximumOn
  refine Finset.sup'_le _ _ fun k hk => ?_
  exact HZ_diff_le_static (p := p) hp hp1 hI hid hsep hi₀
    (R := (runMax p m U i₀ n).toNat) hRz' (Int.toNat_of_nonneg hRz0) hk

/-! ### 6. The quadratic form and measurability of the static maximum -/

/-- The bound of `siteDiff_le_static` in the paper's shape `C (1 + max(h+G))^2`. -/
theorem siteDiff_le_static_sq {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) :
    siteDiff p m n I J hI U
      ≤ ((2 * p - 1) / p) * (N : ℝ) * (8 * (1 + staticMax p m n I hI U) ^ 2) := by
  have h := siteDiff_le_static (p := p) hp hp1 I J hI hJ hid hsep
  set M := staticMax p m n I hI U with hM
  have hM1 : 1 ≤ M := one_le_staticMax (p := p) (hp := le_of_lt hp) (hp1 := hp1) (m := m) (n := n)
    (hI := hI) U
  have hstep : 2 * M * (M + 3) ≤ 8 * (1 + M) ^ 2 := by nlinarith
  have hc : 0 ≤ (2 * p - 1) / p := by
    apply div_nonneg <;> linarith
  calc siteDiff p m n I J hI U
      ≤ ((2 * p - 1) / p) * (N : ℝ) * (2 * M * (M + 3)) := h
    _ ≤ ((2 * p - 1) / p) * (N : ℝ) * (8 * (1 + M) ^ 2) := by
        refine mul_le_mul_of_nonneg_left hstep (mul_nonneg hc (Nat.cast_nonneg N))

theorem measurable_rq (p : ℝ) (m : ℕ) (i : Fin N) (v : ℕ) :
    Measurable fun U : Array N => rq (omegaN p m U i) v := by
  unfold rq
  exact (measurable_const.sub (measurable_omegaN_v p m i v)).div (measurable_omegaN_v p m i v)

theorem measurable_Gtail (p : ℝ) (m : ℕ) (i : Fin N) (x K : ℕ) :
    Measurable fun U : Array N => Gtail p m U i x K := by
  unfold Gtail Gsum
  refine Measurable.add measurable_const (Finset.measurable_sum (Finset.Ico x K) fun z _ => ?_)
  exact Finset.measurable_prod (Finset.Ico (x + 1) (z + 1)) fun v _ => measurable_rq p m i v

theorem measurable_staticMax (p : ℝ) (m n : ℕ) (I : Finset (Fin N)) (hI : I.Nonempty) :
    Measurable fun U : Array N => staticMax p m n I hI U := by
  unfold staticMax Swarming.Group.maximumOn
  have heq : (fun U : Array N => I.sup' hI (fun i => (Finset.range (n + 2)).sup'
        ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun x => hfix (omegaN p m U i) x + Gtail p m U i x (n + 2))))
      = I.sup' hI (fun i (U : Array N) => (Finset.range (n + 2)).sup'
        ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun x => hfix (omegaN p m U i) x + Gtail p m U i x (n + 2))) := by
    funext U
    exact (Finset.sup'_apply hI
      (fun i (U : Array N) => (Finset.range (n + 2)).sup'
        ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun x => hfix (omegaN p m U i) x + Gtail p m U i x (n + 2))) U).symm
  rw [heq]
  refine Finset.measurable_sup' hI (fun i _ => ?_)
  have heq2 : (fun U : Array N => (Finset.range (n + 2)).sup'
        ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun x => hfix (omegaN p m U i) x + Gtail p m U i x (n + 2)))
      = (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun x (U : Array N) => hfix (omegaN p m U i) x + Gtail p m U i x (n + 2)) := by
    funext U
    exact (Finset.sup'_apply ⟨0, Finset.mem_range.mpr (by omega)⟩
      (fun x (U : Array N) => hfix (omegaN p m U i) x + Gtail p m U i x (n + 2)) U).symm
  rw [heq2]
  exact Finset.measurable_sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun x _ =>
    (measurable_hfix_omegaN p m i x).add (measurable_Gtail p m i x (n + 2)))

/-- `windowMax` is dominated by the static maximum (the `G` part is dropped). -/
theorem windowMax_le_staticMax {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {I : Finset (Fin N)} (hI : I.Nonempty) {U : Array N} {i : Fin N} (hi : i ∈ I) :
    windowMax p m n i U ≤ staticMax p m n I hI U := by
  refine Finset.sup'_le _ _ fun u hu => ?_
  have h := hfix_le_staticMax (p := p) (hp := hp) (hp1 := hp1) (m := m) (n := n)
    (hI := hI) (U := U) hi (x := u) (Finset.mem_range.mp hu)
  exact h

theorem PotMax_le_staticMax {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {I : Finset (Fin N)} (hI : I.Nonempty) (U : Array N) :
    PotMax p m n I hI U ≤ staticMax p m n I hI U + 4 := by
  unfold PotMax
  have : Swarming.Group.maximumOn I hI (fun i => windowMax p m n i U)
      ≤ staticMax p m n I hI U := by
    refine Finset.sup'_le hI _ fun i hi => windowMax_le_staticMax hp hp1 hI hi
  linarith

/-- **The paper's one-step size bound for the observable `W`**, with the static maximum
`max_{i∈I, x≤n+1}(h_i(x)+G_i(x))` in place of `siteDiff`: this is the display
`|W_{n+1}^{I,J}-W_n^{I,J}| ≤ C (1+max(h_j+G_j))^2` of the proof of Proposition `group`. -/
theorem abs_WA_drift_le_staticMax {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) :
    |WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ|
      ≤ 2 * staticMax p m n I hI U + 8
        + ((2 * p - 1) / p) * (N : ℝ) * (8 * (1 + staticMax p m n I hI U) ^ 2) := by
  have h1 := abs_WA_drift_le_potMax (p := p) (le_of_lt hp) hp1 I J hI hJ hid
    (U := U) hsep
  have h2 := siteDiff_le_static_sq (p := p) hp hp1 I J hI hJ hid hsep
  have h3 := PotMax_le_staticMax (p := p) (le_of_lt hp) hp1 (m := m) (n := n) (hI := hI) U
  linarith

/-! ### 7. The integral form: `(Mdiff)` on `(sep)` from the static fourth moment -/

/-- `SepSet` is measurable for the *ambient* uniform measure (not only for `posFilt`). -/
theorem measurableSet_sepSet_ambient (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) :
    MeasurableSet {U : Array N | SepSet p m n I J U} :=
  (posFilt N p m).le n _ (measurableSet_sepSet p m n I J)

theorem Gtail_le_succ {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m : ℕ} (U : Array N)
    (i : Fin N) (x K : ℕ) : Gtail p m U i x K ≤ 1 + (K : ℝ) := by
  have hstep : Gsum p m U i x K ≤ ((Finset.Ico x K).card : ℝ) := by
    unfold Gsum
    calc (∑ z ∈ Finset.Ico x K, ∏ v ∈ Finset.Ico (x + 1) (z + 1), rq (omegaN p m U i) v)
        ≤ ∑ _z ∈ Finset.Ico x K, (1 : ℝ) := by
          refine Finset.sum_le_sum fun z _ => ?_
          refine Finset.prod_le_one (fun v _ => rq_nonneg (omegaAt_pos p m U hp i (v : ℤ))
            (omegaAt_le_one p m U hp1 i (v : ℤ))) (fun v _ => ?_)
          exact rq_le_one (omegaAt_pos p m U hp i (v : ℤ)) (one_half_le_omegaAt p m U hp i (v : ℤ))
      _ = ((Finset.Ico x K).card : ℝ) := by simp
  have hcard : ((Finset.Ico x K).card : ℝ) ≤ (K : ℝ) := by
    have h1 : (Finset.Ico x K).card ≤ K := by
      refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_range K))
      intro a ha
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp ha).2
    exact_mod_cast h1
  unfold Gtail
  linarith

theorem staticMax_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {I : Finset (Fin N)} (hI : I.Nonempty) (U : Array N) :
    staticMax p m n I hI U ≤ (2 * ((n : ℝ) + 2) + 3) + (1 + ((n + 2 : ℕ) : ℝ)) := by
  refine Finset.sup'_le hI _ fun i hi => ?_
  refine Finset.sup'_le _ _ fun x hx => ?_
  have h2 : hfix (omegaN p m U i) x ≤ 2 * ((n : ℝ) + 2) + 3 :=
    le_trans (le_windowMax (p := p) (m := m) (n := n) (i := i) (U := U) (Finset.mem_range.mp hx))
      (windowMax_le (p := p) hp hp1 m n i U)
  have h3 : Gtail p m U i x (n + 2) ≤ 1 + ((n + 2 : ℕ) : ℝ) := Gtail_le_succ hp hp1 U i x (n + 2)
  linarith

theorem siteDiff_sq_indicator_le {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (U : Array N) :
    (if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2 else 0)
      ≤ (((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * (1 + staticMax p m n I hI U) ^ 4 := by
  classical
  have hS : (0 : ℝ) ≤ 1 + staticMax p m n I hI U := by
    linarith [one_le_staticMax (p := p) (hp := le_of_lt hp) (hp1 := hp1) (m := m) (n := n)
      (hI := hI) U]
  by_cases h : SepSet p m n I J U
  · rw [if_pos h]
    have h1 := siteDiff_le_static_sq (p := p) hp hp1 I J hI hJ hid h
    have h2 : (0 : ℝ) ≤ siteDiff p m n I J hI U := siteDiff_nonneg (le_of_lt hp) hp1 hI U
    have h3 : (siteDiff p m n I J hI U) ^ 2
        ≤ (((2 * p - 1) / p) * (N : ℝ) * 8 * (1 + staticMax p m n I hI U) ^ 2) ^ 2 := by
      refine pow_le_pow_left₀ h2 ?_ 2
      calc siteDiff p m n I J hI U
          ≤ ((2 * p - 1) / p) * (N : ℝ) * (8 * (1 + staticMax p m n I hI U) ^ 2) := h1
        _ = ((2 * p - 1) / p) * (N : ℝ) * 8 * (1 + staticMax p m n I hI U) ^ 2 := by ring
    have h4 : (((2 * p - 1) / p) * (N : ℝ) * 8 * (1 + staticMax p m n I hI U) ^ 2) ^ 2
        = (((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * (1 + staticMax p m n I hI U) ^ 4 := by ring
    rw [h4] at h3
    exact h3
  · rw [if_neg h]
    positivity

/-- **`(Mdiff)` on `(sep)`, reduced to the static fourth moment.** -/
theorem integral_sq_siteDiff_indicator_le {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) :
    ∫ U, (if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2 else 0)
        ∂(arrayMeasure N)
      ≤ (((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2
          * ∫ U, (1 + staticMax p m n I hI U) ^ 4 ∂(arrayMeasure N) := by
  classical
  have hmeasS : Measurable fun U : Array N => 1 + staticMax p m n I hI U :=
    measurable_const.add (measurable_staticMax p m n I hI)
  have hbound : ∀ U : Array N, |(1 + staticMax p m n I hI U) ^ 2|
      ≤ ((2 * ((n : ℝ) + 2) + 3) + (1 + ((n + 2 : ℕ) : ℝ)) + 1) ^ 2 := by
    intro U
    have h1 : staticMax p m n I hI U ≤ (2 * ((n : ℝ) + 2) + 3) + (1 + ((n + 2 : ℕ) : ℝ)) :=
      staticMax_le (le_of_lt hp) hp1 hI U
    have h2 : (0 : ℝ) ≤ 1 + staticMax p m n I hI U := by
      linarith [one_le_staticMax (p := p) (hp := le_of_lt hp) (hp1 := hp1) (m := m) (n := n)
        (hI := hI) U]
    rw [abs_of_nonneg (by positivity)]
    have h3 : 1 + staticMax p m n I hI U
        ≤ (2 * ((n : ℝ) + 2) + 3) + (1 + ((n + 2 : ℕ) : ℝ)) + 1 := by linarith
    exact pow_le_pow_left₀ h2 h3 2
  have hm2 : AEStronglyMeasurable (fun U : Array N => (1 + staticMax p m n I hI U) ^ 2)
      (arrayMeasure N) := by
    have hfun : (fun U : Array N => (1 + staticMax p m n I hI U) ^ 2)
        = (fun U : Array N => 1 + staticMax p m n I hI U)
          * (fun U : Array N => 1 + staticMax p m n I hI U) := by
      funext U
      rw [Pi.mul_apply, pow_two]
    rw [hfun]
    exact (hmeasS.mul hmeasS).aestronglyMeasurable
  have hintS : Integrable (fun U : Array N => (1 + staticMax p m n I hI U) ^ 4)
      (arrayMeasure N) := by
    have h := integrable_sq_of_abs_bound (f := fun U : Array N => (1 + staticMax p m n I hI U) ^ 2)
      hm2 (by positivity) hbound
    refine h.congr (Eventually.of_forall fun U => ?_)
    show ((1 + staticMax p m n I hI U) ^ 2) ^ 2 = (1 + staticMax p m n I hI U) ^ 4
    ring
  have hintL : Integrable (fun U : Array N =>
      if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2 else 0) (arrayMeasure N) :=
    (integrable_siteDiff_sq (le_of_lt hp) hp1 m n I J hI).indicator
      (measurableSet_sepSet_ambient p m n I J)
  have hmono : ∀ U : Array N,
      (if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2 else 0)
        ≤ (((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * (1 + staticMax p m n I hI U) ^ 4 :=
    siteDiff_sq_indicator_le hp hp1 I J hI hJ hid
  calc ∫ U, (if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2 else 0)
        ∂(arrayMeasure N)
      ≤ ∫ U, (((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * (1 + staticMax p m n I hI U) ^ 4
          ∂(arrayMeasure N) := integral_mono hintL (hintS.const_mul ((((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2)) hmono
    _ = (((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2
          * ∫ U, (1 + staticMax p m n I hI U) ^ 4 ∂(arrayMeasure N) := integral_const_mul _ _

/-- **The residual premise, exactly as used**: a static `(maxmom)`-type fourth moment bound on
`h_i + G_i` implies `(Mdiff)` in its usable `(sep)`-supported form. -/
theorem mdiff_of_static_moment {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {C₄ : ℝ} (hstat : ∀ k : ℕ, ∫ U, (1 + staticMax p m k I hI U) ^ 4 ∂(arrayMeasure N)
      ≤ C₄ * Real.log ((k : ℝ) + 2) ^ 4) :
    ∀ k : ℕ, ∫ U, (if SepSet p m k I J U then (siteDiff p m k I J hI U) ^ 2 else 0)
        ∂(arrayMeasure N)
      ≤ ((((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * C₄) * Real.log ((k : ℝ) + 2) ^ 4 := by
  classical
  intro k
  refine le_trans (integral_sq_siteDiff_indicator_le (p := p) hp hp1 I J hI hJ hid
    (m := m) (n := k)) ?_
  have hK2 : (0 : ℝ) ≤ (((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 := by positivity
  calc (((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2
        * ∫ U, (1 + staticMax p m k I hI U) ^ 4 ∂(arrayMeasure N)
      ≤ (((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * (C₄ * Real.log ((k : ℝ) + 2) ^ 4) :=
        mul_le_mul_of_nonneg_left (hstat k) hK2
    _ = ((((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * C₄) * Real.log ((k : ℝ) + 2) ^ 4 := by ring

/-! ### 8. Integration into `QVarBound`: the raw increment only needs the `(sep)`-supported
`siteDiff` moment -/

/-- `Qraw` vanishes off `(sep)`, so its square is controlled by the `(sep)`-supported `siteDiff`. -/
theorem Qraw_sq_le_static {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    (U : Array N) :
    (Qraw p m I J hI hJ n U) ^ 2
      ≤ 8 * (if SepSet p m n I J U then (PotMax p m n I hI U) ^ 2 else 0)
        + 2 * (if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2 else 0) := by
  classical
  by_cases h : U ∈ {U : Array N | SepSet p m n I J U}
  · have h' : SepSet p m n I J U := h
    rw [if_pos h', if_pos h']
    have hQ : Qraw p m I J hI hJ n U
        = WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ := by
      simp only [Qraw, Set.indicator_of_mem h]
    rw [hQ]
    have h1 := abs_WA_drift_le_potMax (p := p) hp hp1 I J hI hJ hid (U := U) h
    have h2 : |WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ|
        ≤ 2 * PotMax p m n I hI U + siteDiff p m n I J hI U := h1
    have hP : (0 : ℝ) ≤ PotMax p m n I hI U := PotMax_nonneg (p := p) hp hp1 (U := U)
    have hS : (0 : ℝ) ≤ siteDiff p m n I J hI U := siteDiff_nonneg hp hp1 hI U
    have h3 : (WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ) ^ 2
        ≤ (2 * PotMax p m n I hI U + siteDiff p m n I J hI U) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have h4 : (2 * PotMax p m n I hI U + siteDiff p m n I J hI U) ^ 2
        ≤ 8 * (PotMax p m n I hI U) ^ 2 + 2 * (siteDiff p m n I J hI U) ^ 2 := by
      nlinarith [sq_nonneg (2 * PotMax p m n I hI U - siteDiff p m n I J hI U)]
    linarith
  · have h' : ¬ SepSet p m n I J U := h
    rw [if_neg h', if_neg h']
    have hQ : Qraw p m I J hI hJ n U = 0 := by
      simp only [Qraw, Set.indicator_of_notMem h]
    rw [hQ]
    norm_num

/-- The integral version: the `siteDiff` contribution to the `dQ` variance only needs the
`(sep)`-supported second moment. -/
theorem integral_sq_Qraw_le {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) :
    ∫ U, (Qraw p m I J hI hJ n U) ^ 2 ∂(arrayMeasure N)
      ≤ 8 * ∫ U, (PotMax p m n I hI U) ^ 2 ∂(arrayMeasure N)
        + 2 * ∫ U, (if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2 else 0)
            ∂(arrayMeasure N) := by
  classical
  have hp' : 1 / 2 ≤ p := le_of_lt hp
  have hp1' : p ≤ 1 := hp1
  have hprob := arrayMeasure_isProbabilityMeasure N
  have hprob' := hprob
  -- integrability of the right-hand side
  have hPint : Integrable (fun U => (if SepSet p m n I J U then (PotMax p m n I hI U) ^ 2
      else 0)) (arrayMeasure N) :=
    (integrable_potMax_sq hp' hp1' m n I hI).indicator (measurableSet_sepSet_ambient p m n I J)
  have hSint : Integrable (fun U => (if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2
      else 0)) (arrayMeasure N) :=
    (integrable_siteDiff_sq hp' hp1' m n I J hI).indicator
      (measurableSet_sepSet_ambient p m n I J)
  have hQint : Integrable (fun U => (Qraw p m I J hI hJ n U) ^ 2) (arrayMeasure N) := by
    refine integrable_sq_of_abs_bound (integrable_Qraw hp' hp1' m n I J hI hJ).aestronglyMeasurable
      (Qbound_nonneg n) (abs_Qraw_le hp' hp1' m n I J hI hJ)
  have hmono : ∀ U : Array N, (Qraw p m I J hI hJ n U) ^ 2
      ≤ 8 * (if SepSet p m n I J U then (PotMax p m n I hI U) ^ 2 else 0)
        + 2 * (if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2 else 0) :=
    fun U => Qraw_sq_le_static hp' hp1' I J hI hJ hid U
  have hstep : ∫ U, (Qraw p m I J hI hJ n U) ^ 2 ∂(arrayMeasure N)
      ≤ ∫ U, 8 * (if SepSet p m n I J U then (PotMax p m n I hI U) ^ 2 else 0)
          + 2 * (if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2 else 0)
          ∂(arrayMeasure N) :=
    integral_mono hQint ((hPint.const_mul 8).add (hSint.const_mul 2)) hmono
  have hsplit : ∫ U, 8 * (if SepSet p m n I J U then (PotMax p m n I hI U) ^ 2 else 0)
        + 2 * (if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2 else 0)
        ∂(arrayMeasure N)
      = 8 * ∫ U, (if SepSet p m n I J U then (PotMax p m n I hI U) ^ 2 else 0)
          ∂(arrayMeasure N)
        + 2 * ∫ U, (if SepSet p m n I J U then (siteDiff p m n I J hI U) ^ 2 else 0)
            ∂(arrayMeasure N) := by
    rw [integral_add (hPint.const_mul 8) (hSint.const_mul 2), integral_const_mul,
      integral_const_mul]
  have hPotle : ∫ U, (if SepSet p m n I J U then (PotMax p m n I hI U) ^ 2 else 0)
        ∂(arrayMeasure N)
      ≤ ∫ U, (PotMax p m n I hI U) ^ 2 ∂(arrayMeasure N) :=
    integral_mono hPint (integrable_potMax_sq hp' hp1' m n I hI) fun U => by
      by_cases h : SepSet p m n I J U
      · rw [if_pos h]
      · rw [if_neg h]; positivity
  linarith

/-- **The full integration**: the log-fourth variance bound for the actual `Q^{I,J}` from the
static `(Mpot)` bound on `PotMax` and the static fourth-moment bound on `h_i + G_i`.  The
`siteDiff` premise `(Mdiff)` of `QVarBound.Q_log_variance_of_potMoment` is no longer needed. -/
theorem Q_log_variance_of_static {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {C₁ C₄ : ℝ} (hC₁ : 0 ≤ C₁) (hC₄ : 0 ≤ C₄)
    (hPot : ∀ k : ℕ, ∫ U, (PotMax p m k I hI U) ^ 2 ∂(arrayMeasure N)
      ≤ C₁ * (Real.log ((k : ℝ) + 2)) ^ 4)
    (hStat : ∀ k : ℕ, ∫ U, (1 + staticMax p m k I hI U) ^ 4 ∂(arrayMeasure N)
      ≤ C₄ * (Real.log ((k : ℝ) + 2)) ^ 4) :
    (∀ k : ℕ, Integrable
        (fun U => (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2) (arrayMeasure N))
      ∧ ∀ k : ℕ, ∫ U, (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2 ∂(arrayMeasure N)
        ≤ (8 * C₁ + 2 * ((((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * C₄))
            * (Real.log ((k : ℝ) + 2)) ^ 4 := by
  classical
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hK2 : (0 : ℝ) ≤ (((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 := by positivity
  constructor
  · intro k
    rw [inc_Q_sq_eq]
    exact integrable_dQ_sq hp hp1' m k I J hI hJ
  · intro k
    have h1 : ∫ U, (dQ p m I J hI hJ k U) ^ 2 ∂(arrayMeasure N)
        ≤ ∫ U, (Qraw p m I J hI hJ k U) ^ 2 ∂(arrayMeasure N) :=
      integral_sq_dQ_le hp hp1' m k I J hI hJ
    have h2 : ∫ U, (Qraw p m I J hI hJ k U) ^ 2 ∂(arrayMeasure N)
        ≤ 8 * ∫ U, (PotMax p m k I hI U) ^ 2 ∂(arrayMeasure N)
          + 2 * ∫ U, (if SepSet p m k I J U then (siteDiff p m k I J hI U) ^ 2 else 0)
              ∂(arrayMeasure N) :=
      integral_sq_Qraw_le hp0 hp1' I J hI hJ hid (m := m) (n := k)
    have h3 : ∫ U, (if SepSet p m k I J U then (siteDiff p m k I J hI U) ^ 2 else 0)
          ∂(arrayMeasure N)
        ≤ ((((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * C₄) * Real.log ((k : ℝ) + 2) ^ 4 :=
      mdiff_of_static_moment hp0 hp1' I J hI hJ hid (m := m) (C₄ := C₄) hStat k
    have hP := hPot k
    rw [inc_Q_sq_eq]
    nlinarith [h1, h2, h3, hP, hK2, sq_nonneg (Real.log ((k : ℝ) + 2)), hC₁, hC₄]

end SwarmSiteDiff
