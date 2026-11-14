/-
# the deterministic one-step weight/locality claim behind `(locmove)`

The proof of Proposition `local` of `main_1d_revised.tex` compares, at a time `n`
satisfying `(sep)`, the group potential at the *new* positions `X_{n+1}^j` with the weights
of time `n` (`WdriftJoint.Mnext` is exactly `max_{j∈J} H_n^{J^c}(X_{n+1}^j)`), and then
invokes

  `H_{n+1}^A(X_{n+1}^j) = H_n^A(X_{n+1}^j)`   for `j ∈ Aᶜ`  on `(sep)`,        (*)

"weights change only at the positions of `A`, which lie strictly above `Aᶜ` on `(sep)`"
(`LocMoveH.lean`, docstring of `condExp_indicator_Mnext_sub_Mnow_ge_one`).

That inference is *not* immediate, for two independent reasons:

* the positions of `A` at time `n+1` are only `≥` those of `Aᶜ` (not `>`, see
  `SepGroup.Model.sep_pos_succ_le`), so `w_{n+1}^A` and `w_n^A` may well differ **at the
  point** `X_{n+1}^j` itself; and
* `H^A(x)` is a *prefix sum* `∑_{u<x} h^A(u)`, so what matters are the entries
  `u < x`, not the entry at `x`.

This file settles the claim against the actual definitions of `SepGroup.Model`
(`wA`, `hA`, `HA`, the stored local times of `Swarming.Trajectory.trajectory`) and
delimits exactly which local-time entries can move `H^A(x)` at a single step:

* `L_succ` — the stored local time grows at exactly one site, the walker's new position;
* `wA_succ_eq_of_le` — `w_{n+1}^A` and `w_n^A` agree at every site strictly below
  `min_{i∈A} X_{n+1}^i`;
* `HA_succ_eq_of_prefix` — **exact criterion**: `H_{n+1}^A(x) = H_n^A(x)` iff
  `w_{n+1}^A` and `w_n^A` agree on `{0,…,x-1}` (`x ≥ 0`); entries at `≥ x` are free;
* `HA_succ_eq_of_le`, `HA_succ_eq_of_sep` — hence claim (*) holds, under the hypothesis
  `X_{n+1}^j ≤ X_{n+1}^i (i ∈ A)` that `(sep)` supplies at time `n`;
* `maximumOn_succ_eq_of_sep` — the same identity for the maximum over `Aᶜ`, i.e.
  `Mnext` (time-`n` weights at the new positions) `=` the actual time-`(n+1)` maximum,
  so the drift of `LocMoveH.condExp_indicator_Mnext_sub_Mnow_ge_one` is a drift of the
  actual `WA`-maximum on `(sep)`;
* `HA_succ_lt_of_wA_lt`, `wA_eq_of_HA_succ_eq` — **sharpness**: any strict increase of a
  single entry `u < x` forces the strict decrease `H_{n+1}^A(x) < H_n^A(x)`, so the
  criterion is not improvable: the identity at `x` is *not* a consequence of "the weights
  change only at `x`", and it fails one site higher (`Hfix_sharp_at_changed_site`).

Scope, stated explicitly: everything here is deterministic and holds for every driving
array `U`; no probabilistic hypothesis and no `(sep)` beyond the displayed position
inequality is used.  The paper's parenthetical "strictly above" is replaced by the exact
statement: the new positions of `A` are `≥` those of `Aᶜ`, and `H^A` is insensitive to a
change *at* the point itself only because `H^A(x)` sums `h^A(u)` over `u < x`.
-/
import Swarm.SepGroup

open Finset
open SepGroup
open Swarming.Uniform
open Swarming.Trajectory
open SepGroup.Model
open Cookie

namespace LocMoveWeight

set_option linter.unusedVariables false

variable {N : ℕ}

/-! ## 1. One step of the stored local times -/

/-- The stored local time of walker `i` grows, from `n` to `n+1`, at exactly one site:
the walker's new position `X_{n+1}^i`.  Nothing else changes. -/
theorem L_succ (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) (x : ℤ) :
    L p m U (n + 1) i x = L p m U n i x + if x = X p m U (n + 1) i then 1 else 0 := by
  simp only [L_apply, X_apply, trajectory_succ, nextWalkState_ell, nextWalkState_pos]
  rfl

/-- A site that no walker of `A` occupies at time `n+1` has the same `A`-local-time sum at
time `n` and at time `n+1`. -/
theorem sum_L_succ_eq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N)) {x : ℤ}
    (hx : ∀ i ∈ A, X p m U (n + 1) i ≠ x) :
    (∑ i ∈ A, L p m U (n + 1) i x) = ∑ i ∈ A, L p m U n i x := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [L_succ, if_neg (Ne.symm (hx i hi)), add_zero]

/-! ## 2. `w^A` is unchanged strictly below the new positions of `A` -/

/-- If `x` is at most every position `X_{n+1}^i` (`i ∈ A`), then at every site `v < x` the
weight `w^A` did not change at step `n → n+1`.  This is the precise form of "the weights
change only at the positions of `A`". -/
theorem wA_succ_eq_of_le (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N))
    {v : ℕ} {x : ℤ} (hx : ∀ i ∈ A, x ≤ X p m U (n + 1) i) (hv : (v : ℤ) < x) :
    wA p m U (n + 1) A v = wA p m U n A v := by
  have hsum := sum_L_succ_eq p m U n A (x := (v : ℤ)) fun i hi => by
    have hge := hx i hi
    omega
  simp only [wA, hsum]

/-- Contrapositive form: a change of `w^A` at site `v` at step `n → n+1` forces some walker
of `A` to be at `v` at time `n+1` (so `v` is a "changed local-time entry"). -/
theorem exists_pos_of_wA_ne (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N))
    {v : ℕ} (h : wA p m U n A v ≠ wA p m U (n + 1) A v) :
    ∃ i ∈ A, X p m U (n + 1) i = (v : ℤ) := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hsum : (∑ i ∈ A, L p m U (n + 1) i (v : ℤ)) = ∑ i ∈ A, L p m U n i (v : ℤ) :=
    sum_L_succ_eq p m U n A fun i hi => hcon i hi
  exact h (by simp only [wA, hsum])

/-! ## 3. `h^w`, `H^w` see exactly the entries below their argument -/

/-- `hfix` depends only on the values of `w` on `{0,…,k}`. -/
theorem hfix_congr {w w' : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    (hw0' : ∀ n, 0 < w' n) (hw1' : ∀ n, w' n ≤ 1) {k : ℕ}
    (h : ∀ u ≤ k, w u = w' u) : hfix w k = hfix w' k := by
  have h1 : hfix w' k ≤ hfix w k :=
    hfix_mono_prefix (w := w) (w' := w') hw0 hw1 hw0' hw1' k fun u hu => (h u hu).le
  have h2 : hfix w k ≤ hfix w' k :=
    hfix_mono_prefix (w := w') (w' := w) hw0' hw1' hw0 hw1 k fun u hu => (h u hu).ge
  linarith

/-- `Hfix w K = ∑_{u<K} h^w(u)` depends only on the values of `w` on `{0,…,K-1}`. -/
theorem Hfix_congr {w w' : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    (hw0' : ∀ n, 0 < w' n) (hw1' : ∀ n, w' n ≤ 1) {K : ℕ}
    (h : ∀ u < K, w u = w' u) : Hfix w K = Hfix w' K := by
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  exact hfix_congr hw0 hw1 hw0' hw1' fun t ht => h t (lt_of_le_of_lt ht hu)

/-- **Exact criterion.**  For `x ≥ 0`, the potential `H^A(x)` is unchanged at step
`n → n+1` iff the weight entries `w^A(0),…,w^A(x-1)` are unchanged.  (For `x < 0` both
sides are the identity function and no hypothesis is needed.) -/
theorem HA_succ_eq_of_prefix (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N))
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {x : ℤ} (hx0 : 0 ≤ x)
    (h : ∀ u < x.toNat, wA p m U n A u = wA p m U (n + 1) A u) :
    HA p m U (n + 1) A x = HA p m U n A x := by
  rcases lt_or_ge x 0 with hneg | hnon
  · simp only [HA, HZ_neg hneg]
  · simp only [HA, HZ_nonneg hnon]
    exact Hfix_congr (wA_pos p m U hp (n + 1) A) (wA_le_one p m U hp1 (n + 1) A)
      (wA_pos p m U hp n A) (wA_le_one p m U hp1 n A) fun u hu => (h u hu).symm

/-- **Claim (*), general hypothesis.**  If `x` is at most every time-`(n+1)` position of
`A`, then `H_{n+1}^A(x) = H_n^A(x)`.  No `(sep)` is needed, only this position inequality. -/
theorem HA_succ_eq_of_le (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N))
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {x : ℤ} (hx : ∀ i ∈ A, x ≤ X p m U (n + 1) i) :
    HA p m U (n + 1) A x = HA p m U n A x := by
  rcases lt_or_ge x 0 with hneg | hnon
  · simp only [HA, HZ_neg hneg]
  · refine HA_succ_eq_of_prefix p m U n A hp hp1 hnon fun u hu => ?_
    exact (wA_succ_eq_of_le p m U n A (x := x) (v := u) hx (Int.lt_toNat.mp hu)).symm

/-- **Claim (*) on `(sep)`.**  At a time `n` satisfying `(sep)` with `I = A`, `J = Aᶜ`,
the potential of a walker of `Aᶜ` at its *new* position is unchanged by the step
`n → n+1`, although the weight function itself may change at that very position. -/
theorem HA_succ_eq_of_sep (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N))
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hsep : Sep p m U n A Aᶜ) {j : Fin N}
    (hj : j ∈ Aᶜ) :
    HA p m U (n + 1) A (X p m U (n + 1) j) = HA p m U n A (X p m U (n + 1) j) :=
  HA_succ_eq_of_le p m U n A hp hp1 fun i hi =>
    sep_pos_succ_le p m U hsep hi hj

/-- The same identity for the maximum over the separated group: on `(sep)`, the time-`n`
maximum at the *new* positions (the object `WdriftJoint.Mnext p m n Aᶜ hJ` with `J := Aᶜ`)
coincides with the maximum of the actual time-`(n+1)` potentials
`max_{j∈Aᶜ} H_{n+1}^A(X_{n+1}^j)`. -/
theorem maximumOn_succ_eq_of_sep (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (A : Finset (Fin N)) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hsep : Sep p m U n A Aᶜ)
    (hJ : Aᶜ.Nonempty) :
    Swarming.Group.maximumOn Aᶜ hJ (fun j => HA p m U (n + 1) A (X p m U (n + 1) j))
      = Swarming.Group.maximumOn Aᶜ hJ (fun j => HA p m U n A (X p m U (n + 1) j)) := by
  have hpt : ∀ j ∈ Aᶜ, HA p m U (n + 1) A (X p m U (n + 1) j)
      = HA p m U n A (X p m U (n + 1) j) := fun j hj =>
    HA_succ_eq_of_sep p m U n A hp hp1 hsep hj
  have hmain : ∀ (f g : Fin N → ℝ), (∀ j ∈ Aᶜ, f j = g j) →
      Swarming.Group.maximumOn Aᶜ hJ f = Swarming.Group.maximumOn Aᶜ hJ g := by
    intro f g hfg
    rw [Swarming.Group.maximumOn, Swarming.Group.maximumOn]
    refine le_antisymm ?_ ?_
    · rw [Finset.sup'_le_iff]
      intro j hj
      rw [hfg j hj]
      exact (Finset.le_sup'_iff hJ).2 ⟨j, hj, le_rfl⟩
    · rw [Finset.sup'_le_iff]
      intro j hj
      rw [← hfg j hj]
      exact (Finset.le_sup'_iff hJ).2 ⟨j, hj, le_rfl⟩
  exact hmain _ _ hpt

/-! ## 4. Sharpness: every changed entry below `x` is detected -/

/-- Strict version of the one-step comparison of the affine recursion. -/
theorem step_lt {w w' h : ℝ} (hw : 0 < w) (hww' : w < w') (hh : 0 ≤ h) :
    (1 + (1 - w') * h) / w' < (1 + (1 - w) * h) / w := by
  have hw' : 0 < w' := lt_trans hw hww'
  have key : (1 + (1 - w) * h) / w - (1 + (1 - w') * h) / w'
      = ((w' - w) * (1 + h)) / (w * w') := by
    field_simp
    ring
  have hpos : 0 < ((w' - w) * (1 + h)) / (w * w') := by positivity
  linarith

/-- If `w ≤ w'` pointwise and `w u < w' u`, then `h^{w'}(u) < h^{w}(u)` — the value of
`h` at `u` is strictly sensitive to the entry `w u`. -/
theorem hfix_lt_of_lt {w w' : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    (hw0' : ∀ n, 0 < w' n) (hw1' : ∀ n, w' n ≤ 1) (hle : ∀ n, w n ≤ w' n)
    {u : ℕ} (hu : w u < w' u) : hfix w' u < hfix w u := by
  induction u with
  | zero =>
      rw [hfix_eq, hfix_eq, hprev_zero, hprev_zero]
      exact step_lt (hw0 0) hu (by norm_num)
  | succ k ih =>
      have ih' : hfix w' k ≤ hfix w k := hfix_mono w w' hw0 hw1 hw0' hw1' hle k
      have hnonneg : 0 ≤ hfix w k := by
        have := one_le_hfix w hw0 hw1 k
        linarith
      have hstep : (1 + (1 - w' (k + 1)) * hfix w' k) / w' (k + 1)
          ≤ (1 + (1 - w' (k + 1)) * hfix w k) / w' (k + 1) := by
        refine div_le_div_of_nonneg_right ?_ (le_of_lt (hw0' (k + 1)))
        have hc : (0 : ℝ) ≤ 1 - w' (k + 1) := by linarith [hw1' (k + 1)]
        nlinarith
      rw [hfix_eq, hfix_eq, hprev_succ, hprev_succ]
      exact lt_of_le_of_lt hstep (step_lt (hw0 (k + 1)) hu hnonneg)

/-- Any strict increase of one weight entry strictly below `K` strictly decreases
`Hfix · K`.  Hence `H_{n+1}^A(x) = H_n^A(x)` is *equivalent* to "no entry `u < x`
increased" — no more and no less. -/
theorem Hfix_lt_of_entry_lt {w w' : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    (hw0' : ∀ n, 0 < w' n) (hw1' : ∀ n, w' n ≤ 1) (hle : ∀ n, w n ≤ w' n)
    {u K : ℕ} (huK : u < K) (hu : w u < w' u) : Hfix w' K < Hfix w K := by
  rw [Hfix, Hfix]
  refine Finset.sum_lt_sum (fun v _ => hfix_mono w w' hw0 hw1 hw0' hw1' hle v) ?_
  exact ⟨u, Finset.mem_range.mpr huK, hfix_lt_of_lt hw0 hw1 hw0' hw1' hle hu⟩

/-- **Model sharpness.**  A strict increase of the weight `w^A` at any single site
`u < x` (which is exactly what a new local-time visit by a walker of `A` at `u` does)
strictly decreases the potential at `x` at the next step.  So the criterion of
`HA_succ_eq_of_prefix` cannot be weakened: the equality at `x` really does force every
entry below `x` to be unchanged. -/
theorem HA_succ_lt_of_wA_lt (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N))
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {x : ℤ} (hx0 : 0 ≤ x) {u : ℕ} (hu : u < x.toNat)
    (hlt : wA p m U n A u < wA p m U (n + 1) A u) :
    HA p m U (n + 1) A x < HA p m U n A x := by
  simp only [HA, HZ_nonneg hx0]
  exact Hfix_lt_of_entry_lt (wA_pos p m U hp n A) (wA_le_one p m U hp1 n A)
    (wA_pos p m U hp (n + 1) A) (wA_le_one p m U hp1 (n + 1) A)
    (fun v => wA_mono_time p m U hp (Nat.le_succ n) A v) hu hlt

/-- Converse of `HA_succ_eq_of_prefix` in the form used above: equality of the potentials
at `x ≥ 0` forces every entry `u < x` of `w^A` to be unchanged. -/
theorem wA_eq_of_HA_succ_eq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (A : Finset (Fin N))
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {x : ℤ} (hx0 : 0 ≤ x)
    (heq : HA p m U (n + 1) A x = HA p m U n A x) :
    ∀ u < x.toNat, wA p m U n A u = wA p m U (n + 1) A u := by
  intro u hu
  by_contra hne
  have hmono := wA_mono_time p m U hp (Nat.le_succ n) A u
  exact absurd heq (ne_of_lt (HA_succ_lt_of_wA_lt p m U n A hp hp1 hx0 hu
    (lt_of_le_of_ne hmono hne)))

/-! ## 4'. The link to `LocMoveH`: the indicator functions agree, not only their maxima

`LocMoveH.condExp_indicator_Mnext_sub_Mnow_ge_one` states its drift bound for

`A₀.indicator (Mnext - Mnow)`,  `Mnext = max_{j∈Aᶜ} H_n^A(X_{n+1}^j)`,

i.e. with the *time-`n`* weights at the new positions.  The next lemma is the pure
deterministic statement that this integrand is *the same function* as the one with the
actual time-`(n+1)` potential, on every `A₀ ⊆ (sep)`; passing it through `condExp`
therefore needs no new estimate, only the measurability of the substituted maximum. -/

theorem indicator_max_eq_of_subset_sep (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ)
    (A : Finset (Fin N)) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (hJ : Aᶜ.Nonempty)
    {A₀ : Set (Array N)} (hsub : ∀ U ∈ A₀, Sep p m U n A Aᶜ) :
    (fun U => A₀.indicator (fun V =>
        Swarming.Group.maximumOn Aᶜ hJ (fun j => HA p m V (n + 1) A (X p m V (n + 1) j))
        - Swarming.Group.maximumOn Aᶜ hJ (fun j => HA p m V n A (X p m V n j))) U)
      = fun U => A₀.indicator (fun V =>
        Swarming.Group.maximumOn Aᶜ hJ (fun j => HA p m V n A (X p m V (n + 1) j))
        - Swarming.Group.maximumOn Aᶜ hJ (fun j => HA p m V n A (X p m V n j))) U := by
  funext U
  by_cases hU : U ∈ A₀
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU,
      maximumOn_succ_eq_of_sep p m U n A hp hp1 (hsub U hU) hJ]
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]

/-! ## 5. Numerical witness: the entry *at* the point is invisible, the entry below is not

The two weights `w ≡ 1/2` and `w' = 1/2` except `w'(0) = 3/4` model "the changed entry is
the new position of a walker of `A`".  `H^w(0) = 0` for both (the sum is empty), so the
identity at the changed site itself holds; `H^w(1) = h^w(0)` differs strictly, which is the
failure one site higher predicted by `HA_succ_lt_of_wA_lt`. -/

theorem Hfix_zero_insensitive (w : ℕ → ℝ) : Hfix w 0 = 0 := by
  simp [Hfix]

theorem Hfix_sharp_at_changed_site :
    Hfix (fun v => if v = 0 then (3 / 4 : ℝ) else 1 / 2) 1
      < Hfix (fun _ => (1 / 2 : ℝ)) 1 := by
  rw [Hfix_succ, Hfix_succ, Hfix_zero_insensitive, Hfix_zero_insensitive]
  rw [hfix_eq, hfix_eq, hprev_zero]
  norm_num

end LocMoveWeight

/-! ## 6. Axiom audit -/


-- the exact statements, so that the interface can be read off the verification log


