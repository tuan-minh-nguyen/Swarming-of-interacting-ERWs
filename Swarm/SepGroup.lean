/-
Separated groups of walkers **at the actual interacting model**.

This file formalises, for the real trajectory `Swarming.Trajectory.trajectory p m U` of
`main_1d_revised.tex` (§2.3, Proposition `group`), the objects

* `w_n^A(x) = 1/2 + (p - 1/2) 1{∑_{i ∈ A} L_n^i(x) ≥ m}`            (eq. (wA))
* `h_n^A = h^w`, `H_n^A = H^w` (with the `ℤ` extension of (Hdef)),
* the separation condition (sep) and the observable `W_n^{I,J}` of (WA),

and proves, without any probabilistic hypothesis:

* `wA_mono_time`, `hA_antitone_time`, `HZ_diff_monotone_time` — the paper's (hmono), from
  the local-time monotonicity of the actual trajectory;
* `ell_eq_zero_of_sep` — under (sep) the walkers of `J` have never visited the current
  position of a walker of `I`, so their local time there is `0`;
* `sep_pos_succ_le` — one nearest-neighbour jump cannot destroy the two-site gap of (sep);
* `WA_nonneg_of_sep` — (Wpos): `W_n^{I,J} ≥ 0` on (sep);
* `WA_step` — the displayed one-step comparison of Proposition `group`,
  `W_{n+1}^{I,J} ≤ average_I H_n^{J^c}(X_{n+1}) - max_J H_n^{J^c}(X_{n+1})` on (sep);
* `rightProbability_le_wA_of_sep` / `wA_le_rightProbability_of_J` — the actual right
  probabilities against the group weights, `α_n^i ≤ w_n^{J^c}(X_n^i)` for `i ∈ I` and
  `α_n^j ≥ w_n^{J^c}(X_n^j)` for `j ∈ J` (the input `areas/martingale/README.md` records as
  the missing model interface of the drift inequality);
* `stepMean_HA_sub` and `WA_drift_le` — the exact two-point mean identity
  `α h(x) - (1-α) h(x-1) = 1 + (α - w(x))(h(x)+h(x-1))` transported to `H^w`, and the
  paper's drift bound `(Wdrift)` / strict bound `(Wstrict)` for the resulting one-step mean.

## Scope, stated explicitly

`stepMean` is the *exact* mean of `f` at the next position of onewalker, taken over the
single array coordinate that governs that departure, at a fixed state.  `WA_drift_le`
therefore says: the two-point mean of `W_{n+1}^{I,J}` is at most `W_n^{I,J}` on (sep).

It is **not** claimed here that `stepMean` is a conditional expectation `E[· | ℱ_n]`.
That identification needs (i) a nested filtration to which the trajectory *and* the group
weights `H_n^{J^c}` are adapted, and (ii) the joint law of the `|J|` next positions across
walkers (the step `E[max_J ·] ≥ max_J E[·]`).  Both remain separate obligations; this file
proves no instance of `prop:group`'s conditional-expectation statement, only the model-side
deterministic content listed above.  `ALL` of the hypotheses used are stated in the
signatures (`1/2 ≤ p`, `p ≤ 1`, `I`, `J` nonempty and disjoint, and `Sep p m U n I J`).

Build (no Lake project, no project build):

  LEAN_PATH=<root>/.build:<root>:...  lean SepGroup.lean
-/
import Swarm.Imports
import Swarm.Swarming
import Swarm.LocalTime
import Swarm.Trajectory
import Swarm.Reveal

set_option linter.unusedVariables false

namespace SepGroup

open Swarming Swarming.Model Swarming.Trajectory Swarming.Uniform Cookie

open Finset

variable {N : ℕ}

/-! ### (Hdef): the potential `H^w` on all of `ℤ` -/

/-- The paper's `H^w` extended to `ℤ`: `H^w(x) = x` for `x < 0`, and
`H^w(x) = ∑_{u<x} h^w(u)` for `x ≥ 0` (eq. (Hdef)). -/
noncomputable def HZ (w : ℕ → ℝ) (x : ℤ) : ℝ :=
  if x < 0 then (x : ℝ) else Hfix w x.toNat

lemma HZ_neg {w : ℕ → ℝ} {x : ℤ} (hx : x < 0) : HZ w x = (x : ℝ) := by
  simp [HZ, hx]

lemma HZ_nonneg {w : ℕ → ℝ} {x : ℤ} (hx : 0 ≤ x) : HZ w x = Hfix w x.toNat := by
  simp [HZ, not_lt.mpr hx]

@[simp] lemma HZ_zero (w : ℕ → ℝ) : HZ w 0 = 0 := by
  rw [HZ_nonneg le_rfl]
  simp [Hfix]

lemma HZ_nat (w : ℕ → ℝ) (n : ℕ) : HZ w (n : ℤ) = Hfix w n := by
  rw [HZ_nonneg (Int.natCast_nonneg n)]
  simp

/-- `Hfix w` is nondecreasing, since every `h^w(x) ≥ 1`. -/
lemma Hfix_monotone' {w : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1) :
    Monotone (Hfix w) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
      rw [Hfix_succ]
      have := one_le_hfix w hw0 hw1 b
      linarith

lemma Hfix_diff_nonneg {w w' : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    (hw0' : ∀ n, 0 < w' n) (hw1' : ∀ n, w' n ≤ 1) (hle : ∀ n, w n ≤ w' n) (n : ℕ) :
    0 ≤ Hfix w n - Hfix w' n := by
  have := Hfix_mono w w' hw0 hw1 hw0' hw1' hle n
  linarith

lemma HZ_diff_nonneg {w w' : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    (hw0' : ∀ n, 0 < w' n) (hw1' : ∀ n, w' n ≤ 1) (hle : ∀ n, w n ≤ w' n) (x : ℤ) :
    0 ≤ HZ w x - HZ w' x := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [HZ_neg hx, HZ_neg hx, sub_self]
  · rw [HZ_nonneg hx, HZ_nonneg hx]
    exact Hfix_diff_nonneg hw0 hw1 hw0' hw1' hle x.toNat

lemma HZ_mono {w : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1) :
    Monotone (HZ w) := by
  intro x y hxy
  rcases lt_or_ge x 0 with hx | hx
  · rw [HZ_neg hx]
    rcases lt_or_ge y 0 with hy | hy
    · rw [HZ_neg hy]
      exact_mod_cast hxy
    · rw [HZ_nonneg hy]
      have h1 : (0 : ℝ) ≤ Hfix w y.toNat := by
        have h := Hfix_ge w hw0 hw1 y.toNat
        have h2 : (0 : ℝ) ≤ (y.toNat : ℝ) := Nat.cast_nonneg _
        linarith
      have h2 : (x : ℝ) ≤ 0 := by exact_mod_cast hx.le
      linarith
  · rw [HZ_nonneg hx, HZ_nonneg (le_trans hx hxy)]
    exact Hfix_monotone' hw0 hw1 (Int.toNat_le_toNat hxy)

/-- **(hmono)**: for `w ≤ w'` the difference `H^w - H^{w'}` is nonnegative and
nondecreasing (on `ℤ`, with the convention of (Hdef)). -/
lemma HZ_diff_monotone {w w' : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    (hw0' : ∀ n, 0 < w' n) (hw1' : ∀ n, w' n ≤ 1) (hle : ∀ n, w n ≤ w' n) :
    Monotone fun x : ℤ => HZ w x - HZ w' x := by
  intro x y hxy
  change HZ w x - HZ w' x ≤ HZ w y - HZ w' y
  rcases lt_or_ge x 0 with hx | hx
  · rw [HZ_neg hx, HZ_neg hx, sub_self]
    exact HZ_diff_nonneg hw0 hw1 hw0' hw1' hle y
  · rw [HZ_nonneg hx, HZ_nonneg hx, HZ_nonneg (le_trans hx hxy),
    HZ_nonneg (le_trans hx hxy)]
    exact Hfix_diff_monotone w w' hw0 hw1 hw0' hw1' hle (Int.toNat_le_toNat hxy)

/-- `H^w(x+1) = H^w(x) + h^w(x)` for `x ≥ 0`. -/
lemma HZ_add_one {w : ℕ → ℝ} {x : ℤ} (hx : 0 ≤ x) :
    HZ w (x + 1) = HZ w x + hfix w x.toNat := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, x = (k : ℤ) := ⟨x.toNat, (Int.toNat_of_nonneg hx).symm⟩
  rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring]
  rw [HZ_nat, HZ_nat, Hfix_succ]
  simp

/-- `H^w(x-1) = H^w(x) - h^w(x-1)` for `x > 0`, with `h^w(-1) = 1`. -/
lemma HZ_sub_one {w : ℕ → ℝ} {x : ℤ} (hx : 0 < x) :
    HZ w (x - 1) = HZ w x - hprev w x.toNat := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, x = (k : ℤ) := ⟨x.toNat, (Int.toNat_of_nonneg hx.le).symm⟩
  match k with
  | 0 => exact absurd hx (by simp)
  | j + 1 =>
      rw [show (((j + 1 : ℕ)) : ℤ) - 1 = (j : ℤ) by push_cast; ring]
      simp only [Int.toNat_natCast]
      rw [HZ_nat, HZ_nat, hprev_succ, Hfix_succ]
      ring

/-! ### The model objects of Proposition `group` -/

namespace Model

variable (p : ℝ) (m : ℕ) (U : Array N)

/-- Position of walker `i` at time `n` in the actual interacting trajectory. -/
noncomputable def X (n : ℕ) (i : Fin N) : ℤ := (trajectory p m U n).pos i

/-- Local time of walker `i` at site `x` by time `n` (the stored one, which
`ell_eq_localTime` identifies with the path local time). -/
noncomputable def L (n : ℕ) (i : Fin N) (x : ℤ) : ℕ := (trajectory p m U n).ell i x

@[simp] lemma X_apply (n : ℕ) (i : Fin N) : X p m U n i = (trajectory p m U n).pos i := rfl

@[simp] lemma L_apply (n : ℕ) (i : Fin N) (x : ℤ) :
    L p m U n i x = (trajectory p m U n).ell i x := rfl

/-- The paper's group weight (wA):
`w_n^A(x) = 1/2 + (p - 1/2) 1{∑_{i ∈ A} L_n^i(x) ≥ m}`. -/
noncomputable def wA (n : ℕ) (A : Finset (Fin N)) (x : ℕ) : ℝ :=
  1 / 2 + (p - 1 / 2) * (if m ≤ ∑ i ∈ A, L p m U n i (x : ℤ) then (1 : ℝ) else 0)

/-- The paper's `h_n^A = h^{w_n^A}`. -/
noncomputable def hA (n : ℕ) (A : Finset (Fin N)) : ℕ → ℝ := hfix (wA p m U n A)

/-- The paper's `H_n^A = H^{w_n^A}` (on `ℤ`, eq. (Hdef)). -/
noncomputable def HA (n : ℕ) (A : Finset (Fin N)) (x : ℤ) : ℝ := HZ (wA p m U n A) x

/-- The paper's separation condition (sep). -/
def Sep (n : ℕ) (I J : Finset (Fin N)) : Prop :=
  (∀ i, 0 ≤ X p m U n i) ∧ ∀ i ∈ I, ∀ j ∈ J, runMax p m U j n + 2 ≤ X p m U n i

/-- The paper's observable (WA):
`W_n^{I,J} = |I|^{-1} ∑_{i ∈ I} H_n^{J^c}(X_n^i) - max_{j ∈ J} H_n^{J^c}(X_n^j)`. -/
noncomputable def WA (n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) :
    ℝ :=
  Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U n i)) -
    Swarming.Group.maximumOn J hJ (fun j => HA p m U n Jᶜ (X p m U n j))

/-! ### The weight takes only the two values `1/2` and `p` -/

lemma wA_eq_half_or (n : ℕ) (A : Finset (Fin N)) (x : ℕ) :
    wA p m U n A x = 1 / 2 ∨ wA p m U n A x = p := by
  unfold wA
  split_ifs with h
  · right; ring
  · left; ring

lemma wA_pos (hp : 1 / 2 ≤ p) (n : ℕ) (A : Finset (Fin N)) (x : ℕ) :
    0 < wA p m U n A x := by
  rcases wA_eq_half_or p m U n A x with h | h <;> rw [h] <;> linarith

lemma wA_le_one (hp1 : p ≤ 1) (n : ℕ) (A : Finset (Fin N)) (x : ℕ) :
    wA p m U n A x ≤ 1 := by
  rcases wA_eq_half_or p m U n A x with h | h <;> rw [h] <;> linarith

lemma one_half_le_wA (hp : 1 / 2 ≤ p) (n : ℕ) (A : Finset (Fin N)) (x : ℕ) :
    1 / 2 ≤ wA p m U n A x := by
  rcases wA_eq_half_or p m U n A x with h | h <;> rw [h] <;> linarith

/-! ### (hmono): monotonicity in time through the actual local times -/

/-- Local times of the actual trajectory are nondecreasing in time. -/
lemma L_mono_time {n n' : ℕ} (hnn' : n ≤ n') (i : Fin N) (x : ℤ) :
    L p m U n i x ≤ L p m U n' i x := by
  rw [L_apply, L_apply, ell_eq_localTime p m U n i x, ell_eq_localTime p m U n' i x]
  exact localTime_mono (fun k => (trajectory p m U k).pos i) hnn' x

lemma wA_mono_time (hp : 1 / 2 ≤ p) {n n' : ℕ} (hnn' : n ≤ n')
    (A : Finset (Fin N)) (x : ℕ) :
    wA p m U n A x ≤ wA p m U n' A x := by
  have hsum : (∑ i ∈ A, L p m U n i (x : ℤ)) ≤ ∑ i ∈ A, L p m U n' i (x : ℤ) :=
    sum_le_sum fun i _ => L_mono_time p m U hnn' i (x : ℤ)
  have hp' : (0 : ℝ) ≤ p - 1 / 2 := by linarith
  by_cases h : m ≤ ∑ i ∈ A, L p m U n i (x : ℤ)
  · have h' : m ≤ ∑ i ∈ A, L p m U n' i (x : ℤ) := le_trans h hsum
    simp only [wA, if_pos h, if_pos h']
    linarith
  · by_cases h' : m ≤ ∑ i ∈ A, L p m U n' i (x : ℤ)
    · simp only [wA, if_neg h, if_pos h']
      nlinarith
    · simp only [wA, if_neg h, if_neg h']
      linarith

/-- **(hmono)**, first half: `w_n^A` nondecreasing in `n` makes `h_n^A` nonincreasing. -/
lemma hA_antitone_time (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {n n' : ℕ} (hnn' : n ≤ n')
    (A : Finset (Fin N)) (x : ℕ) :
    hfix (wA p m U n' A) x ≤ hfix (wA p m U n A) x :=
  hfix_mono (wA p m U n A) (wA p m U n' A) (wA_pos p m U hp n A) (wA_le_one p m U hp1 n A)
    (wA_pos p m U hp n' A) (wA_le_one p m U hp1 n' A)
    (fun y => wA_mono_time p m U hp hnn' A y) x

/-- **(hmono)**, second half: `H_n^A - H_{n+1}^A` is nonnegative and nondecreasing in `x`. -/
lemma HZ_diff_monotone_time (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (A : Finset (Fin N)) :
    Monotone fun x : ℤ => HA p m U n A x - HA p m U (n + 1) A x :=
  HZ_diff_monotone (wA_pos p m U hp n A) (wA_le_one p m U hp1 n A)
    (wA_pos p m U hp (n + 1) A) (wA_le_one p m U hp1 (n + 1) A)
    (wA_mono_time p m U hp (Nat.le_succ n) A)

lemma HZ_diff_nonneg_time (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (A : Finset (Fin N)) (x : ℤ) :
    0 ≤ HA p m U n A x - HA p m U (n + 1) A x :=
  HZ_diff_nonneg (wA_pos p m U hp n A) (wA_le_one p m U hp1 n A)
    (wA_pos p m U hp (n + 1) A) (wA_le_one p m U hp1 (n + 1) A)
    (wA_mono_time p m U hp (Nat.le_succ n) A) x

end Model

/-! ### Shared finite-sum bookkeeping -/

/-- A sum over a `Finset` of `Fin N` as a sum over the whole index set. -/
lemma sum_mem_univ_eq (s : Finset (Fin N)) (f : Fin N → ℕ) :
    (∑ k ∈ s, f k) = ∑ k, if k ∈ s then f k else 0 := by
  rw [← Finset.sum_filter (s := Finset.univ) (p := fun k => k ∈ s)]
  congr 1
  ext k
  simp

/-- Removing the diagonal term from a sum over a `Finset` containing `i`. -/
lemma sum_ite_diag {α : Type*} [DecidableEq α] {s : Finset α} {i : α} (hi : i ∈ s)
    (f : α → ℕ) :
    (∑ k ∈ s, (if k = i then 0 else f k)) = ∑ k ∈ s.erase i, f k := by
  conv_lhs => rw [← Finset.insert_erase hi]
  rw [Finset.sum_insert (by simp)]
  rw [if_pos rfl, zero_add]
  exact Finset.sum_congr rfl fun k hk => by
    rw [if_neg (Finset.ne_of_mem_erase hk)]

/-- If `c` is a lower bound for `f` on the nonempty `s`, it is at most the average. -/
lemma le_average_of_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → ℝ} {c : ℝ}
    (h : ∀ i ∈ s, c ≤ f i) : c ≤ Swarming.Group.average s f := by
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hs
  have hsum : (s.card : ℝ) * c ≤ ∑ i ∈ s, f i := by
    have h' := Finset.card_nsmul_le_sum s f c h
    simpa [nsmul_eq_mul] using h'
  rw [Swarming.Group.average, le_div_iff₀ hcard]
  linarith

/-- For a monotone `H`, `max_{j ∈ t} H(x_j) = H(max_{j ∈ t} x_j)`. -/
theorem maximumOn_comp {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {H : ℤ → ℝ}
    (hH : Monotone H) (x : ι → ℤ) :
    Swarming.Group.maximumOn t ht (fun j => H (x j)) = H (t.sup' ht x) := by
  rw [Swarming.Group.maximumOn]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le ht _ ?_
    intro j hj
    exact hH (Finset.le_sup' x hj)
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' ht x
    calc H (t.sup' ht x) = H (x j) := by rw [hjeq]
      _ ≤ t.sup' ht (fun j => H (x j)) := Finset.le_sup' (fun j => H (x j)) hj

/-- The average of a function plus a constant is the average plus the constant. -/
lemma average_add_const {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) (c : ℝ) :
    Swarming.Group.average s (fun i => f i + c) = Swarming.Group.average s f + c := by
  have hcard : (s.card : ℝ) ≠ 0 := by
    have : 0 < s.card := Finset.card_pos.2 hs
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  dsimp [Swarming.Group.average]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The maximum of a function plus a constant is the maximum plus the constant. -/
lemma maximumOn_add_const {ι : Type*} {t : Finset ι} (ht : t.Nonempty) (f : ι → ℝ) (c : ℝ) :
    Swarming.Group.maximumOn t ht (fun j => f j + c) = Swarming.Group.maximumOn t ht f + c := by
  rw [Swarming.Group.maximumOn, Swarming.Group.maximumOn]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le ht _ ?_
    intro j hj
    have := Finset.le_sup' f hj
    linarith
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' ht f
    rw [hjeq]
    exact Finset.le_sup' (fun j => f j + c) hj

namespace Model

variable (p : ℝ) (m : ℕ) (U : Array N)

/-! ### (sep) and the locality of local times -/

lemma le_runMax_of_le (n : ℕ) (j : Fin N) {t : ℕ} (ht : t ≤ n) :
    (trajectory p m U t).pos j ≤ runMax p m U j n :=
  Finset.le_sup' (fun t => (trajectory p m U t).pos j)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))

lemma le_runMax_pos (n : ℕ) (j : Fin N) : X p m U n j ≤ runMax p m U j n := by
  rw [X_apply]
  exact le_runMax p m U j n

/-- The local time at a site strictly above the running maximum vanishes. -/
lemma L_eq_zero_of_gt_runMax {n : ℕ} {j : Fin N} {x : ℤ} (hx : runMax p m U j n < x) :
    L p m U n j x = 0 := by
  rw [L_apply, ell_eq_localTime p m U n j x]
  refine localTime_eq_zero_of_lt_all (fun k => (trajectory p m U k).pos j) n ?_
  intro t ht hcontra
  have h1 := le_runMax_of_le p m U n j ht
  omega

/-- **Locality under (sep)**: no walker of `J` has ever visited the current position
of a walker of `I`. -/
lemma ell_eq_zero_of_sep {n : ℕ} {I J : Finset (Fin N)} (hsep : Sep p m U n I J)
    {i : Fin N} (hi : i ∈ I) {j : Fin N} (hj : j ∈ J) :
    L p m U n j (X p m U n i) = 0 := by
  refine L_eq_zero_of_gt_runMax p m U ?_
  have := hsep.2 i hi j hj
  omega

lemma sum_ell_eq_zero_of_sep {n : ℕ} {I J : Finset (Fin N)} (hsep : Sep p m U n I J)
    {i : Fin N} (hi : i ∈ I) :
    (∑ j ∈ J, L p m U n j (X p m U n i)) = 0 :=
  Finset.sum_eq_zero fun j hj => ell_eq_zero_of_sep p m U hsep hi hj

/-- One nearest-neighbour jump moves a walker down by at most one. -/
lemma drivenStep_ge_neg_one (u α : ℝ) : -1 ≤ drivenStep u α := by
  unfold drivenStep
  split <;> norm_num

lemma pos_sub_one_le_succ (n : ℕ) (j : Fin N) :
    (trajectory p m U n).pos j - 1 ≤ (trajectory p m U (n + 1)).pos j := by
  rw [trajectory_succ, nextWalkState_pos, nextPos]
  have := drivenStep_ge_neg_one
    (U (j, (trajectory p m U n).pos j, (trajectory p m U n).ell j ((trajectory p m U n).pos j)))
    (rightProbability p m (trajectory p m U n).ell j ((trajectory p m U n).pos j))
  omega

/-- Under (sep) at time `n`, after one jump every walker of `J` is still to the left of
every walker of `I`: the two-site gap survives a nearest-neighbour step. -/
lemma sep_pos_succ_le {n : ℕ} {I J : Finset (Fin N)} (hsep : Sep p m U n I J)
    {i : Fin N} (hi : i ∈ I) {j : Fin N} (hj : j ∈ J) :
    X p m U (n + 1) j ≤ X p m U (n + 1) i := by
  have hj1 : X p m U (n + 1) j ≤ X p m U n j + 1 := pos_succ_le p m U n j
  have hi1 : X p m U n i - 1 ≤ X p m U (n + 1) i := pos_sub_one_le_succ p m U n i
  have hMj : X p m U n j ≤ runMax p m U j n := le_runMax_pos p m U n j
  have hgap := hsep.2 i hi j hj
  omega

/-! ### (Wpos): nonnegativity of the observable on (sep) -/

theorem HA_maximum_eq (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (A : Finset (Fin N))
    {ι : Type*} {t : Finset ι} (ht : t.Nonempty) (x : ι → ℤ) :
    Swarming.Group.maximumOn t ht (fun j => HA p m U n A (x j)) =
      HA p m U n A (t.sup' ht x) :=
  maximumOn_comp ht
    (HZ_mono (wA_pos p m U hp n A) (wA_le_one p m U hp1 n A)) x

/-- **(Wpos)**: on (sep), `W_n^{I,J} ≥ min_{i ∈ I} X_n^i - max_{j ∈ J} X_n^j ≥ 0`. -/
theorem WA_nonneg_of_sep (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {I J : Finset (Fin N)}
    (hI : I.Nonempty) (hJ : J.Nonempty) (hsep : Sep p m U n I J) :
    0 ≤ WA p m U n I J hI hJ := by
  have hmono : Monotone (HA p m U n Jᶜ) :=
    HZ_mono (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ)
  have hle : J.sup' hJ (fun j => X p m U n j) ≤ I.inf' hI (fun i => X p m U n i) :=
    Finset.sup'_le hJ _ fun j hj =>
      Finset.le_inf' hI _ fun i hi => by
        have h1 : X p m U n j ≤ runMax p m U j n := le_runMax_pos p m U n j
        have h2 := hsep.2 i hi j hj
        omega
  have hmin : HA p m U n Jᶜ (J.sup' hJ (fun j => X p m U n j))
      ≤ HA p m U n Jᶜ (I.inf' hI (fun i => X p m U n i)) := hmono hle
  have havg : HA p m U n Jᶜ (I.inf' hI (fun i => X p m U n i))
      ≤ Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U n i)) :=
    le_average_of_le hI fun i hi => hmono (Finset.inf'_le (fun i => X p m U n i) hi)
  rw [WA, HA_maximum_eq p m U hp hp1 n Jᶜ hJ (fun j => X p m U n j)]
  linarith

/-! ### The one-step comparison of Proposition `group` -/

/-- The paper's displayed one-step estimate: on (sep) at time `n`,
`W_{n+1}^{I,J}` is at most the observable computed with the *old* weights `H_n^{J^c}` at the
*new* positions.  Proof: `H_n - H_{n+1}` is nonnegative and nondecreasing (hmono), and after
one jump the walkers of `J` are still left of those of `I`. -/
theorem WA_step (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {I J : Finset (Fin N)}
    (hI : I.Nonempty) (hJ : J.Nonempty) (hsep : Sep p m U n I J) :
    WA p m U (n + 1) I J hI hJ ≤
      Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U (n + 1) i)) -
        Swarming.Group.maximumOn J hJ (fun j => HA p m U n Jᶜ (X p m U (n + 1) j)) := by
  have hD : Monotone fun x : ℤ => HA p m U n Jᶜ x - HA p m U (n + 1) Jᶜ x :=
    HZ_diff_monotone_time p m U hp hp1 n Jᶜ
  have hsep' : ∀ i ∈ I, ∀ j ∈ J, X p m U (n + 1) j ≤ X p m U (n + 1) i :=
    fun i hi j hj => sep_pos_succ_le p m U hsep hi hj
  have hmain := Swarming.Group.updated_average_le_original_average
    (s := I) (t := J) (x := fun k => X p m U (n + 1) k)
    (H := fun x => HA p m U n Jᶜ x)
    (D := fun x => HA p m U n Jᶜ x - HA p m U (n + 1) Jᶜ x) hD hsep' hI hJ
  have hHD : ∀ k : Fin N, HA p m U n Jᶜ (X p m U (n + 1) k)
        - (HA p m U n Jᶜ (X p m U (n + 1) k) - HA p m U (n + 1) Jᶜ (X p m U (n + 1) k))
      = HA p m U (n + 1) Jᶜ (X p m U (n + 1) k) := fun k => sub_sub_cancel _ _
  simpa only [WA, hHD] using hmain

end Model

/-! ### The actual right probabilities against the group weights -/

namespace Model

variable (p : ℝ) (m : ℕ) (U : Array N)

/-- Under (sep) and `i ∈ I`, `i ∉ J`, every visit paid by a walker of `J` to the site
`X_n^i` is zero, so the "other walkers" sum defining `α_n^i` is dominated by the group sum
defining `w_n^{J^c}(X_n^i)`. -/
lemma otherVisits_le_groupSum {n : ℕ} {I J : Finset (Fin N)} (hid : Disjoint I J)
    (hsep : Sep p m U n I J) {i : Fin N} (hi : i ∈ I) :
    otherVisits (trajectory p m U n).ell i (X p m U n i)
      ≤ ∑ k ∈ Jᶜ, L p m U n k (X p m U n i) := by
  have hiJ : i ∉ J := fun h => Finset.disjoint_left.mp hid hi h
  have hsplit : (∑ k, (if k = i then 0 else L p m U n k (X p m U n i)))
      = (∑ k ∈ J, (if k = i then 0 else L p m U n k (X p m U n i)))
        + ∑ k ∈ Jᶜ, (if k = i then 0 else L p m U n k (X p m U n i)) :=
    (Finset.sum_add_sum_compl J _).symm
  have hJzero : (∑ k ∈ J, (if k = i then 0 else L p m U n k (X p m U n i))) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hki : ¬ (k = i) := fun h => hiJ (h ▸ hk)
    rw [if_neg hki]
    exact ell_eq_zero_of_sep p m U hsep hi hk
  have herase : (∑ k ∈ Jᶜ, (if k = i then 0 else L p m U n k (X p m U n i)))
      = ∑ k ∈ Jᶜ.erase i, L p m U n k (X p m U n i) :=
    sum_ite_diag (Finset.mem_compl.mpr hiJ) _
  have hsub : (∑ k ∈ Jᶜ.erase i, L p m U n k (X p m U n i))
      ≤ ∑ k ∈ Jᶜ, L p m U n k (X p m U n i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Jᶜ)
      (fun k _ _ => Nat.zero_le _)
  calc otherVisits (trajectory p m U n).ell i (X p m U n i)
      = ∑ k, (if k = i then 0 else L p m U n k (X p m U n i)) := rfl
    _ = _ + _ := hsplit
    _ = 0 + ∑ k ∈ Jᶜ.erase i, L p m U n k (X p m U n i) := by rw [hJzero, herase]
    _ = ∑ k ∈ Jᶜ.erase i, L p m U n k (X p m U n i) := zero_add _
    _ ≤ ∑ k ∈ Jᶜ, L p m U n k (X p m U n i) := hsub

/-- For `j ∈ J` the group sum is a sub-sum of the "other walkers" sum, so it is dominated
by it (no separation needed, only `j ∈ J`). -/
lemma groupSum_le_otherVisits {n : ℕ} {J : Finset (Fin N)} {j : Fin N} (hj : j ∈ J) :
    (∑ k ∈ Jᶜ, L p m U n k (X p m U n j))
      ≤ otherVisits (trajectory p m U n).ell j (X p m U n j) := by
  have hjJ : j ∉ Jᶜ := by
    simp only [Finset.mem_compl, not_not]
    exact hj
  rw [sum_mem_univ_eq]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k ∈ Jᶜ
  · have hkj : ¬ (k = j) := fun h => hjJ (h ▸ hk)
    rw [if_pos hk, if_neg hkj]
    exact le_rfl
  · rw [if_neg hk]
    exact Nat.zero_le _

/-- The paper's comparison `α_n^i ≤ w_n^{J^c}(X_n^i)` for `i ∈ I` on (sep). -/
theorem rightProbability_le_wA_of_sep (hp : 1 / 2 ≤ p) {n : ℕ} {I J : Finset (Fin N)}
    (hid : Disjoint I J) (hsep : Sep p m U n I J) {i : Fin N} (hi : i ∈ I) :
    rightProbability p m (trajectory p m U n).ell i (X p m U n i)
      ≤ wA p m U n Jᶜ (X p m U n i).toNat := by
  have hx : 0 ≤ X p m U n i := hsep.1 i
  have hcast : (((X p m U n i).toNat : ℕ) : ℤ) = X p m U n i := Int.toNat_of_nonneg hx
  have hsum := otherVisits_le_groupSum p m U hid hsep hi
  by_cases hexc : Excited m (trajectory p m U n).ell i (X p m U n i)
  · have hcond : m ≤ ∑ k ∈ Jᶜ, L p m U n k (X p m U n i) := le_trans hexc hsum
    have hcond' : m ≤ ∑ k ∈ Jᶜ, L p m U n k ((X p m U n i).toNat : ℤ) := by
      rw [hcast]
      exact hcond
    unfold rightProbability wA
    rw [if_pos hexc, if_pos hcond']
    linarith
  · unfold rightProbability wA
    rw [if_neg hexc]
    split_ifs with h <;> linarith

/-- The paper's comparison `α_n^j ≥ w_n^{J^c}(X_n^j)` for `j ∈ J` (only needs `j ∈ J` and
`X_n^j ≥ 0`; `J^c` never contains `j`). -/
theorem wA_le_rightProbability_of_J (hp : 1 / 2 ≤ p) {n : ℕ} {J : Finset (Fin N)}
    {j : Fin N} (hj : j ∈ J) (hx : 0 ≤ X p m U n j) :
    wA p m U n Jᶜ (X p m U n j).toNat
      ≤ rightProbability p m (trajectory p m U n).ell j (X p m U n j) := by
  have hcast : (((X p m U n j).toNat : ℕ) : ℤ) = X p m U n j := Int.toNat_of_nonneg hx
  have hle := groupSum_le_otherVisits p m U (n := n) hj
  by_cases hexc : Excited m (trajectory p m U n).ell j (X p m U n j)
  · unfold rightProbability wA
    rw [if_pos hexc]
    split_ifs with h <;> linarith
  · have hcond : ¬ (m ≤ ∑ k ∈ Jᶜ, L p m U n k (X p m U n j)) :=
      fun h => hexc (le_trans h hle)
    have hcond' : ¬ (m ≤ ∑ k ∈ Jᶜ, L p m U n k ((X p m U n j).toNat : ℤ)) := by
      rw [hcast]
      exact hcond
    unfold rightProbability wA
    rw [if_neg hexc, if_neg hcond']
    linarith

/-! ### The exact two-point mean and the drift bound -/

/-- The exact mean of `f` at the next position of walker `k` at time `n`, taken over the
single array coordinate governing that departure (the two-point average with the model's
right probability).  This is a state function, not a conditional expectation. -/
noncomputable def stepMean (n : ℕ) (k : Fin N) (f : ℤ → ℝ) : ℝ :=
  rightProbability p m (trajectory p m U n).ell k (X p m U n k) * f (X p m U n k + 1)
    + (1 - rightProbability p m (trajectory p m U n).ell k (X p m U n k))
        * f (X p m U n k - 1)

/-- The two-point identity for one walker step at a fixed state: for `x ≥ 0`,
`α H^w(x+1) + (1-α) H^w(x-1) - H^w(x) = 1 + (α - w(x)) (h^w(x) + h^w(x-1))`. -/
theorem two_point_HZ {w : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) {x : ℤ} (hx : 0 ≤ x) (α : ℝ) :
    α * HZ w (x + 1) + (1 - α) * HZ w (x - 1) - HZ w x
      = 1 + (α - w x.toNat) * (hfix w x.toNat + hprev w x.toNat) := by
  have hup : HZ w (x + 1) = HZ w x + hfix w x.toNat := HZ_add_one hx
  have hdn : HZ w (x - 1) = HZ w x - hprev w x.toNat := by
    rcases eq_or_lt_of_le hx with h0 | h0
    · rw [← h0, HZ_neg (show ((0 : ℤ) - 1) < 0 by norm_num), HZ_zero]
      simp
    · exact HZ_sub_one h0
  rw [hup, hdn]
  have h := drift_identity w (fun n => ne_of_gt (hw0 n)) x.toNat α
  linarith [h]

/-- `h^w(-1) = 1` and `h^w ≥ 1` give `hprev ≥ 1`. -/
lemma one_le_hprev {w : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1) (k : ℕ) :
    1 ≤ hprev w k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · rw [show k = (k - 1) + 1 by omega, hprev_succ]
    exact one_le_hfix w hw0 hw1 (k - 1)

/-- The one-step mean of `H_n^{A}` at walker `k`, in the paper's form. -/
theorem stepMean_HA_sub (hp : 1 / 2 ≤ p) {n : ℕ} {A : Finset (Fin N)} {k : Fin N}
    (hx : 0 ≤ X p m U n k) :
    stepMean p m U n k (HA p m U n A) - HA p m U n A (X p m U n k) =
      1 + (rightProbability p m (trajectory p m U n).ell k (X p m U n k)
            - wA p m U n A (X p m U n k).toNat)
          * (hfix (wA p m U n A) (X p m U n k).toNat
              + hprev (wA p m U n A) (X p m U n k).toNat) :=
  two_point_HZ (wA_pos p m U hp n A) hx _

/-- The average is monotone in the summand. -/
lemma average_mono {ι : Type*} {s : Finset ι} {f g : ι → ℝ} (h : ∀ i ∈ s, f i ≤ g i) :
    Swarming.Group.average s f ≤ Swarming.Group.average s g := by
  have h1 : (∑ i ∈ s, f i) ≤ ∑ i ∈ s, g i := Finset.sum_le_sum h
  dsimp [Swarming.Group.average]
  exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)

/-- **(Wdrift)/(Wstrict) at the level of the exact one-step mean.**  On (sep), the
two-point mean of `W_{n+1}^{I,J}` is at most `W_n^{I,J}`; the strict form
`-(1/|I|) ∑_{i ∈ I} (w_n^{J^c}(X_n^i) - α_n^i)(h + h^-)` is proved by the same chain.

All hypotheses are explicit: `1/2 ≤ p`, `I`, `J` nonempty and disjoint, and (sep) at time
`n`.  Passing from this two-point mean to `E[· | ℱ_n]` is *not* done here. -/
theorem WA_drift_le (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {I J : Finset (Fin N)}
    (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) (hsep : Sep p m U n I J) :
    Swarming.Group.average I (fun i => stepMean p m U n i (HA p m U n Jᶜ)) -
        Swarming.Group.maximumOn J hJ (fun j => stepMean p m U n j (HA p m U n Jᶜ))
      ≤ WA p m U n I J hI hJ := by
  have hpos := wA_pos p m U hp n Jᶜ
  have hone := wA_le_one p m U hp1 n Jᶜ
  have hterm : ∀ k : Fin N, 0 < hfix (wA p m U n Jᶜ) (X p m U n k).toNat
      + hprev (wA p m U n Jᶜ) (X p m U n k).toNat := by
    intro k
    have h1 := one_le_hfix (wA p m U n Jᶜ) hpos hone (X p m U n k).toNat
    have h2 := one_le_hprev hpos hone (X p m U n k).toNat
    linarith
  have hIle : ∀ i ∈ I, stepMean p m U n i (HA p m U n Jᶜ)
      ≤ HA p m U n Jᶜ (X p m U n i) + 1 := by
    intro i hi
    have h1 := stepMean_HA_sub p m U hp (n := n) (A := Jᶜ) (k := i) (hsep.1 i)
    have h2 : rightProbability p m (trajectory p m U n).ell i (X p m U n i)
        - wA p m U n Jᶜ (X p m U n i).toNat ≤ 0 := by
      have h := rightProbability_le_wA_of_sep p m U hp hid hsep hi
      linarith
    have h3 := mul_nonpos_of_nonpos_of_nonneg h2 (le_of_lt (hterm i))
    linarith [h1, h3]
  have hJge : ∀ j ∈ J, HA p m U n Jᶜ (X p m U n j) + 1
      ≤ stepMean p m U n j (HA p m U n Jᶜ) := by
    intro j hj
    have h1 := stepMean_HA_sub p m U hp (n := n) (A := Jᶜ) (k := j) (hsep.1 j)
    have h2 : 0 ≤ rightProbability p m (trajectory p m U n).ell j (X p m U n j)
        - wA p m U n Jᶜ (X p m U n j).toNat := by
      have h := wA_le_rightProbability_of_J p m U hp hj (hsep.1 j)
      linarith
    have h3 := mul_nonneg h2 (le_of_lt (hterm j))
    linarith [h1, h3]
  have havg : Swarming.Group.average I (fun i => stepMean p m U n i (HA p m U n Jᶜ))
      ≤ Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U n i)) + 1 := by
    calc Swarming.Group.average I (fun i => stepMean p m U n i (HA p m U n Jᶜ))
        ≤ Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U n i) + 1) :=
          average_mono hIle
      _ = Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U n i)) + 1 :=
          average_add_const hI _ 1
  have hmax : Swarming.Group.maximumOn J hJ
        (fun j => HA p m U n Jᶜ (X p m U n j) + 1)
      ≤ Swarming.Group.maximumOn J hJ (fun j => stepMean p m U n j (HA p m U n Jᶜ)) :=
    Finset.sup'_le hJ _ fun j hj =>
      le_trans (hJge j hj) (Finset.le_sup' (fun j => stepMean p m U n j (HA p m U n Jᶜ)) hj)
  rw [maximumOn_add_const hJ (fun j => HA p m U n Jᶜ (X p m U n j)) 1] at hmax
  rw [WA]
  linarith

/-- Comparison of potentials on a prefix of the site axis: if `w ≤ w'` on `{0,…,k}`, then
`h^{w'}(k) ≤ h^{w}(k)`.  (The paper uses this when only the sites below the running maximum
are controlled.) -/
lemma hfix_mono_prefix {w w' : ℕ → ℝ} (hw0 : ∀ n, 0 < w n) (hw1 : ∀ n, w n ≤ 1)
    (hw0' : ∀ n, 0 < w' n) (hw1' : ∀ n, w' n ≤ 1) (k : ℕ)
    (hle : ∀ u ≤ k, w u ≤ w' u) : hfix w' k ≤ hfix w k := by
  induction k with
  | zero =>
      rw [hfix_eq, hfix_eq, hprev_zero, hprev_zero]
      exact step_mono (hw0 0) (hle 0 le_rfl) le_rfl
  | succ k ih =>
      have ih' : hfix w' k ≤ hfix w k := ih (fun u hu => hle u (Nat.le_succ_of_le hu))
      rw [hfix_eq, hfix_eq, hprev_succ, hprev_succ]
      calc (1 + (1 - w' (k + 1)) * hfix w' k) / w' (k + 1)
          ≤ (1 + (1 - w' (k + 1)) * hfix w k) / w' (k + 1) :=
            step_mono_h (hw0' (k + 1)) (hw1' (k + 1)) ih'
        _ ≤ (1 + (1 - w (k + 1)) * hfix w k) / w (k + 1) :=
            step_mono (hw0 (k + 1)) (hle (k + 1) le_rfl) (one_le_hfix w hw0 hw1 k)

/-- The paper's mark weight `ω_i = 1/2 + (p-1/2) B_i` read as a weight on `ℕ`
(its values at negative sites are `1`, which is the boundary convention `h(-1)=1`). -/
noncomputable def omegaN (i : Fin N) : ℕ → ℝ := fun x => omegaAt p m U i (x : ℤ)

lemma omegaAt_eq_half_or (i : Fin N) (x : ℤ) :
    omegaAt p m U i x = 1 / 2 ∨ omegaAt p m U i x = p := by
  unfold omegaAt
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma omegaAt_pos (hp : 1 / 2 ≤ p) (i : Fin N) (x : ℤ) : 0 < omegaAt p m U i x := by
  rcases omegaAt_eq_half_or p m U i x with h | h <;> rw [h] <;> linarith

lemma omegaAt_le_one (hp1 : p ≤ 1) (i : Fin N) (x : ℤ) : omegaAt p m U i x ≤ 1 := by
  rcases omegaAt_eq_half_or p m U i x with h | h <;> rw [h] <;> linarith

lemma one_half_le_omegaAt (hp : 1 / 2 ≤ p) (i : Fin N) (x : ℤ) :
    1 / 2 ≤ omegaAt p m U i x := by
  rcases omegaAt_eq_half_or p m U i x with h | h <;> rw [h] <;> linarith

/-- **(hcomp)**, first assertion: for `x < M_n^i` the group weight `w_n^{J^c}` dominates the
mark weight `ω_i` of walker `i` (via the paper's (reveal): a marked site below the running
maximum has been left `m` times, hence is excited for the group). -/
theorem omegaAt_le_wA (hp : 1 / 2 ≤ p) {n : ℕ} {J : Finset (Fin N)} {i : Fin N}
    (hiJ : i ∈ Jᶜ) {x : ℕ} (hxM : (x : ℤ) < runMax p m U i n) :
    omegaAt p m U i (x : ℤ) ≤ wA p m U n Jᶜ x := by
  by_cases hmark : SiteMark p m U i (x : ℤ)
  · have homega : omegaAt p m U i (x : ℤ) = p := by simp [omegaAt, hmark]
    rw [homega]
    have hR : m ≤ localTime (fun k => (trajectory p m U k).pos i) n (x : ℤ) :=
      reveal_runMax hp m U i (Int.natCast_nonneg x) hmark (by omega)
    have h1 : m ≤ L p m U n i (x : ℤ) := by
      rw [L_apply, ell_eq_localTime p m U n i (x : ℤ)]
      exact hR
    have h2 : m ≤ ∑ k ∈ Jᶜ, L p m U n k (x : ℤ) :=
      le_trans h1 (Finset.single_le_sum (f := fun k => L p m U n k (x : ℤ))
        (fun k _ => Nat.zero_le _) hiJ)
    unfold wA
    rw [if_pos h2]
    linarith
  · have homega : omegaAt p m U i (x : ℤ) = 1 / 2 := by simp [omegaAt, hmark]
    rw [homega]
    exact one_half_le_wA p m U hp n Jᶜ x

/-- **(hcomp)**, second assertion: `h_n^{J^c}(x) ≤ h_i(x)` for `x < M_n^i`. -/
theorem hcomp_h (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {J : Finset (Fin N)} {i : Fin N}
    (hiJ : i ∈ Jᶜ) {x : ℕ} (hxM : (x : ℤ) < runMax p m U i n) :
    hfix (wA p m U n Jᶜ) x ≤ hfix (omegaN p m U i) x :=
  hfix_mono_prefix (w := omegaN p m U i) (w' := wA p m U n Jᶜ)
    (fun u => omegaAt_pos p m U hp i (u : ℤ)) (fun u => omegaAt_le_one p m U hp1 i (u : ℤ))
    (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) x
    (fun u hu =>
      omegaAt_le_wA p m U hp hiJ (x := u)
        (lt_of_le_of_lt (show (u : ℤ) ≤ (x : ℤ) by exact_mod_cast hu) hxM))

/-- `h^w(k-1)` for `k > 0`, in terms of `hfix`. -/
lemma hprev_eq_hfix_sub_one {w : ℕ → ℝ} {k : ℕ} (hk : 0 < k) :
    hprev w k = hfix w (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  rw [hprev_succ]
  simp

/-- (hrec) at a site of weight `1/2`: `h^w(r) = h^w(r-1) + 2`. -/
lemma hfix_eq_two_add_hprev {w : ℕ → ℝ} {r : ℕ} (hr : w r = 1 / 2) :
    hfix w r = hprev w r + 2 := by
  rw [hfix_eq, hr]
  field_simp
  ring

/-- **(hcomp)**, third assertion: at the running maximum `R = M_n^i`,
`h_n^{J^c}(R) ≤ h_i(R-1) + 2`.  (Two branches, exactly as in the paper: if the group weight
at `R` is `p` the prefix comparison applies up to `R`; if it is `1/2` the boundary increment
`h^w(R) = h^w(R-1) + 2` and the prefix comparison at `R-1` give the bound.) -/
theorem hcomp_h_runMax (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {J : Finset (Fin N)}
    {i : Fin N} (hiJ : i ∈ Jᶜ) :
    hfix (wA p m U n Jᶜ) (runMax p m U i n).toNat
      ≤ hprev (omegaN p m U i) (runMax p m U i n).toNat + 2 := by
  have hR0 : (0 : ℤ) ≤ runMax p m U i n := by
    have h1 : (trajectory p m U 0).pos i ≤ runMax p m U i n :=
      le_runMax_of_le p m U n i (Nat.zero_le n)
    simpa using h1
  have hRcast : (((runMax p m U i n).toNat : ℕ) : ℤ) = runMax p m U i n :=
    Int.toNat_of_nonneg hR0
  by_cases hcase : wA p m U n Jᶜ (runMax p m U i n).toNat = p
  · have hle : ∀ u ≤ (runMax p m U i n).toNat, omegaN p m U i u ≤ wA p m U n Jᶜ u := by
      intro u hu
      rcases lt_or_eq_of_le hu with hlt | heq
      · refine omegaAt_le_wA p m U hp hiJ (x := u) ?_
        have h1 : (u : ℤ) < ((runMax p m U i n).toNat : ℤ) := by exact_mod_cast hlt
        rwa [hRcast] at h1
      · subst heq
        have h2 : omegaAt p m U i (runMax p m U i n) ≤ p := by
          rcases omegaAt_eq_half_or p m U i (runMax p m U i n) with h | h <;> rw [h] <;> linarith
        calc omegaN p m U i (runMax p m U i n).toNat
            = omegaAt p m U i ((runMax p m U i n).toNat : ℤ) := rfl
          _ = omegaAt p m U i (runMax p m U i n) := by rw [hRcast]
          _ ≤ p := h2
          _ = wA p m U n Jᶜ (runMax p m U i n).toNat := hcase.symm
    calc hfix (wA p m U n Jᶜ) (runMax p m U i n).toNat
        ≤ hfix (omegaN p m U i) (runMax p m U i n).toNat :=
          hfix_mono_prefix (w := omegaN p m U i) (w' := wA p m U n Jᶜ)
            (fun u => omegaAt_pos p m U hp i (u : ℤ))
            (fun u => omegaAt_le_one p m U hp1 i (u : ℤ))
            (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) _ hle
      _ ≤ hprev (omegaN p m U i) (runMax p m U i n).toNat + 2 :=
          Swarming.Constants.hfix_le_hprev_add_two (omegaN p m U i)
            (fun u => omegaAt_pos p m U hp i (u : ℤ))
            (fun u => omegaAt_le_one p m U hp1 i (u : ℤ))
            (fun u => one_half_le_omegaAt p m U hp i (u : ℤ)) _
  · have hw : wA p m U n Jᶜ (runMax p m U i n).toNat = 1 / 2 := by
      rcases wA_eq_half_or p m U n Jᶜ (runMax p m U i n).toNat with h | h
      · exact h
      · exact absurd h hcase
    have hstep : hfix (wA p m U n Jᶜ) (runMax p m U i n).toNat
        = hprev (wA p m U n Jᶜ) (runMax p m U i n).toNat + 2 :=
      hfix_eq_two_add_hprev hw
    rcases Nat.eq_zero_or_pos (runMax p m U i n).toNat with h0 | hpos
    · rw [h0] at hstep ⊢
      rw [hstep]
      simp
    · have hpw : hprev (wA p m U n Jᶜ) (runMax p m U i n).toNat
          = hfix (wA p m U n Jᶜ) ((runMax p m U i n).toNat - 1) :=
        hprev_eq_hfix_sub_one hpos
      have hph : hprev (omegaN p m U i) (runMax p m U i n).toNat
          = hfix (omegaN p m U i) ((runMax p m U i n).toNat - 1) :=
        hprev_eq_hfix_sub_one hpos
      have hcomp : hfix (wA p m U n Jᶜ) ((runMax p m U i n).toNat - 1)
          ≤ hfix (omegaN p m U i) ((runMax p m U i n).toNat - 1) := by
        refine hcomp_h p m U hp hp1 hiJ (x := (runMax p m U i n).toNat - 1) ?_
        have h1 : (((runMax p m U i n).toNat - 1 : ℕ) : ℤ)
            < ((runMax p m U i n).toNat : ℤ) := by
          exact_mod_cast Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp hpos)
        rwa [hRcast] at h1
      rw [hstep, hpw, hph]
      linarith

/-! ### (Wpos), second inequality: the observable dominates the actual gap -/

/-- Cast bookkeeping: for `k ≥ 0`, `((k.toNat : ℕ) : ℝ) = (k : ℝ)`. -/
lemma cast_toNat (k : ℤ) (hk : 0 ≤ k) : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
  have h : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
  calc ((k.toNat : ℕ) : ℝ) = ((k.toNat : ℤ) : ℝ) := by push_cast; ring
    _ = (k : ℝ) := by rw [h]

/-- **(Wpos)**, second inequality: on (sep), `W_n^{I,J}` dominates the actual gap
`min_{i ∈ I} X_n^i - max_{j ∈ J} X_n^j ≥ 0`.  This is the form consumed by the diameter
argument (`gap_div_tendsto_zero` in `Swarm/SeparatedGroups.lean`). -/
theorem gap_le_WA (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {I J : Finset (Fin N)}
    (hI : I.Nonempty) (hJ : J.Nonempty) (hsep : Sep p m U n I J) :
    ((I.inf' hI (fun i => X p m U n i) : ℤ) : ℝ)
        - ((J.sup' hJ (fun j => X p m U n j) : ℤ) : ℝ) ≤ WA p m U n I J hI hJ := by
  have hpos : ∀ x, 0 < wA p m U n Jᶜ x := wA_pos p m U hp n Jᶜ
  have hone : ∀ x, wA p m U n Jᶜ x ≤ 1 := wA_le_one p m U hp1 n Jᶜ
  have hmono : Monotone (HA p m U n Jᶜ) := HZ_mono hpos hone
  have hle : J.sup' hJ (fun j => X p m U n j) ≤ I.inf' hI (fun i => X p m U n i) :=
    Finset.sup'_le hJ _ fun j hj => Finset.le_inf' hI _ fun i hi => by
      have h1 : X p m U n j ≤ runMax p m U j n := le_runMax_pos p m U n j
      have h2 := hsep.2 i hi j hj
      omega
  have hmn0 : (0 : ℤ) ≤ I.inf' hI (fun i => X p m U n i) :=
    Finset.le_inf' hI _ fun i hi => hsep.1 i
  have hmx0 : (0 : ℤ) ≤ J.sup' hJ (fun j => X p m U n j) := by
    obtain ⟨j₀, hj₀⟩ := hJ
    exact le_trans (hsep.1 j₀) (Finset.le_sup' (fun j => X p m U n j) hj₀)
  have hgap : ((I.inf' hI (fun i => X p m U n i) : ℤ) : ℝ)
        - ((J.sup' hJ (fun j => X p m U n j) : ℤ) : ℝ)
      = ((I.inf' hI (fun i => X p m U n i)).toNat : ℝ)
        - ((J.sup' hJ (fun j => X p m U n j)).toNat : ℝ) := by
    rw [← cast_toNat _ hmn0, ← cast_toNat _ hmx0]
  have hsub := Swarming.Constants.Hfix_sub_ge (wA p m U n Jᶜ) hpos hone
    (Int.toNat_le_toNat hle)
  have hH1 : HA p m U n Jᶜ (I.inf' hI (fun i => X p m U n i))
      = Hfix (wA p m U n Jᶜ) (I.inf' hI (fun i => X p m U n i)).toNat := HZ_nonneg hmn0
  have hH2 : HA p m U n Jᶜ (J.sup' hJ (fun j => X p m U n j))
      = Hfix (wA p m U n Jᶜ) (J.sup' hJ (fun j => X p m U n j)).toNat := HZ_nonneg hmx0
  have hmaxeq : Swarming.Group.maximumOn J hJ (fun j => HA p m U n Jᶜ (X p m U n j))
      = HA p m U n Jᶜ (J.sup' hJ (fun j => X p m U n j)) :=
    HA_maximum_eq p m U hp hp1 n Jᶜ hJ (fun j => X p m U n j)
  have hminle : HA p m U n Jᶜ (I.inf' hI (fun i => X p m U n i))
      ≤ Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U n i)) :=
    le_average_of_le hI fun i hi => hmono (Finset.inf'_le (fun i => X p m U n i) hi)
  rw [WA, hmaxeq]
  linarith [hgap, hsub, hH1, hH2, hminle]

/-! ### The paper's strict form (Wstrict) -/

/-- The per-walker correction term of (Wstrict):
`(α_n^i - w_n^{A}(X_n^i)) (h_n^{A}(X_n^i) + h_n^{A}(X_n^i-1))`. -/
noncomputable def corr (n : ℕ) (A : Finset (Fin N)) (i : Fin N) : ℝ :=
  (rightProbability p m (trajectory p m U n).ell i (X p m U n i)
      - wA p m U n A (X p m U n i).toNat)
    * (hfix (wA p m U n A) (X p m U n i).toNat
        + hprev (wA p m U n A) (X p m U n i).toNat)

/-- The one-step mean of `H_n^A` equals `H_n^A(X_n^i) + 1` plus the correction term. -/
lemma stepMean_eq_add_corr (hp : 1 / 2 ≤ p) {n : ℕ} {A : Finset (Fin N)} {i : Fin N}
    (hx : 0 ≤ X p m U n i) :
    stepMean p m U n i (HA p m U n A)
      = HA p m U n A (X p m U n i) + 1 + corr p m U n A i := by
  have h := stepMean_HA_sub p m U hp (n := n) (A := A) (k := i) hx
  unfold corr
  linarith

/-- The average is invariant under a pointwise equal summand. -/
lemma average_congr {ι : Type*} {s : Finset ι} {f g : ι → ℝ} (h : ∀ i ∈ s, f i = g i) :
    Swarming.Group.average s f = Swarming.Group.average s g := by
  dsimp [Swarming.Group.average]
  rw [Finset.sum_congr rfl h]

/-- The average is additive in the summand. -/
lemma average_add {ι : Type*} {s : Finset ι} (f g : ι → ℝ) :
    Swarming.Group.average s (fun i => f i + g i)
      = Swarming.Group.average s f + Swarming.Group.average s g := by
  dsimp [Swarming.Group.average]
  rw [Finset.sum_add_distrib, add_div]

/-- **(Wstrict)** at the level of the exact one-step mean: on (sep),
`W_{n+1}^{I,J} - W_n^{I,J}` has two-point mean at most
`|I|^{-1} ∑_{i ∈ I} (α_n^i - w_n^{J^c}(X_n^i)) (h^w(X_n^i) + h^w(X_n^i-1))`,
which is `-|I|^{-1} ∑_{i ∈ I} (w_n^{J^c}(X_n^i) - α_n^i)(h^w(X_n^i) + h^w(X_n^i-1))`
on the event `i ∈ I`, `α_n^i ≤ w_n^{J^c}(X_n^i)`.

Again this is the two-point mean, not `E[· | ℱ_n]`. -/
theorem WA_drift_le_strict (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {n : ℕ} {I J : Finset (Fin N)}
    (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) (hsep : Sep p m U n I J) :
    Swarming.Group.average I (fun i => stepMean p m U n i (HA p m U n Jᶜ)) -
        Swarming.Group.maximumOn J hJ (fun j => stepMean p m U n j (HA p m U n Jᶜ))
      ≤ WA p m U n I J hI hJ
        + Swarming.Group.average I (fun i => corr p m U n Jᶜ i) := by
  have hJge : ∀ j ∈ J, HA p m U n Jᶜ (X p m U n j) + 1
      ≤ stepMean p m U n j (HA p m U n Jᶜ) := by
    intro j hj
    have h1 := stepMean_HA_sub p m U hp (n := n) (A := Jᶜ) (k := j) (hsep.1 j)
    have h2 : 0 ≤ rightProbability p m (trajectory p m U n).ell j (X p m U n j)
        - wA p m U n Jᶜ (X p m U n j).toNat := by
      have h := wA_le_rightProbability_of_J p m U hp hj (hsep.1 j)
      linarith
    have hpos := wA_pos p m U hp n Jᶜ
    have hone := wA_le_one p m U hp1 n Jᶜ
    have h3 : 0 < hfix (wA p m U n Jᶜ) (X p m U n j).toNat
        + hprev (wA p m U n Jᶜ) (X p m U n j).toNat := by
      have ha := one_le_hfix (wA p m U n Jᶜ) hpos hone (X p m U n j).toNat
      have hb := one_le_hprev hpos hone (X p m U n j).toNat
      linarith
    have h4 := mul_nonneg h2 (le_of_lt h3)
    linarith [h1, h4]
  have hmax : Swarming.Group.maximumOn J hJ
        (fun j => HA p m U n Jᶜ (X p m U n j) + 1)
      ≤ Swarming.Group.maximumOn J hJ (fun j => stepMean p m U n j (HA p m U n Jᶜ)) :=
    Finset.sup'_le hJ _ fun j hj =>
      le_trans (hJge j hj) (Finset.le_sup' (fun j => stepMean p m U n j (HA p m U n Jᶜ)) hj)
  rw [maximumOn_add_const hJ (fun j => HA p m U n Jᶜ (X p m U n j)) 1] at hmax
  have havg : Swarming.Group.average I (fun i => stepMean p m U n i (HA p m U n Jᶜ))
      = Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U n i)) + 1
        + Swarming.Group.average I (fun i => corr p m U n Jᶜ i) := by
    rw [average_congr (f := fun i => stepMean p m U n i (HA p m U n Jᶜ))
      (g := fun i => HA p m U n Jᶜ (X p m U n i) + 1 + corr p m U n Jᶜ i)
      (fun i _ => stepMean_eq_add_corr p m U hp (hsep.1 i))]
    rw [average_add (f := fun i => HA p m U n Jᶜ (X p m U n i) + 1)
      (g := fun i => corr p m U n Jᶜ i), average_add_const hI]
  rw [WA, havg]
  linarith

end Model

end SepGroup

/-! ### Axiom audit -/


