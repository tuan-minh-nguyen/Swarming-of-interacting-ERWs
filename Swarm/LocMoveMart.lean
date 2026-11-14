/-
# `LocMoveMart`: the maximum's literal increment, its signed compensator, and its martingale part

`LocMoveH.condExp_indicator_Mnext_sub_Mnow_ge_one` proves the *conditional-mean* half of
`(locmove)`: on `(sep)` the group maximum `max_{j∈Aᶜ} H^A(X^j)` grows by at least `1` in
conditional mean.  What is missing for the pathwise display of `(locmove)` is the splitting of
that drift into a **signed compensator plus a genuine martingale difference**, together with a
*computed* bound on the increments.

This file supplies exactly that, on the actual interacting array (`arrayMeasure`,
`posFilt`), and nothing more:

* `abs_sup'_sub_sup'_le` — the maximum of a difference is at most the difference of maxima.
  This is what turns a per-walker increment bound into a bound on the maximum's increment
  (the file `QVarBound` bounds the per-walker step only for walkers *inside* the weight group,
  which is the wrong side for `max_{j∈Aᶜ}`; the bound below needs neither `(hcomp)` nor `(sep)`).
* `abs_HA_step_le_lin` — one lattice step of the frozen potential moves it by at most
  `2(n+1)+3`.  The point is that `H^A`'s *step* is `hfix` at the lower site (linear in the
  site), not `H^A` itself (quadratic in the site): the crude uniform bound
  `WdriftJoint.abs_HA_le` would give `2·((n+1)(2(n+1)+3)+3) = O(n²)`.
* `abs_Mnext_sub_Mnow_le` — **bounded increments**: `|Mnext_n - Mnow_n| ≤ 2n+5` for every
  driving array, with no `(sep)` and no hypothesised constant.
* `Mlit` and `indicator_Mlit_eq` — the **literal** increment
  `max_{j∈Aᶜ} H_{n+1}^A(X_{n+1}^j) - max_{j∈Aᶜ} H_n^A(X_n^j)`, i.e. with the *actual*
  time-`(n+1)` weights (not the falsely crossed time-`n` weights at the new positions), and
  its identification with `Mnext_n - Mnow_n` on `(sep)` via
  `LocMoveWeight.indicator_max_eq_of_subset_sep`.  The transport is used *only* on `(sep)`.
* `Mraw`, `Mcomp`, `dM`, `Mcum` — the `(sep)`-truncated increment, its signed compensator
  (the time-`n` conditional mean), the centred increment and its cumulative sum.
* `Mcomp_ge_sep` — the compensator dominates the `(sep)` indicator (`LocMoveH`), transported
  to the *literal* increment.
* `condExp_dM`, `martingale_Mcum` — the centring is a genuine martingale-difference sequence for
  the nested filtration `posFilt`, hence `Mcum` is a `Martingale`.
* `abs_dM_le` — bounded increments of the martingale itself: `|dM_n| ≤ 4n+10` a.e.
* `Mnow_sep_window_ge` — on a window on which `(sep)` holds at *every* time, the running
  maximum telescopes to `(t-s) + Σ dM` plus nothing: the drift half and the martingale half of
  `(locmove)`, with no remainder.
* `Mnow_telescope_decomp` — the exact identity on an arbitrary window, keeping the non-`(sep)`
  remainder explicit instead of silently dropping it.

Scope, stated exactly: the quantitative constants here are the honest ones produced by the
step structure; they are `O(n)` in the absolute time, not the paper's `O(L^{3/4})` record-window
scale, and this file makes no claim about `(locmove)`'s maximal inequality, about `Γ`-trials,
or about regeneration.  No `sorry`, no extra axiom, no `native_decide`.
-/
import Swarm.LocMoveWeight
import Swarm.LocMoveH
import Swarm.QVarBound

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocMoveMart

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift

variable {N : ℕ}

/-! ## 1. The maximum of a difference -/

/-- **`|max f - max g| ≤ max |f - g|`** — for a finite nonempty index set. -/
theorem abs_sup'_sub_sup'_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) :
    |s.sup' hs f - s.sup' hs g| ≤ s.sup' hs (fun i => |f i - g i|) := by
  set M := s.sup' hs (fun i => |f i - g i|) with hM
  have hf : ∀ i ∈ s, f i ≤ g i + M := by
    intro i hi
    have h1 : |f i - g i| ≤ M := hM ▸ Finset.le_sup' (fun i => |f i - g i|) hi
    have h2 : g i ≤ s.sup' hs g := Finset.le_sup' g hi
    linarith [le_abs_self (f i - g i)]
  have hg : ∀ i ∈ s, g i ≤ f i + M := by
    intro i hi
    have h1 : |f i - g i| ≤ M := hM ▸ Finset.le_sup' (fun i => |f i - g i|) hi
    have h2 : f i ≤ s.sup' hs f := Finset.le_sup' f hi
    linarith [neg_le_abs (f i - g i)]
  have h1 : s.sup' hs f ≤ s.sup' hs g + M :=
    Finset.sup'_le hs f fun i hi => by linarith [hf i hi, Finset.le_sup' g hi]
  have h2 : s.sup' hs g ≤ s.sup' hs f + M :=
    Finset.sup'_le hs g fun i hi => by linarith [hg i hi, Finset.le_sup' f hi]
  rw [abs_le]
  constructor <;> linarith

/-- The same statement for `Swarming.Group.maximumOn`. -/
theorem abs_maximumOn_sub_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) :
    |Swarming.Group.maximumOn s hs f - Swarming.Group.maximumOn s hs g|
      ≤ Swarming.Group.maximumOn s hs (fun i => |f i - g i|) :=
  abs_sup'_sub_sup'_le s hs f g

/-! ## 2. One lattice step of the frozen potential is linear in the site -/

theorem toNat_le_of_le {y : ℤ} {k : ℕ} (h : y ≤ (k : ℤ)) : y.toNat ≤ k := by
  rcases lt_or_ge y 0 with hneg | hpos
  · rw [Int.toNat_eq_zero.mpr (by omega)]
    exact Nat.zero_le k
  · have h2 : ((y.toNat : ℕ) : ℤ) ≤ (k : ℤ) := by
      rw [Int.toNat_of_nonneg hpos]
      exact h
    exact_mod_cast h2

/-- `hfix (wA ·) u ≤ 2 u + 3` for every site `u`. -/
theorem hfix_wA_le_lin {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (A : Finset (Fin N)) (U : Array N) (u : ℕ) :
    hfix (wA p m U n A) u ≤ 2 * (u : ℝ) + 3 :=
  SwarmM3.hfix_le_lin (wA p m U n A) (fun v => one_half_le_wA p m U hp n A v)
    (fun v => wA_le_one p m U hp1 n A v) u

/-- **One lattice step of the frozen group potential.**  If `x' = x ± 1` or `x' = x` and both
sites lie in `[-n-1, n+1]`, then `H_n^A` moves by at most `2(n+1)+3`.  (The exact one-step
increment is `hfix` at the lower site, which is linear in the site; the size of `H_n^A` itself
is quadratic.) -/
theorem abs_HA_step_le_lin {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (A : Finset (Fin N)) (U : Array N) {x x' : ℤ}
    (hx : x ≤ (n : ℤ) + 1) (hx' : x' ≤ (n : ℤ) + 1)
    (hd : x' = x + 1 ∨ x' = x - 1 ∨ x' = x) :
    |HA p m U n A x' - HA p m U n A x| ≤ 2 * ((n : ℝ) + 1) + 3 := by
  have hstep := SwarmQVariance.abs_HZ_step_le (w := wA p m U n A) (wA_pos p m U hp n A)
    (wA_le_one p m U hp1 n A) hd
  have hA : ∀ y : ℤ, y ≤ (n : ℤ) + 1 → hfix (wA p m U n A) y.toNat ≤ 2 * ((n : ℝ) + 1) + 3 := by
    intro y hy
    have h1 : y.toNat ≤ n + 1 := toNat_le_of_le hy
    have h2 := hfix_wA_le_lin hp hp1 m n A U y.toNat
    have h3 : (y.toNat : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hmax : max (hfix (wA p m U n A) x.toNat) (hfix (wA p m U n A) x'.toNat)
      ≤ 2 * ((n : ℝ) + 1) + 3 := max_le (hA x hx) (hA x' hx')
  exact le_trans hstep hmax

/-- The per-walker one-step bound at the **actual** positions of walker `j`. -/
theorem abs_HA_step_actual_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (A : Finset (Fin N)) (U : Array N) (j : Fin N) :
    |HA p m U n A (X p m U (n + 1) j) - HA p m U n A (X p m U n j)|
      ≤ 2 * ((n : ℝ) + 1) + 3 := by
  have hxu : X p m U n j ≤ (n : ℤ) := SwarmQVariance.X_le_time p m U n j
  have hxu' : X p m U (n + 1) j ≤ ((n + 1 : ℕ) : ℤ) :=
    SwarmQVariance.X_le_time p m U (n + 1) j
  have hx' : X p m U (n + 1) j ≤ (n : ℤ) + 1 := by push_cast at hxu' ⊢; exact hxu'
  rcases SwarmQVariance.X_succ_sub_X p m U n j with h | h
  · exact abs_HA_step_le_lin hp hp1 m n A U (by omega) hx' (Or.inl h)
  · exact abs_HA_step_le_lin hp hp1 m n A U (by omega) hx' (Or.inr (Or.inl h))

/-! ## 3. Bounded increments of the group maximum -/

/-- **Bounded increment of the maximum, per walker.** -/
theorem abs_Mnext_sub_Mnow_le_sup {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) (U : Array N) :
    |Mnext p m n J hJ U - Mnow p m n J hJ U| ≤ 2 * ((n : ℝ) + 1) + 3 := by
  have h := abs_maximumOn_sub_le J hJ
    (fun j => HA p m U n Jᶜ (X p m U (n + 1) j))
    (fun j => HA p m U n Jᶜ (X p m U n j))
  have hsup : Swarming.Group.maximumOn J hJ
      (fun j => |HA p m U n Jᶜ (X p m U (n + 1) j) - HA p m U n Jᶜ (X p m U n j)|)
      ≤ 2 * ((n : ℝ) + 1) + 3 := by
    unfold Swarming.Group.maximumOn
    refine Finset.sup'_le hJ _ fun j _ => ?_
    exact abs_HA_step_actual_le hp hp1 m n Jᶜ U j
  exact le_trans h hsup

/-- **Bounded increment of the group maximum.**  Uniform over all driving arrays: no `(sep)`,
no `(hcomp)`, no hypothesised constant. -/
theorem abs_Mnext_sub_Mnow_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) (U : Array N) :
    |Mnext p m n J hJ U - Mnow p m n J hJ U| ≤ 2 * (n : ℝ) + 5 := by
  have h := abs_Mnext_sub_Mnow_le_sup hp hp1 m n J hJ U
  have : 2 * ((n : ℝ) + 1) + 3 = 2 * (n : ℝ) + 5 := by ring
  linarith [h, this]


/-! ## 4. The literal increment of the maximum, and its identification on `(sep)` -/

/-- The **literal** increment of the group maximum at step `n → n+1`: the actual time-`(n+1)`
maximum `max_{j∈Aᶜ} H_{n+1}^A(X_{n+1}^j)` minus the actual time-`n` maximum, with `A = Jᶜ`. -/
noncomputable def Mlit (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (U : Array N) : ℝ :=
  Swarming.Group.maximumOn J hJ (fun j => HA p m U (n + 1) Jᶜ (X p m U (n + 1) j))
    - Mnow p m n J hJ U

/-- On `(sep)` the actual time-`(n+1)` group maximum is the time-`n` maximum at the new
positions: `Mnow_{n+1} = Mnext_n`.  This is `LocMoveWeight.maximumOn_succ_eq_of_sep` with
`A = Jᶜ`. -/
theorem Mnow_succ_eq_Mnext_of_sep {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    (J : Finset (Fin N)) (hJ : J.Nonempty) {U : Array N} (hsep : Sep p m U n Jᶜ J) :
    Mnow p m (n + 1) J hJ U = Mnext p m n J hJ U := by
  have h := LocMoveWeight.maximumOn_succ_eq_of_sep p m U n Jᶜ hp hp1 (by simpa using hsep)
    (hJ := by simpa using hJ)
  simpa [Mnow, Mnext] using h

/-- **The transport lemma, used only on `(sep)`.**  On `(sep)` the literal increment equals
`Mnext_n - Mnow_n` (the time-`n` weights at the new positions), because the weights of `A = Jᶜ`
change only at positions at or below the new positions of `Aᶜ = J`
(`LocMoveWeight.HA_succ_eq_of_prefix`).  Off `(sep)` the two differ and nothing is claimed. -/
theorem indicator_Mlit_eq {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    (fun U => ({U | SepSet p m n Jᶜ J U}).indicator (Mlit p m n J hJ) U)
      = fun U => ({U | SepSet p m n Jᶜ J U}).indicator
          (fun U => Mnext p m n J hJ U - Mnow p m n J hJ U) U := by
  funext U
  by_cases hU : U ∈ ({U | SepSet p m n Jᶜ J U} : Set (Array N))
  · rw [Set.indicator_of_mem hU, Set.indicator_of_mem hU]
    show Mnow p m (n + 1) J hJ U - Mnow p m n J hJ U
      = Mnext p m n J hJ U - Mnow p m n J hJ U
    rw [Mnow_succ_eq_Mnext_of_sep hp hp1 (m := m) (n := n) J hJ hU]
  · rw [Set.indicator_of_notMem hU, Set.indicator_of_notMem hU]

/-! ## 5. The `(sep)`-truncated increment, its compensator and the centred increment -/

/-- The unsigned increment `Mnext_n - Mnow_n` of the group maximum (time-`n` weights at the new
positions).  Introduced as a named object so that its measurability is that of the two
`maximumOn` terms, not of a fresh lambda. -/
noncomputable def Mdiff (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (U : Array N) : ℝ :=
  Mnext p m n J hJ U - Mnow p m n J hJ U

/-- The `(sep)`-truncated increment of the group maximum.  By `indicator_Mlit_eq` this is also
`1_{(sep)}·Mlit`, i.e. the truncation of the *actual* increment, not of a crossed-weight
surrogate. -/
noncomputable def Mraw (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (U : Array N) : ℝ :=
  ({U | SepSet p m n Jᶜ J U}).indicator (Mdiff p m n J hJ) U

/-- `Mraw` is the `(sep)`-truncation of the literal increment. -/
theorem Mraw_eq_indicator_Mlit {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    Mraw p m n J hJ = fun U => ({U | SepSet p m n Jᶜ J U}).indicator (Mlit p m n J hJ) U :=
  (indicator_Mlit_eq hp hp1 m n J hJ).symm

/-- The **signed compensator** of the `(sep)`-truncated maximum increment: its conditional mean
given `F_n`. -/
noncomputable def Mcomp (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (U : Array N) : ℝ :=
  condExp (posFilt N p m n) (arrayMeasure N) (Mraw p m n J hJ) U

/-- The **centred increment** (martingale difference). -/
noncomputable def dM (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (U : Array N) : ℝ :=
  Mraw p m n J hJ U - Mcomp p m n J hJ U

/-- The cumulative centred maximum process `Σ_{k<n} dM_k`. -/
noncomputable def Mcum (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (U : Array N) : ℝ :=
  ∑ k ∈ Finset.range n, dM p m k J hJ U

/-! ### 6. Measurability, integrability and the computed bounds -/

theorem measurable_Mnext_succ (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) :
    Measurable[posFilt N p m (n + 1)] (Mnext p m n J hJ) := by
  letI : MeasurableSpace (Array N) := posFilt N p m (n + 1)
  have hfixM : ∀ u, Measurable (fun U : Array N => hfix (wA p m U n Jᶜ) u) := fun u =>
    (SwarmM3.measurable_hfix_wA_posFilt p m n Jᶜ u).mono
      ((posFilt N p m).mono (Nat.le_succ n)) le_rfl
  have hsite : ∀ j : Fin N, Measurable (fun U : Array N => HA p m U n Jᶜ (X p m U (n + 1) j)) :=
    fun j => measurable_HA_random_site' p m n Jᶜ
      (fun U : Array N => X p m U (n + 1) j) (measurable_pos_posFilt p m j le_rfl) hfixM (n + 1)
      (fun U => SwarmM3.abs_X_le p m U (n + 1) j)
  have hfun : Mnext p m n J hJ
      = fun U : Array N => J.sup' hJ (fun j => HA p m U n Jᶜ (X p m U (n + 1) j)) := rfl
  rw [hfun]
  have heta : (fun U : Array N => J.sup' hJ (fun j => HA p m U n Jᶜ (X p m U (n + 1) j)))
      = J.sup' hJ (fun j U => HA p m U n Jᶜ (X p m U (n + 1) j)) := by
    funext U
    rw [Finset.sup'_apply]
  rw [heta]
  exact Finset.measurable_sup' hJ (fun j _ => hsite j)

theorem stronglyMeasurable_Mdiff_succ (p : ℝ) (m n : ℕ) (J : Finset (Fin N))
    (hJ : J.Nonempty) : StronglyMeasurable[posFilt N p m (n + 1)] (Mdiff p m n J hJ) := by
  letI : MeasurableSpace (Array N) := posFilt N p m (n + 1)
  have hA : StronglyMeasurable[posFilt N p m (n + 1)] (Mnext p m n J hJ) :=
    (measurable_Mnext_succ p m n J hJ).stronglyMeasurable
  have hB : StronglyMeasurable[posFilt N p m (n + 1)] (Mnow p m n J hJ) :=
    ((measurable_Mnow_posFilt p m n J hJ).mono
      ((posFilt N p m).mono (Nat.le_succ n)) le_rfl).stronglyMeasurable
  exact hA.sub hB

theorem stronglyMeasurable_Mraw_succ (p : ℝ) (m n : ℕ) (J : Finset (Fin N))
    (hJ : J.Nonempty) : StronglyMeasurable[posFilt N p m (n + 1)] (Mraw p m n J hJ) := by
  letI : MeasurableSpace (Array N) := posFilt N p m (n + 1)
  have h1 : StronglyMeasurable[posFilt N p m (n + 1)] (Mdiff p m n J hJ) :=
    stronglyMeasurable_Mdiff_succ p m n J hJ
  have h2 : MeasurableSet[posFilt N p m (n + 1)] {U : Array N | SepSet p m n Jᶜ J U} :=
    ((posFilt N p m).mono (Nat.le_succ n)) {U : Array N | SepSet p m n Jᶜ J U}
      (measurableSet_sepSet p m n Jᶜ J)
  exact h1.indicator h2

theorem abs_Mraw_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) (U : Array N) :
    |Mraw p m n J hJ U| ≤ 2 * (n : ℝ) + 5 := by
  have h := abs_Mnext_sub_Mnow_le hp hp1 m n J hJ U
  by_cases hU : U ∈ ({U | SepSet p m n Jᶜ J U} : Set (Array N))
  · rw [Mraw, Set.indicator_of_mem hU]
    show |Mdiff p m n J hJ U| ≤ 2 * (n : ℝ) + 5
    rw [Mdiff]
    linarith
  · rw [Mraw, Set.indicator_of_notMem hU, abs_zero]
    positivity

theorem integrable_Mraw {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    Integrable (Mraw p m n J hJ) (arrayMeasure N) := by
  have hd : Integrable (Mdiff p m n J hJ) (arrayMeasure N) :=
    (integrable_Mnext hp hp1 m n J hJ).sub (integrable_Mnow hp hp1 m n J hJ)
  exact hd.indicator (((posFilt N p m).le n) {U : Array N | SepSet p m n Jᶜ J U}
    (measurableSet_sepSet p m n Jᶜ J))

theorem integrable_Mcomp {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    Integrable (Mcomp p m n J hJ) (arrayMeasure N) := by
  have hint := integrable_Mraw hp hp1 m n J hJ
  exact integrable_condExp (μ := arrayMeasure N) (m := posFilt N p m n)
    (f := Mraw p m n J hJ)

theorem integrable_dM {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    Integrable (dM p m n J hJ) (arrayMeasure N) :=
  (integrable_Mraw hp hp1 m n J hJ).sub (integrable_Mcomp hp hp1 m n J hJ)

/-- **The compensator is bounded a.e.** by the same computed constant. -/
theorem abs_Mcomp_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    ∀ᵐ U ∂(arrayMeasure N), |Mcomp p m n J hJ U| ≤ 2 * (n : ℝ) + 5 := by
  have : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have h1 : |condExp (posFilt N p m n) (arrayMeasure N) (Mraw p m n J hJ)|
      ≤ᵐ[arrayMeasure N]
      condExp (posFilt N p m n) (arrayMeasure N) (fun U => |Mraw p m n J hJ U|) :=
    abs_condExp_ae_le_condExp_abs _
  have hcint : Integrable (fun _ : Array N => 2 * (n : ℝ) + 5) (arrayMeasure N) :=
    integrable_const _
  have hconst : condExp (posFilt N p m n) (arrayMeasure N)
      (fun _ : Array N => 2 * (n : ℝ) + 5) = fun _ => 2 * (n : ℝ) + 5 :=
    condExp_const ((posFilt N p m).le n) (2 * (n : ℝ) + 5)
  have h2 : condExp (posFilt N p m n) (arrayMeasure N) (fun U => |Mraw p m n J hJ U|)
      ≤ᵐ[arrayMeasure N] fun _ => 2 * (n : ℝ) + 5 := by
    have hmono := condExp_mono (μ := arrayMeasure N) (m := posFilt N p m n)
      (f := fun U => |Mraw p m n J hJ U|) (g := fun _ : Array N => 2 * (n : ℝ) + 5)
      (integrable_Mraw hp hp1 m n J hJ).abs hcint
      (Filter.Eventually.of_forall (abs_Mraw_le hp hp1 m n J hJ))
    rw [hconst] at hmono
    exact hmono
  exact h1.trans h2


/-- **Bounded increments of the centred maximum process.**  The computed constant is
`2·(2n+5) = 4n+10`. -/
theorem abs_dM_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    ∀ᵐ U ∂(arrayMeasure N), |dM p m n J hJ U| ≤ 4 * (n : ℝ) + 10 := by
  filter_upwards [abs_Mcomp_le hp hp1 m n J hJ] with U hU
  have h1 : |Mraw p m n J hJ U| ≤ 2 * (n : ℝ) + 5 := abs_Mraw_le hp hp1 m n J hJ U
  have h2 : |Mraw p m n J hJ U - Mcomp p m n J hJ U|
      ≤ |Mraw p m n J hJ U| + |Mcomp p m n J hJ U| := by
    have h := abs_add_le (Mraw p m n J hJ U) (-(Mcomp p m n J hJ U))
    simpa only [sub_eq_add_neg, abs_neg] using h
  show |Mraw p m n J hJ U - Mcomp p m n J hJ U| ≤ 4 * (n : ℝ) + 10
  linarith

theorem stronglyMeasurable_dM (p : ℝ) (m n : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) :
    StronglyMeasurable[posFilt N p m (n + 1)] (dM p m n J hJ) := by
  letI : MeasurableSpace (Array N) := posFilt N p m (n + 1)
  have hraw : StronglyMeasurable[posFilt N p m (n + 1)] (Mraw p m n J hJ) :=
    stronglyMeasurable_Mraw_succ p m n J hJ
  have hce : StronglyMeasurable[posFilt N p m (n + 1)] (Mcomp p m n J hJ) :=
    SwarmJointDrift.stronglyMeasurable_mono_filt
      (stronglyMeasurable_condExp : StronglyMeasurable[posFilt N p m n] (Mcomp p m n J hJ))
      ((posFilt N p m).mono (Nat.le_succ n))
  exact hraw.sub hce

/-! ### 7. The compensator dominates the `(sep)` indicator -/

/-- **The drift half, in compensator form**: on `(sep)` the compensator is at least `1`. -/
theorem Mcomp_ge_sep {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    (fun U => ({U | SepSet p m n Jᶜ J U}).indicator (fun _ => (1 : ℝ)) U)
      ≤ᵐ[arrayMeasure N] Mcomp p m n J hJ :=
  LocMove.condExp_indicator_Mnext_sub_Mnow_ge_one hp0 hp1 m n J hJ
    (measurableSet_sepSet p m n Jᶜ J) (fun _ h => h)

/-- **The drift half for the literal increment.**  The compensator of `1_{(sep)}·Mlit` is the
same function, so the drift estimate applies to the actual time-`(n+1)` maximum. -/
theorem condExp_Mlit_ge_sep {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    (fun U => ({U | SepSet p m n Jᶜ J U}).indicator (fun _ => (1 : ℝ)) U)
      ≤ᵐ[arrayMeasure N]
      condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => ({U | SepSet p m n Jᶜ J U}).indicator (Mlit p m n J hJ) U) := by
  have h := Mcomp_ge_sep hp0 hp1 m n J hJ
  refine h.trans_eq ?_
  exact condExp_congr_ae (Filter.EventuallyEq.of_eq (Mraw_eq_indicator_Mlit hp0.le hp1.le m n J hJ))

/-! ### 8. `dM` is a genuine martingale difference, and `Mcum` a martingale -/

/-- **`dM_n` has zero conditional mean given `F_n`.** -/
theorem condExp_dM {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    condExp (posFilt N p m n) (arrayMeasure N) (dM p m n J hJ) =ᵐ[arrayMeasure N] 0 := by
  have hX := integrable_Mraw hp hp1 m n J hJ
  have hY := integrable_Mcomp hp hp1 m n J hJ
  have hsub : condExp (posFilt N p m n) (arrayMeasure N) (dM p m n J hJ)
      =ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N) (Mraw p m n J hJ)
        - condExp (posFilt N p m n) (arrayMeasure N)
            (fun U => condExp (posFilt N p m n) (arrayMeasure N) (Mraw p m n J hJ) U) :=
    condExp_sub hX hY _
  have hpull : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => condExp (posFilt N p m n) (arrayMeasure N) (Mraw p m n J hJ) U)
      = fun U => condExp (posFilt N p m n) (arrayMeasure N) (Mraw p m n J hJ) U :=
    condExp_of_stronglyMeasurable ((posFilt N p m).le n) stronglyMeasurable_condExp hY
  refine hsub.trans ?_
  rw [hpull]
  filter_upwards with U
  simp

theorem stronglyAdapted_Mcum (p : ℝ) (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) :
    StronglyAdapted (posFilt N p m) (fun n U => Mcum p m n J hJ U) := by
  intro n
  show StronglyMeasurable[posFilt N p m n] (fun U => ∑ k ∈ Finset.range n, dM p m k J hJ U)
  have hsum : (fun U : Array N => ∑ k ∈ Finset.range n, dM p m k J hJ U)
      = ∑ k ∈ Finset.range n, fun U => dM p m k J hJ U := by
    funext U
    rw [Finset.sum_apply]
  rw [hsum]
  refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
  have hk' : k < n := Finset.mem_range.mp hk
  exact SwarmJointDrift.stronglyMeasurable_mono_filt (stronglyMeasurable_dM p m k J hJ)
    ((posFilt N p m).mono (Nat.succ_le_of_lt hk'))

theorem integrable_Mcum {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    Integrable (Mcum p m n J hJ) (arrayMeasure N) := by
  show Integrable (fun U => ∑ k ∈ Finset.range n, dM p m k J hJ U) (arrayMeasure N)
  exact integrable_finsetSum _ fun k _ => integrable_dM hp hp1 m k J hJ

theorem condExp_Mcum_succ {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    condExp (posFilt N p m n) (arrayMeasure N) (Mcum p m (n + 1) J hJ)
      =ᵐ[arrayMeasure N] Mcum p m n J hJ := by
  haveI : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have heq : Mcum p m (n + 1) J hJ = fun U => Mcum p m n J hJ U + dM p m n J hJ U := by
    funext U
    simp only [Mcum, Finset.sum_range_succ]
  have hQ : condExp (posFilt N p m n) (arrayMeasure N) (Mcum p m (n + 1) J hJ)
      =ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N)
        (fun U => Mcum p m n J hJ U + dM p m n J hJ U) :=
    condExp_congr_ae (Filter.EventuallyEq.of_eq heq)
  have h1 : condExp (posFilt N p m n) (arrayMeasure N)
      (fun U => Mcum p m n J hJ U + dM p m n J hJ U)
      =ᵐ[arrayMeasure N] condExp (posFilt N p m n) (arrayMeasure N) (Mcum p m n J hJ)
        + condExp (posFilt N p m n) (arrayMeasure N) (dM p m n J hJ) :=
    condExp_add (integrable_Mcum hp hp1 m n J hJ) (integrable_dM hp hp1 m n J hJ) _
  have h2 : condExp (posFilt N p m n) (arrayMeasure N) (Mcum p m n J hJ)
      = Mcum p m n J hJ :=
    condExp_of_stronglyMeasurable ((posFilt N p m).le n) ((stronglyAdapted_Mcum p m J hJ) n)
      (integrable_Mcum hp hp1 m n J hJ)
  have h3 := condExp_dM hp hp1 m n J hJ
  refine hQ.trans ?_
  refine h1.trans ?_
  rw [h2]
  filter_upwards [h3] with U hU
  simp only [Pi.add_apply, hU, Pi.zero_apply, add_zero]

/-- **The centred maximum process is a martingale** for the position filtration. -/
theorem martingale_Mcum {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    Martingale (fun n U => Mcum p m n J hJ U) (posFilt N p m) (arrayMeasure N) :=
  martingale_nat (stronglyAdapted_Mcum p m J hJ) (fun n => integrable_Mcum hp hp1 m n J hJ)
    (fun n => (condExp_Mcum_succ hp hp1 m n J hJ).symm)


/-! ## 9. Telescoping the running maximum over a window -/

/-- Telescoping of the actual group maximum over `[s,t)`. -/
theorem Mnow_telescope {p : ℝ} (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    {s t : ℕ} (hst : s ≤ t) (U : Array N) :
    ∑ k ∈ Finset.Ico s t, (Mnow p m (k + 1) J hJ U - Mnow p m k J hJ U)
      = Mnow p m t J hJ U - Mnow p m s J hJ U := by
  have h := Finset.sum_Ico_sub (fun k => Mnow p m k J hJ U) hst
  exact h

/-- **The exact window decomposition.**  On `(sep)` the step of the running maximum is
`dM_k + Mcomp_k` (the centred increment plus its compensator); off `(sep)` it is what it is, and
this identity keeps that remainder instead of dropping it. -/
theorem Mnow_telescope_decomp {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) {s t : ℕ} (hst : s ≤ t) (U : Array N) :
    Mnow p m t J hJ U - Mnow p m s J hJ U
      = ∑ k ∈ Finset.Ico s t,
          (({U | SepSet p m k Jᶜ J U}).indicator
              (fun U => dM p m k J hJ U + Mcomp p m k J hJ U) U
            + ({U | SepSet p m k Jᶜ J U}ᶜ).indicator
              (fun U => Mnow p m (k + 1) J hJ U - Mnow p m k J hJ U) U) := by
  rw [← Mnow_telescope m J hJ hst U]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : U ∈ ({U | SepSet p m k Jᶜ J U} : Set (Array N))
  · have hstep : Mnow p m (k + 1) J hJ U - Mnow p m k J hJ U = Mdiff p m k J hJ U := by
      rw [Mdiff, Mnow_succ_eq_Mnext_of_sep hp hp1 (m := m) (n := k) J hJ hk]
    have hraw : Mraw p m k J hJ U = Mdiff p m k J hJ U := by
      rw [Mraw, Set.indicator_of_mem hk]
    rw [Set.indicator_of_mem hk, Set.indicator_of_notMem (by simpa using hk), add_zero]
    show Mnow p m (k + 1) J hJ U - Mnow p m k J hJ U
      = dM p m k J hJ U + Mcomp p m k J hJ U
    rw [dM, hraw, hstep]
    ring
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_mem (by simpa using hk), zero_add]

/-- **The drift half holds simultaneously at all times, a.e.** -/
theorem Mcomp_ge_sep_all {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ n : ℕ,
      ({U | SepSet p m n Jᶜ J U}).indicator (fun _ => (1 : ℝ)) U ≤ Mcomp p m n J hJ U :=
  MeasureTheory.ae_all_iff.2 fun n => Mcomp_ge_sep hp0 hp1 m n J hJ

/-- **`(locmove)` on a fully separated window: drift plus martingale, no remainder.**

If `(sep)` holds at *every* time of `[s,t)` for the driving array `U`, then the exact window
decomposition loses its non-`(sep)` remainder, the compensator contributes `1` at each of the
`t-s` times, and

`Mnow_t - Mnow_s ≥ (t-s) + Σ_{k∈[s,t)} dM_k`.

The right-hand side is the window length (the `-(t-s)` of the paper, with the sign convention of
a growing maximum) plus a genuine martingale-difference sum, which `martingale_Mcum` controls.
No term is assumed away: the hypothesis is the actual `(sep)` predicate on the actual
trajectory at every time of the window. -/
theorem Mnow_sep_window_ge {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) {s t : ℕ} (hst : s ≤ t) :
    ∀ᵐ U ∂(arrayMeasure N),
      (∀ k ∈ Finset.Ico s t, Sep p m U k Jᶜ J) →
      ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, dM p m k J hJ U
        ≤ Mnow p m t J hJ U - Mnow p m s J hJ U := by
  filter_upwards [Mcomp_ge_sep_all hp0 hp1 m J hJ] with U hU hsep
  have hdecomp := Mnow_telescope_decomp hp0.le hp1.le m J hJ hst U
  have hterm : ∀ k ∈ Finset.Ico s t,
      (({U | SepSet p m k Jᶜ J U}).indicator
          (fun U => dM p m k J hJ U + Mcomp p m k J hJ U) U
        + ({U | SepSet p m k Jᶜ J U}ᶜ).indicator
          (fun U => Mnow p m (k + 1) J hJ U - Mnow p m k J hJ U) U)
      = dM p m k J hJ U + Mcomp p m k J hJ U := by
    intro k hk
    have hmem : U ∈ ({U | SepSet p m k Jᶜ J U} : Set (Array N)) := hsep k hk
    rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem (by simpa using hmem), add_zero]
  have hsum : (∑ k ∈ Finset.Ico s t, dM p m k J hJ U) + ∑ k ∈ Finset.Ico s t, Mcomp p m k J hJ U
      = Mnow p m t J hJ U - Mnow p m s J hJ U := by
    rw [← Finset.sum_add_distrib, hdecomp]
    exact (Finset.sum_congr rfl hterm).symm
  have hdrift : ((t - s : ℕ) : ℝ) ≤ ∑ k ∈ Finset.Ico s t, Mcomp p m k J hJ U := by
    have h1 : (∑ k ∈ Finset.Ico s t, (1 : ℝ)) ≤ ∑ k ∈ Finset.Ico s t, Mcomp p m k J hJ U := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hmem : U ∈ ({U | SepSet p m k Jᶜ J U} : Set (Array N)) := hsep k hk
      have := hU k
      simpa only [Set.indicator_of_mem hmem] using this
    rwa [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one] at h1
  linarith


/-! ## 10. Axiom audit and the exact interface -/


-- the exact interface, so that it can be read off the verification log


end LocMoveMart
