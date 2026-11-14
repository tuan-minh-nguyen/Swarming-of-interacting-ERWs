/-
# `LocMaxProfile`: the maximal deviation profile of the max-`H` martingale on a window,
# its exact residual, and why the computed `O(n)` increment bound cannot reach `L^{3/4}`

`LocMoveMart` produces a genuine martingale difference `dM_k` with
`martingale_Mcum` (so `μ[dM_k | F_k] =ᵐ 0`), `abs_dM_le` (`|dM_k| ≤ 4k+10` a.e.) and the
separated-window drift bound `Mnow_sep_window_ge`
`Mnow_t - Mnow_s ≥ (t-s) + Σ_{k∈[s,t)} dM_k` whenever `(sep)` holds at every `k ∈ [s,t)`.
What the tree does not yet have is a *tail* statement for the martingale half; `Mcomp_ge_sep`
and `Mnow_sep_window_ge` are conditional-mean statements about the drift.

This file supplies the missing maximal profile, unconditionally, on the actual array:

* `LocMax.measure_max_abs_psum_ge_le_ae` (in `LocMaxVar.lean`) — maximal Hoeffding--Azuma with
  an arbitrary positive envelope, a.e. increment bounds, and the computed proxy `Σ c_k²`.
  The existing `LocMart` engine needs one uniform **pointwise** `C`, which `abs_dM_le` cannot
  supply (it is a.e.) and which does not exist (`4n+10` is unbounded).
* `measure_max_abs_Mcum_window_le` — the instantiation: for every window start `s` and length
  `K ≥ 1`, with the proxy `S = Σ_{k<K} (4(s+k)+10)²` and the single side condition
  `ε·(4(s+k)+10) ≤ 2S` for `k < K`,
  `μ{U | ∃ k ≤ K, ε ≤ |Mcum_{s+k} - Mcum_s|} ≤ 2(K+1)·exp(-ε²/(4S))`.
* `measure_max_abs_Mcum_window_le_C` — the cruder `S ≤ K·C²`, `C = 4(s+K)+10`.
* `measure_sep_window_dev_le` — the `(sep)`-window corollary: the event "`(sep)` at every time of
  `[s,t)` and the maximum falls `ε` below its drift `(t-s)`" is contained (a.e.) in the maximal
  deviation event, so it inherits the same bound.  This is the `(locmove)` lower half at a fixed
  window with no remainder.
* `profile_rhs_ge_one` — **the exact residual, computed**: at the paper's deviation `ε = L^{3/4}`
  and any window of length `K ≥ L`, the right-hand side above is `≥ 1`, so the profile carries no
  information there.  This is not a failure of the maximal inequality; it is the arithmetic of
  the increment bound `4n+10`, and it says precisely which constant has to be replaced.
* `profile_informative_imp` — the honest scaled statement: whenever the bound *is* informative,
  `ε² > 32 K³`, i.e. the deviation must be at least `4√2·K^{3/2}` on a window of length `K`.
  Equivalently `needed_envelope`: the envelope must satisfy `C² < ε²/(2K)`; at `ε = L^{3/4}` and
  `K ≈ L` that is `C ≲ L^{1/4}`, whereas `abs_dM_le` gives `C ≈ 4L`.  The gap is exactly
  `L^{3/4}` and it is a gap in the *increment* bound (`(hcomp)`-type local step control), not in
  the martingale machinery.

No `sorry`, no extra axiom, no `native_decide`.  Drift stays with `LocMoveH`/`Mnow_sep_window_ge`;
this file adds no global ledger and does not claim `(locmove)` at the paper's scale.
-/
import Swarm.LocMaxVar
import Swarm.LocMoveMart

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocMax

open LocMoveMart Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift

variable {N : ℕ}

/-! ## 1. The window objects -/

/-- The computed a.e. envelope of the max-`H` martingale increment at absolute time `s+k`,
from `LocMoveMart.abs_dM_le`: `4(s+k)+10`. -/
def dMbound (s : ℕ) : ℕ → ℝ := fun k => 4 * ((s + k : ℕ) : ℝ) + 10

/-- The position filtration shifted to start at time `s`. -/
noncomputable def shiftFilt (N : ℕ) (p : ℝ) (m s : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Array N)) where
  seq k := posFilt N p m (s + k)
  mono' := by
    intro a b hab
    exact (posFilt N p m).mono (Nat.add_le_add_left hab s)
  le' := fun k => (posFilt N p m).le (s + k)

/-- The martingale increment shifted to the window start `s`. -/
noncomputable def winInc (p : ℝ) (m s : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) :
    ℕ → Array N → ℝ :=
  fun k => dM p m (s + k) J hJ

lemma psum_winInc (p : ℝ) (m s : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) :
    ∀ k : ℕ, LocMart.psum (winInc p m s J hJ) k
      = fun U => Mcum p m (s + k) J hJ U - Mcum p m s J hJ U := by
  intro k
  induction k with
  | zero =>
    funext U
    simp [LocMart.psum_zero, Mcum]
  | succ k ih =>
    funext U
    rw [LocMart.psum_succ]
    have hstep : Mcum p m (s + (k + 1)) J hJ U
        = Mcum p m (s + k) J hJ U + dM p m (s + k) J hJ U := by
      simp only [Mcum]
      rw [show s + (k + 1) = (s + k) + 1 from rfl, Finset.sum_range_succ]
    have hpt := congrFun ih U
    rw [hpt, hstep]
    simp only [winInc]
    ring

/-- The `[s,t)` window sum of the martingale differences, at a point. -/
lemma sum_Ico_dM_eq (p : ℝ) (m s t : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty)
    (hst : s ≤ t) (U : Array N) :
    ∑ k ∈ Finset.Ico s t, dM p m k J hJ U = Mcum p m t J hJ U - Mcum p m s J hJ U := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h1 : (∑ k ∈ Finset.range (t - s), dM p m (s + k) J hJ U)
      = LocMart.psum (winInc p m s J hJ) (t - s) U := by
    simp only [LocMart.psum, winInc]
  rw [h1, psum_winInc]
  rw [Nat.add_sub_cancel' hst]

/-! ## 2. The profile: maximal deviation of the max-`H` martingale on a window -/

/-- **Maximal deviation of the max-`H` martingale over `[s,s+K]`, proxy form.**

`dM_k` is centred given `F_k` (`condExp_dM`) and a.e. bounded by `4k+10` (`abs_dM_le`), so on the
window `[s,s+K)` the proxy is `Σ_{k<K} (4(s+k)+10)²` and, for any `S` dominating it,

  `μ{U | ∃ k ≤ K, ε ≤ |Mcum_{s+k}(U) - Mcum_s(U)|} ≤ 2(K+1)·exp(-ε²/(4S))`,

with the only side condition the Chernoff one `ε · (4(s+k)+10) ≤ 2S` on `k < K`. -/
theorem measure_max_abs_Mcum_window_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) {s K : ℕ} (hK : 1 ≤ K) {S ε : ℝ} (hS : 0 < S)
    (hSp : proxy (dMbound s) K ≤ S) (hε : 0 < ε)
    (hεc : ∀ k < K, ε * dMbound s k ≤ 2 * S) :
    (arrayMeasure N).real
        {U | ∃ k ≤ K, ε ≤ |Mcum p m (s + k) J hJ U - Mcum p m s J hJ U|}
      ≤ 2 * ((K : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * S)) := by
  have hmain := measure_max_abs_psum_ge_le_ae (μ := arrayMeasure N)
    (ℱ := shiftFilt N p m s) (ξ := winInc p m s J hJ) (c := dMbound s) (ε := ε)
    (n := K) (S := S) hK hS hSp ?_ ?_ ?_ ?_ hε hεc
  · have hset : {U : Array N | ∃ k ≤ K, ε ≤ |LocMart.psum (winInc p m s J hJ) k U|}
        = {U : Array N |
            ∃ k ≤ K, ε ≤ |Mcum p m (s + k) J hJ U - Mcum p m s J hJ U|} := by
      ext U
      constructor
      · rintro ⟨k, hk, hdev⟩
        exact ⟨k, hk, by rwa [psum_winInc] at hdev⟩
      · rintro ⟨k, hk, hdev⟩
        exact ⟨k, hk, by rwa [psum_winInc]⟩
    rw [hset] at hmain
    exact hmain
  · intro k hk
    exact stronglyMeasurable_dM p m (s + k) J hJ
  · intro k hk
    simp only [dMbound]
    positivity
  · intro k hk
    filter_upwards [abs_dM_le hp hp1 m (s + k) J hJ] with U hU
    simpa only [winInc, dMbound] using hU
  · intro k hk
    exact condExp_dM hp hp1 m (s + k) J hJ

/-- **The profile with the cruder uniform proxy `S = K·C²`, `C = 4(s+K)+10`.**

  `μ{∃ k ≤ K, ε ≤ |Mcum_{s+k} - Mcum_s|} ≤ 2(K+1)·exp(-ε²/(4 K C²))`

under the side condition `ε ≤ 2 K C`.  This is the form whose right-hand side is analysed in
`profile_rhs_ge_one`, `profile_informative_imp` and `needed_envelope`. -/
theorem measure_max_abs_Mcum_window_le_C {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) {s K : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hεC : ε ≤ 2 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10)) :
    (arrayMeasure N).real
        {U | ∃ k ≤ K, ε ≤ |Mcum p m (s + k) J hJ U - Mcum p m s J hJ U|}
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2)) := by
  have hC0 : (0 : ℝ) ≤ 4 * ((s + K : ℕ) : ℝ) + 10 := by
    have h : (0 : ℝ) ≤ ((s + K : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hKr : (0 : ℝ) < (K : ℝ) := by
    have h : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  -- the proxy is at most `K C²`
  have hprox : proxy (dMbound s) K ≤ (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2 := by
    have hterm : ∀ k ∈ Finset.range K, dMbound s k ^ 2
        ≤ (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2 := by
      intro k hk
      have hkK : k < K := Finset.mem_range.1 hk
      have hsk : ((s + k : ℕ) : ℝ) ≤ ((s + K : ℕ) : ℝ) := by
        have hs : s + k ≤ s + K := Nat.add_le_add_left (Nat.le_of_lt hkK) s
        exact_mod_cast hs
      have h0 : (0 : ℝ) ≤ 4 * ((s + k : ℕ) : ℝ) + 10 := by positivity
      have hle : dMbound s k ≤ 4 * ((s + K : ℕ) : ℝ) + 10 := by
        simp only [dMbound]; linarith
      exact pow_le_pow_left₀ h0 hle 2
    calc proxy (dMbound s) K = ∑ k ∈ Finset.range K, dMbound s k ^ 2 := rfl
      _ ≤ ∑ _k ∈ Finset.range K, (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hS : (0 : ℝ) < (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2 := by positivity
  have hmain := measure_max_abs_Mcum_window_le (p := p) hp hp1 m J hJ hK (S := (K : ℝ) *
    (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2) hS hprox hε ?_
  · refine le_trans hmain ?_
    rw [show (4 : ℝ) * ((K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2)
        = 4 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2 from by ring]
  · intro k hk
    have hle : dMbound s k ≤ 4 * ((s + K : ℕ) : ℝ) + 10 := by
      have hsk : ((s + k : ℕ) : ℝ) ≤ ((s + K : ℕ) : ℝ) := by
        have hs : s + k ≤ s + K := Nat.add_le_add_left (Nat.le_of_lt hk) s
        exact_mod_cast hs
      simp only [dMbound]; linarith
    have h1 : ε * dMbound s k ≤ ε * (4 * ((s + K : ℕ) : ℝ) + 10) :=
      mul_le_mul_of_nonneg_left hle hε.le
    have h2 : ε * (4 * ((s + K : ℕ) : ℝ) + 10)
        ≤ (2 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10)) * (4 * ((s + K : ℕ) : ℝ) + 10) := by
      nlinarith [mul_le_mul_of_nonneg_right hεC hC0]
    have h3 : (2 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10)) * (4 * ((s + K : ℕ) : ℝ) + 10)
        = 2 * ((K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2) := by ring
    linarith

/-! ## 3. The `(sep)`-window corollary: the drift bound's deviation tail -/

/-- **`(locmove)` on a fully separated window, with the profile tail.**

If `(sep)` holds at every time of `[s,t)` and the running maximum of the max-`H` functional
falls more than `ε` below its drift `(t-s)`, then the martingale part has deviated by more than
`ε` somewhere in `[s,t]`.  Hence that event inherits the profile bound.  No remainder, no
optional stopping, no conditional law: the containment is a.e. and the null set is the
`Mnow_sep_window_ge` exceptional set. -/
theorem measure_sep_window_dev_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (J : Finset (Fin N)) (hJ : J.Nonempty) {s t : ℕ} (hst : s ≤ t) (hK : 1 ≤ t - s)
    {ε : ℝ} (hε : 0 < ε)
    (hεc : ∀ k < t - s, ε * dMbound s k ≤ 2 * proxy (dMbound s) (t - s)) :
    (arrayMeasure N).real
        {U | (∀ k ∈ Finset.Ico s t, Sep p m U k Jᶜ J) ∧
          Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε}
      ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * proxy (dMbound s) (t - s))) := by
  set K : ℕ := t - s with hKdef
  set A : Set (Array N) := {U | (∀ k ∈ Finset.Ico s t, Sep p m U k Jᶜ J) ∧
      Mnow p m t J hJ U - Mnow p m s J hJ U < ((t - s : ℕ) : ℝ) - ε} with hA
  set B : Set (Array N) :=
    {U | ∃ k ≤ K, ε ≤ |Mcum p m (s + k) J hJ U - Mcum p m s J hJ U|} with hB
  have hae := Mnow_sep_window_ge (p := p) hp0 hp1 (m := m) J hJ (s := s) (t := t) hst
  have hnull : (arrayMeasure N) {U | ¬ ((∀ k ∈ Finset.Ico s t, Sep p m U k Jᶜ J) →
      ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, dM p m k J hJ U
        ≤ Mnow p m t J hJ U - Mnow p m s J hJ U)} = 0 := by
    have := (MeasureTheory.ae_iff (μ := arrayMeasure N)).1 hae
    exact this
  have hsub : A ⊆ B ∪ {U | ¬ ((∀ k ∈ Finset.Ico s t, Sep p m U k Jᶜ J) →
      ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, dM p m k J hJ U
        ≤ Mnow p m t J hJ U - Mnow p m s J hJ U)} := by
    intro U hU
    by_cases hP : ((∀ k ∈ Finset.Ico s t, Sep p m U k Jᶜ J) →
        ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, dM p m k J hJ U
          ≤ Mnow p m t J hJ U - Mnow p m s J hJ U)
    · refine Or.inl ?_
      have hsep := hU.1
      have hdev := hU.2
      have hineq := hP hsep
      have hsum : ∑ k ∈ Finset.Ico s t, dM p m k J hJ U
          = Mcum p m t J hJ U - Mcum p m s J hJ U := sum_Ico_dM_eq p m s t J hJ hst U
      rw [hsum] at hineq
      have hneg : Mcum p m t J hJ U - Mcum p m s J hJ U < -ε := by linarith
      refine ⟨t - s, le_rfl, ?_⟩
      have hsk : s + (t - s) = t := Nat.add_sub_cancel' hst
      rw [hsk]
      rw [abs_of_neg (by linarith)]
      linarith
    · exact Or.inr hP
  calc (arrayMeasure N).real A
      ≤ (arrayMeasure N).real (B ∪ {U | ¬ ((∀ k ∈ Finset.Ico s t, Sep p m U k Jᶜ J) →
          ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, dM p m k J hJ U
            ≤ Mnow p m t J hJ U - Mnow p m s J hJ U)}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real B
          + (arrayMeasure N).real {U | ¬ ((∀ k ∈ Finset.Ico s t, Sep p m U k Jᶜ J) →
              ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, dM p m k J hJ U
                ≤ Mnow p m t J hJ U - Mnow p m s J hJ U)} :=
        measureReal_union_le _ _
    _ = (arrayMeasure N).real B := by
        have hzero : (arrayMeasure N).real {U | ¬ ((∀ k ∈ Finset.Ico s t, Sep p m U k Jᶜ J) →
            ((t - s : ℕ) : ℝ) + ∑ k ∈ Finset.Ico s t, dM p m k J hJ U
              ≤ Mnow p m t J hJ U - Mnow p m s J hJ U)} = 0 := by
          rw [measureReal_def, hnull]; simp
        rw [hzero, add_zero]
    _ ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * proxy (dMbound s) (t - s))) :=
        measure_max_abs_Mcum_window_le hp0.le hp1.le m J hJ hK
          (proxy_pos (fun k _ => by simp only [dMbound]; positivity) hK) le_rfl hε hεc

/-! ## 4. The exact residual: arithmetic of the computed constants -/

/-- `16K² ≤ C²` for the computed envelope `C = 4(s+K)+10`. -/
lemma Csq_ge (s K : ℕ) : 16 * (K : ℝ) ^ 2 ≤ (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2 := by
  have h1 : (K : ℝ) ≤ ((s + K : ℕ) : ℝ) := by
    have h : K ≤ s + K := Nat.le_add_left K s
    exact_mod_cast h
  have h2 : 4 * (K : ℝ) ≤ 4 * ((s + K : ℕ) : ℝ) + 10 := by linarith
  have h3 : (0 : ℝ) ≤ 4 * (K : ℝ) := by
    have h4 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  calc 16 * (K : ℝ) ^ 2 = (4 * (K : ℝ)) ^ 2 := by ring
    _ ≤ (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2 := pow_le_pow_left₀ h3 h2 2

/-- **The profile is vacuous at the paper's scale.**

At the paper's deviation `ε = L^{3/4}`, on any window of length `K ≥ L ≥ 1`, the right-hand side
`2(K+1)·exp(-ε²/(4KC²))`, `C = 4(s+K)+10`, is **at least `1`**: the maximal inequality carries no
information there.  Computation: `4KC² ≥ 64K³ ≥ 64L³`, while `ε = L^{3/4} ≤ L` gives `ε² ≤ L²`,
so the exponent is at most `L²/(64L³) = 1/(64L) ≤ 1/64`, whence
`exp(-ε²/(4KC²)) ≥ exp(-1/64) ≥ 1 - 1/64 ≥ 1/2`. -/
theorem profile_rhs_ge_one {K L s : ℕ} (hL : 1 ≤ L) (hLK : L ≤ K) :
    1 ≤ 2 * ((K : ℝ) + 1) *
      Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2)
        / (4 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2)) := by
  have hK : 1 ≤ K := le_trans hL hLK
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLK' : (L : ℝ) ≤ (K : ℝ) := by exact_mod_cast hLK
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  set C : ℝ := 4 * ((s + K : ℕ) : ℝ) + 10 with hCdef
  have hCl : 16 * (K : ℝ) ^ 2 ≤ C ^ 2 := Csq_ge s K
  have hCpos : (0 : ℝ) < C := by
    have h0 : (0 : ℝ) ≤ ((s + K : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [hCdef]; linarith
  have hD : (0 : ℝ) < 4 * (K : ℝ) * C ^ 2 := by positivity
  have hεL : (L : ℝ) ^ (3 / 4 : ℝ) ≤ (L : ℝ) :=
    Real.rpow_le_self_of_one_le hLr (by norm_num)
  have hε0 : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hε2 : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 ≤ (L : ℝ) ^ 2 := by
    have hmm := mul_self_le_mul_self hε0 hεL
    calc ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2
        = (L : ℝ) ^ (3 / 4 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := sq _
      _ ≤ (L : ℝ) * (L : ℝ) := hmm
      _ = (L : ℝ) ^ 2 := (sq _).symm
  have hden : 64 * (K : ℝ) ^ 3 ≤ 4 * (K : ℝ) * C ^ 2 := by
    have h0 : (0 : ℝ) ≤ 4 * (K : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left hCl h0
    nlinarith [h]
  have hexp_le : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (4 * (K : ℝ) * C ^ 2) ≤ 1 / 64 := by
    rw [div_le_iff₀ hD]
    have h2 : (L : ℝ) ^ 2 ≤ (K : ℝ) ^ 3 := by nlinarith [hKr, hLK', hKpos]
    have h3 : (K : ℝ) ^ 3 ≤ (4 * (K : ℝ) * C ^ 2) / 64 := by linarith
    nlinarith [hε2, h2, h3]
  have hexp_le' : ((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2
      / (4 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2) ≤ 1 / 64 := by
    simp only [hCdef] at hexp_le ⊢
    exact hexp_le
  have h_exp : (1 : ℝ) / 2 ≤ Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2)
      / (4 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2)) := by
    have h1 : Real.exp (-(1 / 64 : ℝ)) ≤
        Real.exp (-(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2)
          / (4 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2)) := by
      refine Real.exp_le_exp.2 ?_
      have hle := hexp_le'
      have he : -(((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2)
            / (4 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2)
          = -((((L : ℝ) ^ (3 / 4 : ℝ)) ^ 2)
            / (4 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2)) := by ring
      rw [he]
      linarith
    have h2 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 64 : ℝ)) := by
      have := Real.add_one_le_exp (-(1 / 64 : ℝ))
      linarith
    linarith
  have hfin : (1 : ℝ) ≤ 2 * ((K : ℝ) + 1) * (1 / 2) := by nlinarith [hKr]
  exact le_trans hfin (mul_le_mul_of_nonneg_left h_exp (by positivity))

/-- **The honest scaled statement (sharp form).**  Whenever the profile's right-hand side is
`< 1` — i.e. whenever it says anything — the deviation satisfies `ε² > 2 K C²`: with
`D = 4KC²` and `exp(-x) ≥ 1 - x`,

  `1 > 2(K+1) exp(-ε²/D) ≥ 2(K+1)(1 - ε²/D)`,  hence `ε²/D > 1 - 1/(2(K+1)) ≥ 1/2`. -/
theorem profile_informative_imp {K s : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hlt : 2 * ((K : ℝ) + 1) *
      Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2)) < 1) :
    2 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2 < ε ^ 2 := by
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKr0 : (0 : ℝ) < (K : ℝ) := by linarith
  set C : ℝ := 4 * ((s + K : ℕ) : ℝ) + 10 with hCdef
  have hCpos : (0 : ℝ) < C := by
    have h0 : (0 : ℝ) ≤ ((s + K : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [hCdef]; linarith
  have hD : (0 : ℝ) < 4 * (K : ℝ) * C ^ 2 := by positivity
  have hden : (0 : ℝ) < 2 * ((K : ℝ) + 1) := by positivity
  have hlt' : 2 * ((K : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * C ^ 2)) < 1 := by
    simpa only [hCdef] using hlt
  have h1 : Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * C ^ 2)) < 1 / (2 * ((K : ℝ) + 1)) := by
    rw [lt_div_iff₀ hden]
    calc Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * C ^ 2)) * (2 * ((K : ℝ) + 1))
        = 2 * ((K : ℝ) + 1) * Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * C ^ 2)) := by ring
      _ < 1 := hlt'
  have hexp_ge : 1 - ε ^ 2 / (4 * (K : ℝ) * C ^ 2)
      ≤ Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * C ^ 2)) := by
    have h := Real.add_one_le_exp (-(ε ^ 2 / (4 * (K : ℝ) * C ^ 2)))
    have he : -(ε ^ 2) / (4 * (K : ℝ) * C ^ 2) = -(ε ^ 2 / (4 * (K : ℝ) * C ^ 2)) := by ring
    rw [he]
    linarith
  have hquart : 1 / (2 * ((K : ℝ) + 1)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
    nlinarith [hKr]
  have hx : (1 : ℝ) / 2 < ε ^ 2 / (4 * (K : ℝ) * C ^ 2) := by
    have h3 : 1 - ε ^ 2 / (4 * (K : ℝ) * C ^ 2) < 1 / (2 * ((K : ℝ) + 1)) :=
      lt_of_le_of_lt hexp_ge h1
    linarith
  have h4 := (lt_div_iff₀ hD).1 hx
  have h5 : (1 / 2 : ℝ) * (4 * (K : ℝ) * C ^ 2) = 2 * (K : ℝ) * C ^ 2 := by ring
  have h6 : 2 * (K : ℝ) * C ^ 2 < ε ^ 2 := by linarith [h4, h5]
  simpa only [hCdef] using h6

/-- **The scale needed: `ε ≳ K^{3/2}`.**  From the sharp form and `C² ≥ 16K²`, an informative
instance forces `ε² > 32 K³`.  Compare the paper's `ε = L^{3/4}` at `K ≈ L`: a factor
`L^{3/4}` short. -/
theorem profile_scale_cubic {K s : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hlt : 2 * ((K : ℝ) + 1) *
      Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2)) < 1) :
    32 * (K : ℝ) ^ 3 < ε ^ 2 := by
  have h := profile_informative_imp hK hε hlt
  have hC := Csq_ge s K
  have hKr : (0 : ℝ) < (K : ℝ) := by
    have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  nlinarith [h, hC]

/-- **The needed envelope.**  Equivalently, an informative instance on a window of length `K` at
deviation `ε` forces `C² < ε²/(2K)` for the envelope `C` of the increments.  At `ε = L^{3/4}` and
`K ≈ L` this reads `C ≲ L^{1/4}`, whereas `abs_dM_le` gives `C = 4n+10 ≈ 4L`: the missing input
is a *local* increment bound, not a martingale estimate. -/
theorem needed_envelope {K s : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hlt : 2 * ((K : ℝ) + 1) *
      Real.exp (-(ε ^ 2) / (4 * (K : ℝ) * (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2)) < 1) :
    (4 * ((s + K : ℕ) : ℝ) + 10) ^ 2 < ε ^ 2 / (2 * (K : ℝ)) := by
  have h := profile_informative_imp hK hε hlt
  have hKr0 : (0 : ℝ) < (K : ℝ) := by
    have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [h]

/-! ## 5. Axiom audit -/


end LocMax
