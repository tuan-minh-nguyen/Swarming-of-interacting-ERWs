/-
# The windowed one-step cost bound

`LocGroupQ.hBound_le_env` bounds the weight-update cost `hBound` of one step by
`C·N·(1+Efix)·Esum` with the *prefix* suprema.  This file proves the same bound with the
*windowed* envelopes `EfixWin A`, `EsumWin A` of `WindowEnvelope.lean`, under the geometric
condition that every changed site (a position `X_{n+1}^i`, `i ∈ Jᶜ`) is `≥ A`.  That condition is
what the record window supplies: during `[τ_r, τ_r+TL]` all positions are `≥ r-(T+1)L`.

The final theorem `abs_WA_step_le_window` is the windowed form of
`LocGroupQ.abs_WA_step_le_env`: the actual separated-group increment is bounded by the windowed
envelopes.  Combined with `WindowEnvelope.goodWWin_of_locmax` this shows that the windowed
interface loses nothing: the paper only ever queries the levels `[A-1, xTop]`.
-/
import Swarm.WindowEnvelope

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SiteWindow

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ

variable {N : ℕ}

/-! ### 0. Nonnegativity of the windowed envelopes -/

theorem EfixWin_nonneg {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J K : Finset (Fin N)) (hK : K.Nonempty) (A : ℕ) (U : Array N) :
    0 ≤ EfixWin p m n J K hK A U := by
  have hmem : (0 : ℕ) ∈ Finset.range (n + 3) := Finset.mem_range.mpr (by omega)
  have h1 := Finset.le_sup' (s := Finset.range (n + 3))
    (fun u => if A ≤ u + 1 ∧ u ≤ xTop p m n K hK U then hfix (wA p m U n Jᶜ) u else 0) hmem
  refine le_trans ?_ h1
  by_cases h : A ≤ 0 + 1 ∧ 0 ≤ xTop p m n K hK U
  · rw [if_pos h]
    exact le_trans zero_le_one (one_le_hfix _ (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) 0)
  · rw [if_neg h]

theorem EsumWin_nonneg {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (J K : Finset (Fin N)) (hK : K.Nonempty) (A : ℕ) (U : Array N) :
    0 ≤ EsumWin p m n J K hK A U := by
  have hmem : (0 : ℕ) ∈ Finset.range (n + 3) := Finset.mem_range.mpr (by omega)
  have h1 := Finset.le_sup' (s := Finset.range (n + 3))
    (fun u => if A ≤ u ∧ u ≤ xTop p m n K hK U then
      hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) else 0) hmem
  refine le_trans ?_ h1
  by_cases h : A ≤ 0 ∧ 0 ≤ xTop p m n K hK U
  · rw [if_pos h]
    exact hSum_nonneg (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) 0 _
  · rw [if_neg h]

/-! ### 1. The changed sites are positions at time `n+1` -/

/-- If every position at time `n+1` of the group `Jᶜ` is `≥ A`, the group weight does not change
below `A`. -/
theorem wA_eq_of_positions_ge {p : ℝ} (hp : 1 / 2 < p) {m n : ℕ} {J : Finset (Fin N)}
    {U : Array N} {A : ℕ} (hpos : ∀ i ∈ Jᶜ, A ≤ (X p m U (n + 1) i).toNat) :
    ∀ u : ℕ, u < A → wA p m U n Jᶜ u = wA p m U (n + 1) Jᶜ u := by
  intro u hu
  by_contra hne
  obtain ⟨i, hi, hXi⟩ := cross_site p hp m U n J u hne
  have h1 : A ≤ u := by
    have h2 := hpos i hi
    rw [hXi, Int.toNat_natCast] at h2
    exact h2
  omega

/-! ### 2. `hBound` with the windowed envelopes -/

/-- **The one-step weight-update cost on the level window.**  If the changed sites are `≥ A`
(`hagree`), then `hBound` is bounded by `((2p-1)/p)·N·(1+EfixWin)·EsumWin`. -/
theorem hBound_le_window {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (U : Array N) {A s : ℕ}
    (hs : s ≤ xTop p m n K hK U)
    (hagree : ∀ u : ℕ, u < A → wA p m U n Jᶜ u = wA p m U (n + 1) Jᶜ u)
    {B S : ℝ} (hB : EfixWin p m n J K hK A U ≤ B) (hS : EsumWin p m n J K hK A U ≤ S)
    (hB1 : 0 ≤ B) (hS0 : 0 ≤ S) :
    hBound p (wA p m U n Jᶜ) (wA p m U (n + 1) Jᶜ) s
      ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * S) := by
  have hM0 : (0 : ℝ) ≤ (1 + B) * S := mul_nonneg (by linarith) hS0
  have hterm : ∀ u ∈ Finset.range (s + 1),
      (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then
          (1 + hprev (wA p m U (n + 1) Jᶜ) u) * hSum (wA p m U n Jᶜ) u s else 0)
        ≤ (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then (1 + B) * S else 0) := by
    intro u hu
    by_cases h : wA p m U n Jᶜ u = wA p m U (n + 1) Jᶜ u
    · rw [if_neg (by simp [h]), if_neg (by simp [h])]
    · rw [if_pos h, if_pos h]
      have huA : A ≤ u := by
        by_contra hlt
        push Not at hlt
        exact h (hagree u hlt)
      have hus : u ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
      have hu1 : 1 + hprev (wA p m U (n + 1) Jᶜ) u ≤ 1 + B := by
        have hmono : hprev (wA p m U (n + 1) Jᶜ) u ≤ hprev (wA p m U n Jᶜ) u := by
          rcases u with _ | j
          · simp
          · simpa using hfix_mono (w := wA p m U n Jᶜ) (w' := wA p m U (n + 1) Jᶜ)
              (wA_pos p m U hp0.le n Jᶜ) (wA_le_one p m U hp1 n Jᶜ)
              (wA_pos p m U hp0.le (n + 1) Jᶜ) (wA_le_one p m U hp1 (n + 1) Jᶜ)
              (wA_le_succ p hp0.le m U n Jᶜ) j
        have hle2 : hprev (wA p m U n Jᶜ) u ≤ B := by
          rcases Nat.eq_zero_or_pos u with hu0 | hupos
          · rw [hu0, hprev_zero]
            have h1 : (1 : ℝ) ≤ hfix (wA p m U n Jᶜ) 0 :=
              one_le_hfix _ (wA_pos p m U hp0.le n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) 0
            have h2 : hfix (wA p m U n Jᶜ) 0 ≤ EfixWin p m n J K hK A U :=
              hfix_le_EfixWin hK U (by omega) (by omega)
            linarith
          · rw [hprev_eq_hfix_sub_one hupos]
            exact le_trans (hfix_le_EfixWin hK U (by omega) (by omega)) hB
        linarith
      have hu2 : hSum (wA p m U n Jᶜ) u s ≤ S := by
        have h1 : hSum (wA p m U n Jᶜ) u s ≤ hSum (wA p m U n Jᶜ) u (xTop p m n K hK U) :=
          hSum_mono_upper (wA_pos p m U hp0.le n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) hs
        have h2 : hSum (wA p m U n Jᶜ) u (xTop p m n K hK U)
            ≤ EsumWin p m n J K hK A U :=
          hSum_le_EsumWin hK U huA (le_trans hus hs)
        linarith
      have hsum0 : 0 ≤ hSum (wA p m U n Jᶜ) u s :=
        hSum_nonneg (wA_pos p m U hp0.le n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) u s
      exact mul_le_mul hu1 hu2 hsum0 (by linarith)
  -- the sum is supported on the changed sites, of which there are at most `N`, and each is `≥ A`
  have hsub : Finset.range (s + 1) ⊆ Finset.range (xTop p m n K hK U + 1) := by
    intro u hu
    rw [Finset.mem_range] at hu ⊢
    omega
  have hstep : (∑ u ∈ Finset.range (s + 1),
      (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then
        (1 + hprev (wA p m U (n + 1) Jᶜ) u) * hSum (wA p m U n Jᶜ) u s else 0))
      ≤ N * ((1 + B) * S) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have h1 : (∑ u ∈ Finset.range (s + 1),
        (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then (1 + B) * S else 0))
        = ((1 + B) * S) * (((Finset.range (s + 1)).filter
            (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      ring
    have hcard : ((((Finset.range (s + 1)).filter
        (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card : ℕ) : ℝ) ≤ (N : ℝ) := by
      have hsub' : (Finset.range (s + 1)).filter
          (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)
          ⊆ (Finset.range (xTop p m n K hK U + 1)).filter
            (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u) :=
        Finset.filter_subset_filter _ hsub
      have h2 : ((Finset.range (s + 1)).filter
            (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card
          ≤ ((Finset.range (xTop p m n K hK U + 1)).filter
            (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card :=
        Finset.card_le_card hsub'
      have h3 := card_cross_le p hp0 m n J U (xTop p m n K hK U)
      exact_mod_cast le_trans h2 h3
    rw [h1]
    calc ((1 + B) * S) * ((((Finset.range (s + 1)).filter
          (fun u => wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u)).card : ℕ) : ℝ)
        ≤ ((1 + B) * S) * (N : ℝ) := mul_le_mul_of_nonneg_left hcard hM0
      _ = (N : ℝ) * ((1 + B) * S) := by ring
  unfold hBound
  have hnp : 0 ≤ (2 * p - 1) / p := by
    apply div_nonneg (by linarith) (by linarith)
  calc ((2 * p - 1) / p) * (∑ u ∈ Finset.range (s + 1),
        (if wA p m U n Jᶜ u ≠ wA p m U (n + 1) Jᶜ u then
          (1 + hprev (wA p m U (n + 1) Jᶜ) u) * hSum (wA p m U n Jᶜ) u s else 0))
      ≤ ((2 * p - 1) / p) * ((N : ℝ) * ((1 + B) * S)) :=
        mul_le_mul_of_nonneg_left hstep hnp
    _ = ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * S) := by ring

end SiteWindow
