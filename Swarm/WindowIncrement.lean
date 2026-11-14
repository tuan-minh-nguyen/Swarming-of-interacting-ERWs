/-
# The separated-group increment on the windowed envelope

This file composes `WindowStep.hBound_le_window` with the per-walker position step and the
six-part decomposition of `LocGroupQ.abs_WA_step_le_env`, obtaining the actual one-step bound

    |W_{n+1}^{I,J} - W_n^{I,J}| ≤ 2 B + 2 ((2p-1)/p) N ((1+B) B)

with the *windowed* envelopes `B = EfixWin A` and `B' = EsumWin A`, under the record-window
geometry: every current and next position is `≥ A-1` (`hAn`, `hAs`) and every next position of
`Jᶜ` is `≥ A` (`hag`).  No prefix supremum is used.
-/
import Swarm.WindowStep

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SiteWindow

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift SwarmSiteDiff SwarmQVariance LocGroupQ

variable {N : ℕ}

/-! ### 1. The position-move part -/

/-- The position-move part of one walker's potential change, bounded by the windowed `EfixWin`.
Both the current and the next level must lie in `[A-1, ∞)`. -/
theorem abs_HA_pos_step_le_EfixWin {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (U : Array N) {A : ℕ} {k : Fin N} (hk : k ∈ K)
    (hAn : A ≤ (X p m U n k).toNat + 1) (hAs : A ≤ (X p m U (n + 1) k).toNat + 1) :
    |HA p m U n Jᶜ (X p m U (n + 1) k) - HA p m U n Jᶜ (X p m U n k)|
      ≤ EfixWin p m n J K hK A U := by
  have hd : X p m U (n + 1) k = X p m U n k + 1 ∨ X p m U (n + 1) k = X p m U n k - 1 ∨
      X p m U (n + 1) k = X p m U n k := by
    rcases X_succ_sub_X p m U n k with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have h := abs_HZ_step_le (w := wA p m U n Jᶜ) (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) hd
  have hx : X p m U n k ≤ ((xTop p m n K hK U : ℕ) : ℤ) := by
    have h1 : X p m U n k ≤ ((n : ℕ) : ℤ) := by
      have := SwarmM3.abs_X_le p m U n k
      rw [abs_le] at this
      omega
    have h2 : X p m U n k ≤ ((n + 2 : ℕ) : ℤ) := by push_cast; omega
    have h3 : ((xTop p m n K hK U : ℕ) : ℤ)
        = min (((n + 2 : ℕ) : ℤ)) (((Rmax p m n K hK U : ℕ) : ℤ) + 1) := by
      rw [xTop, Nat.cast_min]
      push_cast
      ring_nf
    rw [h3]
    exact le_min h2 (by linarith [X_le_Rmax (p := p) (m := m) (n := n) hK hk U])
  have hy : X p m U (n + 1) k ≤ ((xTop p m n K hK U : ℕ) : ℤ) := X_succ_le_xTop hK hk U
  refine le_trans h (max_le ?_ ?_)
  · exact hfix_le_EfixWin hK U (by omega) (by omega)
  · exact hfix_le_EfixWin hK U (by omega) (by omega)

/-! ### 2. The weight-update part -/

/-- The weight-update part of one walker's potential change, bounded by the windowed envelopes. -/
theorem abs_HA_weight_step_le_window {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    {J K : Finset (Fin N)} (hK : K.Nonempty) (U : Array N) {A : ℕ} {y : ℤ}
    (hy : y ≤ (xTop p m n K hK U : ℤ))
    (hag : ∀ u : ℕ, u < A → wA p m U n Jᶜ u = wA p m U (n + 1) Jᶜ u)
    {B S : ℝ} (hB : EfixWin p m n J K hK A U ≤ B) (hS : EsumWin p m n J K hK A U ≤ S)
    (hB1 : 0 ≤ B) (hS0 : 0 ≤ S) :
    |HA p m U (n + 1) Jᶜ y - HA p m U n Jᶜ y|
      ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * S) := by
  have hw0 : ∀ u, 0 < wA p m U n Jᶜ u := wA_pos p m U hp0.le n Jᶜ
  have hw1 : ∀ u, wA p m U n Jᶜ u ≤ 1 := wA_le_one p m U hp1 n Jᶜ
  have hw0' : ∀ u, 0 < wA p m U (n + 1) Jᶜ u := wA_pos p m U hp0.le (n + 1) Jᶜ
  have hw1' : ∀ u, wA p m U (n + 1) Jᶜ u ≤ 1 := wA_le_one p m U hp1 (n + 1) Jᶜ
  have hv : ∀ u, wA p m U n Jᶜ u = 1 / 2 ∨ wA p m U n Jᶜ u = p := wA_eq_half_or p m U n Jᶜ
  have hv' : ∀ u, wA p m U (n + 1) Jᶜ u = 1 / 2 ∨ wA p m U (n + 1) Jᶜ u = p :=
    wA_eq_half_or p m U (n + 1) Jᶜ
  have hle : ∀ u, wA p m U n Jᶜ u ≤ wA p m U (n + 1) Jᶜ u := fun v =>
    wA_le_succ p hp0.le m U n Jᶜ v
  by_cases hy0 : 0 ≤ y
  swap
  · have h1 : HA p m U (n + 1) Jᶜ y = (y : ℝ) := by
      show SepGroup.HZ (wA p m U (n + 1) Jᶜ) y = _
      rw [SepGroup.HZ_neg (by omega)]
    have h2 : HA p m U n Jᶜ y = (y : ℝ) := by
      show SepGroup.HZ (wA p m U n Jᶜ) y = _
      rw [SepGroup.HZ_neg (by omega)]
    rw [h1, h2, sub_self, abs_zero]
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hc : (0 : ℝ) ≤ (2 * p - 1) / p := by
      apply div_nonneg (by linarith) (by linarith)
    exact mul_nonneg (mul_nonneg hc hN) (mul_nonneg (by linarith) hS0)
  have hHA1 : HA p m U (n + 1) Jᶜ y = Hfix (wA p m U (n + 1) Jᶜ) y.toNat := by
    show SepGroup.HZ (wA p m U (n + 1) Jᶜ) y = _
    rw [SepGroup.HZ_nonneg hy0]
  have hHA2 : HA p m U n Jᶜ y = Hfix (wA p m U n Jᶜ) y.toNat := by
    show SepGroup.HZ (wA p m U n Jᶜ) y = _
    rw [SepGroup.HZ_nonneg hy0]
  rw [hHA1, hHA2]
  have hmono : Hfix (wA p m U (n + 1) Jᶜ) y.toNat ≤ Hfix (wA p m U n Jᶜ) y.toNat :=
    Hfix_mono _ _ hw0 hw1 hw0' hw1' hle y.toNat
  have hneg : Hfix (wA p m U (n + 1) Jᶜ) y.toNat - Hfix (wA p m U n Jᶜ) y.toNat ≤ 0 := by
    linarith
  rw [abs_of_nonpos hneg, neg_sub]
  have hm : y.toNat ≤ xTop p m n K hK U := by
    have h1 : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy0
    have h2 : ((y.toNat : ℕ) : ℤ) ≤ ((xTop p m n K hK U : ℕ) : ℤ) := by rw [h1]; exact hy
    exact_mod_cast h2
  have hp0ne : p ≠ 0 := by linarith
  refine le_trans (Hfix_diff_le_hBound (p := p) hp0 hp0ne hp1 hw0 hw1 hw0' hw1' hv hv'
    hle y.toNat) ?_
  exact hBound_le_window hp0 hp1 hK U hm hag hB hS hB1 hS0

/-! ### 3. The separated-group increment -/

/-- **The windowed one-step bound.**  On `(sep)`, with the current and next positions at levels
`≥ A-1` and the changed sites `≥ A`, the actual increment of `W^{I,J}` is bounded by
`2·EfixWin + 2·((2p-1)/p)·N·(1+EfixWin)·EsumWin`. -/
theorem abs_WA_step_le_window {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {U : Array N} (hsep : SepSet p m n I J U) {A : ℕ}
    (hAn : ∀ k ∈ I ∪ J, A ≤ (X p m U n k).toNat + 1)
    (hAs : ∀ k ∈ I ∪ J, A ≤ (X p m U (n + 1) k).toNat + 1)
    (hag : ∀ u : ℕ, u < A → wA p m U n Jᶜ u = wA p m U (n + 1) Jᶜ u)
    {B S : ℝ}
    (hB : EfixWin p m n J (I ∪ J) (hI.mono Finset.subset_union_left) A U ≤ B)
    (hS : EsumWin p m n J (I ∪ J) (hI.mono Finset.subset_union_left) A U ≤ S)
    (hB1 : 0 ≤ B) (hS0 : 0 ≤ S) :
    |WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ|
      ≤ 2 * B + 2 * (((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * S)) := by
  have hIK : ∀ k ∈ I, k ∈ I ∪ J := fun k hk => Finset.mem_union_left _ hk
  have hJK : ∀ k ∈ J, k ∈ I ∪ J := fun k hk => Finset.mem_union_right _ hk
  set f : Fin N → ℝ := fun k => HA p m U (n + 1) Jᶜ (X p m U (n + 1) k) with hf
  set g : Fin N → ℝ := fun k => HA p m U n Jᶜ (X p m U n k) with hg
  set md : Fin N → ℝ := fun k => HA p m U n Jᶜ (X p m U (n + 1) k) with hmd
  have hBp : ∀ k ∈ I ∪ J, |md k - g k| ≤ EfixWin p m n J (I ∪ J)
      (hI.mono Finset.subset_union_left) A U := by
    intro k hk
    exact abs_HA_pos_step_le_EfixWin hp0.le hp1 (hI.mono Finset.subset_union_left) U hk
      (hAn k hk) (hAs k hk)
  have hBw : ∀ k ∈ I ∪ J, |f k - md k| ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * S) := by
    intro k hk
    exact abs_HA_weight_step_le_window hp0 hp1 (hI.mono Finset.subset_union_left) U
      (X_succ_le_xTop (hI.mono Finset.subset_union_left) hk U) hag hB hS hB1 hS0
  have eA : Swarming.Group.average I f - Swarming.Group.average I g
      = Swarming.Group.average I (fun i => f i - md i)
        + Swarming.Group.average I (fun i => md i - g i) := by
    have h1 : Swarming.Group.average I (fun i => f i - md i)
        = Swarming.Group.average I f - Swarming.Group.average I md := average_sub_group _ _ _
    have h2 : Swarming.Group.average I (fun i => md i - g i)
        = Swarming.Group.average I md - Swarming.Group.average I g := average_sub_group _ _ _
    rw [h1, h2]; ring
  have hWA1 : WA p m U (n + 1) I J hI hJ = Swarming.Group.average I f
      - Swarming.Group.maximumOn J hJ f := rfl
  have hWA0 : WA p m U n I J hI hJ = Swarming.Group.average I g
      - Swarming.Group.maximumOn J hJ g := rfl
  have b1 : |Swarming.Group.average I (fun i => f i - md i)|
      ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * S) :=
    abs_average_le_of_bound hI (fun i hi => hBw i (hIK i hi))
  have b2 : |Swarming.Group.maximumOn J hJ (fun j => f j - md j)|
      ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * S) :=
    abs_maximumOn_le_of_bound hJ (fun j hj => hBw j (hJK j hj))
  have b3 : |Swarming.Group.average I (fun i => md i - g i)| ≤ B :=
    le_trans (abs_average_le_of_bound hI (fun i hi => hBp i (hIK i hi))) hB
  have b4 : |Swarming.Group.maximumOn J hJ (fun j => md j - g j)| ≤ B :=
    le_trans (abs_maximumOn_le_of_bound hJ (fun j hj => hBp j (hJK j hj))) hB
  have b5 : |Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ md|
      ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * S) :=
    abs_sup'_sub_sup'_le (s := J) (hs := hJ) (fun j hj => hBw j (hJK j hj))
  have b6 : |Swarming.Group.maximumOn J hJ md - Swarming.Group.maximumOn J hJ g| ≤ B :=
    le_trans (abs_sup'_sub_sup'_le (s := J) (hs := hJ) (fun j hj => hBp j (hJK j hj))) hB
  rw [hWA1, hWA0]
  have key : (Swarming.Group.average I f - Swarming.Group.maximumOn J hJ f)
        - (Swarming.Group.average I g - Swarming.Group.maximumOn J hJ g)
      = (Swarming.Group.average I f - Swarming.Group.average I g)
        - (Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ g) := by ring
  rw [key, eA]
  have hA2 : |(Swarming.Group.average I (fun i => f i - md i)
        + Swarming.Group.average I (fun i => md i - g i))|
      ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * S) + B :=
    le_trans (abs_add_le _ _) (add_le_add b1 b3)
  have hM2 : |(Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ g)|
      ≤ ((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * S) + B := by
    have hsplit : (Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ g)
        = (Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ md)
          + (Swarming.Group.maximumOn J hJ md - Swarming.Group.maximumOn J hJ g) := by ring
    rw [hsplit]
    exact le_trans (abs_add_le _ _) (add_le_add b5 b6)
  calc |(Swarming.Group.average I (fun i => f i - md i)
          + Swarming.Group.average I (fun i => md i - g i))
        - (Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ g)|
      ≤ |(Swarming.Group.average I (fun i => f i - md i)
          + Swarming.Group.average I (fun i => md i - g i))|
        + |(Swarming.Group.maximumOn J hJ f - Swarming.Group.maximumOn J hJ g)| := abs_sub _ _
    _ ≤ 2 * B + 2 * (((2 * p - 1) / p) * (N : ℝ) * ((1 + B) * S)) := by
      linarith [hA2, hM2]

end SiteWindow
