/-
# Exact obstruction to the current `LeaderRange` instantiation

`LocMoveLocal.LeaderRange` (in `Swarm/LocMoveLocalWindow.lean`) is the only
geometric input still open in the local-martingale route.  Its spatial window is

  `[A - ⌈L^{1/16}⌉, A + L)`      (cardinality `L + ⌈L^{1/16}⌉`),

while the time window on which it is required is `[s, s + T*L)`
(`LocMoveLocalTotal.exists_measure_sep_window_dev_le_total`).

This file proves, on the actual definitions, that the two scales are incompatible:

* `wide_span_le` / `leaderRange_span_le`: any `LeaderRange` window forces the read sites of
  two separated walkers at two times of the window to satisfy
  `X k₂ j₂ - X k₁ j₁ ≤ L + ⌈L^{1/16}⌉ - 3`.
* `X_add_of_run`: along a run of right jumps the actual trajectory rises by the number of
  steps (`X` is nearest-neighbour by construction).
* `leaderRange_fails_of_right_run`: hence, for `T ≥ 2`, a single separated walker that jumps
  right at every step of the window makes `LeaderRange` **false for every anchor** `A`.
* `margin_short`: the margin needed to host the span reachable from `d_r ≤ L` plus
  nearest-neighbour motion, `L + 2*T*L + 2`, exceeds the available `L + ⌈L^{1/16}⌉` for every
  `T ≥ 1`, `L ≥ 2`.
* `wide_of_record_window`: the repair.  With margins `M = L + 2*T*L + 2`, `Up = L`,
  `LeaderRangeW` follows from `d_r ≤ L` and nearest-neighbour motion alone;
  `paper_window_suffices` checks that the paper's `[r-(T+3)L, r+(T+3)L]` has that width.

Scope: deterministic statements about the definitions of `LocMoveLocalWindow.lean`.  They do
not assert anything about the array measure; the probabilistic statement that the failing
position pattern occurs with positive mass is the remaining gap named in `REPORT.md`.
-/
import Swarm.LocMoveLocalWindow

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Finset

namespace LocLeaderObstruction

open LocMoveLocal LocSumAct SepGroup.Model Swarming.Uniform

variable {N : ℕ} {p : ℝ} {m : ℕ} {J : Finset (Fin N)} {U : Array N} {L : ℕ}

/-! ### The same window with its two spatial margins exposed -/

/-- `LeaderRange` with the lower margin `M` and the upper margin `Up` decoupled from the
scale parameter `L`.  The original definition is the case `M = ⌈L^{1/16}⌉`, `Up = L`. -/
def LeaderRangeW (p : ℝ) (m : ℕ) (J : Finset (Fin N)) (M Up A s t : ℕ) (U : Array N) : Prop :=
  ∀ k ∈ Finset.Ico s t, ∃ i ∈ Jᶜ, ∀ j ∈ J, ∀ z ∈
    ({X p m U k j, X p m U k j + 1, X p m U k j - 1} : Finset ℤ),
    z.toNat ∈ Finset.Ico (A - M) (A + Up)

/-- `LeaderRange` is exactly the window `M = ⌈L^{1/16}⌉`, `Up = L`. -/
theorem leaderRange_iff_wide (L A s t : ℕ) :
    LeaderRange p m J L A s t U ↔ LeaderRangeW p m J (ellT (xOf L)) L A s t U :=
  Iff.rfl

/-! ### The necessary condition: the window must contain the whole span of read sites -/

/-- **Two read sites of the window differ by at most the window width minus one.**
The endpoints are the read sites `X k₁ j₁ - 1` and `X k₂ j₂ + 1` of walkers of `J` at two
times of the window.  Nonnegativity makes `Int.toNat` the identity there. -/
theorem wide_span_le {M Up A s t : ℕ} {j₁ j₂ : Fin N}
    (h : LeaderRangeW p m J M Up A s t U) (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J)
    {k₁ k₂ : ℕ} (hk₁ : k₁ ∈ Finset.Ico s t) (hk₂ : k₂ ∈ Finset.Ico s t)
    (hX₁ : 1 ≤ X p m U k₁ j₁) (hX₂ : 0 ≤ X p m U k₂ j₂) :
    X p m U k₂ j₂ - X p m U k₁ j₁ ≤ ((M + Up : ℕ) : ℤ) - 3 := by
  obtain ⟨i₁, -, hi₁⟩ := h k₁ hk₁
  obtain ⟨i₂, -, hi₂⟩ := h k₂ hk₂
  have hz₁ := hi₁ j₁ h₁ (X p m U k₁ j₁ - 1) (by simp)
  have hz₂ := hi₂ j₂ h₂ (X p m U k₂ j₂ + 1) (by simp)
  rw [Finset.mem_Ico] at hz₁ hz₂
  have hnn₁ : 0 ≤ X p m U k₁ j₁ - 1 := by omega
  have hnn₂ : 0 ≤ X p m U k₂ j₂ + 1 := by omega
  have e₁ : ((X p m U k₁ j₁ - 1).toNat : ℤ) = X p m U k₁ j₁ - 1 :=
    Int.toNat_of_nonneg hnn₁
  have e₂ : ((X p m U k₂ j₂ + 1).toNat : ℤ) = X p m U k₂ j₂ + 1 :=
    Int.toNat_of_nonneg hnn₂
  have hlo : ((A - M : ℕ) : ℤ) ≤ X p m U k₁ j₁ - 1 := by
    have h' : ((A - M : ℕ) : ℤ) ≤ ((X p m U k₁ j₁ - 1).toNat : ℤ) := by
      exact_mod_cast hz₁.1
    omega
  have hhi : X p m U k₂ j₂ + 1 < ((A + Up : ℕ) : ℤ) := by
    have h' : ((X p m U k₂ j₂ + 1).toNat : ℤ) < ((A + Up : ℕ) : ℤ) := by
      exact_mod_cast hz₂.2
    omega
  have hspan : ((A + Up : ℕ) : ℤ) - ((A - M : ℕ) : ℤ) ≤ ((M + Up : ℕ) : ℤ) := by
    have h' : (A + Up) - (A - M) ≤ M + Up := by omega
    omega
  omega

/-- The same necessary condition for the actual `LeaderRange`. -/
theorem leaderRange_span_le (h : LeaderRange p m J L A s t U) {j₁ j₂ : Fin N}
    (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J)
    {k₁ k₂ : ℕ} (hk₁ : k₁ ∈ Finset.Ico s t) (hk₂ : k₂ ∈ Finset.Ico s t)
    (hX₁ : 1 ≤ X p m U k₁ j₁) (hX₂ : 0 ≤ X p m U k₂ j₂) :
    X p m U k₂ j₂ - X p m U k₁ j₁ ≤ ((L + ellT (xOf L) : ℕ) : ℤ) - 3 := by
  have h' := wide_span_le (M := ellT (xOf L)) (Up := L)
    ((leaderRange_iff_wide (p := p) (m := m) (J := J) (U := U) L A s t).1 h)
    h₁ h₂ hk₁ hk₂ hX₁ hX₂
  have hcomm : (ellT (xOf L) + L : ℕ) = L + ellT (xOf L) := Nat.add_comm _ _
  rwa [hcomm] at h'

/-- Contrapositive: a span larger than the window width refutes `LeaderRange` for **every**
anchor `A`. -/
theorem not_leaderRange_of_span {A s t : ℕ} {j₁ j₂ : Fin N} (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J)
    {k₁ k₂ : ℕ} (hk₁ : k₁ ∈ Finset.Ico s t) (hk₂ : k₂ ∈ Finset.Ico s t)
    (hX₁ : 1 ≤ X p m U k₁ j₁) (hX₂ : 0 ≤ X p m U k₂ j₂)
    (hspan : ((L + ellT (xOf L) : ℕ) : ℤ) - 3 < X p m U k₂ j₂ - X p m U k₁ j₁) :
    ¬ LeaderRange p m J L A s t U := by
  intro h
  have := leaderRange_span_le (L := L) (A := A) h h₁ h₂ hk₁ hk₂ hX₁ hX₂
  omega

/-! ### The arithmetic: the available margin is strictly too small -/

/-- `L^{1/16} ≤ L` for `L ≥ 1`. -/
theorem xOf_le_self {L : ℕ} (hL : 1 ≤ L) : xOf L ≤ (L : ℝ) := by
  calc xOf L = (L : ℝ) ^ (1 / 16 : ℝ) := rfl
    _ ≤ (L : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hL) (by norm_num)
    _ = (L : ℝ) := Real.rpow_one _

/-- `⌈L^{1/16}⌉ ≤ L` for `L ≥ 1`. -/
theorem ellT_le_self {L : ℕ} (hL : 1 ≤ L) : ellT (xOf L) ≤ L := by
  rw [ellT, Nat.ceil_le]
  exact xOf_le_self hL

/-- **The exact arithmetic failure.**  The span reachable from `d_r ≤ L` together with
`T*L` nearest-neighbour steps is `L + 2*T*L + 2`, which strictly exceeds the width
`L + ⌈L^{1/16}⌉` of the current `LeaderRange` window for every `T ≥ 1`, `L ≥ 2`. -/
theorem margin_short {T L : ℕ} (hT : 1 ≤ T) (hL : 2 ≤ L) :
    L + ellT (xOf L) < L + 2 * T * L + 2 := by
  have hℓ : ellT (xOf L) ≤ L := ellT_le_self (by omega)
  have h2 : L ≤ T * L := by simpa using Nat.mul_le_mul_right L hT
  have hkey : 2 * T * L = T * L + T * L := by ring
  omega

/-! ### What the actual trajectory can do: a run of right jumps -/

/-- Along `r` consecutive right jumps the actual trajectory rises exactly by `r`. -/
theorem X_add_of_run {j : Fin N} {s r : ℕ}
    (hstep : ∀ k < r, X p m U (s + k + 1) j = X p m U (s + k) j + 1) :
    X p m U (s + r) j = X p m U s j + (r : ℤ) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hk : X p m U (s + r + 1) j = X p m U (s + r) j + 1 := hstep r (Nat.lt_succ_self r)
      have hrs : ∀ k < r, X p m U (s + k + 1) j = X p m U (s + k) j + 1 :=
        fun k hk' => hstep k (Nat.lt_trans hk' (Nat.lt_succ_self r))
      rw [show s + (r + 1) = s + r + 1 by omega, hk, ih hrs]
      push_cast
      ring

/-- **The obstruction.**  If one separated walker jumps right at every step of the record
window and the window is long (`T ≥ 2`), then `LeaderRange` fails for every anchor `A`. -/
theorem leaderRange_fails_of_right_run {A s T : ℕ} {j : Fin N} (hj : j ∈ J)
    (hT : 2 ≤ T) (hL : 2 ≤ L)
    (hstep : ∀ k < T * L - 1, X p m U (s + k + 1) j = X p m U (s + k) j + 1)
    (hstart : 1 ≤ X p m U s j) :
    ¬ LeaderRange p m J L A s (s + T * L) U := by
  have hTL : 2 ≤ T * L := le_trans (by norm_num : 2 ≤ 2 * 2) (Nat.mul_le_mul hT hL)
  have hk₁ : s ∈ Finset.Ico s (s + T * L) := by
    rw [Finset.mem_Ico]; constructor <;> omega
  have hk₂ : s + (T * L - 1) ∈ Finset.Ico s (s + T * L) := by
    rw [Finset.mem_Ico]; constructor <;> omega
  have hrise : X p m U (s + (T * L - 1)) j = X p m U s j + ((T * L - 1 : ℕ) : ℤ) :=
    X_add_of_run hstep
  have hX₂ : 0 ≤ X p m U (s + (T * L - 1)) j := by rw [hrise]; omega
  refine not_leaderRange_of_span (L := L) (A := A) (j₁ := j) (j₂ := j) hj hj hk₁ hk₂
    (by omega) hX₂ ?_
  have hℓ : ellT (xOf L) ≤ L := ellT_le_self (by omega)
  have h2L : 2 * L ≤ T * L := Nat.mul_le_mul_right L hT
  have hbig : L + ellT (xOf L) < T * L + 2 := by omega
  have hTL1 : 1 ≤ T * L := by omega
  have hc2 : ((T * L - 1 : ℕ) : ℤ) = ((T * L : ℕ) : ℤ) - 1 := by
    rw [Nat.cast_sub hTL1]; norm_num
  have hb : ((L + ellT (xOf L) : ℕ) : ℤ) < ((T * L : ℕ) : ℤ) + 2 := by
    exact_mod_cast hbig
  rw [hrise, hc2]
  omega


/-! ### The repair: a window of the paper's width is instantiable -/

/-- Position bounds with explicit margins imply `LeaderRangeW` (the proof of
`LocMoveLocal.leaderRange_of_position_bounds` with `⌈L^{1/16}⌉` replaced by `M`). -/
theorem wide_of_position_bounds {M Up A s t : ℕ}
    (hleader : ∀ k ∈ Finset.Ico s t, ∃ i : Fin N, i ∈ Jᶜ)
    (hpos : ∀ k ∈ Finset.Ico s t, ∀ j ∈ J,
      ((A - M : ℕ) : ℤ) + 1 ≤ X p m U k j ∧
        X p m U k j + 1 < ((A + Up : ℕ) : ℤ)) :
    LeaderRangeW p m J M Up A s t U := by
  intro k hk
  obtain ⟨i, hi⟩ := hleader k hk
  refine ⟨i, hi, ?_⟩
  intro j hj z hz
  have hb := hpos k hk j hj
  have hzmem : z = X p m U k j ∨ z = X p m U k j + 1 ∨ z = X p m U k j - 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
  have hzlower : ((A - M : ℕ) : ℤ) ≤ z := by
    rcases hzmem with rfl | rfl | rfl <;> omega
  have hzupper : z < ((A + Up : ℕ) : ℤ) := by
    rcases hzmem with rfl | rfl | rfl <;> omega
  have hz0 : 0 ≤ z := by
    have h0 : (0 : ℤ) ≤ ((A - M : ℕ) : ℤ) := by positivity
    omega
  have e : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
  rw [Finset.mem_Ico]
  constructor
  · have h1 : ((A - M : ℕ) : ℤ) ≤ ((z.toNat : ℕ) : ℤ) := by omega
    exact_mod_cast h1
  · have h1 : ((z.toNat : ℕ) : ℤ) < ((A + Up : ℕ) : ℤ) := by omega
    exact_mod_cast h1

/-- **The corrected window.**  If `d_r ≤ L` at time `s` (all separated walkers at most `L`
below the record `R`), positions stay nonnegative, and `R` is large, then the window with
margins `M = L + 2*T*L + 2` below and `Up = L` above the anchor `R + T*L + 1` contains every
read site of the whole record window `[s, s + T*L)`.  No probabilistic input is used. -/
theorem wide_of_record_window {R s t T : ℕ}
    (hleader : ∀ k ∈ Finset.Ico s t, ∃ i : Fin N, i ∈ Jᶜ)
    (hL : 1 ≤ L) (hR : L + T * L + 1 ≤ R)
    (hpos : ∀ k ∈ Finset.Ico s t, ∀ j ∈ J,
      (R : ℤ) - (L : ℤ) - ((T * L : ℕ) : ℤ) ≤ X p m U k j ∧
        X p m U k j ≤ (R : ℤ) + ((T * L : ℕ) : ℤ)) :
    LeaderRangeW p m J (L + 2 * T * L + 2) L (R + T * L + 1) s t U := by
  refine wide_of_position_bounds (M := L + 2 * T * L + 2) (Up := L) (A := R + T * L + 1)
    hleader ?_
  intro k hk j hj
  have hb := hpos k hk j hj
  have hkey : L + 2 * T * L + 2 = (L + T * L + 1) + (T * L + 1) := by ring
  constructor
  · have hAM : R + T * L + 1 - (L + 2 * T * L + 2) = R - (L + T * L + 1) := by
      rw [hkey]; omega
    have hcast : ((R - (L + T * L + 1) : ℕ) : ℤ) =
        (R : ℤ) - ((L : ℤ) + ((T * L : ℕ) : ℤ) + 1) := by
      rw [Nat.cast_sub hR, Nat.cast_add, Nat.cast_add, Nat.cast_one]
    rw [hAM, hcast]
    linarith [hb.1]
  · have hb2 : X p m U k j ≤ (R : ℤ) + ((T * L : ℕ) : ℤ) := hb.2
    have hLz : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
    have hgoal : (((R + T * L + 1) + L : ℕ) : ℤ) =
        (R : ℤ) + ((T * L : ℕ) : ℤ) + 1 + (L : ℤ) := by
      push_cast
      ring
    rw [hgoal]
    linarith


theorem paper_window_suffices {T L : ℕ} (hL : 1 ≤ L) :
    L + 2 * T * L + 2 ≤ 2 * (T + 3) * L := by
  nlinarith

/-- Along `r` consecutive left jumps the actual trajectory falls exactly by `r`. -/
theorem X_sub_of_run {j : Fin N} {s r : ℕ}
    (hstep : ∀ k < r, X p m U (s + k + 1) j = X p m U (s + k) j - 1) :
    X p m U (s + r) j = X p m U s j - (r : ℤ) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hk : X p m U (s + r + 1) j = X p m U (s + r) j - 1 := hstep r (Nat.lt_succ_self r)
      have hrs : ∀ k < r, X p m U (s + k + 1) j = X p m U (s + k) j - 1 :=
        fun k hk' => hstep k (Nat.lt_trans hk' (Nat.lt_succ_self r))
      rw [show s + (r + 1) = s + r + 1 by omega, hk, ih hrs]
      push_cast
      ring

/-- **The obstruction in the form used by the record window.**  A separated walker that is at
most `L` below the record `R` at time `s` and jumps right at every step of the window
(`T ≥ 2`) refutes `LeaderRange` for every anchor. -/
theorem leaderRange_fails_of_record_right_run {A s T R : ℕ} {j : Fin N} (hj : j ∈ J)
    (hT : 2 ≤ T) (hL : 2 ≤ L) (hR : L + 1 ≤ R)
    (hstart : (R : ℤ) - (L : ℤ) ≤ X p m U s j)
    (hstep : ∀ k < T * L - 1, X p m U (s + k + 1) j = X p m U (s + k) j + 1) :
    ¬ LeaderRange p m J L A s (s + T * L) U := by
  have hRz : (1 : ℤ) ≤ (R : ℤ) - (L : ℤ) := by
    have : (L : ℤ) + 1 ≤ (R : ℤ) := by exact_mod_cast hR
    omega
  exact leaderRange_fails_of_right_run hj hT hL hstep (by omega)

/-- **Two runs cover `T = 1` as well.**  If two separated walkers start ordered
(`X s j₂ ≤ X s j₁`), the lower one is at least `T*L` above zero and then moves left at every
step while the upper one moves right at every step, `LeaderRange` fails for every anchor.
For `T = 1` this is the only obstruction available (a single walker of the window rises by
`L - 1`, which fits the window `L + ⌈L^{1/16}⌉`). -/
theorem leaderRange_fails_of_two_runs {A s T : ℕ} {j₁ j₂ : Fin N} (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J)
    (hT : 1 ≤ T) (hL : 2 ≤ L)
    (horder : X p m U s j₂ ≤ X p m U s j₁)
    (hpos₂ : T * L ≤ X p m U s j₂)
    (hup : ∀ k < T * L - 1, X p m U (s + k + 1) j₁ = X p m U (s + k) j₁ + 1)
    (hdown : ∀ k < T * L - 1, X p m U (s + k + 1) j₂ = X p m U (s + k) j₂ - 1) :
    ¬ LeaderRange p m J L A s (s + T * L) U := by
  have hTL1 : 1 ≤ T * L := by
    have : 1 ≤ 1 * L := by omega
    exact le_trans this (Nat.mul_le_mul_right L hT)
  have hk : s + (T * L - 1) ∈ Finset.Ico s (s + T * L) := by
    rw [Finset.mem_Ico]; constructor <;> omega
  have hrise₁ : X p m U (s + (T * L - 1)) j₁
      = X p m U s j₁ + ((T * L - 1 : ℕ) : ℤ) := X_add_of_run hup
  have hrise₂ : X p m U (s + (T * L - 1)) j₂
      = X p m U s j₂ - ((T * L - 1 : ℕ) : ℤ) := X_sub_of_run hdown
  have hsub : ((T * L - 1 : ℕ) : ℤ) = ((T * L : ℕ) : ℤ) - 1 := by
    rw [Nat.cast_sub hTL1]; norm_num
  have hlow : 1 ≤ X p m U (s + (T * L - 1)) j₂ := by
    rw [hrise₂, hsub]
    have h1 : ((T * L : ℕ) : ℤ) ≤ X p m U s j₂ := by exact_mod_cast hpos₂
    omega
  refine not_leaderRange_of_span (L := L) (A := A) (j₁ := j₂) (j₂ := j₁) h₂ h₁ hk hk
    hlow (by omega) ?_
  have hℓ : ellT (xOf L) ≤ L := ellT_le_self (by omega)
  have hLTL : L ≤ T * L := by simpa using Nat.mul_le_mul_right L hT
  have hsum : L + ellT (xOf L) ≤ 2 * L := by omega
  have hcast : ((L + ellT (xOf L) : ℕ) : ℤ) ≤ ((2 * L : ℕ) : ℤ) := by exact_mod_cast hsum
  have hcast2 : ((2 * L : ℕ) : ℤ) ≤ 2 * ((T * L : ℕ) : ℤ) := by
    have h2 : 2 * L ≤ 2 * (T * L) := Nat.mul_le_mul_left 2 hLTL
    calc ((2 * L : ℕ) : ℤ) ≤ ((2 * (T * L) : ℕ) : ℤ) := by exact_mod_cast h2
      _ = 2 * ((T * L : ℕ) : ℤ) := by push_cast; ring
  rw [hrise₁, hrise₂, hsub]
  omega

/-- **The obstruction does not come from the record defect.**  Even with `d_r = 0` (all
separated walkers exactly at the record) the two runs of `leaderRange_fails_of_two_runs` span
`2*(T*L - 1)` sites, which already exceeds the window width for every `T ≥ 1`. -/
theorem leaderRange_fails_of_two_runs_at_record {A s T : ℕ} {j₁ j₂ : Fin N}
    (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J) (hT : 1 ≤ T) (hL : 2 ≤ L)
    (heq : X p m U s j₂ = X p m U s j₁)
    (hpos : T * L ≤ X p m U s j₁)
    (hup : ∀ k < T * L - 1, X p m U (s + k + 1) j₁ = X p m U (s + k) j₁ + 1)
    (hdown : ∀ k < T * L - 1, X p m U (s + k + 1) j₂ = X p m U (s + k) j₂ - 1) :
    ¬ LeaderRange p m J L A s (s + T * L) U := by
  refine leaderRange_fails_of_two_runs (A := A) (s := s) (T := T) h₁ h₂ hT hL ?_ ?_ hup hdown
  · rw [heq]
  · rw [heq]; exact hpos

/-- Concrete instance of the arithmetic failure: `T = 2`, `L = 4` gives available width
`4 + ⌈4^{1/16}⌉ = 6`, while the reachable span needs `4 + 2*2*4 + 2 = 22`. -/
example : 4 + ellT (xOf 4) < 4 + 2 * 2 * 4 + 2 :=
  margin_short (T := 2) (L := 4) (by norm_num) (by norm_num)

end LocLeaderObstruction
