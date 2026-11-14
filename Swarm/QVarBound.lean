/-
  **Actual `(Qslln)`-side variance bound for `Q^{I,J}` via the static potential maximum.**

  This file reduces the paper's log-fourth variance estimate for the actual separated-group
  martingale `Q^{I,J}` of `Swarm/WdriftJoint.lean` to a single explicit unconditional
  moment bound on the *static* individual potential at the window `[0, n+2]`:

    `windowMax p m n i U = max_{u < n+2} hfix (omegaN p m U i) u`.

  The reduction is genuine: the pointwise step of the actual group potential `H_n^{J^c}` is
  controlled by `(hcomp)` (`hcomp_h`, `hcomp_h_runMax`) through the walker's own mark weight
  `omegaN`, and one extra potential step is paid with `hfix_le_hprev_add_two`.  Nothing below
  asserts `(diam)`, `Swarm.Ballistic`, regeneration, or a common speed.
-/
import Swarm.WdriftJoint

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SwarmQVariance

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift

variable {N : ℕ}

/-! ### 1. One-step facts for the actual positions -/

/-- The increment of `drivenStep` is `±1`. -/
theorem drivenStep_eq_one_or_neg_one (u α : ℝ) : drivenStep u α = 1 ∨ drivenStep u α = -1 := by
  unfold drivenStep
  split_ifs <;> simp

/-- One step of the actual interacting trajectory, unfolded to the driving coordinate. -/
theorem X_succ_eq (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    X p m U (n + 1) i = X p m U n i +
      drivenStep (U (i, X p m U n i, L p m U n i (X p m U n i)))
        (rightProbability p m (trajectory p m U n).ell i (X p m U n i)) := rfl

/-- Every walker moves by exactly one lattice step. -/
theorem X_succ_sub_X (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    X p m U (n + 1) i = X p m U n i + 1 ∨ X p m U (n + 1) i = X p m U n i - 1 := by
  rw [X_succ_eq p m U n i]
  rcases drivenStep_eq_one_or_neg_one _ _ with h | h <;> rw [h] <;> [left; right] <;> ring

theorem X_succ_le_add_one (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    X p m U (n + 1) i ≤ X p m U n i + 1 := by
  rcases X_succ_sub_X p m U n i with h | h <;> omega

theorem X_le_succ_add_one (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    X p m U n i ≤ X p m U (n + 1) i + 1 := by
  rcases X_succ_sub_X p m U n i with h | h <;> omega

/-- Positions never exceed the time. -/
theorem X_le_time (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    X p m U n i ≤ (n : ℤ) := by
  induction n with
  | zero => simp [X]
  | succ k ih =>
      have h := X_succ_le_add_one p m U k i
      push_cast
      omega

/-- Positions never fall below minus the time. -/
theorem neg_time_le_X (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    -((n : ℤ)) ≤ X p m U n i := by
  induction n with
  | zero => simp [X]
  | succ k ih =>
      have h := X_le_succ_add_one p m U k i
      push_cast
      omega

/-- The running maximum never exceeds the time. -/
theorem runMax_le_time (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    runMax p m U i n ≤ (n : ℤ) := by
  refine Finset.sup'_le _ _ fun t ht => ?_
  have ht' : t ≤ n := by simpa using ht
  exact le_trans (X_le_time p m U t i) (by exact_mod_cast ht')

/-- The running maximum is nonnegative. -/
theorem runMax_nonneg' (p : ℝ) (m : ℕ) (U : Array N) (i : Fin N) (n : ℕ) :
    (0 : ℤ) ≤ runMax p m U i n := by
  have h1 : (trajectory p m U 0).pos i ≤ runMax p m U i n :=
    le_runMax_of_le p m U n i (Nat.zero_le n)
  simpa using h1

/-! ### 2. The static window potential `windowMax` -/

open SepGroup

/-- The maximum of the static individual potential `h^{omega_i}` over the window `[0, n+2)`.
This is the paper's `(maxmom)` object read on the actual mark sequence. -/
noncomputable def windowMax (p : ℝ) (m : ℕ) (n : ℕ) (i : Fin N) (U : Array N) : ℝ :=
  (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun u => hfix (omegaN p m U i) u)

theorem le_windowMax {p : ℝ} {m n : ℕ} {i : Fin N} {U : Array N} {u : ℕ} (hu : u < n + 2) :
    hfix (omegaN p m U i) u ≤ windowMax p m n i U :=
  Finset.le_sup' _ (Finset.mem_range.mpr hu)

theorem one_le_windowMax {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (i : Fin N)
    (U : Array N) : 1 ≤ windowMax p m n i U := by
  have h := le_windowMax (p := p) (m := m) (n := n) (i := i) (U := U) (u := 0) (by omega)
  have h1 := Cookie.one_le_hfix (omegaN p m U i)
    (fun u => omegaAt_pos p m U hp i (u : ℤ)) (fun u => omegaAt_le_one p m U hp1 i (u : ℤ)) 0
  linarith

theorem windowMax_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (i : Fin N)
    (U : Array N) : windowMax p m n i U ≤ 2 * ((n : ℝ) + 2) + 3 := by
  refine Finset.sup'_le _ _ fun u hu => ?_
  have hu' : u ≤ n + 1 := by
    have h2 : u < n + 2 := Finset.mem_range.mp hu
    omega
  have h := SwarmM3.hfix_le_lin (omegaN p m U i) (fun v => one_half_le_omegaAt p m U hp i (v : ℤ))
    (fun v => omegaAt_le_one p m U hp1 i (v : ℤ)) u
  have : (u : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hu'
  linarith

/-! ### 3. `(hcomp)` with one-step slack -/

/-- `(hcomp)` at a site at or below the running maximum, with slack `2`. -/
theorem hfix_wA_le_window_add_two {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J : Finset (Fin N)} {i : Fin N} {U : Array N} (hiJ : i ∈ Jᶜ) {k : ℕ}
    (hk : (k : ℤ) ≤ runMax p m U i n) :
    hfix (wA p m U n Jᶜ) k ≤ windowMax p m n i U + 2 := by
  set R := runMax p m U i n with hR
  have hRnn : (0 : ℤ) ≤ R := runMax_nonneg' p m U i n
  have hRle : R ≤ (n : ℤ) := runMax_le_time p m U i n
  have hRcast : ((R.toNat : ℕ) : ℤ) = R := Int.toNat_of_nonneg hRnn
  rcases lt_or_eq_of_le hk with hlt | heq
  · -- strict: the strict `(hcomp)` comparison
    have h := hcomp_h p m U hp hp1 (J := J) (i := i) hiJ (x := k) hlt
    have hk' : k ≤ n + 1 := by
      have : (k : ℤ) < (n : ℤ) + 1 := by omega
      omega
    linarith [le_windowMax (p := p) (m := m) (n := n) (i := i) (U := U) (u := k) (by omega)]
  · -- at the running maximum: one boundary step
    have hkR : k = R.toNat := by omega
    subst hkR
    have h := hcomp_h_runMax p m U hp hp1 (J := J) (i := i) (n := n) hiJ
    rcases Nat.eq_zero_or_pos R.toNat with h0 | hpos
    · rw [h0] at h ⊢
      have h1 := one_le_windowMax (p := p) hp hp1 m n i U
      have h2 : hprev (omegaN p m U i) 0 = 1 := by simp
      linarith
    · rw [hprev_eq_hfix_sub_one (w := omegaN p m U i) hpos] at h
      have hsub : R.toNat - 1 ≤ n + 1 := by
        have h2 : ((R.toNat : ℕ) : ℤ) ≤ (n : ℤ) := by rw [hRcast]; exact hRle
        omega
      linarith [le_windowMax (p := p) (m := m) (n := n) (i := i) (U := U) (u := R.toNat - 1)
        (by omega)]

/-- `(hcomp)` one step beyond the running maximum, with slack `4`. -/
theorem hfix_wA_le_window_add_four {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J : Finset (Fin N)} {i : Fin N} {U : Array N} (hiJ : i ∈ Jᶜ) {k : ℕ}
    (hk : (k : ℤ) ≤ runMax p m U i n + 1) :
    hfix (wA p m U n Jᶜ) k ≤ windowMax p m n i U + 4 := by
  have hRnn : (0 : ℤ) ≤ runMax p m U i n := runMax_nonneg' p m U i n
  have hRcast : (((runMax p m U i n).toNat : ℕ) : ℤ) = runMax p m U i n :=
    Int.toNat_of_nonneg hRnn
  rcases lt_or_ge (runMax p m U i n) (k : ℤ) with hlt | hge
  · -- `k = R + 1`: one potential step of slack on top of `(hcomp)` at `R`
    have h1 : (k : ℤ) = runMax p m U i n + 1 := by omega
    have hkR : k = (runMax p m U i n).toNat + 1 := by
      refine Nat.cast_injective (R := ℤ) ?_
      push_cast
      rw [hRcast]
      exact h1
    subst hkR
    have hstep := Swarming.Constants.hfix_le_hprev_add_two (wA p m U n Jᶜ)
      (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ) (one_half_le_wA p m U hp n Jᶜ)
      ((runMax p m U i n).toNat + 1)
    rw [hprev_succ] at hstep
    have h2 := hfix_wA_le_window_add_two (p := p) hp hp1 (m := m) (n := n) (J := J)
      (i := i) (U := U) hiJ (k := (runMax p m U i n).toNat)
      (by rw [hRcast])
    linarith
  · have h1 := hfix_wA_le_window_add_two (p := p) hp hp1 (m := m) (n := n) (J := J)
      (i := i) (U := U) hiJ (k := k) hge
    linarith

/-! ### 4. One-lattice-step bound for the group potential -/

theorem toNat_add_one {x : ℤ} (hx : 0 ≤ x) : (x + 1).toNat = x.toNat + 1 := by
  have h : (((x + 1).toNat : ℕ) : ℤ) = ((x.toNat + 1 : ℕ) : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ x + 1 by omega), Int.toNat_of_nonneg hx]
  exact Nat.cast_injective h

theorem toNat_sub_one {x : ℤ} (hx : 0 < x) : (x - 1).toNat + 1 = x.toNat := by
  have h : ((((x - 1).toNat + 1 : ℕ)) : ℤ) = ((x.toNat : ℕ) : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ x - 1 by omega), Int.toNat_of_nonneg (le_of_lt hx)]
    ring
  exact Nat.cast_injective h

lemma abs_int_cast_le_one {a : ℤ} (h : |a| ≤ 1) : |((a : ℤ) : ℝ)| ≤ 1 := by
  have h1 := abs_le.mp h
  rw [abs_le]
  exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩

/-- If one of the two sites is strictly negative, the extended potential moves by at most `1`. -/
theorem abs_HZ_step_le_of_neg {w : ℕ → ℝ} {x x' : ℤ} (hx : x < 0 ∨ x' < 0)
    (hd : |x' - x| ≤ 1) : |HZ w x' - HZ w x| ≤ 1 := by
  rcases hx with hx | hx
  · rcases lt_or_ge x' 0 with hx' | hx'
    · rw [HZ_neg hx', HZ_neg hx, ← Int.cast_sub]
      exact abs_int_cast_le_one hd
    · -- `x < 0 ≤ x'`, so `x = -1`, `x' = 0`
      have h1 := abs_le.mp hd
      have hx1 : x = -1 := by omega
      have hx'0 : x' = 0 := by omega
      subst hx1 hx'0
      rw [HZ_zero, HZ_neg (by norm_num : (-1 : ℤ) < 0)]
      norm_num
  · rcases lt_or_ge x 0 with hx0 | hx0
    · rw [HZ_neg hx, HZ_neg hx0, ← Int.cast_sub]
      exact abs_int_cast_le_one hd
    · -- `x' < 0 ≤ x`, so `x' = -1`, `x = 0`
      have h1 := abs_le.mp hd
      have hx'1 : x' = -1 := by omega
      have hx0' : x = 0 := by omega
      subst hx'1 hx0'
      rw [HZ_neg (by norm_num : (-1 : ℤ) < 0), HZ_zero]
      norm_num

/-- **One lattice step of the extended potential.**  Both sites nonnegative: the change is at most
the potential evaluated at the lower site. -/
theorem abs_HZ_step_le_nonneg {w : ℕ → ℝ} (hw0 : ∀ u, 0 < w u) (hw1 : ∀ u, w u ≤ 1)
    {x x' : ℤ} (hx : 0 ≤ x) (hx' : 0 ≤ x')
    (hd : x' = x + 1 ∨ x' = x - 1 ∨ x' = x) :
    |HZ w x' - HZ w x| ≤ max (hfix w x.toNat) (hfix w x'.toNat) := by
  have hone : ∀ u : ℕ, (1 : ℝ) ≤ hfix w u := Cookie.one_le_hfix w hw0 hw1
  rcases hd with rfl | rfl | rfl
  · rw [HZ_nonneg (by omega), HZ_nonneg hx, toNat_add_one hx, Hfix_succ]
    have h1 : (0 : ℝ) ≤ hfix w x.toNat := le_trans zero_le_one (hone x.toNat)
    rw [show Hfix w x.toNat + hfix w x.toNat - Hfix w x.toNat = hfix w x.toNat by ring,
      abs_of_nonneg h1]
    exact le_max_left _ _
  · rw [HZ_nonneg (by omega), HZ_nonneg hx]
    have hcast := toNat_sub_one (x := x) (by omega)
    conv_lhs => rw [← hcast, Hfix_succ]
    have h1 : (0 : ℝ) ≤ hfix w (x - 1).toNat := le_trans zero_le_one (hone (x - 1).toNat)
    rw [show Hfix w (x - 1).toNat - (Hfix w (x - 1).toNat + hfix w (x - 1).toNat)
        = -hfix w (x - 1).toNat by ring, abs_neg, abs_of_nonneg h1]
    exact le_max_right _ _
  · rw [sub_self, abs_zero]
    exact le_max_of_le_left (le_trans zero_le_one (hone _))

/-- **One lattice step of the extended potential.** -/
theorem abs_HZ_step_le {w : ℕ → ℝ} (hw0 : ∀ u, 0 < w u) (hw1 : ∀ u, w u ≤ 1) {x x' : ℤ}
    (hd : x' = x + 1 ∨ x' = x - 1 ∨ x' = x) :
    |HZ w x' - HZ w x| ≤ max (hfix w x.toNat) (hfix w x'.toNat) := by
  have hone : ∀ u : ℕ, (1 : ℝ) ≤ hfix w u := Cookie.one_le_hfix w hw0 hw1
  have hd' : |x' - x| ≤ 1 := by
    rcases hd with rfl | rfl | rfl <;> rw [abs_le] <;> constructor <;> omega
  rcases lt_or_ge x 0 with hx | hx
  · refine le_trans (abs_HZ_step_le_of_neg (Or.inl hx) hd') ?_
    exact le_trans (hone x.toNat) (le_max_left _ _)
  · rcases lt_or_ge x' 0 with hx' | hx'
    · refine le_trans (abs_HZ_step_le_of_neg (Or.inr hx') hd') ?_
      exact le_trans (hone x'.toNat) (le_max_right _ _)
    · exact abs_HZ_step_le_nonneg hw0 hw1 hx hx' hd

/-! ### 5. The per-walker step bound with the window maximum -/

theorem hfix_wA_le_window_of_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J : Finset (Fin N)} {i : Fin N} {U : Array N} (hiJ : i ∈ Jᶜ) {x : ℤ}
    (hx : x ≤ runMax p m U i n) :
    hfix (wA p m U n Jᶜ) x.toNat ≤ windowMax p m n i U + 4 := by
  have hRnn : (0 : ℤ) ≤ runMax p m U i n := runMax_nonneg' p m U i n
  have hle : ((x.toNat : ℕ) : ℤ) ≤ runMax p m U i n + 1 := by
    rcases lt_or_ge x 0 with hneg | hpos
    · have h0 : x.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      rw [h0]
      push_cast
      omega
    · rw [Int.toNat_of_nonneg hpos]
      omega
  exact hfix_wA_le_window_add_four (p := p) hp hp1 (m := m) (n := n) (J := J) (i := i)
    (U := U) hiJ hle

theorem hfix_wA_le_window_of_le_add_one {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J : Finset (Fin N)} {i : Fin N} {U : Array N} (hiJ : i ∈ Jᶜ) {x : ℤ}
    (hx : x ≤ runMax p m U i n + 1) :
    hfix (wA p m U n Jᶜ) x.toNat ≤ windowMax p m n i U + 4 := by
  have hRnn : (0 : ℤ) ≤ runMax p m U i n := runMax_nonneg' p m U i n
  have hle : ((x.toNat : ℕ) : ℤ) ≤ runMax p m U i n + 1 := by
    rcases lt_or_ge x 0 with hneg | hpos
    · have h0 : x.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      rw [h0]
      push_cast
      omega
    · rw [Int.toNat_of_nonneg hpos]
      omega
  exact hfix_wA_le_window_add_four (p := p) hp hp1 (m := m) (n := n) (J := J) (i := i)
    (U := U) hiJ hle

/-- The general one-step bound for the frozen group potential at two sites below the running
maximum (with one step of slack). -/
theorem abs_HA_step_le_of_le_runMax {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J : Finset (Fin N)} {i : Fin N} {U : Array N} (hiJ : i ∈ Jᶜ) {x x' : ℤ}
    (hx : x ≤ runMax p m U i n) (hx' : x' ≤ runMax p m U i n + 1)
    (hd : x' = x + 1 ∨ x' = x - 1 ∨ x' = x) :
    |HA p m U n Jᶜ x' - HA p m U n Jᶜ x| ≤ windowMax p m n i U + 4 := by
  have h := abs_HZ_step_le (w := wA p m U n Jᶜ) (wA_pos p m U hp n Jᶜ) (wA_le_one p m U hp1 n Jᶜ)
    hd
  have hsub : max (hfix (wA p m U n Jᶜ) x.toNat) (hfix (wA p m U n Jᶜ) x'.toNat)
      ≤ windowMax p m n i U + 4 :=
    max_le (hfix_wA_le_window_of_le hp hp1 hiJ hx)
      (hfix_wA_le_window_of_le_add_one hp hp1 hiJ hx')
  exact le_trans h hsub

/-- The one-step bound for one walker of the group. -/
theorem abs_HA_step_le_own {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    {J : Finset (Fin N)} {i : Fin N} {U : Array N} (hiJ : i ∈ Jᶜ) :
    |HA p m U n Jᶜ (X p m U (n + 1) i) - HA p m U n Jᶜ (X p m U n i)|
      ≤ windowMax p m n i U + 4 := by
  refine abs_HA_step_le_of_le_runMax hp hp1 hiJ (U := U)
    (le_runMax_pos p m U n i) ?_ ?_
  · have h := X_succ_le_add_one p m U n i
    have h2 := le_runMax_pos p m U n i
    omega
  · rcases X_succ_sub_X p m U n i with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-! ### 6. The group-level bound on the separated event -/

/-- The static window potential maximised over the leading block, plus the one-step slack. -/
noncomputable def PotMax (p : ℝ) (m n : ℕ) (I : Finset (Fin N)) (hI : I.Nonempty)
    (U : Array N) : ℝ :=
  Swarming.Group.maximumOn I hI (fun i => windowMax p m n i U) + 4

theorem le_PotMax {p : ℝ} {m n : ℕ} {I : Finset (Fin N)} {hI : I.Nonempty} {U : Array N}
    {i : Fin N} (hi : i ∈ I) : windowMax p m n i U + 4 ≤ PotMax p m n I hI U := by
  have h1 : windowMax p m n i U ≤ Swarming.Group.maximumOn I hI (fun i => windowMax p m n i U) :=
    Finset.le_sup' (fun i => windowMax p m n i U) hi
  unfold PotMax
  linarith

theorem average_sub_group {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    Swarming.Group.average s (fun i => f i - g i)
      = Swarming.Group.average s f - Swarming.Group.average s g := by
  simp only [Swarming.Group.average, Finset.sum_sub_distrib, sub_div]

theorem abs_average_le_of_bound {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → ℝ}
    {C : ℝ} (h : ∀ i ∈ s, |f i| ≤ C) : |Swarming.Group.average s f| ≤ C := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have h1 : |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
  have h2 : (∑ i ∈ s, |f i|) ≤ ∑ i ∈ s, C := Finset.sum_le_sum h
  have h3 : (∑ i ∈ s, C) = (s.card : ℝ) * C := by
    simp [Finset.sum_const, nsmul_eq_mul]
  simp only [Swarming.Group.average]
  rw [abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
  linarith

theorem abs_sup'_sub_sup'_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f g : ι → ℝ}
    {C : ℝ} (h : ∀ i ∈ s, |f i - g i| ≤ C) : |s.sup' hs f - s.sup' hs g| ≤ C := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    refine Finset.sup'_le hs _ fun i hi => ?_
    have h1 := (abs_le.mp (h i hi)).2
    have h2 : g i ≤ s.sup' hs g := Finset.le_sup' g hi
    linarith
  · rw [sub_le_iff_le_add]
    refine Finset.sup'_le hs _ fun i hi => ?_
    have h1 := (abs_le.mp (h i hi)).1
    have h2 : f i ≤ s.sup' hs f := Finset.le_sup' f hi
    linarith

/-- The average term moves by at most `PotMax` on the separated event. -/
theorem abs_Anext_sub_Anow_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) {U : Array N}
    (hsep : SepSet p m n I J U) :
    |Anext p m n I J U - Anow p m n I J U| ≤ PotMax p m n I hI U := by
  have hJc : ∀ i ∈ I, i ∈ Jᶜ := by
    intro i hi
    simp only [Finset.mem_compl]
    exact Finset.disjoint_left.mp hid hi
  have hsub : ∀ i ∈ I, |(fun i => HA p m U n Jᶜ (X p m U (n + 1) i)) i
      - (fun i => HA p m U n Jᶜ (X p m U n i)) i| ≤ PotMax p m n I hI U := by
    intro i hi
    refine le_trans (abs_HA_step_le_own hp hp1 (hJc i hi)) ?_
    exact le_PotMax hi
  have h1 : Anext p m n I J U - Anow p m n I J U
      = Swarming.Group.average I (fun i =>
          HA p m U n Jᶜ (X p m U (n + 1) i) - HA p m U n Jᶜ (X p m U n i)) := by
    unfold Anext Anow
    rw [average_sub_group]
  rw [h1]
  exact abs_average_le_of_bound hI hsub

/-- The maximum term moves by at most `PotMax` on the separated event. -/
theorem abs_Mnext_sub_Mnow_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) {U : Array N}
    (hsep : SepSet p m n I J U) :
    |Mnext p m n J hJ U - Mnow p m n J hJ U| ≤ PotMax p m n I hI U := by
  obtain ⟨i₀, hi₀⟩ := hI
  have hI' : I.Nonempty := ⟨i₀, hi₀⟩
  have hiJ : i₀ ∈ Jᶜ := by
    simp only [Finset.mem_compl]
    exact Finset.disjoint_left.mp hid hi₀
  have hterm : ∀ j ∈ J, |(fun j => HA p m U n Jᶜ (X p m U (n + 1) j)) j
      - (fun j => HA p m U n Jᶜ (X p m U n j)) j| ≤ PotMax p m n I hI' U := by
    intro j hj
    have hsepj : runMax p m U j n + 2 ≤ X p m U n i₀ := hsep.2 i₀ hi₀ j hj
    have h1 : X p m U n j ≤ runMax p m U i₀ n := by
      have h2 : X p m U n j ≤ runMax p m U j n := le_runMax_pos p m U n j
      have h3 : X p m U n i₀ ≤ runMax p m U i₀ n := le_runMax_pos p m U n i₀
      omega
    have h2 : X p m U (n + 1) j ≤ runMax p m U i₀ n + 1 := by
      have h3 := X_succ_le_add_one p m U n j
      omega
    have hd : X p m U (n + 1) j = X p m U n j + 1 ∨ X p m U (n + 1) j = X p m U n j - 1
        ∨ X p m U (n + 1) j = X p m U n j := by
      rcases X_succ_sub_X p m U n j with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    exact le_trans (abs_HA_step_le_of_le_runMax hp hp1 hiJ h1 h2 hd) (le_PotMax hi₀)
  have hsup := abs_sup'_sub_sup'_le hJ hterm
  simpa only [Mnext, Mnow, Swarming.Group.maximumOn, hI'] using hsup

/-! ### 7. The one-step group-weight update term -/

/-- The observable `W` read at the *new* positions with the group weights frozen at time `n'`. -/
noncomputable def Fpot (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hJ : J.Nonempty) (n' : ℕ)
    (U : Array N) : ℝ :=
  Swarming.Group.average I (fun i => HA p m U n' Jᶜ (X p m U (n + 1) i))
    - Swarming.Group.maximumOn J hJ (fun j => HA p m U n' Jᶜ (X p m U (n + 1) j))

/-- The total change of the group potential caused by one time step of the local times, at the
walkers of `I ∪ J` at the new positions.  Nonnegative because the group weights only increase. -/
noncomputable def siteDiff (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (U : Array N) : ℝ :=
  Swarming.Group.maximumOn (I ∪ J) (hI.mono (Finset.subset_union_left : I ⊆ I ∪ J))
    (fun k => HA p m U n Jᶜ (X p m U (n + 1) k)
      - HA p m U (n + 1) Jᶜ (X p m U (n + 1) k))

theorem siteDiff_nonneg {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ} {I J : Finset (Fin N)}
    (hI : I.Nonempty) (U : Array N) : 0 ≤ siteDiff p m n I J hI U := by
  obtain ⟨i₀, hi₀⟩ := hI
  unfold siteDiff Swarming.Group.maximumOn
  refine le_trans (HZ_diff_nonneg_time p m U hp hp1 n Jᶜ (X p m U (n + 1) i₀)) ?_
  exact Finset.le_sup' (f := fun k => HA p m U n Jᶜ (X p m U (n + 1) k)
    - HA p m U (n + 1) Jᶜ (X p m U (n + 1) k)) (Finset.mem_union_left J hi₀)

theorem le_siteDiff {p : ℝ} {m n : ℕ} {I J : Finset (Fin N)} {hI : I.Nonempty} {U : Array N}
    {k : Fin N} (hk : k ∈ I ∪ J) :
    HA p m U n Jᶜ (X p m U (n + 1) k) - HA p m U (n + 1) Jᶜ (X p m U (n + 1) k)
      ≤ siteDiff p m n I J hI U := by
  unfold siteDiff Swarming.Group.maximumOn
  exact Finset.le_sup' (f := fun k => HA p m U n Jᶜ (X p m U (n + 1) k)
    - HA p m U (n + 1) Jᶜ (X p m U (n + 1) k)) hk

theorem sup'_sub_sup'_le_sup'_sub {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f g : ι → ℝ) :
    s.sup' hs f - s.sup' hs g ≤ s.sup' hs (fun i => f i - g i) := by
  have h : s.sup' hs f ≤ s.sup' hs g + s.sup' hs (fun i => f i - g i) := by
    refine Finset.sup'_le hs _ fun i hi => ?_
    have h1 : f i - g i ≤ s.sup' hs (fun i => f i - g i) :=
      Finset.le_sup' (fun i => f i - g i) hi
    have h2 : g i ≤ s.sup' hs g := Finset.le_sup' g hi
    linarith
  linarith

theorem average_le_max {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    Swarming.Group.average s f ≤ s.sup' hs f := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have h1 : (∑ i ∈ s, f i) ≤ ∑ i ∈ s, s.sup' hs f := Finset.sum_le_sum fun i hi =>
    Finset.le_sup' f hi
  have h2 : (∑ i ∈ s, s.sup' hs f) = (s.card : ℝ) * s.sup' hs f := by
    simp [Finset.sum_const, nsmul_eq_mul]
  simp only [Swarming.Group.average]
  rw [div_le_iff₀ hcard]
  linarith

theorem sup'_mono_finset {ι : Type*} {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t)
    (f : ι → ℝ) : s.sup' hs f ≤ t.sup' (hs.mono hst) f :=
  Finset.sup'_le _ _ fun i hi => Finset.le_sup' f (hst hi)

/-- One time step of the frozen observable at the new positions is controlled by `siteDiff`. -/
theorem abs_Fpot_succ_sub_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (U : Array N) :
    |Fpot p m n I J hJ (n + 1) U - Fpot p m n I J hJ n U| ≤ siteDiff p m n I J hI U := by
  set D : Fin N → ℝ := fun k => HA p m U n Jᶜ (X p m U (n + 1) k)
    - HA p m U (n + 1) Jᶜ (X p m U (n + 1) k) with hD
  have hDnn : ∀ k, 0 ≤ D k := fun k => HZ_diff_nonneg_time p m U hp hp1 n Jᶜ (X p m U (n + 1) k)
  have hDle : ∀ k ∈ I ∪ J, D k ≤ siteDiff p m n I J hI U := fun k hk => le_siteDiff hk
  have havg_le : Swarming.Group.average I D ≤ siteDiff p m n I J hI U :=
    le_trans (average_le_max hI D)
      (le_trans (sup'_mono_finset hI (Finset.subset_union_left : I ⊆ I ∪ J) D)
        (Finset.sup'_le _ D hDle))
  have havg_nonneg : 0 ≤ Swarming.Group.average I D := by
    have hcard : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hI
    simp only [Swarming.Group.average]
    apply div_nonneg _ (le_of_lt hcard)
    exact Finset.sum_nonneg fun i _ => hDnn i
  have hmax_le : Swarming.Group.maximumOn J hJ (fun j => HA p m U n Jᶜ (X p m U (n + 1) j))
      - Swarming.Group.maximumOn J hJ (fun j => HA p m U (n + 1) Jᶜ (X p m U (n + 1) j))
      ≤ siteDiff p m n I J hI U := by
    refine le_trans (sup'_sub_sup'_le_sup'_sub hJ _ _) ?_
    refine le_trans (sup'_mono_finset hJ (Finset.subset_union_right : J ⊆ I ∪ J) D) ?_
    exact Finset.sup'_le _ D hDle
  have hmax_nonneg : 0 ≤ Swarming.Group.maximumOn J hJ (fun j => HA p m U n Jᶜ (X p m U (n + 1) j))
      - Swarming.Group.maximumOn J hJ (fun j => HA p m U (n + 1) Jᶜ (X p m U (n + 1) j)) := by
    have h : Swarming.Group.maximumOn J hJ (fun j => HA p m U (n + 1) Jᶜ (X p m U (n + 1) j))
        ≤ Swarming.Group.maximumOn J hJ (fun j => HA p m U n Jᶜ (X p m U (n + 1) j)) := by
      refine Finset.sup'_le hJ _ fun j hj => ?_
      have h1 : HA p m U (n + 1) Jᶜ (X p m U (n + 1) j) ≤ HA p m U n Jᶜ (X p m U (n + 1) j) := by
        have h2 := HZ_diff_nonneg_time p m U hp hp1 n Jᶜ (X p m U (n + 1) j)
        linarith
      exact le_trans h1 (Finset.le_sup' (fun j => HA p m U n Jᶜ (X p m U (n + 1) j)) hj)
    linarith
  -- the average difference is `-average D`
  have havg : Swarming.Group.average I (fun i => HA p m U (n + 1) Jᶜ (X p m U (n + 1) i))
      - Swarming.Group.average I (fun i => HA p m U n Jᶜ (X p m U (n + 1) i))
      = - Swarming.Group.average I D := by
    simp only [hD, Swarming.Group.average, Finset.sum_sub_distrib]
    ring
  have hstep : Fpot p m n I J hJ (n + 1) U - Fpot p m n I J hJ n U
      = - Swarming.Group.average I D
        + (Swarming.Group.maximumOn J hJ (fun j => HA p m U n Jᶜ (X p m U (n + 1) j))
          - Swarming.Group.maximumOn J hJ (fun j => HA p m U (n + 1) Jᶜ (X p m U (n + 1) j))) := by
    unfold Fpot
    linarith
  rw [hstep, abs_le]
  constructor <;> linarith

/-- **The one-step drift bound on the separated event.**  The change of `W` is controlled by the
frozen two-time step bound `2 PotMax` plus the one-step group-weight update term `siteDiff`. -/
theorem abs_WA_drift_le_potMax {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) {U : Array N}
    (hsep : SepSet p m n I J U) :
    |WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ|
      ≤ 2 * PotMax p m n I hI U + siteDiff p m n I J hI U := by
  have h1 : WA p m U (n + 1) I J hI hJ = Fpot p m n I J hJ (n + 1) U := rfl
  have h2 : WA p m U n I J hI hJ = Anow p m n I J U - Mnow p m n J hJ U := rfl
  have h3 : Fpot p m n I J hJ n U = Anext p m n I J U - Mnext p m n J hJ U := rfl
  have ha := abs_Anext_sub_Anow_le hp hp1 I J hI hJ hid hsep
  have hm := abs_Mnext_sub_Mnow_le hp hp1 I J hI hJ hid hsep
  have hf := abs_Fpot_succ_sub_le (p := p) hp hp1 (m := m) (n := n) I J hI hJ U
  have hsplit : WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ
      = (Fpot p m n I J hJ (n + 1) U - Fpot p m n I J hJ n U)
        + ((Anext p m n I J U - Anow p m n I J U) - (Mnext p m n J hJ U - Mnow p m n J hJ U)) := by
    rw [h1, h2, h3]
    ring
  rw [hsplit]
  have hstep : |(Anext p m n I J U - Anow p m n I J U) - (Mnext p m n J hJ U - Mnow p m n J hJ U)|
      ≤ 2 * PotMax p m n I hI U := by
    have h4 : |(Anext p m n I J U - Anow p m n I J U) - (Mnext p m n J hJ U - Mnow p m n J hJ U)|
        ≤ |Anext p m n I J U - Anow p m n I J U| + |Mnext p m n J hJ U - Mnow p m n J hJ U| := by
      rw [sub_eq_add_neg, ← abs_neg (Mnext p m n J hJ U - Mnow p m n J hJ U)]
      exact abs_add_le _ _
    linarith
  have h5 : |(Fpot p m n I J hJ (n + 1) U - Fpot p m n I J hJ n U)
      + ((Anext p m n I J U - Anow p m n I J U) - (Mnext p m n J hJ U - Mnow p m n J hJ U))|
      ≤ |Fpot p m n I J hJ (n + 1) U - Fpot p m n I J hJ n U|
        + |(Anext p m n I J U - Anow p m n I J U) - (Mnext p m n J hJ U - Mnow p m n J hJ U)| :=
    abs_add_le _ _
  linarith

/-! ### 8. Measurability of the static window potential -/

theorem measurableSet_siteMark_v (p : ℝ) (m : ℕ) (j : Fin N) (x : ℤ) :
    MeasurableSet {U : Array N | SiteMark p m U j x} := by
  have hset : {U : Array N | SiteMark p m U j x}
      = ⋂ k ∈ Finset.Icc 1 (m - 1), {U : Array N | p < U (j, x, k)} := by
    ext U
    simp only [SiteMark, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  exact Finset.measurableSet_biInter _ (fun k _ =>
    measurableSet_lt measurable_const
      (measurable_pi_apply (X := fun _ : Fin N × ℤ × ℕ => ℝ) (j, x, k)))

theorem measurable_omegaAt_v (p : ℝ) (m : ℕ) (j : Fin N) (x : ℤ) :
    Measurable fun U : Array N => omegaAt p m U j x := by
  unfold omegaAt
  exact Measurable.ite (measurableSet_siteMark_v p m j x) measurable_const measurable_const

theorem measurable_omegaN_v (p : ℝ) (m : ℕ) (j : Fin N) (u : ℕ) :
    Measurable fun U : Array N => omegaN p m U j u :=
  measurable_omegaAt_v p m j (u : ℤ)

theorem measurable_hfix_omegaN (p : ℝ) (m : ℕ) (i : Fin N) (u : ℕ) :
    Measurable fun U : Array N => hfix (omegaN p m U i) u := by
  induction u with
  | zero =>
      have h0 := measurable_omegaN_v p m i 0
      have heq : (fun U : Array N => hfix (omegaN p m U i) 0)
          = fun U : Array N => (1 + (1 - omegaN p m U i 0) * 1) / omegaN p m U i 0 := by
        funext U
        rw [Cookie.hfix]
      rw [heq]
      exact (measurable_const.add ((measurable_const.sub h0).mul measurable_const)).div h0
  | succ u ih =>
      have h0 := measurable_omegaN_v p m i (u + 1)
      have heq : (fun U : Array N => hfix (omegaN p m U i) (u + 1))
          = fun U : Array N =>
            (1 + (1 - omegaN p m U i (u + 1)) * hfix (omegaN p m U i) u) / omegaN p m U i (u + 1) := by
        funext U
        rw [Cookie.hfix_eq, Cookie.hprev_succ]
      rw [heq]
      exact (measurable_const.add ((measurable_const.sub h0).mul ih)).div h0

theorem measurable_windowMax (p : ℝ) (m n : ℕ) (i : Fin N) :
    Measurable fun U : Array N => windowMax p m n i U := by
  unfold windowMax
  set H : (Finset.range (n + 2)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩ with hH
  have heq : (fun U : Array N => (Finset.range (n + 2)).sup' H (fun u => hfix (omegaN p m U i) u))
      = (Finset.range (n + 2)).sup' H (fun u (U : Array N) => hfix (omegaN p m U i) u) := by
    funext U
    exact (Finset.sup'_apply H (fun u (U : Array N) => hfix (omegaN p m U i) u) U).symm
  rw [heq]
  exact Finset.measurable_sup' H (fun u _ => measurable_hfix_omegaN p m i u)

theorem measurable_PotMax (p : ℝ) (m n : ℕ) (I : Finset (Fin N)) (hI : I.Nonempty) :
    Measurable fun U : Array N => PotMax p m n I hI U := by
  have h : Measurable fun U : Array N =>
      Swarming.Group.maximumOn I hI (fun i => windowMax p m n i U) := by
    unfold Swarming.Group.maximumOn
    have heq : (fun U : Array N => I.sup' hI (fun i => windowMax p m n i U))
        = I.sup' hI (fun i (U : Array N) => windowMax p m n i U) := by
      funext U
      exact (Finset.sup'_apply hI (fun i (U : Array N) => windowMax p m n i U) U).symm
    rw [heq]
    exact Finset.measurable_sup' hI (fun i _ => measurable_windowMax p m n i)
  exact h.add measurable_const

theorem measurable_HA_succ_site (p : ℝ) (m n n' : ℕ) (J : Finset (Fin N)) (k : Fin N) :
    Measurable fun U : Array N => HA p m U n' Jᶜ (X p m U (n + 1) k) :=
  measurable_HA_random_site p m n' Jᶜ (fun U => X p m U (n + 1) k)
    (measurable_X_ambient p m (n + 1) k) (n + 1)
    (fun U => SwarmM3.abs_X_le p m U (n + 1) k)

theorem measurable_siteDiff (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty) :
    Measurable fun U : Array N => siteDiff p m n I J hI U := by
  unfold siteDiff Swarming.Group.maximumOn
  set H : (I ∪ J).Nonempty := hI.mono (Finset.subset_union_left : I ⊆ I ∪ J) with hH
  have heq : (fun U : Array N => (I ∪ J).sup' H (fun k => HA p m U n Jᶜ (X p m U (n + 1) k)
        - HA p m U (n + 1) Jᶜ (X p m U (n + 1) k)))
      = (I ∪ J).sup' H (fun k (U : Array N) => HA p m U n Jᶜ (X p m U (n + 1) k)
        - HA p m U (n + 1) Jᶜ (X p m U (n + 1) k)) := by
    funext U
    exact (Finset.sup'_apply H (fun k (U : Array N) => HA p m U n Jᶜ (X p m U (n + 1) k)
      - HA p m U (n + 1) Jᶜ (X p m U (n + 1) k)) U).symm
  rw [heq]
  exact Finset.measurable_sup' H (fun k _ => (measurable_HA_succ_site p m n n J k).sub
    (measurable_HA_succ_site p m n (n + 1) J k))

/-! ### 9. Explicit bounds for the two potential terms -/

theorem PotMax_nonneg {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ} {I : Finset (Fin N)}
    {hI : I.Nonempty} {U : Array N} : 0 ≤ PotMax p m n I hI U := by
  have hmem : Classical.choose hI ∈ I := Classical.choose_spec hI
  have h1 := le_PotMax (p := p) (m := m) (n := n) (hI := hI) (U := U) hmem
  have h2 := one_le_windowMax (p := p) hp hp1 m n (Classical.choose hI) U
  linarith

theorem PotMax_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ} {I : Finset (Fin N)}
    {hI : I.Nonempty} {U : Array N} :
    PotMax p m n I hI U ≤ 2 * ((n : ℝ) + 2) + 3 + 4 := by
  have hsup : Swarming.Group.maximumOn I hI (fun i => windowMax p m n i U)
      ≤ 2 * ((n : ℝ) + 2) + 3 := by
    unfold Swarming.Group.maximumOn
    refine Finset.sup'_le hI (fun i => windowMax p m n i U) fun i _ => ?_
    exact windowMax_le (p := p) hp hp1 m n i U
  unfold PotMax
  linarith

theorem abs_HA_succ_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n n' : ℕ) {J : Finset (Fin N)}
    (k : Fin N) (U : Array N) :
    |HA p m U n' Jᶜ (X p m U (n + 1) k)| ≤ ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 3) + 3 := by
  have hx := SwarmM3.abs_X_le p m U (n + 1) k
  have h2 := abs_HA_le (p := p) hp hp1 m n' U Jᶜ (y := X p m U (n + 1) k)
    (M := n + 1) (by push_cast; exact hx)
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  simpa only [hcast] using h2

theorem siteDiff_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ} {I J : Finset (Fin N)}
    {hI : I.Nonempty} {U : Array N} :
    siteDiff p m n I J hI U ≤ 2 * (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 3) + 3) := by
  unfold siteDiff Swarming.Group.maximumOn
  refine Finset.sup'_le _ (fun k => HA p m U n Jᶜ (X p m U (n + 1) k)
    - HA p m U (n + 1) Jᶜ (X p m U (n + 1) k)) fun k _ => ?_
  have hA := abs_HA_succ_le (p := p) hp hp1 m n n (J := J) k U
  have hB := abs_HA_succ_le (p := p) hp hp1 m n (n + 1) (J := J) k U
  have ha := le_abs_self (HA p m U n Jᶜ (X p m U (n + 1) k))
  have hb := neg_abs_le (HA p m U (n + 1) Jᶜ (X p m U (n + 1) k))
  linarith

/-! ### 10. Integrability of the bounded terms -/

theorem integrable_of_abs_bound {f : Array N → ℝ} (hm : AEStronglyMeasurable f (arrayMeasure N))
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ U, |f U| ≤ C) : Integrable f (arrayMeasure N) := by
  refine Integrable.mono (integrable_const C) hm ?_
  filter_upwards with U
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC]
  exact h U

theorem integrable_sq_of_abs_bound {f : Array N → ℝ} (hm : AEStronglyMeasurable f (arrayMeasure N))
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ U, |f U| ≤ C) :
    Integrable (fun U => f U ^ 2) (arrayMeasure N) := by
  refine Integrable.mono (integrable_const (C ^ 2)) (hm.pow 2) ?_
  filter_upwards with U
  have h1 : ‖f U ^ 2‖ = (f U) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h2 : ‖C ^ 2‖ = C ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [h1, h2, ← sq_abs (f U)]
  exact pow_le_pow_left₀ (abs_nonneg (f U)) (h U) 2

theorem integrable_potMax_sq {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I : Finset (Fin N)) (hI : I.Nonempty) :
    Integrable (fun U => (PotMax p m n I hI U) ^ 2) (arrayMeasure N) := by
  have hC : (0 : ℝ) ≤ 2 * ((n : ℝ) + 2) + 3 + 4 := by positivity
  refine integrable_sq_of_abs_bound (measurable_PotMax p m n I hI).aestronglyMeasurable hC ?_
  intro U
  rw [abs_of_nonneg (PotMax_nonneg (p := p) hp hp1 (U := U))]
  exact PotMax_le (p := p) hp hp1 (U := U)

theorem integrable_siteDiff_sq {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) :
    Integrable (fun U => (siteDiff p m n I J hI U) ^ 2) (arrayMeasure N) := by
  have hC : (0 : ℝ) ≤ 2 * (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 3) + 3) := by positivity
  refine integrable_sq_of_abs_bound (measurable_siteDiff p m n I J hI).aestronglyMeasurable hC ?_
  intro U
  rw [abs_of_nonneg (siteDiff_nonneg (p := p) hp hp1 (hI := hI) U)]
  exact siteDiff_le (p := p) hp hp1 (U := U)

/-! ### 11. The one-step size of `Q^{I,J}` and its variance bound -/

/-- The crude deterministic one-step size of the observable. -/
noncomputable def Qbound (n : ℕ) : ℝ :=
  2 * (((n + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) + 3) + 3)
    + 2 * ((n : ℝ) * (2 * (n : ℝ) + 3) + 3)

theorem Qbound_nonneg (n : ℕ) : 0 ≤ Qbound n := by
  unfold Qbound
  have h1 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem abs_Qraw_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) (U : Array N) :
    |Qraw p m I J hI hJ n U| ≤ Qbound n := by
  have h := abs_WA_drift_le (p := p) hp hp1 m n U I J hI hJ
  have h2 : |Qraw p m I J hI hJ n U|
      ≤ |WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ| := by
    by_cases hU : U ∈ {U : Array N | SepSet p m n I J U}
    · rw [show Qraw p m I J hI hJ n U
        = WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ by
        simp only [Qraw, Set.indicator_of_mem hU]]
    · rw [show Qraw p m I J hI hJ n U = 0 by simp only [Qraw, Set.indicator_of_notMem hU]]
      simp
  exact le_trans h2 h

theorem ae_abs_condExp_Qraw_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) :
    ∀ᵐ U ∂(arrayMeasure N),
      |condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U| ≤ Qbound n := by
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have hXint : Integrable (Qraw p m I J hI hJ n) (arrayMeasure N) :=
    integrable_Qraw hp hp1 m n I J hI hJ
  have hF : (posFilt N p m n) ≤ (inferInstance : MeasurableSpace (Array N)) := (posFilt N p m).le n
  have hup : ∀ᵐ U ∂(arrayMeasure N),
      condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U ≤ Qbound n := by
    have hle : Qraw p m I J hI hJ n ≤ᵐ[arrayMeasure N] fun _ => Qbound n :=
      Filter.Eventually.of_forall fun U => (abs_le.mp (abs_Qraw_le hp hp1 m n I J hI hJ U)).2
    have h := condExp_mono (m := (posFilt N p m n)) hXint (integrable_const (Qbound n)) hle
    rwa [condExp_const hF (Qbound n)] at h
  have hdown : ∀ᵐ U ∂(arrayMeasure N),
      -Qbound n ≤ condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U := by
    have hle : (-(Qraw p m I J hI hJ n)) ≤ᵐ[arrayMeasure N] fun _ => Qbound n :=
      Filter.Eventually.of_forall fun U => by
        have h1 := (abs_le.mp (abs_Qraw_le hp hp1 m n I J hI hJ U)).1
        simp only [Pi.neg_apply]
        linarith
    have h1 : condExp (posFilt N p m n) (arrayMeasure N) (-(Qraw p m I J hI hJ n))
        ≤ᵐ[arrayMeasure N] fun _ => Qbound n := by
      have h := condExp_mono (m := (posFilt N p m n)) hXint.neg (integrable_const (Qbound n)) hle
      rwa [condExp_const hF (Qbound n)] at h
    have h2 := condExp_neg (μ := arrayMeasure N) (Qraw p m I J hI hJ n) (posFilt N p m n)
    filter_upwards [h1, h2] with U h1' h2'
    have h3 : -condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U ≤ Qbound n := by
      simp only [Pi.neg_apply] at h2' ⊢
      rw [← h2']
      exact h1'
    linarith
  filter_upwards [hup, hdown] with U h1 h2
  exact abs_le.mpr ⟨h2, h1⟩

theorem ae_abs_dQ_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    ∀ᵐ U ∂(arrayMeasure N), |dQ p m I J hI hJ n U| ≤ 2 * Qbound n := by
  have h1 := ae_abs_condExp_Qraw_le hp hp1 m n I J hI hJ
  filter_upwards [h1] with U h2
  have h3 : dQ p m I J hI hJ n U
      = Qraw p m I J hI hJ n U
        - condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U := rfl
  have h4 := abs_Qraw_le hp hp1 m n I J hI hJ U
  rw [h3]
  have := abs_sub (Qraw p m I J hI hJ n U)
    (condExp (posFilt N p m n) (arrayMeasure N) (Qraw p m I J hI hJ n) U)
  linarith

theorem inc_Q_eq_dQ (p : ℝ) (m n : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) :
    MartingaleLimit.inc (Q p m I J hI hJ) n = dQ p m I J hI hJ n := by
  funext U
  simp only [MartingaleLimit.inc_apply, Q_succ]
  ring

/-! ### 12. The variance bound for the actual `Q^{I,J}` increments -/

theorem Qraw_sq_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) {m n : ℕ} (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) (U : Array N) :
    (Qraw p m I J hI hJ n U) ^ 2
      ≤ 8 * (PotMax p m n I hI U) ^ 2 + 2 * (siteDiff p m n I J hI U) ^ 2 := by
  have hP : 0 ≤ PotMax p m n I hI U := PotMax_nonneg (p := p) hp hp1 (U := U)
  have hS : 0 ≤ siteDiff p m n I J hI U := siteDiff_nonneg (p := p) hp hp1 (hI := hI) U
  by_cases hsep : U ∈ {U : Array N | SepSet p m n I J U}
  · have h1 := abs_WA_drift_le_potMax (p := p) hp hp1 I J hI hJ hid (U := U) hsep
    have h2 : Qraw p m I J hI hJ n U
        = WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ := by
      simp only [Qraw, Set.indicator_of_mem hsep]
    rw [h2, ← sq_abs (WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ)]
    have h3 : |WA p m U (n + 1) I J hI hJ - WA p m U n I J hI hJ|
        ^ 2 ≤ (2 * PotMax p m n I hI U + siteDiff p m n I J hI U) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h4 : (2 * PotMax p m n I hI U + siteDiff p m n I J hI U) ^ 2
        ≤ 8 * (PotMax p m n I hI U) ^ 2 + 2 * (siteDiff p m n I J hI U) ^ 2 := by
      nlinarith [sq_nonneg (2 * PotMax p m n I hI U - siteDiff p m n I J hI U), hP, hS]
    nlinarith [h3, h4]
  · have h2 : Qraw p m I J hI hJ n U = 0 := by
      simp only [Qraw, Set.indicator_of_notMem hsep]
    rw [h2]
    nlinarith [sq_nonneg (PotMax p m n I hI U), sq_nonneg (siteDiff p m n I J hI U), hP, hS]

theorem integral_sq_dQ_le {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ) (I J : Finset (Fin N))
    (hI : I.Nonempty) (hJ : J.Nonempty) :
    ∫ U, (dQ p m I J hI hJ n U) ^ 2 ∂(arrayMeasure N)
      ≤ ∫ U, (Qraw p m I J hI hJ n U) ^ 2 ∂(arrayMeasure N) := by
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  set X := Qraw p m I J hI hJ n with hX
  set Y := dQ p m I J hI hJ n with hY
  have hXint : Integrable X (arrayMeasure N) := integrable_Qraw hp hp1 m n I J hI hJ
  have hYint : Integrable Y (arrayMeasure N) := integrable_dQ hp hp1 m n I J hI hJ
  have hK : 0 ≤ Qbound n := Qbound_nonneg n
  have hXb : ∀ U, |X U| ≤ Qbound n := abs_Qraw_le hp hp1 m n I J hI hJ
  have hYb : ∀ᵐ U ∂(arrayMeasure N), |Y U| ≤ 2 * Qbound n :=
    ae_abs_dQ_le hp hp1 m n I J hI hJ
  have hCb : ∀ᵐ U ∂(arrayMeasure N),
      |condExp (posFilt N p m n) (arrayMeasure N) X U| ≤ Qbound n :=
    ae_abs_condExp_Qraw_le hp hp1 m n I J hI hJ
  have hX2 : Integrable (fun U => X U ^ 2) (arrayMeasure N) :=
    integrable_sq_of_abs_bound hXint.aestronglyMeasurable hK hXb
  have hY2 : Integrable (fun U => Y U ^ 2) (arrayMeasure N) := by
    refine Integrable.mono (integrable_const ((2 * Qbound n) ^ 2))
      (hYint.aestronglyMeasurable.pow 2) ?_
    filter_upwards [hYb] with U hU
    have h1 : ‖Y U ^ 2‖ = (Y U) ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h2 : ‖(((2 * Qbound n) ^ 2 : ℝ))‖ = (2 * Qbound n) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [h1, h2, ← sq_abs (Y U)]
    exact pow_le_pow_left₀ (abs_nonneg _) hU 2
  have hcm0 : StronglyMeasurable[posFilt N p m n]
      (fun U : Array N => condExp (posFilt N p m n) (arrayMeasure N) X U) :=
    stronglyMeasurable_condExp
  have hcmA : AEStronglyMeasurable
      (fun U : Array N => condExp (posFilt N p m n) (arrayMeasure N) X U) (arrayMeasure N) :=
    (hcm0.measurable.mono ((posFilt N p m).le n) le_rfl).aestronglyMeasurable
  have hC2 : Integrable (fun U => (condExp (posFilt N p m n) (arrayMeasure N) X U) ^ 2)
      (arrayMeasure N) := by
    refine Integrable.mono (integrable_const ((Qbound n) ^ 2)) (hcmA.pow 2) ?_
    filter_upwards [hCb] with U hU
    have h1 : ‖condExp (posFilt N p m n) (arrayMeasure N) X U ^ 2‖
        = (condExp (posFilt N p m n) (arrayMeasure N) X U) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h2 : ‖((Qbound n) ^ 2 : ℝ)‖ = (Qbound n) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [h1, h2, ← sq_abs (condExp (posFilt N p m n) (arrayMeasure N) X U)]
    exact pow_le_pow_left₀ (abs_nonneg _) hU 2
  have hcY : Integrable (fun U => condExp (posFilt N p m n) (arrayMeasure N) X U * Y U)
      (arrayMeasure N) :=
    MartingaleLimit.integrable_mul_of_sq hcmA hYint.aestronglyMeasurable hC2 hY2
  have hXY : Integrable (fun U => X U * Y U) (arrayMeasure N) :=
    MartingaleLimit.integrable_mul_of_sq hXint.aestronglyMeasurable hYint.aestronglyMeasurable
      hX2 hY2
  have hinc : (fun U => Y U) = MartingaleLimit.inc (Q p m I J hI hJ) n := by
    rw [hY]
    exact (inc_Q_eq_dQ p m n I J hI hJ).symm
  have horth : ∫ U, condExp (posFilt N p m n) (arrayMeasure N) X U * Y U
      ∂(arrayMeasure N) = 0 := by
    have hfun : (fun U => condExp (posFilt N p m n) (arrayMeasure N) X U * Y U)
        = fun U => condExp (posFilt N p m n) (arrayMeasure N) X U
          * MartingaleLimit.inc (Q p m I J hI hJ) n U := by
      funext U
      rw [show Y U = MartingaleLimit.inc (Q p m I J hI hJ) n U from congrFun hinc U]
    rw [hfun]
    exact MartingaleLimit.integral_mul_inc_eq_zero (martingale_Q hp hp1 m I J hI hJ)
      hcm0 (hfun ▸ hcY)
  have hpt : ∀ U, Y U ^ 2
      = X U * Y U - condExp (posFilt N p m n) (arrayMeasure N) X U * Y U := by
    intro U
    have hYeq : Y U = X U - condExp (posFilt N p m n) (arrayMeasure N) X U := rfl
    rw [hYeq]
    ring
  have hmain : ∫ U, Y U ^ 2 ∂(arrayMeasure N) = ∫ U, X U * Y U ∂(arrayMeasure N) := by
    have h1 : ∫ U, Y U ^ 2 ∂(arrayMeasure N)
        = ∫ U, (X U * Y U - condExp (posFilt N p m n) (arrayMeasure N) X U * Y U)
            ∂(arrayMeasure N) :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    rw [h1, integral_sub hXY hcY, horth, sub_zero]
  have hAM : ∫ U, X U * Y U ∂(arrayMeasure N)
      ≤ (∫ U, X U ^ 2 ∂(arrayMeasure N) + ∫ U, Y U ^ 2 ∂(arrayMeasure N)) / 2 := by
    have h1 : Integrable (fun U => (X U ^ 2 + Y U ^ 2) / 2) (arrayMeasure N) :=
      (hX2.add hY2).div_const 2
    have h2 : ∫ U, X U * Y U ∂(arrayMeasure N)
        ≤ ∫ U, (X U ^ 2 + Y U ^ 2) / 2 ∂(arrayMeasure N) := by
      refine integral_mono_ae hXY h1 (Filter.Eventually.of_forall fun U => ?_)
      nlinarith [sq_nonneg (X U - Y U)]
    rw [integral_div, integral_add hX2 hY2] at h2
    linarith
  linarith

theorem integral_sq_dQ_le_pot {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) :
    ∫ U, (dQ p m I J hI hJ n U) ^ 2 ∂(arrayMeasure N)
      ≤ 8 * ∫ U, (PotMax p m n I hI U) ^ 2 ∂(arrayMeasure N)
        + 2 * ∫ U, (siteDiff p m n I J hI U) ^ 2 ∂(arrayMeasure N) := by
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have h1 := integral_sq_dQ_le hp hp1 m n I J hI hJ
  have hQ2 : Integrable (fun U => (Qraw p m I J hI hJ n U) ^ 2) (arrayMeasure N) := by
    refine integrable_sq_of_abs_bound (integrable_Qraw hp hp1 m n I J hI hJ).aestronglyMeasurable
      (Qbound_nonneg n) (abs_Qraw_le hp hp1 m n I J hI hJ)
  have hR2 : Integrable (fun U => 8 * (PotMax p m n I hI U) ^ 2
      + 2 * (siteDiff p m n I J hI U) ^ 2) (arrayMeasure N) :=
    ((integrable_potMax_sq hp hp1 m n I hI).const_mul 8).add
      ((integrable_siteDiff_sq hp hp1 m n I J hI).const_mul 2)
  have h2 : ∫ U, (Qraw p m I J hI hJ n U) ^ 2 ∂(arrayMeasure N)
      ≤ ∫ U, 8 * (PotMax p m n I hI U) ^ 2 + 2 * (siteDiff p m n I J hI U) ^ 2
        ∂(arrayMeasure N) :=
    integral_mono_ae hQ2 hR2 (Filter.Eventually.of_forall fun U =>
      Qraw_sq_le hp hp1 I J hI hJ hid U)
  have h3 : ∫ U, 8 * (PotMax p m n I hI U) ^ 2 + 2 * (siteDiff p m n I J hI U) ^ 2
        ∂(arrayMeasure N)
      = 8 * ∫ U, (PotMax p m n I hI U) ^ 2 ∂(arrayMeasure N)
        + 2 * ∫ U, (siteDiff p m n I J hI U) ^ 2 ∂(arrayMeasure N) := by
    rw [integral_add ((integrable_potMax_sq hp hp1 m n I hI).const_mul 8)
      ((integrable_siteDiff_sq hp hp1 m n I J hI).const_mul 2),
      integral_const_mul, integral_const_mul]
  linarith [h1, h2, h3]

theorem integrable_dQ_sq {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (m n : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) :
    Integrable (fun U => (dQ p m I J hI hJ n U) ^ 2) (arrayMeasure N) := by
  have hprob := arrayMeasure_isProbabilityMeasure N
  haveI := hprob
  have hYint : Integrable (dQ p m I J hI hJ n) (arrayMeasure N) :=
    integrable_dQ hp hp1 m n I J hI hJ
  have hYb := ae_abs_dQ_le hp hp1 m n I J hI hJ
  refine Integrable.mono (integrable_const ((2 * Qbound n) ^ 2))
    (hYint.aestronglyMeasurable.pow 2) ?_
  filter_upwards [hYb] with U hU
  have h1 : ‖dQ p m I J hI hJ n U ^ 2‖ = (dQ p m I J hI hJ n U) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h2 : ‖(((2 * Qbound n) ^ 2 : ℝ))‖ = (2 * Qbound n) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [h1, h2, ← sq_abs (dQ p m I J hI hJ n U)]
  exact pow_le_pow_left₀ (abs_nonneg _) hU 2

theorem inc_Q_sq_eq (p : ℝ) (m k : ℕ) (I J : Finset (Fin N)) (hI : I.Nonempty)
    (hJ : J.Nonempty) :
    (fun U => (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2)
      = fun U => (dQ p m I J hI hJ k U) ^ 2 := by
  rw [inc_Q_eq_dQ]

/-- **The log-fourth variance bound for the actual `Q^{I,J}`** from the two explicit moment
premises `(Mpot)` and `(Mdiff)`. -/
theorem Q_log_variance_of_potMoment {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hPot : ∀ k : ℕ, ∫ U, (PotMax p m k I hI U) ^ 2 ∂(arrayMeasure N)
      ≤ C₁ * (Real.log ((k : ℝ) + 2)) ^ 4)
    (hDiff : ∀ k : ℕ, ∫ U, (siteDiff p m k I J hI U) ^ 2 ∂(arrayMeasure N)
      ≤ C₂ * (Real.log ((k : ℝ) + 2)) ^ 4) :
    (∀ k : ℕ, Integrable
        (fun U => (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2) (arrayMeasure N))
      ∧ ∀ k : ℕ, ∫ U, (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2 ∂(arrayMeasure N)
        ≤ (8 * C₁ + 2 * C₂) * (Real.log ((k : ℝ) + 2)) ^ 4 := by
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  constructor
  · intro k
    rw [inc_Q_sq_eq]
    exact integrable_dQ_sq hp hp1' m k I J hI hJ
  · intro k
    have h1 := integral_sq_dQ_le_pot hp hp1' m k I J hI hJ hid
    have h2 := hPot k
    have h3 := hDiff k
    have hlog : (0 : ℝ) ≤ (Real.log ((k : ℝ) + 2)) ^ 4 := by positivity
    have h4 : ∫ U, (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2 ∂(arrayMeasure N)
        = ∫ U, (dQ p m I J hI hJ k U) ^ 2 ∂(arrayMeasure N) := by
      rw [inc_Q_sq_eq]
    rw [h4]
    calc ∫ U, (dQ p m I J hI hJ k U) ^ 2 ∂(arrayMeasure N)
        ≤ 8 * ∫ U, (PotMax p m k I hI U) ^ 2 ∂(arrayMeasure N)
          + 2 * ∫ U, (siteDiff p m k I J hI U) ^ 2 ∂(arrayMeasure N) := h1
      _ ≤ 8 * (C₁ * (Real.log ((k : ℝ) + 2)) ^ 4)
          + 2 * (C₂ * (Real.log ((k : ℝ) + 2)) ^ 4) := by nlinarith
      _ = (8 * C₁ + 2 * C₂) * (Real.log ((k : ℝ) + 2)) ^ 4 := by ring

/-- **The paper's `(Qslln)` for the actual separated-group martingale**, reduced to the two
explicit moment premises on the static window potential and the one-step group-weight update. -/
theorem Qslln_of_potMoment {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hPot : ∀ k : ℕ, ∫ U, (PotMax p m k I hI U) ^ 2 ∂(arrayMeasure N)
      ≤ C₁ * (Real.log ((k : ℝ) + 2)) ^ 4)
    (hDiff : ∀ k : ℕ, ∫ U, (siteDiff p m k I J hI U) ^ 2 ∂(arrayMeasure N)
      ≤ C₂ * (Real.log ((k : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), Tendsto (fun n => Q p m I J hI hJ n U / n) atTop (𝓝 0) := by
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have h := Q_log_variance_of_potMoment hp0 hp1 m I J hI hJ hid hC₁ hC₂ hPot hDiff
  exact Qslln_of_log_variance hp hp1' m I J hI hJ h.1 h.2

/-- The running-maximum form: `max_{t<=n} |Q_t^{I,J}| = o(n)` almost surely. -/
theorem Q_running_max_of_potMoment {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hPot : ∀ k : ℕ, ∫ U, (PotMax p m k I hI U) ^ 2 ∂(arrayMeasure N)
      ≤ C₁ * (Real.log ((k : ℝ) + 2)) ^ 4)
    (hDiff : ∀ k : ℕ, ∫ U, (siteDiff p m k I J hI U) ^ 2 ∂(arrayMeasure N)
      ≤ C₂ * (Real.log ((k : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ((Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
        fun t => |Q p m I J hI hJ t U|) ≤ ε * (n : ℝ) := by
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have h := Q_log_variance_of_potMoment hp0 hp1 m I J hI hJ hid hC₁ hC₂ hPot hDiff
  exact Q_running_max_of_log_variance hp hp1' m I J hI hJ h.1 h.2

/-- **The paper's separated-group conclusion** `W_t <= W_s + o(t)` on an interval on which
`(sep)` holds, from the two moment premises.  This is the form consumed by the leader-set
induction of `(diam)` (`Swarm/LeaderDescent.lean`). -/
theorem telescope_le_of_potMoment {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hPot : ∀ k : ℕ, ∫ U, (PotMax p m k I hI U) ^ 2 ∂(arrayMeasure N)
      ≤ C₁ * (Real.log ((k : ℝ) + 2)) ^ 4)
    (hDiff : ∀ k : ℕ, ∫ U, (siteDiff p m k I J hI U) ^ 2 ∂(arrayMeasure N)
      ≤ C₂ * (Real.log ((k : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, ∀ s : ℕ, s ≤ t →
      (∀ k, s ≤ k → k < t → SepSet p m k I J U) →
      WA p m U t I J hI hJ ≤ WA p m U s I J hI hJ + ε * (t : ℝ) := by
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have htel := telescope_of_sep hp0 hp1 m I J hI hJ hid
  have hrun := Q_running_max_of_potMoment hp0 hp1 m I J hI hJ hid hC₁ hC₂ hPot hDiff
  filter_upwards [htel, hrun] with U htelU hrunU
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hev := hrunU (ε / 2) hε2
  filter_upwards [hev] with t ht s hst hsep
  have ht1 : Q p m I J hI hJ t U ≤ ε / 2 * (t : ℝ) := by
    have h := ht
    have h2 := Finset.le_sup' (fun r => |Q p m I J hI hJ r U|)
      (Finset.mem_range.mpr (Nat.lt_succ_self t)) (s := Finset.range (t + 1))
    have h3 : |Q p m I J hI hJ t U| ≤ ε / 2 * (t : ℝ) := le_trans h2 h
    linarith [le_abs_self (Q p m I J hI hJ t U)]
  have hs1 : -(ε / 2 * (t : ℝ)) ≤ Q p m I J hI hJ s U := by
    have h2 := Finset.le_sup' (fun r => |Q p m I J hI hJ r U|)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hst)) (s := Finset.range (t + 1))
    have h3 : |Q p m I J hI hJ s U| ≤ ε / 2 * (t : ℝ) := le_trans h2 ht
    have h4 := neg_abs_le (Q p m I J hI hJ s U)
    linarith
  have hW := htelU s t hst hsep
  push_cast at hs1 ht1 ⊢
  nlinarith [Nat.cast_nonneg (α := ℝ) s]

end SwarmQVariance
