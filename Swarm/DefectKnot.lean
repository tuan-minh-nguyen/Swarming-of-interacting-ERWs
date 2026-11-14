/-
# The exact knotted defect at a record level, and the `(half)` limit passage

Source: `results/proposition-tight-expanded.md`, Section 5.2 ("Record advance and the
scaled hitting-time limit"), equations (5.9)-(5.14), and Section 5.3.

The source's second block inequality `(half)` is `2 * d_{r+BL} <= L`, obtained by passing
to the limit along the counterexample subsequence at the **exact record knot**
`tau_{r+BL}`.  Three ingredients are purely combinatorial and are proved here with no
probability, no fluid limit and no local-good event:

* `theta_mem_lower`, `theta_mem_upper` -- the scaled hitting-time ratio
  `theta_L = (tau_{r+BL} - tau_r)/L` lies in the compact interval `[B,T]` as soon as
  `(time)` holds.  The lower bound `B <= theta_L` uses only nearest-neighbour motion
  (`runMax_le_add`), not any ballistic input.
* `scaledPosition_knot`, `sup_scaled_knot_eq`, `inf_scaled_knot`, `defect_div_knot` --
  the source's exact knot identity (5.11): the actual record-window interpolant at the
  knot index `tau_{r+BL} - tau_r` is the literal scaled position
  `(X_i(tau_{r+BL}) - r)/L`; hence the sup of the knot configuration is *exactly* `B`, and
  the normalized defect is *exactly* `B` minus the inf of the knot configuration:
  `d_{r+BL}/L = B - inf_i x_i^{(L)}(theta_L)`.  This is (5.13) before the limit, and it is
  an identity, not an estimate.
* `half_ok_iff_inf_ge`, `half_fail_iff_inf_lt`, `knotSpread_eq` -- the arithmetic of the
  halving clause at the knot: `2 * d_{r+BL} <= L` holds exactly when the knot inf is at
  least `B - 1/2`, so the knot spread `sup - inf` is at least `1/2` exactly when `(half)`
  fails at that scale.  The boundary here is the ordinary `L/2`, i.e. `epsilon = 1/2`;
  the much smaller `HalfEps` of the sharper `EndGood` route plays no role.

The limit passage:

* `tendsto_inf'_finset`, `tendsto_sup'_finset` -- finite minima/maxima of convergent
  coordinate sequences converge, so the limit of the knot spread is the spread of the
  limit knot configuration.
* `half_eventually_of_coalesced` -- if the knot configurations converge to a coalesced
  limit then `(half)` holds for all sufficiently large members of the subsequence.
* `spread_ge_half_of_half_fails` -- conversely, if `(half)` fails at every member then the
  limit knot configuration has sup exactly `B` and inf at most `B - 1/2`: it is not
  coalesced, its spread is at least `1/2`, and `d_{r+BL}/L` does not tend to `0`.

So `(half)` holds eventually **iff** the actual knot configurations coalesce in the limit.
The only remaining fluid input of the halving clause is the source's `(5.6)`/`(5.12)`
coalescence statement, and nothing else; no stationary law, start density or
`NoCoalescence` hypothesis appears.

`knot_tendsto_of_uniform` is the glue to the accepted compactness package
(`FluidInterpolation.exists_record_interpolated_limit_subseq`): uniform convergence of the
literal record interpolants plus `theta_L -> theta` gives convergence of the literal scaled
positions at the exact knot for a *varying* knot index, which the accepted fixed-knot lemma
`BlkSeed.scaledPosition_at_knot_tendsto` does not cover.
-/
import Swarm.FluidInterpolationLimit

set_option linter.unusedSectionVars false

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace DefectKnot

open FluidInterpolation FluidLimit RecordDefect

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. First-passage record geometry -/

/-- A single walker rises by at most one per step. -/
theorem walk_le_add {X : ι → ℕ → ℤ}
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (i : ι) (n : ℕ) :
    ∀ d : ℕ, X i (n + d) ≤ X i n + (d : ℤ) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep : X i (n + d + 1) ≤ X i (n + d) + 1 := by
        have h := abs_le.mp (le_of_eq (hne i (n + d)))
        linarith [h.2]
      have hd : n + (d + 1) = n + d + 1 := by omega
      rw [hd]
      push_cast
      linarith

/-- The running maximum rises by at most one per step, hence is `1`-Lipschitz upward.
This is the only input to the lower end `B <= theta_L` of the compact interval. -/
theorem runMax_le_add {X : ι → ℕ → ℤ}
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {n m : ℕ} (hnm : n ≤ m) :
    runMax X m ≤ runMax X n + ((m - n : ℕ) : ℤ) := by
  have h : ∀ i ∈ (Finset.univ : Finset ι), X i m ≤ runMax X n + ((m - n : ℕ) : ℤ) := by
    intro i _
    have h1 := walk_le_add hne i n (m - n)
    rw [Nat.add_sub_cancel' hnm] at h1
    have h2 : X i n ≤ runMax X n := le_runMax n i
    linarith
  calc runMax X m
      = (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => X i m) := rfl
    _ ≤ runMax X n + ((m - n : ℕ) : ℤ) :=
        Finset.sup'_le Finset.univ_nonempty (fun i => X i m) h

/-- Reaching record level `u` from record level `r` needs at least `u - r` steps. -/
theorem tau_level_le {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {r u : ℕ} (hru : r ≤ u) :
    τ r + (u - r) ≤ τ u := by
  have hmono : τ r ≤ τ u := tau_mono hτ hru
  have h1 : runMax X (τ u) ≤ runMax X (τ r) + ((τ u - τ r : ℕ) : ℤ) :=
    runMax_le_add hne hmono
  rw [(hτ u).2, (hτ r).2] at h1
  have hcast : ((τ u - τ r : ℕ) : ℤ) = (τ u : ℤ) - (τ r : ℤ) := by
    push_cast [hmono]; ring
  rw [hcast] at h1
  have h2 : (u : ℤ) - (r : ℤ) ≤ (τ u : ℤ) - (τ r : ℤ) := by linarith
  have h3 : u - r ≤ τ u - τ r := by omega
  omega

/-! ## 2. The scaled hitting time `theta_L` lies in `[B, T]` -/

/-- The knot index `tau_{r+BL} - tau_r`. -/
def knotIdx (τ : ℕ → ℕ) (B r L : ℕ) : ℕ := τ (r + B * L) - τ r

/-- The scaled hitting time `theta_L = (tau_{r+BL} - tau_r)/L`. -/
noncomputable def thetaL (τ : ℕ → ℕ) (B r L : ℕ) : ℝ :=
  (knotIdx τ B r L : ℝ) / (L : ℝ)

/-- `theta_L >= B`: the lower end of the compact interval in (5.10). -/
theorem theta_mem_lower {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) {B r L : ℕ} (hL : 0 < L) :
    (B : ℝ) ≤ thetaL τ B r L := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hble : τ r + (B * L) ≤ τ (r + B * L) := by
    have h := tau_level_le hτ hne (Nat.le_add_right r (B * L))
    rwa [Nat.add_sub_cancel_left] at h
  have hsub : B * L ≤ knotIdx τ B r L := by
    unfold knotIdx
    omega
  have hcast : ((B * L : ℕ) : ℝ) ≤ (knotIdx τ B r L : ℝ) := by exact_mod_cast hsub
  have hBL : ((B * L : ℕ) : ℝ) = (B : ℝ) * (L : ℝ) := by push_cast; ring
  rw [hBL] at hcast
  unfold thetaL
  rw [le_div_iff₀ hLr]
  linarith

/-- `theta_L <= T` under the first block inequality `(time)`. -/
theorem theta_mem_upper {τ : ℕ → ℕ} {B r L T : ℕ}
    (htime : τ (r + B * L) - τ r ≤ T * L) (hL : 0 < L) :
    thetaL τ B r L ≤ (T : ℝ) := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hcast : (knotIdx τ B r L : ℝ) ≤ ((T * L : ℕ) : ℝ) := by
    unfold knotIdx
    exact_mod_cast htime
  have hTL : ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
  rw [hTL] at hcast
  unfold thetaL
  rw [div_le_iff₀ hLr]
  linarith

/-! ## 3. The exact knot identity and the exact defect identity -/

/-- **The exact knot identity.**  The actual record-window interpolant at the knot index
`tau_{r+BL} - tau_r` is the literal scaled position. -/
theorem scaledPosition_knot {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    {B r L : ℕ} (i : ι) :
    scaledPosition X r (τ r) L i (knotIdx τ B r L)
      = (((X i (τ (r + B * L)) : ℤ) : ℝ) - (r : ℝ)) / (L : ℝ) := by
  have hmono : τ r ≤ τ (r + B * L) := tau_mono hτ (Nat.le_add_right r (B * L))
  unfold scaledPosition knotIdx
  rw [Nat.add_sub_cancel' hmono]

/-- Sup of a scaled block, evaluated through the running maximum. -/
theorem sup_scaledPosition_eq {X : ι → ℕ → ℤ} {level start scale : ℕ} (hscale : 0 < scale)
    (k : ℕ) :
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => scaledPosition X level start scale i k)
      = (((runMax X (start + k) : ℤ) : ℝ) - (level : ℝ)) / (scale : ℝ) := by
  have hd : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hscale
  refine le_antisymm ?_ ?_
  · refine (Finset.sup'_le_iff Finset.univ_nonempty
        (fun i => scaledPosition X level start scale i k)).2 ?_
    intro i _
    rw [scaledPosition]
    have h1 : X i (start + k) ≤ runMax X (start + k) := le_runMax _ i
    have h2 : ((X i (start + k) : ℤ) : ℝ) ≤ ((runMax X (start + k) : ℤ) : ℝ) := by
      exact_mod_cast h1
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  · obtain ⟨i₀, -, hi₀⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => X i (start + k))
    have h2 : ((runMax X (start + k) : ℤ) : ℝ) = ((X i₀ (start + k) : ℤ) : ℝ) := by
      rw [show runMax X (start + k)
            = (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => X i (start + k)) from rfl,
        hi₀]
    rw [h2]
    exact Finset.le_sup' (fun i => scaledPosition X level start scale i k) (Finset.mem_univ i₀)

/-- Inf of a scaled block, evaluated through the running minimum. -/
theorem inf_scaledPosition_eq {X : ι → ℕ → ℤ} {level start scale : ℕ} (hscale : 0 < scale)
    (k : ℕ) :
    (Finset.univ : Finset ι).inf' Finset.univ_nonempty
        (fun i => scaledPosition X level start scale i k)
      = (((runMin X (start + k) : ℤ) : ℝ) - (level : ℝ)) / (scale : ℝ) := by
  have hd : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hscale
  refine le_antisymm ?_ ?_
  · obtain ⟨i₀, -, hi₀⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => X i (start + k))
    have h2 : ((runMin X (start + k) : ℤ) : ℝ) = ((X i₀ (start + k) : ℤ) : ℝ) := by
      rw [show runMin X (start + k)
            = (Finset.univ : Finset ι).inf' Finset.univ_nonempty (fun i => X i (start + k)) from rfl,
        hi₀]
    rw [h2]
    exact Finset.inf'_le (fun i => scaledPosition X level start scale i k) (Finset.mem_univ i₀)
  · refine (Finset.le_inf'_iff Finset.univ_nonempty
        (fun i => scaledPosition X level start scale i k)).2 ?_
    intro i _
    rw [scaledPosition]
    have h1 : runMin X (start + k) ≤ X i (start + k) := runMin_le _ i
    have h2 : ((runMin X (start + k) : ℤ) : ℝ) ≤ ((X i (start + k) : ℤ) : ℝ) := by
      exact_mod_cast h1
    exact div_le_div_of_nonneg_right (by linarith) hd.le

/-- The running maximum at the sharp record time is the record level. -/
theorem runMax_record {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ) {B r L : ℕ} :
    ((runMax X (τ (r + B * L)) : ℤ) : ℝ) = (r : ℝ) + (B : ℝ) * (L : ℝ) := by
  rw [(hτ (r + B * L)).2]
  push_cast
  ring

/-- **The source's (5.11):** the sup of the knot configuration is exactly `B`. -/
theorem sup_scaled_knot_eq {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ) {B r L : ℕ}
    (hL : 0 < L) :
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => scaledPosition X r (τ r) L i (knotIdx τ B r L)) = (B : ℝ) := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hmono : τ r ≤ τ (r + B * L) := tau_mono hτ (Nat.le_add_right r (B * L))
  have hidx : τ r + knotIdx τ B r L = τ (r + B * L) := Nat.add_sub_cancel' hmono
  rw [sup_scaledPosition_eq hL, hidx, runMax_record hτ]
  rw [div_eq_iff hLr.ne']
  ring

/-- The inf of the knot configuration, as a running minimum. -/
theorem inf_scaled_knot {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ) {B r L : ℕ}
    (hL : 0 < L) :
    (Finset.univ : Finset ι).inf' Finset.univ_nonempty
        (fun i => scaledPosition X r (τ r) L i (knotIdx τ B r L))
      = (((runMin X (τ (r + B * L)) : ℤ) : ℝ) - (r : ℝ)) / (L : ℝ) := by
  have hmono : τ r ≤ τ (r + B * L) := tau_mono hτ (Nat.le_add_right r (B * L))
  have hidx : τ r + knotIdx τ B r L = τ (r + B * L) := Nat.add_sub_cancel' hmono
  rw [inf_scaledPosition_eq hL, hidx]

/-- **The source's (5.13) before the limit: the normalized defect at the sharp record
level is exactly `B` minus the inf of the knot configuration.** -/
theorem defect_div_knot {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ) {B r L : ℕ}
    (hL : 0 < L) :
    ((defect X τ (r + B * L) : ℤ) : ℝ) / (L : ℝ)
      = (B : ℝ) - (Finset.univ : Finset ι).inf' Finset.univ_nonempty
          (fun i => scaledPosition X r (τ r) L i (knotIdx τ B r L)) := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  rw [inf_scaled_knot hτ hL]
  have hlev : ((r + B * L : ℕ) : ℝ) = (r : ℝ) + (B : ℝ) * (L : ℝ) := by push_cast; ring
  rw [defect]
  have hcast : (((↑(r + B * L) : ℤ) - runMin X (τ (r + B * L)) : ℤ) : ℝ)
      = ((r : ℝ) + (B : ℝ) * (L : ℝ)) - ((runMin X (τ (r + B * L)) : ℤ) : ℝ) := by
    rw [Int.cast_sub]
    push_cast
    ring
  rw [hcast]
  field_simp
  ring

/-- The exact knot spread is the normalized defect: no estimate is involved. -/
theorem knotSpread_eq {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ) {B r L : ℕ}
    (hL : 0 < L) :
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => scaledPosition X r (τ r) L i (knotIdx τ B r L))
      - (Finset.univ : Finset ι).inf' Finset.univ_nonempty
        (fun i => scaledPosition X r (τ r) L i (knotIdx τ B r L))
      = ((defect X τ (r + B * L) : ℤ) : ℝ) / (L : ℝ) := by
  rw [sup_scaled_knot_eq hτ hL, defect_div_knot hτ hL]

/-! ## 4. The halving clause at the knot -/

/-- `(half)` holds exactly when the knot inf is at least `B - 1/2`. -/
theorem half_ok_iff_inf_ge {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ) {B r L : ℕ}
    (hL : 0 < L) :
    (2 * defect X τ (r + B * L) ≤ (L : ℤ)) ↔
      (B : ℝ) - 1 / 2 ≤ (Finset.univ : Finset ι).inf' Finset.univ_nonempty
        (fun i => scaledPosition X r (τ r) L i (knotIdx τ B r L)) := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hkey : ((defect X τ (r + B * L) : ℤ) : ℝ) / (L : ℝ)
      = (B : ℝ) - (Finset.univ : Finset ι).inf' Finset.univ_nonempty
          (fun i => scaledPosition X r (τ r) L i (knotIdx τ B r L)) :=
    defect_div_knot hτ hL
  have h1 : (2 * defect X τ (r + B * L) ≤ (L : ℤ)) ↔
      (2 * (((defect X τ (r + B * L) : ℤ) : ℝ)) ≤ (L : ℝ)) := by
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  have h2 : (2 * ((((defect X τ (r + B * L) : ℤ) : ℝ)) / (L : ℝ)) ≤ 1) ↔
      (2 * (((defect X τ (r + B * L) : ℤ) : ℝ)) ≤ (L : ℝ)) := by
    rw [show 2 * ((((defect X τ (r + B * L) : ℤ) : ℝ)) / (L : ℝ))
          = (2 * (((defect X τ (r + B * L) : ℤ) : ℝ))) / (L : ℝ) by ring,
      div_le_iff₀ hLr, one_mul]
  rw [h1, ← h2, hkey]
  constructor <;> intro h <;> linarith

/-- `(half)` fails exactly when the knot inf is strictly below `B - 1/2`. -/
theorem half_fail_iff_inf_lt {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ) {B r L : ℕ}
    (hL : 0 < L) :
    (¬ (2 * defect X τ (r + B * L) ≤ (L : ℤ))) ↔
      (Finset.univ : Finset ι).inf' Finset.univ_nonempty
        (fun i => scaledPosition X r (τ r) L i (knotIdx τ B r L)) < (B : ℝ) - 1 / 2 := by
  rw [half_ok_iff_inf_ge hτ hL, not_le]

/-! ## 5. Finite minima and maxima of convergent sequences -/

/-- Finite infima of convergent coordinate sequences converge to the infimum of the
limits. -/
theorem tendsto_inf'_finset {z : ℕ → ι → ℝ} {y : ι → ℝ}
    (h : ∀ i, Tendsto (fun n => z n i) atTop (𝓝 (y i))) :
    Tendsto (fun n => (Finset.univ : Finset ι).inf' Finset.univ_nonempty (fun i => z n i))
      atTop (𝓝 ((Finset.univ : Finset ι).inf' Finset.univ_nonempty y)) := by
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty y
  have hval : (Finset.univ : Finset ι).inf' Finset.univ_nonempty y = y i₀ := hi₀
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hall : ∀ᶠ n in atTop, ∀ i, y i - ε / 2 < z n i := by
    rw [eventually_all]
    intro i
    exact (tendsto_order.1 (h i)).1 (y i - ε / 2) (by linarith)
  have hup : ∀ᶠ n in atTop, z n i₀ < y i₀ + ε / 2 :=
    (tendsto_order.1 (h i₀)).2 (y i₀ + ε / 2) (by linarith)
  filter_upwards [hall, hup] with n hn hupn
  rw [Real.dist_eq, hval]
  have hle : (Finset.univ : Finset ι).inf' Finset.univ_nonempty (fun i => z n i) ≤ z n i₀ :=
    Finset.inf'_le (fun i => z n i) (Finset.mem_univ i₀)
  have hmid : y i₀ - ε / 2 ≤ (Finset.univ : Finset ι).inf' Finset.univ_nonempty (fun i => z n i) := by
    refine Finset.le_inf' Finset.univ_nonempty (fun i => z n i) ?_
    intro i _
    have h1 : y i₀ ≤ y i := by
      rw [← hval]
      exact Finset.inf'_le (fun j => y j) (Finset.mem_univ i)
    linarith [hn i]
  have hlow : y i₀ - ε < (Finset.univ : Finset ι).inf' Finset.univ_nonempty (fun i => z n i) := by
    linarith
  have hhigh : (Finset.univ : Finset ι).inf' Finset.univ_nonempty (fun i => z n i) < y i₀ + ε :=
    lt_of_le_of_lt hle (by linarith)
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- Finite suprema of convergent coordinate sequences converge to the supremum of the
limits. -/
theorem tendsto_sup'_finset {z : ℕ → ι → ℝ} {y : ι → ℝ}
    (h : ∀ i, Tendsto (fun n => z n i) atTop (𝓝 (y i))) :
    Tendsto (fun n => (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => z n i))
      atTop (𝓝 ((Finset.univ : Finset ι).sup' Finset.univ_nonempty y)) := by
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty y
  have hval : (Finset.univ : Finset ι).sup' Finset.univ_nonempty y = y i₀ := hi₀
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hall : ∀ᶠ n in atTop, ∀ i, z n i < y i + ε / 2 := by
    rw [eventually_all]
    intro i
    exact (tendsto_order.1 (h i)).2 (y i + ε / 2) (by linarith)
  have hlow : ∀ᶠ n in atTop, y i₀ - ε / 2 < z n i₀ :=
    (tendsto_order.1 (h i₀)).1 (y i₀ - ε / 2) (by linarith)
  filter_upwards [hall, hlow] with n hn hlown
  rw [Real.dist_eq, hval]
  have hle : z n i₀ ≤ (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => z n i) :=
    Finset.le_sup' (fun i => z n i) (Finset.mem_univ i₀)
  have hhigh : (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => z n i) ≤ y i₀ + ε / 2 := by
    refine Finset.sup'_le Finset.univ_nonempty (fun i => z n i) ?_
    intro i _
    have h1 : y i ≤ y i₀ := by
      rw [← hval]
      exact Finset.le_sup' (fun j => y j) (Finset.mem_univ i)
    linarith [hn i]
  have hlow' : y i₀ - ε < (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => z n i) :=
    lt_of_lt_of_le (by linarith) hle
  have hhigh' : (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => z n i) < y i₀ + ε := by
    linarith
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

/-! ## 6. The knot configuration of a sequence of record windows -/

/-- The scaled knot configuration of the `n`-th member of a sequence. -/
noncomputable def knotConf (X : ℕ → ι → ℕ → ℤ) (τ : ℕ → ℕ → ℕ) (B : ℕ)
    (level scale : ℕ → ℕ) (n : ℕ) : ι → ℝ :=
  fun i => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
    (knotIdx (τ n) B (level n) (scale n))

/-- The sup of the knot configuration of the `n`-th member is exactly `B`. -/
theorem sup_knotConf {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {B : ℕ} {level scale : ℕ → ℕ}
    (hτ : ∀ n, IsRecord (X n) (τ n)) (hL : ∀ n, 0 < scale n) (n : ℕ) :
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty (knotConf X τ B level scale n)
      = (B : ℝ) :=
  sup_scaled_knot_eq (hτ n) (hL n)

/-- **`(half)` holds eventually when the knot configurations coalesce in the limit.**

This is the source's passage (5.13)-(5.14) with the exact knot identity: the limit of
`d_{r+BL}/L` is `B - inf_i y_i`, and coalescence forces `inf_i y_i = sup_i y_i = B`. -/
theorem half_eventually_of_coalesced {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {B : ℕ}
    {level scale : ℕ → ℕ} (hτ : ∀ n, IsRecord (X n) (τ n)) (hL : ∀ n, 0 < scale n)
    {y : ι → ℝ}
    (hlim : ∀ i, Tendsto (fun n => knotConf X τ B level scale n i) atTop (𝓝 (y i)))
    (hcoal : ∀ i j, y i = y j) :
    ∀ᶠ n in atTop, 2 * defect (X n) (τ n) (level n + B * scale n) ≤ (scale n : ℤ) := by
  -- the sup of the limit is `B`
  have hsupT := tendsto_sup'_finset hlim
  have hconst : (fun n => (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i => knotConf X τ B level scale n i)) = fun _ => (B : ℝ) := by
    funext n
    exact sup_knotConf hτ hL n
  rw [hconst] at hsupT
  have hsupB : (Finset.univ : Finset ι).sup' Finset.univ_nonempty y = (B : ℝ) :=
    tendsto_nhds_unique hsupT tendsto_const_nhds
  -- coalescence: the inf of the limit is also `B`
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty y
  have hconsty : ∀ i, y i = y i₀ := fun i => hcoal i i₀
  have hsup_eq : (Finset.univ : Finset ι).sup' Finset.univ_nonempty y = y i₀ := by
    refine le_antisymm ?_ ?_
    · refine Finset.sup'_le Finset.univ_nonempty y ?_
      intro i _
      rw [hconsty i]
    · exact Finset.le_sup' y (Finset.mem_univ i₀)
  have hy0 : y i₀ = (B : ℝ) := by
    rw [← hsup_eq]
    exact hsupB
  have hinfB : (Finset.univ : Finset ι).inf' Finset.univ_nonempty y = (B : ℝ) :=
    hi₀.trans hy0
  -- hence `d_{r+BL}/L = B - inf -> 0`
  have hinfT := tendsto_inf'_finset hlim
  have hzero : Tendsto (fun n =>
      ((defect (X n) (τ n) (level n + B * scale n) : ℤ) : ℝ) / (scale n : ℝ))
      atTop (𝓝 0) := by
    have hfun : (fun n =>
        ((defect (X n) (τ n) (level n + B * scale n) : ℤ) : ℝ) / (scale n : ℝ))
        = fun n => (B : ℝ) - (Finset.univ : Finset ι).inf' Finset.univ_nonempty
            (fun i => knotConf X τ B level scale n i) := by
      funext n
      exact defect_div_knot (hτ n) (hL n)
    rw [hfun]
    have hsub := hinfT.const_sub (B : ℝ)
    rw [hinfB] at hsub
    simpa using hsub
  have hev : ∀ᶠ n in atTop,
      ((defect (X n) (τ n) (level n + B * scale n) : ℤ) : ℝ) / (scale n : ℝ) < 1 / 2 :=
    (tendsto_order.1 hzero).2 (1 / 2) (by norm_num)
  filter_upwards [hev] with n hn
  have hlt : 2 * (((defect (X n) (τ n) (level n + B * scale n) : ℤ) : ℝ)) < (scale n : ℝ) := by
    have h2 : 2 * ((((defect (X n) (τ n) (level n + B * scale n) : ℤ) : ℝ)) / (scale n : ℝ)) < 1 := by
      linarith
    rw [show 2 * ((((defect (X n) (τ n) (level n + B * scale n) : ℤ) : ℝ)) / (scale n : ℝ))
          = (2 * (((defect (X n) (τ n) (level n + B * scale n) : ℤ) : ℝ))) / (scale n : ℝ)
        by ring,
      div_lt_iff₀ (by exact_mod_cast hL n), one_mul] at h2
    exact h2
  have hlt' : ((2 * defect (X n) (τ n) (level n + B * scale n) : ℤ) : ℝ) < (scale n : ℝ) := by
    push_cast
    linarith
  exact le_of_lt (by exact_mod_cast hlt')

/-- **A persistent failure of `(half)` forces a non-coalesced limit knot configuration.**

If `(half)` fails at every member of the subsequence, the limit knot configuration has sup
exactly `B` and inf at most `B - 1/2`: its spread is at least `1/2`, so the fluid positions
at the knot are *not* all equal.  This is the contrapositive of the source's (5.12). -/
theorem spread_ge_half_of_half_fails {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {B : ℕ}
    {level scale : ℕ → ℕ} (hτ : ∀ n, IsRecord (X n) (τ n)) (hL : ∀ n, 0 < scale n)
    {y : ι → ℝ}
    (hlim : ∀ i, Tendsto (fun n => knotConf X τ B level scale n i) atTop (𝓝 (y i)))
    (hfail : ∀ n, ¬ (2 * defect (X n) (τ n) (level n + B * scale n) ≤ (scale n : ℤ))) :
    ((Finset.univ : Finset ι).sup' Finset.univ_nonempty y
        - (Finset.univ : Finset ι).inf' Finset.univ_nonempty y ≥ (1 / 2 : ℝ)) ∧
      ¬ (∀ i j, y i = y j) := by
  have hsupT := tendsto_sup'_finset hlim
  have hconst : (fun n => (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i => knotConf X τ B level scale n i)) = fun _ => (B : ℝ) := by
    funext n
    exact sup_knotConf hτ hL n
  rw [hconst] at hsupT
  have hsupB : (Finset.univ : Finset ι).sup' Finset.univ_nonempty y = (B : ℝ) :=
    tendsto_nhds_unique hsupT tendsto_const_nhds
  have hinfT := tendsto_inf'_finset hlim
  have hle : (Finset.univ : Finset ι).inf' Finset.univ_nonempty y ≤ (B : ℝ) - 1 / 2 := by
    refine le_of_tendsto hinfT ?_
    filter_upwards [Filter.Eventually.of_forall hfail] with n hn
    exact le_of_lt ((half_fail_iff_inf_lt (hτ n) (hL n)).1 hn)
  refine ⟨by linarith, ?_⟩
  intro hconst_all
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty y
  obtain ⟨i₂, -, hi₂⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty y
  have : (Finset.univ : Finset ι).inf' Finset.univ_nonempty y
      = (Finset.univ : Finset ι).sup' Finset.univ_nonempty y := by
    rw [hi₁, hi₂, hconst_all i₁ i₂]
  rw [this, hsupB] at hle
  linarith

/-! ## 7. Glue to the accepted compactness package: a varying knot -/

/-- The record interpolant at a grid knot is the scaled position (local copy of the
accepted `BlkSeed.recordFamily_apply_of_eq`, to keep this module's imports minimal). -/
theorem recordFamily_apply_knot {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) {T : ℝ} (n : ℕ) (i : ι) {t : Set.Icc (0 : ℝ) T} {k : ℕ}
    (ht : (t : ℝ) = (k : ℝ) / (scale n : ℝ)) (hk : k ≤ rawHorizon T (scale n)) :
    recordFamily X τ level scale hscale T n i t
      = scaledPosition (X n) (level n) (τ n (level n)) (scale n) i k := by
  have h1 : recordFamily X τ level scale hscale T n i t
      = scaledInterp (X n) (level n) (τ n (level n)) (scale n) i
          (rawHorizon T (scale n)) (t : ℝ) := rfl
  rw [h1, ht]
  exact scaledInterp_at_knot (X n) (level n) (τ n (level n)) (scale n) i (hscale n) hk

/-- **Convergence at the exact knot with a varying knot index.**  Uniform convergence of the
literal record interpolants, plus convergence of the scaled raw knot times, gives convergence
of the literal scaled positions at the knot `k n`.  The accepted
`BlkSeed.scaledPosition_at_knot_tendsto` covers only a fixed knot `m * scale n`. -/
theorem knot_tendsto_of_uniform {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) {T : ℝ} {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n => ⇑(recordFamily X τ level scale hscale T n i)) (fun t => x i t) atTop)
    {k : ℕ → ℕ} {t : ℕ → Set.Icc (0 : ℝ) T} {tlim : Set.Icc (0 : ℝ) T}
    (ht : ∀ n, (t n : ℝ) = (k n : ℝ) / (scale n : ℝ))
    (hk : ∀ n, k n ≤ rawHorizon T (scale n))
    (htend : Tendsto t atTop (𝓝 tlim)) (i : ι) :
    Tendsto (fun n => scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (k n))
      atTop (𝓝 (x i tlim)) := by
  have hpt : ∀ n, scaledPosition (X n) (level n) (τ n (level n)) (scale n) i (k n)
      = recordFamily X τ level scale hscale T n i (t n) :=
    fun n => (recordFamily_apply_knot hscale n i (ht n) (hk n)).symm
  simp only [hpt]
  have hxcont : Tendsto (fun n => x i (t n)) atTop (𝓝 (x i tlim)) :=
    ((x i).continuous.tendsto tlim).comp htend
  have hunif : Tendsto
      (fun n => recordFamily X τ level scale hscale T n i (t n) - x i (t n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp (hconv i) ε hε] with n hn
    have h := hn (t n)
    rw [Real.dist_eq] at h ⊢
    simpa only [sub_zero, abs_sub_comm] using h
  have hsum := hunif.add hxcont
  simpa only [sub_add_cancel, zero_add] using hsum

end DefectKnot
