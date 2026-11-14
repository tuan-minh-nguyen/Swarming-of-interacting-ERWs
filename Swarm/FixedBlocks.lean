/-
# Fixed-constant block goodness (paper's display (block)) for record data

`areas/recordo/RecordoSupply.recordo_blocks` proves the paper's block inequalities for every
fixed level `r` and all large `L`, but its constants `T`, `C₀` are produced by
`tau_le_of_speed`, whose slope `C = max (N₀+1) (4/κ+2)` contains the random threshold `N₀` of
the eventual speed bound.  Consequently `hterm_actual` has `∃ T C₀` **inside** the almost-sure
quantifier, and it does not match the fixed-constant shape that
`SimJump.RecKernel.probCtxRT`/`SwarmM4.PCtxR` require.

This file removes that defect.  The point is elementary: `tau_le_of_speed` only needs the speed
bound from `N₀` on, so the *identity*

  `τ r ≤ max N₀ (2 r / κ)`

holds with the fixed slope `2/κ`; the random `N₀` is then absorbed by the block length `L`
(it appears only additively, and `L` may be taken as large as we like).  Hence for

  `T = ⌈2 B / κ⌉ + 2`,   `C₀ = B + T + 1`

the paper's three block inequalities hold for every level `r` and all sufficiently large `L`,
with `T`, `C₀` depending only on the *model* constants `κ`, `B` — never on the path.

Main declarations:

* `tau_le_threshold`  : `τ r ≤ N₀ + (2/κ) r`.
* `recordo_blocks_fixed` : the paper's display (block) at fixed `T`, `C₀`.
* `hterm_fixed`      : the `hterm` doubling form at the same fixed constants.

Everything is a pathwise statement about one trajectory; the only analytic inputs are the fixed
slope `κ > 0` of a single walker and the defect limit `d_r / r → 0`.  No probability space is
hidden here.
-/
import Swarm.RecordoSupply

open Filter Topology MeasureTheory
open scoped BigOperators

namespace SwarmM4C

namespace FixedConst

open RecordDefect

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ### The record time from a one-walker speed bound with a fixed slope -/

/-- **`τ r ≤ N₀ + (2/κ) r`.**  If walker `i` satisfies the lower speed bound `(κ/2) n ≤ X i n`
for all `n ≥ N₀`, then the record time of level `r` is at most `N₀ + (2/κ) r`: either
`τ r < N₀`, or the speed bound applies at `τ r` where the running maximum equals `r`. -/
theorem tau_le_threshold {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    {i : ι} {κ : ℝ} (hκ : 0 < κ) {N₀ : ℕ}
    (hspd : ∀ n : ℕ, N₀ ≤ n → (κ / 2) * (n : ℝ) ≤ (X i n : ℝ)) (r : ℕ) :
    (τ r : ℝ) ≤ (N₀ : ℝ) + (2 / κ) * (r : ℝ) := by
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hnonneg : (0 : ℝ) ≤ (2 / κ) * (r : ℝ) := mul_nonneg (by positivity) hr0
  rcases lt_or_ge (τ r) N₀ with hlt | hge
  · have h1 : (τ r : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast Nat.le_of_lt hlt
    linarith
  · have hsp := hspd (τ r) hge
    have hrun : X i (τ r) ≤ runMax X (τ r) := le_runMax (τ r) i
    have hreq : runMax X (τ r) = (r : ℤ) := (hτ r).2
    have hreal : (κ / 2) * (τ r : ℝ) ≤ (r : ℝ) := by
      have hle : X i (τ r) ≤ (r : ℤ) := by rw [← hreq]; exact hrun
      have hle' : (X i (τ r) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hle
      linarith
    have hmul := mul_le_mul_of_nonneg_left hreal (by positivity : (0 : ℝ) ≤ 2 / κ)
    have hsimp : (2 / κ) * ((κ / 2) * (τ r : ℝ)) = (τ r : ℝ) := by
      field_simp
    have htarget : (2 / κ) * (r : ℝ) = 2 * (r : ℝ) / κ := by ring
    rw [hsimp, htarget] at hmul
    linarith

/-! ### The paper's display (block) at fixed constants -/

/-- **Fixed-constant `(block)`.**  For a nearest-neighbour family started at the origin, a record
sequence `τ`, a one-walker lower speed bound with fixed slope `κ`, and the defect limit
`d_r / r → 0`, the paper's three block inequalities hold for every level `r` and all sufficiently
large `L` with the *explicit* constants

  `T = ⌈2 B / κ⌉ + 2`,  `C₀ = B + T + 1`,

which depend only on `κ` and `B`.  The random threshold of the speed bound is absorbed into the
threshold of `L`: it enters the time clause only additively, and the defect clause only through
an eventual statement about `r + B L → ∞`. -/
theorem recordo_blocks_fixed {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0)
    {i : ι} {κ : ℝ} (hκ : 0 < κ)
    (hspd : ∀ᶠ n : ℕ in atTop, (κ / 2) * (n : ℝ) ≤ (X i n : ℝ))
    (hdlim : Tendsto (fun n : ℕ => (defect X τ n : ℝ) / (n : ℝ)) atTop (𝓝 0))
    (B : ℕ) (hB : 1 ≤ B) (r : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      RecordoSupply.GoodBlock (defect X τ) τ (⌈2 * (B : ℝ) / κ⌉₊ + 2)
        (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r L := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hspd
  set T : ℕ := ⌈2 * (B : ℝ) / κ⌉₊ + 2 with hTdef
  set C₀ : ℕ := B + T + 1 with hC₀def
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hTcoef : (2 * (B : ℝ) / κ) + 1 ≤ (T : ℝ) := by
    have h1 : (2 * (B : ℝ) / κ) ≤ ((⌈2 * (B : ℝ) / κ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 * (B : ℝ) / κ⌉₊ : ℕ) : ℝ) + 1 ≤ (T : ℝ) := by
      rw [hTdef]; push_cast; linarith
    linarith
  have hτmono : Monotone τ := tau_mono hτ
  have htau : ∀ s : ℕ, (τ s : ℝ) ≤ (N₀ : ℝ) + (2 / κ) * (s : ℝ) :=
    fun s => tau_le_threshold hτ hκ hN₀ s
  have hτge : ∀ s : ℕ, (s : ℝ) ≤ (τ s : ℝ) := fun s => by
    exact_mod_cast RecordoSupply.tau_ge hτ hne h0 s
  -- ### the time clause
  have htime : ∀ᶠ L : ℕ in atTop, τ (r + B * L) - τ r ≤ T * L := by
    set γ : ℝ := 2 * (B : ℝ) / κ with hγdef
    set β : ℝ := max 0 (2 / κ - 1) with hβdef
    have hLbig : ∀ᶠ L : ℕ in atTop, (N₀ : ℝ) + β * (r : ℝ) ≤ (L : ℝ) := by
      refine eventually_atTop.2 ⟨N₀ + ⌈|β| * (r : ℝ)⌉₊, fun L hL => ?_⟩
      have hLc : ((N₀ + ⌈|β| * (r : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      have hcast : ((N₀ + ⌈|β| * (r : ℝ)⌉₊ : ℕ) : ℝ)
          = (N₀ : ℝ) + ((⌈|β| * (r : ℝ)⌉₊ : ℕ) : ℝ) := by push_cast; ring
      have hceil : |β| * (r : ℝ) ≤ ((⌈|β| * (r : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have hbr : β * (r : ℝ) ≤ |β| * (r : ℝ) := by
        have h1 : β ≤ |β| := le_abs_self β
        exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg r)
      rw [hcast] at hLc
      linarith
    filter_upwards [hLbig, eventually_ge_atTop 1] with L hL hL1
    have hLpos : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    have hidx : r ≤ r + B * L := Nat.le_add_right r (B * L)
    have hmono : τ r ≤ τ (r + B * L) := hτmono hidx
    have hcast : ((r + B * L : ℕ) : ℝ) = (r : ℝ) + (B : ℝ) * (L : ℝ) := by push_cast; ring
    have h1 : (τ (r + B * L) : ℝ) ≤ (N₀ : ℝ) + (2 / κ) * ((r : ℝ) + (B : ℝ) * (L : ℝ)) := by
      rw [← hcast]; exact htau _
    have hexp : (2 / κ) * ((r : ℝ) + (B : ℝ) * (L : ℝ))
        = (2 / κ) * (r : ℝ) + γ * (L : ℝ) := by
      rw [hγdef]; ring
    have hβge : (2 / κ - 1) * (r : ℝ) ≤ β * (r : ℝ) := by
      have h1 : (2 / κ - 1) ≤ β := le_max_right _ _
      exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg r)
    have hLb : (N₀ : ℝ) + (2 / κ - 1) * (r : ℝ) ≤ (L : ℝ) := by linarith
    have hτr : (r : ℝ) ≤ (τ r : ℝ) := hτge r
    have hkey : (τ (r + B * L) : ℝ) - (τ r : ℝ) ≤ (γ + 1) * (L : ℝ) := by
      rw [hexp] at h1
      nlinarith [h1, hτr, hLb, hLpos]
    have hmul : (γ + 1) * (L : ℝ) ≤ (T : ℝ) * (L : ℝ) := by
      have h1 : γ + 1 ≤ (T : ℝ) := by rw [hγdef]; exact hTcoef
      exact mul_le_mul_of_nonneg_right h1 hLpos
    have hdiff : ((τ (r + B * L) - τ r : ℕ) : ℝ) = (τ (r + B * L) : ℝ) - (τ r : ℝ) := by
      push_cast [hmono]; ring
    have hreal : ((τ (r + B * L) - τ r : ℕ) : ℝ) ≤ (T * L : ℕ) := by
      rw [hdiff]
      have : ((T * L : ℕ) : ℝ) = (T : ℝ) * (L : ℝ) := by push_cast; ring
      linarith
    exact_mod_cast hreal
  -- ### the defect clause at `r + B L`
  have hdef : ∀ᶠ L : ℕ in atTop, 2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
    have heps : (0 : ℝ) < 1 / (4 * (B : ℝ)) := by positivity
    have hev : ∀ᶠ n : ℕ in atTop, |(defect X τ n : ℝ)| / (n : ℝ) < 1 / (4 * (B : ℝ)) := by
      have h := hdlim.eventually (Metric.ball_mem_nhds (0 : ℝ) heps)
      simpa [Real.dist_eq, abs_sub_comm] using h
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
    refine eventually_atTop.2 ⟨max (max N₁ r) 1, fun L hL => ?_⟩
    have hL1 : 1 ≤ L := le_trans (le_max_right (max N₁ r) 1) hL
    have hLN₁ : N₁ ≤ L := le_trans (le_max_left N₁ r) (le_trans (le_max_left (max N₁ r) 1) hL)
    have hLr : r ≤ L := le_trans (le_max_right N₁ r) (le_trans (le_max_left (max N₁ r) 1) hL)
    have hBL : L ≤ r + B * L :=
      le_trans (Nat.le_mul_of_pos_left L (by omega : 0 < B)) (Nat.le_add_left (B * L) r)
    have huN₁ : N₁ ≤ r + B * L := le_trans hLN₁ hBL
    have hu1 : 1 ≤ r + B * L := le_trans hL1 hBL
    have hupos : (0 : ℝ) < ((r + B * L : ℕ) : ℝ) := by exact_mod_cast hu1
    have habs := hN₁ (r + B * L) huN₁
    have hdiv : (defect X τ (r + B * L) : ℝ) / ((r + B * L : ℕ) : ℝ) < 1 / (4 * (B : ℝ)) :=
      lt_of_le_of_lt (div_le_div_of_nonneg_right (le_abs_self _) (le_of_lt hupos)) habs
    have hdu : (defect X τ (r + B * L) : ℝ) < (1 / (4 * (B : ℝ))) * ((r + B * L : ℕ) : ℝ) := by
      have hu : ((r + B * L : ℕ) : ℝ) ≠ 0 := ne_of_gt hupos
      calc (defect X τ (r + B * L) : ℝ)
          = ((defect X τ (r + B * L) : ℝ) / ((r + B * L : ℕ) : ℝ)) * ((r + B * L : ℕ) : ℝ) := by
            field_simp
        _ < (1 / (4 * (B : ℝ))) * ((r + B * L : ℕ) : ℝ) := by
            exact mul_lt_mul_of_pos_right hdiv hupos
    -- `r ≤ B L`, so `(r + B L) / (4 B) ≤ L / 2`
    have hrBL : (r : ℝ) ≤ (B : ℝ) * (L : ℝ) := by
      have h1 : r ≤ B * L := le_trans hLr (Nat.le_mul_of_pos_left L (by omega))
      have h2 : ((B * L : ℕ) : ℝ) = (B : ℝ) * (L : ℝ) := by push_cast; ring
      rw [← h2]; exact_mod_cast h1
    have hucast : ((r + B * L : ℕ) : ℝ) = (r : ℝ) + (B : ℝ) * (L : ℝ) := by push_cast; ring
    have hbound : (1 / (4 * (B : ℝ))) * ((r + B * L : ℕ) : ℝ) ≤ (L : ℝ) / 2 := by
      rw [hucast]
      have hsum : (r : ℝ) + (B : ℝ) * (L : ℝ) ≤ 2 * ((B : ℝ) * (L : ℝ)) := by linarith
      have h2 : (1 / (4 * (B : ℝ))) * ((r : ℝ) + (B : ℝ) * (L : ℝ))
          ≤ (1 / (4 * (B : ℝ))) * (2 * ((B : ℝ) * (L : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      have h3 : (1 / (4 * (B : ℝ))) * (2 * ((B : ℝ) * (L : ℝ))) = (L : ℝ) / 2 := by
        have hBne : (B : ℝ) ≠ 0 := ne_of_gt hBpos
        field_simp
        ring
      linarith
    have hd : 2 * (defect X τ (r + B * L) : ℝ) < (L : ℝ) := by linarith
    have hdz : 2 * defect X τ (r + B * L) < (L : ℤ) := by exact_mod_cast hd
    omega
  -- ### the third inequality on the block
  have hthird : ∀ᶠ L : ℕ in atTop,
      ∀ u : ℕ, r ≤ u → u ≤ r + B * L → defect X τ u ≤ (C₀ : ℤ) * (L : ℤ) := by
    have hrdef : ∀ᶠ L : ℕ in atTop, defect X τ r ≤ (L : ℤ) := by
      refine eventually_atTop.2 ⟨(defect X τ r).toNat, fun L hL => ?_⟩
      have h1 : (defect X τ r).toNat ≤ L := hL
      have h2 : defect X τ r ≤ ((defect X τ r).toNat : ℤ) := Int.self_le_toNat _
      have h3 : (((defect X τ r).toNat : ℕ) : ℤ) ≤ (L : ℤ) := by exact_mod_cast h1
      linarith
    filter_upwards [hrdef, htime] with L hrL hτL
    have := block_defect_bound hτ hne hrL hτL
    intro u hu1 hu2
    have := this u hu1 hu2
    simpa [hC₀def] using this
  filter_upwards [htime, hdef, hthird] with L h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **`hterm` at fixed constants.**  The doubling form of the tightness interface, with the same
fixed `T = ⌈2 B / κ⌉ + 2` and `C₀ = B + T + 1`. -/
theorem hterm_fixed {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} (hτ : IsRecord X τ)
    (hne : ∀ (i : ι) (n : ℕ), |X i (n + 1) - X i n| = 1) (h0 : ∀ i, X i 0 = 0)
    {i : ι} {κ : ℝ} (hκ : 0 < κ)
    (hspd : ∀ᶠ n : ℕ in atTop, (κ / 2) * (n : ℝ) ≤ (X i n : ℝ))
    (hdlim : Tendsto (fun n : ℕ => (defect X τ n : ℝ) / (n : ℝ)) atTop (𝓝 0))
    (B : ℕ) (hB : 1 ≤ B) :
    ∀ r L : ℕ, 1 ≤ L → ∃ j : ℕ,
      RecordoSupply.GoodBlock (defect X τ) τ (⌈2 * (B : ℝ) / κ⌉₊ + 2)
        (B + (⌈2 * (B : ℝ) / κ⌉₊ + 2) + 1) B r (2 ^ j * L) :=
  RecordoSupply.hterm_of_blocks (fun r => recordo_blocks_fixed hτ hne h0 hκ hspd hdlim B hB r)

end FixedConst

end SwarmM4C


