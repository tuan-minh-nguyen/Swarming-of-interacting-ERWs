/-
# The sharp `(half)` clause from coalescence at ONE fluid time

`CoalescenceTime.exists_coalescence_time_sharp` needs the fluid limit to be coincident on the
whole interval `[s,T]`.  The source's step 6 gives only the *pointwise* statement (5.6):
`there is s_* < B - 2 < T with x_1(s_*) = ... = x_N(s_*)`.  This file gets the sharp `(half)`
from that pointwise statement alone.

The mechanism is that the grid knot does **not** have to land on the fluid time `s_*`: it is
enough to take the knot `k n` with `k n / L_n -> s_*`, because

* the finite-scale value at that knot is within `b/8` of the fluid value there (uniform
  convergence of the raw samples), and
* the fluid values at two times within `c/L` of each other differ by at most `2c/L` (the limit
  is `1`-Lipschitz, which the accepted compactness export provides as `LipschitzWith 1 (x i)`).

So coincidence at the single fluid time `s_*` already produces the one small-spread grid time,
with no persistence, no `StickyOn` and no invariant/stationary input.  The explicit side
condition is `64 ceil(C) <= s_*`: the coalescence time must lie at or after the sharp start of
the record window (in the source, `s_* >= 64 C`).

Residual after this file: the paper's (5.6) -- pointwise fluid coalescence at a time
`s_*` with `64 ceil(C) <= s_* <= B` -- plus the per-scale clause package, the advance clause
`(time)` and the accepted compactness convergence.  Nothing else.
-/
import Swarm.CoalescenceTime
import Swarm.EndpointHalving

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction NNReal

namespace FluidCoincide

open FluidInterpolation FluidLimit Glue JoinStep RecordDefect

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## 1. The knot at a single coincident fluid time -/

/-- **One small-spread grid time from coincidence at a single fluid time.**

If all fluid coordinates agree at the fluid time `s`, and the knot `k n` satisfies
`|k n / scale n - s| <= c / scale n` and stays inside the fluid horizon, then eventually the
whole-pack spread at the grid time `tau_r + k n` is at most `b L`. -/
theorem spreadS_at_knot_le_of_single_coincidence
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ} {level scale : ℕ → ℕ}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    {T : ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T)
    {x : ι → (Set.Icc (0 : ℝ) T →ᵇ ℝ)}
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) T) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i : ι, LipschitzWith 1 (x i))
    (hcoin : ∀ i j : ι, x i ⟨s, hs0, hsT⟩ = x j ⟨s, hs0, hsT⟩)
    (k : ℕ → ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hkT : ∀ n, (k n : ℝ) ≤ T * (scale n : ℝ))
    (hknear : ∀ n, |(k n : ℝ) / (scale n : ℝ) - s| ≤ c / (scale n : ℝ))
    (b : ℝ) (hb : 0 < b) :
    ∀ᶠ n in atTop,
      ((spreadS (X n) (Finset.univ : Finset ι) (τ n (level n) + k n) : ℤ) : ℝ)
        ≤ b * (scale n : ℝ) := by
  have hc8 : (0 : ℝ) < b / 8 := by positivity
  -- uniform closeness at the knots
  have hclose : ∀ᶠ n in atTop, ∀ i : ι, ∀ t : Set.Icc (0 : ℝ) T,
      |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon T (scale n)) t) - x i t| ≤ b / 8 :=
    eventually_uniform_close (X := X) (τ := τ) (level := level) (scale := scale)
      (T := T) (x := x) hconv hc8
  -- the knot is close enough to the coalescence time
  have hroom : ∀ᶠ n in atTop, 2 * c / (scale n : ℝ) ≤ b / 2 := by
    have hcast : Tendsto (fun n : ℕ => (scale n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hscaleTop
    have hge : ∀ᶠ n in atTop, 8 * c / b ≤ (scale n : ℝ) :=
      hcast.eventually_ge_atTop (8 * c / b)
    filter_upwards [hge] with n hn
    have hscR : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
    have hb8 : 8 * c ≤ b * (scale n : ℝ) := by
      have h1 : b * (8 * c / b) ≤ b * (scale n : ℝ) := mul_le_mul_of_nonneg_left hn hb.le
      have h2 : b * (8 * c / b) = 8 * c := by field_simp
      linarith [h1, h2]
    rw [div_le_iff₀ hscR]
    linarith
  filter_upwards [hclose, hroom] with n hn hroomn
  have hscR : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  -- the fluid time of the knot
  have ht0 : (0 : ℝ) ≤ (k n : ℝ) / (scale n : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hscR.le
  have htT : (k n : ℝ) / (scale n : ℝ) ≤ T := by
    rw [div_le_iff₀ hscR]
    linarith [hkT n]
  set t : Set.Icc (0 : ℝ) T := ⟨(k n : ℝ) / (scale n : ℝ), ht0, htT⟩ with ht
  have htval : (t : ℝ) = (k n : ℝ) / (scale n : ℝ) := rfl
  have hraw : rawSample (scale n) (rawHorizon T (scale n)) t = k n := by
    rw [htval]
    exact rawSample_at_knot (hscale n) (hkT n)
  obtain ⟨i₁, hi₁, hmax⟩ :=
    exists_sMax (X := X n) (S := Finset.univ) (n := τ n (level n) + k n) Finset.univ_nonempty
  obtain ⟨j₁, hj₁, hmin⟩ :=
    exists_sMin (X := X n) (S := Finset.univ) (n := τ n (level n) + k n) Finset.univ_nonempty
  have h1 : |scaledPosition (X n) (level n) (τ n (level n)) (scale n) i₁ (k n)
      - x i₁ t| ≤ b / 8 := by
    have := hn i₁ t
    rwa [hraw] at this
  have h2 : |scaledPosition (X n) (level n) (τ n (level n)) (scale n) j₁ (k n)
      - x j₁ t| ≤ b / 8 := by
    have := hn j₁ t
    rwa [hraw] at this
  -- the fluid gap at the knot, from `1`-Lipschitz and coincidence at `s`
  have hdistt : dist t ⟨s, hs0, hsT⟩ = |(t : ℝ) - s| := Subtype.dist_eq ..
  have hlipi : dist (x i₁ t) (x i₁ ⟨s, hs0, hsT⟩) ≤ |(t : ℝ) - s| := by
    have := (hlip i₁).dist_le_mul t ⟨s, hs0, hsT⟩
    simpa [hdistt] using this
  have hlipj : dist (x j₁ t) (x j₁ ⟨s, hs0, hsT⟩) ≤ |(t : ℝ) - s| := by
    have := (hlip j₁).dist_le_mul t ⟨s, hs0, hsT⟩
    simpa [hdistt] using this
  have hneart : |(t : ℝ) - s| ≤ c / (scale n : ℝ) := by
    rw [htval]
    exact hknear n
  have h12 : x i₁ t ≤ x j₁ t + 2 * (c / (scale n : ℝ)) := by
    have hi : |x i₁ t - x i₁ ⟨s, hs0, hsT⟩| ≤ c / (scale n : ℝ) := by
      rw [Real.dist_eq] at hlipi
      exact le_trans hlipi hneart
    have hj : |x j₁ t - x j₁ ⟨s, hs0, hsT⟩| ≤ c / (scale n : ℝ) := by
      rw [Real.dist_eq] at hlipj
      exact le_trans hlipj hneart
    have heq : x i₁ ⟨s, hs0, hsT⟩ = x j₁ ⟨s, hs0, hsT⟩ := hcoin i₁ j₁
    have hA := abs_le.mp hi
    have hB := abs_le.mp hj
    linarith [hA.1, hA.2, hB.1, hB.2, heq]
  -- assemble
  have hspread : ((spreadS (X n) (Finset.univ : Finset ι)
      (τ n (level n) + k n) : ℤ) : ℝ)
      = (X n i₁ (τ n (level n) + k n) : ℝ) - (X n j₁ (τ n (level n) + k n) : ℝ) := by
    unfold spreadS
    rw [hmax, hmin]
    push_cast
    ring
  have hdiff : (X n i₁ (τ n (level n) + k n) : ℝ) - (X n j₁ (τ n (level n) + k n) : ℝ)
      = (scale n : ℝ) * (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i₁ (k n)
          - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j₁ (k n)) := by
    unfold scaledPosition
    field_simp
    ring
  have hbound : scaledPosition (X n) (level n) (τ n (level n)) (scale n) i₁ (k n)
      - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j₁ (k n)
      ≤ b / 8 + 2 * (c / (scale n : ℝ)) + b / 8 := by
    have hA := abs_le.mp h1
    have hB := abs_le.mp h2
    linarith
  rw [hspread, hdiff]
  have hstep : (scale n : ℝ) * (scaledPosition (X n) (level n) (τ n (level n)) (scale n) i₁ (k n)
      - scaledPosition (X n) (level n) (τ n (level n)) (scale n) j₁ (k n))
      ≤ (scale n : ℝ) * (b / 8 + 2 * (c / (scale n : ℝ)) + b / 8) :=
    mul_le_mul_of_nonneg_left hbound hscR.le
  have hsimp : (scale n : ℝ) * (b / 8 + 2 * (c / (scale n : ℝ)) + b / 8) ≤ b * (scale n : ℝ) := by
    have h2c : 2 * c ≤ b / 2 * (scale n : ℝ) := by
      rw [div_le_iff₀ hscR] at hroomn
      linarith
    have hL2 : (scale n : ℝ) * (2 * (c / (scale n : ℝ))) = 2 * c := by
      field_simp
    nlinarith [hscR, h2c, hL2, hb]
  linarith [hstep, hsimp]

/-! ## 2. The canonical knot `floor (s L) + 1` and the sharp `(half)` clause -/

/-- The canonical knot `floor (s L) + 1` sits within `1/L` of the fluid time `s`. -/
theorem knot_floor_add_one_near {scale : ℕ} (hscale : 0 < scale) {s : ℝ} (hs : 0 ≤ s) :
    |((⌊s * (scale : ℝ)⌋₊ + 1 : ℕ) : ℝ) / (scale : ℝ) - s| ≤ 1 / (scale : ℝ) := by
  have hscR : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hscale
  have hx : (0 : ℝ) ≤ s * (scale : ℝ) := mul_nonneg hs hscR.le
  have hfl : ((⌊s * (scale : ℝ)⌋₊ : ℕ) : ℝ) ≤ s * (scale : ℝ) := Nat.floor_le hx
  have hflt : s * (scale : ℝ) < ((⌊s * (scale : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hEq1 : ((⌊s * (scale : ℝ)⌋₊ + 1 : ℕ) : ℝ) / (scale : ℝ) - s
      = (((⌊s * (scale : ℝ)⌋₊ + 1 : ℕ) : ℝ) - s * (scale : ℝ)) / (scale : ℝ) := by
    field_simp
  have hR : (1 / (scale : ℝ)) * (scale : ℝ) = 1 := by field_simp
  rw [hEq1, abs_div, abs_of_pos hscR]
  rw [div_le_iff₀ hscR, hR, abs_le]
  constructor <;> push_cast <;> linarith

/-- **The sharp `(half)` clause from coalescence at ONE fluid time.**

The fluid limit only has to be coincident at the single time `s`: the grid knot
`floor (s L) + 1` is within `1/L` of it, and `1`-Lipschitz continuity of the limit supplies the
`o(L)` fluid gap at that knot.  The knot lies in the sharp subwindow because
`64 ceil(C) <= s` (lower end) and `s + 1 <= B <= T` together with the record-advance lower bound
`tau_r + B L <= tau_{r+BL}` (upper end). -/
theorem halving_eventually_of_pointwise_coalescence_B
    {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {μ C CT : ℝ} {T B : ℕ} {level scale : ℕ → ℕ} {η : ℕ → ℕ}
    {s : ℝ} {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    (hclauses : ∀ n, LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hC : 0 < C) (hHT : 0 ≤ CT) (hL1 : ∀ n, 1 ≤ scale n)
    (hscaleTop : Tendsto scale atTop atTop)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀) (hnum : ∀ n, Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (η n : ℝ))
    (hη : ∀ n, (η n : ℝ) ≤ HalfEps C (Fintype.card ι) * (scale n : ℝ))
    (hLmin : ∀ n, HalfLmin C (Fintype.card ι) ≤ (scale n : ℝ))
    (hrecT : ∀ n, τ n (level n + B * scale n) ≤ τ n (level n) + T * scale n)
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (rawSample (scale n) (rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i : ι, LipschitzWith 1 (x i))
    (hs0 : 0 ≤ s) (hsT : s ≤ (T : ℝ))
    (hcoin : ∀ i j : ι, x i ⟨s, hs0, hsT⟩ = x j ⟨s, hs0, hsT⟩)
    (hs64 : (64 * Nat.ceil C : ℝ) ≤ s)
    (hsB : s + 1 ≤ (B : ℝ)) (hBT : B ≤ T) :
    ∀ᶠ n in atTop, 2 * defect (X n) (τ n) (level n + B * scale n) ≤ (scale n : ℤ) := by
  have hscale : ∀ n, 0 < scale n := fun n => lt_of_lt_of_le Nat.zero_lt_one (hL1 n)
  have hBT' : (B : ℝ) ≤ (T : ℝ) := by exact_mod_cast hBT
  have hkn : ∀ n, ((⌊s * (scale n : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ s * (scale n : ℝ) + 1 := by
    intro n
    have hscR : (0 : ℝ) ≤ (scale n : ℝ) := by positivity
    have hx : (0 : ℝ) ≤ s * (scale n : ℝ) := mul_nonneg hs0 hscR
    have hfl := Nat.floor_le hx
    push_cast
    linarith
  have hk_near : ∀ n, |((⌊s * (scale n : ℝ)⌋₊ + 1 : ℕ) : ℝ) / (scale n : ℝ) - s|
      ≤ 1 / (scale n : ℝ) := by
    intro n
    exact knot_floor_add_one_near (hscale n) hs0
  have hk_T : ∀ n, ((⌊s * (scale n : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ (T : ℝ) * (scale n : ℝ) := by
    intro n
    have hscR : (0 : ℝ) ≤ (scale n : ℝ) := by positivity
    have hL1' : (1 : ℝ) ≤ (scale n : ℝ) := by exact_mod_cast hL1 n
    have hfl := hkn n
    have h1 : s * (scale n : ℝ) + 1 ≤ (s + 1) * (scale n : ℝ) := by nlinarith
    have h2 : (s + 1) * (scale n : ℝ) ≤ (B : ℝ) * (scale n : ℝ) :=
      mul_le_mul_of_nonneg_right hsB hscR
    have h3 : (B : ℝ) * (scale n : ℝ) ≤ (T : ℝ) * (scale n : ℝ) :=
      mul_le_mul_of_nonneg_right hBT' hscR
    linarith
  -- the entry spread at the canonical knot
  have hentry : ∀ᶠ n in atTop,
      ((spreadS (X n) (Finset.univ : Finset ι)
        (τ n (level n) + (⌊s * (scale n : ℝ)⌋₊ + 1)) : ℤ) : ℝ)
        ≤ HalfEps C (Fintype.card ι) * (scale n : ℝ) :=
    spreadS_at_knot_le_of_single_coincidence hscale hscaleTop (T := (T : ℝ)) (s := s) hs0 hsT
      hconv hlip hcoin (fun n => ⌊s * (scale n : ℝ)⌋₊ + 1) (c := 1) zero_le_one hk_T hk_near
      (HalfEps C (Fintype.card ι)) (HalfEps_pos hC _)
  filter_upwards [hentry] with n hsp
  -- the knot lies in the sharp subwindow
  have hlow : τ n (level n) + 64 * Nat.ceil C * scale n
      ≤ τ n (level n) + (⌊s * (scale n : ℝ)⌋₊ + 1) := by
    have hscR : (0 : ℝ) ≤ (scale n : ℝ) := by positivity
    have h1 : (64 * (Nat.ceil C : ℝ)) * (scale n : ℝ) ≤ s * (scale n : ℝ) :=
      mul_le_mul_of_nonneg_right hs64 hscR
    have hlt : s * (scale n : ℝ) < ((⌊s * (scale n : ℝ)⌋₊ + 1 : ℕ) : ℝ) := by
      have hx : (0 : ℝ) ≤ s * (scale n : ℝ) := mul_nonneg hs0 hscR
      have := Nat.lt_floor_add_one (s * (scale n : ℝ))
      push_cast
      linarith
    have hcast : ((64 * Nat.ceil C * scale n : ℕ) : ℝ)
        = (64 * (Nat.ceil C : ℝ)) * (scale n : ℝ) := by push_cast; ring
    have h3 : ((64 * Nat.ceil C * scale n : ℕ) : ℝ)
        ≤ ((⌊s * (scale n : ℝ)⌋₊ + 1 : ℕ) : ℝ) := by
      rw [hcast]; linarith
    have h4 : (64 * Nat.ceil C * scale n : ℕ) ≤ (⌊s * (scale n : ℝ)⌋₊ + 1) := by
      exact_mod_cast h3
    omega
  have hhigh : τ n (level n) + (⌊s * (scale n : ℝ)⌋₊ + 1) ≤ τ n (level n + B * scale n) := by
    have hscR : (0 : ℝ) ≤ (scale n : ℝ) := by positivity
    have hL1' : (1 : ℝ) ≤ (scale n : ℝ) := by exact_mod_cast hL1 n
    have hfl := hkn n
    have h1 : s * (scale n : ℝ) + 1 ≤ (s + 1) * (scale n : ℝ) := by nlinarith
    have h2 : (s + 1) * (scale n : ℝ) ≤ (B : ℝ) * (scale n : ℝ) :=
      mul_le_mul_of_nonneg_right hsB hscR
    have hcastB : ((B * scale n : ℕ) : ℝ) = (B : ℝ) * (scale n : ℝ) := by push_cast; ring
    have h3 : ((⌊s * (scale n : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ (B * scale n : ℕ) := by
      rw [hcastB]; linarith
    have hkB : (⌊s * (scale n : ℝ)⌋₊ + 1) ≤ B * scale n := by exact_mod_cast h3
    have hadv := tau_advance_lower_mul (hτ n) (hne n) B (scale n) (level n)
    omega
  exact halving_of_coalesce_sharp (X := X n) (τ := τ n) (H := H n) (A := A n)
    (hτ n) (hne n) (hclauses n) (hM n) hC hHT (hdr n) (hr n) (hL1 n) hij (hnum n)
    hT64 (hηdef n) hlow hsp (hη n) (hLmin n) (hrecT n) hhigh

end FluidCoincide
