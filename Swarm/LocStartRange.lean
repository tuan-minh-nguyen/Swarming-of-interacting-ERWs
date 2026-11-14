/-
  **Direction A: the exact start-range of the harmonic `locsum`.**

  `LocSumR1.array_locsum_h` assumes the window start `A` satisfies `L ≤ A`.  Reading the proof
  chain (A4Assembly `array_locsum_window_bound`/`array_locsum_intervals`, R2LocMax
  `array_locmax_bound`, R1ProductArray `array_Pz_sq_sum_bound`, R4Assemble `array_locsum_h`)
  shows the hypothesis `L ≤ A` is used **only** through the truncation depth, and in two
  different strengths:

  * `array_locsum_window_bound`: `array_window_concentration` takes `ellT (xOf L) ≤ A` directly;
    the proof derived it as `le_trans hkL hLA` with `hkL : ellT (xOf L) ≤ L`;
  * `array_locmax_bound` and `array_locsum_h`: the arithmetic on
    `Finset.Ico (A - ellT x) (A + L)` (`Nat.card_Ico`, `omega`) needs `ellT x ≤ A`;
  * `array_Pz_sq_sum_bound`: **not** `ellT x ≤ A` but `2 * ellT x ≤ A`.  Its window starts at
    `A - ellT x` and `LocSumR1.lintegral_Pz_sq_sum` is only available on sites of depth `≥ ellT`,
    so every site of `[A-ellT x, A+L)` needs `ellT x ≤ y`, i.e. `2 * ellT x ≤ A`.
    (`R3Array.array_Pz_low_density` already states its own hypothesis as `ellT (xOf L) ≤ A`.)

  This file re-proves the five statements with `ellT (xOf L) ≤ A` (resp. `2 * ellT (xOf L) ≤ A`)
  in place of `L ≤ A`, with literally the same constants and the same probability
  `exp(-c L^{1/16})`, and then applies it to the paper's record window
  `[r-(T+2)L, r+(T+2)L)`.  Consequently the side condition `r ≥ (3T+6)L` of
  `Loccoord.loccoord_full_window` is replaced by
  `2⌈((2T+4)L)^{1/16}⌉ + (T+2)L ≤ r`, which under the paper's `r ≥ (T+3)L` is the purely
  arithmetic requirement `2⌈((2T+4)L)^{1/16}⌉ ≤ L` (Proposition `loccoord_full_window_paper`),
  i.e. `(2T+4)·4^16 ≤ L^15` (Proposition `loccoord_full_window_concrete`).
  `array_locsum_h_of_le` recovers `LocSumR1.array_locsum_h` verbatim from the extension, so the
  new hypothesis is a genuine relaxation (and `locsum_start_strict` shows it is strict).
  No `sorry`, no axioms beyond `propext, Classical.choice, Quot.sound`.
-/
import Swarm.R4Assemble
import Swarm.LocCoordRange

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace LocSumAct

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform

/-- **The window bound on the actual array.**  For `C > M` there is `L₀` such that for every
`L ≥ L₀` and every window start `A ≥ L`, the probability that some walker has some bad block
among the `⌊L/β⌋+1` blocks covering `[A, A+L)` is at most `exp(-((C-M)²/10368)·L^{1/16})`. -/
theorem array_locsum_window_bound_start {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {C : ℝ} (hCM : LocSum.Mb p (qOf p m) < C) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, ellT (xOf L) ≤ A →
      arrayMeasure N {U : Array N |
          WindowBad p m (nT (xOf L)) (ellT (xOf L)) A (numT L (xOf L)) C U}
        ≤ ENNReal.ofReal
            (Real.exp (-((C - LocSum.Mb p (qOf p m)) ^ 2 / 10368) * xOf L)) := by
  set D := C - LocSum.Mb p (qOf p m) with hDdef
  have hD : 0 < D := by rw [hDdef]; linarith
  have hD0 : 0 < D ^ 2 / 5184 := by positivity
  have hC20 : (0 : ℝ) ≤ 20 * (N : ℝ) := by positivity
  have hev : ∀ᶠ L : ℕ in atTop,
      20 * (N : ℝ) * (xOf L) ^ 11 * Real.exp (-(D ^ 2 / 5184) * xOf L)
        ≤ Real.exp (-((D ^ 2 / 5184) / 2) * xOf L) :=
    xOf_tendsto.eventually
      (eventually_poly_mul_exp_le (C := 20 * (N : ℝ)) (c := D ^ 2 / 5184) hC20 hD0)
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hev
  refine ⟨max L₁ (2 ^ 16), ?_⟩
  intro L hL A hLA
  have hLbig : 2 ^ 16 ≤ L := le_trans (le_max_right _ _) hL
  have hLge : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 1 ≤ L := by norm_num at hLbig ⊢; linarith
  have hx1 : 1 ≤ xOf L := one_le_xOf hLpos
  have hx2 : 2 ≤ xOf L := by
    have : (2 : ℝ) ^ 16 ≤ (L : ℝ) := by
      have : ((2 : ℕ) : ℝ) ^ 16 ≤ (L : ℝ) := by exact_mod_cast hLbig
      simpa using this
    rw [xOf]
    calc (2 : ℝ) = (2 ^ 16 : ℝ) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast (2:ℝ) 16, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
          norm_num
      _ ≤ (L : ℝ) ^ (1 / 16 : ℝ) := by
          apply Real.rpow_le_rpow (by norm_num) this (by norm_num)
  have hxe : (xOf L) ^ 16 = (L : ℝ) := xOf_pow L
  have hkx : ((ellT (xOf L) : ℕ) : ℝ) ≤ 2 * xOf L := ellT_le_two hx1
  have hkL : ellT (xOf L) ≤ L := by
    have h1 : ((ellT (xOf L) : ℕ) : ℝ) ≤ 2 * xOf L := hkx
    have h2 : 2 * xOf L ≤ xOf L ^ 16 := two_mul_le_pow hx2
    have h3 : ((ellT (xOf L) : ℕ) : ℝ) ≤ (L : ℝ) := by rw [← hxe]; linarith
    exact_mod_cast h3
  have hk1 : 1 ≤ ellT (xOf L) := ellT_one_le hx1
  -- the transport + union bound
  have hmain := array_window_concentration (N := N) hp1 hp2 m (nT (xOf L)) (ellT (xOf L)) A
    (numT L (xOf L)) hk1 hLA hCM.le
  refine hmain.trans ?_
  -- the exponent comparison
  have hExpLower := exp_arg_lower (x := xOf L) (D := D) hx1 hD.le
  -- the numeric comparison
  have hTle : ((numT L (xOf L) : ℕ) : ℝ) ≤ 8 * xOf L ^ 10 + 1 := by
    have h := numT_le (L := L) (x := xOf L) hx1
    have hx6 : (0 : ℝ) < xOf L ^ 6 := by positivity
    have h1 : 8 * (L : ℝ) / xOf L ^ 6 = 8 * xOf L ^ 10 := by
      rw [← hxe]
      field_simp
    linarith
  have hmul : (8 * xOf L ^ 10 + 1) * ((N : ℝ) * (2 * xOf L))
      ≤ 20 * (N : ℝ) * xOf L ^ 11 := by
    have hx10 : (1 : ℝ) ≤ xOf L ^ 10 := one_le_pow₀ hx1
    have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hxm : (0 : ℝ) ≤ xOf L := by linarith
    have heq : (8 * xOf L ^ 10 + 1) * ((N : ℝ) * (2 * xOf L))
        = (N : ℝ) * (16 * (xOf L ^ 10 * xOf L) + 2 * xOf L) := by ring
    have hx11' : xOf L ^ 11 = xOf L ^ 10 * xOf L := pow_succ _ _
    have hle : 16 * (xOf L ^ 10 * xOf L) + 2 * xOf L ≤ 20 * (xOf L ^ 10 * xOf L) := by
      nlinarith
    rw [heq, hx11']
    calc (N : ℝ) * (16 * (xOf L ^ 10 * xOf L) + 2 * xOf L)
        ≤ (N : ℝ) * (20 * (xOf L ^ 10 * xOf L)) := mul_le_mul_of_nonneg_left hle hN
      _ = 20 * (N : ℝ) * (xOf L ^ 10 * xOf L) := by ring
  -- assemble in `ℝ≥0∞`
  have hexpLe' : Real.exp (-(↑(nT (xOf L)) * D) ^ 2
        / (2 * ↑(∑ _i : Fin (nT (xOf L)), LocSum.subGnn (ellT (xOf L)))))
      ≤ Real.exp (-(D ^ 2 / 5184) * xOf L) := by
    apply Real.exp_le_exp.mpr
    have h1 : -(D ^ 2 / 5184) * xOf L = -(D ^ 2 * xOf L / 5184) := by ring
    rw [h1, neg_div]
    linarith [hExpLower]
  have hstep : (numT L (xOf L) : ℝ≥0∞) * ((N : ℝ≥0∞) * ((ellT (xOf L) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(↑(nT (xOf L)) * D) ^ 2
          / (2 * ↑(∑ _i : Fin (nT (xOf L)), LocSum.subGnn (ellT (xOf L))))))))
      ≤ ENNReal.ofReal (Real.exp (-((D ^ 2 / 5184) / 2) * xOf L)) := by
    have hmerge : (numT L (xOf L) : ℝ≥0∞) * ((N : ℝ≥0∞) * ((ellT (xOf L) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(↑(nT (xOf L)) * D) ^ 2
          / (2 * ↑(∑ _i : Fin (nT (xOf L)), LocSum.subGnn (ellT (xOf L))))))))
        = ENNReal.ofReal (((numT L (xOf L) : ℕ) : ℝ) * (N : ℝ) * ((ellT (xOf L) : ℕ) : ℝ)
            * Real.exp (-(↑(nT (xOf L)) * D) ^ 2
              / (2 * ↑(∑ _i : Fin (nT (xOf L)), LocSum.subGnn (ellT (xOf L)))))) := by
      rw [← ENNReal.ofReal_natCast (numT L (xOf L)), ← ENNReal.ofReal_natCast N,
        ← ENNReal.ofReal_natCast (ellT (xOf L))]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [hmerge]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : (0 : ℝ) < Real.exp (-(↑(nT (xOf L)) * D) ^ 2
        / (2 * ↑(∑ _i : Fin (nT (xOf L)), LocSum.subGnn (ellT (xOf L))))) := Real.exp_pos _
    have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hfac : ((numT L (xOf L) : ℕ) : ℝ) * (N : ℝ) * ((ellT (xOf L) : ℕ) : ℝ)
        ≤ (8 * xOf L ^ 10 + 1) * ((N : ℝ) * (2 * xOf L)) := by
      have h1 : ((numT L (xOf L) : ℕ) : ℝ) * (N : ℝ) ≤ (8 * xOf L ^ 10 + 1) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hTle hN
      have hNN : (0 : ℝ) ≤ (8 * xOf L ^ 10 + 1) * (N : ℝ) := by positivity
      have h2 : ((numT L (xOf L) : ℕ) : ℝ) * (N : ℝ) * ((ellT (xOf L) : ℕ) : ℝ)
          ≤ (8 * xOf L ^ 10 + 1) * (N : ℝ) * (2 * xOf L) :=
        mul_le_mul h1 hkx (by positivity) hNN
      calc ((numT L (xOf L) : ℕ) : ℝ) * (N : ℝ) * ((ellT (xOf L) : ℕ) : ℝ)
          ≤ (8 * xOf L ^ 10 + 1) * (N : ℝ) * (2 * xOf L) := h2
        _ = (8 * xOf L ^ 10 + 1) * ((N : ℝ) * (2 * xOf L)) := by ring
    calc ((numT L (xOf L) : ℕ) : ℝ) * (N : ℝ) * ((ellT (xOf L) : ℕ) : ℝ)
          * Real.exp (-(↑(nT (xOf L)) * D) ^ 2
              / (2 * ↑(∑ _i : Fin (nT (xOf L)), LocSum.subGnn (ellT (xOf L)))))
        ≤ (8 * xOf L ^ 10 + 1) * ((N : ℝ) * (2 * xOf L))
            * Real.exp (-(D ^ 2 / 5184) * xOf L) :=
          mul_le_mul hfac hexpLe' hpos.le (by positivity)
      _ ≤ 20 * (N : ℝ) * xOf L ^ 11 * Real.exp (-(D ^ 2 / 5184) * xOf L) :=
          mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
      _ ≤ Real.exp (-((D ^ 2 / 5184) / 2) * xOf L) := hL₁ L hLge
  -- final rewriting of the constant
  have heqfin : Real.exp (-((D ^ 2 / 5184) / 2) * xOf L)
      = Real.exp (-((C - LocSum.Mb p (qOf p m)) ^ 2 / 10368) * xOf L) := by
    rw [hDdef]
    have hc : (C - LocSum.Mb p (qOf p m)) ^ 2 / 5184 / 2
        = (C - LocSum.Mb p (qOf p m)) ^ 2 / 10368 := by ring
    rw [hc]
  rw [heqfin] at hstep
  exact hstep

/-- **The paper's `(locsum)` on the actual array, for the truncated potential.**  Outside an
event of probability at most `exp(-((C-M)²/10368)·L^{1/16})`, *every* walker's truncated
potential `h^*_{j,ℓ} = Q p ℓ` satisfies

    Σ_{x ∈ [a0,b0)} (h^*_{j,ℓ}(x))² ≤ C (b0 - a0) + 2 C β

for every interval `[a0,b0) ⊆ [A, A+L)`, where `ℓ = ⌈L^{1/16}⌉` and `β = ⌈L^{5/16}/8⌉·ℓ`. -/
theorem array_locsum_intervals_start {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {C : ℝ} (hC1 : 1 ≤ C) (hCM : LocSum.Mb p (qOf p m) < C) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, ellT (xOf L) ≤ A → ∀ U : Array N,
      U ∉ {U : Array N | WindowBad p m (nT (xOf L)) (ellT (xOf L)) A (numT L (xOf L)) C U} →
      ∀ j : Fin N, ∀ a0 b0 : ℕ, A ≤ a0 → b0 ≤ A + L → a0 ≤ b0 →
        ∑ x ∈ Finset.Ico a0 b0, (LocSum.Q p (ellT (xOf L)) x (siteMarks p m U j)) ^ 2
          ≤ C * ((b0 : ℝ) - (a0 : ℝ)) + 2 * C * (betaT (xOf L)) := by
  obtain ⟨L₀, hL₀⟩ := array_locsum_window_bound_start (N := N) hp1 hp2 m hCM
  refine ⟨max L₀ (2 ^ 16), ?_⟩
  intro L hL A hLA U hU j a0 b0 ha hb hab
  have hLge : 2 ^ 16 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 1 ≤ L := by norm_num at hLge ⊢; linarith
  have hx1 : 1 ≤ xOf L := one_le_xOf hLpos
  have hx2 : 2 ≤ xOf L := by
    have h216 : ((2 : ℕ) : ℝ) ^ 16 ≤ (L : ℝ) := by exact_mod_cast hLge
    rw [xOf]
    calc (2 : ℝ) = (2 ^ 16 : ℝ) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast (2:ℝ) 16, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
          norm_num
      _ ≤ (L : ℝ) ^ (1 / 16 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (by simpa using h216) (by norm_num)
  have hk1 : 1 ≤ ellT (xOf L) := ellT_one_le hx1
  have hβge : (1 : ℝ) ≤ (betaT (xOf L) : ℝ) := by
    have h := betaT_lower hx1
    have hx6 : (8 : ℝ) ≤ xOf L ^ 6 := by
      have h2 : (2:ℝ) ^ 6 ≤ xOf L ^ 6 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hx2 6
      norm_num at h2 ⊢
      linarith
    linarith
  -- the blocks of the partition, in `Ico` form
  have hblocks : ∀ t, t < numT L (xOf L) →
      ∑ y ∈ Finset.Ico (A + t * betaT (xOf L)) (A + (t + 1) * betaT (xOf L)),
        (LocSum.Q p (ellT (xOf L)) y (siteMarks p m U j)) ^ 2 ≤ C * (betaT (xOf L)) := by
    intro t ht
    have hnotbad : ¬ BlockBad p m (nT (xOf L)) (ellT (xOf L))
        (A + t * (nT (xOf L) * ellT (xOf L))) C U j := fun hbad => hU ⟨j, ⟨t, ht⟩, hbad⟩
    have hlt := not_le.mp hnotbad
    have h1 : A + t * (nT (xOf L) * ellT (xOf L)) = A + t * betaT (xOf L) := by rw [betaT]
    rw [h1] at hlt
    rw [sum_fin_residue (fun y => (LocSum.Q p (ellT (xOf L)) y (siteMarks p m U j)) ^ 2)
      (A + t * betaT (xOf L)) (ellT (xOf L)) (nT (xOf L))] at hlt
    have h3 : A + t * betaT (xOf L) + nT (xOf L) * ellT (xOf L)
        = A + (t + 1) * betaT (xOf L) := by
      rw [betaT]; ring
    rw [h3] at hlt
    have h4 : C * ((nT (xOf L) : ℝ) * (ellT (xOf L) : ℝ)) = C * (betaT (xOf L) : ℝ) := by
      rw [betaT]; push_cast; ring
    rw [h4] at hlt
    exact le_of_lt hlt
  have hTL : L ≤ numT L (xOf L) * betaT (xOf L) := by
    have hβpos : 0 < betaT (xOf L) := by
      have h : (0 : ℝ) < (betaT (xOf L) : ℝ) := by linarith
      exact_mod_cast h
    have h1 : L = betaT (xOf L) * (L / betaT (xOf L)) + L % betaT (xOf L) :=
      (Nat.div_add_mod L _).symm
    have h2 : L % betaT (xOf L) < betaT (xOf L) := Nat.mod_lt _ hβpos
    have h3 : betaT (xOf L) * (L / betaT (xOf L)) = (L / betaT (xOf L)) * betaT (xOf L) :=
      Nat.mul_comm _ _
    show L ≤ (L / betaT (xOf L) + 1) * betaT (xOf L)
    rw [Nat.add_mul, Nat.one_mul]
    omega
  exact interval_bound_of_blocks (f := fun x =>
      (LocSum.Q p (ellT (xOf L)) x (siteMarks p m U j)) ^ 2)
    (show 1 ≤ betaT (xOf L) by exact_mod_cast hβge)
    (by linarith : (0 : ℝ) ≤ C)
    (fun x => by positivity)
    hTL hblocks ha hb hab

end

end LocSumAct

namespace LocSumR1

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct

/-- **The window maximum on the actual interacting array.**  There is `c > 0` (depending only
on `N,m,p`) such that for all large `L` and every window start `A ≥ ellT (xOf L)`, with
`ℓ = ⌈L^{1/16}⌉`,

    P ( ∃ j < N, ∃ y ∈ [A-ℓ, A+L),  L^{1/16} ≤ h_j(y) ) ≤ e^{-c L^{1/16}}.

This is the `(locmax)` input of the paper's `(locsum)` argument, stated for the actual
harmonic functions `h_j` of the one-sided mark rows of the uniform array. -/
theorem array_locmax_bound_start {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, ellT (xOf L) ≤ A →
      arrayMeasure N {U : Array N | ∃ j : Fin N,
          ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
            xOf L ≤ hof p (siteMarks p m U j) y}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  obtain ⟨θ, hθ, C, hCpos, hCraw⟩ := exists_exp_moment_hof (p := p) hp1 hp2 hm
  have hp0 : 0 < p := by linarith
  have hC : ∀ x : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * hof p ω x))
      ∂(markMeasure (boolMeasure (qOf p m))) ≤ ENNReal.ofReal C := fun x => hCraw x
  have hCnn : (0 : ℝ) ≤ C := hCpos.le
  -- absorption of the union factor
  have hpoly := eventually_poly_mul_exp_le (C := 3 * (N : ℝ) * C) (c := θ)
    (by positivity) hθ 16
  have hev : ∀ᶠ L : ℕ in atTop, (3 * (N : ℝ) * C) * (xOf L) ^ 16 * Real.exp (-θ * xOf L)
      ≤ Real.exp (-(θ / 2) * xOf L) := xOf_tendsto.eventually hpoly
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hev
  refine ⟨θ / 2, by linarith, max L₁ (2 ^ 16), ?_⟩
  intro L hL A hA
  have hLge : 2 ^ 16 ≤ L := le_trans (le_max_right _ _) hL
  have hLge1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 1 ≤ L := by norm_num at hLge ⊢; linarith
  set x := xOf L with hxdef
  have hx1 : 1 ≤ x := one_le_xOf hLpos
  have hx2 : 2 ≤ x := by
    have h216 : ((2 : ℕ) : ℝ) ^ 16 ≤ (L : ℝ) := by exact_mod_cast hLge
    rw [hxdef, xOf]
    calc (2 : ℝ) = (2 ^ 16 : ℝ) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
      _ ≤ (L : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by norm_num) (by simpa using h216)
          (by norm_num)
  have hxe : x ^ 16 = (L : ℝ) := xOf_pow L
  have hℓ2 : ((ellT x : ℕ) : ℝ) ≤ 2 * x := ellT_le_two hx1
  have hℓL : ellT x ≤ L := by
    have h2 : 2 * x ≤ x ^ 16 := by
      have h1 : (2 : ℝ) ^ 15 ≤ x ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
      have h3 : x ^ 16 = x * x ^ 15 := by ring
      nlinarith
    have : ((ellT x : ℕ) : ℝ) ≤ (L : ℝ) := by rw [← hxe]; linarith
    exact_mod_cast this
  have hℓA : ellT x ≤ A := by omega
  -- the per-walker row bound
  have hrow : ∀ j : Fin N, arrayMeasure N {U : Array N | ∃ y ∈ Finset.Ico (A - ellT x) (A + L),
      x ≤ hof p (siteMarks p m U j) y}
      ≤ ((Finset.Ico (A - ellT x) (A + L)).card : ℝ≥0∞)
        * ENNReal.ofReal (C * Real.exp (-(θ * x))) := by
    intro j
    have hmp := measurePreserving_siteMarks (N := N) hp0 hp2 m j
    have hmeas := measurableSet_hof_exists (p := p) (ne_of_gt hp0) (Finset.Ico (A - ellT x) (A + L)) x
    have heq : {U : Array N | ∃ y ∈ Finset.Ico (A - ellT x) (A + L),
        x ≤ hof p (siteMarks p m U j) y}
        = (fun U : Array N => siteMarks p m U j) ⁻¹'
            {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - ellT x) (A + L), x ≤ hof p ω y} := rfl
    rw [heq]
    calc arrayMeasure N ((fun U : Array N => siteMarks p m U j) ⁻¹'
          {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - ellT x) (A + L), x ≤ hof p ω y})
        = (Measure.map (fun U : Array N => siteMarks p m U j) (arrayMeasure N))
            {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - ellT x) (A + L), x ≤ hof p ω y} := by
          rw [Measure.map_apply (measurable_siteMarks hp0 hp2 m j) hmeas]
      _ = markMeasure (boolMeasure (qOf p m))
            {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - ellT x) (A + L), x ≤ hof p ω y} :=
          congrArg (fun ν : Measure (ℕ → Bool) =>
            ν {ω : ℕ → Bool | ∃ y ∈ Finset.Ico (A - ellT x) (A + L), x ≤ hof p ω y}) hmp.map_eq
      _ ≤ _ :=
          markMeasure_exists_site_tail hθ hCnn hC (ne_of_gt hp0)
            (Finset.Ico (A - ellT x) (A + L)) x
  -- the union over the walkers
  have hset : {U : Array N | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - ellT x) (A + L),
        x ≤ hof p (siteMarks p m U j) y}
      = ⋃ j : Fin N, {U : Array N | ∃ y ∈ Finset.Ico (A - ellT x) (A + L),
          x ≤ hof p (siteMarks p m U j) y} := by
    ext U
    simp
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hrow j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the numerical absorption
  have hcardval : (Finset.Ico (A - ellT x) (A + L)).card = L + ellT x := by
    rw [Nat.card_Ico]
    omega
  have hcardle : (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ) ≤ 2 * x ^ 16 := by
    rw [hcardval]
    have h1 : ((L : ℝ) + (ellT x : ℕ)) ≤ x ^ 16 + 2 * x := by
      have : (L : ℝ) = x ^ 16 := hxe.symm
      linarith
    have h2 : 2 * x ≤ x ^ 16 := by
      have h3 : (2 : ℝ) ^ 15 ≤ x ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
      have h4 : x ^ 16 = x * x ^ 15 := by ring
      nlinarith
    push_cast
    linarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hx16 : (0 : ℝ) ≤ x ^ 16 := by positivity
  have hexpnn : (0 : ℝ) ≤ Real.exp (-(θ * x)) := (Real.exp_pos _).le
  have hmono : (N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
      * (C * Real.exp (-(θ * x)))
      ≤ (3 * (N : ℝ) * C) * x ^ 16 * Real.exp (-(θ * x)) := by
    have hstep : (N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ) * C
        ≤ (3 * (N : ℝ) * C) * x ^ 16 := by
      have h1 : (N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ) * C
          ≤ (N : ℝ) * (2 * x ^ 16) * C := by
        refine mul_le_mul_of_nonneg_right ?_ hCnn
        exact mul_le_mul_of_nonneg_left hcardle hNnn
      have h2 : (N : ℝ) * (2 * x ^ 16) * C ≤ (3 * (N : ℝ) * C) * x ^ 16 := by
        have hprod : (0 : ℝ) ≤ (N : ℝ) * C * x ^ 16 := by positivity
        nlinarith [hprod]
      linarith
    calc (N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
          * (C * Real.exp (-(θ * x)))
        = ((N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ) * C)
            * Real.exp (-(θ * x)) := by ring
      _ ≤ ((3 * (N : ℝ) * C) * x ^ 16) * Real.exp (-(θ * x)) :=
          mul_le_mul_of_nonneg_right hstep hexpnn
      _ = (3 * (N : ℝ) * C) * x ^ 16 * Real.exp (-(θ * x)) := by ring
  have hpolyL : (3 * (N : ℝ) * C) * x ^ 16 * Real.exp (-(θ * x))
      ≤ Real.exp (-(θ / 2) * x) := by
    simpa [hxdef] using hL₁ L hLge1
  have hfinal : (N : ℝ) * (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
      * (C * Real.exp (-(θ * x))) ≤ Real.exp (-(θ / 2) * x) := le_trans hmono hpolyL
  rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_natCast
    (Finset.Ico (A - ellT x) (A + L)).card]
  refine ofReal_mul_three_le hNnn (by positivity) (mul_nonneg hCnn hexpnn) ?_
  rw [← mul_assoc]
  exact hfinal

/-- **The window sum event on the actual array.** -/
theorem array_Pz_sq_sum_bound_start {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, 2 * ellT (xOf L) ≤ A →
      arrayMeasure N {U : Array N | ∃ j : Fin N,
          xOf L ≤ ∑ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
            (LocSum.Pz p y (ellT (xOf L)) (siteMarks p m U j)) ^ 2}
        ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < qOf p m := by unfold qOf; positivity
  have hq1 : qOf p m ≤ 1 := by
    unfold qOf; exact pow_le_one₀ (by linarith) (by linarith)
  have hq1' : qOf p m < 1 := by
    unfold qOf
    refine pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have hb0 : 0 ≤ LocSum.bC p (qOf p m) := LocSum.bC_nonneg hp1 hp2 hq0.le hq1
  have hb1 : LocSum.bC p (qOf p m) < 1 := LocSum.bC_lt_one hp1 hp2 hq0
  have hbpos : 0 < LocSum.bC p (qOf p m) := by
    have hq : 0 < 1 - qOf p m := by linarith
    have h2 : 0 ≤ (1 - p) / p := by positivity
    unfold LocSum.bC
    nlinarith [mul_nonneg (le_of_lt hq0) (pow_nonneg h2 2)]
  have hlog : Real.log (LocSum.bC p (qOf p m)) < 0 := Real.log_neg hbpos hb1
  set κ := -Real.log (LocSum.bC p (qOf p m)) with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  -- absorption of the polynomial factor
  have hpoly := eventually_poly_mul_exp_le (C := 2 * (N : ℝ)) (c := κ) (by positivity) hκ 15
  have hev : ∀ᶠ L : ℕ in atTop,
      2 * (N : ℝ) * (xOf L) ^ 15 * Real.exp (-κ * xOf L)
        ≤ Real.exp (-(κ / 2) * xOf L) := xOf_tendsto.eventually hpoly
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hev
  refine ⟨κ / 2, by linarith, max (max L₁ 4) (2 ^ 16), ?_⟩
  intro L hL A hA
  have hLge4 : 4 ≤ L := le_trans (le_trans (le_max_right L₁ 4)
    (le_max_left (max L₁ 4) (2 ^ 16))) hL
  have hLge1 : L₁ ≤ L := le_trans (le_trans (le_max_left L₁ 4)
    (le_max_left (max L₁ 4) (2 ^ 16))) hL
  have hLge : 2 ^ 16 ≤ L := le_trans (le_max_right (max L₁ 4) (2 ^ 16)) hL
  have hLpos : 1 ≤ L := by norm_num at hLge4 ⊢; linarith
  set x := xOf L with hxdef
  have hx1 : 1 ≤ x := one_le_xOf hLpos
  have hx2 : 2 ≤ x := by
    have h216 : ((2 : ℕ) : ℝ) ^ 16 ≤ (L : ℝ) := by exact_mod_cast hLge
    rw [hxdef, xOf]
    calc (2 : ℝ) = (2 ^ 16 : ℝ) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
      _ ≤ (L : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by norm_num) (by simpa using h216)
          (by norm_num)
  have hxe : x ^ 16 = (L : ℝ) := xOf_pow L
  have hℓx : x ≤ (ellT x : ℝ) := le_ellT x
  have hℓ2 : ((ellT x : ℕ) : ℝ) ≤ 2 * x := ellT_le_two hx1
  have hℓL : ellT x ≤ L := by
    have h2 : 2 * x ≤ x ^ 16 := by
      have h1 : (2 : ℝ) ^ 15 ≤ x ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
      have h3 : x ^ 16 = x * x ^ 15 := by ring
      nlinarith
    have : ((ellT x : ℕ) : ℝ) ≤ (L : ℝ) := by rw [← hxe]; linarith
    exact_mod_cast this
  have h2ℓ : 2 * ellT x ≤ L := by
    have h3 : 2 * ((ellT x : ℕ) : ℝ) ≤ 4 * x := by linarith
    have h4 : 4 * x ≤ x ^ 16 := by
      have h5 : (4 : ℝ) ≤ x ^ 15 := by
        have h6 : (2 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx2 2
        have h7 : (2:ℝ) ^ 14 ≤ x ^ 14 := pow_le_pow_left₀ (by norm_num) hx2 14
        have h8 : x ^ 15 = x * x ^ 14 := by ring
        nlinarith
      nlinarith
    have : 2 * ((ellT x : ℕ) : ℝ) ≤ (L : ℝ) := by rw [← hxe]; linarith
    exact_mod_cast this
  have hℓA : ellT x ≤ A := by omega
  -- every site of the window is at depth at least `ellT x`
  have hdepth : ∀ y ∈ Finset.Ico (A - ellT x) (A + L), ellT x ≤ y := by
    intro y hy
    have h1 : A - ellT x ≤ y := (Finset.mem_Ico.mp hy).1
    omega
  -- the per-walker Markov bound
  have hrow : ∀ j : Fin N,
      arrayMeasure N {U : Array N | x ≤ ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          (LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2}
        ≤ ENNReal.ofReal ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
            * (LocSum.bC p (qOf p m)) ^ (ellT x) / x) := by
    intro j
    have hmp := measurePreserving_siteMarks (N := N) hp0 hp2 m j
    have hmeas : Measurable (fun U : Array N =>
        ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          ENNReal.ofReal ((LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2)) :=
      Finset.measurable_sum _ fun y _ =>
        ((LocSum.measurable_Pz p y (ellT x)).comp
          (measurable_siteMarks hp0 hp2 m j)).pow_const 2 |>.ennreal_ofReal
    -- the integral over the array equals the integral over the mark row
    have hfint : Measurable (fun ω : ℕ → Bool => ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
        ENNReal.ofReal ((LocSum.Pz p y (ellT x) ω) ^ 2)) :=
      Finset.measurable_sum _ fun y _ =>
        ((LocSum.measurable_Pz p y (ellT x)).pow_const 2).ennreal_ofReal
    have hrowint : ∫⁻ U, (fun ω : ℕ → Bool => ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          ENNReal.ofReal ((LocSum.Pz p y (ellT x) ω) ^ 2)) (siteMarks p m U j) ∂(arrayMeasure N)
        = ENNReal.ofReal ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
            * (LocSum.bC p (qOf p m)) ^ (ellT x)) := by
      rw [hmp.lintegral_comp hfint]
      exact lintegral_Pz_sq_sum hq0.le hq1 hp1 hp2 _ hdepth
    have hint : ∫⁻ U, (∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          ENNReal.ofReal ((LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2)) ∂(arrayMeasure N)
        = ENNReal.ofReal ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
            * (LocSum.bC p (qOf p m)) ^ (ellT x)) := by
      have hcongr : (∫⁻ U, (∑ y ∈ Finset.Ico (A - ellT x) (A + L),
            ENNReal.ofReal ((LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2)) ∂(arrayMeasure N))
          = ∫⁻ U, (fun ω : ℕ → Bool => ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
              ENNReal.ofReal ((LocSum.Pz p y (ellT x) ω) ^ 2)) (siteMarks p m U j)
              ∂(arrayMeasure N) := rfl
      rw [hcongr, hrowint]
    -- Markov
    have hmk := mul_measure_le_lintegral (μ := arrayMeasure N) hmeas (ENNReal.ofReal x)
    rw [hint] at hmk
    rw [mul_comm] at hmk
    have hxpos : 0 < x := by linarith
    have hxne : ENNReal.ofReal x ≠ 0 := (ENNReal.ofReal_pos.mpr hxpos).ne'
    have hxtop : ENNReal.ofReal x ≠ ⊤ := ENNReal.ofReal_ne_top
    have hkey : arrayMeasure N {U : Array N | ENNReal.ofReal x
        ≤ ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          ENNReal.ofReal ((LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2)}
        ≤ ENNReal.ofReal ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
            * (LocSum.bC p (qOf p m)) ^ (ellT x)) / ENNReal.ofReal x := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hxne) (Or.inl hxtop)]
      exact hmk
    refine le_trans (measure_mono ?_) (hkey.trans (le_of_eq ?_))
    · intro U hU
      simp only [Set.mem_setOf_eq] at hU ⊢
      have hsub : ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          ENNReal.ofReal ((LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2)
          = ENNReal.ofReal (∑ y ∈ Finset.Ico (A - ellT x) (A + L),
              (LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg fun y _ => by positivity).symm
      rw [hsub, ENNReal.ofReal_le_ofReal_iff (by positivity)]
      exact hU
    · rw [← ENNReal.ofReal_div_of_pos hxpos]
  -- union over the walkers
  have hset : {U : Array N | ∃ j : Fin N,
        x ≤ ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          (LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2}
      = ⋃ j : Fin N, {U : Array N | x ≤ ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
          (LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2} := by
    ext U
    simp
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hrow j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- numerical absorption
  have hcardle : (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ) ≤ 2 * x ^ 16 := by
    have hcard : (Finset.Ico (A - ellT x) (A + L)).card = L + ellT x := by
      rw [Nat.card_Ico]; omega
    rw [hcard]
    have h1 : ((L : ℝ) + (ellT x : ℕ)) ≤ x ^ 16 + 2 * x := by
      have h2 : (L : ℝ) = x ^ 16 := hxe.symm
      linarith
    have h3 : 2 * x ≤ x ^ 16 := by
      have h4 : (2 : ℝ) ^ 15 ≤ x ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
      have h5 : x ^ 16 = x * x ^ 15 := by ring
      nlinarith
    push_cast
    linarith
  have hbpow : (LocSum.bC p (qOf p m)) ^ (ellT x) ≤ Real.exp (-(κ * x)) := by
    have h1 : (LocSum.bC p (qOf p m)) ^ (ellT x)
        = Real.exp ((ellT x : ℕ) * Real.log (LocSum.bC p (qOf p m))) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hbpos _)]
    rw [h1]
    refine Real.exp_le_exp.mpr ?_
    have h2 : κ * x ≤ κ * (ellT x : ℕ) := by
      have := hℓx
      nlinarith
    rw [hκdef]
    nlinarith
  -- assemble in `ℝ`
  have hmain : (N : ℝ) * ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
      * (LocSum.bC p (qOf p m)) ^ (ellT x) / x)
      ≤ Real.exp (-(κ / 2) * x) := by
    have hxpos : 0 < x := by linarith
    have h1 : (((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
        * (LocSum.bC p (qOf p m)) ^ (ellT x) / x
        ≤ (2 * x ^ 16) * Real.exp (-(κ * x)) / x := by
      refine div_le_div_of_nonneg_right ?_ hxpos.le
      exact mul_le_mul hcardle hbpow (by positivity) (by positivity)
    have h2 : (2 * x ^ 16) * Real.exp (-(κ * x)) / x = 2 * x ^ 15 * Real.exp (-(κ * x)) := by
      field_simp
    have h3 : (N : ℝ) * ((2 * x ^ 16) * Real.exp (-(κ * x)) / x)
        ≤ Real.exp (-(κ / 2) * x) := by
      rw [h2]
      have h4 : (N : ℝ) * (2 * x ^ 15 * Real.exp (-(κ * x)))
          = 2 * (N : ℝ) * x ^ 15 * Real.exp (-(κ * x)) := by ring
      rw [h4]
      simpa [hxdef] using hL₁ L hLge1
    calc (N : ℝ) * ((((Finset.Ico (A - ellT x) (A + L)).card : ℕ) : ℝ)
          * (LocSum.bC p (qOf p m)) ^ (ellT x) / x)
        ≤ (N : ℝ) * ((2 * x ^ 16) * Real.exp (-(κ * x)) / x) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ Real.exp (-(κ / 2) * x) := h3
  rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hmain

/-- **`(locsum)` for the actual harmonic functions `h_j`.**  For every `C > M = Mb p q` there is
`c > 0` and `L₀` such that for all `L ≥ L₀` and all window starts `A ≥ ellT (xOf L)`: outside one event of
probability at most `e^{-c L^{1/16}}`, every walker `j < N` and every interval
`[a0,b0) ⊆ [A, A+L)` satisfies `Σ_{x∈[a0,b0)} h_j(x)² ≤ 2C(b0-a0) + 6Cβ`. -/
theorem array_locsum_h_start {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C) (hCM : LocSum.Mb p (qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, 2 * ellT (xOf L) ≤ A →
      arrayMeasure N (LsBad N p m C L A) ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) ∧
      (∀ U : Array N, U ∉ LsBad N p m C L A →
        ∀ j : Fin N, ∀ a0 b0 : ℕ, A ≤ a0 → b0 ≤ A + L → a0 ≤ b0 →
          ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
            ≤ 2 * C * ((b0 : ℝ) - (a0 : ℝ)) + 6 * C * ((betaT (xOf L) : ℕ) : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have hCnn : (0 : ℝ) ≤ C := by linarith
  -- the three probabilistic ingredients
  obtain ⟨Lw, hW⟩ := array_locsum_window_bound_start (N := N) (p := p) hp1 hp2 m hCM
  obtain ⟨LQ, hQ⟩ := array_locsum_intervals_start (N := N) (p := p) hp1 hp2 m hC1 hCM
  obtain ⟨c₂, hc₂, L₂, h₂⟩ := array_locmax_bound_start (N := N) (p := p) hp1 hp2 (m := m) hm
  obtain ⟨c₃, hc₃, L₃, h₃⟩ := array_Pz_sq_sum_bound_start (N := N) (p := p) hp1 hp2 (m := m) hm
  set c₁ : ℝ := (C - LocSum.Mb p (qOf p m)) ^ 2 / 10368 with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have : 0 < C - LocSum.Mb p (qOf p m) := by linarith
    positivity
  set cmin : ℝ := min c₁ (min c₂ c₃) with hcmin
  have hcminpos : 0 < cmin := lt_min hc₁ (lt_min hc₂ hc₃)
  have hev : ∀ᶠ L : ℕ in atTop, max (2 : ℝ) (2 * Real.log 3 / cmin) ≤ xOf L :=
    xOf_tendsto.eventually (eventually_ge_atTop _)
  obtain ⟨Lc, hLc⟩ := eventually_atTop.mp hev
  refine ⟨cmin / 2, by linarith, max (max Lw (max LQ (max L₂ (max L₃ Lc)))) (4 ^ 16), ?_⟩
  intro L hL A hA
  have hT1 : max Lw (max LQ (max L₂ (max L₃ Lc))) ≤ L := le_trans (le_max_left _ _) hL
  have hLw : Lw ≤ L := le_trans (le_max_left _ _) hT1
  have hT2 : max LQ (max L₂ (max L₃ Lc)) ≤ L := le_trans (le_max_right _ _) hT1
  have hLQ : LQ ≤ L := le_trans (le_max_left _ _) hT2
  have hT3 : max L₂ (max L₃ Lc) ≤ L := le_trans (le_max_right _ _) hT2
  have hL₂ : L₂ ≤ L := le_trans (le_max_left _ _) hT3
  have hT4 : max L₃ Lc ≤ L := le_trans (le_max_right _ _) hT3
  have hL₃ : L₃ ≤ L := le_trans (le_max_left _ _) hT4
  have hLc' : Lc ≤ L := le_trans (le_max_right _ _) hT4
  have hLbig : 4 ^ 16 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 1 ≤ L := by norm_num at hLbig ⊢; linarith
  set x := xOf L with hxdef
  have hx1 : 1 ≤ x := one_le_xOf hLpos
  have hx4 : 4 ≤ x := by
    have h416 : ((4 : ℕ) : ℝ) ^ 16 ≤ (L : ℝ) := by exact_mod_cast hLbig
    rw [hxdef, xOf]
    calc (4 : ℝ) = (4 ^ 16 : ℝ) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast (4 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
      _ ≤ (L : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by norm_num) (by simpa using h416)
          (by norm_num)
  have hx2 : 2 ≤ x := by linarith
  have hx3 : max (2 : ℝ) (2 * Real.log 3 / cmin) ≤ x := by
    simpa [hxdef] using hLc L hLc'
  have hxe : x ^ 16 = (L : ℝ) := xOf_pow L
  have hℓL : ellT x ≤ L := by
    have h1 : ((ellT x : ℕ) : ℝ) ≤ 2 * x := ellT_le_two hx1
    have h2 : 2 * x ≤ x ^ 16 := by
      have h3 : (2 : ℝ) ^ 15 ≤ x ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
      have h4 : x ^ 16 = x * x ^ 15 := by ring
      nlinarith
    have : ((ellT x : ℕ) : ℝ) ≤ (L : ℝ) := by rw [← hxe]; linarith
    exact_mod_cast this
  have hℓA : ellT x ≤ A := by omega
  have hβge : x ^ 6 / 8 ≤ ((betaT (xOf L) : ℕ) : ℝ) := betaT_lower (le_trans (by norm_num) hx1)
  have hℓA0 : ellT (xOf L) ≤ A := by omega
  -- the probability bound
  have hprob : arrayMeasure N (LsBad N p m C L A) ≤ ENNReal.ofReal (Real.exp (-(cmin / 2) * x)) := by
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add le_rfl (measure_union_le _ _)).trans ?_
    have h1 : arrayMeasure N {U : Array N |
        WindowBad p m (nT (xOf L)) (ellT (xOf L)) A (numT L (xOf L)) C U}
        ≤ ENNReal.ofReal (Real.exp (-c₁ * x)) := by
      exact hW L hLw A hℓA0
    have h2 : arrayMeasure N {U : Array N | ∃ j : Fin N,
        ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L), xOf L ≤ hof p (siteMarks p m U j) y}
        ≤ ENNReal.ofReal (Real.exp (-c₂ * x)) := by
      exact h₂ L hL₂ A hℓA0
    have h3 : arrayMeasure N {U : Array N | ∃ j : Fin N,
        xOf L ≤ ∑ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
          (LocSum.Pz p y (ellT (xOf L)) (siteMarks p m U j)) ^ 2}
        ≤ ENNReal.ofReal (Real.exp (-c₃ * x)) := by
      exact h₃ L hL₃ A hA
    have hc1 : cmin ≤ c₁ := min_le_left _ _
    have hc2 : cmin ≤ c₂ := le_trans (min_le_right _ _) (min_le_left _ _)
    have hc3 : cmin ≤ c₃ := le_trans (min_le_right _ _) (min_le_right _ _)
    have hxnn : 0 ≤ x := by linarith
    have e1 : Real.exp (-c₁ * x) ≤ Real.exp (-cmin * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have e2 : Real.exp (-c₂ * x) ≤ Real.exp (-cmin * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have e3 : Real.exp (-c₃ * x) ≤ Real.exp (-cmin * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    -- absorb the factor `3`
    have h3abs : (3 : ℝ) * Real.exp (-cmin * x) ≤ Real.exp (-(cmin / 2) * x) := by
      have hlog3 : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)
      have hmin : Real.log 3 ≤ cmin * x / 2 := by
        have h1 : 2 * Real.log 3 / cmin ≤ x := le_trans (le_max_right _ _) hx3
        have h2 : 2 * Real.log 3 ≤ x * cmin := by
          rw [div_le_iff₀ hcminpos] at h1
          linarith
        linarith
      calc (3 : ℝ) * Real.exp (-cmin * x)
          = Real.exp (Real.log 3) * Real.exp (-cmin * x) := by rw [hlog3]
        _ = Real.exp (Real.log 3 - cmin * x) := by
            rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-(cmin / 2) * x) := Real.exp_le_exp.mpr (by linarith)
    have hsum3 : ENNReal.ofReal (Real.exp (-c₁ * x)) + ENNReal.ofReal (Real.exp (-c₂ * x))
        + ENNReal.ofReal (Real.exp (-c₃ * x)) ≤ ENNReal.ofReal (Real.exp (-(cmin / 2) * x)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      linarith
    calc arrayMeasure N {U : Array N |
          WindowBad p m (nT (xOf L)) (ellT (xOf L)) A (numT L (xOf L)) C U}
        + (arrayMeasure N {U : Array N | ∃ j : Fin N,
            ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L), xOf L ≤ hof p (siteMarks p m U j) y}
          + arrayMeasure N {U : Array N | ∃ j : Fin N,
            xOf L ≤ ∑ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
              (LocSum.Pz p y (ellT (xOf L)) (siteMarks p m U j)) ^ 2})
        ≤ ENNReal.ofReal (Real.exp (-c₁ * x))
            + (ENNReal.ofReal (Real.exp (-c₂ * x)) + ENNReal.ofReal (Real.exp (-c₃ * x))) := by
          gcongr
      _ = ENNReal.ofReal (Real.exp (-c₁ * x)) + ENNReal.ofReal (Real.exp (-c₂ * x))
            + ENNReal.ofReal (Real.exp (-c₃ * x)) := by ring
      _ ≤ _ := hsum3
  refine ⟨hprob, ?_⟩
  -- the deterministic conclusion
  intro U hU j a0 b0 ha hb hab
  simp only [LsBad, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_le] at hU
  obtain ⟨hblock, hsmall, hsumsmall⟩ := hU
  have hℓa0 : ellT x ≤ a0 := le_trans hℓA ha
  have hQb := hQ L hLQ A hℓA0 U hblock j a0 b0 ha hb hab
  have hQb' : ∑ y ∈ Finset.Ico a0 b0, (LocSum.Q p (ellT (xOf L)) y (siteMarks p m U j)) ^ 2
      ≤ C * ((b0 : ℝ) - (a0 : ℝ)) + 2 * C * ((betaT (xOf L) : ℕ) : ℝ) := hQb
  have hmaxb : ∀ y ∈ Finset.Ico a0 b0, hof p (siteMarks p m U j) (y - ellT x) ≤ x := by
    intro y hy
    have hy1 : a0 ≤ y := (Finset.mem_Ico.mp hy).1
    have hylt : y < b0 := (Finset.mem_Ico.mp hy).2
    have hyge : A - ellT x ≤ y - ellT x :=
      le_trans (Nat.sub_le_sub_right ha (ellT x)) (Nat.sub_le_sub_right hy1 (ellT x))
    have hylt' : y - ellT x < A + L :=
      lt_of_le_of_lt (Nat.sub_le y (ellT x)) (lt_of_lt_of_le hylt hb)
    have hmem : y - ellT x ∈ Finset.Ico (A - ellT (xOf L)) (A + L) :=
      Finset.mem_Ico.mpr ⟨hyge, hylt'⟩
    have hcon : ¬ (xOf L ≤ hof p (siteMarks p m U j) (y - ellT x)) := fun hle =>
      hsmall j (y - ellT x) ⟨hmem, hle⟩
    exact le_of_lt (not_le.mp hcon)
  have hsumsub : ∑ y ∈ Finset.Ico a0 b0, (LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2
      ≤ ∑ y ∈ Finset.Ico (A - ellT x) (A + L),
        (LocSum.Pz p y (ellT x) (siteMarks p m U j)) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro y hy
      simp only [Finset.mem_Ico] at hy ⊢
      omega
    · intro y _ _; positivity
  have hrow := locsum_row_bound hp1 hp2 (siteMarks p m U j) (ℓ := ellT x) (a0 := a0)
    (b0 := b0) (C := C) (β := ((betaT (xOf L) : ℕ) : ℝ)) (u := x) hℓa0 hQb' hmaxb
    (le_trans hsumsub (le_of_lt (hsumsmall j)))
  -- the numerical absorption `4Cβ + 2(1+x)²x ≤ 6Cβ`
  have hβ0 : (0 : ℝ) ≤ ((betaT (xOf L) : ℕ) : ℝ) := by positivity
  have hcorr : 2 * (1 + x) ^ 2 * x ≤ 2 * C * ((betaT (xOf L) : ℕ) : ℝ) := by
    have hu4 : (1 + x) ^ 2 ≤ 4 * x ^ 2 := by nlinarith [hx1]
    have hx3le : 2 * (1 + x) ^ 2 * x ≤ 8 * x ^ 3 := by nlinarith [hu4, hx1]
    have hx3' : 8 * x ^ 3 ≤ 2 * C * (x ^ 6 / 8) := by
      have h32 : (32 : ℝ) ≤ C * x ^ 3 := by
        have hC1' : (1 : ℝ) ≤ C := hC1
        have hx3ge : (32 : ℝ) ≤ x ^ 3 := by nlinarith [hx4]
        nlinarith
      have hx3nn : (0 : ℝ) ≤ x ^ 3 := by positivity
      nlinarith
    calc 2 * (1 + x) ^ 2 * x ≤ 8 * x ^ 3 := hx3le
      _ ≤ 2 * C * (x ^ 6 / 8) := hx3'
      _ ≤ 2 * C * ((betaT (xOf L) : ℕ) : ℝ) := by
          have := hβge
          nlinarith [hCnn]
  calc ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
      ≤ 2 * C * ((b0 : ℝ) - (a0 : ℝ)) + 4 * C * ((betaT (xOf L) : ℕ) : ℝ)
        + 2 * (1 + x) ^ 2 * x := hrow
    _ ≤ 2 * C * ((b0 : ℝ) - (a0 : ℝ)) + 4 * C * ((betaT (xOf L) : ℕ) : ℝ)
        + 2 * C * ((betaT (xOf L) : ℕ) : ℝ) := by linarith [hcorr]
    _ = 2 * C * ((b0 : ℝ) - (a0 : ℝ)) + 6 * C * ((betaT (xOf L) : ℕ) : ℝ) := by ring

end

end LocSumR1

namespace LocSumAct

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform

/-- `2 ⌈L^{1/16}⌉ ≤ L` for `L ≥ 2^16`: the depth of the `Pz` window never exceeds half the
scale.  (This is the arithmetic that `L ≤ A` used to provide for free.) -/
lemma two_mul_ellT_le_self {L : ℕ} (hL : 2 ^ 16 ≤ L) : 2 * ellT (xOf L) ≤ L := by
  have hL1 : 1 ≤ L := by norm_num at hL ⊢; linarith
  have hx1 : 1 ≤ xOf L := one_le_xOf hL1
  have hx0 : (0 : ℝ) ≤ xOf L := by linarith
  have hx2 : 2 ≤ xOf L := by
    have h216 : ((2 : ℕ) : ℝ) ^ 16 ≤ (L : ℝ) := by exact_mod_cast hL
    rw [xOf]
    calc (2 : ℝ) = (2 ^ 16 : ℝ) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
      _ ≤ (L : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by norm_num) (by simpa using h216)
          (by norm_num)
  have h4 : (4 : ℝ) ≤ (xOf L) ^ 15 := by
    have h1 : (2 : ℝ) ^ 15 ≤ (xOf L) ^ 15 := pow_le_pow_left₀ (by norm_num) hx2 15
    norm_num at h1 ⊢
    linarith
  have hxe : (xOf L) ^ 16 = (L : ℝ) := xOf_pow L
  have hsplit : (xOf L) ^ 16 = xOf L * (xOf L) ^ 15 := by ring
  have hstep : 2 * ((ellT (xOf L) : ℕ) : ℝ) ≤ 4 * xOf L := by
    have := ellT_le_two hx1
    linarith
  have hfin : 2 * ((ellT (xOf L) : ℕ) : ℝ) ≤ (L : ℝ) := by
    have h2 : 4 * xOf L ≤ (xOf L) ^ 16 := by
      rw [hsplit]
      nlinarith
    linarith
  exact_mod_cast hfin

/-- **The concrete arithmetic side condition.**  If `(2T+4)·4^16 ≤ L^15` then
`2⌈((2T+4)L)^{1/16}⌉ ≤ L`: the `(locsum)` start condition of
`Loccoord.loccoord_full_window_paper` therefore holds for every `r ≥ (T+3)L` as soon as
`(2T+4)·4^16 ≤ L^15`, i.e. `T ≲ L^15`.  (Before the start-range extension the chain needed
`r ≥ (3T+6)L` with no such arithmetic restriction.) -/
theorem two_mul_ellT_window_le {L T : ℕ} (hL : 1 ≤ L)
    (h : (2 * T + 4) * 4 ^ 16 ≤ L ^ 15) :
    2 * ellT (xOf ((2 * T + 4) * L)) ≤ L := by
  set M : ℕ := (2 * T + 4) * L with hMdef
  have hM1 : 1 ≤ M := by
    have h1 : 1 ≤ 2 * T + 4 := by omega
    calc 1 = 1 * 1 := by norm_num
      _ ≤ (2 * T + 4) * L := Nat.mul_le_mul h1 hL
  have hy1 : 1 ≤ xOf M := one_le_xOf hM1
  have hy0 : (0 : ℝ) ≤ xOf M := by linarith
  have hy16 : (xOf M) ^ 16 = (M : ℝ) := xOf_pow M
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hcast : (((2 * T + 4 : ℕ)) : ℝ) * (4 : ℝ) ^ 16 ≤ (L : ℝ) ^ 15 := by
    exact_mod_cast h
  have hkey : (4 * xOf M) ^ 16 ≤ (L : ℝ) ^ 16 := by
    have h1 : (4 * xOf M) ^ 16 = (4 : ℝ) ^ 16 * (xOf M) ^ 16 := by ring
    rw [h1, hy16]
    have h2 : (M : ℝ) = (((2 * T + 4 : ℕ)) : ℝ) * (L : ℝ) := by
      rw [hMdef]; push_cast; ring
    have h3 : (L : ℝ) ^ 16 = (L : ℝ) ^ 15 * (L : ℝ) := by ring
    rw [h2, h3]
    nlinarith [hcast, hL0]
  have h4y : 4 * xOf M ≤ (L : ℝ) :=
    (pow_le_pow_iff_left₀ (by positivity : (0 : ℝ) ≤ 4 * xOf M) hL0
      (by norm_num : (16 : ℕ) ≠ 0)).mp hkey
  have h2ell : 2 * ((ellT (xOf M) : ℕ) : ℝ) ≤ 4 * xOf M := by
    have := ellT_le_two hy1
    linarith
  have hfin : 2 * ((ellT (xOf M) : ℕ) : ℝ) ≤ (L : ℝ) := le_trans h2ell h4y
  exact_mod_cast hfin

end

end LocSumAct

namespace LocSumR1

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct

/-- **The start-range extension recovers the original hypothesis.**  `L ≤ A` implies
`2 ⌈L^{1/16}⌉ ≤ A` (for `L ≥ 2^16`), so `array_locsum_h_start` is a strict generalisation of
`LocSumR1.array_locsum_h`, with the same constants, the same `L₀` up to `2^16` and the same
probability `exp(-c L^{1/16})`. -/
theorem array_locsum_h_of_le {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C) (hCM : LocSum.Mb p (qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, L ≤ A →
      arrayMeasure N (LsBad N p m C L A) ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) ∧
      (∀ U : Array N, U ∉ LsBad N p m C L A →
        ∀ j : Fin N, ∀ a0 b0 : ℕ, A ≤ a0 → b0 ≤ A + L → a0 ≤ b0 →
          ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
            ≤ 2 * C * ((b0 : ℝ) - (a0 : ℝ)) + 6 * C * ((betaT (xOf L) : ℕ) : ℝ)) := by
  obtain ⟨c, hc, L₀, hL⟩ := array_locsum_h_start (N := N) hp1 hp2 hm hC1 hCM
  exact ⟨c, hc, max L₀ (2 ^ 16), fun L hLbig A hLA =>
    hL L (le_trans (le_max_left _ _) hLbig) A
      (le_trans (two_mul_ellT_le_self (le_trans (le_max_right _ _) hLbig)) hLA)⟩

end

end LocSumR1

namespace Loccoord

noncomputable section

variable {N : ℕ}

/-- **(loccoord) on the full record window, with the exact start condition of the `(locsum)`
chain.**  This is `Loccoord.loccoord_full_window` with the side condition `(3T+6)L ≤ r` replaced
by the condition the `(locsum)` proof actually uses, `2⌈((2T+4)L)^{1/16}⌉ ≤ r-(T+2)L`.
(The two `(locsum)` inputs are `LocSumR1.LsBad` at the enlarged window `[r-(T+2)L, r+(T+2)L)` and
`Loccoord.loccoord_range_of_event`.) -/
theorem loccoord_full_window_start {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ,
      2 * LocSumAct.ellT (LocSumAct.xOf ((2 * T + 4) * L)) + (T + 2) * L ≤ r →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L))
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Xmin p m U B hB s).toNat →
      (Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * C + 1) / 2)
            * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 3 * C * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℝ)) := by
  obtain ⟨c, hc, L₀, hL⟩ := LocSumR1.array_locsum_h_start (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, L₀, ?_⟩
  intro L hLbig T r hcond
  have hLw : L₀ ≤ (2 * T + 4) * L := by
    have h1 : 1 ≤ 2 * T + 4 := by omega
    calc L₀ ≤ L := hLbig
      _ = L * 1 := (Nat.mul_one L).symm
      _ ≤ L * (2 * T + 4) := Nat.mul_le_mul_left L h1
      _ = (2 * T + 4) * L := Nat.mul_comm _ _
  have hcond' : 2 * LocSumAct.ellT (LocSumAct.xOf ((2 * T + 4) * L))
      ≤ r - (T + 2) * L := by omega
  obtain ⟨hmeas, hbound⟩ := hL ((2 * T + 4) * L) hLw (r - (T + 2) * L) hcond'
  refine ⟨hmeas, ?_⟩
  intro U hU B hB s t hst hX0 hXmin hRmax
  have h2 : (T + 2) * L ≤ r := by omega
  have hconv : (Rmax p m U B hB t).toNat ≤ r - (T + 2) * L + (2 * T + 4) * L := by
    have heq : r - (T + 2) * L + (2 * T + 4) * L = r + (T + 2) * L := by
      have h1 : (2 * T + 4) * L = (T + 2) * L + (T + 2) * L := by ring
      have h3 : r - (T + 2) * L + (T + 2) * L = r := Nat.sub_add_cancel h2
      calc r - (T + 2) * L + (2 * T + 4) * L
          = r - (T + 2) * L + (T + 2) * L + (T + 2) * L := by rw [h1]; ring
        _ = r + (T + 2) * L := by rw [h3]
    rw [heq]
    exact hRmax
  exact loccoord_range_of_event (p := p) (m := m) (N := N) (le_of_lt hp1) (le_of_lt hp2) U
    (C := C) (Lw := (2 * T + 4) * L) (A := r - (T + 2) * L)
    (β := ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℝ)))
    (by linarith) (by positivity)
    (fun j a0 b0 ha hb hab => hbound U hU j a0 b0 ha hb hab) hB hst hX0 hXmin hconv

/-- **(loccoord) on the full record window at the paper's threshold `r ≥ (T+3)L`.**  The only
extra side condition is the arithmetic one `2⌈((2T+4)L)^{1/16}⌉ ≤ L` (e.g. `T ≤ L^15`), which is
what remains of `L ≤ A` after the start-range extension.  Compare
`Loccoord.loccoord_full_window`, which needs `(3T+6)L ≤ r`. -/
theorem loccoord_full_window_paper {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ, (T + 3) * L ≤ r →
      2 * LocSumAct.ellT (LocSumAct.xOf ((2 * T + 4) * L)) ≤ L →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L))
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Xmin p m U B hB s).toNat →
      (Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * C + 1) / 2)
            * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 3 * C * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℝ)) := by
  obtain ⟨c, hc, L₀, hL⟩ := loccoord_full_window_start (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, L₀, fun L hLbig T r hr hcond => hL L hLbig T r ?_⟩
  have hmul : (T + 3) * L = (T + 2) * L + L := by ring
  omega

/-- **The new start condition is strictly weaker than `L ≤ A`.**  `L = 5`, `A = 4` satisfies
`2⌈L^{1/16}⌉ ≤ A` but not `L ≤ A`: so `LocSumR1.array_locsum_h_start` is not a renaming of
`LocSumR1.array_locsum_h`. -/
theorem locsum_start_strict : ∃ L A : ℕ,
    2 * LocSumAct.ellT (LocSumAct.xOf L) ≤ A ∧ ¬ (L ≤ A) := by
  refine ⟨5, 4, ?_, by norm_num⟩
  have hx2 : LocSumAct.xOf 5 ≤ 2 := by
    rw [LocSumAct.xOf]
    calc (5 : ℝ) ^ (1 / 16 : ℝ) ≤ ((2 : ℝ) ^ 16) ^ (1 / 16 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 2 := by
          rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
  have hℓ : LocSumAct.ellT (LocSumAct.xOf 5) ≤ 2 := Nat.ceil_le.mpr hx2
  omega

end

end Loccoord

namespace Loccoord

noncomputable section

variable {N : ℕ}

/-- **`(loccoord)` on the full record window at the paper's threshold `r ≥ (T+3)L`, with the side
condition in closed arithmetic form.**  Compare `Loccoord.loccoord_full_window` (`(3T+6)L ≤ r`).
The only price is `(2T+4)·4^16 ≤ L^15`, which is what is left of the `(locsum)` hypothesis
`L ≤ A` after `LocSumR1.array_locsum_h_start`. -/
theorem loccoord_full_window_concrete {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ, (T + 3) * L ≤ r →
      (2 * T + 4) * 4 ^ 16 ≤ L ^ 15 →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L))
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Xmin p m U B hB s).toNat →
      (Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * C + 1) / 2)
            * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 3 * C * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℝ)) := by
  obtain ⟨c, hc, L₀, hL⟩ := loccoord_full_window_paper (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ 1, fun L hLbig T r hr hT => ?_⟩
  exact hL L (le_trans (le_max_left _ _) hLbig) T r hr
    (LocSumAct.two_mul_ellT_window_le (le_trans (le_max_right _ _) hLbig) hT)

end

end Loccoord

namespace Loccoord

noncomputable section

variable {N : ℕ}

/-- **`Loccoord.loccoord_full_window` is recovered.**  The hypothesis
`2⌈((2T+4)L)^{1/16}⌉ + (T+2)L ≤ r` of `loccoord_full_window_start` is implied by the old
`(3T+6)L ≤ r` (because `2⌈u⌉ ≤ u^16 = (2T+4)L` for `u = ((2T+4)L)^{1/16} ≥ 1`), so the extension
reproduces the paper's old statement on the enlarged window without renaming or strengthening any
assumption. -/
theorem loccoord_full_window_of_old {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ T r : ℕ, (3 * T + 6) * L ≤ r →
      Swarming.Uniform.arrayMeasure N
          (LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L))
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf ((2 * T + 4) * L))) ∧
      ∀ U : Swarming.Uniform.Array N,
      U ∉ LocSumR1.LsBad N p m C ((2 * T + 4) * L) (r - (T + 2) * L) →
      ∀ (B : Finset (Fin N)) (hB : B.Nonempty), ∀ s t : ℕ, s ≤ t →
      (hX0 : 0 ≤ Xmin p m U B hB s) →
      r - (T + 2) * L ≤ (Xmin p m U B hB s).toNat →
      (Rmax p m U B hB t).toNat ≤ r + (T + 2) * L →
      Swarming.Group.average B (fun k =>
          SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
            - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
        ≤ ((2 * C + 1) / 2)
            * (((Rmax p m U B hB t : ℤ) : ℝ) - ((Xmin p m U B hB s : ℤ) : ℝ))
          + 3 * C * ((LocSumAct.betaT (LocSumAct.xOf ((2 * T + 4) * L)) : ℝ)) := by
  obtain ⟨c, hc, L₀, hL⟩ := loccoord_full_window_start (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, max L₀ (2 ^ 16), fun L hLbig T r hr => hL L ?_ T r ?_⟩
  · exact le_trans (le_max_left _ _) hLbig
  · have hL1 : 1 ≤ L := by
      have := le_trans (le_max_right _ _) hLbig
      norm_num at this ⊢
      linarith
    have hM : 2 ^ 16 ≤ (2 * T + 4) * L := by
      have h1 : 1 ≤ 2 * T + 4 := by omega
      have h2 : (2 : ℕ) ^ 16 ≤ L := le_trans (le_max_right _ _) hLbig
      calc 2 ^ 16 ≤ L := h2
        _ = L * 1 := (Nat.mul_one L).symm
        _ ≤ L * (2 * T + 4) := Nat.mul_le_mul_left L h1
        _ = (2 * T + 4) * L := Nat.mul_comm _ _
    have h3 : 2 * LocSumAct.ellT (LocSumAct.xOf ((2 * T + 4) * L)) ≤ (2 * T + 4) * L :=
      LocSumAct.two_mul_ellT_le_self hM
    have h4 : (2 * T + 4) * L + (T + 2) * L = (3 * T + 6) * L := by ring
    omega

end

end Loccoord
