/-
  **`locsum`, layer A4: the actual-array local square-sum estimate at the paper's scale.**

  Combining layers A1–A3: with `ℓ = ⌈L^{1/16}⌉`, `n = ⌈L^{5/16}/8⌉`, `β = n·ℓ` and any fixed
  `C > M`, the probability that some walker has a bad `β`-block inside the window
  `[A, A+L)` (with `L ≤ A`) is at most `exp(-c L^{1/16})` for large `L`, `c = (C-M)²/10368`.
  On the complement every interval `[a0,b0) ⊆ [A, A+L)` has

      Σ_{x ∈ [a0,b0)} (h^*_{j,ℓ}(x))² ≤ C (b0 - a0) + 2 C β,

  i.e. the paper's display `(locsum)` for the truncated potential `h^*_{j,ℓ} = Q p ℓ`.
-/
import Swarm.A3Scale

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace LocSumAct

noncomputable section

open SwarmMarks SwarmLogRatio Swarming.Uniform

/-- For `x ≥ 2`, `2x ≤ x^16`. -/
lemma two_mul_le_pow {x : ℝ} (hx : 2 ≤ x) : 2 * x ≤ x ^ 16 := by
  have h1 : (0 : ℝ) < x := by linarith
  have h2 : (2 : ℝ) ^ 15 ≤ x ^ 15 := by
    apply pow_le_pow_left₀ (by norm_num) hx
  have h3 : x ^ 16 = x * x ^ 15 := by ring
  have h4 : 2 ≤ x ^ 15 := by
    have : (2:ℝ) ≤ 2^15 := by norm_num
    linarith
  nlinarith

/-- **The window bound on the actual array.**  For `C > M` there is `L₀` such that for every
`L ≥ L₀` and every window start `A ≥ L`, the probability that some walker has some bad block
among the `⌊L/β⌋+1` blocks covering `[A, A+L)` is at most `exp(-((C-M)²/10368)·L^{1/16})`. -/
theorem array_locsum_window_bound {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    (m : ℕ) {C : ℝ} (hCM : LocSum.Mb p (qOf p m) < C) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, L ≤ A →
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
    (numT L (xOf L)) hk1 (le_trans hkL hLA) hCM.le
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
theorem array_locsum_intervals {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (m : ℕ)
    {C : ℝ} (hC1 : 1 ≤ C) (hCM : LocSum.Mb p (qOf p m) < C) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, L ≤ A → ∀ U : Array N,
      U ∉ {U : Array N | WindowBad p m (nT (xOf L)) (ellT (xOf L)) A (numT L (xOf L)) C U} →
      ∀ j : Fin N, ∀ a0 b0 : ℕ, A ≤ a0 → b0 ≤ A + L → a0 ≤ b0 →
        ∑ x ∈ Finset.Ico a0 b0, (LocSum.Q p (ellT (xOf L)) x (siteMarks p m U j)) ^ 2
          ≤ C * ((b0 : ℝ) - (a0 : ℝ)) + 2 * C * (betaT (xOf L)) := by
  obtain ⟨L₀, hL₀⟩ := array_locsum_window_bound (N := N) hp1 hp2 m hCM
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
