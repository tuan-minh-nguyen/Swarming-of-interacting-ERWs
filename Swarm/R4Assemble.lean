/-
  **`locsum` for the actual harmonic functions `h_j`: the paper's display `(locsum)`.**

  This file assembles the whole chain on the actual interacting array:

  * `A4Assembly.array_locsum_intervals` — block bound for the truncated potential
    `h^*_{j,ℓ} = LocSum.Q p ℓ` (already verified infrastructure, not redone here);
  * `R2LocMax.array_locmax_bound` — `h_j(y) ≤ L^{1/16}` on the window `[A-ℓ, A+L)`;
  * `R3Array.array_Pz_sq_sum_bound` — `Σ_y Pz(y,ℓ)² ≤ L^{1/16}` on the window;
  * `R1Identity.hof_sq_le_Q_add` — the exact `(hstat)` comparison
    `h_j(x)² ≤ 2 h^*_{j,ℓ}(x)² + 2 Pz(x,ℓ)² (1+h_j(x-ℓ))²`.

  Conclusion: outside one event of probability `≤ e^{-c L^{1/16}}`, *every* walker and *every*
  interval `[a0,b0) ⊆ [A, A+L)` satisfies

      Σ_{x∈[a0,b0)} h_j(x)² ≤ 2C(b0-a0) + 6Cβ,   β = betaT (L^{1/16}) ≈ L^{3/8}/8,

  which is the paper's `(locsum)` with the `C L^{1/2}` remainder improved to `C β` (and with
  `h_j` in place of the truncated potential).  No Poincaré/independence-of-adaptive-coordinates
  input is used: every probabilistic ingredient is a statement about the i.i.d. site-mark rows.
-/
import Swarm.R1ProductArray
import Swarm.A4Assembly
import Swarm.B1Potential

set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open SwarmMarks SwarmLogRatio Swarming.Uniform LocSumAct

namespace LocSumR1

noncomputable section

/-- **The deterministic row comparison.**  If the truncated potential has the block bound, the
harmonic function is at most `u` on the shifted interval, and the squared ratio products have
window sum at most `u`, then the harmonic square sum is `2C(b0-a0) + 4Cβ + 2(1+u)²u`. -/
theorem locsum_row_bound {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) (ω : ℕ → Bool)
    {ℓ a0 b0 : ℕ} {C β u : ℝ} (hℓ : ℓ ≤ a0)
    (hQ : ∑ x ∈ Finset.Ico a0 b0, (LocSum.Q p ℓ x ω) ^ 2
      ≤ C * ((b0 : ℝ) - (a0 : ℝ)) + 2 * C * β)
    (hmax : ∀ x ∈ Finset.Ico a0 b0, hof p ω (x - ℓ) ≤ u)
    (hsum : ∑ x ∈ Finset.Ico a0 b0, (LocSum.Pz p x ℓ ω) ^ 2 ≤ u) :
    ∑ x ∈ Finset.Ico a0 b0, (hof p ω x) ^ 2
      ≤ 2 * C * ((b0 : ℝ) - (a0 : ℝ)) + 4 * C * β + 2 * (1 + u) ^ 2 * u := by
  have hterm : ∀ x ∈ Finset.Ico a0 b0, (hof p ω x) ^ 2
      ≤ 2 * (LocSum.Q p ℓ x ω) ^ 2 + 2 * (LocSum.Pz p x ℓ ω) ^ 2 * (1 + u) ^ 2 := by
    intro x hx
    have hxa : a0 ≤ x := (Finset.mem_Ico.mp hx).1
    have hℓx : ℓ ≤ x := le_trans hℓ hxa
    exact hof_sq_le_Q_add hp1 hp2 ω hℓx (hmax x hx)
  refine (Finset.sum_le_sum hterm).trans ?_
  have h2 : ∑ x ∈ Finset.Ico a0 b0, 2 * (LocSum.Pz p x ℓ ω) ^ 2 * (1 + u) ^ 2
      = (2 * (1 + u) ^ 2) * ∑ x ∈ Finset.Ico a0 b0, (LocSum.Pz p x ℓ ω) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have h2Q : ∑ x ∈ Finset.Ico a0 b0, 2 * (LocSum.Q p ℓ x ω) ^ 2
      = 2 * ∑ x ∈ Finset.Ico a0 b0, (LocSum.Q p ℓ x ω) ^ 2 := by
    rw [Finset.mul_sum]
  rw [Finset.sum_add_distrib, h2Q, h2]
  have h3 : (2 * (1 + u) ^ 2) * (∑ x ∈ Finset.Ico a0 b0, (LocSum.Pz p x ℓ ω) ^ 2)
      ≤ (2 * (1 + u) ^ 2) * u := by
    refine mul_le_mul_of_nonneg_left hsum ?_
    positivity
  linarith

/-- The bad set of the `locsum` assembly: a bad block of the truncated potential, or a large
value of the potential on the window, or a large window sum of the squared ratio products. -/
def LsBad (N : ℕ) (p : ℝ) (m : ℕ) (C : ℝ) (L A : ℕ) : Set (Array N) :=
  {U | WindowBad p m (nT (xOf L)) (ellT (xOf L)) A (numT L (xOf L)) C U} ∪
    ({U | ∃ j : Fin N, ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
        xOf L ≤ hof p (siteMarks p m U j) y} ∪
      {U | ∃ j : Fin N, xOf L ≤ ∑ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L),
        (LocSum.Pz p y (ellT (xOf L)) (siteMarks p m U j)) ^ 2})

/-- **`(locsum)` for the actual harmonic functions `h_j`.**  For every `C > M = Mb p q` there is
`c > 0` and `L₀` such that for all `L ≥ L₀` and all window starts `A ≥ L`: outside one event of
probability at most `e^{-c L^{1/16}}`, every walker `j < N` and every interval
`[a0,b0) ⊆ [A, A+L)` satisfies `Σ_{x∈[a0,b0)} h_j(x)² ≤ 2C(b0-a0) + 6Cβ`. -/
theorem array_locsum_h {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1) {m : ℕ}
    (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C) (hCM : LocSum.Mb p (qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, L ≤ A →
      arrayMeasure N (LsBad N p m C L A) ≤ ENNReal.ofReal (Real.exp (-c * xOf L)) ∧
      (∀ U : Array N, U ∉ LsBad N p m C L A →
        ∀ j : Fin N, ∀ a0 b0 : ℕ, A ≤ a0 → b0 ≤ A + L → a0 ≤ b0 →
          ∑ x ∈ Finset.Ico a0 b0, (hof p (siteMarks p m U j) x) ^ 2
            ≤ 2 * C * ((b0 : ℝ) - (a0 : ℝ)) + 6 * C * ((betaT (xOf L) : ℕ) : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have hCnn : (0 : ℝ) ≤ C := by linarith
  -- the three probabilistic ingredients
  obtain ⟨Lw, hW⟩ := array_locsum_window_bound (N := N) (p := p) hp1 hp2 m hCM
  obtain ⟨LQ, hQ⟩ := array_locsum_intervals (N := N) (p := p) hp1 hp2 m hC1 hCM
  obtain ⟨c₂, hc₂, L₂, h₂⟩ := array_locmax_bound (N := N) (p := p) hp1 hp2 (m := m) hm
  obtain ⟨c₃, hc₃, L₃, h₃⟩ := array_Pz_sq_sum_bound (N := N) (p := p) hp1 hp2 (m := m) hm
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
  have hℓA : ellT x ≤ A := le_trans hℓL hA
  have hβge : x ^ 6 / 8 ≤ ((betaT (xOf L) : ℕ) : ℝ) := betaT_lower (le_trans (by norm_num) hx1)
  -- the probability bound
  have hprob : arrayMeasure N (LsBad N p m C L A) ≤ ENNReal.ofReal (Real.exp (-(cmin / 2) * x)) := by
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add le_rfl (measure_union_le _ _)).trans ?_
    have h1 : arrayMeasure N {U : Array N |
        WindowBad p m (nT (xOf L)) (ellT (xOf L)) A (numT L (xOf L)) C U}
        ≤ ENNReal.ofReal (Real.exp (-c₁ * x)) := by
      exact hW L hLw A hA
    have h2 : arrayMeasure N {U : Array N | ∃ j : Fin N,
        ∃ y ∈ Finset.Ico (A - ellT (xOf L)) (A + L), xOf L ≤ hof p (siteMarks p m U j) y}
        ≤ ENNReal.ofReal (Real.exp (-c₂ * x)) := by
      exact h₂ L hL₂ A hA
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
  have hQb := hQ L hLQ A hA U hblock j a0 b0 ha hb hab
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
