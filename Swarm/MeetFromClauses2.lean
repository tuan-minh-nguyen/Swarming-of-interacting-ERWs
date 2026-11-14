/-
# The fluid `(meet)` bound from the finite-scale clauses: main theorem

`M2Meet.meet_of_clauses` is the finite-to-fluid step of the source's `(meet)` with the true
sharp constant `2 C ^ 2`:

* inputs: the literal record and step-one paths at every scale, the finite-scale
  `LocalClauses` (which contain `(locmove)`, `(loccoord)`, `(lococc)`) and `MartClause`,
  the sharp lag `eta_n` with `eta_n / L_n → 0`, the uniform convergence of the actual record
  interpolants to the fluid limit `x`, and a strict fluid separation of the group `D` from its
  complement on `[s,t]` with margin `γ > 0`, inside the sharp window `64⌈C⌉₊ ≤ s`;
* output: `t - s ≤ 2 C^2 (sup_D x(s) - sup_{D^c} x(s))`.

The proof composes `gridSep_eventually` (fluid separation → grid `(sep)` at every grid time),
`JoinStep.run_le_sharp` (grid `(sep)` → lattice sharp bound), `spread_add_gap_le_gapStar`
(bookkeeping) and `meet_of_grid_bounds'` (lattice units → fluid).

No probability, no `StickyOn`, no `arrayMeasure`, no velocity.  The separation is the paper's
own input to the `(meet)` computation and is consumed, not proved, here.
-/
import Swarm.MeetFromClauses

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction

namespace M2Meet

open M2B FluidMerge FluidLimit Glue LocalFluid RecordDefect JoinStep

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- `s * L ≤ ⌈L * s⌉` — the ceiling knot dominates the scaled fluid time. -/
theorem mul_self_le_ceil {L s : ℝ} : s * L ≤ ((⌈L * s⌉₊ : ℕ) : ℝ) := by
  rw [mul_comm s L]
  exact Nat.le_ceil (L * s)

/-- **The source's `(meet)` at the sharp constant `2 C^2`, from the finite-scale clauses.**

If at every scale the actual record satisfies the local clauses and the martingale clause
with the same constants, the sharp lag vanishes after normalisation, the record interpolants
converge to `x`, and the fluid positions of `D` stay strictly above those of `Dᶜ` on `[s,t]`
with a positive margin, then the fluid window obeys `t - s ≤ 2 C^2 (sup_D x(s) - sup_{Dᶜ} x(s))`.
-/
theorem meet_of_clauses {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T : ℕ}
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hC : 0 < C) (hHT : 0 ≤ CT)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hL1 : ∀ n, 1 ≤ scale n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (FluidInterpolation.rawSample (scale n) (FluidInterpolation.rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i))
    {D : Finset ι} (hD : D.Nonempty) (hJ : (Finset.univ \ D).Nonempty)
    {s t γ : ℝ} (hs0 : 0 < s) (hs64 : (64 * Nat.ceil C : ℝ) ≤ s)
    (hst : s < t) (htT : t ≤ (T : ℝ)) (hγ : 0 < γ)
    (hsep : ∀ (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) (T : ℝ)), v ∈ Set.Icc s t →
      γ ≤ D.inf' hD (fun i => M2B.fpos x i hv)
        - (Finset.univ \ D).sup' hJ (fun j => M2B.fpos x j hv)) :
    t - s ≤ 2 * C ^ 2 *
      (D.sup' hD (fun i => M2B.fpos x i ⟨hs0.le, le_of_lt (lt_of_lt_of_le hst htT)⟩)
        - (Finset.univ \ D).sup' hJ
            (fun j => M2B.fpos x j ⟨hs0.le, le_of_lt (lt_of_lt_of_le hst htT)⟩)) := by
  classical
  have hsI : s ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨hs0.le, le_of_lt (lt_of_lt_of_le hst htT)⟩
  have hsLratio : Tendsto (fun n => ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) / (scale n : ℝ))
      atTop (𝓝 s) := tendsto_ceil_mul_div hscale hscaleTop hs0.le
  have hsLh : ∀ᶠ n in atTop, ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) ≤ (T : ℝ) * (scale n : ℝ) :=
    ceil_le_horizon hscale hscaleTop hs0.le (lt_of_lt_of_le hst htT)
  have htransfer : ∀ᶠ n in atTop, ∀ k : ℕ,
      s ≤ (k : ℝ) / (scale n : ℝ) → (k : ℝ) / (scale n : ℝ) ≤ t →
      Sep (X n) D (Finset.univ \ D) (τ n (level n) + k) :=
    gridSep_eventually hscale hscaleTop hτ hne hcl hM hC hHT hdr hr hL1 hij hnum hT64 hηdef
      heta hconv hD hJ hs0 hs64 hst.le htT hγ hsep
  have hceil : ∀ᶠ n in atTop, ⌈(scale n : ℝ) * s⌉₊ ≤ ⌊(scale n : ℝ) * t⌋₊ :=
    eventually_ceil_le_floor hscale hscaleTop hs0 hst
  refine meet_of_grid_bounds' (C := C) (CT := CT) hscale hscaleTop hconv hlip hsI hst htT
    hD hJ hsLratio hsLh ?_ heta
  filter_upwards [htransfer, hceil] with n hn hce
  have hL : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hscale n
  have hD' : D ≠ Finset.univ := by
    intro h
    rw [h] at hJ
    exact absurd hJ (by simp)
  -- the sharp window start
  have hrs : τ n (level n) + 64 * Nat.ceil C * scale n
      ≤ τ n (level n) + ⌈(scale n : ℝ) * s⌉₊ := by
    have h1 : (((64 * Nat.ceil C * scale n : ℕ)) : ℝ) ≤ ((⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) := by
      push_cast
      calc (64 * Nat.ceil C : ℝ) * (scale n : ℝ) ≤ s * (scale n : ℝ) :=
            mul_le_mul_of_nonneg_right hs64 hL.le
        _ ≤ ⌈(scale n : ℝ) * s⌉₊ := mul_self_le_ceil
    have h2 : 64 * Nat.ceil C * scale n ≤ ⌈(scale n : ℝ) * s⌉₊ := by exact_mod_cast h1
    omega
  have htn : τ n (level n) + ⌊(scale n : ℝ) * t⌋₊ ≤ τ n (level n) + T * scale n := by
    have h1 : ⌊(scale n : ℝ) * t⌋₊ ≤ T * scale n := by
      have hmono : ⌊(scale n : ℝ) * t⌋₊ ≤ ⌊((T * scale n : ℕ) : ℝ)⌋₊ := by
        refine Nat.floor_mono ?_
        push_cast
        nlinarith [hL.le, htT]
      have h2 : ⌊((T * scale n : ℕ) : ℝ)⌋₊ = T * scale n := Nat.floor_natCast _
      omega
    omega
  -- grid `(sep)` on the finite window
  have hsepAll : ∀ u, τ n (level n) + ⌈(scale n : ℝ) * s⌉₊ ≤ u →
      u < τ n (level n) + ⌊(scale n : ℝ) * t⌋₊ → Sep (X n) D (Finset.univ \ D) u := by
    intro u hu1 hu2
    have hk_le : ⌈(scale n : ℝ) * s⌉₊ ≤ u - τ n (level n) := by omega
    have hk_lt : u - τ n (level n) < ⌊(scale n : ℝ) * t⌋₊ := by omega
    have hk1 : s ≤ ((u - τ n (level n) : ℕ) : ℝ) / (scale n : ℝ) := by
      have h2 : (scale n : ℝ) * s ≤ ((u - τ n (level n) : ℕ) : ℝ) := by
        calc (scale n : ℝ) * s = s * (scale n : ℝ) := by ring
          _ ≤ (⌈(scale n : ℝ) * s⌉₊ : ℝ) := mul_self_le_ceil
          _ ≤ ((u - τ n (level n) : ℕ) : ℝ) := by exact_mod_cast hk_le
      rw [le_div_iff₀ hL]
      linarith
    have hk2 : ((u - τ n (level n) : ℕ) : ℝ) / (scale n : ℝ) ≤ t := by
      have h2 : ((u - τ n (level n) : ℕ) : ℝ) < (scale n : ℝ) * t := by
        calc ((u - τ n (level n) : ℕ) : ℝ) < (⌊(scale n : ℝ) * t⌋₊ : ℝ) := by
              exact_mod_cast hk_lt
          _ ≤ (scale n : ℝ) * t := Nat.floor_le (by nlinarith [hL.le, hs0.le])
      rw [div_le_iff₀ hL]
      linarith
    have hτu : τ n (level n) ≤ u := by omega
    have heq : τ n (level n) + (u - τ n (level n)) = u := Nat.add_sub_cancel' hτu
    rw [← heq]
    exact hn _ hk1 hk2
  have hsepT : Sep (X n) D (Finset.univ \ D) (τ n (level n) + ⌊(scale n : ℝ) * t⌋₊) := by
    have h1 : s ≤ ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) / (scale n : ℝ) := by
      have h2 : (scale n : ℝ) * s ≤ (⌊(scale n : ℝ) * t⌋₊ : ℝ) := by
        calc (scale n : ℝ) * s = s * (scale n : ℝ) := by ring
          _ ≤ (⌈(scale n : ℝ) * s⌉₊ : ℝ) := mul_self_le_ceil
          _ ≤ (⌊(scale n : ℝ) * t⌋₊ : ℝ) := by exact_mod_cast hce
      rw [le_div_iff₀ hL]
      linarith
    have h2 : ((⌊(scale n : ℝ) * t⌋₊ : ℕ) : ℝ) / (scale n : ℝ) ≤ t := by
      have h3 : (⌊(scale n : ℝ) * t⌋₊ : ℝ) ≤ (scale n : ℝ) * t :=
        Nat.floor_le (by nlinarith [hL.le, hs0.le])
      rw [div_le_iff₀ hL]
      linarith
    exact hn _ h1 h2
  -- two cases: the grid window is degenerate, or it is a genuine interval
  by_cases hdeg : ⌊(scale n : ℝ) * t⌋₊ ≤ ⌈(scale n : ℝ) * s⌉₊
  · -- degenerate: the lattice left-hand side vanishes
    have heq : ⌈(scale n : ℝ) * s⌉₊ = ⌊(scale n : ℝ) * t⌋₊ := le_antisymm hce hdeg
    have hsep' : Sep (X n) D (Finset.univ \ D) (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) := by
      rw [heq]
      exact hsepT
    have hgapnn : 0 ≤ gapStar (X n) D (Finset.univ \ D)
        (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) := by
      have hle : sMax (X n) (Finset.univ \ D) (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊)
          ≤ sMaxM (X n) (Finset.univ \ D) (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) :=
        sMax_le hsep'.nonempty_right (fun j hj =>
          le_trans (le_runMaxI (X n) j _) (le_sMaxM hsep'.nonempty_right hj))
      have h1 : ((sMax (X n) (Finset.univ \ D) (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) : ℤ) : ℝ)
          ≤ ((sMaxM (X n) (Finset.univ \ D) (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) : ℤ) : ℝ) := by
        exact_mod_cast hle
      have h2 : ((sMaxM (X n) (Finset.univ \ D) (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) : ℤ) : ℝ) + 2
          ≤ ((sMin (X n) D (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) : ℤ) : ℝ) := by
        have h := hsep'.gap
        have h' : (((sMaxM (X n) (Finset.univ \ D) (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) + 2 : ℤ)) : ℝ)
            ≤ ((sMin (X n) D (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) : ℤ) : ℝ) := by
          exact_mod_cast h
        push_cast at h'
        linarith
      have h3 : ((sMin (X n) D (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) : ℤ) : ℝ)
          ≤ ((sMax (X n) D (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) : ℤ) : ℝ) := by
        exact_mod_cast sMin_le_sMaxX hD
      unfold gapStar
      linarith
    have heta_nn : (0 : ℝ) ≤ (eta n : ℝ) := by
      have h1 : (0 : ℝ) ≤ CT * (scale n : ℝ) ^ (3 / 4 : ℝ) :=
        mul_nonneg hHT (Real.rpow_nonneg (by positivity) _)
      linarith [hηdef n]
    have hzero : ((⌊(scale n : ℝ) * t⌋₊ - ⌈(scale n : ℝ) * s⌉₊ : ℕ) : ℝ) = 0 := by
      rw [Nat.sub_eq_zero_of_le hdeg]
      simp
    rw [hzero]
    have hnn : (0 : ℝ) ≤ 2 * C ^ 2 * (gapStar (X n) D (Finset.univ \ D)
          (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) + (eta n : ℝ))
        + 2 * C * CT * (scale n : ℝ) ^ (3 / 4 : ℝ) := by
      have h1 : (0 : ℝ) ≤ 2 * C ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ gapStar (X n) D (Finset.univ \ D)
          (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) + (eta n : ℝ) := by linarith
      have h3 : (0 : ℝ) ≤ 2 * C * CT := by nlinarith [hC, hHT]
      have h4 : (0 : ℝ) ≤ (scale n : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
      have h5 := mul_nonneg h1 h2
      have h6 := mul_nonneg h3 h4
      linarith
    linarith
  · -- genuine interval: the accepted finite-scale sharp meet bound applies
    have hstn : ⌈(scale n : ℝ) * s⌉₊ < ⌊(scale n : ℝ) * t⌋₊ := lt_of_not_ge hdeg
    have hstn' : τ n (level n) + ⌈(scale n : ℝ) * s⌉₊ < τ n (level n) + ⌊(scale n : ℝ) * t⌋₊ := by
      omega
    have hR := JoinStep.run_le_sharp (X := X n) (τ := τ n) (H := H n) (A := A n)
      (μ := μ) (C := C) (CT := CT) (T := T) (L := scale n) (r := level n) (η := eta n)
      (hτ n) (hne n) (hcl n) (hM n) hC hHT (hdr n) (hr n) (hL1 n) hij (hnum n) hT64 (hηdef n)
      hD hD' hrs hstn' htn hsepAll hsepT
    have hdiff : ((τ n (level n) + ⌊(scale n : ℝ) * t⌋₊)
          - (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) : ℕ)
        = ⌊(scale n : ℝ) * t⌋₊ - ⌈(scale n : ℝ) * s⌉₊ := by omega
    rw [hdiff] at hR
    have hgap := spread_add_gap_le_gapStar (X := X n) (D := D) (J := Finset.univ \ D)
      (n := τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) hD hJ rfl
    have hC2 : (0 : ℝ) ≤ 2 * C ^ 2 := by positivity
    have hmono : 2 * C ^ 2 * (((spreadS (X n) D (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) : ℤ) : ℝ)
        + ((sMin (X n) D (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊)
            - sMaxM (X n) (Finset.univ \ D) (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) : ℤ) : ℝ)
          + (eta n : ℝ))
        ≤ 2 * C ^ 2 * (gapStar (X n) D (Finset.univ \ D)
          (τ n (level n) + ⌈(scale n : ℝ) * s⌉₊) + (eta n : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ hC2
      linarith [hgap]
    linarith [hR, hmono]

end M2Meet
