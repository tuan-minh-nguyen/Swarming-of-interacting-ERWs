import SwarmDiameter.LinearRecordFluid

open Filter Set
open scoped Topology

namespace Swarming.Diameter

open FluidInterpolation FluidLimit RecordDefect

set_option autoImplicit false

/-- A sufficiently small relative error bounds the defect at the later
record by half the initial scale. -/
theorem record_defect_halves_of_linear_clauses
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] (B T : ℕ)
    {C v : ℝ} (hC : 1 ≤ C) (hv : 0 < v) (hT : (B : ℝ) + 2 ≤ v * (T : ℝ))
    (hB : (1 + 2 / v) * (1 + (C + 1)) ^ (Fintype.card ι - 1) - 1 < (B : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, (T + 3) * L ≤ r →
      ∀ (X : ι → ℕ → ℤ) (τ : ℕ → ℕ),
      IsRecord X τ → (∀ i n, |X i (n + 1) - X i n| = 1) → defect X τ r ≤ (L : ℤ) →
      LinearBlockClauses X τ r T L C v (ε * (L : ℝ)) → 2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
  classical
  by_contra hcon
  let ε (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hε₁ (n : ℕ) : ε n ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) n])
  have hseq : ∀ n : ℕ, ∃ L : ℕ, n + 1 ≤ L ∧ ∃ r : ℕ, (T + 3) * L ≤ r ∧
      ∃ (X : ι → ℕ → ℤ) (τ : ℕ → ℕ),
        IsRecord X τ ∧ (∀ i k, |X i (k + 1) - X i k| = 1) ∧ defect X τ r ≤ (L : ℤ) ∧
        LinearBlockClauses X τ r T L C v (ε n * (L : ℝ)) ∧
        (L : ℤ) < 2 * defect X τ (r + B * L) := by
    push Not at hcon
    intro n
    exact hcon (ε n) (hε n) (hε₁ n) (n + 1)
  choose L hLn r hr X τ hrec hNN hd hcl hbad using hseq
  have htime (n : ℕ) : τ n (r n + B * L n) - τ n (r n) ≤ T * L n :=
    (hcl n).advance (hrec n) (hd n) (hε₁ n) hT
  have hs₀T : 2 / v ≤ (T : ℝ) := (div_le_iff₀ hv).mpr (by
    rw [mul_comm]
    exact (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) B)).trans hT)
  have hLtop : Tendsto L atTop atTop :=
    tendsto_atTop_mono (f := fun n : ℕ => n) (g := L) (fun n => by have := hLn n; omega)
      tendsto_id
  have hLpos : ∀ n, 0 < L n := fun n => by have := hLn n; omega
  have hlow : ∀ n, (B : ℝ) ≤ DefectKnot.thetaL (τ n) B (r n) (L n) :=
    fun n => DefectKnot.theta_mem_lower (hrec n) (hNN n) (hLpos n)
  have hup : ∀ n, DefectKnot.thetaL (τ n) B (r n) (L n) ≤ (T : ℝ) :=
    fun n => DefectKnot.theta_mem_upper (htime n) (hLpos n)
  obtain ⟨θ, hθmem, ψ, hψ, hθtend⟩ := isCompact_Icc.tendsto_subseq
    (x := fun n => DefectKnot.thetaL (τ n) B (r n) (L n)) (fun n => ⟨hlow n, hup n⟩)
  obtain ⟨x, φ, hφ, _hxlip, _hxbound, hxconv, _hxstart, _hlarge', _hscale', _hd', _hsample⟩ :=
    FluidInterpolation.exists_record_interpolated_limit_subseq (T + 3) (T : ℝ) (Nat.cast_nonneg T)
      (fun n => X (ψ n)) (fun n => τ (ψ n)) (fun n => r (ψ n)) (fun n => L (ψ n))
      (fun n => hrec (ψ n)) (fun n => hr (ψ n)) (hLtop.comp hψ.tendsto_atTop)
      (fun n => hLpos (ψ n)) (fun n => hd (ψ n)) ⟨0, ⟨le_rfl, Nat.cast_nonneg T⟩⟩ rfl
      (fun n i k => hNN (ψ n) i k)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa only [ε, Nat.cast_succ, Function.comp_def] using tendsto_inv_atTop_zero.comp ht
  have hcoal : ∀ i j : ι,
      x i ⟨θ, (Nat.cast_nonneg B).trans hθmem.1, hθmem.2⟩ =
        x j ⟨θ, (Nat.cast_nonneg B).trans hθmem.1, hθmem.2⟩ := by
    intro i j
    let a (n : ℕ) := ψ (φ n)
    have ha : Tendsto a atTop atTop := hψ.tendsto_atTop.comp hφ.tendsto_atTop
    exact coalesced_at_of_linear_errors
      (scale := fun n => L (a n)) (level := fun n => r (a n)) (ε := fun n => ε (a n))
      (fun n => hLpos (a n)) (hLtop.comp ha) (fun n => hrec (a n)) (fun n => hNN (a n))
      (fun n => hd (a n)) (fun n => hr (a n)) (fun n => hcl (a n)) hC hv
      (fun n => (hε (a n)).le) (fun n => hε₁ (a n)) (hεlim.comp ha)
      hxconv hs₀T hB hθmem.1 i j
  have hθtendφ : Tendsto
      (fun n => DefectKnot.thetaL (τ (ψ (φ n))) B (r (ψ (φ n))) (L (ψ (φ n))))
      atTop (𝓝 (θ : ℝ)) := hθtend.comp hφ.tendsto_atTop
  have hlim : ∀ i, Tendsto (fun n => DefectKnot.knotConf (fun n => X (ψ (φ n)))
      (fun n => τ (ψ (φ n))) B (fun n => r (ψ (φ n))) (fun n => L (ψ (φ n))) n i)
      atTop (𝓝 (x i ⟨(θ : ℝ), (Nat.cast_nonneg B).trans hθmem.1, hθmem.2⟩)) :=
    fun i => DefectKnot.knotConf_tendsto_of_uniform (X := fun n => X (ψ n))
      (τ := fun n => τ (ψ n)) (B := B) (Tn := T) (Nat.cast_nonneg B)
      (level := fun n => r (ψ n)) (scale := fun n => L (ψ n))
      (fun n => hrec (ψ n)) (fun n => hLpos (ψ n)) (fun n i k => hNN (ψ n) i k)
      (fun n => htime (ψ n)) hφ hxconv hθmem.1 hθtendφ i
  have hev := DefectKnot.half_eventually_of_coalesced (X := fun n => X (ψ (φ n)))
    (τ := fun n => τ (ψ (φ n))) (B := B) (level := fun n => r (ψ (φ n)))
    (scale := fun n => L (ψ (φ n))) (fun n => hrec (ψ (φ n)))
    (fun n => hLpos (ψ (φ n)))
    (y := fun i => x i ⟨(θ : ℝ), (Nat.cast_nonneg B).trans hθmem.1, hθmem.2⟩) hlim hcoal
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hev] with n hn
    exact (not_le.2 (hbad (ψ (φ n)))) hn
  exact hfalse.exists.elim (fun n hn => hn)

end Swarming.Diameter
