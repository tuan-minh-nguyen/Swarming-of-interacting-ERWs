import SwarmDiameter.RecordFluidLimit
import Swarm.M1Half

open Filter Set
open scoped Topology

namespace Swarming.Diameter

open FluidInterpolation FluidLimit JoinStep RecordDefect

set_option autoImplicit false

/-- A sufficiently small linear error in the local clauses suffices to halve the
defect at the later record, uniformly over the paths and record levels. -/
theorem record_defect_halves_of_local_clauses
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] (C₀ B T : ℕ)
    {C : ℝ} (hC : 1 ≤ C) (hT64 : 64 * Nat.ceil C ≤ T) (hC₀ : T + 3 ≤ C₀)
    (hB : (1 + 64 * (Nat.ceil C : ℝ)) * (1 + 2 * C ^ 2) ^ (Fintype.card ι - 1) - 1
      < (B : ℝ) - 2) (hcard : 2 ≤ Fintype.card ι) (μ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ r : ℕ, C₀ * L ≤ r →
      ∀ (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (H : Finset ι → ℕ → ℤ → ℤ) (A : ι → ℕ → ℕ) (CT : ℝ),
      IsRecord X τ → (∀ i n, |X i (n + 1) - X i n| = 1) → defect X τ r ≤ (L : ℤ) →
      τ (r + B * L) - τ r ≤ T * L →
      BlkCoin.BlockClauses X τ H C CT T L r → MartClause X τ A μ CT T L r →
      0 ≤ CT → CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ ε * (L : ℝ) →
      2 * defect X τ (r + B * L) ≤ (L : ℤ) := by
  classical
  by_contra hcon
  let ε (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hε₁ (n : ℕ) : ε n ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) n])
  have hseq : ∀ n : ℕ, ∃ L : ℕ, n + 1 ≤ L ∧ ∃ r : ℕ, C₀ * L ≤ r ∧
      ∃ (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (H : Finset ι → ℕ → ℤ → ℤ) (A : ι → ℕ → ℕ) (CT : ℝ),
        IsRecord X τ ∧ (∀ i k, |X i (k + 1) - X i k| = 1) ∧ defect X τ r ≤ (L : ℤ) ∧
        τ (r + B * L) - τ r ≤ T * L ∧ BlkCoin.BlockClauses X τ H C CT T L r ∧
        MartClause X τ A μ CT T L r ∧ 0 ≤ CT ∧ CT * (L : ℝ) ^ (3 / 4 : ℝ) ≤ ε n * L ∧
        (L : ℤ) < 2 * defect X τ (r + B * L) := by
    push Not at hcon
    intro n
    exact hcon (ε n) (hε n) (hε₁ n) (n + 1)
  choose L hLn r hrL X τ H A CT hrec hNN hd htime hBC hM hCT herr hbad using hseq
  have hLtop : Tendsto L atTop atTop :=
    tendsto_atTop_mono (f := fun n : ℕ => n) (g := L) (fun n => by have := hLn n; omega)
      tendsto_id
  have hLpos : ∀ n, 0 < L n := fun n => by have := hLn n; omega
  have hr : ∀ n, (T + 3) * L n ≤ r n :=
    fun n => le_trans (Nat.mul_le_mul_right (L n) hC₀) (hrL n)
  have hlow : ∀ n, (B : ℝ) ≤ DefectKnot.thetaL (τ n) B (r n) (L n) :=
    fun n => DefectKnot.theta_mem_lower (hrec n) (hNN n) (hLpos n)
  have hup : ∀ n, DefectKnot.thetaL (τ n) B (r n) (L n) ≤ (T : ℝ) :=
    fun n => DefectKnot.theta_mem_upper (htime n) (hLpos n)
  obtain ⟨θ, hθmem, ψ, hψ, hθtend⟩ := isCompact_Icc.tendsto_subseq
    (x := fun n => DefectKnot.thetaL (τ n) B (r n) (L n)) (fun n => ⟨hlow n, hup n⟩)
  obtain ⟨x, φ, hφ, _hxlip, _hxbound, hxconv, _hxstart, _hlarge', _hscale', _hd', _hsample⟩ :=
    FluidInterpolation.exists_record_interpolated_limit_subseq C₀ (T : ℝ) (Nat.cast_nonneg T)
      (fun n => X (ψ n)) (fun n => τ (ψ n)) (fun n => r (ψ n)) (fun n => L (ψ n))
      (fun n => hrec (ψ n)) (fun n => hrL (ψ n)) (hLtop.comp hψ.tendsto_atTop)
      (fun n => hLpos (ψ n)) (fun n => hd (ψ n)) ⟨0, ⟨le_rfl, Nat.cast_nonneg T⟩⟩ rfl
      (fun n i k => hNN (ψ n) i k)
  obtain ⟨i₀, j₀, hij⟩ : ∃ i₀ j₀ : ι, i₀ ≠ j₀ := by
    have h1 : 1 < Fintype.card ι := by omega
    obtain ⟨a⟩ := (inferInstance : Nonempty ι)
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card h1 a
    exact ⟨b, a, hb⟩
  let η (n : ℕ) := ⌈CT n * (L n : ℝ) ^ (3 / 4 : ℝ)⌉₊
  have hη (n : ℕ) : CT n * (L n : ℝ) ^ (3 / 4 : ℝ) ≤ (η n : ℝ) := Nat.le_ceil _
  have hnum (n : ℕ) : Numerics C (CT n) (L n) :=
    (herr n).trans (mul_le_mul_of_nonneg_right ((hε₁ n).trans hC) (Nat.cast_nonneg _))
  have hLr (n : ℕ) : (0 : ℝ) < (L n : ℝ) := by exact_mod_cast hLpos n
  have hηbound (n : ℕ) : (η n : ℝ) / (L n : ℝ) ≤ ε n + (L n : ℝ)⁻¹ := by
    have hceil : (η n : ℝ) ≤ CT n * (L n : ℝ) ^ (3 / 4 : ℝ) + 1 :=
      (Nat.ceil_lt_add_one (mul_nonneg (hCT n) (Real.rpow_nonneg (Nat.cast_nonneg _) _))).le
    rw [div_le_iff₀ (hLr n), add_mul, inv_mul_cancel₀ (hLr n).ne']
    exact hceil.trans (add_le_add (herr n) le_rfl)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa only [ε, Nat.cast_succ, Function.comp_def] using tendsto_inv_atTop_zero.comp ht
  have hinv : Tendsto (fun n => (L n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hLtop)
  have hsum : Tendsto (fun n => ε n + (L n : ℝ)⁻¹) atTop (𝓝 0) := by simpa using hεlim.add hinv
  have hratio : Tendsto (fun n => (η n : ℝ) / (L n : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun n => by positivity) hηbound hsum
  have hcoal : ∀ i j : ι,
      x i ⟨θ, (Nat.cast_nonneg B).trans hθmem.1, hθmem.2⟩ =
        x j ⟨θ, (Nat.cast_nonneg B).trans hθmem.1, hθmem.2⟩ := by
    intro i j
    exact coalesced_at_of_local_errors
      (scale := fun n => L (ψ (φ n))) (level := fun n => r (ψ (φ n)))
      (CT := fun n => CT (ψ (φ n))) (eta := fun n => η (ψ (φ n)))
      (fun n => hLpos (ψ (φ n))) ((hLtop.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop)
      (fun n => hrec (ψ (φ n))) (fun n i k => hNN (ψ (φ n)) i k)
      (fun n => hBC (ψ (φ n))) (fun n => hM (ψ (φ n))) hC (fun n => hCT (ψ (φ n)))
      (fun n => hd (ψ (φ n))) (fun n => hr (ψ (φ n))) hij (fun n => hnum (ψ (φ n))) hT64
      (fun n => hη (ψ (φ n))) ((hratio.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop)
      hxconv hB hθmem.1 i j
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
