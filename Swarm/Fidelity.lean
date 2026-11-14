/-
Fidelity checks for the **current** (repaired) assembly interface of
`Swarm/Assembly.lean`.

Companion to `OldInterface.lean`, which refutes the pre-repair `Sandwich`.

The three checks:

* `paper_sandwich`: the current `Sandwich` entails exactly the paper's displayed inequality
  `z_k <= X_n^i < z_{k+1}` for `sigma_k <= n < sigma_{k+1}`, `k >= 1`
  (`main_1d_revised.tex:1874`).  This is the forward fidelity direction: the Lean hypothesis
  really does say what the paper says on the paper's own scope.
* `ballistic_of_mainClaim`: `MainClaim m p -> Ballistic m p`.  The lower-speed input is
  therefore not stronger than the paper's theorem, so naming it as an input loses nothing.
  (Nothing is claimed for the other two inputs; `OldInterface.lean` shows what happened to
  the version of `RegenAvailable` that was *not* implied by the theorem.)
* `one_le_D_zero` / `one_le_mean_D`: the interface and `RegenLaw` together *derive* the lower
  half of the paper's `(ED)`, `1 <= E^*D`.  `RegenLaw` itself only assumes `T >= 1`; the
  positivity of the regeneration distance comes from the path structure.
-/
import Swarm.Assembly

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace Swarm

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
variable {X : ℕ → Ω → Fin N → ℤ} {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {m : ℕ} {p : ℝ}

/-- **Forward source fidelity of `Sandwich`.**  On the paper's own scope (`k >= 1`,
`sigma_k <= n < sigma_{k+1}`) the Lean interface gives exactly the displayed inequality
`z_k <= X_n^i < z_{k+1}` of `main_1d_revised.tex`. -/
theorem paper_sandwich {D T : ℕ → Ω → ℕ} (hsand : Sandwich μ X D T) :
    ∀ᵐ ω ∂μ, ∀ (i : Fin N) (k n : ℕ), 1 ≤ k →
      blockSum (fun j => T j ω) k ≤ n → n < blockSum (fun j => T j ω) (k + 1) →
      (blockSum (fun j => D j ω) k : ℤ) ≤ X n ω i ∧
        X n ω i < (blockSum (fun j => D j ω) (k + 1) : ℤ) := by
  filter_upwards [hsand] with ω h i k n hk h1 h2
  refine ⟨(h i k n).1 hk h1, ?_⟩
  by_contra hcon
  push Not at hcon
  have := (h i k n).2 hcon
  omega

/-- **`MainClaim m p` implies `Ballistic m p`.** -/
theorem ballistic_of_mainClaim {m : ℕ} {p : ℝ} (h : MainClaim m p) : Ballistic m p := by
  obtain ⟨κ, hκpos, hκ⟩ := h
  refine ⟨κ, hκpos, ?_⟩
  intro N Ω _ μ _ X 𝓕 hN hlaw
  obtain ⟨v, hvκ, _hv2, hv⟩ := hκ N Ω μ X 𝓕 hN hlaw
  filter_upwards [hv] with ω hω i
  have hlim : Tendsto (fun n => pos X n i ω / n) atTop (𝓝 v) := hω i
  rw [hlim.liminf_eq]
  exact hvκ

/-- **The first regeneration level is positive.**  Clause 2 with `k = n = 0` reads
`D 0 <= X 0 i -> T 0 <= 0`; since `X 0 i = 0` and `1 <= T 0`, this gives `1 <= D 0`. -/
theorem one_le_D_zero (hlaw : IsInteractingLaw 𝓕 μ X m p) (hN : 1 ≤ N)
    {D T : ℕ → Ω → ℕ} (hreg : RegenLaw μ D T) (hsand : Sandwich μ X D T) :
    ∀ᵐ ω ∂μ, 1 ≤ D 0 ω := by
  obtain ⟨i₀⟩ : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hT : ∀ k ω, 1 ≤ T k ω := hreg.2.2.1
  filter_upwards [hsand] with ω h
  have hcl := (h i₀ 0 0).2
  have hx : X 0 ω i₀ = 0 := hlaw.2.1 ω i₀
  have hD1 : blockSum (fun j => D j ω) 1 = D 0 ω := by simp [blockSum]
  have hT1 : blockSum (fun j => T j ω) 1 = T 0 ω := by simp [blockSum]
  have hTm : 1 ≤ blockSum (fun j => T j ω) 1 := by rw [hT1]; exact hT 0 ω
  rw [hD1, hx] at hcl
  by_contra hcon
  push Not at hcon
  have hDz : D 0 ω = 0 := by omega
  have hant : (D 0 ω : ℤ) ≤ 0 := by omega
  have h2 : blockSum (fun j => T j ω) 1 ≤ 0 := hcl hant
  omega

/-- **The lower half of the paper's `(ED)`: `1 <= E^*D`.** -/
theorem one_le_mean_D (hlaw : IsInteractingLaw 𝓕 μ X m p) (hN : 1 ≤ N)
    {D T : ℕ → Ω → ℕ} (hreg : RegenLaw μ D T) (hsand : Sandwich μ X D T) :
    1 ≤ ∫ ω, (D 0 ω : ℝ) ∂μ := by
  have hae : ∀ᵐ ω ∂μ, (1 : ℝ) ≤ (D 0 ω : ℝ) := by
    filter_upwards [one_le_D_zero hlaw hN hreg hsand] with ω hω
    exact_mod_cast hω
  have hcongr : ∫ ω, (D 0 ω : ℝ) ∂μ = ∫ ω, max 1 ((D 0 ω : ℝ)) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    exact (max_eq_right hω).symm
  have hint : Integrable (fun ω => max 1 ((D 0 ω : ℝ))) μ :=
    Integrable.sup (integrable_const 1) (hreg.1 0)
  have hmono : ∫ _ : Ω, (1 : ℝ) ∂μ ≤ ∫ ω, max 1 ((D 0 ω : ℝ)) ∂μ :=
    integral_mono (integrable_const 1) hint (fun ω => le_max_left _ _)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hmono
  rw [hcongr]
  exact hmono

/-- `Pairwise` constrains only distinct indices, so `RegenLaw`'s independence conjunct is not
the (unsatisfiable) requirement that an increment be independent of itself. -/
theorem pairwise_distinct (r : ℕ → ℕ → Prop) :
    Pairwise r ↔ ∀ a b : ℕ, a ≠ b → r a b := Iff.rfl

end Swarm


namespace Swarm

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
variable {X : ℕ → Ω → Fin N → ℤ} {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {m : ℕ} {p : ℝ}

/-- **Backward source fidelity of `Sandwich`'s lower clause.**  The paper's displayed
inequality for `sigma_k <= n < sigma_{k+1}` and `k >= 1` alone implies the whole `k >= 1`
lower clause of `Swarm.Sandwich`, i.e. that the level `z_k` is not undercut at *any* time
after `sigma_k`: take `j = renewCount T n` (so `sigma_j <= n < sigma_{j+1}`) and use
`z_k <= z_j`.

Together with `paper_sandwich` this says: on the paper's scope `k >= 1`, the Lean lower
clause of `Sandwich` is *equivalent* to the paper's inequality.  The only content of
`Sandwich` that the paper's displayed inequality does not supply is clause 2 at `k = 0`,
i.e. "no walker reaches the first regeneration level `z_1` strictly before `sigma_1`"; the
paper gets that from its *definition* of `sigma_1` as a simultaneous record time, and the
assembly needs it for `hit_level` at `k = 1` (hence for `kappa <= v`) and for
`1 <= E^*D` (`one_le_D_zero`). -/
theorem sandwich_clause1_of_paper_ineq {D T : ℕ → Ω → ℕ} (hT : ∀ k, 1 ≤ T k)
    (h : ∀ᵐ ω ∂μ, ∀ (i : Fin N) (k n : ℕ), 1 ≤ k →
      blockSum (fun j => T j ω) k ≤ n → n < blockSum (fun j => T j ω) (k + 1) →
      (blockSum (fun j => D j ω) k : ℤ) ≤ X n ω i) :
    ∀ᵐ ω ∂μ, ∀ (i : Fin N) (k n : ℕ), 1 ≤ k →
      blockSum (fun j => T j ω) k ≤ n → (blockSum (fun j => D j ω) k : ℤ) ≤ X n ω i := by
  filter_upwards [h] with ω h i k n hk hσk
  have hTω : ∀ j, 1 ≤ T j ω := fun j => hT j ω
  have hmono : StrictMono (blockSum (fun j => T j ω)) := strictMono_blockSum hTω
  have hσj : blockSum (fun j => T j ω) (renewCount (fun j => T j ω) n) ≤ n :=
    blockSum_renewCount_le _ n
  have hσj1 : n < blockSum (fun j => T j ω) (renewCount (fun j => T j ω) n + 1) :=
    lt_blockSum_renewCount_succ hTω n
  have hkj : k ≤ renewCount (fun j => T j ω) n := by
    by_contra hlt
    push Not at hlt
    have h1 : blockSum (fun j => T j ω) (renewCount (fun j => T j ω) n + 1)
        ≤ blockSum (fun j => T j ω) k := hmono.monotone (by omega)
    omega
  have hj1 : 1 ≤ renewCount (fun j => T j ω) n := le_trans hk hkj
  have hz : blockSum (fun j => D j ω) k ≤ blockSum (fun j => D j ω)
      (renewCount (fun j => T j ω) n) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hkj)
      (fun _ _ _ => Nat.zero_le _)
  have hcast : (blockSum (fun j => D j ω) k : ℤ)
      ≤ (blockSum (fun j => D j ω) (renewCount (fun j => T j ω) n) : ℤ) := by
    exact_mod_cast hz
  exact le_trans hcast (h i _ n hj1 hσj hσj1)

end Swarm

