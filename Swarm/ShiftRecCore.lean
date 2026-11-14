/-
  **Direction C: the generic shifted-seed recursion for the projected potential.**

  The paper's occupation-time estimate needs the projected potential
  `e_g = E[h_j(M_n^j + g) | F_n]` and its affine recursion `e_{g+1} = 1 + a (1 + e_g)`.
  The existing `areas/spatialavg/S14.lean` proves that recursion for the *deterministic* record
  `r` and the *specific* seed `E[h(r) | Gfilt r]`, where `Gfilt r` is the σ-algebra of the site
  marks `0, …, r`.  The interacting array needs two things S14 does not supply:

  * an **arbitrary** conditioning σ-algebra `K` (the enlarged information at the random record),
    not `Gfilt r`; and
  * an **arbitrary** `K`-measurable seed (the conditional mean of the potential at the record),
    not the concrete `hof r`.

  This file supplies exactly that: a shifted-seed recursion that starts at an arbitrary
  `K`-measurable seed and at an arbitrary set of sites *strictly after* the record, with the
  independence hypothesis stated in the minimal form used by the proof

      `Y (g+1)` is independent of `K ⊔ σ(X g)` and `∫ Y (g+1) = a`.

  ## Contents

  * `shiftRec`: the deterministic recursion `e_0 = seed`, `e_{g+1} = 1 + a (1 + e_g)`;
    closed form (`shiftRec_eq_pow_sum`, `shiftRec_closed`), the `e_{g+1} = a e_g + (1+a)` shape
    (`shiftRec_rec`), nonnegativity and the linear growth bound `e_g ≤ seed + 2g`.
  * `condExp_one_step`: the one-step conditional law at a fresh factor,
    `E[1 + Y (1 + X) | m] =ᵐ 1 + a (1 + X)` for any `m` with `X` measurable and `Y ⟂ m`.
  * `condExp_shiftRec`: **the projected recursion from an arbitrary `K`-measurable seed**,
    `E[X g | K] =ᵐ shiftRec a (E[X 0 | K]) g`.
  * `condExp_shiftRec_of_filtration`: the same when the independence is available against an
    increasing family of enlargements `Kf g ⊇ K` with `X g` measurable for `Kf g` — the form in
    which a fresh-block lemma on the enlarged filtration delivers it.

  ## Honest scope

  The independence hypothesis is *not* discharged here for the interacting array: the passage
  from `prefRead n γ` (a random set) to a fresh family is a separate statement.
  The record edge is handled by keeping the seed general: nothing here asserts that the actual
  potential `h` at the record is `K`-measurable, and `condExp_shiftRec` consumes only its
  conditional mean.
-/
import Swarm.Imports
import Mathlib.Probability.ConditionalExpectation

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.overlappingInstances false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace SwarmShift

variable {Ω : Type*}

/-! ### 1. The deterministic recursion -/

/-- The projected potential: `e 0 = seed`, `e (g+1) = 1 + a * (1 + e g)`. -/
noncomputable def shiftRec (a : ℝ) (seed : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => seed
  | (g + 1) => fun ω => 1 + a * (1 + shiftRec a seed g ω)

@[simp] lemma shiftRec_zero (a : ℝ) (seed : Ω → ℝ) : shiftRec a seed 0 = seed := rfl

@[simp] lemma shiftRec_succ (a : ℝ) (seed : Ω → ℝ) (g : ℕ) :
    shiftRec a seed (g + 1) = fun ω => 1 + a * (1 + shiftRec a seed g ω) := rfl

lemma shiftRec_succ_apply (a : ℝ) (seed : Ω → ℝ) (g : ℕ) (ω : Ω) :
    shiftRec a seed (g + 1) ω = 1 + a * (1 + shiftRec a seed g ω) := rfl

/-- The recursion in the shape `e_{g+1} = a e_g + (1 + a)` used by the paper's estimates. -/
lemma shiftRec_rec (a : ℝ) (seed : Ω → ℝ) (g : ℕ) (ω : Ω) :
    shiftRec a seed (g + 1) ω = a * shiftRec a seed g ω + (1 + a) := by
  rw [shiftRec_succ_apply]; ring

lemma geom_sum_one_add (a : ℝ) (k : ℕ) :
    (1 : ℝ) + a * ∑ i ∈ Finset.range k, a ^ i = ∑ i ∈ Finset.range (k + 1), a ^ i := by
  induction k with
  | zero => simp
  | succ n ih =>
      calc (1 : ℝ) + a * ∑ i ∈ Finset.range (n + 1), a ^ i
          = (1 + a * ∑ i ∈ Finset.range n, a ^ i) + a * a ^ n := by
            rw [Finset.sum_range_succ]; ring
        _ = (∑ i ∈ Finset.range (n + 1), a ^ i) + a * a ^ n := by rw [ih]
        _ = ∑ i ∈ Finset.range (n + 2), a ^ i := by
            rw [← pow_succ']
            conv_rhs => rw [Finset.sum_range_succ]

/-- Closed form of the recursion against the geometric series. -/
lemma shiftRec_eq_pow_sum (a : ℝ) (seed : Ω → ℝ) (g : ℕ) (ω : Ω) :
    shiftRec a seed g ω = a ^ g * seed ω + (1 + a) * ∑ i ∈ Finset.range g, a ^ i := by
  induction g with
  | zero => simp
  | succ k ih =>
      rw [shiftRec_succ_apply, ih, ← geom_sum_one_add a k, pow_succ']
      ring

/-- The closed form with `a ≠ 1`: `e_g = a^g seed + (1+a) (a^g - 1)/(a - 1)`. -/
lemma shiftRec_closed {a : ℝ} (ha : a ≠ 1) (seed : Ω → ℝ) (g : ℕ) (ω : Ω) :
    shiftRec a seed g ω = a ^ g * seed ω + (1 + a) * ((a ^ g - 1) / (a - 1)) := by
  rw [shiftRec_eq_pow_sum, geom_sum_eq ha]

/-- The projected potential stays nonnegative when `0 ≤ a` and the seed is nonnegative. -/
lemma shiftRec_nonneg {a : ℝ} (ha : 0 ≤ a) {seed : Ω → ℝ} (hs : ∀ ω, 0 ≤ seed ω)
    (g : ℕ) (ω : Ω) : 0 ≤ shiftRec a seed g ω := by
  induction g with
  | zero => exact hs ω
  | succ k ih => rw [shiftRec_succ_apply]; nlinarith

/-- Linear growth bound: for `0 ≤ a ≤ 1` the recursion gains at most `2` per step. -/
lemma shiftRec_le_add {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {seed : Ω → ℝ}
    (hs : ∀ ω, 0 ≤ seed ω) (g : ℕ) (ω : Ω) : shiftRec a seed g ω ≤ seed ω + 2 * g := by
  induction g with
  | zero => simp
  | succ k ih =>
      have hk := shiftRec_nonneg ha0 hs k ω
      have h1 : a * (1 + shiftRec a seed k ω) ≤ 1 + shiftRec a seed k ω :=
        mul_le_of_le_one_left (by linarith) ha1
      rw [shiftRec_succ_apply]
      push_cast
      linarith

/-! ### 2. Measurability of the recursion -/

section Measurable

variable [instΩ : MeasurableSpace Ω]

lemma measurable_shiftRec {a : ℝ} {seed : Ω → ℝ} (h : Measurable seed) (g : ℕ) :
    Measurable (shiftRec a seed g) := by
  induction g with
  | zero => simpa using h
  | succ k ih =>
      have heq : (fun ω => 1 + a * (1 + shiftRec a seed k ω))
          = fun ω => a * (1 + shiftRec a seed k ω) + 1 := by
        funext ω; ring
      rw [shiftRec_succ, heq]
      exact (measurable_const.mul (measurable_const.add ih)).add measurable_const

lemma stronglyMeasurable_shiftRec {m : MeasurableSpace Ω} {a : ℝ} {seed : Ω → ℝ}
    (h : StronglyMeasurable[m] seed) (g : ℕ) : StronglyMeasurable[m] (shiftRec a seed g) := by
  induction g with
  | zero => simpa using h
  | succ k ih =>
      have heq : (fun ω => 1 + a * (1 + shiftRec a seed k ω))
          = fun ω => a * (1 + shiftRec a seed k ω) + 1 := by
        funext ω; ring
      rw [shiftRec_succ, heq]
      exact (stronglyMeasurable_const.mul (stronglyMeasurable_const.add ih)).add
        stronglyMeasurable_const

end Measurable

/-! ### 3. The one-step conditional law at a fresh factor -/

section Prob

variable {K : MeasurableSpace Ω} {m : MeasurableSpace Ω} {Kf : ℕ → MeasurableSpace Ω}
variable [instΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The one-step conditional recursion at a fresh factor.**  If `X` is `m`-measurable and
`Y` is independent of `m` with mean `a`, then the conditional mean of the branch value
`1 + Y (1 + X)` given `m` is `1 + a (1 + X)`.

The only probabilistic input is the independence `Indep (σ Y) m`. -/
theorem condExp_one_step (hm : m ≤ instΩ) {X Y : Ω → ℝ} {a : ℝ}
    (hXm : Measurable[m] X) (hYm : Measurable Y) (hXi : Integrable X μ)
    (hYi : Integrable Y μ) (hprodi : Integrable (fun ω => Y ω * (1 + X ω)) μ)
    (hind : Indep (MeasurableSpace.comap Y (inferInstance : MeasurableSpace ℝ)) m μ)
    (hmean : ∫ ω, Y ω ∂μ = a) :
    condExp m μ (fun ω => 1 + Y ω * (1 + X ω)) =ᵐ[μ] fun ω => 1 + a * (1 + X ω) := by
  have hYle : MeasurableSpace.comap Y (inferInstance : MeasurableSpace ℝ) ≤ instΩ := hYm.comap_le
  have hXsm : StronglyMeasurable[m] X := hXm.stronglyMeasurable
  have hYsm : StronglyMeasurable[MeasurableSpace.comap Y (inferInstance : MeasurableSpace ℝ)] Y :=
    (comap_measurable Y).stronglyMeasurable
  have hce : condExp m μ Y =ᵐ[μ] fun _ => a := by
    have h := condExp_indep_eq (m₁ := MeasurableSpace.comap Y (inferInstance : MeasurableSpace ℝ))
      (m₂ := m) (m := instΩ) hYle hm hYsm hind
    simpa [hmean] using h
  have hgsm : StronglyMeasurable[m] (fun ω => 1 + X ω) := hXsm.const_add 1
  have hpt : (fun ω => Y ω * (1 + X ω)) = Y * fun ω => 1 + X ω := by
    funext ω; simp
  have hpull : condExp m μ (fun ω => Y ω * (1 + X ω)) =ᵐ[μ] fun ω => a * (1 + X ω) := by
    have h0 := condExp_mul_of_stronglyMeasurable_right (m := m) (f := Y)
      (g := fun ω => 1 + X ω) hgsm hprodi hYi
    have h : condExp m μ (fun ω => Y ω * (1 + X ω))
        =ᵐ[μ] condExp m μ Y * (fun ω => 1 + X ω) := by
      rw [hpt]; exact h0
    filter_upwards [h, hce] with ω h1 h2
    rw [Pi.mul_apply] at h1
    rw [h1, h2]
  have hpt2 : (fun ω => 1 + Y ω * (1 + X ω))
      = (fun _ : Ω => (1 : ℝ)) + fun ω => Y ω * (1 + X ω) := by
    funext ω; simp
  have hadd : condExp m μ (fun ω => 1 + Y ω * (1 + X ω))
      =ᵐ[μ] condExp m μ (fun _ => (1 : ℝ)) + condExp m μ (fun ω => Y ω * (1 + X ω)) := by
    rw [hpt2]
    exact condExp_add (m := m) (f := fun _ : Ω => (1 : ℝ))
      (g := fun ω => Y ω * (1 + X ω)) (integrable_const 1) hprodi
  have hone : condExp m μ (fun _ => (1 : ℝ)) =ᵐ[μ] fun _ => (1 : ℝ) :=
    Filter.EventuallyEq.of_eq (condExp_const (μ := μ) hm (1 : ℝ))
  filter_upwards [hadd, hpull, hone] with ω h1 h2 h3
  simp only [Pi.add_apply] at h1 h3
  rw [h1, h2, h3]

/-- Affineness of the one-step recursion:
`E[1 + c (1 + f) | m] =ᵐ 1 + c (1 + E[f | m])`. -/
theorem condExp_affine (hm : m ≤ instΩ) (f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ) :
    condExp m μ (fun ω => 1 + c * (1 + f ω))
      =ᵐ[μ] fun ω => 1 + c * (1 + condExp m μ f ω) := by
  set g : Ω → ℝ := fun ω => 1 + f ω with hg
  have hgint : Integrable g μ := by
    have h : Integrable ((fun _ : Ω => (1 : ℝ)) + f) μ := (integrable_const 1).add hf
    refine h.congr (Eventually.of_forall fun ω => ?_)
    simp [hg, Pi.add_apply]
  have e1 : condExp m μ (fun ω => 1 + c * g ω)
      =ᵐ[μ] condExp m μ ((fun _ : Ω => (1 : ℝ)) + c • g) :=
    condExp_congr_ae (Eventually.of_forall fun ω => by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul])
  have e2 : condExp m μ ((fun _ : Ω => (1 : ℝ)) + c • g)
      =ᵐ[μ] condExp m μ (fun _ : Ω => (1 : ℝ)) + condExp m μ (c • g) :=
    condExp_add (integrable_const 1) (hgint.const_mul c) m
  have e3 : condExp m μ (fun _ : Ω => (1 : ℝ)) =ᵐ[μ] fun _ => (1 : ℝ) :=
    Filter.EventuallyEq.of_eq (condExp_const (μ := μ) hm (1 : ℝ))
  have e4 : condExp m μ (c • g) =ᵐ[μ] c • condExp m μ g :=
    condExp_smul (μ := μ) (m := m) (𝕜 := ℝ) c g
  have e5 : condExp m μ g =ᵐ[μ] condExp m μ ((fun _ : Ω => (1 : ℝ)) + f) :=
    condExp_congr_ae (Eventually.of_forall fun ω => by simp [hg, Pi.add_apply])
  have e6 : condExp m μ ((fun _ : Ω => (1 : ℝ)) + f)
      =ᵐ[μ] condExp m μ (fun _ : Ω => (1 : ℝ)) + condExp m μ f :=
    condExp_add (integrable_const 1) hf m
  filter_upwards [e1, e2, e3, e4, e5, e6] with ω h1ω h2ω h3ω h4ω h5ω h6ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1ω h2ω h3ω h4ω h5ω h6ω ⊢
  rw [h1ω, h2ω, h3ω, h4ω, h5ω, h6ω, h3ω]

/-! ### 4. The projected recursion from an arbitrary seed -/

/-- **The projected recursion.**  Let `X` be a sequence of integrable potentials driven by
`X (g+1) = 1 + Y (g+1) (1 + X g)`, where the factor `Y (g+1)` is independent of
`K ⊔ σ (X g)` with mean `a`.  Then the conditional means given `K` follow the deterministic
shifted recursion started at the conditional mean of the seed.

No measurability of the seed for `K` is assumed, and nothing is asserted about the seed being
the actual value of a potential: it enters only through `condExp K μ (X 0)`. -/
theorem condExp_shiftRec (hK : K ≤ instΩ)
    (X Y : ℕ → Ω → ℝ) (a : ℝ)
    (hXm : ∀ g, Measurable (X g)) (hXi : ∀ g, Integrable (X g) μ)
    (hrec : ∀ g, X (g + 1) = fun ω => 1 + Y (g + 1) ω * (1 + X g ω))
    (hYi : ∀ g, Integrable (Y (g + 1)) μ) (hYm : ∀ g, Measurable (Y (g + 1)))
    (hYmean : ∀ g, ∫ ω, Y (g + 1) ω ∂μ = a)
    (hind : ∀ g, Indep (MeasurableSpace.comap (Y (g + 1)) (inferInstance : MeasurableSpace ℝ))
      (K ⊔ MeasurableSpace.comap (X g) (inferInstance : MeasurableSpace ℝ)) μ) :
    ∀ g, condExp K μ (X g) =ᵐ[μ] shiftRec a (condExp K μ (X 0)) g := by
  have hprodi : ∀ g, Integrable (fun ω => Y (g + 1) ω * (1 + X g ω)) μ := by
    intro g
    have h : Integrable (fun ω => X (g + 1) ω - 1) μ := (hXi (g + 1)).sub (integrable_const 1)
    refine h.congr (Eventually.of_forall fun ω => ?_)
    rw [hrec g]
    simp
  intro g
  induction g with
  | zero => exact EventuallyEq.rfl
  | succ k ih =>
      have hXkle : MeasurableSpace.comap (X k) (inferInstance : MeasurableSpace ℝ) ≤ instΩ :=
        (hXm k).comap_le
      have hXkmeas : Measurable[K ⊔ MeasurableSpace.comap (X k)
          (inferInstance : MeasurableSpace ℝ)] (X k) :=
        (comap_measurable (X k)).mono le_sup_right le_rfl
      have hstep : condExp (K ⊔ MeasurableSpace.comap (X k)
            (inferInstance : MeasurableSpace ℝ)) μ
            (fun ω => 1 + Y (k + 1) ω * (1 + X k ω))
          =ᵐ[μ] fun ω => 1 + a * (1 + X k ω) :=
        condExp_one_step (sup_le hK hXkle) hXkmeas (hYm k) (hXi k) (hYi k) (hprodi k)
          (hind k) (hYmean k)
      have htow : condExp K μ (X (k + 1))
          =ᵐ[μ] condExp K μ (fun ω => 1 + a * (1 + X k ω)) := by
        rw [hrec k]
        have htower : condExp K μ (fun ω => 1 + Y (k + 1) ω * (1 + X k ω))
            =ᵐ[μ] condExp K μ (condExp (K ⊔ MeasurableSpace.comap (X k)
              (inferInstance : MeasurableSpace ℝ)) μ
                (fun ω => 1 + Y (k + 1) ω * (1 + X k ω))) :=
          (condExp_condExp_of_le (μ := μ) (m₁ := K)
            (m₂ := K ⊔ MeasurableSpace.comap (X k) (inferInstance : MeasurableSpace ℝ))
            (m₀ := instΩ) le_sup_left (sup_le hK hXkle)).symm
        exact htower.trans (condExp_congr_ae hstep)
      have haff : condExp K μ (fun ω => 1 + a * (1 + X k ω))
          =ᵐ[μ] fun ω => 1 + a * (1 + shiftRec a (condExp K μ (X 0)) k ω) := by
        have h := condExp_affine (μ := μ) (m := K) hK (X k) (hXi k) a
        have h2 : (fun ω => (1 : ℝ) + a * (1 + (condExp K μ (X k)) ω))
            =ᵐ[μ] fun ω => 1 + a * (1 + shiftRec a (condExp K μ (X 0)) k ω) := by
          filter_upwards [ih] with ω hω
          rw [hω]
        exact h.trans h2
      exact htow.trans haff

/-- **The projected recursion with an increasing environment enlargement.**  The independence is
available against a family `Kf g ⊇ K` for which `X g` is measurable; this is the form in which a
fresh-block lemma on the enlarged filtration delivers it (each new block is adjoined to the
previous enlargement, so the conditioning σ-algebra grows with `g`). -/
theorem condExp_shiftRec_of_filtration (hK : K ≤ instΩ) (hKf : ∀ g, K ≤ Kf g)
    (hKfle : ∀ g, Kf g ≤ instΩ)
    (X Y : ℕ → Ω → ℝ) (a : ℝ)
    (hXm : ∀ g, Measurable[Kf g] (X g)) (hXi : ∀ g, Integrable (X g) μ)
    (hrec : ∀ g, X (g + 1) = fun ω => 1 + Y (g + 1) ω * (1 + X g ω))
    (hYi : ∀ g, Integrable (Y (g + 1)) μ) (hYm : ∀ g, Measurable (Y (g + 1)))
    (hYmean : ∀ g, ∫ ω, Y (g + 1) ω ∂μ = a)
    (hind : ∀ g, Indep (MeasurableSpace.comap (Y (g + 1)) (inferInstance : MeasurableSpace ℝ))
      (Kf g) μ) :
    ∀ g, condExp K μ (X g) =ᵐ[μ] shiftRec a (condExp K μ (X 0)) g := by
  refine condExp_shiftRec hK X Y a (fun g => (hXm g).mono (hKfle g) le_rfl) hXi hrec hYi hYm
    hYmean ?_
  intro g
  refine indep_of_indep_of_le_right (hind g) ?_
  exact sup_le (hKf g) (hXm g).comap_le

/-! ### 5. Congruence of the recursion in the seed -/

section Congr

variable [instΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- The recursion is a continuous function of the seed: almost-everywhere equal seeds give
almost-everywhere equal recursions. -/
lemma shiftRec_congr {a : ℝ} {seed seed' : Ω → ℝ} (h : seed =ᵐ[μ] seed') (g : ℕ) :
    shiftRec a seed g =ᵐ[μ] shiftRec a seed' g := by
  induction g with
  | zero => simpa using h
  | succ k ih =>
      filter_upwards [ih] with ω hω
      rw [shiftRec_succ_apply, shiftRec_succ_apply, hω]

end Congr

/-- **The projected recursion with the actual seed.**  When the seed is itself `K`-measurable —
which is the case once the record site's mark has been adjoined to the base information — the
conclusion can be written with `X 0` in place of its conditional mean.  This is the form the
interacting-array enlargement (direction B) is expected to hand over. -/
theorem condExp_shiftRec_selfseed (hK : K ≤ instΩ)
    (X Y : ℕ → Ω → ℝ) (a : ℝ)
    (hXm : ∀ g, Measurable (X g)) (hXi : ∀ g, Integrable (X g) μ)
    (hX0K : StronglyMeasurable[K] (X 0))
    (hrec : ∀ g, X (g + 1) = fun ω => 1 + Y (g + 1) ω * (1 + X g ω))
    (hYi : ∀ g, Integrable (Y (g + 1)) μ) (hYm : ∀ g, Measurable (Y (g + 1)))
    (hYmean : ∀ g, ∫ ω, Y (g + 1) ω ∂μ = a)
    (hind : ∀ g, Indep (MeasurableSpace.comap (Y (g + 1)) (inferInstance : MeasurableSpace ℝ))
      (K ⊔ MeasurableSpace.comap (X g) (inferInstance : MeasurableSpace ℝ)) μ) :
    ∀ g, condExp K μ (X g) =ᵐ[μ] shiftRec a (X 0) g := by
  have hmain := condExp_shiftRec hK X Y a hXm hXi hrec hYi hYm hYmean hind
  have hseed : condExp K μ (X 0) =ᵐ[μ] X 0 :=
    Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hK hX0K (hXi 0))
  exact fun g => (hmain g).trans (shiftRec_congr hseed g)

/-! ### 6. The recursion restricted to a `K`-measurable event

When the record index is only meaningful on a measurable event (in the interacting model, the
eventual-nonnegativity event `{0 ≤ M_n^j}`), the recursion is known only on that event.  The
following two results keep the restriction: they never assert anything off the event. -/

/-- **The restricted one-step recursion.**  If the branch identity for `X'` holds only on a
`K`-measurable event `R`, then the `K`-conditional mean of `X'` obeys the affine recursion
multiplied by the indicator of `R`. -/
theorem condExp_step_indicator (hK : K ≤ instΩ) {m : MeasurableSpace Ω} (hm : m ≤ instΩ)
    (hKm : K ≤ m) {R : Set Ω} (hR : MeasurableSet[K] R)
    {X X' Y : Ω → ℝ} {a : ℝ} (hXm : Measurable[m] X)
    (hXi : Integrable X μ) (hX'i : Integrable X' μ) (hYi : Integrable Y μ)
    (hprodi : Integrable (fun ω => Y ω * (1 + X ω)) μ)
    (hstep : condExp m μ (fun ω => 1 + Y ω * (1 + X ω)) =ᵐ[μ] fun ω => 1 + a * (1 + X ω))
    (hrec : R.indicator X' =ᵐ[μ] R.indicator (fun ω => 1 + Y ω * (1 + X ω))) :
    R.indicator (condExp K μ X')
      =ᵐ[μ] R.indicator (fun ω => 1 + a * (1 + condExp K μ X ω)) := by
  letI : MeasurableSpace Ω := instΩ
  have hKpull : condExp K μ (R.indicator X') =ᵐ[μ] R.indicator (condExp K μ X') :=
    condExp_indicator hX'i hR
  have hcongr : condExp K μ (R.indicator X')
      =ᵐ[μ] condExp K μ (R.indicator (fun ω => 1 + Y ω * (1 + X ω))) :=
    condExp_congr_ae hrec
  have hprodint : Integrable (fun ω => 1 + Y ω * (1 + X ω)) μ :=
    (integrable_const 1).add hprodi
  have hRpull : condExp K μ (R.indicator (fun ω => 1 + Y ω * (1 + X ω)))
      =ᵐ[μ] R.indicator (condExp K μ (fun ω => 1 + Y ω * (1 + X ω))) :=
    condExp_indicator hprodint hR
  have htower : condExp K μ (fun ω => 1 + Y ω * (1 + X ω))
      =ᵐ[μ] condExp K μ (condExp m μ (fun ω => 1 + Y ω * (1 + X ω))) :=
    (condExp_condExp_of_le (μ := μ) (m₁ := K) (m₂ := m) (m₀ := instΩ) hKm hm).symm
  have htower2 : condExp K μ (condExp m μ (fun ω => 1 + Y ω * (1 + X ω)))
      =ᵐ[μ] condExp K μ (fun ω => 1 + a * (1 + X ω)) := condExp_congr_ae hstep
  have haff : condExp K μ (fun ω => 1 + a * (1 + X ω))
      =ᵐ[μ] fun ω => 1 + a * (1 + condExp K μ X ω) :=
    condExp_affine hK X hXi a
  have hfun : condExp K μ (fun ω => 1 + Y ω * (1 + X ω))
      =ᵐ[μ] fun ω => 1 + a * (1 + condExp K μ X ω) := htower.trans (htower2.trans haff)
  have hind_eq : R.indicator (condExp K μ (fun ω => 1 + Y ω * (1 + X ω)))
      =ᵐ[μ] R.indicator (fun ω => 1 + a * (1 + condExp K μ X ω)) := by
    filter_upwards [hfun] with ω hω
    by_cases h : ω ∈ R
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hω]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
  exact hKpull.symm.trans (hcongr.trans (hRpull.trans hind_eq))


/-- **The projected recursion restricted to a `K`-measurable event.**  If the branch identity for
`X` is known only on `R` — in the interacting model, on the eventual-nonnegativity event
`{0 ≤ M_n^j}` that makes the record index a natural number — then the conclusion holds only
multiplied by the indicator of `R`, and nothing is asserted off `R`.

No independence or measurability is required off `R`; `R` itself must be `K`-measurable, which is
the case for the eventual-nonnegativity event when the base information contains the trajectory. -/
theorem condExp_shiftRec_restrict (hK : K ≤ instΩ)
    (R : Set Ω) (hR : MeasurableSet[K] R)
    (X Y : ℕ → Ω → ℝ) (a : ℝ)
    (hXm : ∀ g, Measurable (X g)) (hXi : ∀ g, Integrable (X g) μ)
    (hYm : ∀ g, Measurable (Y (g + 1))) (hYi : ∀ g, Integrable (Y (g + 1)) μ)
    (hprodi : ∀ g, Integrable (fun ω => Y (g + 1) ω * (1 + X g ω)) μ)
    (hYmean : ∀ g, ∫ ω, Y (g + 1) ω ∂μ = a)
    (hrec : ∀ g, R.indicator (X (g + 1))
      =ᵐ[μ] R.indicator (fun ω => 1 + Y (g + 1) ω * (1 + X g ω)))
    (hind : ∀ g, Indep (MeasurableSpace.comap (Y (g + 1)) (inferInstance : MeasurableSpace ℝ))
      (K ⊔ MeasurableSpace.comap (X g) (inferInstance : MeasurableSpace ℝ)) μ) :
    ∀ g, R.indicator (condExp K μ (X g))
      =ᵐ[μ] R.indicator (shiftRec a (R.indicator (condExp K μ (X 0))) g) := by
  intro g
  induction g with
  | zero =>
      rw [shiftRec_zero]
      filter_upwards with ω
      by_cases h : ω ∈ R <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  | succ k ih =>
      rw [shiftRec_succ]
      have hXkle : MeasurableSpace.comap (X k) (inferInstance : MeasurableSpace ℝ) ≤ instΩ :=
        (hXm k).comap_le
      have hXkmeas : Measurable[K ⊔ MeasurableSpace.comap (X k)
          (inferInstance : MeasurableSpace ℝ)] (X k) :=
        (comap_measurable (X k)).mono le_sup_right le_rfl
      have hstep : condExp (K ⊔ MeasurableSpace.comap (X k)
            (inferInstance : MeasurableSpace ℝ)) μ
            (fun ω => 1 + Y (k + 1) ω * (1 + X k ω))
          =ᵐ[μ] fun ω => 1 + a * (1 + X k ω) :=
        condExp_one_step (sup_le hK hXkle) hXkmeas (hYm k) (hXi k) (hYi k) (hprodi k)
          (hind k) (hYmean k)
      have hstep' := condExp_step_indicator (K := K)
        (m := K ⊔ MeasurableSpace.comap (X k) (inferInstance : MeasurableSpace ℝ))
        hK (sup_le hK hXkle) le_sup_left hR hXkmeas (hXi k) (hXi (k + 1)) (hYi k)
        (hprodi k) hstep (hrec k)
      refine hstep'.trans ?_
      filter_upwards [ih] with ω hω
      by_cases h : ω ∈ R
      · simp only [Set.indicator_of_mem h] at hω ⊢
        rw [hω]
      · simp only [Set.indicator_of_notMem h]

end Prob

end SwarmShift


