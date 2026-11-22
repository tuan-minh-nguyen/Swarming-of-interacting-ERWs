import Swarm.M1Coalesce

open Finset
open Glue LocalFluid RecordDefect

namespace Swarming.Diameter

set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Deterministic estimates on a record interval. The comparison estimates
are expressed directly in the walkers' positions. -/
structure LinearBlockClauses (X : ι → ℕ → ℤ) (τ : ℕ → ℕ) (r T L : ℕ)
    (C v E : ℝ) : Prop where
  down : ∀ i s t, τ r ≤ s → s ≤ t → t ≤ τ r + T * L → (X i s : ℝ) - X i t ≤ E
  minimum : ∀ s t, τ r ≤ s → s ≤ t → t ≤ τ r + T * L →
    (runMin X s : ℝ) + v * ((t : ℝ) - s) - E ≤ (runMin X t : ℝ)
  compare : ∀ (J : Finset ι) (i : ι), i ∈ Jᶜ → ∀ s t,
    τ r ≤ s → s ≤ t → t ≤ τ r + T * L →
    (∀ u ∈ Finset.Icc s t, Glue.Sep X Jᶜ J u) →
    (X i t : ℝ) - sMin X J t ≤ C * ((X i s : ℝ) - sMin X J s) + E
  meet : ∀ (J : Finset ι) s t, τ r ≤ s → s ≤ t → t ≤ τ r + T * L →
    (∀ u ∈ Finset.Icc s t, Glue.Sep X Jᶜ J u) →
    (t : ℝ) - s ≤ C * ((sMaxM X Finset.univ s : ℝ) - runMin X s) + E

theorem LinearBlockClauses.mono_error {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {r T L : ℕ}
    {C v E E' : ℝ} (h : LinearBlockClauses X τ r T L C v E) (hE : E ≤ E') :
    LinearBlockClauses X τ r T L C v E' :=
  ⟨fun i s t hs hst ht => (h.down i s t hs hst ht).trans hE,
   fun s t hs hst ht => (sub_le_sub_left hE _).trans (h.minimum s t hs hst ht),
   fun J i hi s t hs hst ht hsep =>
     (h.compare J i hi s t hs hst ht hsep).trans (add_le_add_right hE _),
   fun J s t hs hst ht hsep => (h.meet J s t hs hst ht hsep).trans (add_le_add_right hE _)⟩

theorem LinearBlockClauses.lag {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {r T L : ℕ}
    {C v E : ℝ} (h : LinearBlockClauses X τ r T L C v E) (hτ : IsRecord X τ)
    {t : ℕ} (_hs : τ r ≤ t) (ht : t ≤ τ r + T * L)
    (hr : (r : ℤ) ≤ runMin X t) (hE : 0 ≤ E) (i : ι) :
    (runMaxI X i t : ℝ) - X i t ≤ E := by
  have hX (n : ℕ) (hn : n ≤ t) : (X i n : ℝ) ≤ (X i t : ℝ) + E := by
    by_cases hn' : n ≤ τ r
    · have h₁ := (le_runMaxI X i n).trans (runMaxI_le_of_le_tau X hτ i hn')
      have h₂ := hr.trans (runMin_le (X := X) t i)
      have hx : (X i n : ℝ) ≤ X i t := by exact_mod_cast h₁.trans h₂
      linarith only [hE, hx]
    · have hx := h.down i n t (by omega) hn ht
      linarith only [hx]
  have hm (n : ℕ) (hn : n ≤ t) : (runMaxI X i n : ℝ) ≤ (X i t : ℝ) + E := by
    induction n with
    | zero => exact hX 0 hn
    | succ n ih =>
      rw [runMaxI_succ, Int.cast_max]
      exact max_le (ih (Nat.le_of_succ_le hn)) (hX (n + 1) hn)
  linarith only [hm t le_rfl]

/-- Positive advance of the minimum forces the later record to occur
within the prescribed interval. -/
theorem LinearBlockClauses.advance {X : ι → ℕ → ℤ} {τ : ℕ → ℕ} {r T L B : ℕ}
    {C v ε : ℝ} (h : LinearBlockClauses X τ r T L C v (ε * (L : ℝ)))
    (hτ : IsRecord X τ) (hd : defect X τ r ≤ (L : ℤ)) (hε : ε ≤ 1)
    (hT : (B : ℝ) + 2 ≤ v * (T : ℝ)) :
    τ (r + B * L) - τ r ≤ T * L := by
  have hmin := h.minimum (τ r) (τ r + T * L) le_rfl (Nat.le_add_right _ _) le_rfl
  push_cast at hmin
  have hdi : (r : ℝ) - (runMin X (τ r) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hd
  have htarget : (r : ℝ) + (B : ℝ) * (L : ℝ) ≤ (runMin X (τ r + T * L) : ℝ) := by
    nlinarith only [hmin, hdi, mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α := ℝ) L),
      mul_le_mul_of_nonneg_right hT (Nat.cast_nonneg (α := ℝ) L)]
  have hi : ((r + B * L : ℕ) : ℤ) ≤ runMin X (τ r + T * L) := by exact_mod_cast htarget
  have hrec : τ (r + B * L) ≤ τ r + T * L := by
    by_contra! hbad
    exact (not_le_of_gt ((hτ _).1 _ hbad)) (hi.trans (runMin_le_runMax (X := X) _))
  omega

end Swarming.Diameter
