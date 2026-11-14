/-
# The `(locmove)` drift half with the martingale defect bounded

`Swarming.GammaStrict.ae_window_gamma_drift_le` proves, at the paper's own constants, the
`-(R_t^A - R_s^A)` half of display `(locmove)`:

  `W_t^{A,Aᶜ} - W_s^{A,Aᶜ} ≤ -γ (R_t^A - R_s^A) + κ C L^{3/4} + (Q_t^{A,Aᶜ} - Q_s^{A,Aᶜ})`,

with `γ = (2p-1)(1-p)^{(2m-1)|A|}/|A|`, `κ = (2p-1)/|A|`, `C = 2m(1-p)^{(2m-1)|A|} + 4m`, and
leaves the martingale defect `Q_t - Q_s` explicit.  `LocGroupWindow.ae_psum_dQT_eq_Q_sub` shows
that on a window on which the predictable event `GoodW` holds at every time this defect *is* the
truncated martingale sum, whose maximal deviation is bounded by
`LocGroupWindow.measure_deviation_goodW_le`.  Composing the two removes the defect:

* `measure_gamma_window_le` — on the event
  `ambGood ∧ (sep) on [s,t) ∧ GoodW on [s,t) ∧ r-L ≤ R^A_{n₀} ≤ r`,
  the paper's drift bound plus `ε` fails only on a set of measure at most
  `2 (t-s+1) exp (-ε²/(4 (t-s) (2 envB p B)²))`, provided `ε ≤ 4 (t-s) envB p B`.

Scope.  This is *not* `(locmove)`: the `-(t-s)/C` term of the paper comes from the growth of the
group maximum `max_{j∈Aᶜ} H^A(X^j)` (`LocMoveH`), which is a second, independent drift and is not
composed here.  What is claimed is exactly the displayed inequality with the martingale defect
*estimated* rather than left as a free difference.  No `(locgroup)`, no `(loccoord)`, no
`(coincide)`, no `(meet)`, no halving, no invariant law, no `MainClaim`.
-/
import Swarm.LocGroupWindow
import Swarm.GammaStrictWindow

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace LocGroupGamma

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift Swarming.Enl LocGroupQ LocGroupWindow

variable {N : ℕ}

/-- **The `-(R_t^A - R_s^A)` half of `(locmove)` with the martingale defect bounded.** -/
theorem measure_gamma_window_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    {Th Lh : ℕ} (hL : 1 ≤ Lh) {r : ℤ} (hr : (((Th + 3) * Lh : ℕ) : ℤ) ≤ r)
    {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (Th + 3) * Lh)
    {B : ℝ} (hB : 0 < B) (hK : 1 ≤ t - s) {ε : ℝ} (hε : 0 < ε)
    (hside : ε ≤ 4 * ((t - s : ℕ) : ℝ) * stepEnv (N := N) p B) :
    (arrayMeasure N).real
      {U : Array N |
        U ∈ ambGood p m hA r Th Lh ∧
        (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) ∧
        (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA B U) ∧
        (r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r) ∧
        (-((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
            ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ)
          + (2 * p - 1) / ((A.card : ℕ) : ℝ) *
              ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                Real.sqrt (Lh * Real.sqrt Lh))
          + ε < WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc)}
      ≤ 2 * (((t - s : ℕ) : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (4 * (((t - s : ℕ) : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hid : Disjoint A Aᶜ := disjoint_compl_right
  -- the bounded maximal deviation of the truncated process
  have hdev := measure_deviation_goodW_le (N := N) (m := m)
    (s := s) (K := t - s) (B := B) (ε := ε) hp0 hp1 A Aᶜ hA hAc hid hB hK hε hside
  -- the drift half, with the defect explicit
  have hdrift := Swarming.GammaStrict.ae_window_gamma_drift_le (N := N) hp0 hp1 hm A hA hAc
    hL hr hn0 hst hhor
  -- the defect is the truncated sum on a `GoodW` window
  have hQeq := ae_psum_dQT_eq_Q_sub (N := N) hp0 hp1 (m := m) A Aᶜ hA hAc hid B
  -- the event is contained in the deviation event off a null set
  have hsub : {U : Array N |
        U ∈ ambGood p m hA r Th Lh ∧
        (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) ∧
        (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA B U) ∧
        (r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r) ∧
        (-((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
            ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ)
          + (2 * p - 1) / ((A.card : ℕ) : ℝ) *
              ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                Real.sqrt (Lh * Real.sqrt Lh))
          + ε < WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc)}
      ⊆ {U : Array N | ∃ k ≤ t - s,
            ε ≤ |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U|}
        ∪ ({U : Array N | ¬ (U ∈ ambGood p m hA r Th Lh →
              (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
                r - (Lh : ℤ) ≤ runMaxA p m U hA n0 →
                  runMaxA p m U hA n0 ≤ r →
                    WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
                      -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
                          ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) +
                        (2 * p - 1) / ((A.card : ℕ) : ℝ) *
                          ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                            Real.sqrt (Lh * Real.sqrt Lh)) +
                        (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U))}
          ∪ {U : Array N | ¬ (∀ s' t' : ℕ, s' ≤ t' →
              (∀ k, s' ≤ k → k < t' → GoodW p m k A Aᶜ hA B U) →
              LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s' + j)) (t' - s') U
                = Q p m A Aᶜ hA hAc t' U - Q p m A Aᶜ hA hAc s' U)}) := by
    intro U hU
    obtain ⟨hgood, hsep, hgoodW, hrec, hgain⟩ := hU
    show (∃ k ≤ t - s, ε ≤ |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U|)
        ∨ (¬ (U ∈ ambGood p m hA r Th Lh →
              (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
                r - (Lh : ℤ) ≤ runMaxA p m U hA n0 →
                  runMaxA p m U hA n0 ≤ r →
                    WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
                      -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
                          ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) +
                        (2 * p - 1) / ((A.card : ℕ) : ℝ) *
                          ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                            Real.sqrt (Lh * Real.sqrt Lh)) +
                        (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U)))
        ∨ (¬ (∀ s' t' : ℕ, s' ≤ t' →
              (∀ k, s' ≤ k → k < t' → GoodW p m k A Aᶜ hA B U) →
              LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s' + j)) (t' - s') U
                = Q p m A Aᶜ hA hAc t' U - Q p m A Aᶜ hA hAc s' U))
    by_cases hdr : U ∈ ambGood p m hA r Th Lh →
        (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
          r - (Lh : ℤ) ≤ runMaxA p m U hA n0 →
            runMaxA p m U hA n0 ≤ r →
              WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
                -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
                    ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) +
                  (2 * p - 1) / ((A.card : ℕ) : ℝ) *
                    ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                      Real.sqrt (Lh * Real.sqrt Lh)) +
                  (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U)
    · by_cases hQ : ∀ s' t' : ℕ, s' ≤ t' →
          (∀ k, s' ≤ k → k < t' → GoodW p m k A Aᶜ hA B U) →
          LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s' + j)) (t' - s') U
            = Q p m A Aᶜ hA hAc t' U - Q p m A Aᶜ hA hAc s' U
      · left
        have hd := hdr hgood hsep hrec.1 hrec.2
        have hQ' := hQ s t hst (fun k hk hkt => hgoodW k (Finset.mem_Ico.mpr ⟨hk, hkt⟩))
        have hgt : ε < LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) (t - s) U := by
          linarith
        exact ⟨t - s, le_rfl, le_trans (le_of_lt hgt) (le_abs_self _)⟩
      · exact Or.inr (Or.inr hQ)
    · exact Or.inr (Or.inl hdr)
  -- the two exceptional sets are null
  have hnull1 : (arrayMeasure N).real {U : Array N | ¬ (U ∈ ambGood p m hA r Th Lh →
        (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
          r - (Lh : ℤ) ≤ runMaxA p m U hA n0 →
            runMaxA p m U hA n0 ≤ r →
              WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
                -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
                    ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) +
                  (2 * p - 1) / ((A.card : ℕ) : ℝ) *
                    ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                      Real.sqrt (Lh * Real.sqrt Lh)) +
                  (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U))} = 0 := by
    rw [MeasureTheory.measureReal_eq_zero_iff, ← MeasureTheory.ae_iff]
    exact hdrift
  have hnull2 : (arrayMeasure N).real {U : Array N | ¬ (∀ s' t' : ℕ, s' ≤ t' →
        (∀ k, s' ≤ k → k < t' → GoodW p m k A Aᶜ hA B U) →
        LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s' + j)) (t' - s') U
          = Q p m A Aᶜ hA hAc t' U - Q p m A Aᶜ hA hAc s' U)} = 0 := by
    rw [MeasureTheory.measureReal_eq_zero_iff, ← MeasureTheory.ae_iff]
    exact hQeq
  have hN : (arrayMeasure N).real
      ({U : Array N | ¬ (U ∈ ambGood p m hA r Th Lh →
          (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
            r - (Lh : ℤ) ≤ runMaxA p m U hA n0 →
              runMaxA p m U hA n0 ≤ r →
                WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
                  -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
                      ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) +
                    (2 * p - 1) / ((A.card : ℕ) : ℝ) *
                      ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                        Real.sqrt (Lh * Real.sqrt Lh)) +
                    (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U))}
        ∪ {U : Array N | ¬ (∀ s' t' : ℕ, s' ≤ t' →
            (∀ k, s' ≤ k → k < t' → GoodW p m k A Aᶜ hA B U) →
            LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s' + j)) (t' - s') U
              = Q p m A Aᶜ hA hAc t' U - Q p m A Aᶜ hA hAc s' U)}) = 0 := by
    have hle := MeasureTheory.measureReal_union_le
      (μ := arrayMeasure N)
      {U : Array N | ¬ (U ∈ ambGood p m hA r Th Lh →
          (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
            r - (Lh : ℤ) ≤ runMaxA p m U hA n0 →
              runMaxA p m U hA n0 ≤ r →
                WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
                  -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
                      ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) +
                    (2 * p - 1) / ((A.card : ℕ) : ℝ) *
                      ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                        Real.sqrt (Lh * Real.sqrt Lh)) +
                    (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U))}
      {U : Array N | ¬ (∀ s' t' : ℕ, s' ≤ t' →
          (∀ k, s' ≤ k → k < t' → GoodW p m k A Aᶜ hA B U) →
          LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s' + j)) (t' - s') U
            = Q p m A Aᶜ hA hAc t' U - Q p m A Aᶜ hA hAc s' U)}
    rw [hnull1, hnull2, add_zero] at hle
    have h0 : 0 ≤ (arrayMeasure N).real
        ({U : Array N | ¬ (U ∈ ambGood p m hA r Th Lh →
            (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
              r - (Lh : ℤ) ≤ runMaxA p m U hA n0 →
                runMaxA p m U hA n0 ≤ r →
                  WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
                    -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
                        ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) +
                      (2 * p - 1) / ((A.card : ℕ) : ℝ) *
                        ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                          Real.sqrt (Lh * Real.sqrt Lh)) +
                      (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U))}
          ∪ {U : Array N | ¬ (∀ s' t' : ℕ, s' ≤ t' →
              (∀ k, s' ≤ k → k < t' → GoodW p m k A Aᶜ hA B U) →
              LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s' + j)) (t' - s') U
                = Q p m A Aᶜ hA hAc t' U - Q p m A Aᶜ hA hAc s' U)}) := by positivity
    linarith
  -- conclude
  have hmono : (arrayMeasure N).real {U : Array N |
        U ∈ ambGood p m hA r Th Lh ∧
        (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) ∧
        (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA B U) ∧
        (r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r) ∧
        (-((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
            ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ)
          + (2 * p - 1) / ((A.card : ℕ) : ℝ) *
              ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                Real.sqrt (Lh * Real.sqrt Lh))
          + ε < WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc)}
      ≤ (arrayMeasure N).real {U : Array N | ∃ k ≤ t - s,
            ε ≤ |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U|} := by
    have h1 : (arrayMeasure N).real {U : Array N |
        U ∈ ambGood p m hA r Th Lh ∧
        (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) ∧
        (∀ n ∈ Finset.Ico s t, GoodW p m n A Aᶜ hA B U) ∧
        (r - (Lh : ℤ) ≤ runMaxA p m U hA n0 ∧ runMaxA p m U hA n0 ≤ r) ∧
        (-((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
            ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ)
          + (2 * p - 1) / ((A.card : ℕ) : ℝ) *
              ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                Real.sqrt (Lh * Real.sqrt Lh))
          + ε < WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc)}
        ≤ (arrayMeasure N).real
          ({U : Array N | ∃ k ≤ t - s,
              ε ≤ |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U|}
            ∪ ({U : Array N | ¬ (U ∈ ambGood p m hA r Th Lh →
                (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
                  r - (Lh : ℤ) ≤ runMaxA p m U hA n0 →
                    runMaxA p m U hA n0 ≤ r →
                      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
                        -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
                            ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) +
                          (2 * p - 1) / ((A.card : ℕ) : ℝ) *
                            ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                              Real.sqrt (Lh * Real.sqrt Lh)) +
                          (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U))}
              ∪ {U : Array N | ¬ (∀ s' t' : ℕ, s' ≤ t' →
                  (∀ k, s' ≤ k → k < t' → GoodW p m k A Aᶜ hA B U) →
                  LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s' + j)) (t' - s') U
                    = Q p m A Aᶜ hA hAc t' U - Q p m A Aᶜ hA hAc s' U)})) :=
      MeasureTheory.measureReal_mono hsub (by finiteness)
    have h2 : (arrayMeasure N).real
          ({U : Array N | ∃ k ≤ t - s,
              ε ≤ |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U|}
            ∪ ({U : Array N | ¬ (U ∈ ambGood p m hA r Th Lh →
                (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
                  r - (Lh : ℤ) ≤ runMaxA p m U hA n0 →
                    runMaxA p m U hA n0 ≤ r →
                      WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
                        -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
                            ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) +
                          (2 * p - 1) / ((A.card : ℕ) : ℝ) *
                            ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                              Real.sqrt (Lh * Real.sqrt Lh)) +
                          (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U))}
              ∪ {U : Array N | ¬ (∀ s' t' : ℕ, s' ≤ t' →
                  (∀ k, s' ≤ k → k < t' → GoodW p m k A Aᶜ hA B U) →
                  LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s' + j)) (t' - s') U
                    = Q p m A Aᶜ hA hAc t' U - Q p m A Aᶜ hA hAc s' U)}))
        ≤ (arrayMeasure N).real {U : Array N | ∃ k ≤ t - s,
              ε ≤ |LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s + j)) k U|}
          + (arrayMeasure N).real
              ({U : Array N | ¬ (U ∈ ambGood p m hA r Th Lh →
                  (∀ n ∈ Finset.Ico s t, SepSet p m n A Aᶜ U) →
                    r - (Lh : ℤ) ≤ runMaxA p m U hA n0 →
                      runMaxA p m U hA n0 ≤ r →
                        WA p m U t A Aᶜ hA hAc - WA p m U s A Aᶜ hA hAc ≤
                          -((2 * p - 1) * (1 - p) ^ ((2 * m - 1) * A.card) / ((A.card : ℕ) : ℝ)) *
                              ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) +
                            (2 * p - 1) / ((A.card : ℕ) : ℝ) *
                              ((2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
                                Real.sqrt (Lh * Real.sqrt Lh)) +
                            (Q p m A Aᶜ hA hAc t U - Q p m A Aᶜ hA hAc s U))}
                ∪ {U : Array N | ¬ (∀ s' t' : ℕ, s' ≤ t' →
                    (∀ k, s' ≤ k → k < t' → GoodW p m k A Aᶜ hA B U) →
                    LocMart.psum (fun j => dQT p m A Aᶜ hA hAc B (s' + j)) (t' - s') U
                      = Q p m A Aᶜ hA hAc t' U - Q p m A Aᶜ hA hAc s' U)}) :=
      MeasureTheory.measureReal_union_le _ _
    have h3 := hN
    linarith
  exact le_trans hmono hdev

end LocGroupGamma
