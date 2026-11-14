/-
  **(loccoord) discharged on the actual `(locsum)` event.**

  `LocCoord` proves the deterministic chain

      H_n^B(b0) - H_n^B(a0) = Σ_{a0 ≤ x < b0} h_n^B(x) ≤ Σ_{a0 ≤ x < b0} h_i(x),   i ∈ B,

  for `b0 ≤ M_n^i`, and turns the `(locsum)` square bound into a linear bound.  The only
  stochastic input is `(locsum)`, which the campaign has already proved **for the actual
  harmonic functions** as `LocSumR1.array_locsum_h`:

      Σ_{a0 ≤ x < b0} h_j(x)² ≤ 2C(b0-a0) + 6Cβ,     β = betaT (xOf L),

  off `LsBad N p m C L A`, a set of `arrayMeasure` at most `exp(-c L^{1/16})`.

  This file feeds that event into `LocCoord.loccoord_average`.  Because `(locsum)` is stated
  for `hof (siteMarks j)` while the model potential of `SepGroup` is `hfix (omegaN j)`, the
  bridge `LocCoord.hfix_omegaN_eq_hof` is what makes the two composable.

  Conclusion (the paper's `(loccoord)`, two-time changing-weight form, on one explicit event):
  for every group `B`, every leader `i ∈ B`, every `s ≤ t`, and every window interval
  `[a0,b0) ⊆ [A, A+L)` with `b0 ≤ M_t^i`,

      average_{k∈B} (H_t^B(X_t^k) - H_s^B(X_s^k))
        ≤ ((2C+1)/2)(b0-a0) + 3C β.

  No `sorry`, no axioms beyond `propext, Classical.choice, Quot.sound`.
-/
import Swarm.LocCoord
import Swarm.R4Assemble

set_option linter.unusedVariables false

open Finset
open scoped BigOperators

namespace Loccoord

noncomputable section

/-- **(loccoord) on the actual `(locsum)` event.** -/
theorem loccoord_on_locsum_event {N : ℕ} {p : ℝ} (hp1 : (1 : ℝ) / 2 < p) (hp2 : p < 1)
    {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC1 : 1 ≤ C)
    (hCM : LocSum.Mb p (LocSumAct.qOf p m) < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ A : ℕ, L ≤ A →
      Swarming.Uniform.arrayMeasure N (LocSumR1.LsBad N p m C L A)
          ≤ ENNReal.ofReal (Real.exp (-c * LocSumAct.xOf L)) ∧
      ∀ U : Swarming.Uniform.Array N, U ∉ LocSumR1.LsBad N p m C L A →
        ∀ (B : Finset (Fin N)), B.Nonempty → ∀ i, i ∈ B →
        ∀ s t : ℕ, s ≤ t →
        ∀ a0 b0 : ℕ, A ≤ a0 → b0 ≤ A + L → a0 ≤ b0 →
        (b0 : ℤ) ≤ Swarming.Trajectory.runMax p m U i t →
        (∀ k ∈ B, (a0 : ℤ) ≤ SepGroup.Model.X p m U s k) →
        (∀ k ∈ B, SepGroup.Model.X p m U t k ≤ (b0 : ℤ)) →
        Swarming.Group.average B (fun k =>
            SepGroup.Model.HA p m U t B (SepGroup.Model.X p m U t k)
              - SepGroup.Model.HA p m U s B (SepGroup.Model.X p m U s k))
          ≤ ((2 * C + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ))
              + 3 * C * ((LocSumAct.betaT (LocSumAct.xOf L) : ℕ) : ℝ) := by
  obtain ⟨c, hc, L₀, hL⟩ := LocSumR1.array_locsum_h (N := N) hp1 hp2 hm hC1 hCM
  refine ⟨c, hc, L₀, ?_⟩
  intro L hLbig A hA
  obtain ⟨hmeas, hbound⟩ := hL L hLbig A hA
  refine ⟨hmeas, ?_⟩
  intro U hU B hB i hiB s t hst a0 b0 hAa hbL hab hbR hXa hXb
  have hp : 1 / 2 ≤ p := le_of_lt hp1
  have hp1' : p ≤ 1 := le_of_lt hp2
  have hp0 : p ≠ 0 := by linarith
  set β : ℝ := ((LocSumAct.betaT (LocSumAct.xOf L) : ℕ) : ℝ) with hβdef
  -- the bridge `hfix (omegaN i) = hof (siteMarks i)`, so `(locsum)` applies to `h_i`
  have hbridge : ∀ x : ℕ, Cookie.hfix (SepGroup.Model.omegaN p m U i) x
      = SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U i) x :=
    fun x => hfix_omegaN_eq_hof hp0 i x
  have hsum_hof := hbound U hU i a0 b0 hAa hbL hab
  have hsum : ∑ x ∈ Finset.Ico a0 b0,
      (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
      ≤ 2 * C * ((b0 : ℝ) - (a0 : ℝ)) + 6 * C * β := by
    have hcongr : ∑ x ∈ Finset.Ico a0 b0,
        (Cookie.hfix (SepGroup.Model.omegaN p m U i) x) ^ 2
        = ∑ x ∈ Finset.Ico a0 b0,
          (SwarmMarks.hof p (SwarmLogRatio.siteMarks p m U i) x) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [hbridge x]
    rw [hcongr]
    rw [hβdef]
    exact hsum_hof
  have hmain := loccoord_average (p := p) (m := m) (N := N) hp hp1' U hst hB hiB hab
    hXa hXb hbR (K := 2 * C) (β := 3 * β) (by linarith) (by positivity) (by
      rw [hβdef] at hsum ⊢
      linarith)
  have harith : ((2 * C + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ)) + ((2 * C) / 2) * (3 * β)
      = ((2 * C + 1) / 2) * ((b0 : ℝ) - (a0 : ℝ)) + 3 * C * β := by ring
  rw [harith] at hmain
  exact hmain

end

end Loccoord
