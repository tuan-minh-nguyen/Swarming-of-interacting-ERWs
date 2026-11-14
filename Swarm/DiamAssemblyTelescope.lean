/-
# Downstream diameter assembly (direction 4): uniform-in-block telescoped drift

The deterministic nested-leader reduction consumes, as its single `o(n)` potential input at a
separated leading block `A` with reset time `s`,

  `W^{A,A^c}_n <= W^{A,A^c}_s + o(n)`.

`SwarmJointDrift` proves the *conditional drift* `E[W_{n+1}-W_n | F_n] <= 0` on `(sep)`, the
martingale `Q^{I,J}` and — conditional on the paper's log-fourth variance estimate — its strong
law and the running-maximum form.  What was missing downstream is the *uniformity over blocks and
over the reset time*: the strong law is stated block by block, the reset time is a random index,
and the deterministic reduction needs all of it simultaneously for every leading block.

This module supplies exactly that composition.  Its only stochastic input is the paper's
log-fourth variance estimate on the `Q^{A,A^c}` increments, taken here as an explicit, named,
block-uniform hypothesis `LogVarBound`; nothing else is assumed.
-/
import Swarm.DiamAssemblyBridge

open Filter Finset MeasureTheory Topology
open scoped BigOperators

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup SepGroup.Model Cookie

namespace DiamAssembly

variable {N : ℕ}

/-! ## 1. The single stochastic input: the paper's log-fourth variance estimate

The paper's `(Qslln)` is proved in `SwarmJointDrift.Qslln_of_log_variance` /
`Q_running_max_of_log_variance` from the estimate `E[(dQ_k)^2] <= C log^4(k+2)`.  Downstream we
need it for every block `A` simultaneously, with a single constant `C` that does not depend on the
block (and, by construction, does not depend on `N` either: it is an input). -/

/-- The paper's log-fourth variance estimate for the separated-group martingale `Q^{A,A^c}`,
uniformly over all nondegenerate blocks `A`. -/
def LogVarBound (p : ℝ) (m : ℕ) (C : ℝ) : Prop :=
  (∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (k : ℕ), Integrable
    (fun U => (MartingaleLimit.inc (SwarmJointDrift.Q p m A Aᶜ hA hAc) k U) ^ 2)
    (arrayMeasure N)) ∧
  ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (k : ℕ),
    ∫ U, (MartingaleLimit.inc (SwarmJointDrift.Q p m A Aᶜ hA hAc) k U) ^ 2 ∂(arrayMeasure N)
      ≤ C * (Real.log ((k : ℝ) + 2)) ^ 4

/-! ## 2. The telescoped drift for one fixed block, uniform in the starting time -/

/-- **Telescoped `(Wdrift)` with the `Q` correction, uniform in `s`.**  For a fixed nondegenerate,
disjoint pair `(I,J)`: almost surely, for every `ε > 0` and all large `n`, every `s <= n` such that
`(sep)` holds at every integer time of `[s,n)` satisfies `W_n <= W_s + ε n`.

The `o(n)` gain is the running maximum of `|Q^{I,J}|` at time `n`, which dominates `|Q_t|` for
every `t <= n` — this is what makes the bound uniform in the starting time `s`, and hence
applicable at the (random) reset time. -/
theorem ae_telescope_block {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) {C : ℝ}
    (hint : ∀ k : ℕ, Integrable
      (fun U => (MartingaleLimit.inc (SwarmJointDrift.Q p m I J hI hJ) k U) ^ 2) (arrayMeasure N))
    (hvar : ∀ k : ℕ, ∫ U, (MartingaleLimit.inc (SwarmJointDrift.Q p m I J hI hJ) k U) ^ 2
      ∂(arrayMeasure N) ≤ C * (Real.log ((k : ℝ) + 2)) ^ 4) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, s ≤ n →
      (∀ k, s ≤ k → k < n → SwarmJointDrift.SepSet p m k I J U) →
      SepGroup.Model.WA p m U n I J hI hJ ≤ SepGroup.Model.WA p m U s I J hI hJ + ε * (n : ℝ) := by
  have hprob := arrayMeasure_isProbabilityMeasure N
  have := hprob
  have hp : 1 / 2 ≤ p := le_of_lt hp0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have htel := SwarmJointDrift.telescope_of_sep hp0 hp1 m I J hI hJ hid
  have hrun := SwarmJointDrift.Q_running_max_of_log_variance hp hp1' m I J hI hJ hint hvar
  filter_upwards [htel, hrun] with U hUtele hUrun
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [hUrun (ε / 2) hε2] with n hn s hs hsep
  have h1 : |SwarmJointDrift.Q p m I J hI hJ n U| ≤ ε / 2 * (n : ℝ) :=
    le_trans (le_sup' (fun t => |SwarmJointDrift.Q p m I J hI hJ t U|)
      (mem_range.mpr (Nat.lt_succ_self n))) hn
  have h2 : |SwarmJointDrift.Q p m I J hI hJ s U| ≤ ε / 2 * (n : ℝ) :=
    le_trans (le_sup' (fun t => |SwarmJointDrift.Q p m I J hI hJ t U|)
      (mem_range.mpr (Nat.lt_succ_of_le hs))) hn
  have h3 := hUtele s n hs hsep
  have h4 : -(SwarmJointDrift.Q p m I J hI hJ s U) ≤ |SwarmJointDrift.Q p m I J hI hJ s U| :=
    neg_le_abs _
  have h5 : SwarmJointDrift.Q p m I J hI hJ n U ≤ |SwarmJointDrift.Q p m I J hI hJ n U| :=
    le_abs_self _
  nlinarith [h1, h2, h3, h4, h5]

/-! ## 3. Uniformity over all blocks -/

/-- The same telescoped bound for the totalised potential `Wtot`, for one block. -/
theorem ae_Wtot_telescope {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) {C : ℝ}
    (hC : LogVarBound (N := N) p m C) (A : Finset (Fin N)) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, s ≤ n →
      (∀ k, s ≤ k → k < n → SwarmJointDrift.SepSet p m k A Aᶜ U) →
      Wtot p m U n A ≤ Wtot p m U s A + ε * (n : ℝ) := by
  by_cases h : A.Nonempty ∧ Aᶜ.Nonempty
  · have hb := ae_telescope_block (N := N) hp0 hp1 m A Aᶜ h.1 h.2 disjoint_compl_right
      (hC.1 A h.1 h.2) (hC.2 A h.1 h.2)
    filter_upwards [hb] with U hU ε hε
    filter_upwards [hU ε hε] with n hn s hs hsep
    rw [Wtot_eq p m U n h.1 h.2, Wtot_eq p m U s h.1 h.2]
    exact hn s hs hsep
  · filter_upwards with U ε hε
    filter_upwards with n s hs hsep
    rw [Wtot_eq_zero p m U n h, Wtot_eq_zero p m U s h]
    positivity

/-- **Uniformity over blocks and over the starting time.**  Almost surely, for every `ε > 0` and
all large `n`, *every* block `A` and *every* `s <= n` on whose interval `[s,n)` the condition
`(sep)` holds for the pair `(A, Aᶜ)` satisfy the telescoped drift bound. -/
theorem ae_Wtot_telescope_all {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) {C : ℝ}
    (hC : LogVarBound (N := N) p m C) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ (s : ℕ), s ≤ n →
      ∀ A : Finset (Fin N),
      (∀ k, s ≤ k → k < n → SwarmJointDrift.SepSet p m k A Aᶜ U) →
      Wtot p m U n A ≤ Wtot p m U s A + ε * (n : ℝ) := by
  have hall : ∀ᵐ U ∂(arrayMeasure N),
      ∀ A : Finset (Fin N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, s ≤ n →
        (∀ k, s ≤ k → k < n → SwarmJointDrift.SepSet p m k A Aᶜ U) →
        Wtot p m U n A ≤ Wtot p m U s A + ε * (n : ℝ) :=
    MeasureTheory.ae_all_iff.mpr (fun A => ae_Wtot_telescope hp0 hp1 m hC A)
  filter_upwards [hall] with U hU ε hε
  filter_upwards [Filter.eventually_all.mpr (fun A : Finset (Fin N) => hU A ε hε)] with n hn s hs A hsep
  exact hn A s hs hsep

/-! ## 4. The residual drift input of the nested-leader reduction, at the reset time -/

/-- **`htel` for the actual array.**  Almost surely, for every `ε > 0` and all large `n`, every
separated leading block `A` satisfies

  `W_n^{A,A^c} <= W_{resetTime A n}^{A,A^c} + ε n`.

This is exactly the `htel` hypothesis of `NestedLeader.spread_div_tendsto_zero_of_W`: the reset
time is the first time of the final separating run, so `(sep)` holds on `[resetTime A n, n)` and
the uniform telescoped drift of §3 applies. -/
theorem ae_htel_reset {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) {C : ℝ}
    (hC : LogVarBound (N := N) p m C) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset (Fin N)) (_hA : A.Nonempty) (_hAc : (univ \ A).Nonempty),
        NestedLeader.Leading (fun i => XA p m U i n) A →
        LeaderDescent.SepMax (XA p m U) A n →
        Wtot p m U n A ≤
          Wtot p m U (LeaderDescent.resetTime (XA p m U) A n) A + ε * (n : ℝ) := by
  filter_upwards [ae_Wtot_telescope_all hp0 hp1 m hC] with U hU ε hε
  filter_upwards [hU ε hε] with n hn A hA hAc hlead hsep
  have hs : LeaderDescent.resetTime (XA p m U) A n ≤ n :=
    LeaderDescent.resetTime_minimal (XA p m U) A n (fun t ht1 ht2 => by
      rw [le_antisymm ht2 ht1]; exact hsep)
  have hsep' : ∀ k, LeaderDescent.resetTime (XA p m U) A n ≤ k → k < n →
      SwarmJointDrift.SepSet p m k A Aᶜ U := fun k hk hkn =>
    (sepMax_iff_sep p m U A k).mp
      (LeaderDescent.resetTime_spec (XA p m U) A n k hk (le_of_lt hkn))
  exact hn (LeaderDescent.resetTime (XA p m U) A n) hs A hsep'

end DiamAssembly
