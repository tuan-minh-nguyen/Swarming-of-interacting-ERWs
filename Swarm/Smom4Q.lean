/-
  **Consequences of `(Smom₄)` for the actual separated-group martingale `Q^{I,J}`.**

  `Smom4Main.hSmom4_actual` discharges the static fourth moment that
  `SwarmSiteDiff.mdiff_of_static_moment` / `Q_log_variance_of_static` take as a premise.  With
  `(Mpot)` already discharged in `SwarmMpot.hPot_actual'`, the whole `QVarBound` chain becomes
  unconditional for the actual array:

  * `mdiff_sep_actual`: the `(sep)`-supported form of `(Mdiff)`,
    `∫ 1_(sep) (siteDiff p m k I J)² ≤ K²·Csmom4·log⁴(k+2)`;
  * `Q_log_variance_actual`: `∫ (inc Q k)² ≤ (8 C₁ + 2 K² C₄) log⁴(k+2)`, together with
    `Integrable ((inc Q k)²)` — the paper's log-fourth variance estimate for `Q^{I,J}`;
  * `Qslln_actual`, `Q_running_max_actual`, `telescope_le_actual`: the paper's `(Qslln)`, its
    running-maximum form, and the `WA_t ≤ WA_s + εt` telescoped bound on intervals on which `(sep)`
    holds (the exact input of the leader-set induction of `(diam)` in
    `Swarm/LeaderDescent.lean`).

  Nothing about `(diam)`, the nested leader induction, `Ballistic`, `MainClaim`, the record law or
  a common speed is proved here: those consume `telescope_le_actual` and are separate.
-/
import Swarm.Smom4Main

set_option maxHeartbeats 3000000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SwarmSmom4

open Classical
open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmQVariance SwarmJointDrift SwarmSiteDiff SwarmMpot

variable {N : ℕ} {p : ℝ} {m : ℕ}

/-- **`(Mdiff)` in its `(sep)`-supported form, for the actual array.** -/
theorem mdiff_sep_actual (hp0 : 1 / 2 < p) (hp1 : p < 1)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) :
    ∀ k : ℕ, ∫ U, (if SepSet p m k I J U then (siteDiff p m k I J hI U) ^ 2 else 0)
        ∂(arrayMeasure N)
      ≤ ((((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * Csmom4 p m N)
          * Real.log ((k : ℝ) + 2) ^ 4 :=
  mdiff_of_static_moment hp0 hp1.le I J hI hJ hid (C₄ := Csmom4 p m N)
    (hSmom4_actual hp0 hp1 (m := m) hI)

/-- **The log-fourth variance estimate for the actual `Q^{I,J}`, unconditionally.** -/
theorem Q_log_variance_actual (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) :
    (∀ k : ℕ, Integrable
        (fun U => (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2) (arrayMeasure N))
      ∧ ∀ k : ℕ, ∫ U, (MartingaleLimit.inc (Q p m I J hI hJ) k U) ^ 2 ∂(arrayMeasure N)
        ≤ (8 * C1 p m N
            + 2 * ((((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * Csmom4 p m N))
          * (Real.log ((k : ℝ) + 2)) ^ 4 :=
  Q_log_variance_of_static hp0 hp1 m I J hI hJ hid
    (C1_pos hp0 hp1 m N).le (Csmom4_pos hp0 hp1 m N).le
    (fun k => hPot_actual' hp0 hp1 hI k) (hSmom4_actual hp0 hp1 hI)

/-- **The paper's `(Qslln)` for the actual `Q^{I,J}`, unconditionally.** -/
theorem Qslln_actual (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) :
    ∀ᵐ U ∂(arrayMeasure N), Tendsto (fun n => Q p m I J hI hJ n U / n) atTop (𝓝 0) := by
  have h := Q_log_variance_actual hp0 hp1 m I J hI hJ hid
  exact Qslln_of_log_variance hp0.le hp1.le m I J hI hJ h.1 h.2

/-- The running-maximum form of `(Qslln)` for the actual `Q^{I,J}`. -/
theorem Q_running_max_actual (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ((Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
        fun t => |Q p m I J hI hJ t U|) ≤ ε * (n : ℝ) := by
  have h := Q_log_variance_actual hp0 hp1 m I J hI hJ hid
  exact Q_running_max_of_log_variance hp0.le hp1.le m I J hI hJ h.1 h.2

/-- **The telescoped separated-group bound, for the actual array**: on every interval on which
`(sep)` holds, `WA_t ≤ WA_s + εt`.  This is the input consumed by the leader-set induction. -/
theorem telescope_le_actual (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ)
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, ∀ s : ℕ, s ≤ t →
      (∀ k, s ≤ k → k < t → SepSet p m k I J U) →
      WA p m U t I J hI hJ ≤ WA p m U s I J hI hJ + ε * (t : ℝ) := by
  have htel := telescope_of_sep hp0 hp1 m I J hI hJ hid
  have hrun := Q_running_max_actual hp0 hp1 m I J hI hJ hid
  filter_upwards [htel, hrun] with U htelU hrunU
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hev := hrunU (ε / 2) hε2
  filter_upwards [hev] with t ht s hst hsep
  have ht1 : Q p m I J hI hJ t U ≤ ε / 2 * (t : ℝ) := by
    have h := ht
    have h2 := Finset.le_sup' (fun r => |Q p m I J hI hJ r U|)
      (Finset.mem_range.mpr (Nat.lt_succ_self t)) (s := Finset.range (t + 1))
    have h3 : |Q p m I J hI hJ t U| ≤ ε / 2 * (t : ℝ) := le_trans h2 h
    linarith [le_abs_self (Q p m I J hI hJ t U)]
  have hs1 : -(ε / 2 * (t : ℝ)) ≤ Q p m I J hI hJ s U := by
    have h2 := Finset.le_sup' (fun r => |Q p m I J hI hJ r U|)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hst)) (s := Finset.range (t + 1))
    have h3 : |Q p m I J hI hJ s U| ≤ ε / 2 * (t : ℝ) := le_trans h2 ht
    have h4 := neg_abs_le (Q p m I J hI hJ s U)
    linarith
  have hW := htelU s t hst hsep
  nlinarith [Nat.cast_nonneg (α := ℝ) s]

/-- **Block-uniform form.**  A single constant
`Cq p m N = 8·C1 p m N + 2·K²·Csmom4 p m N` works for *every* nondegenerate block `A`
simultaneously (the pair is `(A, Aᶜ)`), with the two conclusions of
`Q_log_variance_actual`.  This is the shape of `LogVarBound` in
`areas/martingale` / the `(diam)` assembly: the constant does not depend on the block, only on
`p`, `m` and `N` (the paper's `C_s(N,m,p)`), so no `N`-independence is claimed for it. -/
noncomputable def Cq (p : ℝ) (m N : ℕ) : ℝ :=
  8 * C1 p m N + 2 * ((((2 * p - 1) / p) * (N : ℝ) * 8) ^ 2 * Csmom4 p m N)

theorem Q_log_variance_uniform_blocks (hp0 : 1 / 2 < p) (hp1 : p < 1) (m : ℕ) :
    (∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (k : ℕ), Integrable
        (fun U => (MartingaleLimit.inc (Q p m A Aᶜ hA hAc) k U) ^ 2) (arrayMeasure N))
      ∧ ∀ (A : Finset (Fin N)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (k : ℕ),
        ∫ U, (MartingaleLimit.inc (Q p m A Aᶜ hA hAc) k U) ^ 2 ∂(arrayMeasure N)
          ≤ Cq p m N * (Real.log ((k : ℝ) + 2)) ^ 4 := by
  constructor
  · intro A hA hAc k
    exact (Q_log_variance_actual hp0 hp1 m A Aᶜ hA hAc disjoint_compl_right).1 k
  · intro A hA hAc k
    have h := (Q_log_variance_actual hp0 hp1 m A Aᶜ hA hAc disjoint_compl_right).2 k
    exact h

end SwarmSmom4
