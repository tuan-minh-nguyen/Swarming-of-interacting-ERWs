/-
# The `GoodW`/`GoodStep` maximal deviation estimates without the Chernoff side condition

`LocGroupWindow.measure_deviation_goodW_le` and
`LocMoveLocal.measure_max_abs_Lcum_window_le` both require `ε ≤ 4 (t-s) B`.  At the paper's local
scale that is `L ≤ t-s`, the restriction recorded in `LOC_MOVE_COMPOSE.md`.  Using
`WCJFSharp.measure_max_abs_psum_ge_le_sharp` (no side condition, sharp exponent) we obtain both
estimates with **no** hypothesis on `ε` and with the exponent improved from
`-ε²/(4 K (2B)²)` to `-ε²/(2 K (2B)²)`:

* `measure_deviation_goodW_le_sharp` — the `Γ`-drift half's martingale (`dQT`);
* `measure_max_abs_Lcum_window_le_sharp` — the max-growth half's martingale (`Lcum`).

The statements are otherwise identical (same carrier event, same truncated process, same union
factor `K+1`).  Everything is on the actual model measure `arrayMeasure N`.

No `sorry`, no new axiom, no change of model parameters.
-/
import Swarm.AzumaSharp
import Swarm.LocGroupWindow
import Swarm.LocMoveLocalProfile
import Swarm.PaperScale

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace WCJFSharp

open Swarming Swarming.Uniform Swarming.Trajectory Swarming.Model SepGroup.Model Cookie
open SwarmJointDrift LocGroupQ LocGroupWindow LocMoveMart LocMoveLocal Swarming.Enl Loccoord

variable {N : ℕ}

/-! ## 1. The `Γ`-drift half (`dQT`) -/

/-- **Maximal deviation of the `GoodW`-truncated `Γ`-martingale, every `ε > 0`.** -/
theorem measure_deviation_goodW_le_sharp {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 < B) {s K : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real
      {U : Array N | ∃ k ≤ K,
        ε ≤ |LocMart.psum (fun j => dQT p m I J hI hJ B (s + j)) k U|}
      ≤ 2 * ((K : ℝ) + 1) *
          Real.exp (-(ε ^ 2) / (2 * ((K : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hp1' : p ≤ 1 := le_of_lt hp1
  set E : ℝ := stepEnv (N := N) p B with hE
  have hEpos : 0 < E := stepEnv_pos hp0 hp1' hB
  set S : ℝ := (K : ℝ) * (2 * E) ^ 2 with hS
  have hSpos : 0 < S := by
    have h2 : (0 : ℝ) < 2 * E := by linarith
    rw [hS]; positivity
  have hprox : LocMax.proxy (fun _ : ℕ => 2 * E) K ≤ S := by
    have h : LocMax.proxy (fun _ : ℕ => 2 * E) K = (K : ℝ) * (2 * E) ^ 2 := by
      simp only [LocMax.proxy, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h, hS]
  have hmeas : ∀ k, StronglyMeasurable[(shiftedFilt (N := N) p m s) (k + 1)]
      (fun U => dQT p m I J hI hJ B (s + k) U) := by
    intro k
    exact stronglyMeasurable_dQT p m (s + k) I J hI hJ B
  have hcpos : ∀ k, 0 < (fun _ : ℕ => 2 * E) k := fun k => by
    have h2 : (0 : ℝ) < 2 * E := by linarith
    exact h2
  have hbdd : ∀ k, ∀ᵐ U ∂(arrayMeasure N),
      |(fun U => dQT p m I J hI hJ B (s + k) U) U| ≤ (fun _ : ℕ => 2 * E) k := by
    intro k
    simpa only [hE] using ae_abs_dQT_le (N := N) hp0 hp1' I J hI hJ hid hB.le (n := s + k)
  have hmean : ∀ k,
      (arrayMeasure N)[(fun U => dQT p m I J hI hJ B (s + k) U)
        | ↑((shiftedFilt (N := N) p m s) k)] =ᵐ[arrayMeasure N] 0 := by
    intro k
    exact condExp_dQT hp0.le hp1' m (s + k) I J hI hJ B
  have key := measure_max_abs_psum_ge_le_sharp (μ := arrayMeasure N)
    (ℱ := shiftedFilt (N := N) p m s)
    (ξ := fun k U => dQT p m I J hI hJ B (s + k) U) (c := fun _ : ℕ => 2 * E)
    (n := K) (S := S) hmeas (fun k => (hcpos k).le) hbdd hmean hSpos hprox hε
  rw [hS, hE] at key
  exact key

/-! ## 2. The max-growth half (`Lcum`) -/

/-- **Maximal deviation of the truncated maximum martingale, every `ε > 0`.** -/
theorem measure_max_abs_Lcum_window_le_sharp {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (J : Finset (Fin N)) (hJ : J.Nonempty) {B : ℝ} (hB : 0 < B)
    {s K : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real
        {U | ∃ k ≤ K, ε ≤ |Lcum p m (s + k) J hJ B U - Lcum p m s J hJ B U|}
      ≤ 2 * ((K : ℝ) + 1) * Real.exp (-(ε ^ 2) / (2 * ((K : ℝ) * (2 * B) ^ 2))) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hS : 0 < (K : ℝ) * (2 * B) ^ 2 := by positivity
  have hprox : LocMax.proxy (fun _ : ℕ => 2 * B) K ≤ (K : ℝ) * (2 * B) ^ 2 := by
    simp only [LocMax.proxy, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact le_rfl
  have hmeas : ∀ k, StronglyMeasurable[(LocMax.shiftFilt N p m s) (k + 1)]
      (winLInc p m s J hJ B k) := by
    intro k
    exact stronglyMeasurable_LdM p m (s + k) J hJ B
  have hbdd : ∀ k, ∀ᵐ U ∂(arrayMeasure N), |winLInc p m s J hJ B k U| ≤ (fun _ : ℕ => 2 * B) k := by
    intro k
    simpa only [winLInc] using abs_LdM_le (p := p) (m := m) (n := s + k) hp hp1 hJ hB.le
  have hmean : ∀ k, (arrayMeasure N)[winLInc p m s J hJ B k
      | ↑((LocMax.shiftFilt N p m s) k)] =ᵐ[arrayMeasure N] 0 := by
    intro k
    exact condExp_LdM hp hp1 m (s + k) J hJ B
  have hmain := measure_max_abs_psum_ge_le_sharp (μ := arrayMeasure N)
    (ℱ := LocMax.shiftFilt N p m s) (ξ := winLInc p m s J hJ B)
    (c := fun _ : ℕ => 2 * B) (n := K) (S := (K : ℝ) * (2 * B) ^ 2)
    hmeas (fun k => by positivity) hbdd hmean hS hprox hε
  have hset : {U : Array N | ∃ k ≤ K, ε ≤ |LocMart.psum (winLInc p m s J hJ B) k U|} =
      {U : Array N | ∃ k ≤ K,
        ε ≤ |Lcum p m (s + k) J hJ B U - Lcum p m s J hJ B U|} := by
    ext U
    constructor
    · rintro ⟨k, hk, hdev⟩
      exact ⟨k, hk, by rwa [psum_winLInc] at hdev⟩
    · rintro ⟨k, hk, hdev⟩
      exact ⟨k, hk, by rwa [psum_winLInc]⟩
  rw [hset] at hmain
  exact hmain

/-! ## 3. The one-sided `(locgroup)` advance bound, no union factor -/

/-- **One-sided advance bound on the `GoodW` window, every `ε > 0`.**  On the event that `GoodW`
holds at *every* time of `[s, s+K)` and the advance of `W^{I,J}` exceeds `ε`, the measure is at
most `exp (-ε²/(2 K (2 stepEnv)²))` — one-sided, no union factor, no side condition.  This is the
shape the advance/defect chain consumes; the accepted `measure_goodW_window_le` pays an extra
`2(K+1)` factor and requires `ε ≤ 4 K stepEnv`. -/
theorem measure_goodW_advance_le {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 < B) {s K : ℕ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    (arrayMeasure N).real
      {U : Array N |
        (∀ k ∈ Finset.Ico s (s + K), GoodW p m k I J hI B U) ∧
          ε ≤ WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ}
      ≤ Real.exp (-(ε ^ 2) / (2 * ((K : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))) := by
  haveI hprob : IsProbabilityMeasure (arrayMeasure N) := arrayMeasure_isProbabilityMeasure N
  have hp1' : p ≤ 1 := le_of_lt hp1
  set E : ℝ := stepEnv (N := N) p B with hE
  have hEpos : 0 < E := stepEnv_pos hp0 hp1' hB
  have hSpos : 0 < (K : ℝ) * (2 * E) ^ 2 := by
    have h2 : (0 : ℝ) < 2 * E := by linarith
    have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
    positivity
  have hprox : LocMax.proxy (fun _ : ℕ => 2 * E) K ≤ (K : ℝ) * (2 * E) ^ 2 := by
    have h : LocMax.proxy (fun _ : ℕ => 2 * E) K = (K : ℝ) * (2 * E) ^ 2 := by
      simp only [LocMax.proxy, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h]
  have hmom := measure_psum_ge_le_sharp (μ := arrayMeasure N)
    (ℱ := shiftedFilt (N := N) p m s)
    (ξ := fun k U => dQT p m I J hI hJ B (s + k) U) (c := fun _ : ℕ => 2 * E)
    (n := K) (S := (K : ℝ) * (2 * E) ^ 2)
    (fun k => stronglyMeasurable_dQT p m (s + k) I J hI hJ B)
    (fun k => (show (0 : ℝ) ≤ 2 * E by linarith))
    (fun k => by
      simpa only [hE] using ae_abs_dQT_le (N := N) hp0 hp1' I J hI hJ hid hB.le (n := s + k))
    (fun k => condExp_dQT hp0.le hp1' m (s + k) I J hI hJ B)
    hSpos hprox hε
  have htel := ae_telescope_goodW (N := N) hp0 hp1 (m := m) I J hI hJ hid B
  have hsub : {U : Array N |
        (∀ k ∈ Finset.Ico s (s + K), GoodW p m k I J hI B U) ∧
          ε ≤ WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ}
      ⊆ {U : Array N |
          ε ≤ LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U}
        ∪ {U : Array N | ¬ (∀ s K : ℕ,
            (∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) →
            WA p m U (s + K) I J hI hJ ≤ WA p m U s I J hI hJ
              + LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U)} := by
    intro U hU
    by_cases hb : (∀ s K : ℕ,
        (∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) →
        WA p m U (s + K) I J hI hJ ≤ WA p m U s I J hI hJ
          + LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U)
    · refine Or.inl ?_
      have hgood : ∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U := by
        intro k hk hkt
        exact hU.1 k (Finset.mem_Ico.mpr ⟨hk, hkt⟩)
      have h2 := hb s K hgood
      have h3 : ε ≤ WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ := hU.2
      have h4 : WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ
          ≤ LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U := by
        linarith only [h2]
      simp only [Set.mem_setOf_eq]
      linarith only [h3, h4]
    · exact Or.inr hb
  have hnull : (arrayMeasure N).real {U : Array N | ¬ (∀ s K : ℕ,
        (∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) →
        WA p m U (s + K) I J hI hJ ≤ WA p m U s I J hI hJ
          + LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U)} = 0 := by
    have h0 : (arrayMeasure N) {U : Array N | ¬ (∀ s K : ℕ,
        (∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) →
        WA p m U (s + K) I J hI hJ ≤ WA p m U s I J hI hJ
          + LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U)} = 0 := by
      rw [← MeasureTheory.ae_iff]
      exact htel
    rw [measureReal_def, h0]
    simp
  calc (arrayMeasure N).real {U : Array N |
        (∀ k ∈ Finset.Ico s (s + K), GoodW p m k I J hI B U) ∧
          ε ≤ WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ}
      ≤ (arrayMeasure N).real ({U : Array N |
            ε ≤ LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U}
          ∪ {U : Array N | ¬ (∀ s K : ℕ,
            (∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) →
            WA p m U (s + K) I J hI hJ ≤ WA p m U s I J hI hJ
              + LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U)}) :=
        measureReal_mono (μ := arrayMeasure N) hsub (measure_ne_top _ _)
    _ ≤ (arrayMeasure N).real {U : Array N |
            ε ≤ LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U}
          + (arrayMeasure N).real {U : Array N | ¬ (∀ s K : ℕ,
            (∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) →
            WA p m U (s + K) I J hI hJ ≤ WA p m U s I J hI hJ
              + LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U)} :=
        measureReal_union_le (μ := arrayMeasure N) _ _
    _ = (arrayMeasure N).real {U : Array N |
            ε ≤ LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U} := by
        have hz : (arrayMeasure N).real {U : Array N | ¬ (∀ s K : ℕ,
            (∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) →
            WA p m U (s + K) I J hI hJ ≤ WA p m U s I J hI hJ
              + LocMart.psum (fun k U => dQT p m I J hI hJ B (s + k) U) K U)} = 0 := hnull
        rw [hz]
        ring
    _ ≤ Real.exp (-(ε ^ 2) / (2 * ((K : ℝ) * (2 * stepEnv (N := N) p B) ^ 2))) := hmom

/-! ## 4. The deterministic one-step envelope over a good window -/

/-- **Pathwise envelope over a full good window.**  If `GoodW` holds at every time of
`[s, s+K)`, the whole change of `W^{I,J}` over the window is at most `K · stepEnv` in absolute
value — no probability, no martingale argument.  This is the paper's "the `C_T L^{3/4}` slack
covers the short windows by the deterministic one-step envelope": with `K · stepEnv p B ≤ L^{3/4}`
the deviation term is bounded outright. -/
theorem abs_WA_window_le_of_goodW {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p ≤ 1) {m : ℕ}
    (I J : Finset (Fin N)) (hI : I.Nonempty) (hJ : J.Nonempty) (hid : Disjoint I J)
    {B : ℝ} (hB : 0 ≤ B) {s K : ℕ} (U : Array N)
    (hgood : ∀ k, s ≤ k → k < s + K → GoodW p m k I J hI B U) :
    |WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ|
      ≤ (K : ℝ) * stepEnv (N := N) p B := by
  have henv0 : 0 ≤ stepEnv (N := N) p B := stepEnv_nonneg hp0 hp1 hB
  induction K with
  | zero => simp
  | succ K ih =>
    have hsplit : WA p m U (s + (K + 1)) I J hI hJ - WA p m U s I J hI hJ
        = (WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ)
          + (WA p m U (s + (K + 1)) I J hI hJ - WA p m U (s + K) I J hI hJ) := by ring
    have hstep : |WA p m U (s + (K + 1)) I J hI hJ - WA p m U (s + K) I J hI hJ|
        ≤ stepEnv (N := N) p B := by
      have hlast : GoodW p m (s + K) I J hI B U := by
        refine hgood (s + K) (Nat.le_add_right s K) ?_
        omega
      have h := abs_WA_step_le_of_goodW (p := p) (m := m) (n := s + K) hp0 hp1
        I J hI hJ hid hlast
      have hsn : s + K + 1 = s + (K + 1) := by omega
      rw [← hsn]
      simpa only [stepEnv_eq] using h
    have hih : |WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ|
        ≤ (K : ℝ) * stepEnv (N := N) p B := by
      refine ih ?_
      intro k hk hkt
      exact hgood k hk (by omega)
    rw [hsplit]
    calc |(WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ)
          + (WA p m U (s + (K + 1)) I J hI hJ - WA p m U (s + K) I J hI hJ)|
        ≤ |WA p m U (s + K) I J hI hJ - WA p m U s I J hI hJ|
          + |WA p m U (s + (K + 1)) I J hI hJ - WA p m U (s + K) I J hI hJ| := abs_add_le _ _
      _ ≤ (K : ℝ) * stepEnv (N := N) p B + stepEnv (N := N) p B := add_le_add hih hstep
      _ = ((K + 1 : ℕ) : ℝ) * stepEnv (N := N) p B := by push_cast; ring

end WCJFSharp
