import Swarm.Assembly

/-!
# Finite mean regeneration duration from the ballistic lower bound

Source: `results/main_1d_revised.tex`, §3.4 ("Finite mean duration and the common velocity"),
the step

> If `E^*T_1 = inf`, we obtain `X_{sigma_k}^i / sigma_k = (z_k/k)/(sigma_k/k) -> 0`,
> contrary to `(lower)`. We conclude that `E^*T_1 < inf`.

The campaign recorded (`areas/assembly/GAP_LEDGER.md`, §3, finding 3) that this derivation
needs "the strong law for non-integrable nonnegative variables, which Mathlib does not
provide in the required form".  This file removes that obstruction without it:

* `exists_trunc_integral_ge`: if the `lintegral` of an `NN`-valued variable is `inf`, then its
  truncated expectations `E[T and M]` are unbounded (monotone convergence, `AEMeasurable` form).
* `eventually_blockSum_ge`: hence, for every `A`, almost surely the renewal count grows at
  least `A` per step eventually (Etemadi on the truncated increments).
* `integrable_duration_of_liminf`: the paper's contradiction.  Instead of evaluating the
  `liminf` bound at the random time `sigma_k` (which needs `X_{sigma_k} = z_k`, unavailable from
  the campaign's `Sandwich`), it evaluates it at `sigma_{k+1} - 1`, where the *upper* clause of
  `Sandwich` gives `X < z_{k+1}`.  The contradiction yields `Integrable T 0` directly.

Consequently `RegenLaw`'s duration-integrability conjunct can be *derived* from
`Ballistic`, so `RegenAvailable` may be weakened to `RegenWeakAvailable` (no `Integrable T`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace Swarm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The `lintegral` of the truncated duration is the `ofReal` of its real integral. -/
lemma lintegral_trunc_eq (T : ℕ → Ω → ℕ) (hT : AEMeasurable (fun ω => (T 0 ω : ℝ)) μ) (M : ℕ) :
    ∫⁻ ω, ((min (T 0 ω) M : ℕ) : ℝ≥0∞) ∂μ
      = ENNReal.ofReal (∫ ω, ((min (T 0 ω) M : ℕ) : ℝ) ∂μ) := by
  have hAEM : AEMeasurable (fun ω => ((min (T 0 ω) M : ℕ) : ℝ)) μ := by
    have h1 : AEMeasurable (fun ω => min ((T 0 ω : ℕ) : ℝ) (M : ℝ)) μ :=
      hT.min aemeasurable_const
    refine h1.congr ?_
    filter_upwards with ω
    show min ((T 0 ω : ℕ) : ℝ) (M : ℝ) = ((min (T 0 ω) M : ℕ) : ℝ)
    exact (Nat.cast_min _ _).symm
  have hbound : ∀ᵐ ω ∂μ, ‖((min (T 0 ω) M : ℕ) : ℝ)‖ ≤ (M : ℝ) := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact_mod_cast min_le_right (T 0 ω) M
  have hint : Integrable (fun ω => ((min (T 0 ω) M : ℕ) : ℝ)) μ :=
    Integrable.of_bound hAEM.aestronglyMeasurable (M : ℝ) hbound
  have hnonneg : 0 ≤ᵐ[μ] (fun ω => ((min (T 0 ω) M : ℕ) : ℝ)) :=
    Filter.Eventually.of_forall fun ω => by positivity
  have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ := μ) hint hnonneg
  rw [h]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  exact (ENNReal.ofReal_natCast (min (T 0 ω) M)).symm

/-- **Truncation means are unbounded for a non-integrable nonnegative integer variable.** -/
lemma exists_trunc_integral_ge (T : ℕ → Ω → ℕ) (hT : AEMeasurable (fun ω => (T 0 ω : ℝ)) μ)
    (htop : ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂μ = ⊤) (A : ℝ) :
    ∃ M : ℕ, A ≤ ∫ ω, ((min (T 0 ω) M : ℕ) : ℝ) ∂μ := by
  have hAEM : ∀ M : ℕ, AEMeasurable (fun ω => ((min (T 0 ω) M : ℕ) : ℝ≥0∞)) μ := by
    intro M
    have h1 : AEMeasurable (fun ω => ENNReal.ofReal (min ((T 0 ω : ℕ) : ℝ) (M : ℝ))) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hT.min aemeasurable_const)
    refine h1.congr ?_
    filter_upwards with ω
    rw [← ENNReal.ofReal_natCast, Nat.cast_min]
  have hmono : ∀ᵐ ω ∂μ, Monotone fun M => ((min (T 0 ω) M : ℕ) : ℝ≥0∞) := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    intro a b hab
    have h : min (T 0 ω) a ≤ min (T 0 ω) b := min_le_min_left _ hab
    show ((min (T 0 ω) a : ℕ) : ℝ≥0∞) ≤ ((min (T 0 ω) b : ℕ) : ℝ≥0∞)
    exact_mod_cast h
  have hpt : ∀ ω, (⨆ M : ℕ, ((min (T 0 ω) M : ℕ) : ℝ≥0∞)) = (T 0 ω : ℝ≥0∞) := by
    intro ω
    refine le_antisymm (iSup_le fun M => ?_) ?_
    · have h : min (T 0 ω) M ≤ T 0 ω := min_le_left _ _
      show ((min (T 0 ω) M : ℕ) : ℝ≥0∞) ≤ (T 0 ω : ℝ≥0∞)
      exact_mod_cast h
    · simpa using le_iSup (fun M => ((min (T 0 ω) M : ℕ) : ℝ≥0∞)) (T 0 ω)
  have hsup : (⨆ M : ℕ, ∫⁻ ω, ((min (T 0 ω) M : ℕ) : ℝ≥0∞) ∂μ) = ⊤ := by
    rw [← lintegral_iSup' hAEM hmono]
    rw [show (∫⁻ a, ⨆ n, ((min (T 0 a) n : ℕ) : ℝ≥0∞) ∂μ) = ∫⁻ a, (T 0 a : ℝ≥0∞) ∂μ from
      lintegral_congr fun a => hpt a]
    exact htop
  obtain ⟨M, hM⟩ := iSup_eq_top.mp hsup (ENNReal.ofReal A) ENNReal.ofReal_lt_top
  refine ⟨M, ?_⟩
  rw [lintegral_trunc_eq T hT M] at hM
  have hq : 0 ≤ ∫ ω, ((min (T 0 ω) M : ℕ) : ℝ) ∂μ := integral_nonneg fun ω => by positivity
  rcases eq_or_lt_of_le hq with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero] at hM
    exact absurd hM (by simp)
  · exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff hpos).mp hM)

/-- **The truncated strong law gives an eventual linear lower bound on the renewal count.**
If the `lintegral` of the durations is infinite, then for every `A` almost every point has
`blockSum T k / k >= A` for all large `k`. -/
lemma eventually_blockSum_ge {T : ℕ → Ω → ℕ}
    (hTmeas : AEMeasurable (fun ω => (T 0 ω : ℝ)) μ)
    (hTind : Pairwise fun i j => IndepFun (fun ω => (T i ω : ℝ)) (fun ω => (T j ω : ℝ)) μ)
    (hTid : ∀ i, IdentDistrib (fun ω => (T i ω : ℝ)) (fun ω => (T 0 ω : ℝ)) μ μ)
    (htop : ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂μ = ⊤) (A : ℕ) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, (A : ℝ) ≤ (blockSum (fun j => T j ω) k : ℝ) / k := by
  obtain ⟨M, hM⟩ := exists_trunc_integral_ge T hTmeas htop ((A : ℝ) + 1)
  have hMeq : (∫ ω, ((min (T 0 ω) M : ℕ) : ℝ) ∂μ)
      = ∫ ω, min ((T 0 ω : ℕ) : ℝ) (M : ℝ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact Nat.cast_min (T 0 ω) M
  rw [hMeq] at hM
  have hφ : Measurable (fun x : ℝ => min x (M : ℝ)) := measurable_id.min measurable_const
  have hAEMtr : AEMeasurable (fun ω => min ((T 0 ω : ℕ) : ℝ) (M : ℝ)) μ :=
    hTmeas.min aemeasurable_const
  have hint : Integrable (fun ω => min ((T 0 ω : ℕ) : ℝ) (M : ℝ)) μ := by
    refine Integrable.of_bound hAEMtr.aestronglyMeasurable (M : ℝ) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact min_le_right _ _
  have hpair : Pairwise fun i j =>
      IndepFun (fun ω => min ((T i ω : ℕ) : ℝ) (M : ℝ))
        (fun ω => min ((T j ω : ℕ) : ℝ) (M : ℝ)) μ := by
    intro i j hij
    exact (hTind hij).comp hφ hφ
  have hid : ∀ i, IdentDistrib (fun ω => min ((T i ω : ℕ) : ℝ) (M : ℝ))
      (fun ω => min ((T 0 ω : ℕ) : ℝ) (M : ℝ)) μ μ := by
    intro i
    exact (hTid i).comp hφ
  have hSL := strong_law_ae_real (fun i ω => min ((T i ω : ℕ) : ℝ) (M : ℝ)) hint hpair hid
  filter_upwards [hSL] with ω hω
  have hgt : ∀ᶠ k in atTop,
      (A : ℝ) < (∑ i ∈ Finset.range k, min ((T i ω : ℕ) : ℝ) (M : ℝ)) / k :=
    hω.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [hgt, eventually_ge_atTop (1 : ℕ)] with k hk hk1
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hle : (∑ i ∈ Finset.range k, min ((T i ω : ℕ) : ℝ) (M : ℝ))
      ≤ (blockSum (fun j => T j ω) k : ℝ) := by
    rw [blockSum, Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => min_le_left _ _
  calc (A : ℝ) ≤ (∑ i ∈ Finset.range k, min ((T i ω : ℕ) : ℝ) (M : ℝ)) / k := le_of_lt hk
    _ ≤ (blockSum (fun j => T j ω) k : ℝ) / k :=
        div_le_div_of_nonneg_right hle (le_of_lt hkpos)


/-- From `kappa <= liminf u` and a bounded sequence `u` we get `kappa/2 <= u n` eventually.
(The bounds are needed only because `Filter.le_liminf_iff` asks for them.) -/
lemma eventually_le_of_le_liminf {u : ℕ → ℝ} {κ c C : ℝ}
    (hκ : 0 < κ) (hc : ∀ n, c ≤ u n) (hC : ∀ n, u n ≤ C)
    (h : κ ≤ liminf u atTop) : ∀ᶠ n in atTop, κ / 2 ≤ u n := by
  have hbdd : IsBoundedUnder (fun a b : ℝ => a ≥ b) atTop u :=
    isBoundedUnder_of ⟨c, fun n => hc n⟩
  have hcob : IsCoboundedUnder (fun a b : ℝ => a ≥ b) atTop u :=
    isCoboundedUnder_ge_of_le (atTop) hC
  have hiff := le_liminf_iff (f := (atTop : Filter ℕ)) (u := u) (x := κ) hcob hbdd
  filter_upwards [(hiff.mp h) (κ / 2) (by linarith)] with n hn using le_of_lt hn


/-- One-sided version of `eventually_le_of_le_liminf`: only an eventual **lower** bound on `u`
is needed.  (Both `IsBoundedUnder` fields of `Filter.le_liminf_iff` are avoided by comparing
with `sSup {a | eventually a <= u}` directly.) -/
lemma eventually_le_of_le_liminf_of_lower {u : ℕ → ℝ} {κ c : ℝ}
    (hκ : 0 < κ) (hc : ∀ n, c ≤ u n) (h : κ ≤ liminf u atTop) :
    ∀ᶠ n in atTop, κ / 2 ≤ u n := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ n in atTop, u n ≤ κ / 2 := hcon.mono fun n hn => le_of_lt (not_le.mp hn)
  have hne : ({a : ℝ | ∀ᶠ n in atTop, a ≤ u n}).Nonempty :=
    ⟨c, Filter.Eventually.of_forall hc⟩
  have hupper : ∀ a ∈ ({a : ℝ | ∀ᶠ n in atTop, a ≤ u n}), a ≤ κ / 2 := by
    intro a ha
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨N, hN⟩ := eventually_atTop.mp ha
    rw [frequently_atTop] at hfreq
    obtain ⟨n, hn1, hn2⟩ := hfreq N
    linarith [hN n hn1, hn2]
  have hbdd : BddAbove {a : ℝ | ∀ᶠ n in atTop, a ≤ u n} := ⟨κ / 2, hupper⟩
  have hle : liminf u atTop ≤ κ / 2 := by
    rw [Filter.liminf_eq]
    exact csSup_le hne hupper
  linarith

/-- **Finite mean regeneration duration** (paper §3.4, first paragraph).

For a system with regeneration increments `(D,T)`, `T >= 1`, pairwise independent and
identically distributed durations, integrable distances, the paper's path structure
`Sandwich`, and the ballistic lower bound `kappa <= liminf X_n^i/n` for at least one walker,
the duration increment is integrable.

This is the paper's derivation of `E^*T_1 < inf` from `(lower)`, with two formal
adjustments: the `liminf` is evaluated at the deterministic-shift point `sigma_{k+1} - 1`
(the only index at which `Sandwich` bounds `X` from above), and the infinite-mean strong law
is replaced by the truncated strong law plus the fact that the sum of the first `k` durations
dominates `k`. -/
theorem integrable_duration_of_liminf
    {N : ℕ} {D T : ℕ → Ω → ℕ} {X : ℕ → Ω → Fin N → ℤ} {κ : ℝ}
    (hκ : 0 < κ) (hN : 1 ≤ N)
    (hDint : Integrable (fun ω => (D 0 ω : ℝ)) μ)
    (hDind : Pairwise fun i j => IndepFun (fun ω => (D i ω : ℝ)) (fun ω => (D j ω : ℝ)) μ)
    (hDid : ∀ i, IdentDistrib (fun ω => (D i ω : ℝ)) (fun ω => (D 0 ω : ℝ)) μ μ)
    (hTpos : ∀ i ω, 1 ≤ T i ω)
    (hTind : Pairwise fun i j => IndepFun (fun ω => (T i ω : ℝ)) (fun ω => (T j ω : ℝ)) μ)
    (hTid : ∀ i, IdentDistrib (fun ω => (T i ω : ℝ)) (fun ω => (T 0 ω : ℝ)) μ μ)
    (hsand : Sandwich μ X D T)
    (hball : ∀ᵐ ω ∂μ, ∀ i : Fin N, κ ≤ liminf (fun n => pos X n i ω / n) atTop)
    (hbd : ∀ᵐ ω ∂μ, ∀ (i : Fin N) (n : ℕ), -(1 : ℝ) ≤ pos X n i ω / n) :
    Integrable (fun ω => (T 0 ω : ℝ)) μ := by
  by_contra hcon
  have hTmeas : AEMeasurable (fun ω => (T 0 ω : ℝ)) μ := (hTid 0).aemeasurable_fst
  have htop : ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂μ = ⊤ := by
    have hnn : 0 ≤ᵐ[μ] (fun ω => (T 0 ω : ℝ)) :=
      Filter.Eventually.of_forall fun ω => by positivity
    have hnot : ¬ HasFiniteIntegral (fun ω => (T 0 ω : ℝ)) μ := fun hfi =>
      hcon ⟨hTmeas.aestronglyMeasurable, hfi⟩
    have hlt : ¬ (∫⁻ ω, ENNReal.ofReal ((T 0 ω : ℕ) : ℝ) ∂μ < ⊤) := fun h =>
      hnot ((hasFiniteIntegral_iff_ofReal hnn).mpr h)
    have heq : (∫⁻ ω, ENNReal.ofReal ((T 0 ω : ℕ) : ℝ) ∂μ) = ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂μ :=
      lintegral_congr fun ω => ENNReal.ofReal_natCast (T 0 ω)
    rw [heq] at hlt
    exact eq_top_iff.mpr (not_lt.mp hlt)
  set i₀ : Fin N := ⟨0, by omega⟩ with hi₀
  set L : ℝ := ∫ ω, (D 0 ω : ℝ) ∂μ with hL
  set C : ℝ := |L| + 1 with hCL
  have hCpos : 0 < C := by rw [hCL]; positivity
  have hLC : L < C := by
    have h1 := le_abs_self L
    rw [hCL]; linarith
  set A : ℕ := ⌈8 * C / κ⌉₊ + 2 with hA
  have hAlt : 8 * C / κ < (A : ℝ) := by
    have h1 : 8 * C / κ ≤ (⌈8 * C / κ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈8 * C / κ⌉₊ : ℝ) ≤ (A : ℝ) - 1 := by
      rw [hA]; push_cast; linarith
    linarith
  have hkey := eventually_blockSum_ge hTmeas hTind hTid htop A
  have hDsl := strong_law_ae_real (fun i ω => (D i ω : ℝ)) hDint hDind hDid
  have hfalse : ∀ᵐ ω ∂μ, False := by
    filter_upwards [hkey, hDsl, hsand, hball, hbd] with ω hkeyω hDω hsandω hballω hbdω
    have hlim : ∀ᶠ n in atTop, κ / 2 ≤ pos X n i₀ ω / n :=
      eventually_le_of_le_liminf_of_lower hκ (fun n => hbdω i₀ n) (hballω i₀)
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hlim
    have hDupper : ∀ᶠ k in atTop, (blockSum (fun j => D j ω) (k + 1) : ℝ) / (k + 1) ≤ C := by
      have hev : ∀ᶠ k in atTop, (∑ i ∈ Finset.range k, ((D i ω : ℕ) : ℝ)) / k ≤ C := by
        have h1 : ∀ᶠ k in atTop, (∑ i ∈ Finset.range k, ((D i ω : ℕ) : ℝ)) / k < C :=
          hDω.eventually (eventually_lt_nhds (by rw [← hL]; exact hLC))
        filter_upwards [h1] with k hk using le_of_lt hk
      obtain ⟨K, hK⟩ := eventually_atTop.mp hev
      refine eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
      have h' := hK (k + 1) (by omega)
      simpa [blockSum, Nat.cast_sum] using h'
    have key : ∀ᶠ k : ℕ in atTop, False := by
      filter_upwards [hkeyω, hDupper, (eventually_ge_atTop N₀ : ∀ᶠ k : ℕ in atTop, N₀ ≤ k),
        (eventually_ge_atTop (1 : ℕ) : ∀ᶠ k : ℕ in atTop, 1 ≤ k)] with k hkA hkD hkN hk1
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have hk1r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      set blk : ℕ := blockSum (fun j => T j ω) k with hblk
      set σ : ℕ := blockSum (fun j => T j ω) (k + 1) with hσ
      set z : ℕ := blockSum (fun j => D j ω) (k + 1) with hz
      set n : ℕ := σ - 1 with hn
      have hσeq : σ = blk + T k ω := by
        rw [hσ, hblk, blockSum_succ]
      have hkblk : k ≤ blk := by
        rw [hblk, blockSum]
        calc k = ∑ j ∈ Finset.range k, 1 := by simp
          _ ≤ ∑ j ∈ Finset.range k, T j ω :=
              Finset.sum_le_sum fun j _ => hTpos j ω
      have hblkn : blk ≤ n := by
        have hT1 : 1 ≤ T k ω := hTpos k ω
        omega
      have hn1 : 1 ≤ n := le_trans hk1 (le_trans hkblk hblkn)
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hNn : N₀ ≤ n := le_trans hkN (le_trans hkblk hblkn)
      have hAn : (A : ℝ) * (k : ℝ) ≤ (blk : ℝ) := by
        have h := (le_div_iff₀ hkpos).mp hkA
        rw [hblk] at h ⊢
        simpa using h
      have hA0 : (0 : ℝ) ≤ (A : ℝ) := by positivity
      have hn_lb : (A : ℝ) * (k : ℝ) / 2 ≤ (n : ℝ) := by
        have hbn : (blk : ℝ) ≤ (n : ℝ) := by exact_mod_cast hblkn
        nlinarith [hAn, hbn, hA0, hk1r]
      have hstep : κ / 2 * (n : ℝ) ≤ (X n ω i₀ : ℝ) := by
        have h := hN₀ n hNn
        have h' : κ / 2 ≤ (X n ω i₀ : ℝ) / (n : ℝ) := h
        exact (le_div_iff₀ hnpos).mp h'
      have hXz : X n ω i₀ < (z : ℤ) := by
        refine lt_of_not_ge fun hle => ?_
        have h2 : blockSum (fun j => T j ω) (k + 1) ≤ n := (hsandω i₀ k n).2 hle
        rw [← hσ] at h2
        have hT1 : 1 ≤ T k ω := hTpos k ω
        omega
      have hXzr : (X n ω i₀ : ℝ) ≤ (z : ℝ) - 1 := by
        have h : X n ω i₀ ≤ (z : ℤ) - 1 := by omega
        have h' : ((X n ω i₀ : ℤ) : ℝ) ≤ (((z : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast h
        push_cast at h'
        exact h'
      have hz_le : (z : ℝ) ≤ C * ((k : ℝ) + 1) := by
        have hden : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have h := (div_le_iff₀ hden).mp hkD
        rw [hz] at h ⊢
        push_cast at h ⊢
        simpa [Nat.cast_add, Nat.cast_one] using h
      have hmain : κ * (A : ℝ) / 4 * (k : ℝ) ≤ 2 * C * (k : ℝ) := by
        nlinarith [hstep, hXzr, hz_le, hn_lb, hk1r, hκ]
      have h2 : κ * (A : ℝ) / 4 ≤ 2 * C :=
        le_of_mul_le_mul_right hmain hkpos
      have h3 : (A : ℝ) ≤ 8 * C / κ := by
        have hq : (0 : ℝ) < κ / 4 := by linarith
        have h4 : (A : ℝ) ≤ 2 * C / (κ / 4) := (le_div_iff₀ hq).mpr (by linarith)
        have he : 2 * C / (κ / 4) = 8 * C / κ := by
          field_simp
          ring
        linarith [h4, he.symm.le, h4]
      exact absurd h3 (not_le.mpr hAlt)
    obtain ⟨k, hk⟩ := key.exists
    exact hk
  have h0 : μ (Set.univ) = 0 := by
    have h := MeasureTheory.ae_iff.mp hfalse
    simpa using h
  have h1 : μ (Set.univ) = 1 := measure_univ
  rw [h1] at h0
  exact one_ne_zero h0


/-! ### Weakening the regeneration input: `RegenLaw` without duration integrability -/

/-- `RegenLaw` with the **duration-integrability** conjunct removed.  Everything else
(integrable distances, `T >= 1`, pairwise independence and identical distribution of both
increments) is kept. -/
def RegenLawWeak (μ : Measure Ω) (D T : ℕ → Ω → ℕ) : Prop :=
  (∀ i, Integrable (fun ω => (D i ω : ℝ)) μ) ∧
  (∀ i ω, 1 ≤ T i ω) ∧
  (Pairwise fun i j => IndepFun (fun ω => (D i ω : ℝ)) (fun ω => (D j ω : ℝ)) μ) ∧
  (∀ i, IdentDistrib (fun ω => (D i ω : ℝ)) (fun ω => (D 0 ω : ℝ)) μ μ) ∧
  (Pairwise fun i j => IndepFun (fun ω => (T i ω : ℝ)) (fun ω => (T j ω : ℝ)) μ) ∧
  (∀ i, IdentDistrib (fun ω => (T i ω : ℝ)) (fun ω => (T 0 ω : ℝ)) μ μ)

/-- Every `RegenLaw` is a `RegenLawWeak` (forget duration integrability). -/
theorem regenLawWeak_of_regenLaw {D T : ℕ → Ω → ℕ} (h : RegenLaw μ D T) : RegenLawWeak μ D T :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Adding back duration integrability (for one index, propagated by identical distribution). -/
theorem regenLaw_of_regenLawWeak {D T : ℕ → Ω → ℕ} (h : RegenLawWeak μ D T)
    (hint : Integrable (fun ω => (T 0 ω : ℝ)) μ) : RegenLaw μ D T := by
  obtain ⟨hD, hTpos, hDind, hDid, hTind, hTid⟩ := h
  refine ⟨hD, ?_, hTpos, hDind, hDid, hTind, hTid⟩
  intro i
  exact (hTid i).integrable_iff.mpr hint

/-- **Duration integrability for the weak regeneration input.** -/
theorem integrable_duration_of_regenLawWeak {N : ℕ} {D T : ℕ → Ω → ℕ}
    {X : ℕ → Ω → Fin N → ℤ} {κ : ℝ}
    (hκ : 0 < κ) (hN : 1 ≤ N) (h : RegenLawWeak μ D T) (hsand : Sandwich μ X D T)
    (hball : ∀ᵐ ω ∂μ, ∀ i : Fin N, κ ≤ liminf (fun n => pos X n i ω / n) atTop)
    (hbd : ∀ᵐ ω ∂μ, ∀ (i : Fin N) (n : ℕ), -(1 : ℝ) ≤ pos X n i ω / n) :
    Integrable (fun ω => (T 0 ω : ℝ)) μ := by
  obtain ⟨hD, hTpos, hDind, hDid, hTind, hTid⟩ := h
  exact integrable_duration_of_liminf hκ hN (hD 0) hDind hDid hTpos hTind hTid hsand hball hbd


/-! ### The reduced input `RegenWeakAvailable`, and `MainClaim` from it -/

/-- **`RegenAvailable` with the duration-integrability conjunct removed.**  By
`integrable_duration_of_regenLawWeak` this is enough once `Ballistic` is available: the
paper's own route derives `E^*T_1 < inf` from the positive lower speed. -/
def RegenWeakAvailable (m : ℕ) (p : ℝ) : Prop :=
  ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
    2 ≤ N → IsInteractingLaw 𝓕 μ X m p →
      ∃ (D T : ℕ → Ω → ℕ), RegenLawWeak μ D T ∧ Sandwich μ X D T

/-- `RegenWeakAvailable` is strictly weaker than `RegenAvailable`. -/
theorem regenWeakAvailable_of_regenAvailable {m : ℕ} {p : ℝ} (h : RegenAvailable m p) :
    RegenWeakAvailable m p := by
  intro N Ω _ μ _ X 𝓕 hN hlaw
  obtain ⟨D, T, hreg, hsand⟩ := h N Ω μ X 𝓕 hN hlaw
  exact ⟨D, T, regenLawWeak_of_regenLaw hreg, hsand⟩

/-- **`RegenAvailable` from the weak input and `Ballistic`.**  The duration-integrability
conjunct is *derived*, exactly as in the paper (§3.4). -/
theorem regenAvailable_of_ballistic_weak {m : ℕ} {p : ℝ} (hball : Ballistic m p)
    (hweak : RegenWeakAvailable m p) : RegenAvailable m p := by
  obtain ⟨κ, hκpos, hκ⟩ := hball
  intro N Ω _ μ _ X 𝓕 hN hlaw
  obtain ⟨D, T, hreg, hsand⟩ := hweak N Ω μ X 𝓕 hN hlaw
  have hbd : ∀ᵐ ω ∂μ, ∀ (i : Fin N) (n : ℕ), -(1 : ℝ) ≤ pos X n i ω / n := by
    have hb := abs_le_time_of_law hlaw
    filter_upwards with ω
    intro i n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : X 0 ω i = 0 := hlaw.2.1 ω i
      simp [pos, h0]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hX : -(n : ℝ) ≤ (X n ω i : ℝ) := by
        have h := (abs_le.mp (hb n ω i)).1
        have h' : (-(n : ℤ) : ℤ) ≤ X n ω i := by omega
        exact_mod_cast h'
      have hdiv : -(1 : ℝ) ≤ (X n ω i : ℝ) / (n : ℝ) := by
        rw [le_div_iff₀ hnpos]
        nlinarith
      simpa [pos] using hdiv
  have hint : Integrable (fun ω => (T 0 ω : ℝ)) μ :=
    integrable_duration_of_regenLawWeak hκpos (by omega) hreg hsand
      (hκ N Ω μ X 𝓕 hN hlaw) hbd
  exact ⟨D, T, regenLaw_of_regenLawWeak hreg hint, hsand⟩

/-- **`InitalRegen` is not an input**: `ae_tendsto_of_regen` already gives the untranslated
limit, so the shift `S = 0` and the level `c = 0` satisfy the initial-regeneration clause.
(Restated here so that this module is
self-contained.) -/
theorem initialRegen_free (m : ℕ) (p : ℝ) : InitialRegen m p := by
  intro N Ω _ μ _ X 𝓕 hN hlaw D T hreg hsand
  filter_upwards [ae_tendsto_of_regen hreg hsand] with ω hω
  exact ⟨0, 0, fun i => by simpa using hω i⟩

/-- **Theorem 1.1 of the paper from `Ballistic` and the weakened regeneration input.** -/
theorem main_theorem_of_ballistic_weak {m : ℕ} {p : ℝ} (hm : 2 ≤ m) (hp1 : 1 / 2 < p)
    (hp2 : p < 1) (hball : Ballistic m p) (hweak : RegenWeakAvailable m p) : MainClaim m p :=
  main_claim_of_inputs hm hp1 hp2 hball (regenAvailable_of_ballistic_weak hball hweak)
    (initialRegen_free m p)

/-- The same statement with the conclusion written out (the shape of `main_theorem`). -/
theorem main_theorem_of_ballistic_weak' {m : ℕ} {p : ℝ} (hm : 2 ≤ m) (hp1 : 1 / 2 < p)
    (hp2 : p < 1) (hball : Ballistic m p) (hweak : RegenWeakAvailable m p) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
      2 ≤ N → IsInteractingLaw 𝓕 μ X m p →
        ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
          ∀ᵐ ω ∂μ, ∀ i : Fin N, Tendsto (fun n => pos X n i ω / n) atTop (𝓝 v) :=
  main_theorem_of_ballistic_weak hm hp1 hp2 hball hweak

end Swarm


