/-
# RETIRED: `RecordTight.PCtx` is uninhabited

`ScaleVacuous.not_nonempty_pctx_bound` and `not_nonempty_pctx_hstart` prove that no instance
exists, for two independent reasons (`hscale_bound 0` and the level-independent `R` in
`hstart`).  No theorem taking a `PCtx` is a meaningful tightness reduction.  This module is
retained only so `ScaleVacuous.lean` can state and verify that refutation.  Use the explicitly
non-vacuous `SwarmM4.PCtxR` interface in `ScaleRepair.lean` instead.

# Original specification: record-distance tightness from a single good level per index

The following prose describes the defective, now retired interface, not an available result.

`Tightness.lean` derives the union bound from three almost-sure inputs: `hterm` (`(recordo)`),
`hR` (a statement about failing blocks at *all* levels) and `hblk` (`(blkprob)`).  `hR` is
stronger than the paper's mechanism: `(recordo)` plus `(blkprob)` and Borel–Cantelli only give, at
each index `r`, one good level `Λ r ≈ r / (2C₀)`, not goodness at every level above it.

This file replaces `hR` by that single-level statement.  The structure `PCtx` is `ProbCtx` with
`hR` deleted and three scale fields added:

* `g : ℕ → ℕ`, the *scale* `Λ r = 2 ^ g r` (in the paper, the largest dyadic integer at most
  `r/(2C₀)`);
* `hscale_mono : ∀ r r', g r ≤ g r' + 1` — the scale drops by at most a factor two between
  consecutive indices;
* `hscale_bound : ∀ r, 2 * C₀ * 2 ^ g r ≤ r` — the scale is below `r/(2C₀)` (arithmetic of the
  concrete `g`, kept abstract here);
* `hscale_good : ∀ᵐ ω, ∀ r ≥ R ω, Good ω r (2 ^ g r)` — the single-level goodness that
  `(recordo)` + `(blkprob)` + Borel–Cantelli actually provide;
* `hstart : ∀ a, ∀ᵐ ω, max (2 ^ a) (d ω (R ω)) ≤ 2 ^ g (R ω)` — the transient condition
  `d (R ω) ≤ Λ (R ω)` at the single random index `R ω`.

Everything else is copied from `Tightness.lean` unchanged; the only difference in the body is that
the level bound `C₀ ℓ ≤ r` on certificates comes from `LevelCover.Ctx.exists_certificate_le`
instead of from `hR`.

Consequence: `PCtx.tightness` recovers the tightness conclusion with `hR` replaced by
`hscale_good`, `hscale_mono`, `hscale_bound` and `hstart`.  Note that `hscale_bound` and
`hscale_mono` are deterministic arithmetic; `hstart` is an almost-sure statement at one index;
`hscale_good` is one level per index.  None of them is proved here.
-/
import Swarm.LevelCover

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace RecordTight

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Probabilistic data for the tightness argument with the scale hypothesis in place of `hR`. -/
structure PCtx (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  hprob : IsProbabilityMeasure μ
  B : ℕ
  C₀ : ℕ
  d : Ω → ℕ → ℕ
  Good : Ω → ℕ → ℕ → Prop
  R : Ω → ℕ
  p : ℕ → ℝ≥0∞
  /-- The scale exponent: the good level at index `r` is `2 ^ g r`. -/
  g : ℕ → ℕ
  hB : 1 ≤ B
  hC₀ : 1 ≤ C₀
  hd : Measurable d
  hdR : Measurable fun ω => d ω (R ω)
  hg : ∀ r ℓ, MeasurableSet {ω | Good ω r ℓ}
  hRmeas : Measurable R
  hS : ∀ ω r L, Good ω r L → d ω r ≤ L →
    d ω (r + B * L) ≤ L / 2 ∧ ∀ u, r ≤ u → u ≤ r + B * L → d ω u ≤ C₀ * L
  hterm : ∀ r L, 1 ≤ L → ∀ᵐ ω ∂μ, ∃ j, Good ω r (2 ^ j * L)
  hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
    μ ({ω | d ω r ≤ ℓ} ∩ {ω | ¬ Good ω r ℓ}) ≤ p ℓ
  /-- The scale is nondecreasing (in particular it drops by at most a factor two per step). -/
  hscale_mono : ∀ r r', r ≤ r' → g r ≤ g r'
  /-- The scale is at most `r / (2 C₀)`. -/
  hscale_bound : ∀ r, 2 * C₀ * 2 ^ g r ≤ r
  /-- One good level per index: the paper's `(recordo)` at the scale `Λ r = 2 ^ g r`. -/
  hscale_good : ∀ᵐ ω ∂μ, ∀ r, R ω ≤ r → Good ω r (2 ^ g r)
  /-- The transient condition at the single random index `R`. -/
  hstart : ∀ a : ℕ, ∀ᵐ ω ∂μ, max (2 ^ a) (d ω (R ω)) ≤ 2 ^ g (R ω)

namespace PCtx

variable (c : PCtx Ω)

lemma measurable_d (r : ℕ) : Measurable fun ω => c.d ω r :=
  (measurable_pi_apply r).comp c.hd

lemma measurable_dR : Measurable fun ω => c.d ω (c.R ω) := c.hdR

/-- The finite random initial transient: the procedure starts at the scale `Λ (R ω)`. -/
noncomputable def U (ω : Ω) : ℕ := c.R ω + 2 * c.B * 2 ^ c.g (c.R ω)

lemma measurable_U : Measurable c.U := by
  have h2 : Measurable fun ω => c.g (c.R ω) :=
    (measurable_of_countable (fun n : ℕ => c.g n)).comp c.hRmeas
  have h1 : Measurable fun ω => 2 ^ c.g (c.R ω) :=
    (measurable_of_countable (fun n : ℕ => 2 ^ n)).comp h2
  have h3 : Measurable fun ω => 2 * c.B * 2 ^ c.g (c.R ω) := measurable_const.mul h1
  exact c.hRmeas.add h3

/-- The certificate weight at level `ℓ`. -/
noncomputable def w (ℓ : ℕ) : ℝ≥0∞ := ((4 * c.B * ℓ + 1 : ℕ) : ℝ≥0∞) * c.p ℓ

/-- The certificate set. -/
noncomputable def certSet (K u : ℕ) : Set Ω :=
  ⋃ k : ℕ, ⋃ r ∈ Finset.Icc (u - 4 * c.B * (k + K)) u,
    (if c.C₀ * (k + K) ≤ r then
      ({ω | c.d ω r ≤ k + K} ∩ {ω | ¬ c.Good ω r (k + K)}) else ∅)

lemma measurableSet_certSet (K u : ℕ) : MeasurableSet (c.certSet K u) := by
  refine MeasurableSet.iUnion fun k => ?_
  refine MeasurableSet.biUnion (Finset.countable_toSet _) fun r _ => ?_
  by_cases h' : c.C₀ * (k + K) ≤ r
  · simp only [h', if_true]
    exact ((c.measurable_d r measurableSet_Iic).inter (c.hg r (k + K)).compl)
  · simp only [h', if_false]; exact MeasurableSet.empty

/-- **The union bound over certificates.** -/
lemma measure_certSet_le (K u : ℕ) (hK : 1 ≤ K) :
    c.μ (c.certSet K u) ≤ ∑' k : ℕ, c.w (k + K) := by
  haveI := c.hprob
  refine le_trans (measure_iUnion_le (fun k : ℕ => ⋃ r ∈ Finset.Icc (u - 4 * c.B * (k + K)) u,
    (if c.C₀ * (k + K) ≤ r then
      ({ω | c.d ω r ≤ k + K} ∩ {ω | ¬ c.Good ω r (k + K)}) else ∅))) ?_
  refine ENNReal.tsum_le_tsum fun k => ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hℓ : 1 ≤ k + K := by omega
  calc ∑ r ∈ Finset.Icc (u - 4 * c.B * (k + K)) u,
        c.μ (if c.C₀ * (k + K) ≤ r then
          ({ω | c.d ω r ≤ k + K} ∩ {ω | ¬ c.Good ω r (k + K)}) else ∅)
      ≤ ∑ r ∈ Finset.Icc (u - 4 * c.B * (k + K)) u, c.p (k + K) := by
        refine Finset.sum_le_sum fun r _ => ?_
        by_cases h : c.C₀ * (k + K) ≤ r
        · rw [if_pos h]; exact c.hblk (k + K) hℓ r h
        · rw [if_neg h]; simp
    _ = (Finset.Icc (u - 4 * c.B * (k + K)) u).card • c.p (k + K) := Finset.sum_const _
    _ = ((Finset.Icc (u - 4 * c.B * (k + K)) u).card : ℝ≥0∞) * c.p (k + K) := nsmul_eq_mul _ _
    _ ≤ ((4 * c.B * (k + K) + 1 : ℕ) : ℝ≥0∞) * c.p (k + K) := by
        gcongr
        rw [Nat.card_Icc]
        omega
    _ = c.w (k + K) := by simp only [w]

/-- **Per-level bound without `hR`.**  For every `a` and every index `u`, the probability that the
record distance at `u` exceeds `C₀ 2^a` is at most the probability of the initial transient plus
the total certificate probability past level `2^a`.  The only structural input is the scale
hypothesis, used through `Ctx.exists_certificate_le`. -/
theorem measure_gt_le (a u : ℕ) :
    c.μ {ω | c.C₀ * 2 ^ a < c.d ω u} ≤
      c.μ {ω | u < c.U ω} + ∑' k : ℕ, c.w (k + 2 ^ a) := by
  haveI := c.hprob
  have hterm_all : ∀ᵐ ω ∂c.μ, ∀ (r L : ℕ), 1 ≤ L → ∃ j, c.Good ω r (2 ^ j * L) := by
    rw [ae_all_iff]
    intro r
    rw [ae_all_iff]
    intro L
    by_cases h : 1 ≤ L
    · filter_upwards [c.hterm r L h] with ω hω; exact fun _ => hω
    · filter_upwards with ω; exact fun hcon => absurd hcon h
  have hae : ∀ᵐ ω ∂c.μ,
      (∀ (r L : ℕ), 1 ≤ L → ∃ j, c.Good ω r (2 ^ j * L)) ∧
      (∀ r, c.R ω ≤ r → c.Good ω r (2 ^ c.g r)) ∧
      (max (2 ^ a) (c.d ω (c.R ω)) ≤ 2 ^ c.g (c.R ω)) :=
    hterm_all.and (c.hscale_good.and (c.hstart a))
  have hsub : {ω | c.C₀ * 2 ^ a < c.d ω u} ≤ᵐ[c.μ]
      Set.union {ω | u < c.U ω} (c.certSet (2 ^ a) u) := by
    filter_upwards [hae] with ω hω hx
    obtain ⟨htermω, hgoodω, hstartω⟩ := hω
    by_cases hu : u < c.U ω
    · exact Or.inl hu
    · push_neg at hu
      have hK1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      let ctx : Ctx :=
        { K := 2 ^ a, B := c.B, C₀ := c.C₀, d := fun r => c.d ω r,
          Good := fun r ℓ => c.Good ω r ℓ, r₀ := c.R ω, L₀ := 2 ^ c.g (c.R ω),
          hterm := fun r L hKL => htermω r L (le_trans hK1 hKL),
          hS := fun r L hG hd => c.hS ω r L hG hd,
          hB := c.hB, hK := hK1, hstart := hstartω }
      have hga : ∀ r, c.R ω ≤ r → a ≤ c.g r := by
        intro r hr
        have h2 := c.hscale_mono (c.R ω) r hr
        have h3 : 2 ^ a ≤ 2 ^ c.g (c.R ω) := le_trans (le_max_left _ _) hstartω
        have h4 : 2 ^ a ≤ 2 ^ c.g r := le_trans h3 (Nat.pow_le_pow_right (by norm_num) h2)
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h4
      obtain ⟨r, ℓ, hKℓ, hdr, hng, hr0, hru, huℓ, hC₀ℓ⟩ :=
        ctx.exists_certificate_le (fun r => c.g r - a)
          (fun r hr => by
            have h1 : 2 ^ (c.g r - a) * 2 ^ a = 2 ^ c.g r := by
              rw [← pow_add, Nat.sub_add_cancel (hga r hr)]
            rw [h1]
            exact hgoodω r hr)
          (fun r r' _ hr' => by have := c.hscale_mono r r' hr'; omega)
          ⟨c.g (c.R ω) - a, by
            have h1 : 2 ^ (c.g (c.R ω) - a) * 2 ^ a = 2 ^ c.g (c.R ω) := by
              rw [← pow_add, Nat.sub_add_cancel (hga (c.R ω) (le_refl _))]
            rw [h1], le_rfl⟩
          (fun r hr => by
            have h1 : 2 ^ (c.g r - a) * 2 ^ a = 2 ^ c.g r := by
              rw [← pow_add, Nat.sub_add_cancel (hga r hr)]
            rw [h1]
            exact c.hscale_bound r) hu hx
      have hℓ1 : 1 ≤ ℓ := le_trans hK1 hKℓ
      have hsub : u - 4 * c.B * ℓ ≤ r := Nat.sub_le_iff_le_add.2 huℓ
      refine Or.inr (Set.mem_iUnion.2 ⟨ℓ - 2 ^ a, ?_⟩)
      have hℓK : ℓ - 2 ^ a + 2 ^ a = ℓ := Nat.sub_add_cancel hKℓ
      rw [hℓK]
      refine Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
      · exact Finset.mem_Icc.2 ⟨hsub, hru⟩
      · rw [if_pos hC₀ℓ]
        exact ⟨hdr, hng⟩
  refine le_trans (measure_mono_ae hsub) (le_trans (measure_union_le _ _) ?_)
  exact add_le_add le_rfl (c.measure_certSet_le (2 ^ a) u (Nat.one_le_two_pow))

/-- For a natural-valued measurable statistic, the upper tails vanish. -/
lemma tendsto_measure_lt_nat (f : Ω → ℕ) (hf : Measurable f) :
    Tendsto (fun K => c.μ {ω | K < f ω}) atTop (𝓝 0) := by
  haveI := c.hprob
  have hmono : Antitone fun K => {ω | K < f ω} := by
    intro a b hab ω h
    exact lt_of_le_of_lt hab h
  have hne : ∃ K, c.μ {ω | K < f ω} ≠ ∞ := ⟨0, measure_ne_top _ _⟩
  have hInter : (⋂ K, {ω | K < f ω}) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_lt]
    exact ⟨f ω, le_rfl⟩
  have hnull : ∀ K, NullMeasurableSet {ω | K < f ω} c.μ := fun K =>
    (hf measurableSet_Ioi).nullMeasurableSet
  have ht := tendsto_measure_iInter_atTop hnull hmono hne
  rw [hInter, measure_empty] at ht
  exact ht

/-- **Tightness without `hR`.**  If the certificate series is finite, the family of laws of the
record distances is tight.  Compared with `Tightness.ProbCtx.tightness` the hypothesis `hR` is
replaced by the scale fields of `PCtx`. -/
theorem tightness
    (hsum : (∑' ℓ : ℕ, c.w ℓ) ≠ ⊤)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K' : ℕ, ∀ u : ℕ, c.μ {ω | K' < c.d ω u} ≤ ε := by
  haveI := c.hprob
  -- the tail sums of the certificate probabilities vanish
  have htail : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → (∑' k : ℕ, c.w (k + m)) ≤ ε / 2 := by
    have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
    have ht := ENNReal.tendsto_sum_nat_add c.w hsum
    have hev : ∀ᶠ m : ℕ in atTop, (∑' k : ℕ, c.w (k + m)) ≤ ε / 2 :=
      ENNReal.tendsto_nhds_zero.1 ht (ε / 2) hε2
    exact eventually_atTop.1 hev
  obtain ⟨M, hM⟩ := htail
  -- the initial transient has vanishing probability
  have htend := c.tendsto_measure_lt_nat c.U c.measurable_U
  have hev : ∀ᶠ u : ℕ in atTop, c.μ {ω | u < c.U ω} ≤ ε / 2 :=
    ENNReal.tendsto_nhds_zero.1 htend (ε / 2) (ENNReal.div_pos hε.ne' (by norm_num))
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.1 hev
  -- the finitely many earlier indices
  have hsingle : ∀ u : ℕ, ∃ Ku : ℕ, c.μ {ω | Ku < c.d ω u} ≤ ε := by
    intro u
    have ht := c.tendsto_measure_lt_nat (fun ω => c.d ω u) (c.measurable_d u)
    have hev' : ∀ᶠ K' : ℕ in atTop, c.μ {ω | K' < c.d ω u} ≤ ε :=
      ENNReal.tendsto_nhds_zero.1 ht ε hε
    obtain ⟨b, hb⟩ := eventually_atTop.1 hev'
    exact ⟨b, hb b le_rfl⟩
  choose Ku hKu using hsingle
  -- choose `a` so that `2 ^ a` is above both the tail threshold and the finite exceptions
  obtain ⟨a, ha⟩ : ∃ a : ℕ, max M ((Finset.range u₀).sup Ku) ≤ 2 ^ a := by
    refine ⟨max M ((Finset.range u₀).sup Ku) + 1, ?_⟩
    have hlt := Nat.lt_two_pow_self (n := max M ((Finset.range u₀).sup Ku))
    have hle : 2 ^ max M ((Finset.range u₀).sup Ku) ≤
        2 ^ (max M ((Finset.range u₀).sup Ku) + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨c.C₀ * 2 ^ a, fun u => ?_⟩
  have hj' : (∑' k : ℕ, c.w (k + 2 ^ a)) ≤ ε / 2 :=
    hM (2 ^ a) (le_trans (le_max_left _ _) ha)
  rcases lt_or_ge u u₀ with hu | hu
  · have hle : c.μ {ω | c.C₀ * 2 ^ a < c.d ω u} ≤ c.μ {ω | Ku u < c.d ω u} := by
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have h1 : Ku u ≤ (Finset.range u₀).sup Ku := Finset.le_sup (Finset.mem_range.2 hu)
      have h2 : (Finset.range u₀).sup Ku ≤ 2 ^ a := le_trans (le_max_right _ _) ha
      have h3 : 1 ≤ c.C₀ := c.hC₀
      have h4 : 2 ^ a ≤ c.C₀ * 2 ^ a := Nat.le_mul_of_pos_left _ (by omega)
      omega
    exact le_trans hle (hKu u)
  · calc c.μ {ω | c.C₀ * 2 ^ a < c.d ω u}
        ≤ c.μ {ω | u < c.U ω} + (∑' k : ℕ, c.w (k + 2 ^ a)) := c.measure_gt_le a u
      _ ≤ ε / 2 + ε / 2 := add_le_add (hu₀ u hu) hj'
      _ = ε := ENNReal.add_halves ε

end PCtx

end RecordTight


