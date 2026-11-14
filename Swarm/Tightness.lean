/-
# Record-distance tightness from the paper's block estimate

This file turns the deterministic covering lemma of `TightCover.lean` into the measure-theoretic
statement the Krylov–Bogoliubov reduction needs, i.e. the conclusion of Prop. "tight" of
`main_1d_revised.tex`.

The data are a probability space `(Ω, μ)`, a sequence of record distances `d ω u = max_i d^i_u`,
the block-goodness relation `Good ω r L`, a "certificate" threshold `R` and a tail profile `p`.

Hypotheses (`ProbCtx`):

* `hS`: `Good ω r L` is the paper's conjunction of the three block inequalities, so that it
  implies `d ω (r+BL) ≤ L/2` and `d ω u ≤ C₀ L` for `u ∈ [r, r+BL]`;
* `hterm`: for each `r` and `L`, a.e. trajectory has a good block after finitely many doublings
  (the paper's almost-sure statements `(recordo)`);
* `hR`: a.e. trajectory, from some (random) index `R ω` on, a *failing* block at level `ℓ` can
  only happen when `2 C₀ ℓ ≤ r`.  This is exactly the Borel–Cantelli consequence the paper draws
  from `(recordo)` and `(blkprob)` with `λ(r)` the largest dyadic integer at most `r/(2C₀)`;
* `hblk`: the fluid-limit block estimate `(blkprob)`:
  `μ {d r ≤ ℓ} ∩ {Good r ℓ}ᶜ ≤ p ℓ` for `ℓ ≥ 1` and `C₀ ℓ ≤ r`.

Conclusions:

* `measure_gt_le`: for every level cap `K ≥ 1` and index `u`,
  `μ {d u > C₀ K} ≤ μ {u < U K} + ∑_{ℓ ≥ K} (4Bℓ+1) p ℓ`,
  where `U K` is the finite random initial transient `R + 2B max K (d R)`;
* `tightness`: if the tail sums of `(4Bℓ+1) p ℓ` vanish, the family of laws of `d u` is tight.

The union bound is over the certificates of `TightCover.exists_certificate`: at level `ℓ` there
are at most `4Bℓ + 1` integers `r ∈ [u - 4Bℓ, u]`, and each certificate event has probability at
most `p ℓ`.
-/
import Swarm.TightCover

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace RecordTight

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Probabilistic data for the tightness argument.  All hypotheses are stated without a level
cap so that they can be used at every `K ≥ 1`: `hterm` and `hR` are the paper's almost-sure
statements for all levels `L ≥ 1`, and `hblk` is the block estimate for all `ℓ ≥ 1`. -/
structure ProbCtx (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  hprob : IsProbabilityMeasure μ
  B : ℕ
  C₀ : ℕ
  d : Ω → ℕ → ℕ
  Good : Ω → ℕ → ℕ → Prop
  R : Ω → ℕ
  p : ℕ → ℝ≥0∞
  hB : 1 ≤ B
  hC₀ : 1 ≤ C₀
  hd : Measurable d
  hdR : Measurable fun ω => d ω (R ω)
  hg : ∀ r ℓ, MeasurableSet {ω | Good ω r ℓ}
  hRmeas : Measurable R
  hS : ∀ ω r L, Good ω r L → d ω r ≤ L →
    d ω (r + B * L) ≤ L / 2 ∧ ∀ u, r ≤ u → u ≤ r + B * L → d ω u ≤ C₀ * L
  hterm : ∀ r L, 1 ≤ L → ∀ᵐ ω ∂μ, ∃ j, Good ω r (2 ^ j * L)
  hR : ∀ᵐ ω ∂μ, ∀ r, R ω ≤ r → ∀ ℓ, 1 ≤ ℓ → d ω r ≤ ℓ → ¬ Good ω r ℓ → 2 * C₀ * ℓ ≤ r
  hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
    μ ({ω | d ω r ≤ ℓ} ∩ {ω | ¬ Good ω r ℓ}) ≤ p ℓ

namespace ProbCtx

variable (c : ProbCtx Ω)

lemma measurable_d (r : ℕ) : Measurable fun ω => c.d ω r :=
  (measurable_pi_apply r).comp c.hd

lemma measurable_dR : Measurable fun ω => c.d ω (c.R ω) := c.hdR

/-- The finite random initial transient of the halving procedure started at `R`. -/
noncomputable def U (K : ℕ) (ω : Ω) : ℕ := c.R ω + 2 * c.B * max K (c.d ω (c.R ω))

lemma measurable_U (K : ℕ) : Measurable (c.U K) := by
  have h1 : Measurable fun ω => 2 * c.B * max K (c.d ω (c.R ω)) :=
    (measurable_const.mul (measurable_const.max c.measurable_dR))
  exact c.hRmeas.add h1

/-- The certificate weight at level `ℓ`: the number `4Bℓ+1` of possible start indices times
the block estimate `p ℓ`. -/
noncomputable def w (ℓ : ℕ) : ℝ≥0∞ := ((4 * c.B * ℓ + 1 : ℕ) : ℝ≥0∞) * c.p ℓ

/-- The certificate set: `ω` carries a failing block at level `ℓ = k + K ≥ K` started at some
`r ∈ [u - 4Bℓ, u]` with `C₀ ℓ ≤ r` and `d ω r ≤ ℓ`.  Indexing the outer union by `k` (rather
than by `ℓ` with a side condition `K ≤ ℓ`) makes the union bound produce the shifted sum
`∑ k, (4B(k+K)+1) p (k+K)` directly, i.e. the tail of a single series. -/
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

/-- **Per-level bound.**  For every level cap `K ≥ 1` and index `u`, the probability that the
record distance at `u` exceeds `C₀ K` is at most the probability of the initial transient plus
the total certificate probability past level `K`. -/
theorem measure_gt_le (K u : ℕ) (hK : 1 ≤ K) :
    c.μ {ω | c.C₀ * K < c.d ω u} ≤
      c.μ {ω | u < c.U K ω} + ∑' k : ℕ, c.w (k + K) := by
  haveI := c.hprob
  -- the two almost-sure inputs, simultaneously
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
      (∀ r, c.R ω ≤ r → ∀ ℓ, 1 ≤ ℓ → c.d ω r ≤ ℓ → ¬ c.Good ω r ℓ → 2 * c.C₀ * ℓ ≤ r) :=
    hterm_all.and c.hR
  -- the a.e. set inclusion
  have hsub : {ω | c.C₀ * K < c.d ω u} ≤ᵐ[c.μ]
      Set.union {ω | u < c.U K ω} (c.certSet K u) := by
    filter_upwards [hae] with ω hω hx
    by_cases hu : u < c.U K ω
    · exact Or.inl hu
    · push_neg at hu
      obtain ⟨htermω, hRω⟩ := hω
      let ctx : Ctx :=
        { K := K, B := c.B, C₀ := c.C₀, d := fun r => c.d ω r,
          Good := fun r ℓ => c.Good ω r ℓ, r₀ := c.R ω, L₀ := max K (c.d ω (c.R ω)),
          hterm := fun r L hKL => htermω r L (le_trans hK hKL),
          hS := fun r L hG hd => c.hS ω r L hG hd,
          hB := c.hB, hK := hK, hstart := le_rfl }
      obtain ⟨r, ℓ, hKℓ, hdr, hng, hr0, hru, huℓ⟩ := ctx.exists_certificate hu hx
      have hℓ1 : 1 ≤ ℓ := le_trans hK hKℓ
      have hC₀ℓ : c.C₀ * ℓ ≤ r := by
        have h2 := hRω r hr0 ℓ hℓ1 hdr hng
        have h3 : c.C₀ * ℓ ≤ 2 * c.C₀ * ℓ := by nlinarith
        omega
      have hsub : u - 4 * c.B * ℓ ≤ r := Nat.sub_le_iff_le_add.2 huℓ
      refine Or.inr (Set.mem_iUnion.2 ⟨ℓ - K, ?_⟩)
      have hℓK : ℓ - K + K = ℓ := Nat.sub_add_cancel hKℓ
      rw [hℓK]
      refine Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
      · exact Finset.mem_Icc.2 ⟨hsub, hru⟩
      · rw [if_pos hC₀ℓ]
        exact ⟨hdr, hng⟩
  refine le_trans (measure_mono_ae hsub) (le_trans (measure_union_le _ _) ?_)
  exact add_le_add le_rfl (c.measure_certSet_le K u hK)

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

/-- **Tightness.**  If the total certificate probability `∑ ℓ, (4Bℓ+1) p ℓ` is finite, the
family of laws of the record distances `d u` is tight.  Finiteness is the only remaining
analytic input; the tail sums vanish by `ENNReal.tendsto_sum_nat_add`. -/
theorem tightness
    (hsum : (∑' ℓ : ℕ, c.w ℓ) ≠ ⊤)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K' : ℕ, ∀ u : ℕ, c.μ {ω | K' < c.d ω u} ≤ ε := by
  haveI := c.hprob
  -- the tail sums of the certificate probabilities vanish
  have htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, 1 ≤ K ∧
      (∑' k : ℕ, c.w (k + K)) ≤ ε := by
    intro ε' hε'
    have ht := ENNReal.tendsto_sum_nat_add c.w hsum
    have hev : ∀ᶠ K : ℕ in atTop, (∑' k : ℕ, c.w (k + K)) ≤ ε' :=
      ENNReal.tendsto_nhds_zero.1 ht ε' hε'
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hev
    exact ⟨max K₀ 1, le_max_right _ _, hK₀ _ (le_max_left _ _)⟩
  have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨K, hK, hKbound⟩ := htail (ε / 2) hε2
  -- the initial transient has vanishing probability
  have htend := c.tendsto_measure_lt_nat (c.U K) (c.measurable_U K)
  have hev : ∀ᶠ u : ℕ in atTop, c.μ {ω | u < c.U K ω} ≤ ε / 2 :=
    ENNReal.tendsto_nhds_zero.1 htend (ε / 2) hε2
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.1 hev
  -- the finitely many earlier indices
  have hsingle : ∀ u : ℕ, ∃ Ku : ℕ, c.μ {ω | Ku < c.d ω u} ≤ ε := by
    intro u
    have ht := c.tendsto_measure_lt_nat (fun ω => c.d ω u) (c.measurable_d u)
    have hev' : ∀ᶠ K' : ℕ in atTop, c.μ {ω | K' < c.d ω u} ≤ ε :=
      ENNReal.tendsto_nhds_zero.1 ht ε hε
    obtain ⟨a, ha⟩ := eventually_atTop.1 hev'
    exact ⟨a, ha a le_rfl⟩
  choose Ku hKu using hsingle
  refine ⟨max (c.C₀ * K) ((Finset.range u₀).sup Ku), fun u => ?_⟩
  have hmono : c.μ {ω | max (c.C₀ * K) ((Finset.range u₀).sup Ku) < c.d ω u} ≤
      c.μ {ω | c.C₀ * K < c.d ω u} := by
    refine measure_mono ?_
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact lt_of_le_of_lt (le_max_left _ _) hω
  rcases lt_or_ge u u₀ with hu | hu
  · have hle : c.μ {ω | max (c.C₀ * K) ((Finset.range u₀).sup Ku) < c.d ω u} ≤
        c.μ {ω | Ku u < c.d ω u} := by
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      exact lt_of_le_of_lt
        (le_trans (Finset.le_sup (Finset.mem_range.2 hu)) (le_max_right _ _)) hω
    exact le_trans hle (hKu u)
  · refine le_trans hmono (le_trans (c.measure_gt_le K u hK) ?_)
    calc c.μ {ω | u < c.U K ω} +
          (∑' k : ℕ, c.w (k + K))
        ≤ ε / 2 + ε / 2 := add_le_add (hu₀ u hu) hKbound
      _ = ε := ENNReal.add_halves ε

end ProbCtx

end RecordTight
