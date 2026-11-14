/-
# A satisfiable replacement for the scale-based tightness interface

`ScaleVacuous.lean` proves that `RecordTight.PCtx` (`Swarm/ScaleTight.lean`) has no
instance, so its tightness theorem is vacuous.  This file repairs the interface and re-proves the
tightness conclusion for the repaired one.

The two defects and their repairs:

* `hscale_bound : ∀ r, 2 * C₀ * 2 ^ (g r) ≤ r` is false at `r = 0..2C₀-1`, where no positive
  dyadic scale can sit below `r / (2C₀)`.  Repair: quantify only over `r ≥ 2 C₀`, and record the
  deterministic side condition `hRge : ∀ a ω, 2 C₀ ≤ R a ω` that lets every certificate index
  satisfy it.
* `hstart : ∀ a, ∀ᵐ ω, max (2 ^ a) (d ω (R ω)) ≤ 2 ^ (g (R ω))` is impossible for a probability
  measure because `g (R ω)` is finite: it forces the scale at the start index to exceed `2 ^ a`
  for every level `a` simultaneously.  The paper only needs, *for each fixed level* `a`, a
  (random) start index beyond which that level is below the scale.  Repair: make the start index
  depend on the level, `R : ℕ → Ω → ℕ`, and keep the almost-sure statement per level.

`PCtxR.measure_gt_le` and `PCtxR.tightness` re-prove the covering/tightness conclusion with these
repairs; the proof is the argument of `ScaleTight.lean` with `R` replaced by `R a`.
`PCtxR.tightness` keeps the same conclusion, `∃ K', ∀ u, μ {K' < d u} ≤ ε`.

`example_PCtxR` below exhibits an explicit instance on `Unit` with `d ≡ 0`, `Good ≡ True`,
`g r = r.log2 - 1`, `R a = 2 ^ (a+1)`, so the repaired interface is non-vacuous; the residual
inputs (`hterm`, `hblk`, `hscale_good`, `hstart`) are then genuine obligations for the model, as the
campaign README states.
-/
import Swarm.ScaleTight

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SwarmM4

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The repaired scale interface: `R` depends on the level `a`, and the scale bound is asserted
only where a positive dyadic scale can exist. -/
structure PCtxR (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  hprob : IsProbabilityMeasure μ
  B : ℕ
  C₀ : ℕ
  d : Ω → ℕ → ℕ
  Good : Ω → ℕ → ℕ → Prop
  R : ℕ → Ω → ℕ
  p : ℕ → ℝ≥0∞
  g : ℕ → ℕ
  hB : 1 ≤ B
  hC₀ : 1 ≤ C₀
  hd : Measurable d
  hdR : ∀ a, Measurable fun ω => d ω (R a ω)
  hg : ∀ r ℓ, MeasurableSet {ω | Good ω r ℓ}
  hRmeas : ∀ a, Measurable (R a)
  /-- The start index of the halving procedure for level `a` is past the scale's support. -/
  hRge : ∀ a ω, 2 * C₀ ≤ R a ω
  hS : ∀ ω r L, Good ω r L → d ω r ≤ L →
    d ω (r + B * L) ≤ L / 2 ∧ ∀ u, r ≤ u → u ≤ r + B * L → d ω u ≤ C₀ * L
  hterm : ∀ r L, 1 ≤ L → ∀ᵐ ω ∂μ, ∃ j, Good ω r (2 ^ j * L)
  hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
    μ ({ω | d ω r ≤ ℓ} ∩ {ω | ¬ Good ω r ℓ}) ≤ p ℓ
  hscale_mono : ∀ r r', r ≤ r' → g r ≤ g r'
  hscale_bound : ∀ r, 2 * C₀ ≤ r → 2 * C₀ * 2 ^ g r ≤ r
  hscale_good : ∀ a, ∀ᵐ ω ∂μ, ∀ r, R a ω ≤ r → Good ω r (2 ^ g r)
  hstart : ∀ a, ∀ᵐ ω ∂μ, max (2 ^ a) (d ω (R a ω)) ≤ 2 ^ g (R a ω)

namespace PCtxR

variable (c : PCtxR Ω)

lemma measurable_d (r : ℕ) : Measurable fun ω => c.d ω r :=
  (measurable_pi_apply r).comp c.hd

lemma measurable_gR (a : ℕ) : Measurable fun ω => c.g (c.R a ω) :=
  (measurable_of_countable (fun n : ℕ => c.g n)).comp (c.hRmeas a)

/-- The finite random initial transient, started at the level-dependent index `R a`. -/
noncomputable def U (a : ℕ) (ω : Ω) : ℕ := c.R a ω + 2 * c.B * 2 ^ c.g (c.R a ω)

lemma measurable_U (a : ℕ) : Measurable (c.U a) := by
  have h1 : Measurable fun ω => 2 ^ c.g (c.R a ω) :=
    (measurable_of_countable (fun n : ℕ => 2 ^ n)).comp (c.measurable_gR a)
  have h3 : Measurable fun ω => 2 * c.B * 2 ^ c.g (c.R a ω) := measurable_const.mul h1
  exact (c.hRmeas a).add h3

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
  have := c.hprob
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
    _ = ((Finset.Icc (u - 4 * c.B * (k + K)) u).card : ℝ≥0∞) * c.p (k + K) :=
        nsmul_eq_mul _ _
    _ ≤ ((4 * c.B * (k + K) + 1 : ℕ) : ℝ≥0∞) * c.p (k + K) := by
        gcongr
        rw [Nat.card_Icc]
        omega
    _ = c.w (k + K) := by simp only [w]

/-- **Per-level bound.**  For every level `a` and index `u`, the probability that the record
distance at `u` exceeds `C₀ 2^a` is at most the probability of the initial transient plus the total
certificate probability past level `2^a`. -/
theorem measure_gt_le (a u : ℕ) :
    c.μ {ω | c.C₀ * 2 ^ a < c.d ω u} ≤
      c.μ {ω | u < c.U a ω} + ∑' k : ℕ, c.w (k + 2 ^ a) := by
  have := c.hprob
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
      (∀ r, c.R a ω ≤ r → c.Good ω r (2 ^ c.g r)) ∧
      (max (2 ^ a) (c.d ω (c.R a ω)) ≤ 2 ^ c.g (c.R a ω)) :=
    hterm_all.and ((c.hscale_good a).and (c.hstart a))
  have hsub : {ω | c.C₀ * 2 ^ a < c.d ω u} ≤ᵐ[c.μ]
      Set.union {ω | u < c.U a ω} (c.certSet (2 ^ a) u) := by
    filter_upwards [hae] with ω hω hx
    obtain ⟨htermω, hgoodω, hstartω⟩ := hω
    by_cases hu : u < c.U a ω
    · exact Or.inl hu
    · push Not at hu
      have hK1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      let ctx : RecordTight.Ctx :=
        { K := 2 ^ a, B := c.B, C₀ := c.C₀, d := fun r => c.d ω r,
          Good := fun r ℓ => c.Good ω r ℓ, r₀ := c.R a ω, L₀ := 2 ^ c.g (c.R a ω),
          hterm := fun r L hKL => htermω r L (le_trans hK1 hKL),
          hS := fun r L hG hd => c.hS ω r L hG hd,
          hB := c.hB, hK := hK1, hstart := hstartω }
      have hga : ∀ r, c.R a ω ≤ r → a ≤ c.g r := by
        intro r hr
        have h2 := c.hscale_mono (c.R a ω) r hr
        have h3 : 2 ^ a ≤ 2 ^ c.g (c.R a ω) := le_trans (le_max_left _ _) hstartω
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
          ⟨c.g (c.R a ω) - a, by
            have h1 : 2 ^ (c.g (c.R a ω) - a) * 2 ^ a = 2 ^ c.g (c.R a ω) := by
              rw [← pow_add, Nat.sub_add_cancel (hga (c.R a ω) (le_refl _))]
            rw [h1], le_rfl⟩
          (fun r hr => by
            have h1 : 2 ^ (c.g r - a) * 2 ^ a = 2 ^ c.g r := by
              rw [← pow_add, Nat.sub_add_cancel (hga r hr)]
            rw [h1]
            exact c.hscale_bound r (le_trans (c.hRge a ω) hr)) hu hx
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
  have := c.hprob
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

/-- **Tightness for the repaired interface.**  Same conclusion as `RecordTight.PCtx.tightness`,
but from a structure that has instances (`example_PCtxR`).

The construction is the one of `ScaleTight.lean`; the difference is that the level `a` is chosen
*before* the transient index `u₀`, because the transient now depends on `a`.  The final threshold
is `max (C₀ 2^a) (sup_{u < u₀} Ku u)`. -/
theorem tightness
    (hsum : (∑' ℓ : ℕ, c.w ℓ) ≠ ⊤)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K' : ℕ, ∀ u : ℕ, c.μ {ω | K' < c.d ω u} ≤ ε := by
  have := c.hprob
  have htail : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → (∑' k : ℕ, c.w (k + m)) ≤ ε / 2 := by
    have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
    have ht := ENNReal.tendsto_sum_nat_add c.w hsum
    have hev : ∀ᶠ m : ℕ in atTop, (∑' k : ℕ, c.w (k + m)) ≤ ε / 2 :=
      ENNReal.tendsto_nhds_zero.1 ht (ε / 2) hε2
    exact eventually_atTop.1 hev
  obtain ⟨M, hM⟩ := htail
  -- choose the level first, above the tail threshold
  obtain ⟨a, ha⟩ : ∃ a : ℕ, M ≤ 2 ^ a := by
    refine ⟨M + 1, ?_⟩
    have hlt := Nat.lt_two_pow_self (n := M)
    omega
  -- the transient for this level
  have htend := c.tendsto_measure_lt_nat (c.U a) (c.measurable_U a)
  have hev : ∀ᶠ u : ℕ in atTop, c.μ {ω | u < c.U a ω} ≤ ε / 2 :=
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
  refine ⟨max (c.C₀ * 2 ^ a) ((Finset.range u₀).sup Ku), fun u => ?_⟩
  have hj' : (∑' k : ℕ, c.w (k + 2 ^ a)) ≤ ε / 2 := hM (2 ^ a) ha
  rcases lt_or_ge u u₀ with hu | hu
  · -- the finitely many early indices
    have hle : c.μ {ω | max (c.C₀ * 2 ^ a) ((Finset.range u₀).sup Ku) < c.d ω u} ≤
        c.μ {ω | Ku u < c.d ω u} := by
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have h1 : Ku u ≤ (Finset.range u₀).sup Ku := Finset.le_sup (Finset.mem_range.2 hu)
      have h2 : (Finset.range u₀).sup Ku ≤ max (c.C₀ * 2 ^ a) ((Finset.range u₀).sup Ku) :=
        le_max_right _ _
      omega
    exact le_trans hle (hKu u)
  · -- the indices past the transient
    have hle : c.μ {ω | max (c.C₀ * 2 ^ a) ((Finset.range u₀).sup Ku) < c.d ω u} ≤
        c.μ {ω | c.C₀ * 2 ^ a < c.d ω u} := by
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have := le_max_left (c.C₀ * 2 ^ a) ((Finset.range u₀).sup Ku)
      omega
    calc c.μ {ω | max (c.C₀ * 2 ^ a) ((Finset.range u₀).sup Ku) < c.d ω u}
        ≤ c.μ {ω | c.C₀ * 2 ^ a < c.d ω u} := hle
      _ ≤ c.μ {ω | u < c.U a ω} + (∑' k : ℕ, c.w (k + 2 ^ a)) := c.measure_gt_le a u
      _ ≤ ε / 2 + ε / 2 := add_le_add (hu₀ u hu) hj'
      _ = ε := ENNReal.add_halves ε

end PCtxR

/-! ### Non-vacuity of the repaired interface -/

open scoped Classical in
/-- The level scale used in the example: `g r = r.log2 - 1`, the exponent of the largest power of
two at most `r / 2`. -/
noncomputable def gex (r : ℕ) : ℕ := r.log2 - 1

lemma two_pow_log2_le {n : ℕ} (hn : n ≠ 0) : 2 ^ n.log2 ≤ n :=
  (Nat.le_log2 hn).1 le_rfl

lemma log2_mono' {a b : ℕ} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; exact Nat.zero_le _
  · rw [Nat.le_log2 (by omega)]
    exact le_trans (two_pow_log2_le ha.ne') h

lemma gex_mono {r r' : ℕ} (h : r ≤ r') : gex r ≤ gex r' :=
  Nat.sub_le_sub_right (log2_mono' h) 1

lemma gex_bound {r : ℕ} (hr : 2 ≤ r) : 2 * 2 ^ gex r ≤ r := by
  have h2 : r ≠ 0 := by omega
  have hlog : 1 ≤ r.log2 := (Nat.le_log2 h2).2 (by simpa using hr)
  have hpos : 1 ≤ r.log2 := hlog
  have hsplit : 2 ^ gex r = 2 ^ (r.log2 - 1) := rfl
  have hrec : 2 ^ (r.log2 - 1) * 2 = 2 ^ r.log2 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  have hle := two_pow_log2_le h2
  nlinarith [hrec, hle, Nat.one_le_two_pow (n := r.log2 - 1)]

lemma gex_pow (a : ℕ) : gex (2 ^ (a + 1)) = a := by
  have hne : 2 ^ (a + 1) ≠ 0 := by positivity
  have hlog : (2 ^ (a + 1)).log2 = a + 1 := by
    rw [Nat.log2_eq_iff hne]
    exact ⟨le_rfl, Nat.pow_lt_pow_right (by norm_num) (by omega)⟩
  unfold gex
  rw [hlog]
  omega

/-- **The repaired interface is inhabited**: a one-point probability space with `d ≡ 0`,
`Good ≡ True`, `p ≡ 0`, scale `g r = r.log2 - 1` and level-dependent start `R a = 2 ^ (a+1)`.

This is exactly what `RecordTight.PCtx` fails to have, and it is what makes the figures of
`ScaleRepair.lean` statements meaningful rather than vacuous.  The certificate series is finite
because `p ≡ 0`; the remaining fields hold trivially. -/
noncomputable def example_PCtxR : PCtxR Unit where
  μ := Measure.dirac ()
  hprob := inferInstance
  B := 1
  C₀ := 1
  d := fun _ _ => 0
  Good := fun _ _ _ => True
  R := fun a _ => 2 ^ (a + 1)
  p := fun _ => 0
  g := gex
  hB := le_rfl
  hC₀ := le_rfl
  hd := measurable_const
  hdR := fun _ => measurable_const
  hg := fun _ _ => MeasurableSet.univ
  hRmeas := fun _ => measurable_const
  hRge := by
    intro a ω
    have h : 2 ≤ 2 ^ (a + 1) := by
      have h1 : 2 ^ 1 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using h1
    simpa using h
  hS := by
    intro ω r L _ _; exact ⟨Nat.zero_le _, fun u _ _ => Nat.zero_le _⟩
  hterm := by intro r L _; exact Eventually.of_forall fun ω => ⟨0, trivial⟩
  hblk := by intro ℓ _ r _; simp
  hscale_mono := fun r r' h => gex_mono h
  hscale_bound := by
    intro r hr
    have h2 : 2 ≤ r := by
      have : 2 * 1 ≤ r := by simpa using hr
      omega
    simpa using gex_bound h2
  hscale_good := by intro a; exact Eventually.of_forall fun ω r _ => trivial
  hstart := by
    intro a
    refine Eventually.of_forall fun ω => ?_
    simp only [gex_pow]
    exact max_le le_rfl (Nat.zero_le _)

/-- The example has the tightness conclusion, unconditionally, so `PCtxR.tightness` is not
vacuously applied. -/
example (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K' : ℕ, ∀ u : ℕ, example_PCtxR.μ {ω | K' < example_PCtxR.d ω u} ≤ ε :=
  example_PCtxR.tightness (by simp [PCtxR.w, example_PCtxR]) ε hε

end SwarmM4
