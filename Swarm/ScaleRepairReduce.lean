/-
# Reducing the scale hypotheses to an almost-sure defect bound and the block estimate

`ScaleRepair.lean` replaces the empty `RecordTight.PCtx` by the satisfiable `PCtxR`, whose
stochastic fields are `hterm`, `hblk`, `hscale_good` (one good level per index) and `hstart`
(the transient at the level-dependent start index).  This file *derives* `hscale_good` and
`hstart` from

* `hblk`, the paper's block estimate `(blkprob)`;
* summability of the dyadic block profile `∑_r p (2 ^ (g r))`;
* `hdef`, the almost-sure statement that the record defect is eventually below the scale,
  `∀ᵐ ω, ∀ᶠ r, d ω r ≤ 2 ^ (g r)`;
* monotonicity and the arithmetic of the scale, `hmono` and `a ≤ g (2 ^ (a+1))`.

The derivation is the paper's Borel–Cantelli step: the events
`E_r = {d_r ≤ 2^(g r)} ∩ {¬ Good r (2^(g r))}` have `μ (E_r) ≤ p (2^(g r))` for `r ≥ 2 C₀`
(and mass at most `1` for the finitely many smaller `r`), so almost every trajectory is in only
finitely many of them; combined with `hdef` this gives goodness at the scale eventually, and the
measurable threshold is extracted by `exists_measurable_threshold`.

Consequently the residual analytic premises of the scale route are exactly
`hterm`, `hblk` and `hdef` (plus the deterministic scale arithmetic, and summability).
-/
import Swarm.ScaleRepair

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

namespace SwarmM4

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Measurable thresholds from almost-sure events -/

/-- **From an almost-sure eventually-true family with measurable slices, extract a measurable
threshold.** -/
theorem exists_measurable_threshold {μ : Measure Ω} {P : Ω → ℕ → Prop}
    (hP : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, P ω n)
    (hmeas : ∀ n, MeasurableSet {ω | P ω n}) :
    ∃ R : Ω → ℕ, Measurable R ∧ ∀ᵐ ω ∂μ, ∀ n, R ω ≤ n → P ω n := by
  classical
  set A : Set Ω := {ω | ∃ N, ∀ n, N ≤ n → P ω n} with hA
  have hslice : ∀ N : ℕ, MeasurableSet {ω : Ω | ∀ n, N ≤ n → P ω n} := by
    intro N
    have hEq : {ω : Ω | ∀ n, N ≤ n → P ω n} = ⋂ k : ℕ, {ω | P ω (N + k)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h k; exact h (N + k) (Nat.le_add_right N k)
      · intro h n hn
        have h' := h (n - N)
        have hN : N + (n - N) = n := by omega
        rwa [hN] at h'
    rw [hEq]
    exact MeasurableSet.iInter fun k => hmeas (N + k)
  have hAmeas : MeasurableSet A := by
    have hEq : A = ⋃ N : ℕ, {ω : Ω | ∀ n, N ≤ n → P ω n} := by
      ext ω
      simp only [hA, Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [hEq]
    exact MeasurableSet.iUnion hslice
  have haeA : ∀ᵐ ω ∂μ, ω ∈ A := by
    filter_upwards [hP] with ω hω
    exact (eventually_atTop.1 hω).imp fun N hN => fun n hn => hN n hn
  set Q : ℕ → Ω → Prop := fun N ω => (∀ n, N ≤ n → P ω n) ∨ ω ∉ A with hQ
  have hQmeas : ∀ N, MeasurableSet {ω | Q N ω} := by
    intro N
    simp only [hQ, Set.ofPred_or]
    exact (hslice N).union hAmeas.compl
  have hex : ∀ ω, ∃ N, Q N ω := by
    intro ω
    by_cases h : ω ∈ A
    · obtain ⟨N, hN⟩ := h
      exact ⟨N, Or.inl hN⟩
    · exact ⟨0, Or.inr h⟩
  have hfib : ∀ k : ℕ, MeasurableSet {ω : Ω | Nat.find (hex ω) = k} := by
    intro k
    have hEq : {ω : Ω | Nat.find (hex ω) = k}
        = {ω | Q k ω} ∩ ⋂ m ∈ Finset.range k, {ω | ¬ Q m ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range]
      constructor
      · intro h
        refine ⟨h ▸ Nat.find_spec (hex ω), fun m hm hQm => ?_⟩
        exact Nat.find_min (hex ω) (h.symm ▸ hm) hQm
      · rintro ⟨hQk, hmin⟩
        refine (Nat.find_eq_iff (hex ω)).2 ⟨hQk, fun m hm => ?_⟩
        by_contra hc
        exact hmin m hm hc
    rw [hEq]
    refine (hQmeas k).inter ?_
    exact MeasurableSet.biInter (Finset.countable_toSet _) fun m _ => (hQmeas m).compl
  have hRmeas : Measurable fun ω : Ω => Nat.find (hex ω) :=
    measurable_to_countable fun y => hfib (Nat.find (hex y))
  refine ⟨fun ω => Nat.find (hex ω), hRmeas, ?_⟩
  filter_upwards [haeA] with ω hωA n hn
  rcases Nat.find_spec (hex ω) with h | h
  · exact h n hn
  · exact absurd hωA h

/-- Evaluation of a measurable `ℕ`-valued kernel at a measurable random index is measurable. -/
theorem measurable_apply_comp {d : Ω → ℕ → ℕ} (hd : Measurable d) {R : Ω → ℕ}
    (hR : Measurable R) : Measurable fun ω => d ω (R ω) := by
  have hfib : ∀ n : ℕ, MeasurableSet {ω | d ω (R ω) = n} := by
    intro n
    have hEq : {ω | d ω (R ω) = n} = ⋃ k : ℕ, ({ω | R ω = k} ∩ {ω | d ω k = n}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨R ω, rfl, h⟩
      · rintro ⟨k, hk, hd'⟩; simpa [hk] using hd'
    rw [hEq]
    exact MeasurableSet.iUnion fun k =>
      (hR (measurableSet_singleton k)).inter
        ((measurable_pi_apply k).comp hd (measurableSet_singleton n))
  exact measurable_to_countable (f := fun ω : Ω => d ω (R ω)) fun y => hfib (d y (R y))

/-! ### The Borel–Cantelli step -/

/-- **Goodness at the scale, eventually, from the block estimate.** -/
theorem ae_eventually_good_of_blk {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : Ω → ℕ → ℕ} {Good : Ω → ℕ → ℕ → Prop} {p : ℕ → ℝ≥0∞} {C₀ : ℕ} {g : ℕ → ℕ}
    (hd : Measurable d) (hG : ∀ r ℓ, MeasurableSet {ω | Good ω r ℓ})
    (hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      μ ({ω | d ω r ≤ ℓ} ∩ {ω | ¬ Good ω r ℓ}) ≤ p ℓ)
    (hbound : ∀ r, 2 * C₀ ≤ r → 2 * C₀ * 2 ^ g r ≤ r)
    (hsum : (∑' r : ℕ, p (2 ^ g r)) ≠ ⊤)
    (hdef : ∀ᵐ ω ∂μ, ∀ᶠ r in atTop, d ω r ≤ 2 ^ g r) :
    ∀ᵐ ω ∂μ, ∀ᶠ r in atTop, Good ω r (2 ^ g r) := by
  have hEmeas : ∀ r : ℕ, MeasurableSet
      ({ω | d ω r ≤ 2 ^ g r} ∩ {ω | ¬ Good ω r (2 ^ g r)}) := fun r =>
    ((measurable_pi_apply r).comp hd measurableSet_Iic).inter (hG r (2 ^ g r)).compl
  -- the per-index bound
  have hper : ∀ r : ℕ, μ ({ω | d ω r ≤ 2 ^ g r} ∩ {ω | ¬ Good ω r (2 ^ g r)})
      ≤ if r < 2 * C₀ then 1 else p (2 ^ g r) := by
    intro r
    by_cases hr : r < 2 * C₀
    · rw [if_pos hr]
      exact le_trans (measure_mono (Set.subset_univ _)) (by simp)
    · rw [if_neg hr]
      have hr' : 2 * C₀ ≤ r := by omega
      refine hblk (2 ^ g r) Nat.one_le_two_pow r ?_
      calc C₀ * 2 ^ g r ≤ 2 * C₀ * 2 ^ g r := by
            have : (1 : ℕ) ≤ 2 := by norm_num
            nlinarith [Nat.one_le_two_pow (n := g r), Nat.zero_le C₀]
        _ ≤ r := hbound r hr'
  have hfin : (∑' r : ℕ, (if r < 2 * C₀ then (1 : ℝ≥0∞) else 0)) = ((2 * C₀ : ℕ) : ℝ≥0∞) := by
    have hzero : ∀ b ∉ Finset.range (2 * C₀),
        (if b < 2 * C₀ then (1 : ℝ≥0∞) else 0) = 0 := by
      intro b hb
      have hnb : ¬ b < 2 * C₀ := by simpa [Finset.mem_range] using hb
      simp [hnb]
    rw [tsum_eq_sum (s := Finset.range (2 * C₀)) hzero]
    have hone : ∀ b ∈ Finset.range (2 * C₀),
        (if b < 2 * C₀ then (1 : ℝ≥0∞) else 0) = 1 := by
      intro b hb
      have hb' : b < 2 * C₀ := Finset.mem_range.1 hb
      simp [hb']
    rw [Finset.sum_congr rfl hone]
    simp
  have hb : (∑' r : ℕ, μ ({ω | d ω r ≤ 2 ^ g r} ∩ {ω | ¬ Good ω r (2 ^ g r)}))
      ≤ ((2 * C₀ : ℕ) : ℝ≥0∞) + ∑' r : ℕ, p (2 ^ g r) := by
    calc (∑' r : ℕ, μ ({ω | d ω r ≤ 2 ^ g r} ∩ {ω | ¬ Good ω r (2 ^ g r)}))
        ≤ ∑' r : ℕ, ((if r < 2 * C₀ then (1 : ℝ≥0∞) else 0) + p (2 ^ g r)) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          refine le_trans (hper r) ?_
          by_cases hr : r < 2 * C₀ <;> simp [hr]
      _ = (∑' r : ℕ, (if r < 2 * C₀ then (1 : ℝ≥0∞) else 0)) + ∑' r : ℕ, p (2 ^ g r) :=
          ENNReal.tsum_add
      _ = ((2 * C₀ : ℕ) : ℝ≥0∞) + ∑' r : ℕ, p (2 ^ g r) := by rw [hfin]
  have htop : ((2 * C₀ : ℕ) : ℝ≥0∞) + (∑' r : ℕ, p (2 ^ g r)) ≠ ⊤ := by
    have h2 : ((2 * C₀ : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    exact ENNReal.add_ne_top.2 ⟨by simpa using h2, hsum⟩
  have hEsum : (∑' r : ℕ, μ ({ω | d ω r ≤ 2 ^ g r} ∩ {ω | ¬ Good ω r (2 ^ g r)})) ≠ ⊤ :=
    ne_top_of_le_ne_top htop hb
  filter_upwards [ae_eventually_notMem hEsum, hdef] with ω hnot hdω
  filter_upwards [hnot, hdω] with r hnr hdr
  by_contra hng
  exact hnr ⟨hdr, hng⟩

/-! ### The reduced interface -/

/-- **`PCtxR` from `hterm`, `hblk`, the almost-sure defect bound and the scale arithmetic.**

WARNING: `hgpow` and `hbound` together force `C₀ ≤ 1`; see
`HblkScale.scale_hypotheses_incompatible`.  This constructor is retained only for the original
reduction and its explicit vacuity check.  At the paper's constants use
`HblkScale.PCtxR.of_eventual_pow`, which has a compatible power-indexed hypothesis. -/
noncomputable def PCtxR.of_eventual
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B C₀ : ℕ) (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀)
    (d : Ω → ℕ → ℕ) (Good : Ω → ℕ → ℕ → Prop) (p : ℕ → ℝ≥0∞) (g : ℕ → ℕ)
    (hd : Measurable d) (hG : ∀ r ℓ, MeasurableSet {ω | Good ω r ℓ})
    (hS : ∀ ω r L, Good ω r L → d ω r ≤ L →
      d ω (r + B * L) ≤ L / 2 ∧ ∀ u, r ≤ u → u ≤ r + B * L → d ω u ≤ C₀ * L)
    (hterm : ∀ r L, 1 ≤ L → ∀ᵐ ω ∂μ, ∃ j, Good ω r (2 ^ j * L))
    (hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      μ ({ω | d ω r ≤ ℓ} ∩ {ω | ¬ Good ω r ℓ}) ≤ p ℓ)
    (hmono : ∀ r r', r ≤ r' → g r ≤ g r')
    (hbound : ∀ r, 2 * C₀ ≤ r → 2 * C₀ * 2 ^ g r ≤ r)
    (hgpow : ∀ a, a ≤ g (2 ^ (a + 1)))
    (hsum : (∑' r : ℕ, p (2 ^ g r)) ≠ ⊤)
    (hdef : ∀ᵐ ω ∂μ, ∀ᶠ r in atTop, d ω r ≤ 2 ^ g r) :
    PCtxR Ω := by
  classical
  -- measurable thresholds: for the defect, and for the goodness at the scale
  have hdef' : ∀ᵐ ω ∂μ, ∀ᶠ r in atTop, d ω r ≤ 2 ^ g r := hdef
  have hex₀ : ∃ R : Ω → ℕ, Measurable R ∧ ∀ᵐ ω ∂μ, ∀ n, R ω ≤ n → d ω n ≤ 2 ^ g n :=
    exists_measurable_threshold (P := fun ω n => d ω n ≤ 2 ^ g n) hdef'
      (fun r => (measurable_pi_apply r).comp hd measurableSet_Iic)
  have hex₁ : ∃ R : Ω → ℕ, Measurable R ∧ ∀ᵐ ω ∂μ, ∀ n, R ω ≤ n → Good ω n (2 ^ g n) :=
    exists_measurable_threshold (P := fun ω n => Good ω n (2 ^ g n))
      (ae_eventually_good_of_blk hd hG hblk hbound hsum hdef) (fun r => hG r (2 ^ g r))
  set R₀ : Ω → ℕ := Classical.choose hex₀ with hR₀def
  have hR₀meas : Measurable R₀ := (Classical.choose_spec hex₀).1
  have hR₀ : ∀ᵐ ω ∂μ, ∀ n, R₀ ω ≤ n → d ω n ≤ 2 ^ g n := (Classical.choose_spec hex₀).2
  set R₁ : Ω → ℕ := Classical.choose hex₁ with hR₁def
  have hR₁meas : Measurable R₁ := (Classical.choose_spec hex₁).1
  have hR₁ : ∀ᵐ ω ∂μ, ∀ n, R₁ ω ≤ n → Good ω n (2 ^ g n) := (Classical.choose_spec hex₁).2
  refine
    { μ := μ, hprob := inferInstance, B := B, C₀ := C₀, d := d, Good := Good
      R := fun a ω => max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1)))
      p := p, g := g, hB := hB, hC₀ := hC₀, hd := hd
      hdR := ?_, hg := hG, hRmeas := ?_, hRge := ?_, hS := hS, hterm := hterm, hblk := hblk
      hscale_mono := hmono, hscale_bound := hbound, hscale_good := ?_, hstart := ?_ }
  · intro a
    exact measurable_apply_comp hd (by
      exact ((hR₀meas.max hR₁meas).max (measurable_const.max measurable_const)))
  · intro a
    exact ((hR₀meas.max hR₁meas).max (measurable_const.max measurable_const))
  · intro a ω
    have h1 : 2 * C₀ ≤ max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1))) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    exact h1
  · intro a
    filter_upwards [hR₁] with ω hω r hr
    exact hω r (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr)
  · intro a
    filter_upwards [hR₀, hR₁] with ω h₀ h₁
    have hRge : max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1)))
        = max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1))) := rfl
    have hle₀ : R₀ ω ≤ max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1))) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hpow : 2 ^ (a + 1) ≤ max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1))) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hd0 : d ω (max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1)))) ≤ 2 ^ g _ := h₀ _ hle₀
    have hmono' : g (2 ^ (a + 1)) ≤ g (max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1)))) :=
      hmono _ _ hpow
    have h2a : 2 ^ a ≤ 2 ^ g (max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1)))) := by
      have h1 : a ≤ g (max (max (R₀ ω) (R₁ ω)) (max (2 * C₀) (2 ^ (a + 1)))) :=
        le_trans (hgpow a) (hmono _ _ hpow)
      exact Nat.pow_le_pow_right (by norm_num) h1
    exact max_le h2a hd0

/-- **Tightness from the reduced premises.**

With the certificate series finite as well, the `PCtxR` of `PCtxR.of_eventual` gives record-distance
tightness.  Compare `ScaleTight.PCtx.tightness`, whose hypothesis set is empty. -/
theorem tightness_of_eventual
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B C₀ : ℕ) (hB : 1 ≤ B) (hC₀ : 1 ≤ C₀)
    (d : Ω → ℕ → ℕ) (Good : Ω → ℕ → ℕ → Prop) (p : ℕ → ℝ≥0∞) (g : ℕ → ℕ)
    (hd : Measurable d) (hG : ∀ r ℓ, MeasurableSet {ω | Good ω r ℓ})
    (hS : ∀ ω r L, Good ω r L → d ω r ≤ L →
      d ω (r + B * L) ≤ L / 2 ∧ ∀ u, r ≤ u → u ≤ r + B * L → d ω u ≤ C₀ * L)
    (hterm : ∀ r L, 1 ≤ L → ∀ᵐ ω ∂μ, ∃ j, Good ω r (2 ^ j * L))
    (hblk : ∀ ℓ, 1 ≤ ℓ → ∀ r, C₀ * ℓ ≤ r →
      μ ({ω | d ω r ≤ ℓ} ∩ {ω | ¬ Good ω r ℓ}) ≤ p ℓ)
    (hmono : ∀ r r', r ≤ r' → g r ≤ g r')
    (hbound : ∀ r, 2 * C₀ ≤ r → 2 * C₀ * 2 ^ g r ≤ r)
    (hgpow : ∀ a, a ≤ g (2 ^ (a + 1)))
    (hsum₂ : (∑' r : ℕ, p (2 ^ g r)) ≠ ⊤)
    (hdef : ∀ᵐ ω ∂μ, ∀ᶠ r in atTop, d ω r ≤ 2 ^ g r)
    (hcert : (∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ) ≠ ⊤)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K' : ℕ, ∀ u : ℕ, μ {ω | K' < d ω u} ≤ ε := by
  classical
  let c : PCtxR Ω := PCtxR.of_eventual μ B C₀ hB hC₀ d Good p g hd hG hS hterm hblk hmono
    hbound hgpow hsum₂ hdef
  have hw : ∀ ℓ : ℕ, c.w ℓ = ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ := fun ℓ => rfl
  have hcert' : (∑' ℓ : ℕ, c.w ℓ) ≠ ⊤ := by
    have hEq : (∑' ℓ : ℕ, c.w ℓ) = ∑' ℓ : ℕ, ((4 * B * ℓ + 1 : ℕ) : ℝ≥0∞) * p ℓ := by
      simp only [hw]
    rw [hEq]
    exact hcert
  have hres := c.tightness hcert' ε hε
  simpa [c, PCtxR.of_eventual] using hres

end SwarmM4
