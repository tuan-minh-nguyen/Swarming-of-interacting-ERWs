/-
# The finite coalescence induction in the paper's fluid block argument

This dependency-light file isolates the part of Proposition `tight` between
`(meet)`/`(coincide)` and the assertion that all fluid paths coalesce before
level `B - 2`. It imports no WCJF module.

For a finite nonempty family `x i t`, `leaders` is the set of maximisers and
`fluidGap` is the diameter of one configuration. `FluidMotionOn` is the fluid
inequality `0 ≤ x i t - x i s ≤ t - s` on the bounded time interval. It proves the paper's diameter-growth
inequality; unit Lipschitzness alone would only give a factor `2`.

`JoinRuleFrom x s₀ b T` is the remaining geometric input. At a proper leading
set, before the candidate deadline `s + b * diameter < T`, it supplies a later
time at which that leading set strictly increases, before the same candidate
deadline. This packages the paper's `(meet)`, its first-joining-time argument,
and preservation of the old leaders. `StickyOn` is `(coincide)` on the bounded
interval after `s₀`. Neither input is proved here, and no local good-event probability is asserted.

The main induction tracks both the time and diameter at the `q`-th joining
time. Strict growth of the leading set gives `q + 1 ≤ card(leaders)`. Thus
full coalescence occurs at a time at most

  `D * (1 + b)^(N - 1) - 1`,

and remains coalesced thereafter. With `D = 1 + 64*C` and `s₀ = 64*C`, this
is exactly the paper's `(1 + 64*C) * (1 + b)^(N - 1) - 1` bound. The separate
scalar hypotheses place that time below `B - 2` and below `T`.

Scope: this is a deterministic fluid-path ingredient for the halving part of
`(blkprob)`. It does not construct fluid limits, prove `JoinRuleFrom` from the
local good event, estimate its failure probability, or deduce `BadHalf`,
`QuarterGood`, tightness, `Ballistic`, or `MainClaim`.
-/

import Swarm.Imports

open Classical

namespace FluidMerge

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Largest coordinate of a finite nonempty configuration. -/
noncomputable def fluidMax (x : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty x

/-- Smallest coordinate of a finite nonempty configuration. -/
noncomputable def fluidMin (x : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty x

/-- Diameter of a finite nonempty configuration. -/
noncomputable def fluidGap (x : ι → ℝ) : ℝ := fluidMax x - fluidMin x

/-- The set of coordinates equal to the current maximum. -/
noncomputable def leaders (x : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => x i = fluidMax x)

@[simp] theorem mem_leaders {x : ι → ℝ} {i : ι} :
    i ∈ leaders x ↔ x i = fluidMax x := by
  simp [leaders]

/-- The leading set is nonempty, by finite maximiser attainment. -/
theorem leaders_nonempty (x : ι → ℝ) : (leaders x).Nonempty := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset ι)) Finset.univ_nonempty x
  refine ⟨i, mem_leaders.mpr ?_⟩
  change x i = Finset.univ.sup' Finset.univ_nonempty x
  exact hmax.symm

/-- The leading set is universal exactly when all coordinates equal the maximum. -/
theorem leaders_eq_univ_iff (x : ι → ℝ) :
    leaders x = Finset.univ ↔ ∀ i, x i = fluidMax x := by
  constructor
  · intro h i
    have hi : i ∈ leaders x := by
      rw [h]
      exact Finset.mem_univ i
    exact mem_leaders.mp hi
  · intro h
    ext i
    simp [h i]

/-- Configuration diameter is nonnegative. -/
theorem fluidGap_nonneg (x : ι → ℝ) : 0 ≤ fluidGap x := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset ι)) Finset.univ_nonempty x
  have hle : fluidMin x ≤ fluidMax x := by
    calc
      fluidMin x ≤ x i := by
        exact Finset.inf'_le (fun j => x j) (Finset.mem_univ i)
      _ = fluidMax x := hmax.symm
  unfold fluidGap
  linarith

/-- The fluid inequality on the paper's bounded time interval: paths are
nondecreasing and grow at speed at most one. -/
def FluidMotionOn (x : ι → ℝ → ℝ) (s₀ T : ℝ) : Prop :=
  ∀ i s t, s₀ ≤ s → s ≤ t → t ≤ T →
    0 ≤ x i t - x i s ∧ x i t - x i s ≤ t - s

/-- After `s₀`, every proper leading set has a strictly larger later leading
set, with a joining time no greater than the paper's candidate deadline. -/
def JoinRuleFrom (x : ι → ℝ → ℝ) (s₀ b T : ℝ) : Prop :=
  ∀ s, s₀ ≤ s → leaders (fun i => x i s) ≠ Finset.univ →
    s + b * fluidGap (fun i => x i s) < T →
    ∃ u, s ≤ u ∧ u ≤ s + b * fluidGap (fun i => x i s) ∧
      leaders (fun i => x i s) ⊂ leaders (fun i => x i u)

/-- Coordinates which coincide on the interval starting at `s₀` remain
coincident for as long as they stay in that interval. -/
def StickyOn (x : ι → ℝ → ℝ) (s₀ T : ℝ) : Prop :=
  ∀ i j s t, s₀ ≤ s → s ≤ t → t ≤ T → x i s = x j s → x i t = x j t

/-- The paper's `(diamgrow)` follows from the one-sided fluid inequalities.
Monotonicity controls the minimum without an extra elapsed-time term. -/
theorem fluidGap_growth {x : ι → ℝ → ℝ} {s₀ T : ℝ}
    (hmove : FluidMotionOn x s₀ T) {s t : ℝ}
    (hs₀ : s₀ ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    fluidGap (fun i => x i t) ≤ fluidGap (fun i => x i s) + (t - s) := by
  have hmax : fluidMax (fun i => x i t) ≤ fluidMax (fun i => x i s) + (t - s) := by
    unfold fluidMax
    refine Finset.sup'_le Finset.univ_nonempty _ (fun i hi => ?_)
    have hstep := (hmove i s t hs₀ hst htT).2
    have hbase : x i s ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => x j s) :=
      Finset.le_sup' (fun j => x j s) (Finset.mem_univ i)
    linarith
  have hmin : fluidMin (fun i => x i s) ≤ fluidMin (fun i => x i t) := by
    unfold fluidMin
    refine Finset.le_inf' Finset.univ_nonempty _ (fun i hi => ?_)
    calc
      Finset.univ.inf' Finset.univ_nonempty (fun j => x j s) ≤ x i s :=
        Finset.inf'_le (fun j => x j s) (Finset.mem_univ i)
      _ ≤ x i t := by
        have hstep := (hmove i s t hs₀ hst htT).1
        linarith
  unfold fluidGap
  linarith

/-- Monotonicity of the scale enclosing the `q`-th joining time and diameter. -/
theorem scale_mono {D b : ℝ} (hD : 0 ≤ D) (hb : 0 ≤ b)
    {q n : ℕ} (hqn : q ≤ n) :
    D * (1 + b) ^ q - 1 ≤ D * (1 + b) ^ n - 1 := by
  have hp : (1 + b) ^ q ≤ (1 + b) ^ n :=
    pow_le_pow_right₀ (by linarith) hqn
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hp hD) 1

/-- Induction on the number of nonleaders. The additional invariant
`q + 1 ≤ card(leaders)` is what converts strict leader growth into the
geometric time bound. -/
theorem exists_coalescence_aux (x : ι → ℝ → ℝ) (s₀ b D T : ℝ)
    (hmove : FluidMotionOn x s₀ T) (hjoin : JoinRuleFrom x s₀ b T)
    (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hlim : D * (1 + b) ^ (Fintype.card ι - 1) - 1 < T) :
    ∀ (fuel q : ℕ) (s : ℝ),
      Fintype.card ι - (leaders (fun i => x i s)).card ≤ fuel →
      q + 1 ≤ (leaders (fun i => x i s)).card →
      s₀ ≤ s →
      s ≤ D * (1 + b) ^ q - 1 →
      fluidGap (fun i => x i s) ≤ D * (1 + b) ^ q →
      ∃ u, s ≤ u ∧ u ≤ D * (1 + b) ^ (Fintype.card ι - 1) - 1 ∧
        leaders (fun i => x i u) = Finset.univ := by
  intro fuel
  induction fuel with
  | zero =>
      intro q s hfuel hcard hstart hs hgap
      have hzero : Fintype.card ι - (leaders (fun i => x i s)).card = 0 :=
        Nat.eq_zero_of_le_zero hfuel
      have hle := Finset.card_le_univ (leaders (fun i => x i s))
      have heqcard : (leaders (fun i => x i s)).card = Fintype.card ι := by omega
      refine ⟨s, le_rfl, ?_, Finset.eq_univ_of_card _ heqcard⟩
      exact hs.trans (scale_mono hD hb (by omega))
  | succ fuel ih =>
      intro q s hfuel hcard hstart hs hgap
      by_cases hfull : leaders (fun i => x i s) = Finset.univ
      · have hle := Finset.card_le_univ (leaders (fun i => x i s))
        rw [hfull] at hcard
        simp only [Finset.card_univ] at hcard
        refine ⟨s, le_rfl, ?_, hfull⟩
        exact hs.trans (scale_mono hD hb (by omega))
      · have hle := Finset.card_le_univ (leaders (fun i => x i s))
        have hnecard : (leaders (fun i => x i s)).card ≠ Fintype.card ι := by
          intro heq
          exact hfull (Finset.eq_univ_of_card _ heq)
        have hcardlt : (leaders (fun i => x i s)).card < Fintype.card ι := by omega
        have hqn : q + 1 ≤ Fintype.card ι - 1 := by omega
        have hnext : s + b * fluidGap (fun i => x i s) ≤
            D * (1 + b) ^ (q + 1) - 1 := by
          calc
            s + b * fluidGap (fun i => x i s) ≤
                (D * (1 + b) ^ q - 1) + b * (D * (1 + b) ^ q) :=
              add_le_add hs (mul_le_mul_of_nonneg_left hgap hb)
            _ = D * (1 + b) ^ (q + 1) - 1 := by
              rw [pow_succ]
              ring
        have hcand : s + b * fluidGap (fun i => x i s) < T :=
          hnext.trans_lt ((scale_mono hD hb hqn).trans_lt hlim)
        obtain ⟨u, hsu, hu, hss⟩ := hjoin s hstart hfull hcand
        have hcardgrow := Finset.card_lt_card hss
        have hnextcard : q + 1 + 1 ≤ (leaders (fun i => x i u)).card := by omega
        have hnextle := Finset.card_le_univ (leaders (fun i => x i u))
        have hfuelnext : Fintype.card ι - (leaders (fun i => x i u)).card ≤ fuel := by
          omega
        have huscale : u ≤ D * (1 + b) ^ (q + 1) - 1 := hu.trans hnext
        have hgapnext : fluidGap (fun i => x i u) ≤ D * (1 + b) ^ (q + 1) := by
          have hdelta : u - s ≤ b * fluidGap (fun i => x i s) := by linarith
          calc
            fluidGap (fun i => x i u) ≤
                fluidGap (fun i => x i s) + (u - s) :=
              fluidGap_growth hmove hstart hsu (hu.trans_lt hcand).le
            _ ≤ fluidGap (fun i => x i s) + b * fluidGap (fun i => x i s) := by
              exact add_le_add le_rfl hdelta
            _ ≤ D * (1 + b) ^ q + b * (D * (1 + b) ^ q) :=
              add_le_add hgap (mul_le_mul_of_nonneg_left hgap hb)
            _ = D * (1 + b) ^ (q + 1) := by
              rw [pow_succ]
              ring
        obtain ⟨v, huv, hv, hvlead⟩ := ih (q + 1) u hfuelnext hnextcard
          (hstart.trans hsu) huscale hgapnext
        exact ⟨v, hsu.trans huv, hv, hvlead⟩

/-- Strictly growing leaders force persistent full coalescence before the
geometric deadline, and sticky paths remain mutually equal afterwards within
the same time interval. -/
theorem exists_persistent_coalescence (x : ι → ℝ → ℝ) (s₀ b D T : ℝ)
    (hmove : FluidMotionOn x s₀ T) (hjoin : JoinRuleFrom x s₀ b T)
    (hsticky : StickyOn x s₀ T) (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hlim : D * (1 + b) ^ (Fintype.card ι - 1) - 1 < T)
    (hs₀ : s₀ ≤ D - 1) (hgap₀ : fluidGap (fun i => x i s₀) ≤ D) :
    ∃ u, s₀ ≤ u ∧ u ≤ D * (1 + b) ^ (Fintype.card ι - 1) - 1 ∧ u < T ∧
      ∀ t, u ≤ t → t ≤ T → ∀ i j, x i t = x j t := by
  have hcard₀ : 0 + 1 ≤ (leaders (fun i => x i s₀)).card := by
    simpa using (Finset.card_pos.mpr (leaders_nonempty (fun i => x i s₀)))
  obtain ⟨u, hsu, hu, hlead⟩ := exists_coalescence_aux x s₀ b D T hmove hjoin hD hb hlim
    (Fintype.card ι) 0 s₀ (Nat.sub_le _ _) hcard₀ le_rfl (by simpa using hs₀) (by simpa using hgap₀)
  refine ⟨u, hsu, hu, hu.trans_lt hlim, ?_⟩
  intro t ht htT i j
  have heq : x i u = x j u := by
    have hi := (leaders_eq_univ_iff (fun k => x k u)).mp hlead i
    have hj := (leaders_eq_univ_iff (fun k => x k u)).mp hlead j
    exact hi.trans hj.symm
  exact hsticky i j u t hsu ht htT heq

/-- The paper's scalar form. If the geometric joining bound is below `B - 2`
and `B - 2 < T`, all fluid paths are equal at one time below `B - 2` and at
every later time in the bounded interval. -/
theorem paper_fluid_coalesce_before_B_sub_two {N : ℕ} [Nonempty (Fin N)]
    (x : Fin N → ℝ → ℝ) {C b T : ℝ} {B : ℕ}
    (hC : 0 ≤ C) (hb : 0 ≤ b) (hmove : FluidMotionOn x (64 * C) T)
    (hjoin : JoinRuleFrom x (64 * C) b T) (hsticky : StickyOn x (64 * C) T)
    (hB : (1 + 64 * C) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2)
    (hBT : (B : ℝ) - 2 < T)
    (hgap₀ : fluidGap (fun i => x i (64 * C)) ≤ 1 + 64 * C) :
    ∃ u, 64 * C ≤ u ∧ u < (B : ℝ) - 2 ∧
      ∀ t, u ≤ t → t ≤ T → ∀ i j, x i t = x j t := by
  have hD : 0 ≤ 1 + 64 * C := by linarith
  have hstart : 64 * C ≤ (1 + 64 * C) - 1 := le_of_eq (by ring)
  have hB' : (1 + 64 * C) * (1 + b) ^ (Fintype.card (Fin N) - 1) - 1 < (B : ℝ) - 2 := by
    simpa using hB
  obtain ⟨u, hsu, hu, hT, hpersist⟩ := exists_persistent_coalescence x (64 * C) b (1 + 64 * C) T
    hmove hjoin hsticky hD hb (hB'.trans hBT) hstart hgap₀
  exact ⟨u, hsu, hu.trans_lt hB', hpersist⟩

/-- At a fully coalesced fluid configuration whose maximum is `B`, the
normalized record-defect expression `B - min_i x_i` is exactly zero. -/
theorem normalized_defect_zero_of_coalesced (z : ι → ℝ) {B : ℝ}
    (hlead : leaders z = Finset.univ) (hB : fluidMax z = B) :
    B - fluidMin z = 0 := by
  have hall := (leaders_eq_univ_iff z).mp hlead
  have hminmax : fluidMin z = fluidMax z := by
    apply le_antisymm
    · obtain ⟨i, hi⟩ := leaders_nonempty z
      have hmi : fluidMin z ≤ z i :=
        Finset.inf'_le (fun j => z j) (Finset.mem_univ i)
      exact hmi.trans_eq (mem_leaders.mp hi)
    · unfold fluidMin
      refine Finset.le_inf' Finset.univ_nonempty _ (fun i hi => ?_)
      rw [hall i]
  rw [hminmax, hB]
  ring

/-- The paper's displayed `BTchoice` inequality is stronger than the scalar
margin needed by the merge induction. -/
theorem paper_margin_of_BTchoice {N B : ℕ} {C b : ℝ}
    (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hchoice : (1 + 64 * C) * (1 + b) ^ N + 2 < (B : ℝ)) :
    (1 + 64 * C) * (1 + b) ^ (N - 1) - 1 < (B : ℝ) - 2 := by
  have hD : 0 ≤ 1 + 64 * C := by linarith
  have hmono := scale_mono hD hb (q := N - 1) (n := N) (Nat.sub_le N 1)
  linarith

end FluidMerge


