/-
# Total lift of a fluid limit defined on `Icc 0 T`

The fluid limit `x` of the record interpolants lives on the compact time interval
`Set.Icc (0 : ℝ) (T : ℝ)`.  `MeetBound` and the meeting-rule chain
(`MeetJoin.reaches_of_meetBound`, `MeetJoin.joinRuleFrom_of_meetBound`) are stated for total
functions `ℝ → ℝ`.  `lift` extends `x` by zero outside the interval, and the two agree on it,
so no information is lost.
-/
import Swarm.MeetFromClauses2
import Swarm.MeetJoin

open Filter Topology Set
open scoped BigOperators BoundedContinuousFunction

namespace M2Meet

open M2B FluidMerge FluidLimit Glue LocalFluid RecordDefect JoinStep

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Extend a function on `Icc 0 T` to all of `ℝ` by zero. -/
noncomputable def lift {T : ℕ} (x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)) (i : ι) (r : ℝ) : ℝ :=
  if h : r ∈ Set.Icc (0 : ℝ) (T : ℝ) then x i ⟨r, h⟩ else 0

/-- On the interval, the lift is the original fluid limit. -/
theorem lift_apply {T : ℕ} {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)} {i : ι} {r : ℝ}
    (h : r ∈ Set.Icc (0 : ℝ) (T : ℝ)) : lift x i r = x i ⟨r, h⟩ := by
  simp only [lift, dif_pos h]

/-- On the interval, the lift agrees with `M2B.fpos`. -/
theorem fpos_eq_lift {T : ℕ} {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)} {i : ι} {v : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) (T : ℝ)) : M2B.fpos x i hv = lift x i v :=
  (lift_apply hv).symm

/-- The lift is continuous on the interval. -/
theorem continuousOn_lift {T : ℕ} (x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)) (i : ι) :
    ContinuousOn (lift x i) (Set.Icc (0 : ℝ) (T : ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have h1 : (Set.Icc (0 : ℝ) (T : ℝ)).domRestrict (lift x i) = ⇑(x i) := by
    funext ⟨r, hr⟩
    exact lift_apply hr
  rw [h1]
  exact (x i).continuous

/-! ## 1. A positive separation margin from strict separation on a compact interval -/

/-- The strict separation of `MeetBound` on a compact interval has a positive margin. -/
theorem exists_sep_margin {x : ι → ℝ → ℝ} {s₀ T : ℝ}
    (hcont : ∀ i, ContinuousOn (x i) (Set.Icc s₀ T))
    {D J : Finset ι} (hD : D.Nonempty) (hJ : J.Nonempty)
    {s v : ℝ} (hs₀ : s₀ ≤ s) (hsv : s ≤ v) (hvT : v ≤ T)
    (hsep : ∀ r ∈ Set.Icc s v, ∀ i ∈ D, ∀ j ∈ J, x j r < x i r) :
    ∃ γ, 0 < γ ∧ ∀ r ∈ Set.Icc s v,
      γ ≤ D.inf' hD (fun i => x i r) - J.sup' hJ (fun j => x j r) := by
  classical
  have hsub : Set.Icc s v ⊆ Set.Icc s₀ T := fun u hu =>
    ⟨le_trans hs₀ hu.1, le_trans hu.2 hvT⟩
  have hcontInf : ContinuousOn (fun r => D.inf' hD (fun i => x i r)) (Set.Icc s v) := by
    have h := ContinuousOn.finset_inf' (s := D) (t := Set.Icc s v)
      (f := fun i (r : ℝ) => x i r) hD (fun i _ => (hcont i).mono hsub)
    have hh : (D.inf' hD (fun i (r : ℝ) => x i r)) = (fun r => D.inf' hD (fun i => x i r)) := by
      funext r
      exact Finset.inf'_apply hD (fun i (v : ℝ) => x i v) r
    rwa [hh] at h
  have hcontSup : ContinuousOn (fun r => J.sup' hJ (fun j => x j r)) (Set.Icc s v) := by
    have h := ContinuousOn.finset_sup' (s := J) (t := Set.Icc s v)
      (f := fun j (r : ℝ) => x j r) hJ (fun j _ => (hcont j).mono hsub)
    have hh : (J.sup' hJ (fun j (r : ℝ) => x j r)) = (fun r => J.sup' hJ (fun j => x j r)) := by
      funext r
      exact Finset.sup'_apply hJ (fun j (v : ℝ) => x j v) r
    rwa [hh] at h
  have hcontG : ContinuousOn
      (fun r => D.inf' hD (fun i => x i r) - J.sup' hJ (fun j => x j r)) (Set.Icc s v) :=
    hcontInf.sub hcontSup
  have hpos : ∀ r ∈ Set.Icc s v,
      0 < D.inf' hD (fun i => x i r) - J.sup' hJ (fun j => x j r) := by
    intro r hr
    obtain ⟨i, hi, hival⟩ := Finset.exists_mem_eq_inf' hD (fun i => x i r)
    obtain ⟨j, hj, hjval⟩ := Finset.exists_mem_eq_sup' hJ (fun j => x j r)
    have hlt := hsep r hr i hi j hj
    rw [hival, hjval]
    linarith
  obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn (⟨s, le_rfl, hsv⟩ : (Set.Icc s v).Nonempty) hcontG
  exact ⟨D.inf' hD (fun i => x i r₀) - J.sup' hJ (fun j => x j r₀), hpos r₀ hr₀,
    fun r hr => hmin hr⟩

/-- **The scalar fluid `(meet)` bound from the finite-scale clauses**, at the sharp window
origin `64⌈C⌉₊` and the sharp constant `2 C^2`. -/
theorem meetBound_of_clauses {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T : ℕ}
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hC : 0 < C) (hHT : 0 ≤ CT)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hL1 : ∀ n, 1 ≤ scale n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (FluidInterpolation.rawSample (scale n) (FluidInterpolation.rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i)) :
    MeetBound (fun i r => lift x i r) (64 * Nat.ceil C : ℝ) (2 * C ^ 2) (T : ℝ) := by
  classical
  have hC0 : (0 : ℝ) ≤ (64 * Nat.ceil C : ℝ) := by positivity
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := by positivity
  intro A hA s v hs₀ hsv hvT hAdef hAne hsep
  have hApos : A.Nonempty := hA
  have hJ : (Finset.univ \ A).Nonempty := by
    refine Finset.sdiff_nonempty.mpr ?_
    intro hsub
    exact hAne (Finset.eq_univ_iff_forall.mpr (fun i => hsub (Finset.mem_univ i)))
  have hJpos : (Finset.univ \ A).Nonempty := hJ
  rcases eq_or_lt_of_le hsv with heq | hlt
  · rw [← heq]
    simp only [sub_self]
    exact mul_nonneg (by positivity) (fluidGap_nonneg _)
  · have hceilpos : (0 : ℝ) < (Nat.ceil C : ℝ) := by
      have h1 : 0 < Nat.ceil C := Nat.ceil_pos.mpr hC
      exact_mod_cast h1
    have hs0 : 0 < s := lt_of_lt_of_le (by nlinarith : (0 : ℝ) < 64 * Nat.ceil C) hs₀
    have hsI : s ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨hs0.le, le_of_lt (lt_of_lt_of_le hlt hvT)⟩
    have hcontL : ∀ i, ContinuousOn (fun r => lift x i r)
        (Set.Icc (64 * Nat.ceil C : ℝ) (T : ℝ)) := fun i =>
      (continuousOn_lift x i).mono (fun u hu => ⟨hC0.trans hu.1, hu.2⟩)
    obtain ⟨γ, hγ, hγb⟩ := exists_sep_margin (x := fun i r => lift x i r) hcontL hA hJ
      hs₀ hlt.le hvT hsep
    have hγb' : ∀ (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) (T : ℝ)), u ∈ Set.Icc s v →
        γ ≤ A.inf' hA (fun i => M2B.fpos x i hu)
          - (Finset.univ \ A).sup' hJ (fun j => M2B.fpos x j hu) := by
      intro u hu huI
      have h := hγb u huI
      simpa only [fpos_eq_lift hu] using h
    have hmain := meet_of_clauses hscale hscaleTop hτ hne hcl hM hC hHT hdr hr hL1 hij hnum
      hT64 hηdef heta hconv hlip hA hJ hs0 hs₀ hlt hvT hγ hγb'
    -- the leader maximum is the fluid maximum
    have hconv' : (fun i => M2B.fpos x i hsI) = (fun i => lift x i s) := by
      funext i
      exact fpos_eq_lift hsI
    have hmaxL : A.sup' hA (fun i => lift x i s) = fluidMax (fun i => lift x i s) := by
      refine le_antisymm (Finset.sup'_le hA _ (fun i hi => ?_)) ?_
      · have h1 : i ∈ leaders (fun i => lift x i s) := by rw [← hAdef]; exact hi
        exact (mem_leaders.mp h1).le
      · obtain ⟨i₁, hi₁⟩ := hApos
        have h1 : i₁ ∈ leaders (fun i => lift x i s) := by rw [← hAdef]; exact hi₁
        calc fluidMax (fun i => lift x i s) = lift x i₁ s := (mem_leaders.mp h1).symm
          _ ≤ A.sup' hA (fun i => lift x i s) := Finset.le_sup' (fun i => lift x i s) hi₁
    have hmin_le : fluidMin (fun i => lift x i s)
        ≤ (Finset.univ \ A).sup' hJ (fun j => lift x j s) := by
      obtain ⟨j, hj⟩ := hJpos
      exact (Finset.inf'_le (fun i => lift x i s) (Finset.mem_univ j)).trans
        (Finset.le_sup' (fun j => lift x j s) hj)
    have hgap : A.sup' hA (fun i => lift x i s)
          - (Finset.univ \ A).sup' hJ (fun j => lift x j s)
        ≤ fluidGap (fun i => lift x i s) := by
      rw [hmaxL]
      unfold fluidGap
      linarith [hmin_le]
    simp only [hconv'] at hmain
    calc v - s
        ≤ 2 * C ^ 2 * (A.sup' hA (fun i => lift x i s)
            - (Finset.univ \ A).sup' hJ (fun j => lift x j s)) := hmain
      _ ≤ 2 * C ^ 2 * fluidGap (fun i => lift x i s) :=
          mul_le_mul_of_nonneg_left hgap (by positivity)

/-! ## 3. The meeting rule from the finite-scale clauses -/

/-- **The source's step 6 from the actual finite-scale clauses.**

Inputs: at every scale `L_n → ∞` the literal record, unit-step paths, the finite-scale
`LocalClauses` and `MartClause` with the same constants, the sharp lag `eta_n` with
`eta_n / L_n → 0`, the uniform convergence of the actual record interpolants to the fluid
limit `x`, the `LipschitzWith 1` fluid motion, and `(coincide)` (`StickyOn`) on the sharp
window `[64⌈C⌉₊, T]` for the lifted limit.

Output: the paper's meeting rule `FluidMerge.JoinRuleFrom` at the sharp constant `2 C^2` and
the source's sharp window origin `64C`.  The `(meet)` separation hypothesis is *not* an input:
`reaches_of_meetBound` produces the contact time internally and `exists_sep_margin` converts
its strict separation into the positive margin that `meet_of_clauses` consumes. -/
theorem joinRuleFrom_of_clauses {X : ℕ → ι → ℕ → ℤ} {τ : ℕ → ℕ → ℕ}
    {H : ℕ → Finset ι → ℕ → ℤ → ℤ} {A : ℕ → ι → ℕ → ℕ}
    {level scale eta : ℕ → ℕ} {C CT μ : ℝ} {T : ℕ}
    {x : ι → (Set.Icc (0 : ℝ) (T : ℝ) →ᵇ ℝ)}
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hτ : ∀ n, IsRecord (X n) (τ n))
    (hne : ∀ n (i : ι) (k : ℕ), |X n i (k + 1) - X n i k| = 1)
    (hcl : ∀ n, LocalClauses (X n) (τ n) (H n) C CT T (scale n) (level n))
    (hM : ∀ n, MartClause (X n) (τ n) (A n) μ CT T (scale n) (level n))
    (hC : 0 < C) (hHT : 0 ≤ CT)
    (hdr : ∀ n, defect (X n) (τ n) (level n) ≤ (scale n : ℤ))
    (hr : ∀ n, (T + 3) * scale n ≤ level n)
    (hL1 : ∀ n, 1 ≤ scale n)
    {i₀ j₀ : ι} (hij : i₀ ≠ j₀)
    (hnum : ∀ n, Numerics C CT (scale n))
    (hT64 : 64 * Nat.ceil C ≤ T)
    (hηdef : ∀ n, CT * (scale n : ℝ) ^ (3 / 4 : ℝ) ≤ (eta n : ℝ))
    (heta : Tendsto (fun n => (eta n : ℝ) / (scale n : ℝ)) atTop (𝓝 0))
    (hconv : ∀ i, TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) (T : ℝ)) =>
        scaledPosition (X n) (level n) (τ n (level n)) (scale n) i
          (FluidInterpolation.rawSample (scale n) (FluidInterpolation.rawHorizon (T : ℝ) (scale n)) t))
      (fun t => x i t) atTop)
    (hlip : ∀ i, LipschitzWith 1 (x i))
    (hsticky : StickyOn (fun i r => lift x i r) (64 * Nat.ceil C : ℝ) (T : ℝ)) :
    JoinRuleFrom (fun i r => lift x i r) (64 * Nat.ceil C : ℝ) (2 * C ^ 2) (T : ℝ) := by
  refine joinRuleFrom_of_meetBound hsticky ?_ (meetBound_of_clauses hscale hscaleTop hτ hne hcl
    hM hC hHT hdr hr hL1 hij hnum hT64 hηdef heta hconv hlip) (by positivity)
  intro i
  exact (continuousOn_lift x i).mono (fun u hu =>
    ⟨(by positivity : (0 : ℝ) ≤ (64 * Nat.ceil C : ℝ)).trans hu.1, hu.2⟩)

end M2Meet
