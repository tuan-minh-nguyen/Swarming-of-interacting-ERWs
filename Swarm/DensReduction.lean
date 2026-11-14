/-
# The exact excitation-density form of `Swarm.Ballistic`, pathwise

## The question

`Swarm.Ballistic m p` (`Swarm/Assembly.lean`) quantifies over **every**
system `(Ω, μ, X, 𝓕)` satisfying the one-walker marginal law `Swarm.IsInteractingLaw`, and
asserts a single `κ > 0` with `κ ≤ liminf X_n^i/n` almost surely.  The marginal law fixes each
walker's conditional up-probability exactly,

`P(X_{n+1}^i = X_n^i + 1 | 𝓕_n) = 1/2 + (p - 1/2)·1{excited at n}`,

which is the set-integral identity `Swarm.setIntegral_step`; so the only freedom the model
leaves is the joint law of the `N` simultaneous jumps, i.e. the copula between the walkers.
`SwarmLaw.marginal_not_enough` shows that this copula is not determined by the marginals.  The
audit question is therefore how much of `Ballistic` is copula content, and whether the target
is overstrong.

## What this file proves

The answer is exact, and it is *not* that the target is overstrong.  Using the already verified
drift martingale `M^i_n = X^i_n - (2p-1)·#{t < n : excited}` (`Swarm.mart`, `Swarm.excCount`)
together with `SwarmHosc.ae_mart_max_div` (Hall-Heyde's martingale strong law for bounded
increments), it is proved that the martingale part is `o(n)` **pathwise**; hence for every
lawful system and every walker, almost surely

`liminf X^i_n/n = liminf (2p-1)·ρ^i_n`  and  `limsup X^i_n/n = limsup (2p-1)·ρ^i_n`,

where `ρ^i_n = (1/n)·#{t < n : walker i excited at t}` is the *excitation density*
(`excDens`).  Consequently:

* `Swarm.Ballistic m p ↔ BallisticDensity m p` (`ballistic_iff_ballisticDensity`), where
  `BallisticDensity` is the **same statement with the same generic quantifiers** and the
  position `X_n^i/n` replaced by the excitation term `(2p-1)·ρ^i_n`;
* for `1/2 < p < 1` it is equivalently a **positive-density** statement
  (`ballistic_iff_pos_density`);
* the paper's upper bound survives pathwise with no convergence hypothesis
  (`ae_limsup_pos_div_le`): `limsup X^i_n/n ≤ 2p-1` for every lawful system;
* the limit speed exists iff the excitation density has a limit, and the two agree
  (`ae_tendsto_pos_div_iff`).

So the generic marginal target carries **no hidden copula substitution and no loss**: it is
exactly the assertion that every coupling of the interacting system excites each walker on a
set of positive asymptotic density.  That residual claim is genuinely about the dependence
structure (the marginal law cannot decide it), but it is precisely the content of Proposition
`ball`.

## Sharpness: the `2 ≤ N` quantifier cannot be weakened

The audit also records where the marginal law *does* fail to produce speed: for `N ≤ 1` there
is no other walker, so the excitation event is **empty** (`not_excited_of_subsingleton`), the
law forces a fair coin, and the speed is `0` (`ae_tendsto_pos_div_zero_of_subsingleton`).  The
actual array at `N = 1` (`SwarmCross.Actual.actual_isInteractingLaw`) is such a system, so the
`2 ≤ N` hypothesis of `Swarm.Ballistic` is essential: the same statement with `1 ≤ N` is
**false** (`not_ballistic_one_le`).  Positive speed therefore comes from the interaction of at
least two walkers, not from the marginal law, which delimits the copula question exactly.

## Scope

Nothing here proves `Swarm.Ballistic`, `Swarm.RegenAvailable`, `Swarm.CommonLimit` or
`Swarm.MainClaim`.  The file reduces the first to an exact density statement, recovers the
upper half of the paper's interval pathwise, and exhibits the exact limit of the marginal
interface.  Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
-/
import Swarm.Imports
import Swarm.Assembly
import Swarm.ActualInstance
import Swarm.SwarmMart

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace SwarmDens

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
  {X : ℕ → Ω → Fin N → ℤ} {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {m : ℕ} {p : ℝ}

/-! ## 1. The excitation density -/

/-- The excitation density `ρ^i_n = (1/n)·#{t < n : walker i excited at t}`, as a real number.
`(0 : ℝ)⁻¹ = 0` in Lean, so its value at `n = 0` is `0`. -/
noncomputable def excDens (X : ℕ → Ω → Fin N → ℤ) (m n : ℕ) (ω : Ω) (i : Fin N) : ℝ :=
  (1 / (n : ℝ)) * (Swarm.excCount X m n ω i : ℝ)

/-- The drift term `(2p-1)·ρ^i_n` in the pathwise decomposition
`X_n^i/n = M_n^i/n + (2p-1)·ρ^i_n`. -/
noncomputable def densTerm (p : ℝ) (X : ℕ → Ω → Fin N → ℤ) (m n : ℕ) (ω : Ω)
    (i : Fin N) : ℝ :=
  (2 * p - 1) * excDens X m n ω i

omit [MeasurableSpace Ω] in
lemma densTerm_eq (p : ℝ) (X : ℕ → Ω → Fin N → ℤ) (m n : ℕ) (ω : Ω) (i : Fin N) :
    densTerm p X m n ω i = (2 * p - 1) * ((1 / (n : ℝ)) * (Swarm.excCount X m n ω i : ℝ)) :=
  rfl

/-- The excitation density is bounded by one. -/
lemma abs_excDens_le_one (n : ℕ) (ω : Ω) (i : Fin N) : |excDens X m n ω i| ≤ 1 := by
  have hle : (Swarm.excCount X m n ω i : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast SwarmHosc.excCount_le (X := X) (m := m) n ω i
  have hnn : (0 : ℝ) ≤ (Swarm.excCount X m n ω i : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [excDens, hn]
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hval : excDens X m n ω i = (Swarm.excCount X m n ω i : ℝ) / n := by
      rw [excDens, one_div, div_eq_inv_mul]
    rw [hval, abs_of_nonneg (by positivity), div_le_one hn']
    exact hle

/-- `|(2p-1)·ρ| ≤ 1` in the paper's parameter range. -/
lemma abs_densTerm_le_one (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 1) (n : ℕ) (ω : Ω) (i : Fin N) :
    |densTerm p X m n ω i| ≤ 1 := by
  have hc : |2 * p - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  rw [densTerm, abs_mul]
  calc |2 * p - 1| * |excDens X m n ω i| ≤ 1 * 1 :=
        mul_le_mul hc (abs_excDens_le_one (X := X) (m := m) n ω i) (abs_nonneg _)
          (by norm_num)
    _ = 1 := by norm_num

/-- The normalised position is bounded by one. -/
lemma abs_pos_div_le_one (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (n : ℕ) (ω : Ω)
    (i : Fin N) : |Swarm.pos X n i ω / (n : ℝ)| ≤ 1 := by
  have h := Swarm.norm_div_le_one hlaw n ω i
  rwa [Real.norm_eq_abs] at h

/-! ## 2. `liminf`/`limsup` calculus for vanishing differences -/

/-- Boundedness below, from an absolute bound. -/
lemma isBoundedUnder_ge_of_abs_le {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, |u n| ≤ C) :
    IsBoundedUnder (· ≥ ·) atTop u := by
  refine ⟨-C, ?_⟩
  rw [Filter.eventually_map]
  exact Filter.Eventually.of_forall fun n => (abs_le.1 (h n)).1

/-- The coboundedness side condition of the `liminf` API, from an absolute bound. -/
lemma isCoboundedUnder_ge_of_abs_le {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, |u n| ≤ C) :
    IsCoboundedUnder (· ≥ ·) atTop u := by
  refine ⟨C + 1, fun a ha => ?_⟩
  rw [Filter.eventually_map] at ha
  obtain ⟨n, hn⟩ := ha.exists
  have := (abs_le.1 (h n)).2
  linarith

/-- The boundedness side condition of the `limsup` API, from an absolute bound. -/
lemma isBoundedUnder_le_of_abs_le {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, |u n| ≤ C) :
    IsBoundedUnder (· ≤ ·) atTop u := by
  refine ⟨C, ?_⟩
  rw [Filter.eventually_map]
  exact Filter.Eventually.of_forall fun n => (abs_le.1 (h n)).2

/-- The coboundedness side condition of the `limsup` API, from an absolute bound. -/
lemma isCoboundedUnder_le_of_abs_le {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, |u n| ≤ C) :
    IsCoboundedUnder (· ≤ ·) atTop u := by
  refine ⟨-C - 1, fun a ha => ?_⟩
  rw [Filter.eventually_map] at ha
  obtain ⟨n, hn⟩ := ha.exists
  have := (abs_le.1 (h n)).1
  linarith

/-- An eventual smallness statement for a sequence whose difference tends to zero. -/
lemma abs_sub_eventually_lt {u v : ℕ → ℝ} (h : Tendsto (fun n => u n - v n) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ n : ℕ in atTop, |u n - v n| < δ := by
  have h' : Tendsto (fun n => |u n - v n|) atTop (𝓝 0) := by
    have := h.abs
    simpa using this
  exact h'.eventually (eventually_lt_nhds hδ)

/-- **`liminf` transfer for a vanishing difference.**  If `a - b → 0` and both sequences are
bounded by one, then `κ ≤ liminf a ↔ κ ≤ liminf b`. -/
theorem le_liminf_iff_of_tendsto_sub_zero {a b : ℕ → ℝ} {κ : ℝ}
    (ha : ∀ n, |a n| ≤ 1) (hb : ∀ n, |b n| ≤ 1)
    (h : Tendsto (fun n => a n - b n) atTop (𝓝 0)) :
    κ ≤ liminf a atTop ↔ κ ≤ liminf b atTop := by
  have key : ∀ {u v : ℕ → ℝ} {κ : ℝ}, (∀ n, |u n| ≤ 1) → (∀ n, |v n| ≤ 1) →
      Tendsto (fun n => u n - v n) atTop (𝓝 0) → κ ≤ liminf v atTop → κ ≤ liminf u atTop := by
    intro u v κ hu hv huv hκ
    refine (le_liminf_iff (isCoboundedUnder_ge_of_abs_le hu)
      (isBoundedUnder_ge_of_abs_le hu)).mpr ?_
    intro y hy
    obtain ⟨y₂, hyy₂, hy₂κ⟩ := exists_between hy
    obtain ⟨y₃, hy₂y₃, hy₃l⟩ := exists_between (lt_of_lt_of_le hy₂κ hκ)
    have hδ : (0 : ℝ) < y₂ - y := by linarith
    have hev : ∀ᶠ n : ℕ in atTop, y₂ < v n :=
      (le_liminf_iff (isCoboundedUnder_ge_of_abs_le hv)
        (isBoundedUnder_ge_of_abs_le hv)).mp (le_of_lt hy₃l) y₂ hy₂y₃
    have hdiff : ∀ᶠ n : ℕ in atTop, |u n - v n| < y₂ - y :=
      abs_sub_eventually_lt huv hδ
    filter_upwards [hev, hdiff] with n hvn hdn
    have h1 : v n - u n ≤ |u n - v n| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  exact ⟨fun hκ => key (u := b) (v := a) hb ha (by simpa using h.neg) hκ,
    fun hκ => key (u := a) (v := b) ha hb h hκ⟩

/-- **Equality of `liminf`s for a vanishing difference.** -/
theorem liminf_eq_of_tendsto_sub_zero {a b : ℕ → ℝ}
    (ha : ∀ n, |a n| ≤ 1) (hb : ∀ n, |b n| ≤ 1)
    (h : Tendsto (fun n => a n - b n) atTop (𝓝 0)) :
    liminf a atTop = liminf b atTop :=
  le_antisymm (le_liminf_iff_of_tendsto_sub_zero ha hb h |>.mp le_rfl)
    (le_liminf_iff_of_tendsto_sub_zero ha hb h |>.mpr le_rfl)

/-- **`limsup` transfer for a vanishing difference.** -/
theorem le_limsup_iff_of_tendsto_sub_zero {a b : ℕ → ℝ} {κ : ℝ}
    (ha : ∀ n, |a n| ≤ 1) (hb : ∀ n, |b n| ≤ 1)
    (h : Tendsto (fun n => a n - b n) atTop (𝓝 0)) :
    limsup a atTop ≤ κ ↔ limsup b atTop ≤ κ := by
  have key : ∀ {u v : ℕ → ℝ} {κ : ℝ}, (∀ n, |u n| ≤ 1) → (∀ n, |v n| ≤ 1) →
      Tendsto (fun n => u n - v n) atTop (𝓝 0) → limsup v atTop ≤ κ → limsup u atTop ≤ κ := by
    intro u v κ hu hv huv hκ
    refine (limsup_le_iff (isCoboundedUnder_le_of_abs_le hu)
      (isBoundedUnder_le_of_abs_le hu)).mpr ?_
    intro y hy
    obtain ⟨y₂, hyκ₂, hy₂y⟩ := exists_between hy
    have hδ : (0 : ℝ) < y - y₂ := by linarith
    have hev : ∀ᶠ n : ℕ in atTop, v n < y₂ :=
      (limsup_le_iff (isCoboundedUnder_le_of_abs_le hv)
        (isBoundedUnder_le_of_abs_le hv)).mp hκ y₂ hyκ₂
    have hdiff : ∀ᶠ n : ℕ in atTop, |u n - v n| < y - y₂ :=
      abs_sub_eventually_lt huv hδ
    filter_upwards [hev, hdiff] with n hvn hdn
    have h1 : u n - v n ≤ |u n - v n| := le_abs_self _
    linarith
  exact ⟨fun hκ => key (u := b) (v := a) hb ha (by simpa using h.neg) hκ,
    fun hκ => key (u := a) (v := b) ha hb h hκ⟩

/-- **Equality of `limsup`s for a vanishing difference.** -/
theorem limsup_eq_of_tendsto_sub_zero {a b : ℕ → ℝ}
    (ha : ∀ n, |a n| ≤ 1) (hb : ∀ n, |b n| ≤ 1)
    (h : Tendsto (fun n => a n - b n) atTop (𝓝 0)) :
    limsup a atTop = limsup b atTop :=
  le_antisymm (le_limsup_iff_of_tendsto_sub_zero ha hb h |>.mpr le_rfl)
    (le_limsup_iff_of_tendsto_sub_zero ha hb h |>.mp le_rfl)

/-! ## 3. The drift martingale is `o(n)` pathwise -/

/-- **`M^i_n / n → 0` almost surely.**  The drift martingale of the marginal law, normalised
by `n`, vanishes pathwise.  This is the Hall-Heyde strong law in the bounded-increment form
already verified as `SwarmHosc.ae_mart_max_div`; the only new work is passing from the running
maximum to the sequence itself. -/
theorem ae_mart_div_zero (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p)
    (hp2 : p ≤ 1) (i : Fin N) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => Swarm.mart p X m n ω i / (n : ℝ)) atTop (𝓝 0) := by
  filter_upwards [SwarmHosc.ae_mart_max_div hlaw hp1 hp2 i] with ω hω
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hω (ε / 2) (by linarith), Filter.eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have h1 : |Swarm.mart p X m n ω i| ≤ (ε / 2) * (n : ℝ) := hn n le_rfl
  rw [Real.dist_eq, sub_zero, abs_div, Nat.abs_cast, div_lt_iff₀ hn0']
  nlinarith

/-- **The pathwise decomposition** `X_n^i/n = M_n^i/n + (2p-1)ρ^i_n`: the difference tends to
zero almost surely. -/
theorem ae_pos_div_sub_dens (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p)
    (hp2 : p ≤ 1) (i : Fin N) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => Swarm.pos X n i ω / (n : ℝ) - densTerm p X m n ω i)
      atTop (𝓝 0) := by
  filter_upwards [ae_mart_div_zero (X := X) (m := m) hlaw hp1 hp2 i] with ω hω
  refine hω.congr (fun n => ?_)
  simp only [densTerm, excDens, Swarm.mart]
  ring

/-- **The exact `liminf` identity**: almost surely
`liminf X_n^i/n = liminf (2p-1)ρ^i_n`, for every system satisfying the marginal law. -/
theorem ae_liminf_pos_div_eq (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p)
    (hp2 : p ≤ 1) (i : Fin N) :
    ∀ᵐ ω ∂μ, liminf (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop
      = liminf (fun n => densTerm p X m n ω i) atTop := by
  filter_upwards [ae_pos_div_sub_dens (X := X) (m := m) hlaw hp1 hp2 i] with ω hω
  exact liminf_eq_of_tendsto_sub_zero (fun n => abs_pos_div_le_one hlaw n ω i)
    (fun n => abs_densTerm_le_one (X := X) (m := m) hp1 hp2 n ω i) hω

/-- **The exact `limsup` identity**: almost surely
`limsup X_n^i/n = limsup (2p-1)ρ^i_n`. -/
theorem ae_limsup_pos_div_eq (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p)
    (hp2 : p ≤ 1) (i : Fin N) :
    ∀ᵐ ω ∂μ, limsup (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop
      = limsup (fun n => densTerm p X m n ω i) atTop := by
  filter_upwards [ae_pos_div_sub_dens (X := X) (m := m) hlaw hp1 hp2 i] with ω hω
  exact limsup_eq_of_tendsto_sub_zero (fun n => abs_pos_div_le_one hlaw n ω i)
    (fun n => abs_densTerm_le_one (X := X) (m := m) hp1 hp2 n ω i) hω

/-- **Pathwise upper half of the paper's interval**, with no convergence hypothesis: for every
system satisfying the marginal law and every walker, `limsup X_n^i/n ≤ 2p-1` almost surely.
The bound is `(2p-1)·limsup ρ ≤ 2p-1` because the excitation density never exceeds one. -/
theorem ae_limsup_pos_div_le (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p)
    (hp2 : p ≤ 1) (i : Fin N) :
    ∀ᵐ ω ∂μ, limsup (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop ≤ 2 * p - 1 := by
  filter_upwards [ae_limsup_pos_div_eq (X := X) (m := m) hlaw hp1 hp2 i] with ω heq
  rw [heq]
  refine (limsup_le_iff
    (isCoboundedUnder_le_of_abs_le (fun n => abs_densTerm_le_one (X := X) (m := m)
      hp1 hp2 n ω i))
    (isBoundedUnder_le_of_abs_le (fun n => abs_densTerm_le_one (X := X) (m := m)
      hp1 hp2 n ω i))).mpr ?_
  intro y hy
  have hc : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  filter_upwards with n
  have h2 : densTerm p X m n ω i ≤ 2 * p - 1 := by
    have hρ : excDens X m n ω i ≤ 1 := by
      linarith [abs_excDens_le_one (X := X) (m := m) n ω i,
        (abs_le.1 (abs_excDens_le_one (X := X) (m := m) n ω i)).2]
    calc densTerm p X m n ω i = (2 * p - 1) * excDens X m n ω i := rfl
      _ ≤ (2 * p - 1) * 1 := mul_le_mul_of_nonneg_left hρ hc
      _ = 2 * p - 1 := by ring
  linarith

/-- The limit speed exists iff the excitation density has a limit, and the two agree. -/
theorem ae_tendsto_pos_div_iff (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p)
    (hp2 : p ≤ 1) (i : Fin N) {v : ℝ} :
    (∀ᵐ ω ∂μ, Tendsto (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop (𝓝 v))
      ↔ (∀ᵐ ω ∂μ, Tendsto (fun n => densTerm p X m n ω i) atTop (𝓝 v)) := by
  have hdec := ae_pos_div_sub_dens (X := X) (m := m) hlaw hp1 hp2 i
  constructor
  · intro hv
    filter_upwards [hv, hdec] with ω hvω hω
    have h := hvω.sub hω
    simpa using h
  · intro hv
    filter_upwards [hv, hdec] with ω hvω hω
    have h := hvω.add hω
    simpa using h

/-! ## 4. The generic marginal target is exactly an excitation-density bound -/

/-- `Swarm.Ballistic` with the position replaced by the excitation term `(2p-1)ρ`.  The
quantifiers are literally those of `Swarm.Ballistic m p`; only the sequence changes. -/
def BallisticDensity (m : ℕ) (p : ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
    2 ≤ N → Swarm.IsInteractingLaw 𝓕 μ X m p →
      ∀ᵐ ω ∂μ, ∀ i : Fin N, κ ≤ liminf (fun n => densTerm p X m n ω i) atTop

/-- **The generic marginal target is exactly its excitation-density form.**

`Swarm.Ballistic` quantifies over every system satisfying the one-walker marginal law.  By the
pathwise cancellation of the drift martingale (`ae_liminf_pos_div_eq`), the position bound is
equivalent, with the *same* quantifiers and the *same* constant, to the bound on the excitation
term `(2p-1)ρ`.  In particular the generic target is neither stronger nor weaker than a
statement about the asymptotic excitation density, i.e. about the effect of the coupling. -/
theorem ballistic_iff_ballisticDensity {m : ℕ} {p : ℝ} (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 1) :
    Swarm.Ballistic m p ↔ BallisticDensity m p := by
  have hper : ∀ {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X : ℕ → Ω → Fin N → ℤ} {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›},
      Swarm.IsInteractingLaw 𝓕 μ X m p → ∀ᵐ ω ∂μ, ∀ i : Fin N,
        liminf (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop
          = liminf (fun n => densTerm p X m n ω i) atTop := by
    intro N Ω _ μ _ X 𝓕 hlaw
    exact ae_all_iff.mpr (fun i => ae_liminf_pos_div_eq (X := X) (m := m) hlaw hp1 hp2 i)
  constructor
  · rintro ⟨κ, hκ, h⟩
    refine ⟨κ, hκ, ?_⟩
    intro N Ω _ μ _ X 𝓕 hN hlaw
    filter_upwards [h N Ω μ X 𝓕 hN hlaw, hper hlaw] with ω hω hperω
    intro i
    rw [← hperω i]
    exact hω i
  · rintro ⟨κ, hκ, h⟩
    refine ⟨κ, hκ, ?_⟩
    intro N Ω _ μ _ X 𝓕 hN hlaw
    filter_upwards [h N Ω μ X 𝓕 hN hlaw, hper hlaw] with ω hω hperω
    intro i
    rw [hperω i]
    exact hω i

/-- **The generic target as a uniform positive excitation-density statement** on the paper's
parameter range: `Ballistic m p` is equivalent to the existence of `δ > 0` with
`δ ≤ liminf ρ^i_n` almost surely, uniformly over every lawful system and every walker. -/
theorem ballistic_iff_pos_density {m : ℕ} {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    Swarm.Ballistic m p ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
        2 ≤ N → Swarm.IsInteractingLaw 𝓕 μ X m p →
          ∀ᵐ ω ∂μ, ∀ i : Fin N, δ ≤ liminf (fun n => excDens X m n ω i) atTop := by
  have hp1' : (1 : ℝ) / 2 ≤ p := le_of_lt hp1
  have hp2' : p ≤ 1 := le_of_lt hp2
  have hc : (0 : ℝ) < 2 * p - 1 := by linarith
  rw [ballistic_iff_ballisticDensity (m := m) (p := p) hp1' hp2']
  constructor
  · rintro ⟨κ, hκ, h⟩
    refine ⟨κ / (2 * p - 1), by positivity, ?_⟩
    intro N Ω _ μ _ X 𝓕 hN hlaw
    filter_upwards [h N Ω μ X 𝓕 hN hlaw] with ω hω
    intro i
    refine (le_liminf_iff
      (isCoboundedUnder_ge_of_abs_le (fun n => abs_excDens_le_one (X := X) (m := m) n ω i))
      (isBoundedUnder_ge_of_abs_le (fun n => abs_excDens_le_one (X := X) (m := m) n ω i)
        )).mpr ?_
    intro y hy
    have hyκ : (2 * p - 1) * y < κ := by
      have h' : y * (2 * p - 1) < κ := (lt_div_iff₀ hc).mp hy
      linarith
    obtain ⟨y', hyy', hy'κ⟩ := exists_between hyκ
    have hev : ∀ᶠ n : ℕ in atTop, y' < densTerm p X m n ω i :=
      (le_liminf_iff
        (isCoboundedUnder_ge_of_abs_le (fun n =>
          abs_densTerm_le_one (X := X) (m := m) hp1' hp2' n ω i))
        (isBoundedUnder_ge_of_abs_le (fun n =>
          abs_densTerm_le_one (X := X) (m := m) hp1' hp2' n ω i))).mp (hω i) y' hy'κ
    filter_upwards [hev] with n hn
    rw [densTerm] at hn
    exact (mul_lt_mul_iff_of_pos_left hc).mp (lt_trans hyy' hn)
  · rintro ⟨δ, hδ, h⟩
    refine ⟨(2 * p - 1) * δ, by positivity, ?_⟩
    intro N Ω _ μ _ X 𝓕 hN hlaw
    filter_upwards [h N Ω μ X 𝓕 hN hlaw] with ω hω
    intro i
    refine (le_liminf_iff
      (isCoboundedUnder_ge_of_abs_le (fun n =>
        abs_densTerm_le_one (X := X) (m := m) hp1' hp2' n ω i))
      (isBoundedUnder_ge_of_abs_le (fun n =>
        abs_densTerm_le_one (X := X) (m := m) hp1' hp2' n ω i))).mpr ?_
    intro y hy
    have hyδ : y / (2 * p - 1) < δ := by
      rw [div_lt_iff₀ hc]; linarith
    have hev : ∀ᶠ n : ℕ in atTop, y / (2 * p - 1) < excDens X m n ω i :=
      (le_liminf_iff
        (isCoboundedUnder_ge_of_abs_le (fun n => abs_excDens_le_one (X := X) (m := m) n ω i))
        (isBoundedUnder_ge_of_abs_le (fun n =>
          abs_excDens_le_one (X := X) (m := m) n ω i))).mp (hω i) (y / (2 * p - 1)) hyδ
    filter_upwards [hev] with n hn
    have hy' : (2 * p - 1) * (y / (2 * p - 1)) = y := by
      rw [mul_comm]; exact div_mul_cancel₀ y (ne_of_gt hc)
    rw [densTerm, ← hy']
    exact (mul_lt_mul_iff_of_pos_left hc).mpr hn

/-! ## 5. Sharpness: single-walker systems are fair walks -/

omit [MeasurableSpace Ω] in
/-- With a subsingleton index type there is no other walker, so the other-visit sum is empty. -/
lemma otherVisits_eq_zero_of_subsingleton [Subsingleton (Fin N)] (n : ℕ) (ω : Ω) (i : Fin N)
    (x : ℤ) : Swarm.otherVisits X n ω i x = 0 := by
  have hempty : (Finset.univ.erase i : Finset (Fin N)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    rw [Finset.mem_erase] at hj
    exact hj.1 (Subsingleton.elim j i)
  simp [Swarm.otherVisits, hempty]

/-- With a single walker the excitation event is empty. -/
lemma not_excited_of_subsingleton [Subsingleton (Fin N)] (hm : 1 ≤ m) (n : ℕ) (ω : Ω)
    (i : Fin N) : ¬ Swarm.Excited X m n ω i := by
  have h := otherVisits_eq_zero_of_subsingleton (X := X) n ω i (X n ω i)
  simp only [Swarm.Excited, h]
  omega

/-- With a single walker the excitation counter vanishes. -/
lemma excCount_eq_zero_of_subsingleton [Subsingleton (Fin N)] (hm : 1 ≤ m) (n : ℕ) (ω : Ω)
    (i : Fin N) : Swarm.excCount X m n ω i = 0 := by
  rw [Swarm.excCount]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [if_neg (not_excited_of_subsingleton (X := X) hm t ω i)]

/-- With a single walker the excitation density vanishes. -/
lemma excDens_eq_zero_of_subsingleton [Subsingleton (Fin N)] (hm : 1 ≤ m) (n : ℕ) (ω : Ω)
    (i : Fin N) : excDens X m n ω i = 0 := by
  simp [excDens, excCount_eq_zero_of_subsingleton (X := X) hm n ω i]

/-- **Single-walker systems are fair walks.**  Every system satisfying the marginal law with
`N ≤ 1` has zero speed almost surely: the drift term is identically zero. -/
theorem ae_tendsto_pos_div_zero_of_subsingleton [Subsingleton (Fin N)]
    (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 1) (hm : 1 ≤ m)
    (i : Fin N) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop (𝓝 0) := by
  filter_upwards [ae_pos_div_sub_dens (X := X) (m := m) hlaw hp1 hp2 i] with ω hω
  have hzero : ∀ n, densTerm p X m n ω i = 0 := fun n => by
    simp [densTerm, excDens_eq_zero_of_subsingleton (X := X) hm n ω i]
  simpa only [hzero, sub_zero] using hω

/-- **The `2 ≤ N` quantifier of `Swarm.Ballistic` cannot be weakened to `1 ≤ N`.**  For
`N = 1` there is no other walker, the marginal law degenerates to a fair coin, and the actual
array (`arrayMeasure 1`, `trajectory p m`) is a lawful single-walker system whose speed is `0`
almost surely.  Hence no positive `κ` is uniform over all `1 ≤ N`. -/
theorem not_ballistic_one_le {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p < 1) :
    ¬ ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
      1 ≤ N → Swarm.IsInteractingLaw 𝓕 μ X m p →
        ∀ᵐ ω ∂μ, ∀ i : Fin N, κ ≤ liminf (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop := by
  rintro ⟨κ, hκ, h⟩
  haveI hprob : IsProbabilityMeasure (Swarming.Uniform.arrayMeasure 1) :=
    Swarming.Uniform.arrayMeasure_isProbabilityMeasure 1
  haveI hne : (ae (Swarming.Uniform.arrayMeasure 1)).NeBot := by
    rw [ae_neBot]
    intro hzero
    have h1 : Swarming.Uniform.arrayMeasure 1 Set.univ = 1 := measure_univ
    rw [hzero] at h1
    simp at h1
  let Xa : ℕ → Swarming.Uniform.Array 1 → Fin 1 → ℤ :=
    fun t U => (Swarming.Trajectory.trajectory p m U t).pos
  have hlaw : Swarm.IsInteractingLaw (SwarmCross.pathFilt (N := 1) p m)
      (Swarming.Uniform.arrayMeasure 1) Xa m p :=
    SwarmCross.Actual.actual_isInteractingLaw (N := 1) hp1 hp2 m
  have hb := h 1 (Swarming.Uniform.Array 1) (Swarming.Uniform.arrayMeasure 1) Xa
    (SwarmCross.pathFilt (N := 1) p m) le_rfl hlaw
  have hzero : ∀ᵐ U ∂(Swarming.Uniform.arrayMeasure 1), ∀ i : Fin 1,
      Tendsto (fun n => Swarm.pos Xa n i U / (n : ℝ)) atTop (𝓝 0) :=
    ae_all_iff.mpr (fun i => ae_tendsto_pos_div_zero_of_subsingleton (X := Xa) (m := m)
      (𝓕 := SwarmCross.pathFilt (N := 1) p m) hlaw hp1.le hp2.le hm i)
  obtain ⟨U, hU1, hU2⟩ := (hb.and hzero).exists
  let i0 : Fin 1 := ⟨0, by omega⟩
  have hlim := hU2 i0
  have hlow := hU1 i0
  rw [hlim.liminf_eq] at hlow
  linarith

/-- The density term is nonnegative on the paper's range (the excitation density is). -/
lemma densTerm_nonneg (hp1 : 1 / 2 ≤ p) (n : ℕ) (ω : Ω) (i : Fin N) :
    0 ≤ densTerm p X m n ω i := by
  have hc : (0 : ℝ) ≤ 2 * p - 1 := by linarith
  have hρ : (0 : ℝ) ≤ excDens X m n ω i := by
    rw [excDens]
    exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg n)) (Nat.cast_nonneg _)
  rw [densTerm]
  exact mul_nonneg hc hρ

/-- **Pathwise nonnegativity of the lower speed**: `0 ≤ liminf X_n^i/n` almost surely for every
lawful system, with no convergence hypothesis.  The existing pathwise statement
`Swarm.speed_nonneg` assumes that the limit exists; here the `liminf` is bounded below because the
excitation term `(2p-1)ρ` is nonnegative. -/
theorem ae_liminf_pos_div_nonneg (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p)
    (hp2 : p ≤ 1) (i : Fin N) :
    ∀ᵐ ω ∂μ, 0 ≤ liminf (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop := by
  filter_upwards [ae_liminf_pos_div_eq (X := X) (m := m) hlaw hp1 hp2 i] with ω heq
  rw [heq]
  exact le_liminf_of_le
    (isCoboundedUnder_ge_of_abs_le (fun n =>
      abs_densTerm_le_one (X := X) (m := m) hp1 hp2 n ω i))
    (Filter.Eventually.of_forall fun n => densTerm_nonneg (X := X) (m := m) hp1 n ω i)

/-- **The paper's interval, pathwise and without assuming that the speed exists**:
`0 ≤ liminf X_n^i/n` and `limsup X_n^i/n ≤ 2p-1` almost surely, for every system satisfying the
marginal law.  Combined with `liminf ≤ limsup`, every lawful system's lower and upper speeds lie
in `[0, 2p-1]`; the only open half of Proposition `ball` is the *uniform* positivity `κ ≤ liminf`,
which by `ballistic_iff_pos_density` is a positive excitation-density statement. -/
theorem ae_pos_div_interval (hlaw : Swarm.IsInteractingLaw 𝓕 μ X m p) (hp1 : 1 / 2 ≤ p)
    (hp2 : p ≤ 1) (i : Fin N) :
    ∀ᵐ ω ∂μ, 0 ≤ liminf (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop ∧
      limsup (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop ≤ 2 * p - 1 := by
  filter_upwards [ae_liminf_pos_div_nonneg (X := X) (m := m) hlaw hp1 hp2 i,
    ae_limsup_pos_div_le (X := X) (m := m) hlaw hp1 hp2 i] with ω h1 h2
  exact ⟨h1, h2⟩

/-! ## 6. The threshold `m = 0`: the interface is non-vacuous

When the local-time threshold is `m = 0` the excitation predicate is identically true, so the
excitation density is `1` and the reduction `ae_liminf_pos_div_eq` gives the ballistic bound for
**every** lawful system with `κ = 2p-1`, with no coupling hypothesis at all.  This is a
non-vacuity check of the generic target: it shows that the whole difficulty of Proposition `ball`
is the threshold `m >= 2` (a genuine, coupling-dependent excitation density), not the shape of
the statement.
-/

/-- With threshold `0` every walker is excited at every time. -/
lemma excited_zero (n : ℕ) (ω : Ω) (i : Fin N) : Swarm.Excited X 0 n ω i := by
  simp [Swarm.Excited]

/-- With threshold `0` the excitation counter equals the time: `excCount = n`. -/
lemma excCount_zero (n : ℕ) (ω : Ω) (i : Fin N) : Swarm.excCount X 0 n ω i = n := by
  classical
  simp only [Swarm.excCount]
  have h : ∀ t ∈ Finset.range n, (if Swarm.Excited X 0 t ω i then (1 : ℕ) else 0) = 1 := by
    intro t _
    rw [if_pos (excited_zero (X := X) t ω i)]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- With threshold `0` the excitation density is `1` at every positive time. -/
lemma excDens_zero {n : ℕ} (hn : 0 < n) (ω : Ω) (i : Fin N) : excDens X 0 n ω i = 1 := by
  rw [excDens, excCount_zero]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

/-- **At threshold `0` the lower speed is exactly `2p-1`**, for every lawful system. -/
theorem ae_liminf_pos_div_eq_two_p_sub_one (hlaw : Swarm.IsInteractingLaw 𝓕 μ X 0 p)
    (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 1) (i : Fin N) :
    ∀ᵐ ω ∂μ,
      liminf (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop = 2 * p - 1 := by
  filter_upwards [ae_liminf_pos_div_eq (X := X) (m := 0) hlaw hp1 hp2 i] with ω h
  rw [h]
  have hev : (fun n => densTerm p X 0 n ω i) =ᶠ[atTop] fun _ => (2 * p - 1) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    rw [densTerm, excDens_zero (X := X) hn]
    ring
  rw [Filter.liminf_congr hev, Filter.liminf_const]

/-- **`Swarm.Ballistic 0 p` is a theorem** on the paper's `p`-range: at threshold `0` the
ballistic constant is `2p-1`, uniformly over all `N >= 2` and all couplings.  Since
`Ballistic m p` is defined for every `m`, this also shows that the generic quantifier of the
target is non-vacuous. -/
theorem ballistic_zero {p : ℝ} (hp1 : 1 / 2 < p) (hp2 : p ≤ 1) : Swarm.Ballistic 0 p := by
  refine ⟨2 * p - 1, by linarith, ?_⟩
  intro N Ω _ μ _ X 𝓕 hN hlaw
  have hper : ∀ᵐ ω ∂μ, ∀ i : Fin N,
      liminf (fun n => Swarm.pos X n i ω / (n : ℝ)) atTop = 2 * p - 1 :=
    ae_all_iff.mpr fun i => ae_liminf_pos_div_eq_two_p_sub_one (X := X) hlaw hp1.le hp2 i
  filter_upwards [hper] with ω hω i
  rw [hω i]

end SwarmDens
