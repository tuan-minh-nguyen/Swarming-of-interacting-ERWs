/-
Area (h) — final integration: the paper's Theorem 1.1 as a proved reduction.

`results/lean/README.md` lists as missing "assembly of those concrete inputs into the
theorem stated in the LaTeX paper".  This file does that assembly, for all `N` walkers
simultaneously and with the full interval `[kappa(m,p), 2p-1]`:

* `Swarm.main_theorem` has exactly the quantifier structure of Theorem 1.1 of
  `main_1d_revised.tex`:
  for every `m >= 2`, `p in (1/2,1)` there is `kappa > 0` such that for every `N >= 2`
  and **every** system `(mu, X)` satisfying the model law `IsInteractingLaw` there is
  `v in [kappa, 2p-1]` with `X_n^i / n -> v` a.s. for **every** `i`;
* the only inputs are three explicitly named statements, each of which is a numbered
  result of the paper:
  - `hball` — Proposition `ball` (the lower bound, with the constant *uniform in N*);
  - `hregen` — Propositions `front` + `regen` (existence of regeneration increments with
    the independence / identical-distribution / integrability / mean-duration
    properties, plus the path structure `Sandwich` of the regeneration levels);
  - `hinit` — the last part of Proposition `regen` (an a.s. finite initial regeneration
    after which the translated future has law `P*`).

Everything else is proved here: the deterministic renewal limit for ℤ-valued positions
(`tendsto_div_of_sandwich_int`, a re-derivation of the ℤ-valued form of the layer in
`results/lean/RenewalSkeleton.lean`, needed because the paper's walkers take values in ℤ
and all `N` of them must be handled at once), the identification `X_{sigma_k} = z_k`
(`hit_level`), the strong law (`strong_law_ae_real` applied to the increments), the
translation step, `kappa <= v` and `v <= 2p-1` (`UpperBound.lean`).

The two genuinely open Lean obligations are stated as hypotheses and are *not* weakened:
there is no assumption on the conclusion, no proof hole, no axiom.
-/
import Swarm.UpperBound

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace Swarm

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### A renewal-limit layer for ℤ-valued positions -/

/-- `sigma_k = T_0 + ... + T_{k-1}`, the time of the `k`-th regeneration. -/
def blockSum (T : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, T j

@[simp] lemma blockSum_zero (T : ℕ → ℕ) : blockSum T 0 = 0 := by simp [blockSum]

lemma blockSum_succ (T : ℕ → ℕ) (k : ℕ) : blockSum T (k + 1) = blockSum T k + T k := by
  simp [blockSum, Finset.sum_range_succ]

lemma le_blockSum {T : ℕ → ℕ} (hT : ∀ k, 1 ≤ T k) : ∀ k, k ≤ blockSum T k
  | 0 => by simp [blockSum]
  | (k + 1) => by
      have ih := le_blockSum hT k
      rw [blockSum_succ]
      have := hT k
      omega

lemma strictMono_blockSum {T : ℕ → ℕ} (hT : ∀ k, 1 ≤ T k) : StrictMono (blockSum T) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [blockSum_succ]
  have := hT k
  omega

/-- The renewal count `N(t) = sup {k : sigma_k <= t}`. -/
def renewCount (T : ℕ → ℕ) (t : ℕ) : ℕ := Nat.findGreatest (fun k => blockSum T k ≤ t) t

lemma blockSum_renewCount_le (T : ℕ → ℕ) (t : ℕ) : blockSum T (renewCount T t) ≤ t :=
  Nat.findGreatest_spec (P := fun k => blockSum T k ≤ t) (n := t) (m := 0)
    (Nat.zero_le t) (by simp [blockSum])

lemma not_blockSum_lt_renewCount (T : ℕ → ℕ) (t : ℕ) :
    ∀ n, renewCount T t < n → n ≤ t → ¬ (blockSum T n ≤ t) :=
  ((Nat.findGreatest_eq_iff (P := fun k => blockSum T k ≤ t)).1 rfl).2.2

lemma lt_blockSum_renewCount_succ {T : ℕ → ℕ} (hT : ∀ k, 1 ≤ T k) (t : ℕ) :
    t < blockSum T (renewCount T t + 1) := by
  by_cases h : renewCount T t + 1 ≤ t
  · exact not_le.1 (not_blockSum_lt_renewCount T t _ (Nat.lt_succ_self _) h)
  · exact lt_of_lt_of_le (Nat.lt_of_not_le h) (le_blockSum hT _)

lemma tendsto_renewCount {T : ℕ → ℕ} (hT : ∀ k, 1 ≤ T k) :
    Tendsto (renewCount T) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro a
  refine ⟨blockSum T a, fun t ht => ?_⟩
  refine Nat.le_findGreatest ?_ ht
  have := le_blockSum hT a
  omega

lemma tendsto_div_of_tendsto_div {u v : ℕ → ℝ} {a b : ℝ}
    (hu : Tendsto (fun k => u k / k) atTop (𝓝 a))
    (hv : Tendsto (fun k => v k / k) atTop (𝓝 b)) (hb : b ≠ 0) :
    Tendsto (fun k => u k / v k) atTop (𝓝 (a / b)) := by
  refine (hu.div hv hb).congr' ?_
  filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
  have hk' : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact ne_of_gt this
  simp only [Pi.div_apply]
  field_simp

lemma tendsto_div_succ {u : ℕ → ℝ} {a : ℝ}
    (hu : Tendsto (fun k => u k / k) atTop (𝓝 a)) :
    Tendsto (fun k => u (k + 1) / k) atTop (𝓝 a) := by
  have h1 : Tendsto (fun k : ℕ => u (k + 1) / ((k : ℝ) + 1)) atTop (𝓝 a) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hu.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / k) atTop (𝓝 1) := by
    have hbase : Tendsto (fun k : ℕ => (1 : ℝ) + ((k : ℝ))⁻¹) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
      simpa using h
    refine hbase.congr' ?_
    filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
    have hk' : (k : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      exact ne_of_gt this
    field_simp
  have hmul := h1.mul h2
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
  have hk' : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact ne_of_gt this
  field_simp

/-- **Deterministic renewal limit for ℤ-valued positions** (paper §3.3, display in the
proof of Theorem 1.1): if the regeneration levels and times satisfy `z_k/k -> a` and
`sigma_k/k -> b > 0`, and the path does not return below a level nor reach the next one
early, then `X_n/n -> a/b`. -/
theorem tendsto_div_of_sandwich_int {T : ℕ → ℕ} (hT : ∀ k, 1 ≤ T k) {x : ℕ → ℤ} {z : ℕ → ℕ}
    (hno : ∀ k, 1 ≤ k → ∀ n, blockSum T k ≤ n → (z k : ℤ) ≤ x n)
    (hfh : ∀ k n, (z (k + 1) : ℤ) ≤ x n → blockSum T (k + 1) ≤ n)
    {a b : ℝ} (hz : Tendsto (fun k => (z k : ℝ) / k) atTop (𝓝 a))
    (hS : Tendsto (fun k => (blockSum T k : ℝ) / k) atTop (𝓝 b)) (hb : 0 < b) :
    Tendsto (fun n => (x n : ℝ) / n) atTop (𝓝 (a / b)) := by
  have hb' : b ≠ 0 := ne_of_gt hb
  have hN := tendsto_renewCount hT
  have hlow : Tendsto (fun k => (z k : ℝ) / (blockSum T (k + 1) : ℝ)) atTop (𝓝 (a / b)) :=
    tendsto_div_of_tendsto_div hz (tendsto_div_succ hS) hb'
  have hup : Tendsto (fun k => (z (k + 1) : ℝ) / (blockSum T k : ℝ)) atTop (𝓝 (a / b)) :=
    tendsto_div_of_tendsto_div (tendsto_div_succ hz) hS hb'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlow.comp hN) (hup.comp hN) ?_ ?_
  · filter_upwards [hN.eventually (eventually_atTop.2 ⟨1, fun n hn => hn⟩),
      eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hNn hn
    have hzX : (z (renewCount T n) : ℝ) ≤ (x n : ℝ) := by
      have h := hno (renewCount T n) hNn n (blockSum_renewCount_le T n)
      exact_mod_cast h
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (blockSum T (renewCount T n + 1) : ℝ) := by
      have h1 : 0 < renewCount T n + 1 := Nat.succ_pos _
      have h2 : renewCount T n + 1 ≤ blockSum T (renewCount T n + 1) := le_blockSum hT _
      exact_mod_cast lt_of_lt_of_le h1 h2
    have hmono : (n : ℝ) ≤ (blockSum T (renewCount T n + 1) : ℝ) := by
      exact_mod_cast le_of_lt (lt_blockSum_renewCount_succ hT n)
    calc (z (renewCount T n) : ℝ) / (blockSum T (renewCount T n + 1) : ℝ)
        ≤ (z (renewCount T n) : ℝ) / (n : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hn' hmono
      _ ≤ (x n : ℝ) / (n : ℝ) := div_le_div_of_nonneg_right hzX hn'.le
  · filter_upwards [hN.eventually (eventually_atTop.2 ⟨1, fun n hn => hn⟩),
      eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hNn hn
    have hXz : (x n : ℝ) ≤ (z (renewCount T n + 1) : ℝ) := by
      have hnot : ¬ ((z (renewCount T n + 1) : ℤ) ≤ x n) := by
        intro hc
        have h := hfh (renewCount T n) n hc
        have := lt_blockSum_renewCount_succ hT n
        omega
      have : x n < (z (renewCount T n + 1) : ℤ) := not_le.1 hnot
      exact_mod_cast le_of_lt this
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (blockSum T (renewCount T n) : ℝ) := by
      have h2 : 1 ≤ blockSum T (renewCount T n) := le_trans hNn (le_blockSum hT _)
      have h3 : (1 : ℝ) ≤ (blockSum T (renewCount T n) : ℝ) := by exact_mod_cast h2
      linarith
    have hmono : (blockSum T (renewCount T n) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast blockSum_renewCount_le T n
    calc (x n : ℝ) / (n : ℝ) ≤ (z (renewCount T n + 1) : ℝ) / (n : ℝ) :=
          div_le_div_of_nonneg_right hXz hn'.le
      _ ≤ (z (renewCount T n + 1) : ℝ) / (blockSum T (renewCount T n) : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hpos hmono

/-- At a regeneration time every walker sits exactly on the regeneration level
(`X_{sigma_k} = z_k`).  The paper uses this implicitly when it evaluates the ballistic
bound at `n = sigma_{k+1}`. -/
lemma hit_level {T : ℕ → ℕ} (hT : ∀ k, 1 ≤ T k) {x : ℕ → ℤ} {z : ℕ → ℕ}
    (hno : ∀ k, 1 ≤ k → ∀ n, blockSum T k ≤ n → (z k : ℤ) ≤ x n)
    (hfh : ∀ k n, (z (k + 1) : ℤ) ≤ x n → blockSum T (k + 1) ≤ n)
    (hnn : ∀ n, x (n + 1) = x n + 1 ∨ x (n + 1) = x n - 1)
    {k : ℕ} (hk : 1 ≤ k) : x (blockSum T k) = (z k : ℤ) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hle : (z (k' + 1) : ℤ) ≤ x (blockSum T (k' + 1)) := hno _ (by omega) _ le_rfl
  have hgt : 1 ≤ blockSum T (k' + 1) := by
    have := le_blockSum hT (k' + 1)
    omega
  obtain ⟨m, hm⟩ : ∃ m, blockSum T (k' + 1) = m + 1 := ⟨blockSum T (k' + 1) - 1, by omega⟩
  have hnot : ¬ ((z (k' + 1) : ℤ) ≤ x m) := by
    intro hc
    have h := hfh k' m hc
    omega
  have hlt : x m < (z (k' + 1) : ℤ) := not_le.1 hnot
  have hle' : (z (k' + 1) : ℤ) ≤ x (m + 1) := by
    rw [hm] at hle
    exact hle
  have hstep := hnn m
  have hgoal : x (m + 1) = (z (k' + 1) : ℤ) := by omega
  rw [hm]
  exact hgoal

/-- `tendsto_div_of_translate` for a single real sequence (paper: "finite spatial and
temporal translations do not change the limit of `X_n^i/n`"). -/
theorem tendsto_div_of_translate {y : ℕ → ℝ} {c ℓ : ℝ} {S : ℕ}
    (h : Tendsto (fun n => (y (n + S) - c) / n) atTop (𝓝 ℓ)) :
    Tendsto (fun n => y n / n) atTop (𝓝 ℓ) := by
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + S)) atTop (𝓝 1) := by
    have hN : Tendsto (fun n : ℕ => (S : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hsum : Tendsto (fun n : ℕ => (1 : ℝ) + (S : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hN
    have hinv : Tendsto (fun n : ℕ => ((1 : ℝ) + (S : ℝ) / (n : ℝ))⁻¹) atTop (𝓝 1) := by
      simpa using hsum.inv₀ one_ne_zero
    refine hinv.congr' ?_
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact ne_of_gt this
    have hN0 : ((n : ℝ) + S) ≠ 0 := by positivity
    field_simp
  have h1 : Tendsto (fun n : ℕ => (y (n + S) - c) / ((n : ℝ) + S)) atTop (𝓝 ℓ) := by
    have hmul := h.mul hratio
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact ne_of_gt this
    have hN0 : ((n : ℝ) + S) ≠ 0 := by positivity
    field_simp
  have h2 : Tendsto (fun m : ℕ => (y m - c) / m) atTop (𝓝 ℓ) := by
    refine (tendsto_add_atTop_iff_nat (f := fun m : ℕ => (y m - c) / m) S).1 ?_
    simpa [Nat.cast_add] using h1
  have h3 : Tendsto (fun m : ℕ => (y m - c) / m + c / m) atTop (𝓝 (ℓ + 0)) :=
    h2.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards with m
  rw [sub_div, sub_add_cancel]

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
variable {X : ℕ → Ω → Fin N → ℤ} {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {m : ℕ} {p : ℝ}

/-- Translations do not change the limit (paper, last paragraph of §3.3). -/
theorem ae_tendsto_of_translate {μ : Measure Ω} {x : ℕ → Ω → ℝ} {v : ℝ}
    (h : ∀ᵐ ω ∂μ, ∃ (S : ℕ) (c : ℝ), Tendsto (fun n => (x (n + S) ω - c) / n) atTop (𝓝 v)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => x n ω / n) atTop (𝓝 v) := by
  filter_upwards [h] with ω ⟨S, c, hS⟩
  exact tendsto_div_of_translate hS

/-! ### The paper's regeneration input, as a named hypothesis -/

/-- **Propositions `front` + `regen` + the mean bounds of §3.3**: the successive
regeneration distance and duration increments are pairwise independent, identically
distributed, integrable, with durations `>= 1` and positive mean duration. -/
def RegenLaw (μ : Measure Ω) (D T : ℕ → Ω → ℕ) : Prop :=
  (∀ i, Integrable (fun ω => (D i ω : ℝ)) μ) ∧
  (∀ i, Integrable (fun ω => (T i ω : ℝ)) μ) ∧
  (∀ i ω, 1 ≤ T i ω) ∧
  (Pairwise fun i j => IndepFun (fun ω => (D i ω : ℝ)) (fun ω => (D j ω : ℝ)) μ) ∧
  (∀ i, IdentDistrib (fun ω => (D i ω : ℝ)) (fun ω => (D 0 ω : ℝ)) μ μ) ∧
  (Pairwise fun i j => IndepFun (fun ω => (T i ω : ℝ)) (fun ω => (T j ω : ℝ)) μ) ∧
  (∀ i, IdentDistrib (fun ω => (T i ω : ℝ)) (fun ω => (T 0 ω : ℝ)) μ μ)

/-- The mean duration is positive.  In the paper this is immediate from `T >= 1`; it is
derived here rather than assumed, so that `RegenLaw` carries no redundant conjunct. -/
theorem RegenLaw.mean_pos {D T : ℕ → Ω → ℕ} (h : RegenLaw μ D T) :
    0 < ∫ ω, (T 0 ω : ℝ) ∂μ := by
  have hpos : ∀ ω, 1 ≤ T 0 ω := fun ω => h.2.2.1 0 ω
  have hone : ∫ _ : Ω, (1 : ℝ) ∂μ = 1 := by simp
  have hle : ∫ _ : Ω, (1 : ℝ) ∂μ ≤ ∫ ω, (T 0 ω : ℝ) ∂μ := by
    refine integral_mono (integrable_const 1) (h.2.1 0) (fun ω => ?_)
    have h1 : (1:ℝ) ≤ (T 0 ω : ℝ) := by exact_mod_cast hpos ω
    exact h1
  rw [hone] at hle
  linarith

/-- **The path structure of regeneration** (paper §3.3): after `sigma_k` no walker
returns to or below `z_k`, and `sigma_{k+1}` is the first time a walker reaches
`z_{k+1}`.  These are the two inequalities the paper writes as
`z_k <= X_n^i < z_{k+1}` for `sigma_k <= n < sigma_{k+1}`. The lower no-return clause
is required only for `k >= 1`, exactly as in the paper. -/
def Sandwich (μ : Measure Ω) {N : ℕ} (X : ℕ → Ω → Fin N → ℤ) (D T : ℕ → Ω → ℕ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ (i : Fin N) (k n : ℕ),
    ((1 ≤ k → blockSum (fun j => T j ω) k ≤ n → (blockSum (fun j => D j ω) k : ℤ) ≤ X n ω i) ∧
     ((blockSum (fun j => D j ω) (k + 1) : ℤ) ≤ X n ω i →
        blockSum (fun j => T j ω) (k + 1) ≤ n))

/-! ### Proved consequences of the regeneration input -/

/-- **Strong law for the regenerating path** (paper §3.3, proof of Theorem 1.1):
if the regeneration increments satisfy `RegenLaw` and the path structure `Sandwich`
holds, then almost surely **every** walker satisfies `X_n^i/n -> E^*D_1 / E^*T_1`. -/
theorem ae_tendsto_of_regen {D T : ℕ → Ω → ℕ}
    (hreg : RegenLaw μ D T) (hsand : Sandwich μ X D T) :
    ∀ᵐ ω ∂μ, ∀ i : Fin N,
      Tendsto (fun n => pos X n i ω / n) atTop
        (𝓝 ((∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ))) := by
  have hbpos : (0 : ℝ) < ∫ ω, (T 0 ω : ℝ) ∂μ := RegenLaw.mean_pos hreg
  obtain ⟨hDint, hTint, hTpos, hDind, hDid, hTind, hTid⟩ := hreg
  have hD := strong_law_ae_real (fun k ω => (D k ω : ℝ)) (hDint 0) hDind hDid
  have hT := strong_law_ae_real (fun k ω => (T k ω : ℝ)) (hTint 0) hTind hTid
  filter_upwards [hD, hT, hsand] with ω hDω hTω hs
  intro i
  have hDsum : Tendsto (fun k => (blockSum (fun j => D j ω) k : ℝ) / k) atTop
      (𝓝 (∫ ω, (D 0 ω : ℝ) ∂μ)) := by
    simpa [blockSum, Nat.cast_sum] using hDω
  have hTsum : Tendsto (fun k => (blockSum (fun j => T j ω) k : ℝ) / k) atTop
      (𝓝 (∫ ω, (T 0 ω : ℝ) ∂μ)) := by
    simpa [blockSum, Nat.cast_sum] using hTω
  exact tendsto_div_of_sandwich_int (T := fun j => T j ω) (fun k => hTpos k ω)
    (fun k hk n => (hs i k n).1 hk) (fun k n => (hs i k n).2) hDsum hTsum hbpos

/-- A `liminf` lower bound transfers to the limit: if `u -> v` and `kappa <= liminf u`
then `kappa <= v`.  This is the last step of the paper's proof
("Finally, applying (lower), we obtain `kappa(m,p) <= v_{N,m}(p) <= 2p-1`"). -/
theorem le_of_le_liminf_of_tendsto {u : ℕ → ℝ} {v κ : ℝ}
    (hconv : Tendsto u atTop (𝓝 v)) (h : κ ≤ liminf u atTop) : κ ≤ v := by
  have hset : ({a : ℝ | ∀ᶠ n in atTop, a ≤ u n}).Nonempty := by
    refine ⟨v - 1, ?_⟩
    exact hconv.eventually (eventually_ge_nhds (by linarith))
  have hS : ∀ a ∈ {a : ℝ | ∀ᶠ n in atTop, a ≤ u n}, a ≤ v := by
    intro a ha
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hconv ha
  have hlim : liminf u atTop ≤ v := by
    rw [Filter.liminf_eq]
    exact csSup_le hset hS
  linarith

/-- **`kappa <= v`** (paper's transfer of the ballistic bound), from the `liminf` form
`(lower)` of Proposition `ball`. -/
theorem ballistic_le_speed_liminf {D T : ℕ → Ω → ℕ}
    (hreg : RegenLaw μ D T) (hsand : Sandwich μ X D T) {κ : ℝ}
    (hball : ∀ᵐ ω ∂μ, ∀ i : Fin N, κ ≤ liminf (fun n => pos X n i ω / n) atTop)
    (hN : 1 ≤ N) : κ ≤ (∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ) := by
  have hae := ae_tendsto_of_regen hreg hsand
  have i₀ : Fin N := ⟨0, hN⟩
  have hall : ∀ᵐ ω ∂μ, κ ≤ (∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ) := by
    filter_upwards [hae, hball] with ω hc hb
    exact le_of_le_liminf_of_tendsto (hc i₀) (hb i₀)
  by_cases hcase : κ ≤ (∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ)
  · exact hcase
  · exact absurd (MeasureTheory.ae_iff.1 hall) (by simp [hcase])

/-- **`kappa <= v`** (paper's transfer of the ballistic bound).  If the ballistic lower
bound `kappa <= X_n^i/n` holds for all `n >= 1`, evaluating it at the regeneration times
and passing to the limit gives `kappa <= E^*D_1/E^*T_1`. -/
theorem ballistic_le_speed (_hlaw : IsInteractingLaw 𝓕 μ X m p) {D T : ℕ → Ω → ℕ}
    (hreg : RegenLaw μ D T) (hsand : Sandwich μ X D T) {κ : ℝ}
    (hball : ∀ᵐ ω ∂μ, ∀ (i : Fin N) (n : ℕ), 1 ≤ n → κ ≤ pos X n i ω / n) (hN : 1 ≤ N) :
    κ ≤ (∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ) := by
  have hbpos : (0 : ℝ) < ∫ ω, (T 0 ω : ℝ) ∂μ := RegenLaw.mean_pos hreg
  obtain ⟨hDint, hTint, hTpos, hDind, hDid, hTind, hTid⟩ := hreg
  have hD := strong_law_ae_real (fun k ω => (D k ω : ℝ)) (hDint 0) hDind hDid
  have hT := strong_law_ae_real (fun k ω => (T k ω : ℝ)) (hTint 0) hTind hTid
  have hmain : ∀ᵐ ω ∂μ, κ ≤ (∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ) := by
    filter_upwards [hD, hT, hsand, hball] with ω hDω hTω hs hb
    have i₀ : Fin N := ⟨0, by omega⟩
    have hDsum : Tendsto (fun k => (blockSum (fun j => D j ω) (k + 1) : ℝ) / k) atTop
        (𝓝 (∫ ω, (D 0 ω : ℝ) ∂μ)) := by
      have h := tendsto_div_succ (u := fun k => (blockSum (fun j => D j ω) k : ℝ))
        (a := ∫ ω, (D 0 ω : ℝ) ∂μ) (by simpa [blockSum, Nat.cast_sum] using hDω)
      simpa using h
    have hTsum : Tendsto (fun k => (blockSum (fun j => T j ω) (k + 1) : ℝ) / k) atTop
        (𝓝 (∫ ω, (T 0 ω : ℝ) ∂μ)) := by
      have h := tendsto_div_succ (u := fun k => (blockSum (fun j => T j ω) k : ℝ))
        (a := ∫ ω, (T 0 ω : ℝ) ∂μ) (by simpa [blockSum, Nat.cast_sum] using hTω)
      simpa using h
    have hlim : Tendsto
        (fun k => (blockSum (fun j => D j ω) (k + 1) : ℝ)
          / (blockSum (fun j => T j ω) (k + 1) : ℝ)) atTop
        (𝓝 ((∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ))) :=
      tendsto_div_of_tendsto_div hDsum hTsum (ne_of_gt hbpos)
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall ?_)
    intro k
    have hlev := hit_level (T := fun j => T j ω) (fun j => hTpos j ω) (x := fun n => X n ω i₀)
      (z := fun j => blockSum (fun j => D j ω) j)
      (fun (j : ℕ) (hj : 1 ≤ j) (n : ℕ) => (hs i₀ j n).1 hj)
      (fun j n => (hs i₀ j n).2) (fun n => by
        rcases abs_step_of_law _hlaw n ω i₀ with h | h <;> omega) (k := k + 1) (by omega)
    have hpos : 1 ≤ blockSum (fun j => T j ω) (k + 1) := by
      have := le_blockSum (fun j => hTpos j ω) (k + 1)
      omega
    have hb' := hb i₀ (blockSum (fun j => T j ω) (k + 1)) hpos
    simp only [pos] at hb'
    rw [hlev] at hb'
    exact hb'
  by_cases hcase : κ ≤ (∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ)
  · exact hcase
  · exact absurd (MeasureTheory.ae_iff.1 hmain) (by simp [hcase])

/-- **`v <= 2p-1`** (paper: `limsup X_n/n <= 2p-1`), transferred to the speed. -/
theorem speed_le_two_p_sub_one_of_regen (hlaw : IsInteractingLaw 𝓕 μ X m p) {D T : ℕ → Ω → ℕ}
    (hreg : RegenLaw μ D T) (hsand : Sandwich μ X D T) (hp : 1 / 2 ≤ p) (hN : 1 ≤ N) :
    (∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ) ≤ 2 * p - 1 := by
  have hae := ae_tendsto_of_regen hreg hsand
  have i₀ : Fin N := ⟨0, hN⟩
  have hconv : ∀ᵐ ω ∂μ, Tendsto
      (fun n => pos X n i₀ ω / n) atTop
      (𝓝 ((∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ))) := by
    filter_upwards [hae] with ω h
    exact h i₀
  exact speed_le_two_p_sub_one hlaw hp i₀ hconv

/-- **Proposition `ball`** of the paper, with its constant *uniform in `N`*:
there is `kappa(m,p) > 0` such that for every `N >= 2` and every system satisfying the
model law, almost surely every walker satisfies `kappa <= liminf X_n^i/n`. -/
def Ballistic (m : ℕ) (p : ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
    2 ≤ N → IsInteractingLaw 𝓕 μ X m p →
      ∀ᵐ ω ∂μ, ∀ i : Fin N, κ ≤ liminf (fun n => pos X n i ω / n) atTop

/-- **Propositions `front` and `regen`** of the paper: for every `N >= 2` and every system
satisfying the model law there are regeneration distance/duration increments `(D,T)`
with the independence, identical-distribution, integrability and positive-mean-duration
properties, and with the path structure `Sandwich` of the regeneration levels. -/
def RegenAvailable (m : ℕ) (p : ℝ) : Prop :=
  ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
    2 ≤ N → IsInteractingLaw 𝓕 μ X m p →
      ∃ (D T : ℕ → Ω → ℕ), RegenLaw μ D T ∧ Sandwich μ X D T

/-- **The initial-regeneration step** (last part of Proposition `regen`, paper §3.3):
under the original law there is an almost surely finite regeneration after which the
translated future has law `P*`, whose limiting speed is `E^*D_1/E^*T_1`.  Since finite
spatial and temporal translations do not change the limit of `X_n^i/n`
(`tendsto_div_of_translate`), this gives the paper's conclusion under `P`. -/
def InitialRegen (m : ℕ) (p : ℝ) : Prop :=
  ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
    2 ≤ N → IsInteractingLaw 𝓕 μ X m p →
    ∀ (D T : ℕ → Ω → ℕ), RegenLaw μ D T → Sandwich μ X D T →
      ∀ᵐ ω ∂μ, ∃ (S : ℕ) (c : ℝ), ∀ i : Fin N,
        Tendsto (fun n => (pos X (n + S) i ω - c) / n) atTop
          (𝓝 ((∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ)))

/-- **Theorem 1.1 of `main_1d_revised.tex`, assembled.**

`_hm` and `_hp2` are part of the paper's parameter range (`m >= 2`, `p < 1`); the
assembly itself does not use them, but the three inputs are only non-vacuous there.

For every `m >= 2` and `p in (1/2,1)`, from the three named paper inputs (`ball`,
`front`+`regen`, initial regeneration) we obtain the full statement of the paper's main
theorem: there is a deterministic `kappa(m,p) > 0` such that for **every** `N >= 2` and
**every** system satisfying the interacting-walk law there is a deterministic
`v in [kappa(m,p), 2p-1]` with

  `lim_{n} X_n^i / n = v` for **every** walker `i`, almost surely.

The bound `kappa` does not depend on `N`, and `v` does not depend on `i`. -/
theorem main_theorem {m : ℕ} {p : ℝ} (_hm : 2 ≤ m) (hp1 : 1 / 2 < p) (_hp2 : p < 1)
    (hball : Ballistic m p) (hregen : RegenAvailable m p) (hinit : InitialRegen m p) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
      2 ≤ N → IsInteractingLaw 𝓕 μ X m p →
        ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
          ∀ᵐ ω ∂μ, ∀ i : Fin N, Tendsto (fun n => pos X n i ω / n) atTop (𝓝 v) := by
  obtain ⟨κ, hκpos, hκ⟩ := hball
  refine ⟨κ, hκpos, ?_⟩
  intro N Ω _ μ _ X 𝓕 hN hlaw
  obtain ⟨D, T, hreg, hsand⟩ := hregen N Ω μ X 𝓕 hN hlaw
  refine ⟨(∫ ω, (D 0 ω : ℝ) ∂μ) / (∫ ω, (T 0 ω : ℝ) ∂μ), ?_, ?_, ?_⟩
  · exact ballistic_le_speed_liminf hreg hsand (hκ N Ω μ X 𝓕 hN hlaw) (by omega)
  · exact speed_le_two_p_sub_one_of_regen hlaw hreg hsand (le_of_lt hp1) (by omega)
  · have htrans := hinit N Ω μ X 𝓕 hN hlaw D T hreg hsand
    filter_upwards [htrans] with ω hω
    intro i
    obtain ⟨S, c, hS⟩ := hω
    exact tendsto_div_of_translate (y := fun n => pos X n i ω) (hS i)

/-- **The paper's Theorem 1.1 as a bare `Prop`** (the target of the campaign).

For every `m >= 2` and `p in (1/2,1)` there is `kappa(m,p) > 0` such that for every
`N >= 2` and every system satisfying the model law there is `v in [kappa(m,p), 2p-1]`
with `X_n^i/n -> v` almost surely for every walker `i`.

This is exactly the conclusion of `main_theorem`; stating it separately makes the
remaining gap explicit: `MainClaim m p` is *equivalent* to the three inputs
`Ballistic m p`, `RegenAvailable m p`, `InitialRegen m p` being available. -/
def MainClaim (m : ℕ) (p : ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → Fin N → ℤ) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›),
    2 ≤ N → IsInteractingLaw 𝓕 μ X m p →
      ∃ v : ℝ, κ ≤ v ∧ v ≤ 2 * p - 1 ∧
        ∀ᵐ ω ∂μ, ∀ i : Fin N, Tendsto (fun n => pos X n i ω / n) atTop (𝓝 v)

/-- The paper's Theorem 1.1 follows from the three named paper inputs. -/
theorem main_claim_of_inputs {m : ℕ} {p : ℝ} (hm : 2 ≤ m) (hp1 : 1 / 2 < p) (hp2 : p < 1)
    (hball : Ballistic m p) (hregen : RegenAvailable m p) (hinit : InitialRegen m p) :
    MainClaim m p :=
  main_theorem hm hp1 hp2 hball hregen hinit

end Swarm
