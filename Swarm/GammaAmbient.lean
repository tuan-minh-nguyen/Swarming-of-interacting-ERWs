/-
  **Finite-union / profile assembly for the Gamma trial count on a fixed deterministic
  ambient window (direction A).**

  The paper (`main_1d_revised.tex`, proof of Proposition `local`) needs the count bound
  `(locsum)`-type statement at the display before line 1226: simultaneously for every nonempty
  proper `A`, every residue class `q` mod `2m` and *every* integer interval
  `[a₀,b₀] ⊂ [r-(T+3)L, r+(T+3)L]`,

  `∑_{a₀≤y≤b₀, y≡q} 1_{Γ_y^A} ≥ (1-p)^{(2m-1)|A|} #{y ∈ [a₀,b₀] : y ≡ q} - 2L^{3/4}`,

  outside an event of probability `C_T e^{-c_T L^{1/2}}`.

  The accepted packages already give, for one *fixed* integer interval `[a₀,b₀]`, the count
  bound with `2m·exp(-t²/K̄(a₀,b₀))` (`GammaInterval.gamma_interval_count_lower`) and the
  finite-family union `GammaInterval.gamma_family_count_lower`.  What is added here is the
  assembly that the paper performs implicitly:

  * the ambient window `[r-(T+3)L, r+(T+3)L]` is a **deterministic** set of integers
    (it depends only on `r,T,L`, never on the array `U`), and the family `ambFamily r T L`
    of *all* its integer subintervals is finite with the explicit cardinal bound
    `(2(T+3)L+1)²`;
  * the `K̄` of every member is bounded by the single linear-in-`L` quantity `2(T+3)L+1`,
    hence by `(2T+7)L` for `L ≥ 1`, so the exponent is at least `(4/(2T+7))·√L` uniformly;
  * the `2^N` groups, the `(2(T+3)L+1)²` intervals and the `2m` residue classes are absorbed
    into explicit `C_T`, `c_T` with `C_T = 2^N·2m·(2T+7)²·(2(2T+7)/e)^4` and `c_T = 2/(2T+7)`
    (`ambConst`; the constants depend only on `N,m,T` — not on `p`, `L` or the array);
  * the set of paths on which **every** member of the deterministic family satisfies the count
    bound is shown measurable;
  * finally the genuine *dynamic* step is separated out and proved: on that deterministic good
    event, for a path `U` and times `n₀ ≤ s ≤ t` with `t ≤ n₀ + (T+3)L`, the **random** window
    `(R^A_s, R^A_t - 2m]` is one of the deterministic family's members as soon as the group
    record at `n₀` is `r` (or, in the paper's `d_r ≤ L` form, as soon as all group positions at
    `n₀` are at least `r - L`).  Consequently the count bound holds for the actual random
    record window, not merely for a pre-chosen one.

  What is *not* claimed: the paper's full `goodprob` event (which also contains `(locmax)`,
  `(locsum)` for `h_j`, and the `O_T(L)` martingale collections), `(locgroup)`, `(locmove)`,
  tightness, regeneration or `MainClaim`.  The `h_j^2` sum `(locsum)` and the martingale
  deviations are separate developments; this file is the Gamma-count term only.

  Axiom/scope: uses only the accepted `GammaInterval`/`GammaSigma`/`GammaEndpoint` API; no
  `sorry`, no new axiom, no `native_decide`.
-/
import Swarm.GammaInterval
import Swarm.Reveal

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set
open Swarming.Model Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

attribute [local instance 10] Classical.propDecidable

namespace Swarming.Enl

variable {N : ℕ}

/-! ## §1. The fixed deterministic ambient window and the family of all its subintervals -/

/-- The left endpoint `r-(T+3)L` of the paper's ambient window.  Deterministic: it does not
depend on the driving array. -/
noncomputable def ambLo (r : ℤ) (T L : ℕ) : ℤ := r - ((T + 3) * L : ℕ)

/-- The right endpoint `r+(T+3)L` of the paper's ambient window. -/
noncomputable def ambHi (r : ℤ) (T L : ℕ) : ℤ := r + ((T + 3) * L : ℕ)

/-- The number `2(T+3)L+1` of integers in the ambient window. -/
def ambWidth (T L : ℕ) : ℕ := 2 * ((T + 3) * L) + 1

/-- **The finite family of *all* integer subintervals of the ambient window**
`[r-(T+3)L, r+(T+3)L]`.  This is the finite set over which the paper takes its union bound. -/
noncomputable def ambFamily (r : ℤ) (T L : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (ambLo r T L) (ambHi r T L)) ×ˢ
      (Finset.Icc (ambLo r T L) (ambHi r T L))).filter (fun ab => ab.1 ≤ ab.2)

lemma mem_ambFamily_iff {r : ℤ} {T L : ℕ} {ab : ℤ × ℤ} :
    ab ∈ ambFamily r T L ↔
      ambLo r T L ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ ambHi r T L := by
  simp only [ambFamily, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩
    exact ⟨h1, h5, h4⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨⟨h1, h2.trans h3⟩, ⟨h1.trans h2, h3⟩⟩, h2⟩

/-- The ambient window has exactly `ambWidth T L` integers. -/
lemma card_Icc_amb (r : ℤ) (T L : ℕ) :
    (Finset.Icc (ambLo r T L) (ambHi r T L)).card = ambWidth T L := by
  have hz : ambHi r T L + 1 - ambLo r T L = ((ambWidth T L : ℕ) : ℤ) := by
    simp only [ambLo, ambHi, ambWidth]
    push_cast
    ring
  rw [Int.card_Icc, hz, Int.toNat_natCast]

/-- **The explicit cardinal bound**: the ambient window has `2(T+3)L+1` integers, so it has at
most `(2(T+3)L+1)²` integer subintervals. -/
lemma ambFamily_card_le (r : ℤ) (T L : ℕ) :
    (ambFamily r T L).card ≤ ambWidth T L ^ 2 := by
  have h1 : (ambFamily r T L).card ≤
      ((Finset.Icc (ambLo r T L) (ambHi r T L)) ×ˢ
        (Finset.Icc (ambLo r T L) (ambHi r T L))).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_product] at h1
  simp only [card_Icc_amb] at h1
  calc (ambFamily r T L).card ≤ ambWidth T L * ambWidth T L := h1
    _ = ambWidth T L ^ 2 := (sq _).symm

/-- Inside the ambient window the left endpoint is automatically nonnegative, as soon as the
window starts at a nonnegative integer.  This is the hypothesis `0 ≤ a₀` needed by the accepted
interval bound, discharged from `r ≥ (T+3)L`. -/
lemma ambLo_nonneg {r : ℤ} {T L : ℕ} (hr : ((T + 3) * L : ℤ) ≤ r) : 0 ≤ ambLo r T L := by
  simp only [ambLo]
  push_cast
  linarith

/-- Every member of the family is a genuine interval inside the window. -/
lemma ambFamily_spec {r : ℤ} {T L : ℕ} {ab : ℤ × ℤ} (h : ab ∈ ambFamily r T L) :
    ambLo r T L ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ ambHi r T L :=
  mem_ambFamily_iff.mp h

/-! ## §2. One linear-in-`L` bound on the class depth `K̄` -/

/-- **`K̄` is at most the width of the ambient window.**  Since `b₀-a₀ ≤ 2(T+3)L` inside the
window and `2m ≥ 2`, the class depth `⌊(b₀-a₀)/2m⌋+1` is at most `2(T+3)L+1`. -/
lemma clsKbar_le_ambWidth {r : ℤ} {T L m : ℕ} {ab : ℤ × ℤ} (h : ab ∈ ambFamily r T L) :
    clsKbar ab.1 ab.2 m ≤ ambWidth T L := by
  obtain ⟨hlo, hab, hhi⟩ := ambFamily_spec h
  have hhi' : ab.2 ≤ r + (((T : ℤ) + 3) * (L : ℤ)) := by
    have h' := hhi
    simp only [ambHi] at h'
    push_cast at h'
    linarith
  have hlo' : r - (((T : ℤ) + 3) * (L : ℤ)) ≤ ab.1 := by
    have h' := hlo
    simp only [ambLo] at h'
    push_cast at h'
    linarith
  have hz : ab.2 - ab.1 ≤ ((2 * ((T + 3) * L) : ℕ) : ℤ) := by
    have h2 : ab.2 - ab.1 ≤ 2 * (((T : ℤ) + 3) * (L : ℤ)) := by linarith
    calc ab.2 - ab.1 ≤ 2 * (((T : ℤ) + 3) * (L : ℤ)) := h2
      _ = ((2 * ((T + 3) * L) : ℕ) : ℤ) := by push_cast; ring
  have hnat : (ab.2 - ab.1).toNat ≤ 2 * ((T + 3) * L) := Int.toNat_le.mpr hz
  have hd : (ab.2 - ab.1).toNat / (2 * m) ≤ (ab.2 - ab.1).toNat := Nat.div_le_self _ _
  simp only [clsKbar, ambWidth]
  omega

/-- **The linear-in-`L` form.**  For `L ≥ 1` the width `2(T+3)L+1` is at most `(2T+7)L`. -/
lemma ambWidth_le_linear {T : ℕ} {L : ℕ} (hL : 1 ≤ L) :
    (ambWidth T L : ℝ) ≤ (2 * (T : ℝ) + 7) * (L : ℝ) := by
  have hL' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  simp only [ambWidth]
  push_cast
  nlinarith

/-! ## §3. The uniform exponential exponent and the per-group finite-family bound -/

/-- `K̄ ≥ 1`, so the exponent `t²/K̄` is always defined with a positive denominator. -/
lemma one_le_clsKbar (a0 b0 : ℤ) (m : ℕ) : 1 ≤ clsKbar a0 b0 m := by
  simp only [clsKbar]
  exact Nat.le_add_left 1 _

/-- **The exponent comparison.**  With the paper's deviation `t = 2L^{3/4}` the exponent of
`gamma_interval_count_lower` is `4L√L/K̄`; since `K̄ ≤ 2(T+3)L+1 ≤ (2T+7)L` for `L ≥ 1`, it is
at least `(4/(2T+7))√L` — one `L`-independent coefficient, uniform over the whole family. -/
lemma exp_ambFamily_le {r : ℤ} {T L m : ℕ} (hL : 1 ≤ L) {ab : ℤ × ℤ}
    (hmem : ab ∈ ambFamily r T L) :
    Real.exp (-((2 * Real.sqrt (L * Real.sqrt L)) ^ 2 / (clsKbar ab.1 ab.2 m : ℝ))) ≤
      Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hD : (0 : ℝ) < 2 * (T : ℝ) + 7 := by positivity
  have hKpos : (0 : ℝ) < (clsKbar ab.1 ab.2 m : ℝ) := by
    have := one_le_clsKbar ab.1 ab.2 m
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one this
  have hsL : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hsq : Real.sqrt L * Real.sqrt L = (L : ℝ) := Real.mul_self_sqrt hLpos.le
  -- the uniform linear bound on `K̄`
  have hKL : (clsKbar ab.1 ab.2 m : ℝ) ≤ (2 * (T : ℝ) + 7) * (L : ℝ) :=
    (by exact_mod_cast clsKbar_le_ambWidth hmem : (clsKbar ab.1 ab.2 m : ℝ) ≤ (ambWidth T L : ℝ)).trans
      (ambWidth_le_linear hL)
  -- `4√L/D ≤ 4L√L/K̄`
  have hkey : 4 / (2 * (T : ℝ) + 7) * Real.sqrt L ≤
      4 * (L : ℝ) * Real.sqrt L / (clsKbar ab.1 ab.2 m : ℝ) := by
    rw [show 4 / (2 * (T : ℝ) + 7) * Real.sqrt L =
      4 * Real.sqrt L / (2 * (T : ℝ) + 7) by ring]
    rw [div_le_div_iff₀ hD hKpos]
    have hmul : (clsKbar ab.1 ab.2 m : ℝ) * Real.sqrt L ≤
        ((2 * (T : ℝ) + 7) * (L : ℝ)) * Real.sqrt L := by
      nlinarith [hKL, hsL.le]
    nlinarith [hmul]
  have harg : -((2 * Real.sqrt (L * Real.sqrt L)) ^ 2 / (clsKbar ab.1 ab.2 m : ℝ)) ≤
      -(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L := by
    have hsq' : (2 * Real.sqrt (L * Real.sqrt L)) ^ 2 = 4 * (L : ℝ) * Real.sqrt L :=
      two_mul_pow_three_quarters_sq hLpos.le
    rw [hsq']
    linarith
  exact Real.exp_le_exp.mpr harg

/-- **The finite-family count bound over the whole deterministic ambient window, for one
group `A`.**  Outside one event,

`P ≤ (2(T+3)L+1)² · 2m · exp(-(4/(2T+7))·√L)`,

simultaneously for **every** integer subinterval `[a₀,b₀]` of `[r-(T+3)L, r+(T+3)L]` the number
of successful trials `Γ^A_y`, `y ∈ [a₀,b₀]`, is at least
`(1-p)^{(2m-1)|A|}(b₀-a₀+1) - 4m L^{3/4}`.

The endpoints of every interval in the family are **deterministic** integers; nothing here is
conditioned on the array.  All constants are explicit: the only losses are the cardinality of
the family, the `2m` residue classes and the linear bound `K̄ ≤ (2T+7)L`. -/
theorem gamma_ambient_family_count_lower (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) (A : Finset (Fin N)) (hA : A.Nonempty) {r : ℤ} {T L : ℕ} (hL : 1 ≤ L)
    (hr : ((T + 3) * L : ℤ) ≤ r) :
    arrayMeasure N (⋃ ab ∈ ambFamily r T L, {U : Array N |
        ((Finset.Icc ab.1 ab.2).filter (fun y => U ∈ GammaSet p m hA y)).card
          < (1 - p) ^ ((2 * m - 1) * A.card) * ((ab.2 - ab.1).toNat + 1 : ℝ)
            - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L)})
      ≤ ((ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) * ((2 * m : ℕ) * ENNReal.ofReal
          (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L))) := by
  classical
  have ht : (0 : ℝ) ≤ 2 * Real.sqrt (L * Real.sqrt L) := by positivity
  have hlo : ∀ ab ∈ ambFamily r T L, 0 ≤ ab.1 := by
    intro ab hab
    exact (ambLo_nonneg hr).trans (ambFamily_spec hab).1
  have hle : ∀ ab ∈ ambFamily r T L, ab.1 ≤ ab.2 := fun ab hab => (ambFamily_spec hab).2.1
  have hfam := gamma_family_count_lower (p := p) hp0 hp1 m hm A hA
    (Is := ambFamily r T L) ht hlo hle
  -- rewrite the paper's deviation `2·m·(2L^{3/4})` as `4m√(L√L)`
  have hthr : ∀ ab : ℤ × ℤ,
      (1 - p) ^ ((2 * m - 1) * A.card) * ((ab.2 - ab.1).toNat + 1 : ℝ)
          - 2 * (m : ℝ) * (2 * Real.sqrt (L * Real.sqrt L)) =
        (1 - p) ^ ((2 * m - 1) * A.card) * ((ab.2 - ab.1).toNat + 1 : ℝ)
          - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L) := by
    intro ab
    rw [two_m_mul_paper_deviation]
  simp only [hthr] at hfam
  refine hfam.trans ?_
  have hterm : ∀ ab ∈ ambFamily r T L,
      (2 * m : ℕ) * ENNReal.ofReal
          (Real.exp (-((2 * Real.sqrt (L * Real.sqrt L)) ^ 2 / (clsKbar ab.1 ab.2 m : ℝ))))
        ≤ (2 * m : ℕ) * ENNReal.ofReal
            (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L)) := by
    intro ab hab
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (exp_ambFamily_le hL hab)) _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_left ?_ _
  exact_mod_cast ambFamily_card_le r T L

/-! ## §4. Union over all nonempty proper groups -/

/-- The finite set of **nonempty proper** groups `A ⊂ {1,…,N}` over which the paper takes its
union bound.  It is finite because `Finset (Fin N)` is. -/
noncomputable def properGroups (N : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Finset (Fin N))).filter (fun A => A.Nonempty ∧ A ≠ Finset.univ)

lemma mem_properGroups {A : Finset (Fin N)} :
    A ∈ properGroups N ↔ A.Nonempty ∧ A ≠ (Finset.univ : Finset (Fin N)) := by
  simp only [properGroups, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The number of nonempty proper subsets is at most `2^N`. -/
lemma card_properGroups_le (N : ℕ) : (properGroups N).card ≤ 2 ^ N := by
  have h1 : (properGroups N).card ≤ (Finset.univ : Finset (Finset (Fin N))).card :=
    Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset (Finset (Fin N))).card = 2 ^ N := by
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  omega

/-- **The count bound simultaneously for every nonempty proper group and every integer
subinterval of the deterministic ambient window.**  The union over the finitely many groups
costs the factor `#properGroups ≤ 2^N`:

`P ≤ 2^N · (2(T+3)L+1)² · 2m · exp(-(4/(2T+7))√L)`.

Every constant is explicit and independent of `p`; the event is a finite union of explicitly
described measurable sets. -/
theorem gamma_ambient_all_groups_count_lower (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) {r : ℤ} {T L : ℕ} (hL : 1 ≤ L) (hr : ((T + 3) * L : ℤ) ≤ r) :
    arrayMeasure N (⋃ A ∈ (properGroups (N := N)).attach, ⋃ ab ∈ ambFamily r T L, {U : Array N |
        ((Finset.Icc ab.1 ab.2).filter (fun y => U ∈ GammaSet p m (mem_properGroups.mp A.2).1 y)).card
          < (1 - p) ^ ((2 * m - 1) * A.1.card) * ((ab.2 - ab.1).toNat + 1 : ℝ)
            - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L)})
      ≤ (2 ^ N : ℕ) * (((ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) * ((2 * m : ℕ) * ENNReal.ofReal
          (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L)))) := by
  classical
  have hper : ∀ A ∈ (properGroups (N := N)).attach,
      arrayMeasure N (⋃ ab ∈ ambFamily r T L, {U : Array N |
          ((Finset.Icc ab.1 ab.2).filter
            (fun y => U ∈ GammaSet p m (mem_properGroups.mp A.2).1 y)).card
            < (1 - p) ^ ((2 * m - 1) * A.1.card) * ((ab.2 - ab.1).toNat + 1 : ℝ)
              - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L)})
        ≤ ((ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) * ((2 * m : ℕ) * ENNReal.ofReal
            (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L))) := by
    intro A _
    exact gamma_ambient_family_count_lower p hp0 hp1 m hm A.1 (mem_properGroups.mp A.2).1 hL hr
  refine (measure_biUnion_finset_le (properGroups (N := N)).attach _).trans ?_
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_left ?_ _
  rw [Finset.card_attach]
  exact_mod_cast card_properGroups_le N

/-! ## §5. Absorption of the cardinality profile into explicit `C_T`, `c_T` -/

/-- `e·s ≤ e^s` for every real `s` (the tangent at `1` of the logarithm). -/
lemma exp_one_mul_le_exp (s : ℝ) : Real.exp 1 * s ≤ Real.exp s := by
  have h : s ≤ Real.exp (s - 1) := by
    have := Real.add_one_le_exp (s - 1)
    linarith
  calc Real.exp 1 * s ≤ Real.exp 1 * Real.exp (s - 1) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le
    _ = Real.exp s := by
        rw [← Real.exp_add, show 1 + (s - 1) = s by ring]

/-- **`u e^{-cu} ≤ 1/(ec)`**: the elementary exponential maximum used to absorb polynomial
factors. -/
lemma mul_exp_neg_le (c : ℝ) (hc : 0 < c) (u : ℝ) (hu : 0 ≤ u) :
    u * Real.exp (-(c * u)) ≤ 1 / (Real.exp 1 * c) := by
  have hden : (0 : ℝ) < Real.exp 1 * c := by positivity
  rw [le_div_iff₀ hden]
  have h1 : Real.exp 1 * (c * u) ≤ Real.exp (c * u) := exp_one_mul_le_exp _
  have h2 : Real.exp 1 * (c * u) * Real.exp (-(c * u)) ≤
      Real.exp (c * u) * Real.exp (-(c * u)) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have h3 : Real.exp (c * u) * Real.exp (-(c * u)) = 1 := by
    rw [← Real.exp_add, show c * u + -(c * u) = 0 by ring, Real.exp_zero]
  have h4 : u * Real.exp (-(c * u)) * (Real.exp 1 * c) =
      Real.exp 1 * (c * u) * Real.exp (-(c * u)) := by ring
  rw [h4]
  exact h2.trans_eq h3

/-- **`u⁴ e^{-bu} ≤ (4/(eb))⁴`**: absorbing a quartic growth factor. -/
lemma pow_four_mul_exp_neg_le (b : ℝ) (hb : 0 < b) (u : ℝ) (hu : 0 ≤ u) :
    u ^ 4 * Real.exp (-(b * u)) ≤ (4 / (Real.exp 1 * b)) ^ 4 := by
  have hb4 : (0 : ℝ) < b / 4 := by linarith
  have hbase : u * Real.exp (-(b / 4 * u)) ≤ 1 / (Real.exp 1 * (b / 4)) :=
    mul_exp_neg_le (b / 4) hb4 u hu
  have hnn : (0 : ℝ) ≤ u * Real.exp (-(b / 4 * u)) :=
    mul_nonneg hu (Real.exp_pos _).le
  have h4 := pow_le_pow_left₀ hnn hbase 4
  have hexp : Real.exp (-(b / 4 * u)) ^ 4 = Real.exp (-(b * u)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hleft : (u * Real.exp (-(b / 4 * u))) ^ 4 = u ^ 4 * Real.exp (-(b * u)) := by
    rw [mul_pow, hexp]
  have hright : (1 / (Real.exp 1 * (b / 4))) ^ 4 = (4 / (Real.exp 1 * b)) ^ 4 := by
    congr 1
    field_simp
  rwa [hleft, hright] at h4

/-- The explicit constant `C_T` of the Gamma count term for `N` walkers and the group size
parameter `m`:  `C_T = 2^N · 2m · (2T+7)² · (2(2T+7)/e)⁴`.  It depends only on `N,m,T` — not on
`p`, not on `L`, and not on the driving array. -/
noncomputable def ambConst (N m T : ℕ) : ℝ :=
  (2 : ℝ) ^ N * (2 * (m : ℝ) * (2 * (T : ℝ) + 7) ^ 2 *
    (2 * (2 * (T : ℝ) + 7) / Real.exp 1) ^ 4)

lemma ambConst_nonneg (N m T : ℕ) : 0 ≤ ambConst N m T := by
  unfold ambConst
  positivity

/-- Combining four nonnegative `ofReal` factors. -/
lemma ofReal_four_mul (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ENNReal.ofReal a * (ENNReal.ofReal b * (ENNReal.ofReal c * ENNReal.ofReal d)) =
      ENNReal.ofReal (a * b * c * d) := by
  rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul ha]
  congr 1
  ring

/-- **The real-variable absorption.**  The cardinality profile `2^N w² · 2m` and the exponent
`-(4/(2T+7))√L` are absorbed into `C_T e^{-(2/(2T+7))√L}`. -/
lemma amb_real_absorb (N m T : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    (2 : ℝ) ^ N * (((ambWidth T L : ℝ)) ^ 2 * ((2 * (m : ℝ)) *
        Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L)))
      ≤ ambConst N m T * Real.exp (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt L) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hD : (0 : ℝ) < 2 * (T : ℝ) + 7 := by positivity
  have hu : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hsq : Real.sqrt L ^ 2 = (L : ℝ) := Real.sq_sqrt hLpos.le
  have hw : ((ambWidth T L : ℝ)) ≤ (2 * (T : ℝ) + 7) * Real.sqrt L ^ 2 := by
    have h := ambWidth_le_linear (T := T) hL
    rwa [← hsq] at h
  have hw0 : (0 : ℝ) ≤ (ambWidth T L : ℝ) := by positivity
  have hw2 : ((ambWidth T L : ℝ)) ^ 2 ≤ (2 * (T : ℝ) + 7) ^ 2 * Real.sqrt L ^ 4 := by
    have h : ((ambWidth T L : ℝ)) ^ 2 ≤ ((2 * (T : ℝ) + 7) * Real.sqrt L ^ 2) ^ 2 :=
      pow_le_pow_left₀ hw0 hw 2
    calc ((ambWidth T L : ℝ)) ^ 2 ≤ ((2 * (T : ℝ) + 7) * Real.sqrt L ^ 2) ^ 2 := h
      _ = (2 * (T : ℝ) + 7) ^ 2 * Real.sqrt L ^ 4 := by ring
  have hq : Real.sqrt L ^ 4 * Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)) ≤
      (4 / (Real.exp 1 * (2 / (2 * (T : ℝ) + 7)))) ^ 4 :=
    pow_four_mul_exp_neg_le _ (by positivity) _ hu
  have hq' : (4 / (Real.exp 1 * (2 / (2 * (T : ℝ) + 7)))) ^ 4 =
      (2 * (2 * (T : ℝ) + 7) / Real.exp 1) ^ 4 := by
    congr 1
    field_simp
    ring
  have hem0 : (0 : ℝ) ≤ 2 * (m : ℝ) := by positivity
  have he2 : (0 : ℝ) < Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)) := Real.exp_pos _
  have hsplit : Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L) =
      Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)) *
        Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hstep1 : ((ambWidth T L : ℝ)) ^ 2 * (2 * (m : ℝ)) *
        Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L)
      ≤ ((2 * (T : ℝ) + 7) ^ 2 * Real.sqrt L ^ 4) * (2 * (m : ℝ)) *
          (Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)) *
            Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L))) := by
    rw [hsplit]
    have h3 : (0 : ℝ) ≤ Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)) *
        Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw2 hem0) h3
  have hstep2 : ((2 * (T : ℝ) + 7) ^ 2 * Real.sqrt L ^ 4) * (2 * (m : ℝ)) *
        (Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)) *
          Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)))
      = (2 * (m : ℝ) * (2 * (T : ℝ) + 7) ^ 2) *
          (Real.sqrt L ^ 4 * Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L))) *
            Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)) := by ring
  have hstep3 : (2 * (m : ℝ) * (2 * (T : ℝ) + 7) ^ 2) *
        (Real.sqrt L ^ 4 * Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L))) *
          Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L))
      ≤ (2 * (m : ℝ) * (2 * (T : ℝ) + 7) ^ 2) *
          (2 * (2 * (T : ℝ) + 7) / Real.exp 1) ^ 4 *
            Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)) := by
    have hpos1 : (0 : ℝ) ≤ 2 * (m : ℝ) * (2 * (T : ℝ) + 7) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hq.trans_eq hq') hpos1) he2.le
  have hchain : ((ambWidth T L : ℝ)) ^ 2 * (2 * (m : ℝ)) *
        Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L)
      ≤ (2 * (m : ℝ) * (2 * (T : ℝ) + 7) ^ 2 *
          (2 * (2 * (T : ℝ) + 7) / Real.exp 1) ^ 4) *
            Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L)) := by
    refine hstep1.trans ?_
    rw [hstep2]
    refine hstep3.trans (le_of_eq ?_)
    ring
  calc (2 : ℝ) ^ N * (((ambWidth T L : ℝ)) ^ 2 * ((2 * (m : ℝ)) *
        Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L)))
      = (2 : ℝ) ^ N * (((ambWidth T L : ℝ)) ^ 2 * (2 * (m : ℝ)) *
          Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L)) := by ring
    _ ≤ (2 : ℝ) ^ N * ((2 * (m : ℝ) * (2 * (T : ℝ) + 7) ^ 2 *
          (2 * (2 * (T : ℝ) + 7) / Real.exp 1) ^ 4) *
            Real.exp (-(2 / (2 * (T : ℝ) + 7) * Real.sqrt L))) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = ambConst N m T * Real.exp (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt L) := by
        unfold ambConst
        rw [show -(2 / (2 * (T : ℝ) + 7)) * Real.sqrt L =
          -(2 / (2 * (T : ℝ) + 7) * Real.sqrt L) by ring]
        ring

/-- **Absorption lemma (ENNReal form).**  For `L ≥ 1` the profile `2^N(2(T+3)L+1)²·2m` and the
exponent `-(4/(2T+7))√L` are absorbed into `C_T e^{-c_T√L}` with `c_T = 2/(2T+7)`; this is the
paper's `C_T e^{-c_T L^{1/2}}` shape. -/
theorem amb_profile_absorb (N m T : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    (2 ^ N : ℕ) * (((ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) * ((2 * m : ℕ) * ENNReal.ofReal
        (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L))))
      ≤ ENNReal.ofReal (ambConst N m T * Real.exp
          (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt L)) := by
  have hw2nn : (0 : ℝ) ≤ ((ambWidth T L : ℝ)) ^ 2 := by positivity
  have hexpnn : (0 : ℝ) ≤ Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L) :=
    (Real.exp_pos _).le
  have hcast2 : ((ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (((ambWidth T L : ℝ)) ^ 2) := by
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  have h2N : ((2 ^ N : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ N) := by
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  have h2m : ((2 * m : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) * (m : ℝ)) := by
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  rw [hcast2, h2N, h2m]
  rw [ofReal_four_mul ((2 : ℝ) ^ N) (((ambWidth T L : ℝ)) ^ 2) ((2 : ℝ) * (m : ℝ))
    (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L))
    (by positivity) hw2nn (by positivity) hexpnn]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (2 : ℝ) ^ N * ((ambWidth T L : ℝ)) ^ 2 * (2 * (m : ℝ)) *
        Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L)
      = (2 : ℝ) ^ N * (((ambWidth T L : ℝ)) ^ 2 * ((2 * (m : ℝ)) *
          Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L))) := by ring
    _ ≤ ambConst N m T * Real.exp (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt L) :=
        amb_real_absorb N m T hL

/-! ## §6. The named bad/good events and their measurability -/

/-- **The bad event of the Gamma-count term for one group `A`.**  It is the union, over the finite
family of all integer subintervals of the deterministic ambient window, of the sets on which the
number of successful trials `Γ^A_y` in that interval falls below
`(1-p)^{(2m-1)|A|}(b₀-a₀+1) - 4m L^{3/4}`. -/
noncomputable def ambBad (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty) (r : ℤ)
    (T L : ℕ) : Set (Array N) :=
  ⋃ ab ∈ ambFamily r T L, {U : Array N |
    (((Finset.Icc ab.1 ab.2).filter (fun y => U ∈ GammaSet p m hA y)).card : ℝ)
      < (1 - p) ^ ((2 * m - 1) * A.card) * ((ab.2 - ab.1).toNat + 1 : ℝ)
        - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L)}

/-- The good event for one group: on it every integer subinterval of the ambient window carries
the paper's count lower bound. -/
noncomputable def ambGood (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty) (r : ℤ)
    (T L : ℕ) : Set (Array N) :=
  (ambBad p m hA r T L)ᶜ

/-- The bad event for the paper's simultaneous statement: the union over every nonempty proper
group.  (`.attach` only carries the nonemptiness witness of each member.) -/
noncomputable def ambBadAll (p : ℝ) (m : ℕ) (r : ℤ) (T L : ℕ) : Set (Array N) :=
  ⋃ A ∈ (properGroups (N := N)).attach, ambBad p m (mem_properGroups.mp A.2).1 r T L

/-- The paper's simultaneous good event for the Gamma count term. -/
noncomputable def ambGoodAll (p : ℝ) (m : ℕ) (r : ℤ) (T L : ℕ) : Set (Array N) :=
  (ambBadAll p m r T L)ᶜ

/-- On the good event of one group, every integer subinterval of the deterministic ambient
window carries the paper's count lower bound. -/
lemma ambGood_count_le {p : ℝ} {m : ℕ} {A : Finset (Fin N)} {hA : A.Nonempty} {r : ℤ}
    {T L : ℕ} {U : Array N} (hU : U ∈ ambGood p m hA r T L) {ab : ℤ × ℤ}
    (hab : ab ∈ ambFamily r T L) :
    (1 - p) ^ ((2 * m - 1) * A.card) * ((ab.2 - ab.1).toNat + 1 : ℝ)
        - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L)
      ≤ (((Finset.Icc ab.1 ab.2).filter (fun y => U ∈ GammaSet p m hA y)).card : ℝ) := by
  by_contra hlt
  exact hU (Set.mem_iUnion.mpr ⟨ab, Set.mem_iUnion.mpr ⟨hab, not_le.mp hlt⟩⟩)

/-- On the simultaneous good event, every nonempty proper group and every integer subinterval of
the deterministic ambient window carries the paper's count lower bound. -/
lemma ambGoodAll_count_le {p : ℝ} {m : ℕ} {r : ℤ} {T L : ℕ} {A : Finset (Fin N)}
    (hA : A ∈ properGroups (N := N)) {U : Array N} (hU : U ∈ ambGoodAll (N := N) p m r T L)
    {ab : ℤ × ℤ} (hab : ab ∈ ambFamily r T L) :
    (1 - p) ^ ((2 * m - 1) * A.card) * ((ab.2 - ab.1).toNat + 1 : ℝ)
        - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L)
      ≤ (((Finset.Icc ab.1 ab.2).filter
          (fun y => U ∈ GammaSet p m (mem_properGroups.mp hA).1 y)).card : ℝ) := by
  have hbad : U ∉ ambBad p m (mem_properGroups.mp hA).1 r T L := by
    intro h
    exact hU (Set.mem_iUnion.mpr ⟨⟨A, hA⟩, Set.mem_iUnion.mpr ⟨Finset.mem_attach _ _, h⟩⟩)
  exact ambGood_count_le hbad hab

/-- The paper's window count is a sum over the `2m` residue classes of the ambient interval, so
the event that it is below a real threshold is measurable. -/
lemma measurableSet_window_count_lt (p : ℝ) (m : ℕ) (hm : 0 < m) {A : Finset (Fin N)}
    (hA : A.Nonempty) {a0 b0 : ℤ} (hab : a0 ≤ b0) {x : ℝ} :
    MeasurableSet {U : Array N |
      (((Finset.Icc a0 b0).filter (fun y => U ∈ GammaSet p m hA y)).card : ℝ) < x} := by
  classical
  have hset : {U : Array N |
        (((Finset.Icc a0 b0).filter (fun y => U ∈ GammaSet p m hA y)).card : ℝ) < x}
      = {U : Array N | (∑ j ∈ Finset.range (2 * m),
          (clsCount p m hA (clsY0 a0 j) (clsK a0 b0 m j) U : ℝ)) < x} := by
    ext U
    simp only [Set.mem_ofPred_eq]
    rw [card_filter_Icc_eq_sum_clsCount p m hm hA hab U, Nat.cast_sum]
  rw [hset]
  exact measurableSet_lt (Finset.measurable_sum _ fun j _ => measurable_clsCount p m hA _ _)
    measurable_const

lemma measurableSet_ambBad (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (hm : 0 < m)
    {A : Finset (Fin N)} (hA : A.Nonempty) (r : ℤ) (T L : ℕ) :
    MeasurableSet (ambBad p m hA r T L) := by
  refine Finset.measurableSet_biUnion _ ?_
  intro ab hab
  exact measurableSet_window_count_lt p m hm hA (ambFamily_spec hab).2.1

lemma measurableSet_ambBadAll (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ) (hm : 0 < m)
    (r : ℤ) (T L : ℕ) :
    MeasurableSet (ambBadAll (N := N) p m r T L) := by
  refine Finset.measurableSet_biUnion _ ?_
  intro A _
  exact measurableSet_ambBad p hp0 hp1 m hm (mem_properGroups.mp A.2).1 r T L

/-- **The paper's `goodprob` shape for the Gamma count term** (the count part only): the
simultaneous good event over all nonempty proper groups and all integer subintervals of the
deterministic ambient window has complement of measure at most `C_T e^{-c_T L^{1/2}}`, with the
explicit `C_T = ambConst N m T` and `c_T = 2/(2T+7)`. -/
theorem gamma_ambient_good_measure_ge (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) {r : ℤ} {T L : ℕ} (hL : 1 ≤ L) (hr : ((T + 3) * L : ℤ) ≤ r) :
    1 - ENNReal.ofReal (ambConst N m T * Real.exp
        (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt L))
      ≤ arrayMeasure N (ambGoodAll (N := N) p m r T L) := by
  have hbound : arrayMeasure N (ambBadAll (N := N) p m r T L) ≤
      ENNReal.ofReal (ambConst N m T * Real.exp
        (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt L)) :=
    (gamma_ambient_all_groups_count_lower p hp0 hp1 m hm hL hr).trans
      (amb_profile_absorb N m T hL)
  rw [ambGoodAll, measure_compl (measurableSet_ambBadAll p hp0 hp1 m hm r T L) (measure_ne_top _ _),
    measure_univ]
  exact tsub_le_tsub_left hbound 1

/-! ## §7. The actual random record window is covered by the deterministic family

The previous sections are statements about the fixed deterministic window and its subintervals.
The paper uses them at the **random** window `(R^A_s, R^A_t - 2m]`: the record levels `R^A_s`,
`R^A_t` are not known in advance and are not even measurable at time `s`.  The lemmas below are
the exact bridge.  They are *pathwise*: given a single path `U` on the good event and two times
`n₀ ≤ s ≤ t` with `t ≤ n₀ + (T+3)L`, if the group record at `n₀` is `r` (or lies above `r - L`),
then the random window is literally one of the finitely many deterministic intervals of
`ambFamily r T L`, so the deterministic count bound applies to it.

The only genuinely dynamic input is therefore the level `r` and the horizon: the window has to
be compared with a level that the path has actually reached by time `s`.  On the paper's event
`{d_r ≤ L}` this is supplied by `ARMax` at the first passage of the global record to `r`; see
`gamma_actual_window_count_ARMax`. -/

/-- The paper's count over the **random** record window
`(R^A_s, R^A_t - 2m] = {y ∈ ℤ : R^A_s < y ≤ R^A_t - 2m}`. -/
noncomputable def recWindowCount (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (U : Array N) (s t : ℕ) : ℕ :=
  ((Finset.Icc (runMaxA p m U hA s + 1)
    (runMaxA p m U hA t - ((2 * m : ℕ) : ℤ))).filter (fun y => U ∈ GammaSet p m hA y)).card

/-- The random-window count as the paper's sum of indicators. -/
lemma recWindowCount_eq_sum (p : ℝ) (m : ℕ) {A : Finset (Fin N)} (hA : A.Nonempty)
    (U : Array N) (s t : ℕ) :
    (recWindowCount p m hA U s t : ℝ) =
      ∑ y ∈ Finset.Icc (runMaxA p m U hA s + 1)
          (runMaxA p m U hA t - ((2 * m : ℕ) : ℤ)),
        (if U ∈ GammaSet p m hA y then (1 : ℝ) else 0) := by
  rw [recWindowCount]
  exact (sum_indicator_GammaSet p m hA U).symm

/-- The group record increases by at most one per step, hence by at most `k` in `k` steps. -/
lemma runMaxA_add_le {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    (n0 : ℕ) (k : ℕ) :
    runMaxA p m U hA (n0 + k) ≤ runMaxA p m U hA n0 + (k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : runMaxA p m U hA (n0 + (k + 1)) ≤ runMaxA p m U hA (n0 + k) + 1 := by
        have h2 := runMaxA_succ_le (p := p) (m := m) (U := U) (hA := hA) (n0 + k)
        rwa [show n0 + k + 1 = n0 + (k + 1) by ring] at h2
      push_cast
      omega

/-- **The deterministic family covers the random record window.**  If at time `n₀` the group
record is at least `r - L` and at most `r`, and `t ≤ n₀ + (T+3)L`, then for any `n₀ ≤ s ≤ t` the
random window `(R^A_s, R^A_t - 2m]` (when nonempty) is a member of `ambFamily r T L`. -/
lemma record_window_mem_ambFamily {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)}
    {hA : A.Nonempty} {r : ℤ} {T L : ℕ} (hL : 1 ≤ L) {n0 s t : ℕ} (hn0 : n0 ≤ s)
    (hst : s ≤ t) (hhor : t ≤ n0 + (T + 3) * L) (hr : ((T + 3) * L : ℤ) ≤ r)
    (hlo0 : r - (L : ℤ) ≤ runMaxA p m U hA n0)
    (hhi : runMaxA p m U hA n0 ≤ r)
    (hne : runMaxA p m U hA s + 1 ≤ runMaxA p m U hA t - ((2 * m : ℕ) : ℤ)) :
    (runMaxA p m U hA s + 1, runMaxA p m U hA t - ((2 * m : ℕ) : ℤ)) ∈ ambFamily r T L := by
  have hLZ : (L : ℤ) ≤ ((T + 3) * L : ℕ) := by
    have h : L ≤ (T + 3) * L := Nat.le_mul_of_pos_left L (by omega)
    exact_mod_cast h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hn0.trans hst)
  subst hk
  have hmono : runMaxA p m U hA n0 ≤ runMaxA p m U hA s := runMaxA_mono hn0
  have hk : (k : ℤ) ≤ ((T + 3) * L : ℕ) := by
    have h : k ≤ (T + 3) * L := by omega
    exact_mod_cast h
  have hlt : runMaxA p m U hA (n0 + k) ≤ runMaxA p m U hA n0 + (k : ℤ) :=
    runMaxA_add_le n0 k
  refine mem_ambFamily_iff.mpr ⟨?_, hne, ?_⟩
  · simp only [ambLo]
    omega
  · simp only [ambHi]
    omega

/-- **The count bound on the actual random record window.**  On the good event of §6, for a path
`U` and times `n₀ ≤ s ≤ t ≤ n₀ + (T+3)L` satisfying the two level conditions at `n₀`, the number
of successful trials in the *random* window `(R^A_s, R^A_t - 2m]` is at least

`(1-p)^{(2m-1)|A|} (R^A_t - R^A_s - 2m) - 4m L^{3/4}`,

which is exactly the paper's display preceding `(locmove)` (line 1290 of `main_1d_revised.tex`).
No probability is used: this is a pathwise consequence of the deterministic good event. -/
theorem gamma_actual_window_count (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) {A : Finset (Fin N)} (hA : A.Nonempty) {r : ℤ} {T L : ℕ} (hL : 1 ≤ L)
    (hr : ((T + 3) * L : ℤ) ≤ r) {U : Array N} (hgood : U ∈ ambGood p m hA r T L)
    {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (T + 3) * L)
    (hlo0 : r - (L : ℤ) ≤ runMaxA p m U hA n0) (hhi : runMaxA p m U hA n0 ≤ r) :
    (1 - p) ^ ((2 * m - 1) * A.card) *
        (((runMaxA p m U hA t - runMaxA p m U hA s - ((2 * m : ℕ) : ℤ)).toNat : ℝ))
          - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L)
      ≤ (recWindowCount p m hA U s t : ℝ) := by
  classical
  set Rs := runMaxA p m U hA s with hRs
  set Rt := runMaxA p m U hA t with hRt
  by_cases hne : Rs + 1 ≤ Rt - ((2 * m : ℕ) : ℤ)
  · have hmem : (Rs + 1, Rt - ((2 * m : ℕ) : ℤ)) ∈ ambFamily r T L :=
      record_window_mem_ambFamily hL hn0 hst hhor hr hlo0 hhi hne
    have hle := ambGood_count_le hgood hmem
    -- the index identity `(R_t - 2m - (R_s+1)) + 1 = R_t - R_s - 2m`
    have hX0 : (0 : ℤ) ≤ Rt - Rs - ((2 * m : ℕ) : ℤ) - 1 := by omega
    have hA0 : Rt - ((2 * m : ℕ) : ℤ) - (Rs + 1) =
        Rt - Rs - ((2 * m : ℕ) : ℤ) - 1 := by ring
    have hnat : (Rt - Rs - ((2 * m : ℕ) : ℤ)).toNat =
        (Rt - Rs - ((2 * m : ℕ) : ℤ) - 1).toNat + 1 := by
      rw [show Rt - Rs - ((2 * m : ℕ) : ℤ) =
        (Rt - Rs - ((2 * m : ℕ) : ℤ) - 1) + 1 by ring,
        Int.toNat_add hX0 (show (0 : ℤ) ≤ 1 by norm_num)]
      norm_num
    have hidx : ((Rt - ((2 * m : ℕ) : ℤ) - (Rs + 1)).toNat + 1 : ℝ) =
        ((Rt - Rs - ((2 * m : ℕ) : ℤ)).toNat : ℝ) := by
      rw [hA0, hnat]
      push_cast
      ring
    rw [hidx] at hle
    simpa only [recWindowCount, hRs, hRt] using hle
  · -- empty window: the target lower bound is nonpositive
    have hzero : (Rt - Rs - ((2 * m : ℕ) : ℤ)).toNat = 0 := by
      have : Rt - Rs - ((2 * m : ℕ) : ℤ) ≤ 0 := by omega
      exact Int.toNat_of_nonpos this
    have hcount : (0 : ℝ) ≤ (recWindowCount p m hA U s t : ℝ) := Nat.cast_nonneg _
    have hR : (0 : ℝ) < Real.sqrt (L * Real.sqrt L) := by
      apply Real.sqrt_pos.mpr
      have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      positivity
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hzero]
    simp only [Nat.cast_zero, mul_zero, zero_sub]
    nlinarith [hcount, hR, hm0]

/-- The group record is monotone in the group. -/
lemma runMaxA_mono_group {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {hU : (Finset.univ : Finset (Fin N)).Nonempty} (n : ℕ) :
    runMaxA p m U hA n ≤ runMaxA p m U hU n := by
  refine Finset.sup'_le hA _ (fun j _ => ?_)
  exact (le_runMaxA (p := p) (m := m) (U := U) (hA := hU) (n := n)
    (Finset.mem_univ j)).trans_eq rfl

/-- A group member's position is below the group record. -/
lemma pos_le_runMaxA_pos {p : ℝ} {m : ℕ} {U : Array N} {A : Finset (Fin N)} {hA : A.Nonempty}
    {n : ℕ} {i : Fin N} (hi : i ∈ A) :
    (trajectory p m U n).pos i ≤ runMaxA p m U hA n :=
  (le_runMax (p := p) (m := m) (U := U) (j := i) (n := n)).trans (le_runMaxA hi)

/-- **The actual record window in the paper's `{d_r ≤ L}` geometry.**  Here `n₀` is the first
passage of the *global* record to the level `r` (the paper's `τ_r`), so the group record at `n₀`
is automatically at most `r`; the position hypothesis `r - L ≤ X^i_{n₀}` (`i ∈ A`) is the part of
`{d_r ≤ L}` that concerns the group, and it gives the lower level bound.  Then, exactly as in
`gamma_actual_window_count`, the random window `(R^A_s, R^A_t - 2m]` carries the count bound for
all `n₀ ≤ s ≤ t ≤ n₀ + (T+3)L`.

The remaining dynamic content is explicit: the level `r` is attained by the path, the first
passage `n₀` is a random time, and the bound is only asserted for times within `(T+3)L` of it.
Nothing is assumed about the *future* of the path. -/
theorem gamma_actual_window_count_ARMax (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) {A : Finset (Fin N)} (hA : A.Nonempty) {r : ℤ} {T L : ℕ} (hL : 1 ≤ L)
    (hr : ((T + 3) * L : ℤ) ≤ r)
    {hU : (Finset.univ : Finset (Fin N)).Nonempty} {U : Array N}
    (hgood : U ∈ ambGood p m hA r T L) {n0 s t : ℕ}
    (hAR : ARMax p m U hU r n0)
    (hpos : ∀ i ∈ A, r - (L : ℤ) ≤ (trajectory p m U n0).pos i)
    (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (T + 3) * L) :
    (1 - p) ^ ((2 * m - 1) * A.card) *
        (((runMaxA p m U hA t - runMaxA p m U hA s - ((2 * m : ℕ) : ℤ)).toNat : ℝ))
          - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L)
      ≤ (recWindowCount p m hA U s t : ℝ) := by
  have hr0 : 0 ≤ r := le_trans (by positivity) hr
  have hhi : runMaxA p m U hA n0 ≤ r := by
    refine (runMaxA_mono_group (hA := hA) (hU := hU) n0).trans_eq ?_
    exact ARMax.eq hr0 hAR
  have hlo0 : r - (L : ℤ) ≤ runMaxA p m U hA n0 := by
    obtain ⟨i, hi⟩ := hA
    exact (hpos i hi).trans (pos_le_runMaxA_pos hi)
  exact gamma_actual_window_count p hp0 hp1 m hm hA hL hr hgood hn0 hst hhor hlo0 hhi

/-- **The paper's form of the random-window count bound**: with `C = 2m(1-p)^{(2m-1)|A|} + 4m`,

`(1-p)^{(2m-1)|A|}(R^A_t - R^A_s) - C L^{3/4} ≤ #{R^A_s < y ≤ R^A_t - 2m : Γ^A_y}`,

the display on line 1290 of `main_1d_revised.tex`.  It follows from
`gamma_actual_window_count` by paying `2m` levels and using `L^{3/4} ≥ 1` for `L ≥ 1`. -/
theorem gamma_actual_window_count_paper (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) {A : Finset (Fin N)} (hA : A.Nonempty) {r : ℤ} {T L : ℕ} (hL : 1 ≤ L)
    (hr : ((T + 3) * L : ℤ) ≤ r) {U : Array N} (hgood : U ∈ ambGood p m hA r T L)
    {n0 s t : ℕ} (hn0 : n0 ≤ s) (hst : s ≤ t) (hhor : t ≤ n0 + (T + 3) * L)
    (hlo0 : r - (L : ℤ) ≤ runMaxA p m U hA n0) (hhi : runMaxA p m U hA n0 ≤ r) :
    (1 - p) ^ ((2 * m - 1) * A.card) *
        ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ)
          - (2 * (m : ℝ) * (1 - p) ^ ((2 * m - 1) * A.card) + 4 * (m : ℝ)) *
              Real.sqrt (L * Real.sqrt L)
      ≤ (recWindowCount p m hA U s t : ℝ) := by
  have hmain := gamma_actual_window_count p hp0 hp1 m hm hA hL hr hgood hn0 hst hhor hlo0 hhi
  set c : ℝ := (1 - p) ^ ((2 * m - 1) * A.card) with hc
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hc]
    have : (0 : ℝ) ≤ 1 - p := by linarith
    positivity
  -- `L^{3/4} ≥ 1`
  have hs1 : (1 : ℝ) ≤ Real.sqrt (L * Real.sqrt L) := by
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hsL1 : (1 : ℝ) ≤ Real.sqrt L := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hL1
    have h2 : (1 : ℝ) ≤ L * Real.sqrt L := by nlinarith
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (L * Real.sqrt L) := Real.sqrt_le_sqrt h2
  set X : ℤ := runMaxA p m U hA t - runMaxA p m U hA s - ((2 * m : ℕ) : ℤ) with hX
  by_cases hX0 : 0 ≤ X
  · -- `(X).toNat = X` as a real, so the `2m` levels can be paid
    have hcast : ((X.toNat : ℕ) : ℝ) = (X : ℝ) := by
      have h : ((X.toNat : ℕ) : ℤ) = X := Int.toNat_of_nonneg hX0
      exact_mod_cast h
    have hXY : (runMaxA p m U hA t - runMaxA p m U hA s : ℤ) = X + ((2 * m : ℕ) : ℤ) := by
      rw [hX]; ring
    rw [hcast] at hmain
    rw [hXY]
    push_cast
    have heq : c * ((X : ℝ) + 2 * (m : ℝ)) -
          (2 * (m : ℝ) * c + 4 * (m : ℝ)) * Real.sqrt (L * Real.sqrt L)
        = (c * (X : ℝ) - 4 * (m : ℝ) * Real.sqrt (L * Real.sqrt L))
          - 2 * (m : ℝ) * c * (Real.sqrt (L * Real.sqrt L) - 1) := by ring
    rw [heq]
    have hnn : (0 : ℝ) ≤ 2 * (m : ℝ) * c * (Real.sqrt (L * Real.sqrt L) - 1) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  · -- the window is short: the bound is trivial
    have hXneg : X ≤ 0 := by omega
    have hzero : X.toNat = 0 := Int.toNat_of_nonpos hXneg
    rw [hzero] at hmain
    simp only [Nat.cast_zero, mul_zero, zero_sub] at hmain
    have hcount : (0 : ℝ) ≤ (recWindowCount p m hA U s t : ℝ) := Nat.cast_nonneg _
    have hRs : (runMaxA p m U hA t - runMaxA p m U hA s : ℤ) ≤ ((2 * m : ℕ) : ℤ) := by
      rw [hX] at hXneg; omega
    have hz : ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) ≤ 2 * (m : ℝ) := by
      have h : ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) ≤
          (((2 * m : ℕ) : ℤ) : ℝ) := by exact_mod_cast hRs
      have h2 : (((2 * m : ℕ) : ℤ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
      linarith
    have hstep : c * ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) ≤
        (2 * (m : ℝ) * c + 4 * (m : ℝ)) * Real.sqrt (L * Real.sqrt L) := by
      have h1 : c * ((runMaxA p m U hA t - runMaxA p m U hA s : ℤ) : ℝ) ≤ c * (2 * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hz hc0
      have h4 : (0 : ℝ) ≤ 2 * (m : ℝ) * c + 4 * (m : ℝ) := by positivity
      have h5 : (2 * (m : ℝ) * c) * Real.sqrt (L * Real.sqrt L) ≤
          (2 * (m : ℝ) * c + 4 * (m : ℝ)) * Real.sqrt (L * Real.sqrt L) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h6 : (2 * (m : ℝ) * c) ≤ (2 * (m : ℝ) * c) * Real.sqrt (L * Real.sqrt L) := by
        have := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) * c)
        rwa [mul_one] at this
      have h2 : c * (2 * (m : ℝ)) = 2 * (m : ℝ) * c := by ring
      linarith
    linarith

/-! ## §8. The paper's display verbatim: per residue class, per interval, per group

The paper's display (before line 1226) is stated **per residue class** `q mod 2m`:
`∑_{a₀≤y≤b₀, y≡q} 1_{Γ_y^A} ≥ (1-p)^{(2m-1)|A|}#{y∈[a₀,b₀] : y≡q} - 2L^{3/4}`.  Section §3
above proves the *interval total* (deviation `2m·2L^{3/4}`), which is what line 1290 consumes.
For completeness we record the per-class form as well: the finite family is
`(q, [a₀,b₀])` over `q < 2m` and all ambient subintervals, of cardinality at most
`2m·(2(T+3)L+1)²`, and each member carries deviation `2L^{3/4}` with the same exponent
`(4/(2T+7))√L`.  The extra factor `2m` is again absorbed into `C_T`. -/

/-- The finite family of `(residue class, ambient subinterval)` pairs. -/
noncomputable def ambClsFamily (r : ℤ) (T L m : ℕ) : Finset (ℕ × (ℤ × ℤ)) :=
  Finset.range (2 * m) ×ˢ ambFamily r T L

lemma mem_ambClsFamily_iff {r : ℤ} {T L m : ℕ} {qj : ℕ × (ℤ × ℤ)} :
    qj ∈ ambClsFamily r T L m ↔ qj.1 < 2 * m ∧ qj.2 ∈ ambFamily r T L := by
  simp only [ambClsFamily, Finset.mem_product, Finset.mem_range]

lemma ambClsFamily_card_le (r : ℤ) (T L m : ℕ) :
    (ambClsFamily r T L m).card ≤ 2 * m * ambWidth T L ^ 2 := by
  rw [ambClsFamily, Finset.card_product, Finset.card_range]
  exact Nat.mul_le_mul_left _ (ambFamily_card_le r T L)

/-- **One class of one interval, uniformly.**  For every member `(q,[a₀,b₀])` of the ambient
family, the probability that the class count of successful trials falls below
`(1-p)^{(2m-1)|A|}·#(class) - 2L^{3/4}` is at most `exp(-(4/(2T+7))√L)`. -/
lemma gamma_ambclass_tail_uniform (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) (A : Finset (Fin N)) (hA : A.Nonempty) {r : ℤ} {T L : ℕ} (hL : 1 ≤ L)
    (hr : ((T + 3) * L : ℤ) ≤ r) {qj : ℕ × (ℤ × ℤ)} (hmem : qj ∈ ambClsFamily r T L m) :
    arrayMeasure N {U : Array N |
        ((clsCount p m hA (clsY0 qj.2.1 qj.1) (clsK qj.2.1 qj.2.2 m qj.1) U : ℕ) : ℝ)
          < (1 - p) ^ ((2 * m - 1) * A.card) * (clsK qj.2.1 qj.2.2 m qj.1 : ℝ)
            - 2 * Real.sqrt (L * Real.sqrt L)}
      ≤ ENNReal.ofReal (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L)) := by
  classical
  obtain ⟨hj, hab⟩ := mem_ambClsFamily_iff.mp hmem
  obtain ⟨hlo, hle, hhi⟩ := ambFamily_spec hab
  set cr : ℝ := (1 - p) ^ ((2 * m - 1) * A.card) with hcr
  set K : ℕ := clsK qj.2.1 qj.2.2 m qj.1 with hK
  set t : ℝ := 2 * Real.sqrt (L * Real.sqrt L) with htdef
  have ht : (0 : ℝ) ≤ t := by rw [htdef]; positivity
  by_cases hK0 : K = 0
  · -- an empty class carries no trials, so the bad event is empty
    have hempty : {U : Array N |
        ((clsCount p m hA (clsY0 qj.2.1 qj.1) K U : ℕ) : ℝ) < cr * (K : ℝ) - t} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      intro U hU
      rw [Set.mem_ofPred_eq] at hU
      rw [hK0] at hU
      simp only [Nat.cast_zero, mul_zero, zero_sub] at hU
      have h0 : (0 : ℝ) ≤ (clsCount p m hA (clsY0 qj.2.1 qj.1) 0 U : ℝ) := Nat.cast_nonneg _
      linarith
    rw [hempty]
    simp only [MeasureTheory.measure_empty]
    exact zero_le
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKpos
    -- `K ≤ K̄ ≤ (2T+7)L`
    have hKK : K ≤ clsKbar qj.2.1 qj.2.2 m := clsK_le_Kbar hm hle
    have hKL : (K : ℝ) ≤ (2 * (T : ℝ) + 7) * (L : ℝ) := by
      have h1 : (clsKbar qj.2.1 qj.2.2 m : ℝ) ≤ (ambWidth T L : ℝ) := by
        exact_mod_cast clsKbar_le_ambWidth hab
      have h2 : (ambWidth T L : ℝ) ≤ (2 * (T : ℝ) + 7) * (L : ℝ) := ambWidth_le_linear hL
      have h3 : (K : ℝ) ≤ (clsKbar qj.2.1 qj.2.2 m : ℝ) := by exact_mod_cast hKK
      linarith
    have hbase := gamma_class_tail p hp0 hp1 m hm A hA (a0 := qj.2.1) (b0 := qj.2.2)
      (ha0 := (ambLo_nonneg hr).trans hlo) (hab := hle) (t := t) ht (j := qj.1) hj
    refine hbase.trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.exp_le_exp, htdef]
    -- `t²/K ≥ (4/(2T+7))√L`
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hD : (0 : ℝ) < 2 * (T : ℝ) + 7 := by positivity
    have hKposR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
    have hsL : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hLpos
    have hsq : (2 * Real.sqrt (L * Real.sqrt L)) ^ 2 = 4 * (L : ℝ) * Real.sqrt L :=
      two_mul_pow_three_quarters_sq hLpos.le
    have hkey : 4 / (2 * (T : ℝ) + 7) * Real.sqrt L ≤
        4 * (L : ℝ) * Real.sqrt L / (K : ℝ) := by
      rw [show 4 / (2 * (T : ℝ) + 7) * Real.sqrt L =
        4 * Real.sqrt L / (2 * (T : ℝ) + 7) by ring]
      rw [div_le_div_iff₀ hD hKposR]
      have hmul : (K : ℝ) * Real.sqrt L ≤ ((2 * (T : ℝ) + 7) * (L : ℝ)) * Real.sqrt L := by
        nlinarith [hKL, hsL.le]
      nlinarith [hmul]
    rw [hsq]
    linarith

/-- **The paper's per-class display, simultaneously over all groups, classes and intervals.**
Outside one event, for every nonempty proper `A`, every `q < 2m` and every integer subinterval
`[a₀,b₀]` of the deterministic ambient window, the number of successful trials `Γ^A_y` with
`y ∈ [a₀,b₀]`, `y ≡ a₀+q (mod 2m)` is at least

`(1-p)^{(2m-1)|A|}·#{y ∈ [a₀,b₀] : y ≡ a₀+q} - 2L^{3/4}`.

The event has measure at most `2^N·(2(T+3)L+1)²·2m·exp(-(4/(2T+7))√L)` — the same profile as
§3, since the `2m` classes and the `2m` cardinality factor are the same corner of the estimate. -/
theorem gamma_ambient_class_display (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) {r : ℤ} {T L : ℕ} (hL : 1 ≤ L) (hr : ((T + 3) * L : ℤ) ≤ r) :
    arrayMeasure N (⋃ A ∈ (properGroups (N := N)).attach,
        ⋃ qj ∈ ambClsFamily r T L m, {U : Array N |
          ((clsCount p m (mem_properGroups.mp A.2).1 (clsY0 qj.2.1 qj.1)
              (clsK qj.2.1 qj.2.2 m qj.1) U : ℕ) : ℝ)
            < (1 - p) ^ ((2 * m - 1) * A.1.card) * (clsK qj.2.1 qj.2.2 m qj.1 : ℝ)
              - 2 * Real.sqrt (L * Real.sqrt L)})
      ≤ (2 ^ N : ℕ) * (((ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) * ((2 * m : ℕ) * ENNReal.ofReal
          (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L)))) := by
  classical
  have hreorder : ((2 * m * ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) =
      ((ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) * ((2 * m : ℕ) : ℝ≥0∞) := by
    push_cast
    ring
  have hper : ∀ A ∈ (properGroups (N := N)).attach,
      arrayMeasure N (⋃ qj ∈ ambClsFamily r T L m, {U : Array N |
          ((clsCount p m (mem_properGroups.mp A.2).1 (clsY0 qj.2.1 qj.1)
              (clsK qj.2.1 qj.2.2 m qj.1) U : ℕ) : ℝ)
            < (1 - p) ^ ((2 * m - 1) * A.1.card) * (clsK qj.2.1 qj.2.2 m qj.1 : ℝ)
              - 2 * Real.sqrt (L * Real.sqrt L)})
        ≤ ((ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) * ((2 * m : ℕ) * ENNReal.ofReal
            (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L))) := by
    intro A _
    refine (measure_biUnion_finset_le (ambClsFamily r T L m) _).trans ?_
    refine (Finset.sum_le_sum fun qj hqj =>
      gamma_ambclass_tail_uniform p hp0 hp1 m hm A.1 (mem_properGroups.mp A.2).1 hL hr hqj).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((ambClsFamily r T L m).card : ℝ≥0∞) ≤ ((2 * m * ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast ambClsFamily_card_le r T L m
    calc ((ambClsFamily r T L m).card : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L))
        ≤ ((2 * m * ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal
            (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L)) := mul_le_mul_left hcard _
      _ = ((ambWidth T L ^ 2 : ℕ) : ℝ≥0∞) * ((2 * m : ℕ) * ENNReal.ofReal
            (Real.exp (-(4 / (2 * (T : ℝ) + 7)) * Real.sqrt L))) := by
            rw [hreorder, mul_assoc]
  refine (measure_biUnion_finset_le (properGroups (N := N)).attach _).trans ?_
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_attach]
  refine mul_le_mul_left ?_ _
  exact_mod_cast card_properGroups_le N

/-- **The per-class display with the constants absorbed**: the same explicit `C_T`, `c_T` as §5,
`P(·) ≤ C_T e^{-c_T √L}`. -/
theorem gamma_ambient_class_display_absorbed (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) {r : ℤ} {T L : ℕ} (hL : 1 ≤ L) (hr : ((T + 3) * L : ℤ) ≤ r) :
    arrayMeasure N (⋃ A ∈ (properGroups (N := N)).attach,
        ⋃ qj ∈ ambClsFamily r T L m, {U : Array N |
          ((clsCount p m (mem_properGroups.mp A.2).1 (clsY0 qj.2.1 qj.1)
              (clsK qj.2.1 qj.2.2 m qj.1) U : ℕ) : ℝ)
            < (1 - p) ^ ((2 * m - 1) * A.1.card) * (clsK qj.2.1 qj.2.2 m qj.1 : ℝ)
              - 2 * Real.sqrt (L * Real.sqrt L)})
      ≤ ENNReal.ofReal (ambConst N m T * Real.exp
          (-(2 / (2 * (T : ℝ) + 7)) * Real.sqrt L)) :=
  (gamma_ambient_class_display p hp0 hp1 m hm hL hr).trans (amb_profile_absorb N m T hL)
