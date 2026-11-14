/-
  The paper's running-maximum estimate `M^i_n >= n^{1/4}` for the actual interacting
  trajectory (`main_1d_revised.tex`, proof of Lemma `transience`, first display):

    `sum_{r>=1} P(M^i_{2^r} < ceil(2^{r/3})) <= C sum_r 2^{-r/6} < infinity`

  followed by Borel--Cantelli and a block covering.  We use the equivalent (and, for
  Lean, cleaner) block grid `n_j = (j+1)^8` with threshold `(j+2)^2`; the reflection
  estimate gives the summable bound `12*sqrt 2/(j+1)^2`.  For `(j+1)^8 <= n < (j+2)^8`
  one has `(j+2)^2 >= n^{1/4}`, hence almost surely

    `sqrt (sqrt n) = floor(n^{1/4}) <= M^i_n`  eventually in `n`.

  Everything here is unconditional for `p >= 1/2`: the only probabilistic input is
  `Swarming.Actual.nonhit_le_sqrt`, i.e. the reflection bound already transported to the
  actual interacting trajectory.  No independence of adaptive increments is used.
-/
import Swarm.ActualBounds
import Swarm.Speed

open MeasureTheory Filter
open Swarming Swarming.Uniform Swarming.Trajectory
open scoped ENNReal BigOperators

namespace SwarmRate

variable {N : ℕ}

/-! ### The elementary estimate on one block -/

/-- Arithmetic core of the block estimate: at horizon `(j+1)^8` and level `(j+2)^2` the
reflection bound `(2b+1)√2/√(n+1)` is at most `12√2/(j+1)^2`, which is summable in `j`. -/
theorem block_arith (j : ℕ) :
    (2 * ((((j + 2) ^ 2 : ℕ)) : ℝ) + 1) * Real.sqrt 2
        / Real.sqrt ((((j + 1) ^ 8 : ℕ) : ℝ) + 1)
      ≤ 12 * Real.sqrt 2 * (1 / ((j : ℝ) + 1) ^ 2) := by
  set r : ℝ := (j : ℝ) + 1 with hr
  have hr1 : (1 : ℝ) ≤ r := by
    rw [hr]
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hsqrt2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hcast1 : ((((j + 1) ^ 8 : ℕ)) : ℝ) = r ^ 8 := by
    rw [hr]; push_cast; ring
  have hcast2 : ((((j + 2) ^ 2 : ℕ)) : ℝ) = (r + 1) ^ 2 := by
    rw [hr]; push_cast; ring
  rw [hcast1, hcast2]
  have hden : r ^ 4 ≤ Real.sqrt (r ^ 8 + 1) := by
    apply Real.le_sqrt_of_sq_le
    have h : (r ^ 4) ^ 2 = r ^ 8 := by ring
    rw [h]
    linarith
  have hdenpos : (0 : ℝ) < Real.sqrt (r ^ 8 + 1) := Real.sqrt_pos.2 (by positivity)
  have hr4pos : (0 : ℝ) < r ^ 4 := by positivity
  have hnum : 2 * (r + 1) ^ 2 + 1 ≤ 12 * r ^ 2 := by nlinarith [hr1]
  have hstep : (2 * (r + 1) ^ 2 + 1) * Real.sqrt 2 / Real.sqrt (r ^ 8 + 1)
      ≤ (12 * r ^ 2) * Real.sqrt 2 / r ^ 4 :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hnum hsqrt2) hr4pos hden
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-! ### Arithmetic of `floor(n^{1/8})` -/

/-- `r = floor(n^{1/8})` satisfies `r^8 <= n`. -/
theorem pow_eight_le (n : ℕ) : (Nat.sqrt (Nat.sqrt (Nat.sqrt n))) ^ 8 ≤ n := by
  set a := Nat.sqrt n with ha
  set b := Nat.sqrt a with hb
  set r := Nat.sqrt b with hrr
  have h1 : r ^ 2 ≤ b := Nat.sqrt_le' b
  have h2 : b ^ 2 ≤ a := Nat.sqrt_le' a
  have h3 : a ^ 2 ≤ n := Nat.sqrt_le' n
  have h4 : (r ^ 2) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left h1 2
  have h5 : ((r ^ 2) ^ 2) ^ 2 ≤ (b ^ 2) ^ 2 := Nat.pow_le_pow_left h4 2
  have h6 : (b ^ 2) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left h2 2
  have h7 : ((r ^ 2) ^ 2) ^ 2 = r ^ 8 := by ring
  omega

/-- `r = floor(n^{1/8})` satisfies `n < (r+1)^8`. -/
theorem lt_succ_pow_eight (n : ℕ) : n < (Nat.sqrt (Nat.sqrt (Nat.sqrt n)) + 1) ^ 8 := by
  set a := Nat.sqrt n with ha
  set b := Nat.sqrt a with hb
  set r := Nat.sqrt b with hrr
  have h1 : n < (a + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have h2 : a < (b + 1) ^ 2 := Nat.lt_succ_sqrt' a
  have h3 : b < (r + 1) ^ 2 := Nat.lt_succ_sqrt' b
  have h6 : (b + 1) ^ 2 ≤ ((r + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h3 2
  have h7 : a + 1 ≤ ((r + 1) ^ 2) ^ 2 := le_trans h2 h6
  have h8 : (a + 1) ^ 2 ≤ (((r + 1) ^ 2) ^ 2) ^ 2 := Nat.pow_le_pow_left h7 2
  have h9 : (((r + 1) ^ 2) ^ 2) ^ 2 = (r + 1) ^ 8 := by ring
  omega

/-- For `n >= (J+1)^8` the index `floor(n^{1/8})` is at least `J`. -/
theorem le_of_pow_eight_le {n J : ℕ} (h : (J + 1) ^ 8 ≤ n) :
    J ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt n)) := by
  set a := Nat.sqrt n with ha
  set b := Nat.sqrt a with hb
  have h1 : (J + 1) ^ 4 ≤ a := by
    rw [ha, Nat.le_sqrt]
    have he : (J + 1) ^ 4 * (J + 1) ^ 4 = (J + 1) ^ 8 := by ring
    rw [he]
    exact h
  have h2 : (J + 1) ^ 2 ≤ b := by
    rw [hb, Nat.le_sqrt]
    have he : (J + 1) ^ 2 * (J + 1) ^ 2 = (J + 1) ^ 4 := by ring
    rw [he]
    exact h1
  have h3 : J + 1 ≤ b.sqrt := by
    rw [Nat.le_sqrt]
    have he : (J + 1) * (J + 1) = (J + 1) ^ 2 := by ring
    rw [he]
    exact h2
  omega

/-- `floor(n^{1/4})` is at most `(j+2)^2` when `n < (j+2)^8`. -/
theorem sqrt_sqrt_le_of_lt_pow_eight {n j : ℕ} (h : n < (j + 2) ^ 8) :
    Nat.sqrt (Nat.sqrt n) ≤ (j + 2) ^ 2 := by
  have h1 : Nat.sqrt n < (j + 2) ^ 4 := by
    rw [Nat.sqrt_lt]
    have he : (j + 2) ^ 4 * (j + 2) ^ 4 = (j + 2) ^ 8 := by ring
    rw [he]
    exact h
  have h2 : Nat.sqrt (Nat.sqrt n) ≤ Nat.sqrt ((j + 2) ^ 4) :=
    Nat.sqrt_le_sqrt (le_of_lt h1)
  have h3 : Nat.sqrt ((j + 2) ^ 4) = (j + 2) ^ 2 := by
    rw [show (j + 2) ^ 4 = ((j + 2) ^ 2) ^ 2 by ring, Nat.sqrt_eq']
  rw [h3] at h2
  exact h2

/-! ### The block estimate for the actual trajectory -/

/-- **One block of the running-maximum estimate.**  The actual interacting walker `i` fails
to reach level `(j+2)^2` by time `(j+1)^8` with probability at most `12√2/(j+1)^2`. -/
theorem block_reach (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) (j : ℕ) :
    (arrayMeasure N) {U : Array N |
        ∀ k ≤ (j + 1) ^ 8, (trajectory p m U k).pos i < (((j + 2) ^ 2 : ℕ) : ℤ)}
      ≤ ENNReal.ofReal (12 * Real.sqrt 2 * (1 / ((j : ℝ) + 1) ^ 2)) := by
  have hb : 1 ≤ (j + 2) ^ 2 := by
    have h0 : 1 ≤ j + 2 := Nat.succ_le_succ (Nat.zero_le _)
    calc 1 = 1 ^ 2 := by norm_num
      _ ≤ (j + 2) ^ 2 := Nat.pow_le_pow_left h0 2
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (block_arith j))
  rw [← ENNReal.ofReal_toReal (measure_ne_top (arrayMeasure N) _)]
  exact ENNReal.ofReal_le_ofReal
    (Swarming.Actual.nonhit_le_sqrt (N := N) hp m i ((j + 1) ^ 8) hb)

/-! ### Borel--Cantelli over the blocks -/

/-- **Almost sure reach of every block level.**  Almost surely, for all large `j`, the
actual interacting walker `i` reaches level `(j+2)^2` by time `(j+1)^8`. -/
theorem ae_exists_reach (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ j : ℕ in atTop,
      ∃ k ≤ (j + 1) ^ 8, (((j + 2) ^ 2 : ℕ) : ℤ) ≤ (trajectory p m U k).pos i := by
  classical
  have hshift : Summable (fun j : ℕ => 12 * Real.sqrt 2 * (1 / ((j : ℝ) + 1) ^ 2)) := by
    have hsq : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
      (Real.summable_one_div_nat_pow).mpr (by norm_num : 1 < 2)
    have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) 1).mpr hsq
    have h' : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
      simpa using h
    simpa [mul_assoc] using h'.mul_left (12 * Real.sqrt 2)
  have htsum : ∑' j : ℕ, (arrayMeasure N) {U : Array N |
      ∀ k ≤ (j + 1) ^ 8, (trajectory p m U k).pos i < (((j + 2) ^ 2 : ℕ) : ℤ)} ≠ ⊤ := by
    have hle := ENNReal.tsum_le_tsum (fun j => block_reach (N := N) hp m i j)
    have hof : ENNReal.ofReal (∑' j : ℕ, 12 * Real.sqrt 2 * (1 / ((j : ℝ) + 1) ^ 2))
        = ∑' j : ℕ, ENNReal.ofReal (12 * Real.sqrt 2 * (1 / ((j : ℝ) + 1) ^ 2)) :=
      ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hshift
    rw [← hof] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hae := MeasureTheory.ae_eventually_notMem htsum
  filter_upwards [hae] with U hU
  filter_upwards [hU] with j hj
  simp only [not_forall, not_lt] at hj
  exact ⟨hj.choose, hj.choose_spec.1, hj.choose_spec.2⟩

/-- **The paper's running-maximum estimate, unconditionally.**  Almost surely
`floor(n^{1/4}) <= M^i_n` for all large `n`, where `M^i_n` is the running maximum of the
actual interacting trajectory. -/
theorem ae_eventually_sqrt_sqrt_le_runMax (hp : 1 / 2 ≤ p) (m : ℕ) (i : Fin N) :
    ∀ᵐ U ∂(arrayMeasure N), ∀ᶠ n : ℕ in atTop,
      Nat.sqrt (Nat.sqrt n) ≤ SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n := by
  classical
  filter_upwards [ae_exists_reach (N := N) hp m i] with U hU
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hU
  refine eventually_atTop.2 ⟨(J + 2) ^ 8, fun n hn => ?_⟩
  set r : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt n)) with hrdef
  have hrJ : J + 1 ≤ r := le_of_pow_eight_le (J := J + 1) hn
  have hr1 : 1 ≤ r := le_trans (Nat.succ_le_succ (Nat.zero_le _)) hrJ
  have hjr : r - 1 + 1 = r := by omega
  have hjr2 : r - 1 + 2 = r + 1 := by omega
  have hjj : J ≤ r - 1 := by omega
  obtain ⟨k, hk1, hk2⟩ := hJ (r - 1) hjj
  rw [hjr] at hk1
  rw [hjr2] at hk2
  have hk_le : k ≤ n := le_trans hk1 (pow_eight_le n)
  have hstep : (((r + 1) ^ 2 : ℕ) : ℤ) ≤
      SwarmSpeed.runMax (fun t => (trajectory p m U t).pos i) n := by
    have hle := SwarmSpeed.le_runMax (u := fun t => (trajectory p m U t).pos i) hk_le
    exact le_trans hk2 hle
  have hlt : n < (r - 1 + 2) ^ 8 := by
    rw [show r - 1 + 2 = r + 1 by omega]
    rw [hrdef]
    exact lt_succ_pow_eight n
  have hhalf : Nat.sqrt (Nat.sqrt n) ≤ (r + 1) ^ 2 := by
    have h := sqrt_sqrt_le_of_lt_pow_eight (j := r - 1) hlt
    rwa [show r - 1 + 2 = r + 1 by omega] at h
  have := Int.ofNat_le.mpr hhalf
  linarith

/-! ### Axiom audit -/


end SwarmRate
