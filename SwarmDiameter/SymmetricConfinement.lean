import Swarm.Reflect.Basic

open Finset SwarmReflect
open scoped Classical

namespace Swarming.Diameter

private abbrev staysIn (L : ℕ) {n : ℕ} (ω : Fin n → Bool) : Prop :=
  ∀ k ≤ n, |psum ω k| ≤ (L : ℤ)

private noncomputable def weight (L : ℕ) (z : ℤ) : ℝ :=
  (((L : ℝ) + 1) ^ 2 - (z : ℝ) ^ 2) ^ 2

private noncomputable def confinedWeight (L : ℕ) {n : ℕ} (ω : Fin n → Bool) : ℝ :=
  if staysIn L ω then weight L (psum ω n) else 0

private theorem psum_snoc {n : ℕ} (ω : Fin n → Bool) (b : Bool) {k : ℕ} (hk : k ≤ n) :
    psum (Fin.snoc ω b) k = psum ω k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [psum_succ_of_lt _ (by omega : k < n + 1), psum_succ_of_lt _ (by omega : k < n),
      ih (by omega : k ≤ n)]
    exact congrArg (psum ω k + step ·) (Fin.snoc_castSucc (α := fun _ => Bool)
      (p := ω) (x := b) (i := ⟨k, by omega⟩))

private theorem psum_snoc_end {n : ℕ} (ω : Fin n → Bool) (b : Bool) :
    psum (Fin.snoc ω b) (n + 1) = psum ω n + step b := by
  rw [psum_succ_of_lt _ (Nat.lt_succ_self n), psum_snoc ω b le_rfl]
  change _ + step (Fin.snoc (α := fun _ => Bool) ω b (Fin.last n)) = _
  rw [Fin.snoc_last]

private theorem staysIn_snoc {n L : ℕ} (ω : Fin n → Bool) (b : Bool) :
    staysIn L (Fin.snoc ω b) ↔ staysIn L ω ∧ |psum ω n + step b| ≤ (L : ℤ) := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · rw [← psum_snoc ω b hk]
      exact h k (by omega)
    · rw [← psum_snoc_end]
      exact h _ le_rfl
  · rintro ⟨h, hlast⟩ k hk
    by_cases hk' : k ≤ n
    · rw [psum_snoc ω b hk']
      exact h k hk'
    · obtain rfl : k = n + 1 := by omega
      rwa [psum_snoc_end]

private theorem weight_eq_zero_of_step_out {L : ℕ} {z : ℤ} (b : Bool)
    (hz : |z| ≤ (L : ℤ)) (hout : ¬ |z + step b| ≤ (L : ℤ)) :
    weight L (z + step b) = 0 := by
  have hstep : |step b| = 1 := by
    cases b <;> simp
  have h := (abs_add_le z (step b)).trans (add_le_add hz hstep.le)
  have he : |z + step b| = (L : ℤ) + 1 := by omega
  have he' : |((z + step b : ℤ) : ℝ)| = (L : ℝ) + 1 := by exact_mod_cast he
  unfold weight
  rw [← sq_abs ((z + step b : ℤ) : ℝ), he', sub_self, zero_pow (by decide : 2 ≠ 0)]

private theorem confinedWeight_snoc {n L : ℕ} (ω : Fin n → Bool) (b : Bool) :
    confinedWeight L (Fin.snoc ω b) =
      if staysIn L ω then weight L (psum ω n + step b) else 0 := by
  have he := staysIn_snoc (L := L) ω b
  by_cases h : staysIn L ω
  · rw [if_pos h]
    by_cases hb : |psum ω n + step b| ≤ (L : ℤ)
    · rw [confinedWeight, if_pos (he.mpr ⟨h, hb⟩), psum_snoc_end]
    · rw [confinedWeight, if_neg (fun hh => hb (he.mp hh).2),
        weight_eq_zero_of_step_out b (h n le_rfl) hb]
  · rw [confinedWeight, if_neg (fun hh => h (he.mp hh).1), if_neg h]

private theorem weight_step_le (L : ℕ) (z : ℤ) :
    (2 * (1 - 2 / ((L : ℝ) + 1) ^ 2)) * weight L z ≤
      weight L (z + 1) + weight L (z - 1) := by
  let a : ℝ := ((L : ℝ) + 1) ^ 2
  have ha : 0 < a := by positivity
  apply (mul_le_mul_iff_of_pos_left ha).mp
  have h :
      a * (weight L (z + 1) + weight L (z - 1)) -
          (2 * (a - 2)) * weight L z =
        2 * a + 4 * a * (z : ℝ) ^ 2 + 4 * (z : ℝ) ^ 4 := by
    dsimp only [weight, a]
    push_cast
    ring
  calc
    a * ((2 * (1 - 2 / a)) * weight L z) = (2 * (a - 2)) * weight L z := by
      field_simp
    _ ≤ _ := sub_nonneg.mp (h ▸ (by positivity : 0 ≤ 2 * a + 4 * a * (z : ℝ) ^ 2 +
      4 * (z : ℝ) ^ 4))

private theorem sum_snoc {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ ω, f ω) = ∑ ω : Fin n → Bool, (f (Fin.snoc ω true) + f (Fin.snoc ω false)) := by
  let e := (Equiv.prodComm (Fin n → Bool) Bool).trans (Fin.snocEquiv (fun _ => Bool))
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  exact Fintype.sum_bool _

private theorem sum_confinedWeight_ge {L : ℕ} (hL : 1 ≤ L) (n : ℕ) :
    (2 * (1 - 2 / ((L : ℝ) + 1) ^ 2)) ^ n * weight L 0 ≤
      ∑ ω : Fin n → Bool, confinedWeight L ω := by
  let a := ((L : ℝ) + 1) ^ 2
  let q := 1 - 2 / a
  have ha : 0 < a := by positivity
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have ha' : 4 ≤ a := by
    dsimp only [a]
    nlinarith
  have hq : 0 ≤ q := sub_nonneg.mpr ((div_le_one₀ ha).mpr (by linarith))
  change (2 * q) ^ n * weight L 0 ≤ _
  induction n with
  | zero =>
    have h (ω : Fin 0 → Bool) : confinedWeight L ω = weight L 0 := by
      rw [confinedWeight, if_pos]
      · simp
      · intro k hk
        obtain rfl : k = 0 := by omega
        simp
    simp only [pow_zero, one_mul, h, sum_const, card_univ]
    simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, sum_snoc]
    calc
      _ ≤ (2 * q) * (∑ ω : Fin n → Bool, confinedWeight L ω) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg (by norm_num) hq)
      _ = ∑ ω : Fin n → Bool, (2 * q) * confinedWeight L ω := Finset.mul_sum _ _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro ω _
        rw [confinedWeight_snoc, confinedWeight_snoc, confinedWeight]
        by_cases h : staysIn L ω
        · simpa only [if_pos h, step_true, step_false, sub_eq_add_neg, q, a] using
            weight_step_le L (psum ω n)
        · simp only [if_neg h, mul_zero, add_zero, le_refl]

private theorem confinedWeight_le {L n : ℕ} (ω : Fin n → Bool) :
    confinedWeight L ω ≤ if staysIn L ω then weight L 0 else 0 := by
  rw [confinedWeight]
  split_ifs with h
  · have hz : |(psum ω n : ℝ)| ≤ (L : ℝ) := by exact_mod_cast h n le_rfl
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have hs : (psum ω n : ℝ) ^ 2 ≤ ((L : ℝ) + 1) ^ 2 := by
      rw [← sq_abs (psum ω n : ℝ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hz.trans (by linarith)) _
    simp only [weight, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
    exact pow_le_pow_left₀ (sub_nonneg.mpr hs) (sub_le_self _ (sq_nonneg _)) _
  · exact le_rfl

/-- The number of symmetric walk paths of length `L³` that stay in `[-L,L]`. -/
theorem exp_neg_le_card_symmetric_confinement {L : ℕ} (hL : 1 ≤ L) :
    let n := L ^ 3
    Real.exp (-4 * (L : ℝ)) * (2 : ℝ) ^ n ≤
      ((univ.filter fun ω : Fin n → Bool => ∀ k ≤ n, |psum ω k| ≤ (L : ℤ)).card : ℝ) := by
  let n := L ^ 3
  let a := ((L : ℝ) + 1) ^ 2
  let q := 1 - 2 / a
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have ha : 0 < a := by positivity
  have ha' : 4 ≤ a := by dsimp only [a]; nlinarith
  have hq : (1 / 2 : ℝ) ≤ q := by
    dsimp only [q]
    have h := (div_le_iff₀ ha).mpr (show (2 : ℝ) ≤ 1 / 2 * a by linarith)
    linarith
  have hq₀ : 0 < q := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hq
  have hinv : q⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hq₀).mpr (by linarith)
  have hlog : -(4 / a) ≤ Real.log q := by
    have he : q⁻¹ - 1 = (2 / a) * q⁻¹ := by
      calc
        _ = (1 - q) * q⁻¹ := by rw [sub_mul, one_mul, mul_inv_cancel₀ hq₀.ne']
        _ = _ := by dsimp only [q]; ring
    have h := Real.one_sub_inv_le_log_of_pos hq₀
    have hb := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 2 / a by positivity)
    rw [show 2 / a * 2 = 4 / a by ring] at hb
    linarith
  have hn : (n : ℝ) ≤ (L : ℝ) * a := by
    dsimp only [n, a]
    push_cast
    nlinarith [sq_nonneg (L : ℝ)]
  have hpow : Real.exp (-4 * (L : ℝ)) ≤ q ^ n := by
    rw [← Real.exp_log (pow_pos hq₀ n), Real.log_pow]
    apply Real.exp_le_exp.mpr
    calc
      _ = -(4 / a) * ((L : ℝ) * a) := by field_simp
      _ ≤ -(4 / a) * (n : ℝ) :=
        mul_le_mul_of_nonpos_left hn (neg_nonpos.mpr (by positivity))
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) n)
  let C := (univ.filter fun ω : Fin n → Bool => staysIn L ω).card
  change Real.exp (-4 * (L : ℝ)) * (2 : ℝ) ^ n ≤ (C : ℝ)
  have hw : 0 < weight L 0 := by
    simp only [weight, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
    positivity
  have hc : (2 * q) ^ n ≤ (C : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hw).mp
    calc
      _ ≤ ∑ ω : Fin n → Bool, confinedWeight L ω := sum_confinedWeight_ge hL n
      _ ≤ ∑ ω : Fin n → Bool, if staysIn L ω then weight L 0 else 0 :=
        Finset.sum_le_sum (fun ω _ => confinedWeight_le ω)
      _ = (C : ℝ) * weight L 0 := by
        rw [← Finset.sum_filter]
        simp [C]
  calc
    _ ≤ q ^ n * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (2 * q) ^ n := by rw [mul_pow, mul_comm]
    _ ≤ _ := hc

end Swarming.Diameter
