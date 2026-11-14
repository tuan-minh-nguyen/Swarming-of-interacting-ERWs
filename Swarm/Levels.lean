/-
  The paper's concrete level sequences `b_k = floor(k^{1/4}) - 1` and `a_k = floor(b_k/2)`
  from the proof of Lemma `transience` (main_1d_revised.tex, §2.2), with the
  arithmetic facts the pathwise argument of `DeepReturn.lean` consumes:

    a_k <= b_k,   b_k < k,   a_k -> infinity,   b_k -> infinity.

  `floor(k^{1/4})` is written `Nat.sqrt (Nat.sqrt k)`.
-/
import Swarm.Imports
import Swarm.DeepReturn

open Filter

namespace SwarmSpeed

/-- `b_k = floor(k^{1/4}) - 1`, the paper's level. -/
def lvlB (k : ℕ) : ℕ := Nat.sqrt (Nat.sqrt k) - 1

/-- `a_k = floor(b_k/2)`, the paper's lower level. -/
def lvlA (k : ℕ) : ℕ := lvlB k / 2

lemma lvlA_le_lvlB (k : ℕ) : lvlA k ≤ lvlB k := Nat.div_le_self _ _

lemma lvlB_lt_self {k : ℕ} (hk : 2 ≤ k) : lvlB k < k := by
  have h1 : Nat.sqrt k < k := Nat.sqrt_lt_self (by omega)
  have h2 : Nat.sqrt (Nat.sqrt k) ≤ Nat.sqrt k := Nat.sqrt_le_self _
  unfold lvlB
  omega

lemma lvlB_mono : Monotone lvlB := by
  intro a b hab
  unfold lvlB
  exact Nat.sub_le_sub_right (Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hab)) 1

lemma lvlA_mono : Monotone lvlA := fun _ _ hab => Nat.div_le_div_right (lvlB_mono hab)

/-- `b_k` tends to infinity in `k`. -/
lemma tendsto_lvlB : Tendsto lvlB atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  -- `k = (B+2)^4` forces `sqrt (sqrt k) >= B + 2`
  refine ⟨(B + 2) ^ 4, fun k hk => ?_⟩
  have h1 : Nat.sqrt (Nat.sqrt ((B + 2) ^ 4)) ≤ Nat.sqrt (Nat.sqrt k) :=
    Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk)
  have h2 : Nat.sqrt (Nat.sqrt ((B + 2) ^ 4)) = B + 2 := by
    rw [show (B + 2) ^ 4 = ((B + 2) ^ 2) ^ 2 by ring]
    rw [Nat.sqrt_eq', Nat.sqrt_eq']
  unfold lvlB
  omega

lemma tendsto_lvlA : Tendsto lvlA atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro A
  obtain ⟨B, hB⟩ := (tendsto_atTop_atTop.mp tendsto_lvlB) (2 * A + 1)
  refine ⟨B, fun k hk => ?_⟩
  have h1 : 2 * A + 1 ≤ lvlB k := hB k hk
  unfold lvlA
  omega

/-- **Lemma `transience` with the paper's concrete levels**: given nearest-neighbour
motion from `0`, that every level is visited, that above some level `K` there is no bad time
`<= (k+1)^4`, that level `k+1` is reached before `(k+1)^4`, and that the other walker's
running maximum dominates `s^{1/4}` (i.e. exceeds `b_k` on `[k, (k+1)^4]`), the walker is
transient to `+infinity`. -/
theorem transience_of_paper_levels (u v : ℕ → ℤ) (hu : UnitSteps u) (hu0 : u 0 = 0)
    (h : ∀ z, ∃ n, u n = z) {K : ℕ}
    (hK : 2 ≤ K)
    (hbad : ∀ k ≥ K, ∀ s ≤ (k + 1) ^ 4, ¬ (u s = (lvlB k : ℤ) ∧ (lvlB k : ℤ) + 1 ≤ runMax v s ∧
      hitBefore u s ((lvlB k : ℤ) + 1) (lvlA k)))
    (hτk : ∀ k ≥ K, firstHit u h ((k : ℤ) + 1) ≤ (k + 1) ^ 4)
    (hMv : ∀ k ≥ K, ∀ s, k ≤ s → s ≤ (k + 1) ^ 4 → (lvlB k : ℤ) + 1 ≤ runMax v s) :
    Tendsto u atTop atTop :=
  tendsto_atTop_of_no_deep_returns hu hu0 h (K := K) (b := lvlB) (a := lvlA)
    (fun k _ => lvlA_le_lvlB k) (fun k hk => lvlB_lt_self (le_trans hK hk))
    lvlA_mono tendsto_lvlA hbad hτk hMv

end SwarmSpeed
