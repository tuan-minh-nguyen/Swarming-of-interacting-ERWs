import Swarm.Imports

open Finset

namespace SwarmReflect

/-- The step contributed by one coordinate. -/
def step (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem step_true : step true = 1 := rfl

@[simp] theorem step_false : step false = -1 := rfl

theorem step_flip (b : Bool) : step (!b) = -step b := by
  cases b <;> simp [step]

theorem step_eq (b : Bool) : step b = 1 ∨ step b = -1 := by
  cases b <;> simp

/-- The `k`-th partial sum of the walk. -/
def psum {n : ℕ} (ω : Fin n → Bool) : ℕ → ℤ
  | 0 => 0
  | (k + 1) => psum ω k + if h : k < n then step (ω ⟨k, h⟩) else 0

@[simp] theorem psum_zero {n : ℕ} (ω : Fin n → Bool) : psum ω 0 = 0 := rfl

theorem psum_succ {n : ℕ} (ω : Fin n → Bool) (k : ℕ) :
    psum ω (k + 1) = psum ω k + if h : k < n then step (ω ⟨k, h⟩) else 0 := by
  rw [psum]

theorem psum_succ_of_lt {n : ℕ} (ω : Fin n → Bool) {k : ℕ} (h : k < n) :
    psum ω (k + 1) = psum ω k + step (ω ⟨k, h⟩) := by
  rw [psum_succ, dif_pos h]

theorem psum_sub_succ {n : ℕ} (ω : Fin n → Bool) {k : ℕ} (h : k < n) :
    psum ω (k + 1) = psum ω k + 1 ∨ psum ω (k + 1) = psum ω k - 1 := by
  rw [psum_succ_of_lt ω h]
  rcases step_eq (ω ⟨k, h⟩) with hs | hs <;> rw [hs] <;> [left; right] <;> ring

def negate {n : ℕ} (ω : Fin n → Bool) : Fin n → Bool := fun i => !(ω i)

theorem negate_negate {n : ℕ} (ω : Fin n → Bool) : negate (negate ω) = ω := by
  funext i; simp [negate]

theorem psum_negate {n : ℕ} (ω : Fin n → Bool) (k : ℕ) :
    psum (negate ω) k = -psum ω k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hneg : ∀ (h : k < n), negate ω ⟨k, h⟩ = !(ω ⟨k, h⟩) := fun _ => rfl
    rw [psum_succ, psum_succ, ih]
    by_cases h : k < n
    · rw [dif_pos h, dif_pos h, hneg h, step_flip]; ring
    · rw [dif_neg h, dif_neg h]; ring

/-! ## The running maximum -/

def rmax {n : ℕ} (ω : Fin n → Bool) : ℕ → ℤ
  | 0 => psum ω 0
  | (k + 1) => max (rmax ω k) (psum ω (k + 1))

@[simp] theorem rmax_zero {n : ℕ} (ω : Fin n → Bool) : rmax ω 0 = 0 := by
  simp [rmax]

theorem rmax_succ {n : ℕ} (ω : Fin n → Bool) (k : ℕ) :
    rmax ω (k + 1) = max (rmax ω k) (psum ω (k + 1)) := by
  rw [rmax]

theorem psum_le_rmax {n : ℕ} (ω : Fin n → Bool) (k : ℕ) : psum ω k ≤ rmax ω k := by
  induction k with
  | zero => simp
  | succ k _ => rw [rmax_succ]; exact le_max_right _ _

theorem rmax_le_succ {n : ℕ} (ω : Fin n → Bool) (k : ℕ) : rmax ω k ≤ rmax ω (k + 1) := by
  rw [rmax_succ]; exact le_max_left _ _

theorem rmax_mono {n : ℕ} (ω : Fin n → Bool) {j k : ℕ} (h : j ≤ k) : rmax ω j ≤ rmax ω k := by
  induction k with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · have hjk : j ≤ k := by omega
      exact le_trans (ih hjk) (rmax_le_succ ω k)
    · have hjk : j = k + 1 := by omega
      subst hjk; exact le_refl _

theorem le_rmax_of_psum {n : ℕ} (ω : Fin n → Bool) {j : ℕ} {b : ℤ} (hj : j ≤ n)
    (h : b ≤ psum ω j) : b ≤ rmax ω n := by
  calc b ≤ psum ω j := h
    _ ≤ rmax ω j := psum_le_rmax ω j
    _ ≤ rmax ω n := rmax_mono ω hj

theorem exists_le_psum_of_le_rmax {n : ℕ} (ω : Fin n → Bool) {b : ℤ} :
    ∀ k ≤ n, b ≤ rmax ω k → ∃ j ≤ k, b ≤ psum ω j := by
  intro k
  induction k with
  | zero =>
    intro _ h
    exact ⟨0, le_rfl, by simpa using h⟩
  | succ k ih =>
    intro hkn h
    rw [rmax_succ] at h
    rcases le_max_iff.mp h with hleft | hright
    · obtain ⟨j, hj, hbj⟩ := ih (by omega) hleft
      exact ⟨j, by omega, hbj⟩
    · exact ⟨k + 1, le_rfl, hright⟩

/-- **Discrete intermediate value, bounded form.** If `b ≥ 1` and the running maximum
up to `n` reaches `b`, then some partial sum with index at most `n` equals `b`. -/
theorem exists_hit_le {n : ℕ} (ω : Fin n → Bool) {b : ℤ} (hb : 1 ≤ b)
    (h : b ≤ rmax ω n) : ∃ j ≤ n, psum ω j = b := by
  obtain ⟨j, hjn, hbj⟩ := exists_le_psum_of_le_rmax ω n le_rfl h
  have hex : ∃ m, b ≤ psum ω m := ⟨j, hbj⟩
  have hspec : b ≤ psum ω (Nat.find hex) := Nat.find_spec hex
  have hkle : Nat.find hex ≤ n := le_trans (Nat.find_le hbj) hjn
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp only [psum_zero] at hspec
    omega
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hprev' : psum ω m ≤ b - 1 := by
    have hcon : ¬ (b ≤ psum ω m) := Nat.find_min hex (by omega)
    omega
  have hstep : psum ω (m + 1) ≤ psum ω m + 1 := by
    rcases psum_sub_succ ω (k := m) (by omega : m < n) with hs | hs <;> omega
  have hspec' : b ≤ psum ω (m + 1) := by rw [← hm]; exact hspec
  refine ⟨Nat.find hex, hkle, ?_⟩
  rw [hm]
  omega

/-- **Discrete intermediate value.** If `b ≥ 1` and the running maximum up to `n`
reaches `b`, then some partial sum equals `b`. -/
theorem exists_psum_eq_rmax {n : ℕ} (ω : Fin n → Bool) {b : ℤ} (hb : 1 ≤ b)
    (h : b ≤ rmax ω n) : ∃ j, psum ω j = b := by
  obtain ⟨j, -, hj⟩ := exists_hit_le ω hb h
  exact ⟨j, hj⟩

/-! ## Reflecting the tail of a path -/

def flipTail {n : ℕ} (t : ℕ) (ω : Fin n → Bool) : Fin n → Bool :=
  fun i => if (i : ℕ) < t then ω i else !(ω i)

theorem flipTail_apply {n : ℕ} (t : ℕ) (ω : Fin n → Bool) (i : Fin n) :
    flipTail t ω i = if (i : ℕ) < t then ω i else !(ω i) := rfl

theorem flipTail_flipTail {n : ℕ} (t : ℕ) (ω : Fin n → Bool) :
    flipTail t (flipTail t ω) = ω := by
  funext i
  rw [flipTail_apply, flipTail_apply]
  by_cases h : (i : ℕ) < t <;> simp [h]

theorem psum_flipTail {n : ℕ} (ω : Fin n → Bool) (t k : ℕ) (hk : k ≤ n) :
    psum (flipTail t ω) k = if k ≤ t then psum ω k else 2 * psum ω t - psum ω k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkn : k < n := by omega
    have hstep : step (flipTail t ω ⟨k, hkn⟩) = if k < t then step (ω ⟨k, hkn⟩) else -step (ω ⟨k, hkn⟩) := by
      rw [flipTail_apply]
      by_cases hkt : k < t
      · simp [hkt]
      · simp [hkt, step_flip]
    have ihk := ih (by omega : k ≤ n)
    rw [psum_succ_of_lt (h := hkn), ihk]
    rcases lt_trichotomy k t with hlt | heq | hgt
    · -- before the reflection point
      rw [if_pos (by omega : k ≤ t), hstep, if_pos hlt]
      rw [psum_succ_of_lt ω hkn, if_pos (by omega : k + 1 ≤ t)]
    · -- at the reflection point
      subst heq
      rw [if_pos (le_refl k), hstep, if_neg (by omega : ¬ k < k)]
      rw [psum_succ_of_lt ω hkn, if_neg (by omega : ¬ k + 1 ≤ k)]
      ring
    · -- after the reflection point
      rw [if_neg (by omega : ¬ k ≤ t), hstep, if_neg (by omega : ¬ k < t)]
      rw [psum_succ_of_lt ω hkn, if_neg (by omega : ¬ k + 1 ≤ t)]
      ring

theorem psum_flipTail_self {n : ℕ} (ω : Fin n → Bool) {t : ℕ} (ht : t ≤ n) :
    psum (flipTail t ω) t = psum ω t := by
  rw [psum_flipTail ω t t ht, if_pos le_rfl]

theorem psum_flipTail_end {n : ℕ} (ω : Fin n → Bool) {t : ℕ} (ht : t ≤ n) :
    psum (flipTail t ω) n = 2 * psum ω t - psum ω n := by
  rw [psum_flipTail ω t n le_rfl]
  by_cases h : n ≤ t
  · have htn : t = n := by omega
    subst htn
    rw [if_pos le_rfl]; ring
  · rw [if_neg h]

theorem psum_flipTail_le {n : ℕ} (ω : Fin n → Bool) {t k : ℕ} (hk : k ≤ t) (hn : k ≤ n) :
    psum (flipTail t ω) k = psum ω k := by
  rw [psum_flipTail ω t k hn, if_pos hk]

end SwarmReflect
