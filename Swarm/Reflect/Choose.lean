/-
# The endpoint distribution of the symmetric walk is the binomial law

This module identifies the number of `±1` step sequences of length `n` with a
given endpoint: writing `support ω` for the set of coordinates carrying a `+1`
step, one has `S_n(ω) = 2 #(support ω) - n`, and `support` is a bijection onto
the `n`-element ground set's subsets, so

  `#{ω : S_n = 2m - n} = n.choose m`.

Consequently every endpoint mass is at most the middle binomial coefficient
`n.choose (n/2)`, and the exact law of the running maximum of `Reflect.Law`
becomes a statement about binomial coefficients.
-/
import Swarm.Imports
import Swarm.Reflect.Basic
import Swarm.Reflect.Law

open Finset

namespace SwarmReflect

open Classical

variable {n : ℕ}

/-! ## The support of a path -/

/-- The set of coordinates at which the walk steps `+1`. -/
def support (ω : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter fun i => ω i = true

theorem mem_support {ω : Fin n → Bool} {i : Fin n} : i ∈ support ω ↔ ω i = true := by
  simp [support]

theorem support_injective : Function.Injective (support (n := n)) := by
  intro ω₁ ω₂ h
  funext i
  have h1 : i ∈ support ω₁ ↔ i ∈ support ω₂ := by rw [h]
  rw [mem_support, mem_support] at h1
  cases h₁ : ω₁ i <;> cases h₂ : ω₂ i <;> simp_all

theorem support_of_mem (s : Finset (Fin n)) :
    support (fun i => decide (i ∈ s)) = s := by
  ext i
  rw [mem_support]
  simp

theorem decide_support (ω : Fin n → Bool) :
    (fun i => decide (i ∈ support ω)) = ω := by
  funext i
  cases h : ω i <;> simp [mem_support, h]

/-! ## Endpoint in terms of the support -/

theorem step_eq_indicator (b : Bool) :
    step b = 2 * (if b = true then (1 : ℤ) else 0) - 1 := by
  cases b <;> simp [step]

theorem sum_step_eq (ω : Fin n → Bool) :
    ∑ i : Fin n, step (ω i) = 2 * ((support ω).card : ℤ) - (n : ℤ) := by
  have hind : ∀ i : Fin n, step (ω i) = 2 * (if ω i = true then (1 : ℤ) else 0) - 1 :=
    fun i => step_eq_indicator (ω i)
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hind i)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ i : Fin n, (if ω i = true then (1 : ℤ) else 0) = ((support ω).card : ℤ) := by
    rw [Finset.sum_boole]
    simp [support]
  have h2 : ∑ _i : Fin n, (1 : ℤ) = (n : ℤ) := by
    simp
  rw [h1, h2]

theorem psum_eq_sum_range (ω : Fin n → Bool) (k : ℕ) :
    psum ω k = ∑ i ∈ Finset.range k, (if h : i < n then step (ω ⟨i, h⟩) else 0) := by
  induction k with
  | zero => simp
  | succ k ih => rw [psum_succ, ih, Finset.sum_range_succ]

theorem psum_eq_sum_fin (ω : Fin n → Bool) : psum ω n = ∑ i : Fin n, step (ω i) := by
  rw [psum_eq_sum_range ω n,
    ← Fin.sum_univ_eq_sum_range
      (fun i : ℕ => if h : i < n then step (ω ⟨i, h⟩) else 0) n]
  refine Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => ?_
  rw [dif_pos i.isLt]

/-- The endpoint of the walk is determined by the number of upward steps. -/
theorem psum_eq_support (ω : Fin n → Bool) :
    psum ω n = 2 * ((support ω).card : ℤ) - (n : ℤ) := by
  rw [psum_eq_sum_fin, sum_step_eq]

/-! ## The binomial count -/

theorem card_support_eq (m : ℕ) :
    (Finset.univ.filter fun ω : Fin n → Bool => (support ω).card = m).card = n.choose m := by
  have hbij : (Finset.univ.filter fun ω : Fin n → Bool => (support ω).card = m).card
      = (Finset.univ.powersetCard m : Finset (Finset (Fin n))).card := by
    apply Finset.card_bij'
      (i := fun (ω : Fin n → Bool)
        (_ : ω ∈ Finset.univ.filter fun ω : Fin n → Bool => (support ω).card = m) => support ω)
      (j := fun (s : Finset (Fin n))
        (_ : s ∈ Finset.univ.powersetCard m) => fun i => decide (i ∈ s))
    · intro ω hω
      rw [Finset.mem_filter] at hω
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hω.2⟩
    · intro s hs
      rw [Finset.mem_powersetCard] at hs
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [support_of_mem]; exact hs.2⟩
    · intro ω _
      exact decide_support ω
    · intro s _
      exact support_of_mem s
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **The endpoint distribution.** The number of step sequences of length `n`
ending at `2m - n` is the binomial coefficient `n.choose m`. -/
theorem card_psum_eq_choose (m : ℕ) :
    (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = 2 * (m : ℤ) - (n : ℤ)).card
      = n.choose m := by
  have hset : (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = 2 * (m : ℤ) - (n : ℤ))
      = (Finset.univ.filter fun ω : Fin n → Bool => (support ω).card = m) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, psum_eq_support ω]
    constructor <;> intro h <;> omega
  rw [hset, card_support_eq]

/-- Every endpoint mass is at most the middle binomial coefficient. -/
theorem card_psum_le_middle (k : ℤ) :
    (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = k).card ≤ n.choose (n / 2) := by
  by_cases hempty : (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = k) = ∅
  · rw [hempty]; simp
  · obtain ⟨ω₀, hω₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hk : psum ω₀ n = k := (Finset.mem_filter.mp hω₀).2
    have hk' : k = 2 * ((support ω₀).card : ℤ) - (n : ℤ) := by
      rw [← hk, psum_eq_support ω₀]
    have hset : (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = k)
        = (Finset.univ.filter fun ω : Fin n → Bool =>
            (support ω).card = (support ω₀).card) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, psum_eq_support ω]
      constructor
      · intro h
        rw [hk'] at h
        have h3 : ((support ω).card : ℤ) = ((support ω₀).card : ℤ) := by omega
        exact_mod_cast h3
      · intro h
        rw [h, hk']
    rw [hset, card_support_eq]
    exact Nat.choose_le_middle (support ω₀).card n

/-- **Law of the running maximum with binomial endpoints.** For `b ≥ 1` the paths
that never reach `b` are exactly as numerous as those ending at `b` or strictly
inside `(-b, b)`, and every such endpoint mass is a binomial coefficient
`n.choose m` (`card_psum_eq_choose`). -/
theorem card_rmax_lt_eq_endpoints {b : ℤ} (hb : 1 ≤ b) :
    (Finset.univ.filter fun ω : Fin n → Bool => rmax ω n < b).card
      = (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = b).card
        + (Finset.univ.filter fun ω : Fin n → Bool => |psum ω n| < b).card :=
  card_rmax_lt hb

/-- **Running-maximum bound reduced to the middle binomial coefficient.**
For every level `b ≥ 1` the number of step sequences of length `n` that never
reach `b` is at most `(2b + 1) · n.choose (n/2)`. Together with the classical
Wallis estimate `n.choose (n/2) ≤ 2^n / sqrt n` this is the paper's
`P(max_{t≤n} S_t < b) ≤ C b n^{-1/2}`. -/
theorem card_rmax_lt_le_middle (b : ℕ) (hb : 1 ≤ b) :
    (Finset.univ.filter fun ω : Fin n → Bool => rmax ω n < (b : ℤ)).card
      ≤ (2 * b + 1) * n.choose (n / 2) := by
  have hbz : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
  have hmain := card_rmax_lt (n := n) hbz
  have h1 : (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = (b : ℤ)).card
      ≤ n.choose (n / 2) := card_psum_le_middle (b : ℤ)
  have h2 : (Finset.univ.filter fun ω : Fin n → Bool => |psum ω n| < (b : ℤ)).card
      ≤ (2 * b) * n.choose (n / 2) := by
    have hpart : (Finset.univ.filter fun ω : Fin n → Bool => |psum ω n| < (b : ℤ))
        = (Finset.Icc (1 - (b : ℤ)) ((b : ℤ) - 1)).biUnion
            (fun k => Finset.univ.filter fun ω : Fin n → Bool => psum ω n = k) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_Icc, abs_lt]
      constructor
      · intro h
        exact ⟨psum ω n, ⟨by omega, by omega⟩, rfl⟩
      · rintro ⟨k, ⟨hk1, hk2⟩, hk⟩
        omega
    rw [hpart]
    calc ((Finset.Icc (1 - (b : ℤ)) ((b : ℤ) - 1)).biUnion
            (fun k => Finset.univ.filter fun ω : Fin n → Bool => psum ω n = k)).card
        ≤ ∑ k ∈ Finset.Icc (1 - (b : ℤ)) ((b : ℤ) - 1),
            (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = k).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ Finset.Icc (1 - (b : ℤ)) ((b : ℤ) - 1), n.choose (n / 2) :=
          Finset.sum_le_sum fun k (_ : k ∈ Finset.Icc (1 - (b : ℤ)) ((b : ℤ) - 1)) =>
            card_psum_le_middle k
      _ = ((Finset.Icc (1 - (b : ℤ)) ((b : ℤ) - 1)).card) * n.choose (n / 2) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (2 * b) * n.choose (n / 2) := by
          have hc : (Finset.Icc (1 - (b : ℤ)) ((b : ℤ) - 1)).card ≤ 2 * b := by
            rw [Int.card_Icc]
            omega
          exact Nat.mul_le_mul_right _ hc
  rw [hmain]
  calc (Finset.univ.filter fun ω : Fin n → Bool => psum ω n = (b : ℤ)).card
        + (Finset.univ.filter fun ω : Fin n → Bool => |psum ω n| < (b : ℤ)).card
      ≤ n.choose (n / 2) + (2 * b) * n.choose (n / 2) := Nat.add_le_add h1 h2
    _ = (2 * b + 1) * n.choose (n / 2) := by ring

end SwarmReflect
