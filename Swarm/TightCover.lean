/-
# Record-distance tightness: the covering step of Prop. "tight"

`main_1d_revised.tex`, Prop. `tight`, proves `lim_K limsup_r P (d_r > K) = 0` for the
record distances `d_r` from two ingredients:

* the fluid-limit **block estimate** `(blkprob)`: for a threshold `L`, an integer `r >= C₀ L`
  and constants `B, T, C₀` chosen as in `(BTchoice)`, the event
  `{d_r <= L} ∩ {block fails}` has probability at most `C_T * exp (-c_T * L^(1/16))`, where
  "block fails" means that one of the three inequalities of `(block)` fails:
  `τ_{r+BL} - τ_r <= T L`, `d_{r+BL} <= L/2`, `max_{r <= u <= r+BL} d_u <= C₀ L`;
* the **covering argument**: the paper's halving procedure, which turns the block estimate
  into `limsup_u P (d_u > C₀ K) <= ∑_{ℓ >= K} (4Bℓ+1) C_T exp (-c_T ℓ^(1/16))`.

This file proves the covering argument in full abstraction, with no probability theory at all.
The object is an arbitrary sequence `d : ℕ → ℕ` (think: `d u = max_i d^i_u`, the largest distance
below the running record at record index `u`), together with an arbitrary "good block" relation
`Good r L` whose only role is to stand for the conjunction of the paper's three block
inequalities.  Two hypotheses are used:

* `hS` (`Good` really is the conjunction of the three block inequalities, so that it implies the
  two consequences the paper uses);
* `hterm` (the halving procedure eventually succeeds, i.e. the paper's almost-sure statement
  `(recordo)` that every block inequality holds for all large `L`, for each fixed `r`).

The conclusion is exactly the paper's covering statement: every index `u` at distance more than
`C₀ K` below the record, past the initial transient `2 B L₀`, carries a *certificate*
`(r, ℓ)`: a failing block at level `ℓ >= K` started at `r`, whose region `[r, r + 4 B ℓ]`
contains `u`.  The number of blocks of level `ℓ` that can contain a given index is at most
`4Bℓ + 1`, which is what the union bound in `Tightness.lean` needs.
-/
import Swarm.Imports

open Classical
open scoped BigOperators

namespace RecordTight

/-- The data of the halving argument: the level cap `K`, the block-length coefficient `B`, the
spatial coefficient `C₀`, the record-distance sequence `d`, the block-goodness relation and the
two structural hypotheses.  The starting index `r₀` and starting level `L₀` of the procedure
are part of the data because the probabilistic wrapper starts the procedure past the
almost-sure threshold of the paper's Borel–Cantelli step. -/
structure Ctx where
  K : ℕ
  B : ℕ
  C₀ : ℕ
  d : ℕ → ℕ
  Good : ℕ → ℕ → Prop
  r₀ : ℕ
  L₀ : ℕ
  /-- The halving procedure succeeds after finitely many doublings at every start. -/
  hterm : ∀ r L, K ≤ L → ∃ j, Good r (2 ^ j * L)
  /-- `Good r L` is the conjunction of the paper's three block inequalities, so it forces the
  endpoint distance `d_{r+BL} <= L/2` and the bound `d_u <= C₀ L` inside the block. -/
  hS : ∀ r L, Good r L → d r ≤ L →
    d (r + B * L) ≤ L / 2 ∧ ∀ u, r ≤ u → u ≤ r + B * L → d u ≤ C₀ * L
  hB : 1 ≤ B
  hK : 1 ≤ K
  hstart : max K (d r₀) ≤ L₀

namespace Ctx

/-! ## The halving procedure

From a start `(L, r)`, double `L` until the block is good; the successful level `M` advances the
index by `B * M` and the next level is `M / 2`, capped below by `K`. -/

/-- One step of the halving procedure. -/
noncomputable def stepState (c : Ctx) (p : ℕ × ℕ) : ℕ × ℕ :=
  let L := max c.K p.1
  let r := p.2
  let j := Nat.find (c.hterm r L (le_max_left c.K p.1))
  (max c.K (2 ^ j * L / 2), r + c.B * (2 ^ j * L))

/-- The iterated procedure. -/
noncomputable def st (c : Ctx) : ℕ → ℕ × ℕ :=
  fun n => Nat.rec (motive := fun _ => ℕ × ℕ) (max c.K c.L₀, c.r₀)
    (fun _ p => c.stepState p) n

lemma st_succ (c : Ctx) (n : ℕ) : c.st (n + 1) = c.stepState (c.st n) := rfl

/-- The level at the `n`-th step. -/
noncomputable def lv (c : Ctx) (n : ℕ) : ℕ := (c.st n).1

/-- The index (record count) at which the `n`-th step starts. -/
noncomputable def ps (c : Ctx) (n : ℕ) : ℕ := (c.st n).2

/-- The number of doublings needed at the `n`-th step. -/
noncomputable def kf (c : Ctx) (n : ℕ) : ℕ :=
  Nat.find (c.hterm (c.ps n) (max c.K (c.lv n)) (le_max_left c.K (c.lv n)))

/-- The level of the good block found at the `n`-th step. -/
noncomputable def Mlv (c : Ctx) (n : ℕ) : ℕ := 2 ^ c.kf n * max c.K (c.lv n)

lemma lv_succ (c : Ctx) (n : ℕ) : c.lv (n + 1) = max c.K (c.Mlv n / 2) := by
  simp only [lv, Mlv, kf, ps, st_succ, stepState]

lemma ps_succ (c : Ctx) (n : ℕ) : c.ps (n + 1) = c.ps n + c.B * c.Mlv n := by
  simp only [ps, lv, Mlv, kf, st_succ, stepState]

lemma lv_zero (c : Ctx) : c.lv 0 = max c.K c.L₀ := rfl

lemma ps_zero (c : Ctx) : c.ps 0 = c.r₀ := rfl

/-- The level is always at least `K`. -/
lemma le_lv (c : Ctx) (n : ℕ) : c.K ≤ c.lv n := by
  cases n with
  | zero => rw [lv_zero]; exact le_max_left _ _
  | succ n => rw [lv_succ]; exact le_max_left _ _

lemma max_lv_eq (c : Ctx) (n : ℕ) : max c.K (c.lv n) = c.lv n :=
  max_eq_right (c.le_lv n)

lemma Mlv_eq (c : Ctx) (n : ℕ) : c.Mlv n = 2 ^ c.kf n * c.lv n := by
  simp only [Mlv, c.max_lv_eq n]

lemma le_Mlv (c : Ctx) (n : ℕ) : c.lv n ≤ c.Mlv n := by
  rw [c.Mlv_eq n]
  calc c.lv n = 1 * c.lv n := (one_mul _).symm
    _ ≤ 2 ^ c.kf n * c.lv n := Nat.mul_le_mul_right _ (Nat.one_le_two_pow)

lemma one_le_Mlv (c : Ctx) (n : ℕ) : 1 ≤ c.Mlv n :=
  le_trans c.hK (le_trans (c.le_lv n) (c.le_Mlv n))

lemma pos_advance (c : Ctx) (n : ℕ) : 1 ≤ c.B * c.Mlv n :=
  Nat.mul_pos c.hB (c.one_le_Mlv n)

/-- The block found at step `n` is good. -/
lemma good_Mlv (c : Ctx) (n : ℕ) : c.Good (c.ps n) (c.Mlv n) :=
  Nat.find_spec (c.hterm (c.ps n) (max c.K (c.lv n)) (le_max_left c.K (c.lv n)))

/-- The indices are strictly increasing. -/
lemma ps_strictMono (c : Ctx) : StrictMono c.ps := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [ps_succ]
  have := c.pos_advance n
  omega

lemma ps_mono (c : Ctx) : Monotone c.ps := c.ps_strictMono.monotone

lemma le_ps_add (c : Ctx) (n : ℕ) : c.r₀ + n ≤ c.ps n := by
  induction n with
  | zero => rw [ps_zero, Nat.add_zero]
  | succ n ih =>
      rw [ps_succ]
      have := c.pos_advance n
      omega

lemma lt_ps_ps (c : Ctx) {m n : ℕ} (h : m < n) : c.ps m < c.ps n := c.ps_strictMono h

/-! ## The invariants of the procedure -/

/-- The current level dominates the current distance. -/
lemma d_ps_le_lv (c : Ctx) (n : ℕ) : c.d (c.ps n) ≤ c.lv n := by
  cases n with
  | zero =>
      rw [ps_zero, lv_zero]
      exact le_trans (le_trans (le_max_right _ _) c.hstart) (le_max_right _ _)
  | succ n =>
      have h1 : c.d (c.ps n + c.B * c.Mlv n) ≤ c.Mlv n / 2 :=
        (c.hS (c.ps n) (c.Mlv n) (c.good_Mlv n)
          (le_trans (c.d_ps_le_lv n) (c.le_Mlv n))).1
      rw [ps_succ, lv_succ]
      exact le_trans h1 (le_max_right _ _)

/-- Every index inside the block of step `n` is at distance at most `C₀ M`. -/
lemma d_le_of_mem_block (c : Ctx) (n u : ℕ) (h1 : c.ps n ≤ u)
    (h2 : u ≤ c.ps (n + 1)) : c.d u ≤ c.C₀ * c.Mlv n := by
  have hS := c.hS (c.ps n) (c.Mlv n) (c.good_Mlv n)
    (le_trans (c.d_ps_le_lv n) (c.le_Mlv n))
  rw [ps_succ] at h2
  exact hS.2 u h1 h2

/-! ## Elementary arithmetic of repeated halving -/

end Ctx

/-- Truncated geometric bound for repeated halving: `∑_{t<N} L / 2^t ≤ 2 L`. -/
lemma sum_div_two_pow_le : ∀ (L N : ℕ), ∑ t ∈ Finset.range N, L / 2 ^ t ≤ 2 * L := by
  intro L N
  induction N generalizing L with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ']
      have hcongr : ∑ t ∈ Finset.range N, L / 2 ^ (t + 1) = ∑ t ∈ Finset.range N, L / 2 / 2 ^ t := by
        refine Finset.sum_congr rfl ?_
        intro t _
        rw [pow_succ']
        exact (Nat.div_div_eq_div_mul L 2 (2 ^ t)).symm
      rw [hcongr]
      have h2 : ∑ t ∈ Finset.range N, L / 2 / 2 ^ t ≤ 2 * (L / 2) := ih (L / 2)
      have h3 : 2 * (L / 2) ≤ L := by
        have := Nat.div_mul_le_self L 2
        omega
      simp only [pow_zero, Nat.div_one]
      omega

namespace Ctx

lemma Mlv_eq_of_kf_zero (c : Ctx) {n : ℕ} (h : c.kf n = 0) : c.Mlv n = c.lv n := by
  rw [c.Mlv_eq n, h, pow_zero, one_mul]

/-- A successful step at a capped level never increases the level. -/
lemma lv_succ_le_of_kf_zero (c : Ctx) {n : ℕ} (h : c.kf n = 0) : c.lv (n + 1) ≤ c.lv n := by
  rw [lv_succ, c.Mlv_eq_of_kf_zero h]
  exact max_le (c.le_lv n) (Nat.div_le_self _ _)

/-- Along a run of successful blocks the level never increases. -/
lemma lv_le_of_successes (c : Ctx) {m n : ℕ} (hmn : m ≤ n)
    (hsucc : ∀ i, m ≤ i → i < n → c.kf i = 0) : c.lv n ≤ c.lv m := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
      have h1 : c.lv n ≤ c.lv m := ih (fun i hi hi2 => hsucc i hi (by omega))
      have h2 : c.lv (n + 1) ≤ c.lv n :=
        lv_succ_le_of_kf_zero c (hsucc n hmn (by omega))
      omega

/-- After a successful step, if the level is still above `K` it halved exactly. -/
lemma lv_succ_eq_div (c : Ctx) {n : ℕ} (hkf : c.kf n = 0) (h : c.K < c.lv (n + 1)) :
    c.lv (n + 1) = c.lv n / 2 := by
  rw [lv_succ, c.Mlv_eq_of_kf_zero hkf] at h ⊢
  have hx : c.K < c.lv n / 2 := by
    by_cases h' : c.lv n / 2 ≤ c.K
    · rw [max_eq_left h'] at h; exact absurd h (lt_irrefl c.K)
    · omega
  rw [max_eq_right (le_of_lt hx)]

lemma le_pow_mul_lv (c : Ctx) {n : ℕ} (h : 1 ≤ c.kf n) :
    c.lv n ≤ 2 ^ (c.kf n - 1) * c.lv n := by
  calc c.lv n = 1 * c.lv n := (one_mul _).symm
    _ ≤ 2 ^ (c.kf n - 1) * c.lv n := Nat.mul_le_mul_right _ Nat.one_le_two_pow

/-- **The failing block.**  If at least one doubling was needed, the last level tried is
certified: the block there fails, and the level is at most that failing level. -/
lemma fail_not_good (c : Ctx) {n : ℕ} (h : 1 ≤ c.kf n) :
    ¬ c.Good (c.ps n) (2 ^ (c.kf n - 1) * c.lv n) := by
  have hlt : c.kf n - 1 < c.kf n := by omega
  have hmin := Nat.find_min (c.hterm (c.ps n) (max c.K (c.lv n)) (le_max_left _ _)) hlt
  refine fun hg => hmin ?_
  rw [c.max_lv_eq n]
  exact hg

lemma Mlv_eq_two_mul (c : Ctx) {n : ℕ} (h : 1 ≤ c.kf n) :
    c.Mlv n = 2 * (2 ^ (c.kf n - 1) * c.lv n) := by
  rw [c.Mlv_eq n]
  have hk : c.kf n = c.kf n - 1 + 1 := by omega
  conv_lhs => rw [hk, pow_succ]
  ring

/-- After a failing block the next level is exactly the last failing level. -/
lemma lv_succ_eq_of_fail (c : Ctx) {n : ℕ} (h : 1 ≤ c.kf n) :
    c.lv (n + 1) = 2 ^ (c.kf n - 1) * c.lv n := by
  have hd : c.Mlv n / 2 = 2 ^ (c.kf n - 1) * c.lv n := by
    rw [c.Mlv_eq_two_mul h, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  rw [lv_succ, hd]
  exact max_eq_right (le_trans (c.le_lv n) (c.le_pow_mul_lv h))

/-! ## The telescoping bound along a run of successful blocks -/

/-- Along a run of successful blocks in which the level stays above `K`, the index advances at
most `B * 2 * L` where `L` is the level at the start of the run.

The proof uses the invariant `ps i + 2 B lv i <= ps (j+1) + 2 B lv (j+1)`: every successful
step adds `B lv i` to the index and halves the level, and `2 * (lv i / 2) <= lv i`. -/
lemma chain_bound (c : Ctx) {j n : ℕ}
    (hsucc : ∀ i, j < i → i ≤ n → c.kf i = 0)
    (hgt : ∀ i, j < i → i ≤ n → c.K < c.lv i) :
    c.ps (n + 1) ≤ c.ps (j + 1) + c.B * (2 * c.lv (j + 1)) := by
  by_cases hlt : j < n
  · have key : ∀ i, j + 1 ≤ i → i ≤ n →
        c.ps i + 2 * (c.B * c.lv i) ≤ c.ps (j + 1) + 2 * (c.B * c.lv (j + 1)) := by
      intro i hi1 hi2
      induction i, hi1 using Nat.le_induction with
      | base => exact le_rfl
      | succ i hi1 ih =>
          have h1 : c.ps i + 2 * (c.B * c.lv i) ≤
              c.ps (j + 1) + 2 * (c.B * c.lv (j + 1)) := ih (by omega)
          have hkf : c.kf i = 0 := hsucc i (by omega) (by omega)
          have hstep : c.lv (i + 1) = c.lv i / 2 :=
            lv_succ_eq_div (hkf := hkf) (h := hgt (i + 1) (by omega) (by omega))
          have hps : c.ps (i + 1) = c.ps i + c.B * c.lv i := by
            rw [ps_succ, c.Mlv_eq_of_kf_zero hkf]
          have h2 : 2 * (c.B * (c.lv i / 2)) ≤ c.B * c.lv i := by
            have h3 := Nat.div_mul_le_self (c.lv i) 2
            nlinarith [Nat.zero_le c.B, Nat.zero_le (c.lv i)]
          rw [hps, hstep]
          omega
    have hkfn : c.kf n = 0 := hsucc n hlt (le_rfl)
    have hpsn : c.ps (n + 1) = c.ps n + c.B * c.lv n := by
      rw [ps_succ, c.Mlv_eq_of_kf_zero hkfn]
    have hfin := key n (by omega) (le_rfl)
    have h5 : c.B * (2 * c.lv (j + 1)) = 2 * (c.B * c.lv (j + 1)) := by ring
    rw [hpsn, h5]
    omega
  · push_neg at hlt
    exact le_trans (c.ps_mono (by omega)) (Nat.le_add_right _ _)

/-! ## The covering theorem -/

/-- **Covering by certificates (the paper's covering argument for Prop. `tight`).**

Fix the level cap `K`, the block coefficient `B` and the spatial coefficient `C₀`, and suppose
that the halving procedure can always find a good block after finitely many doublings.  Then for
every index `u` past the initial transient `r₀ + 2 B L₀` whose distance below the record exceeds
`C₀ K`, there is a *certificate*: a failing block at level `ℓ ≥ K` started at some `r`, with
`d r ≤ ℓ`, whose region `[r, r + 4 B ℓ]` contains `u`.

This is exactly the paper's conclusion
"every integer `u` with `d_u > C₀K` belongs to `[r, r+4Bℓ]` for some `r` and dyadic `ℓ ≥ K`
such that `d_r ≤ ℓ` and `(block)` fails with `L = ℓ`",
with the dyadic grid replaced by the doubling grid of the procedure itself: the paper needs
dyadic `ℓ` only to enumerate its cover, whereas the union bound of `Tightness.lean` counts the
integers `r ∈ [u - 4Bℓ, u]` directly. -/
theorem exists_certificate (c : Ctx) {u : ℕ} (hu : c.r₀ + 2 * c.B * c.L₀ ≤ u)
    (hdu : c.C₀ * c.K < c.d u) :
    ∃ r ℓ, c.K ≤ ℓ ∧ c.d r ≤ ℓ ∧ ¬ c.Good r ℓ ∧ c.r₀ ≤ r ∧ r ≤ u ∧ u ≤ r + 4 * c.B * ℓ := by
  have hKL₀ : c.K ≤ c.L₀ := le_trans (le_max_left _ _) c.hstart
  have hlvv : c.lv 0 = c.L₀ := by rw [lv_zero, max_eq_right hKL₀]
  -- the block containing `u`
  have hex : ∃ n, u < c.ps (n + 1) := ⟨u, by have := c.le_ps_add (u + 1); omega⟩
  obtain ⟨n, hn, hnmin⟩ : ∃ n, u < c.ps (n + 1) ∧ ∀ m < n, c.ps (m + 1) ≤ u :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_lt.1 (Nat.find_min hex hm)⟩
  have hpsn_le : c.ps n ≤ u := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, ps_zero]; omega
    · simpa [Nat.sub_add_cancel h] using hnmin (n - 1) (by omega)
  have hblock : c.d u ≤ c.C₀ * c.Mlv n := c.d_le_of_mem_block n u hpsn_le hn.le
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- the first block
    subst hn0
    have hn1 : u < c.ps 1 := by simpa using hn
    have hk0 : 1 ≤ c.kf 0 := by
      rcases Nat.eq_zero_or_pos (c.kf 0) with h | h
      · exfalso
        have hps1 : c.ps 1 = c.r₀ + c.B * c.L₀ := by
          rw [ps_succ, ps_zero, c.Mlv_eq_of_kf_zero h, hlvv]
        have h1 : c.ps 1 ≤ u := by rw [hps1]; nlinarith
        omega
      · exact h
    refine ⟨c.ps 0, 2 ^ (c.kf 0 - 1) * c.lv 0, ?_, ?_, c.fail_not_good hk0, ?_, ?_, ?_⟩
    · exact le_trans (c.le_lv 0) (c.le_pow_mul_lv hk0)
    · exact le_trans (c.d_ps_le_lv 0) (c.le_pow_mul_lv hk0)
    · rw [ps_zero]
    · rw [ps_zero]; exact le_trans (Nat.le_add_right _ _) hu
    · rw [ps_succ, c.Mlv_eq_two_mul hk0] at hn
      have h1 : c.B * (2 * (2 ^ (c.kf 0 - 1) * c.lv 0)) ≤
          4 * c.B * (2 ^ (c.kf 0 - 1) * c.lv 0) := by
        nlinarith [Nat.zero_le (c.B * (2 ^ (c.kf 0 - 1) * c.lv 0))]
      omega
  · -- later blocks: the last failing block index at or before `n`
    set P : ℕ → Prop := fun i => 1 ≤ c.kf i with hP
    set j := Nat.findGreatest P n with hj
    have hj_le : j ≤ n := Nat.findGreatest_le n
    by_cases hfail : P j
    · have hsucc : ∀ i, j < i → i ≤ n → c.kf i = 0 := by
        intro i hi1 hi2
        have h := Nat.findGreatest_is_greatest (P := P) hi1 hi2
        simp only [hP] at h ⊢
        omega
      have hgt : ∀ i, j < i → i ≤ n → c.K < c.lv i := by
        intro i hi1 hi2
        by_contra hle
        push_neg at hle
        have hik : c.lv i = c.K := le_antisymm hle (c.le_lv i)
        have hkfn : c.kf n = 0 := hsucc n (by omega) le_rfl
        have hlvn : c.lv n ≤ c.lv i :=
          c.lv_le_of_successes hi2 (fun k hk1 hk2 => hsucc k (by omega) (by omega))
        refine absurd hdu (not_lt.2 ?_)
        refine le_trans hblock ?_
        rw [c.Mlv_eq_of_kf_zero hkfn]
        exact Nat.mul_le_mul_left _ (le_trans hlvn (le_of_eq hik))
      have hchain := c.chain_bound hsucc hgt
      have hpsj1 : c.ps (j + 1) = c.ps j + c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j)) := by
        rw [ps_succ, c.Mlv_eq_two_mul hfail]
      have hlvj1 : c.lv (j + 1) = 2 ^ (c.kf j - 1) * c.lv j := c.lv_succ_eq_of_fail hfail
      refine ⟨c.ps j, 2 ^ (c.kf j - 1) * c.lv j, ?_, ?_, c.fail_not_good hfail, ?_, ?_, ?_⟩
      · exact le_trans (c.le_lv j) (c.le_pow_mul_lv hfail)
      · exact le_trans (c.d_ps_le_lv j) (c.le_pow_mul_lv hfail)
      · exact le_trans (Nat.le_add_right _ _) (le_ps_add c j)
      · exact le_trans (c.ps_mono hj_le) hpsn_le
      · have hb : c.ps (n + 1) ≤
            c.ps j + 2 * (c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j))) := by
          rw [hpsj1, hlvj1] at hchain
          calc c.ps (n + 1) ≤ (c.ps j + c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j))) +
                c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j)) := hchain
            _ = c.ps j + 2 * (c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j))) := by ring
        have h4 : 2 * (c.B * (2 * (2 ^ (c.kf j - 1) * c.lv j))) =
            4 * c.B * (2 ^ (c.kf j - 1) * c.lv j) := by ring
        omega
    · -- no failing block at all
      have hkfz : ∀ i, i ≤ n → c.kf i = 0 := by
        intro i hi
        have hPi : ¬ P i := by
          rcases Nat.eq_zero_or_pos j with hj0 | hjpos
          · rcases Nat.eq_zero_or_pos i with hi0 | hipos
            · rw [hi0]; exact hj0 ▸ hfail
            · have hfg : Nat.findGreatest P n = 0 := hj.symm.trans hj0
              exact Nat.findGreatest_eq_zero_iff.1 hfg hipos hi
          · exact absurd (Nat.findGreatest_of_ne_zero hj.symm hjpos.ne') hfail
        simp only [hP] at hPi
        omega
      have hgt : ∀ i, 0 < i → i ≤ n → c.K < c.lv i := by
        intro i hi1 hi2
        by_contra hle
        push_neg at hle
        have hik : c.lv i = c.K := le_antisymm hle (c.le_lv i)
        have hlvn : c.lv n ≤ c.lv i :=
          c.lv_le_of_successes hi2 (fun k _ _ => hkfz k (by omega))
        refine absurd hdu (not_lt.2 ?_)
        refine le_trans hblock ?_
        rw [c.Mlv_eq_of_kf_zero (hkfz n le_rfl)]
        exact Nat.mul_le_mul_left _ (le_trans hlvn (le_of_eq hik))
      have hchain := c.chain_bound (j := 0) (n := n)
        (fun i _ hi2 => hkfz i hi2) hgt
      have hps1 : c.ps 1 = c.r₀ + c.B * c.L₀ := by
        rw [ps_succ, ps_zero, c.Mlv_eq_of_kf_zero (hkfz 0 (by omega)), hlvv]
      have hlv1 : c.lv 1 = c.L₀ / 2 := by
        rw [lv_succ_eq_div (hkf := hkfz 0 (by omega)) (h := hgt 1 (by omega) hnpos), hlvv]
      rw [hps1, hlv1] at hchain
      have h2 : 2 * (c.L₀ / 2) ≤ c.L₀ := by
        have := Nat.div_mul_le_self c.L₀ 2
        omega
      have h3 : c.ps (n + 1) ≤ c.r₀ + 2 * c.B * c.L₀ := by nlinarith
      omega

end Ctx

end RecordTight
