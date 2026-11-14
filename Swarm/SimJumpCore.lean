/-
# Simultaneous-jump transition algebra for the interacting excited random walks

Formal companion to `main_1d_revised.tex`:

* eq. (rule)  — the conditional jump law of the `N` interacting walkers,
* §3.1 eq. (state), (states) — the record state with local times capped at `m`,
* §3.1 the truncation step `∑_{j≠i} ℓ_j ≥ m  ↔  ∑_{j≠i} (ℓ_j ∧ m) ≥ m`,
* §3.1 eq. (recmark) — the one-step transition law of the record chain,
* Prop. (front) / eq. (force) — the prescribed-path lower bound on the mass of the
  event that the next record state lies in `F = {d : d_i = 0 ∀ i}`.

Everything here is *finite-horizon* algebra with `ℝ`-valued weights: no measure theory,
no stopping-time or integrability hypothesis is used or claimed.
-/
import Swarm.Imports

namespace SimJump

open Finset

/-- A jump vector; `true` is a right jump `+1`, `false` a left jump `-1`. -/
abbrev JumpVec (N : ℕ) := Fin N → Bool

/-! ### Capped local times -/

/-- The truncated (capped) local time `ℓ ∧ m` of the paper. -/
def cap (m x : ℕ) : ℕ := min x m

lemma cap_le (m x : ℕ) : cap m x ≤ m := min_le_right x m

lemma cap_of_lt {m x : ℕ} (h : x ≤ m) : cap m x = x := by simp [cap, min_eq_left h]

lemma cap_of_le {m x : ℕ} (h : m ≤ x) : cap m x = m := by simp [cap, min_eq_right h]

/-- **Truncation invariance** (§3.1, the displayed equivalence): the excitation
condition `∑_{j ≠ i} ℓ_j ≥ m` is unchanged by capping the local times at `m`.  This is
the reason the record chain may store only the capped local times. -/
theorem sum_ge_iff_sum_cap_ge {ι : Type*} (s : Finset ι) (l : ι → ℕ) (m : ℕ) :
    (m ≤ ∑ j ∈ s, l j) ↔ (m ≤ ∑ j ∈ s, cap m (l j)) := by
  by_cases hex : ∃ j ∈ s, m ≤ l j
  · obtain ⟨j, hj, hjl⟩ := hex
    have hcap : cap m (l j) = m := cap_of_le hjl
    have hraw : m ≤ ∑ k ∈ s, l k :=
      calc m ≤ l j := hjl
        _ ≤ ∑ k ∈ s, l k :=
            Finset.single_le_sum (f := fun k => l k) (fun k _ => Nat.zero_le _) hj
    have hcapped : m ≤ ∑ k ∈ s, cap m (l k) :=
      calc m = cap m (l j) := hcap.symm
        _ ≤ ∑ k ∈ s, cap m (l k) :=
            Finset.single_le_sum (f := fun k => cap m (l k)) (fun k _ => Nat.zero_le _) hj
    exact ⟨fun _ => hcapped, fun _ => hraw⟩
  · push Not at hex
    have hall : ∀ j ∈ s, cap m (l j) = l j := fun j hj => cap_of_lt (le_of_lt (hex j hj))
    rw [Finset.sum_congr rfl hall]

/-! ### States and the one-step law -/

/-- A configuration with local times capped at `m`: the positions of the `N` walkers and,
for every site of `ℤ`, the (capped) local times of every walker. -/
structure State (N m : ℕ) where
  pos : Fin N → ℤ
  eta : Fin N → ℤ → ℕ
  hcap : ∀ i x, eta i x ≤ m

/-- Total capped local time of the walkers **other than** `i` at the position of `i`. -/
noncomputable def otherVisits {N m : ℕ} (s : State N m) (i : Fin N) : ℕ :=
  ∑ j ∈ univ.erase i, s.eta j (s.pos i)

/-- The probability that walker `i` jumps right from state `s` (eq. (rule)): `p` if the
other walkers have visited its current site at least `m` times, and `1/2` otherwise. -/
noncomputable def qRight (p : ℝ) (m : ℕ) (s : State N m) (i : Fin N) : ℝ :=
  if m ≤ otherVisits s i then p else 1 / 2

/-- The joint one-step weight of the jump vector `v`: conditionally on the state the `N`
jumps are independent, so the joint weight is the product of the two-point laws. -/
noncomputable def stepW (p : ℝ) (m : ℕ) (s : State N m) (v : JumpVec N) : ℝ :=
  ∏ i, if v i = true then qRight p m s i else 1 - qRight p m s i

/-- The two-point law of a single walker, indexed by its jump. -/
noncomputable def stepFactor (p : ℝ) (m : ℕ) (s : State N m) (i : Fin N) (b : Bool) : ℝ :=
  if b = true then qRight p m s i else 1 - qRight p m s i

lemma stepW_eq_prod (p : ℝ) (m : ℕ) (s : State N m) (v : JumpVec N) :
    stepW p m s v = ∏ i, stepFactor p m s i (v i) := rfl

lemma stepFactor_false_add_true (p : ℝ) (m : ℕ) (s : State N m) (i : Fin N) :
    stepFactor p m s i false + stepFactor p m s i true = 1 := by
  simp only [stepFactor, Bool.false_eq_true, if_false, if_true]
  ring

/-- New position of walker `i` after the jump vector `v`. -/
def stepPos {N m : ℕ} (s : State N m) (v : JumpVec N) (i : Fin N) : ℤ :=
  s.pos i + if v i = true then 1 else -1

/-- One step of the chain: the positions move by the jump vector, and each walker
increments *its own* capped local time at its *new* position by one, up to `m`. -/
noncomputable def step (m : ℕ) (s : State N m) (v : JumpVec N) : State N m where
  pos := stepPos s v
  eta i x := if x = stepPos s v i then cap m (s.eta i x + 1) else s.eta i x
  hcap := by
    intro i x
    split
    · exact cap_le m _
    · exact s.hcap i x

@[simp] lemma step_pos {N : ℕ} (m : ℕ) (s : State N m) (v : JumpVec N) :
    (step m s v).pos = stepPos s v := rfl

lemma step_eta_of_eq {N : ℕ} (m : ℕ) (s : State N m) (v : JumpVec N) (i : Fin N) :
    (step m s v).eta i (stepPos s v i) = cap m (s.eta i (stepPos s v i) + 1) := by
  simp [step]

lemma step_eta_of_ne {N : ℕ} (m : ℕ) (s : State N m) (v : JumpVec N) (i : Fin N) {x : ℤ}
    (hx : x ≠ stepPos s v i) : (step m s v).eta i x = s.eta i x := by
  simp [step, hx]

/-! ### The joint law of a simultaneous jump -/

/-- The joint law of a jump vector is a product of one-walker laws, so summing it over all
jump vectors factors coordinatewise. -/
theorem sum_prod_bool {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → Bool → ℝ) :
    ∑ v : ι → Bool, ∏ i, g i (v i) = ∏ i, (g i true + g i false) := by
  have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Bool))
    (fun i b => g i b)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  simp

/-- **The one-step joint law is a probability law**: its total mass is `1`. -/
theorem stepW_sum_one {N : ℕ} (p : ℝ) (m : ℕ) (s : State N m) :
    ∑ v : JumpVec N, stepW p m s v = 1 := by
  simp_rw [stepW_eq_prod]
  rw [sum_prod_bool]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [add_comm]
  exact stepFactor_false_add_true p m s i

lemma qRight_nonneg {N : ℕ} (p : ℝ) (m : ℕ) (s : State N m) (i : Fin N) (hp : 0 ≤ p) :
    0 ≤ qRight p m s i := by
  unfold qRight
  split
  · exact hp
  · norm_num

lemma qRight_le_one {N : ℕ} (p : ℝ) (m : ℕ) (s : State N m) (i : Fin N) (hp : p ≤ 1) :
    qRight p m s i ≤ 1 := by
  unfold qRight
  split
  · exact hp
  · norm_num

/-- Each factor of the one-step law is nonnegative and at least `1 - p` when
`1/2 ≤ p ≤ 1`. -/
lemma stepFactor_bounds {N : ℕ} (p : ℝ) (m : ℕ) (s : State N m) (i : Fin N) (b : Bool)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ stepFactor p m s i b ∧ 1 - p ≤ stepFactor p m s i b := by
  have h0 : 0 ≤ p := le_trans (by norm_num) hp
  unfold stepFactor
  by_cases h : m ≤ otherVisits s i
  · cases b
    · simp only [Bool.false_eq_true, if_false, qRight, if_pos h]
      exact ⟨by linarith, by linarith⟩
    · simp only [if_true, qRight, if_pos h]
      exact ⟨h0, by linarith⟩
  · cases b
    · simp only [Bool.false_eq_true, if_false, qRight, if_neg h]
      exact ⟨by norm_num, by linarith⟩
    · simp only [if_true, qRight, if_neg h]
      exact ⟨by norm_num, by linarith⟩

/-- Nonnegativity of the joint one-step weight. -/
theorem stepW_nonneg {N : ℕ} (p : ℝ) (m : ℕ) (s : State N m) (v : JumpVec N)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) : 0 ≤ stepW p m s v := by
  rw [stepW_eq_prod]
  exact Finset.prod_nonneg fun i _ => (stepFactor_bounds p m s i (v i) hp hp1).1

/-- **Every prescribed joint jump has probability at least `(1-p)^N`**: fixing the jump
vector, each walker's jump has conditional probability `p ≥ 1-p` (excited) or `1/2 ≥ 1-p`
(unexcited), whatever the state is.  This is the estimate underlying eq. (force). -/
theorem stepW_ge {N : ℕ} (p : ℝ) (m : ℕ) (s : State N m) (v : JumpVec N)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) : (1 - p) ^ N ≤ stepW p m s v := by
  have hnn : (0 : ℝ) ≤ 1 - p := by linarith
  rw [stepW_eq_prod]
  have h2 : ∏ _i : Fin N, (1 - p) ≤ ∏ i : Fin N, stepFactor p m s i (v i) :=
    Finset.prod_le_prod (fun i _ => hnn)
      (fun i _ => (stepFactor_bounds p m s i (v i) hp hp1).2)
  rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2

/-- **The marginal of the joint law is the rule (1)**: the probability that walker `i`
jumps right is `qRight`, whatever the other walkers do — the jumps are conditionally
independent. -/
theorem stepW_marginal {N : ℕ} (p : ℝ) (m : ℕ) (s : State N m) (i : Fin N) :
    ∑ v : JumpVec N, (if v i = true then (1 : ℝ) else 0) * stepW p m s v
      = qRight p m s i := by
  classical
  set g : Fin N → Bool → ℝ := fun k b =>
    if k = i then (if b = true then qRight p m s i else 0) else stepFactor p m s k b with hg
  have hpt : ∀ v : JumpVec N,
      (if v i = true then (1 : ℝ) else 0) * stepW p m s v = ∏ k, g k (v k) := by
    intro v
    rw [stepW_eq_prod]
    by_cases hv : v i = true
    · rw [if_pos hv, one_mul]
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases hk : k = i
      · subst hk; simp [hg, hv, stepFactor]
      · simp [hg, hk]
    · rw [if_neg hv, zero_mul]
      exact Eq.symm (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hg, hv]))
  calc ∑ v : JumpVec N, (if v i = true then (1 : ℝ) else 0) * stepW p m s v
      = ∑ v : JumpVec N, ∏ k, g k (v k) := Finset.sum_congr rfl fun v _ => hpt v
    _ = ∏ k, (g k true + g k false) := sum_prod_bool g
    _ = (g i true + g i false) := by
        refine Finset.prod_eq_single i (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ i) h)
        simp only [hg, if_neg hb]
        rw [add_comm]
        exact stepFactor_false_add_true p m s b
    _ = qRight p m s i := by simp [hg]

end SimJump
