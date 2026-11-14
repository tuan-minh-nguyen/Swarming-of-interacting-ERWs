import Swarm.Imports
import Swarm.EnvCore
import Swarm.Fcorr
import Swarm.ProjRec
import Swarm.Vdrift
import Swarm.Jsum
import Swarm.OccAssemble
import Swarm.Speed

open Finset Filter
open scoped BigOperators Topology

namespace SwarmJb

open SwarmOcc

/-- The paper's record-cost increment `J_{t+1}`, for a record `r` and a cap sequence `b`
(`b_n = b (r_n)` in the paper, with `b x = h_j(x-1) + 2`).

`J_{t+1} = F_{b_{t+1}}(X^i_{t+1} - r_{t+1}) - F_{b_t}(X^i_{t+1} - r_t)`. -/
noncomputable def Jinc (a ε : ℝ) (b : ℕ → ℝ) (X : ℕ → ℤ) (r : ℕ → ℕ) (t : ℕ) : ℝ :=
  Fcorr a ε (b (r (t + 1))) ((X (t + 1) : ℤ) - (r (t + 1) : ℤ)) -
    Fcorr a ε (b (r t)) ((X (t + 1) : ℤ) - (r t : ℤ))

/-- `F_b` vanishes on the nonpositive integers (`(Fdef)`: `F_b(g) = 0` for `g <= 0`). -/
lemma Fcorr_eq_zero_of_nonpos {a ε b : ℝ} {g : ℤ} (hg : g ≤ 0) : Fcorr a ε b g = 0 := by
  unfold Fcorr
  rw [Int.toNat_of_nonpos hg, Finset.range_zero, Finset.sum_empty]

/-- **The exact pointwise `(Jbound)` support**, with the paper's event
`{r_{t+1} = r_t + 1, X^i_{t+1} > r_t}`. -/
theorem Jinc_abs_le {a ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hε : 0 < ε)
    {b w : ℕ → ℝ} (hb : ∀ x, 0 ≤ b x) (hbw : ∀ x, b x ^ 2 ≤ w x)
    {X : ℕ → ℤ} {r : ℕ → ℕ} (hmono : ∀ t, r t ≤ r (t + 1))
    (hstep : ∀ t, r (t + 1) ≤ r t + 1) (t : ℕ) :
    |Jinc a ε b X r t| ≤
      (1 / (ε * (1 - a) ^ 2)) * (w (r t) + w (r t + 1)) *
        (if r (t + 1) = r t + 1 ∧ (r t : ℤ) < X (t + 1) then 1 else 0) := by
  unfold Jinc
  rcases eq_or_ne (r (t + 1)) (r t + 1) with hsucc | hsucc
  · rcases lt_or_ge ((r t : ℤ)) (X (t + 1)) with hx | hx
    · rw [if_pos ⟨hsucc, hx⟩]
      have hJ := J_abs_le (a := a) (ε := ε) (b0 := b (r t)) (b1 := b (r (t + 1)))
        ha0 ha1 (hb (r t)) (hb (r (t + 1))) hε
        ((X (t + 1) : ℤ) - (r t : ℤ)) ((X (t + 1) : ℤ) - (r (t + 1) : ℤ))
      have hbnd : (b (r (t + 1)) ^ 2 + b (r t) ^ 2) / (ε * (1 - a) ^ 2)
          ≤ (1 / (ε * (1 - a) ^ 2)) * (w (r t) + w (r t + 1)) * 1 := by
        rw [hsucc, mul_one, div_eq_mul_inv, one_div,
          mul_comm (ε * (1 - a) ^ 2)⁻¹ (w (r t) + w (r t + 1))]
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · have h1 : b (r t + 1) ^ 2 ≤ w (r t + 1) := hbw _
          have h2 : b (r t) ^ 2 ≤ w (r t) := hbw _
          linarith
        · have : (0 : ℝ) < 1 - a := by linarith
          positivity
      linarith
    · have hne : ¬ (r (t + 1) = r t + 1 ∧ (r t : ℤ) < X (t + 1)) := by
        intro hh; omega
      rw [if_neg hne, mul_zero]
      have h1 : (X (t + 1) : ℤ) - (r (t + 1) : ℤ) ≤ 0 := by omega
      have h2 : (X (t + 1) : ℤ) - (r t : ℤ) ≤ 0 := by omega
      rw [Fcorr_eq_zero_of_nonpos h1, Fcorr_eq_zero_of_nonpos h2, sub_zero, abs_zero]
  · have hrt : r (t + 1) = r t := by
      have h1 := hmono t; have h2 := hstep t; omega
    have hne : ¬ (r (t + 1) = r t + 1 ∧ (r t : ℤ) < X (t + 1)) := fun hh => hsucc hh.1
    rw [if_neg hne, mul_zero, hrt, sub_self, abs_zero]


/-! ### The combinatorial summation, indexed by walker `i`'s running maximum -/

/-- **`(Jbound)`, counting form with the correct spatial index.**

For a nondecreasing unit-step record `r`, a nonnegative weight `w`, and record costs supported
on the paper's event `{r_{t+1} = r_t + 1, X_{t+1} > r_t}`,

    sum_{t<n} |J_t| <= 2 C sum_{x < M+1} w x   (`J_t` is the paper's `J_{t+1}`)

whenever `X_t <= M` for `t <= n`.  The point of the position condition `X_{t+1} > r_t` is that
every advance value `r_t` is then `< M`, so the two injective record images
`r_t`, `r_t + 1` both land in `[0, M]`: the spatial sum is bounded by walker `i`'s running
maximum `M = M^i_n`, not by walker `j`'s record `r_n = M^j_n`.

This is the paper's step "for `t<n`, the event requires `r_t < M_n^i`, and there is at most one
increase from each value of `r_t`".  `SwarmOcc.Jsum_bound` instead produces the weaker
`2 C K (r_n + 2)` with `r_n = M^j_n`, which cannot be fed to the occupation assembly. -/
theorem Jsum_le_index {r : ℕ → ℕ} {X : ℕ → ℤ} {w : ℕ → ℝ} {C : ℝ} {J : ℕ → ℝ}
    (hmono : ∀ t, r t ≤ r (t + 1)) (hw : ∀ x, 0 ≤ w x) (hC : 0 ≤ C)
    (hJ : ∀ t, |J t| ≤ C * (w (r t) + w (r t + 1)) *
      (if r (t + 1) = r t + 1 ∧ (r t : ℤ) < X (t + 1) then 1 else 0))
    (n M : ℕ) (hX : ∀ t, t + 1 ≤ n → X (t + 1) ≤ (M : ℤ)) :
    ∑ t ∈ Finset.range n, |J t| ≤ 2 * C * ∑ x ∈ Finset.range (M + 1), w x := by
  classical
  set S : Finset ℕ :=
    (Finset.range n).filter (fun t => r (t + 1) = r t + 1 ∧ (r t : ℤ) < X (t + 1)) with hS
  have hSsub : S ⊆ (Finset.range n).filter (fun u => r (u + 1) = r u + 1) := by
    intro t ht
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨h1, h2⟩
  -- (1) the sum is supported on `S`
  have hstep1 : ∑ t ∈ Finset.range n, |J t|
      ≤ C * ∑ t ∈ S, (w (r t) + w (r t + 1)) := by
    have h1 : ∑ t ∈ Finset.range n, |J t|
        ≤ ∑ t ∈ Finset.range n, C * (w (r t) + w (r t + 1)) *
            (if r (t + 1) = r t + 1 ∧ (r t : ℤ) < X (t + 1) then 1 else 0) :=
      Finset.sum_le_sum fun t _ => hJ t
    have h2 : ∑ t ∈ Finset.range n, C * (w (r t) + w (r t + 1)) *
            (if r (t + 1) = r t + 1 ∧ (r t : ℤ) < X (t + 1) then 1 else 0)
        = C * ∑ t ∈ S, (w (r t) + w (r t + 1)) := by
      rw [hS, Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases hh : r (t + 1) = r t + 1 ∧ (r t : ℤ) < X (t + 1)
      · simp [hh]
      · simp [hh]
    linarith
  -- (2) every advance value and its successor lie below `M + 1`
  have hlt : ∀ t ∈ S, r t < M := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp ht
    have h4 : t + 1 ≤ n := by
      have := Finset.mem_range.mp h1; omega
    have h5 : X (t + 1) ≤ (M : ℤ) := hX t h4
    omega
  have hlt1 : ∀ t ∈ S, r t + 1 < M + 1 := by
    intro t ht
    exact Nat.succ_lt_succ (hlt t ht)
  -- (3) `t |-> r_t` is injective on `S`
  have hinj : ∀ s ∈ S, ∀ t ∈ S, r s = r t → s = t := by
    intro s hs t ht hst
    by_contra hne
    exact SwarmOcc.advance_inj hmono (hSsub hs) (hSsub ht) hne hst
  have hinj' : ∀ s ∈ S, ∀ t ∈ S, r s + 1 = r t + 1 → s = t := by
    intro s hs t ht hst
    exact hinj s hs t ht (by omega)
  -- (4) push to the spatial range
  have himg1 : ∑ t ∈ S, w (r t) = ∑ x ∈ S.image r, w x := (Finset.sum_image hinj).symm
  have himg2 : ∑ t ∈ S, w (r t + 1) = ∑ x ∈ S.image (fun t => r t + 1), w x :=
    (Finset.sum_image hinj').symm
  have hsub1 : S.image r ⊆ Finset.range (M + 1) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (hlt t ht))
  have hsub2 : S.image (fun t => r t + 1) ⊆ Finset.range (M + 1) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hlt1 t ht)
  have hb1 : ∑ x ∈ S.image r, w x ≤ ∑ x ∈ Finset.range (M + 1), w x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun x _ _ => hw x
  have hb2 : ∑ x ∈ S.image (fun t => r t + 1), w x ≤ ∑ x ∈ Finset.range (M + 1), w x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun x _ _ => hw x
  have hG : (0 : ℝ) ≤ ∑ x ∈ Finset.range (M + 1), w x := Finset.sum_nonneg fun x _ => hw x
  have hsplit : ∑ t ∈ S, (w (r t) + w (r t + 1))
      = (∑ t ∈ S, w (r t)) + (∑ t ∈ S, w (r t + 1)) := Finset.sum_add_distrib
  rw [hsplit, himg1, himg2] at hstep1
  nlinarith [hstep1, hb1, hb2, hG, hC]

/-- **`(Jbound)` with a linear spatial average.**  Adding the paper's `(spav)` input in
deterministic form, `sum_{x<m} w x <= K m` for every `m`:

    sum_{t<n} |J_t| <= 2 C K (M^i_n + 1),

which is the paper's `sum |J_{t+1}| <= C M^i_n + O(1)` with the explicit coefficient `2 C K`
and additive constant `2 C K`. -/
theorem Jsum_bound_index {r : ℕ → ℕ} {X : ℕ → ℤ} {w : ℕ → ℝ} {C K : ℝ} {J : ℕ → ℝ}
    (hmono : ∀ t, r t ≤ r (t + 1)) (hw : ∀ x, 0 ≤ w x) (hC : 0 ≤ C)
    (hJ : ∀ t, |J t| ≤ C * (w (r t) + w (r t + 1)) *
      (if r (t + 1) = r t + 1 ∧ (r t : ℤ) < X (t + 1) then 1 else 0))
    (hces : ∀ m : ℕ, ∑ x ∈ Finset.range m, w x ≤ K * (m : ℝ))
    (n M : ℕ) (hX : ∀ t, t + 1 ≤ n → X (t + 1) ≤ (M : ℤ)) :
    ∑ t ∈ Finset.range n, |J t| ≤ 2 * C * K * ((M : ℝ) + 1) := by
  have h1 := Jsum_le_index hmono hw hC hJ n M hX
  have hK : (0 : ℝ) ≤ K := by
    have h := hces 1
    simp only [Finset.sum_range_one, Nat.cast_one, mul_one] at h
    linarith [hw 0]
  have h2 : ∑ x ∈ Finset.range (M + 1), w x ≤ K * ((M : ℝ) + 1) := by
    have h := hces (M + 1)
    push_cast at h
    linarith
  have hG : (0 : ℝ) ≤ ∑ x ∈ Finset.range (M + 1), w x := Finset.sum_nonneg fun x _ => hw x
  have h3 : (0 : ℝ) ≤ 2 * C := by linarith
  have h4 : 2 * C * ∑ x ∈ Finset.range (M + 1), w x
      ≤ 2 * C * (K * ((M : ℝ) + 1)) := mul_le_mul_of_nonneg_left h2 h3
  nlinarith [h1, h4]

/-! ### `(Jbound)` for the actual record-cost increment, and the `runMax` form -/

/-- **`(Jbound)`**, the paper's display

    sum_{t<n} |J_{t+1}| <= C_eps sum_{x=0}^{M-1} h_j(x-1)^2 <= C M^i_n + O(1),

with the explicit coefficient `2 C_eps K`, `C_eps = 1/(ε(1-a)^2)`, additive constant
`2 C_eps K`, and the spatial index `M = M^i_n` of walker `i`.  The two inputs are the pointwise
bound `Jinc_abs_le` and the `(spav)`-type linear spatial bound `hces`; no probability is used. -/
theorem Jbound_of_spav {a ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hε : 0 < ε)
    {b w : ℕ → ℝ} (hb : ∀ x, 0 ≤ b x) (hw : ∀ x, 0 ≤ w x) (hbw : ∀ x, b x ^ 2 ≤ w x)
    {X : ℕ → ℤ} {r : ℕ → ℕ} (hmono : ∀ t, r t ≤ r (t + 1))
    (hstep : ∀ t, r (t + 1) ≤ r t + 1)
    {K : ℝ} (hces : ∀ m : ℕ, ∑ x ∈ Finset.range m, w x ≤ K * (m : ℝ))
    (n M : ℕ) (hX : ∀ t, t + 1 ≤ n → X (t + 1) ≤ (M : ℤ)) :
    ∑ t ∈ Finset.range n, |Jinc a ε b X r t| ≤
      2 * (1 / (ε * (1 - a) ^ 2)) * K * ((M : ℝ) + 1) := by
  have hden : (0 : ℝ) ≤ 1 / (ε * (1 - a) ^ 2) := by
    have : (0 : ℝ) < 1 - a := by linarith
    positivity
  exact Jsum_bound_index (J := fun t => Jinc a ε b X r t) (X := X)
    hmono hw hden
    (fun t => Jinc_abs_le (X := X) (r := r) ha0 ha1 hε hb hbw hmono hstep t) hces n M hX

/-- `((max 0 z.toNat : ℕ) : ℝ) = max 0 (z : ℝ)`: the natural-number running maximum used as a
summation index is the nonnegative part of the integer running maximum. -/
lemma natCast_max_toNat (z : ℤ) : ((max 0 z.toNat : ℕ) : ℝ) = max 0 (z : ℝ) := by
  rcases lt_or_ge z 0 with hz | hz
  · have h1 : z.toNat = 0 := Int.toNat_of_nonpos hz.le
    have h2 : ((max 0 z.toNat : ℕ) : ℝ) = 0 := by rw [h1]; simp
    have h3 : max 0 (z : ℝ) = 0 := by
      have h4 : (z : ℝ) ≤ 0 := by exact_mod_cast hz.le
      rw [max_eq_left h4]
    rw [h2, h3]
  · have h1 : (max 0 z.toNat : ℕ) = z.toNat := Nat.max_eq_right (Nat.zero_le _)
    have h2 : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
    have h3 : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    rw [h1, h3, max_eq_right h4]

/-- The integer running maximum is at most the natural index `max 0 z.toNat`. -/
lemma runMax_le_maxToNat (z : ℤ) : z ≤ ((max 0 z.toNat : ℕ) : ℤ) := by
  rcases lt_or_ge z 0 with hz | hz
  · have h1 : z.toNat = 0 := Int.toNat_of_nonpos hz.le
    have : (0 : ℤ) ≤ ((max 0 z.toNat : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
    omega
  · have h1 : (max 0 z.toNat : ℕ) = z.toNat := Nat.max_eq_right (Nat.zero_le _)
    have h2 : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
    omega

/-- **`(Jbound)` at the running maximum of walker `i`.**  Taking `M = M^i_n` (the positive part of
`SwarmSpeed.runMax X n`, which dominates `X_t` for every `t <= n`) gives

    sum_{t<n} |J_{t+1}| <= 2 C_eps K (max 0 (M^i_n) + 1).

This is the exact shape consumed by the occupation assembly, whose `hJ` premise is stated with
`(SwarmSpeed.runMax u n : ℝ)`. -/
theorem Jbound_runMax {a ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hε : 0 < ε)
    {b w : ℕ → ℝ} (hb : ∀ x, 0 ≤ b x) (hw : ∀ x, 0 ≤ w x) (hbw : ∀ x, b x ^ 2 ≤ w x)
    {X : ℕ → ℤ} {r : ℕ → ℕ} (hmono : ∀ t, r t ≤ r (t + 1))
    (hstep : ∀ t, r (t + 1) ≤ r t + 1)
    {K : ℝ} (hces : ∀ m : ℕ, ∑ x ∈ Finset.range m, w x ≤ K * (m : ℝ)) (n : ℕ) :
    ∑ t ∈ Finset.range n, |Jinc a ε b X r t| ≤
      2 * (1 / (ε * (1 - a) ^ 2)) * K * (max 0 ((SwarmSpeed.runMax X n : ℤ) : ℝ) + 1) := by
  have hX : ∀ t, t + 1 ≤ n → X (t + 1) ≤ ((max 0 (SwarmSpeed.runMax X n).toNat : ℕ) : ℤ) := by
    intro t ht
    have h1 : X (t + 1) ≤ SwarmSpeed.runMax X n := SwarmSpeed.le_runMax (by omega)
    exact le_trans h1 (runMax_le_maxToNat _)
  have h := Jbound_of_spav ha0 ha1 hε hb hw hbw hmono hstep hces n
    (max 0 (SwarmSpeed.runMax X n).toNat) hX
  rwa [natCast_max_toNat] at h

/-! ### The occupation assembly with an abstract coefficient on `M^i_n`

`SwarmOcc.occbnd_of_pieces` requires the `Z` and `J` premises at coefficient *exactly* `1`
(`Z n ≤ M n + δ n`, `J n ≤ M n + δ n`), so that the final coefficient of `M^i_n` is `2` and
`swarmSpeed.exists_kappa_of_occupation` can be run at `C = 2`.  But the paper's `(Jbound)`
coefficient `2 C_ε K` is *not* bounded by `1` — it grows like `1/ε` — and `(Vbound)`'s
coefficient `(1+a)/(1-a) + 1 + C_ε` is larger still.  The paper correspondingly carries an
arbitrary constant `C = C(m,p,ε)` in `(occbnd)`, and `κ = 7/(40 C)`.

The theorem below keeps that constant abstract: the coefficient of `M^i_n` is `A + B`, and the
covering argument is then run at `C = A + B`.  Nothing else changes. -/

/-- **`(occbnd)`, final step, with an abstract coefficient.**  From the summed drift inequality
and eventual bounds `Z n ≤ A M n + δ n`, `J n ≤ B M n + δ n`, `-(δ n) ≤ Q n`:

    Occ n <= (A + B) M n + (ε + 3 δ) n + max 0 (-Z_0). -/
theorem occbnd_of_pieces_coef {Occ Z J Q M : ℕ → ℝ} {ε δ A B : ℝ} {N : ℕ}
    (hdrift : ∀ n, Occ n ≤ ε * n + (Z n - Z 0) + J n - Q n)
    (hZ : ∀ n ≥ N, Z n ≤ A * M n + δ * n)
    (hJ : ∀ n ≥ N, J n ≤ B * M n + δ * n)
    (hQ : ∀ n ≥ N, -(δ * n) ≤ Q n) :
    ∀ n ≥ N, Occ n ≤ (A + B) * M n + (ε + 3 * δ) * n + max 0 (-(Z 0)) := by
  intro n hn
  have h1 := hdrift n
  have h2 := hZ n hn
  have h3 := hJ n hn
  have h4 := hQ n hn
  have h5 : -(Z 0) ≤ max 0 (-(Z 0)) := le_max_right _ _
  nlinarith

/-- **`(occbnd)` at `ε = 1/8`, abstract coefficient.**  With `ε = 1/32` in the drift inequality
and each of the three `o(n)` terms budgeted `n/64`, the occupation count satisfies

    Occ n <= max 1 (A + B) * M n + (1/8) n

eventually; the constant term `-Z_0` is absorbed once `n >= 64 max 0 (-Z_0)`. -/
theorem occbnd_coef {Occ Z J Q M : ℕ → ℝ} {A B : ℝ} {N : ℕ}
    (hM : ∀ n, 0 ≤ M n)
    (hdrift : ∀ n, Occ n ≤ (1 / 32) * n + (Z n - Z 0) + J n - Q n)
    (hZ : ∀ n ≥ N, Z n ≤ A * M n + (1 / 64) * n)
    (hJ : ∀ n ≥ N, J n ≤ B * M n + (1 / 64) * n)
    (hQ : ∀ n ≥ N, -((1 / 64) * n) ≤ Q n) :
    ∀ n ≥ max N ⌈64 * max 0 (-(Z 0))⌉₊, Occ n ≤ max 1 (A + B) * M n + (1 / 8) * n := by
  intro n hn
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have h1 := occbnd_of_pieces_coef (A := A) (B := B) (ε := 1 / 32) (δ := 1 / 64)
    hdrift hZ hJ hQ n hN
  have hc : max 0 (-(Z 0)) ≤ (n : ℝ) / 64 := by
    have h2 : (⌈64 * max 0 (-(Z 0))⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hn
    have h3 : 64 * max 0 (-(Z 0)) ≤ (⌈64 * max 0 (-(Z 0))⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have h4 : (A + B) * M n ≤ max 1 (A + B) * M n := by
    have h5 : A + B ≤ max 1 (A + B) := le_max_right _ _
    have h6 : 0 ≤ M n := hM n
    nlinarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [h1, h4, hc, hnn]

/-- **Proposition `ball` (lower half) from the four explicit premises with abstract
coefficients.**  Same as `SwarmOcc.speed_from_occupation_pieces`, but the `Z` and `J` premises
carry arbitrary coefficients `A`, `B`, `A'`, `B'`, and the covering argument is run at
`C = max 1 (max (A+B) (A'+B'))` so that `κ = 7/(40 C) > 0` without any numerical constraint on
`(spav)`'s constant. -/
theorem speed_from_pieces_coef (u v : ℕ → ℤ) (h0 : 0 ≤ u 0) (h0' : 0 ≤ v 0)
    {Z J Q Z' J' Q' : ℕ → ℝ} {N N' : ℕ} {A B A' B' : ℝ}
    (hdrift : ∀ n, SwarmSpeed.occ u (SwarmSpeed.runMax v) n
      ≤ (1 / 32) * n + (Z n - Z 0) + J n - Q n)
    (hZ : ∀ n ≥ N, Z n ≤ A * (SwarmSpeed.runMax u n : ℝ) + (1 / 64) * n)
    (hJ : ∀ n ≥ N, J n ≤ B * (SwarmSpeed.runMax u n : ℝ) + (1 / 64) * n)
    (hQ : ∀ n ≥ N, -((1 / 64) * n) ≤ Q n)
    (hdrift' : ∀ n, SwarmSpeed.occ v (SwarmSpeed.runMax u) n
      ≤ (1 / 32) * n + (Z' n - Z' 0) + J' n - Q' n)
    (hZ' : ∀ n ≥ N', Z' n ≤ A' * (SwarmSpeed.runMax v n : ℝ) + (1 / 64) * n)
    (hJ' : ∀ n ≥ N', J' n ≤ B' * (SwarmSpeed.runMax v n : ℝ) + (1 / 64) * n)
    (hQ' : ∀ n ≥ N', -((1 / 64) * n) ≤ Q' n)
    (hosc : Tendsto (fun n : ℕ => ((SwarmSpeed.runMax u n : ℝ) - (u n : ℝ)) / n)
      atTop (nhds 0)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (κ - ε) * n ≤ (u n : ℝ) := by
  set C : ℝ := max (max 1 (A + B)) (max 1 (A' + B')) with hCdef
  have hMu : ∀ n, (0 : ℝ) ≤ (SwarmSpeed.runMax u n : ℝ) := by
    intro n
    have h1 : u 0 ≤ SwarmSpeed.runMax u n := SwarmSpeed.le_runMax (Nat.zero_le n)
    have h2 : (u 0 : ℝ) ≤ (SwarmSpeed.runMax u n : ℝ) := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ (u 0 : ℝ) := by exact_mod_cast h0
    linarith
  have hMv : ∀ n, (0 : ℝ) ≤ (SwarmSpeed.runMax v n : ℝ) := by
    intro n
    have h1 : v 0 ≤ SwarmSpeed.runMax v n := SwarmSpeed.le_runMax (Nat.zero_le n)
    have h2 : (v 0 : ℝ) ≤ (SwarmSpeed.runMax v n : ℝ) := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ (v 0 : ℝ) := by exact_mod_cast h0'
    linarith
  have hC1 : (1 : ℝ) ≤ C := by
    have h1 : (1 : ℝ) ≤ max 1 (A + B) := le_max_left _ _
    have h2 : max 1 (A + B) ≤ C := le_max_left _ _
    linarith
  -- convert the abstract-coefficient occupation bounds to the single coefficient `C`
  have hocc : ∀ n ≥ max N ⌈64 * max 0 (-(Z 0))⌉₊,
      SwarmSpeed.occ u (SwarmSpeed.runMax v) n
        ≤ C * (SwarmSpeed.runMax u n : ℝ) + (1 / 8) * n := by
    intro n hn
    have h1 := occbnd_coef (M := fun m => (SwarmSpeed.runMax u m : ℝ)) hMu
      hdrift hZ hJ hQ n hn
    have h2 : max 1 (A + B) ≤ C := le_max_left _ _
    have h3 : max 1 (A + B) * (SwarmSpeed.runMax u n : ℝ)
        ≤ C * (SwarmSpeed.runMax u n : ℝ) :=
      mul_le_mul_of_nonneg_right h2 (hMu n)
    linarith
  have hocc' : ∀ n ≥ max N' ⌈64 * max 0 (-(Z' 0))⌉₊,
      SwarmSpeed.occ v (SwarmSpeed.runMax u) n
        ≤ C * (SwarmSpeed.runMax v n : ℝ) + (1 / 8) * n := by
    intro n hn
    have h1 := occbnd_coef (M := fun m => (SwarmSpeed.runMax v m : ℝ)) hMv
      hdrift' hZ' hJ' hQ' n hn
    have h2 : max 1 (A' + B') ≤ C := le_max_right _ _
    have h3 : max 1 (A' + B') * (SwarmSpeed.runMax v n : ℝ)
        ≤ C * (SwarmSpeed.runMax v n : ℝ) :=
      mul_le_mul_of_nonneg_right h2 (hMv n)
    linarith
  exact SwarmSpeed.exists_kappa_of_occupation (u := u) (v := v) (h0 := h0) (C := C) hC1
    (N := max (max N ⌈64 * max 0 (-(Z 0))⌉₊) (max N' ⌈64 * max 0 (-(Z' 0))⌉₊))
    (hocc := fun n hn => hocc n (le_trans (le_max_left _ _) hn))
    (hocc' := fun n hn => hocc' n (le_trans (le_max_right _ _) hn))
    (hosc := hosc)

/-! ### Two deterministic bookkeeping lemmas for the two hypotheses of `(Jbound)` -/

/-- The revealed-potential bound `b x ^ 2 <= w x` is met by the paper's own choice
`b x = h_j(x-1) + 2`, `w x = 9 h_j(x-1)^2`, because `h_j >= 1` (both branches of `(hrec)`
give `h_j(x) >= 1`).  This is the lemma that makes `hbw` instantiable in the model. -/
lemma sq_add_two_le_nine_mul_sq {t : ℝ} (ht : 1 ≤ t) : (t + 2) ^ 2 ≤ 9 * t ^ 2 := by
  nlinarith [sq_nonneg (t - 1)]

/-- The `(spav)`-type input in the form used by `Jsum_bound_index` follows from its
`limsup` form `sum_{x<m} w x <= K m` **eventually**: the finitely many small `m` are absorbed
into the constant.  This is exactly the passage from the paper's
`limsup_{r} r^{-1} sum_{x<r} h_j(x)^2 <= C` to a `K` valid for every `m`. -/
lemma hces_of_eventually {w : ℕ → ℝ} (hw : ∀ x, 0 ≤ w x) {K : ℝ} {m0 : ℕ}
    (h : ∀ m ≥ m0, ∑ x ∈ Finset.range m, w x ≤ K * (m : ℝ)) :
    ∃ K' : ℝ, ∀ m : ℕ, ∑ x ∈ Finset.range m, w x ≤ K' * (m : ℝ) := by
  refine ⟨|K| + ∑ x ∈ Finset.range m0, w x, fun m => ?_⟩
  have hS : (0 : ℝ) ≤ ∑ x ∈ Finset.range m0, w x := Finset.sum_nonneg fun x _ => hw x
  have hK' : (0 : ℝ) ≤ |K| + ∑ x ∈ Finset.range m0, w x := by positivity
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · rcases lt_or_ge m m0 with hm0 | hm0
    · -- small `m`: absorb the initial spatial sum into the constant
      have h2 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h3 : ∑ x ∈ Finset.range m, w x ≤ ∑ x ∈ Finset.range m0, w x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hm0.le)
          fun x _ _ => hw x
      have h4 : ∑ x ∈ Finset.range m0, w x
          ≤ (|K| + ∑ x ∈ Finset.range m0, w x) * (m : ℝ) := by
        have h5 : ∑ x ∈ Finset.range m0, w x
            ≤ (|K| + ∑ x ∈ Finset.range m0, w x) * 1 := by linarith [abs_nonneg K]
        nlinarith [h5, hK', h2]
      linarith
    · -- large `m`: the assumed linear bound, with `K <= K'`
      have h1 := h m hm0
      have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h3 : K ≤ |K| + ∑ x ∈ Finset.range m0, w x := by
        have := le_abs_self K; linarith
      have : K * (m : ℝ) ≤ (|K| + ∑ x ∈ Finset.range m0, w x) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right h3 h2
      linarith

/-- **The `hJ` premise of the occupation assembly, from `(Jbound)`.**

`SwarmOcc.occbnd_of_pieces` consumes `J n <= M n + δ n` with `M n = M^i_n` the running maximum of
walker `i`.  `Jbound_runMax` gives the summed record cost up to the explicit constant
`(2 C_ε K) (M^i_n + 1)`.  Hence the premise holds at any `δ n >= 1` **provided**

* `M^i_n >= 0` (true for all large `n` once walker `j` is transient, which is now proved), and
* the numerical constraint `2 C_ε K <= 1`.

The second condition is the honest residual: the paper does not assert it (its `(occbnd)`
coefficient `C(m,p,ε)` is arbitrary and grows like `1/ε`), which is why
`occbnd_of_pieces_coef` keeps the coefficient abstract instead. -/
theorem Jbound_hJ_shape {a ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hε : 0 < ε)
    {b w : ℕ → ℝ} (hb : ∀ x, 0 ≤ b x) (hw : ∀ x, 0 ≤ w x) (hbw : ∀ x, b x ^ 2 ≤ w x)
    {X : ℕ → ℤ} {r : ℕ → ℕ} (hmono : ∀ t, r t ≤ r (t + 1))
    (hstep : ∀ t, r (t + 1) ≤ r t + 1)
    {K : ℝ} (hces : ∀ m : ℕ, ∑ x ∈ Finset.range m, w x ≤ K * (m : ℝ))
    {δ : ℝ} (hδ : 1 ≤ δ) (n : ℕ)
    (hMnn : 0 ≤ (SwarmSpeed.runMax X n : ℝ))
    (hcoef : 2 * (1 / (ε * (1 - a) ^ 2)) * K ≤ 1) :
    ∑ t ∈ Finset.range n, |Jinc a ε b X r t| ≤ (SwarmSpeed.runMax X n : ℝ) + δ * n := by
  have h := Jbound_runMax (X := X) (r := r) ha0 ha1 hε hb hw hbw hmono hstep hces n
  have h1 : max 0 ((SwarmSpeed.runMax X n : ℤ) : ℝ) = (SwarmSpeed.runMax X n : ℝ) :=
    max_eq_right hMnn
  rw [h1] at h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using hMnn
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (1 : ℝ) ≤ δ * (n : ℝ) := by nlinarith
    have h3 : 2 * (1 / (ε * (1 - a) ^ 2)) * K * ((SwarmSpeed.runMax X n : ℝ) + 1)
        ≤ 1 * ((SwarmSpeed.runMax X n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hcoef (by linarith)
    nlinarith [h, h2, h3]

end SwarmJb
