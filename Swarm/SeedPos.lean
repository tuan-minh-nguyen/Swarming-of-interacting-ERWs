/-
# `P(V) > 0`: the seed probability of the regeneration event

This is the paper's proof that `P(V) > 0` (`V` = every walker is strictly positive at every
positive time), for the actual i.i.d. array law.

Given the finite prefix `γ` and the state `s = pathState γ` with
`P(prefix γ and future from s nonnegative) > 0` (from transience, `exists_prefix_state`), build
the paper's prescribed path: go uphill to level `t+1`, then replay `γ` translated by `t+1`.  At
time `L = 2t+1` the state `sC` of that path is the state `s` translated up by `K = t+1`
(`ShiftAgree K sC s`, using `Swarming.Paths.localTime_prescribed` for the local-time identity).
Then

* the prescribed prefix is a finite cylinder of positive mass (`measure_follows_ne_zero`);
* the future from `sC` stays above `K` with the same probability as the future from `s` stays
  above `0` (`future_ge_transfer`) — positive;
* the future event depends only on the coordinates outside the prefix cylinder
  (`future_determined`), so the two factorise (`cylinder_factor`).

On the intersection the whole path is: `0` at time `0`, at least `1` at times `1, …, L`
(prescribed, strictly positive by construction) and at least `K ≥ 1` after `L`.  This is exactly
`strictPos`, so its probability is positive.
-/
import Swarm.SeedExistsState
import Swarm.FreshLaw

open MeasureTheory Set ProbabilityTheory Filter
open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory SwarmRestart SwarmFresh

namespace SwarmSeed

variable {N : ℕ}

/-! ### Elementary facts about the actual trajectory -/

theorem trajectory_step (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    (trajectory p m U (n + 1)).pos i = (trajectory p m U n).pos i
      + drivenStep (U (departureCoord p m U n i))
        (rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i)) := rfl

theorem drivenStep_eq_one_or_neg (u α : ℝ) : drivenStep u α = 1 ∨ drivenStep u α = -1 := by
  unfold drivenStep
  split_ifs <;> simp

/-- The position of every walker stays within `[-n, n]`. -/
theorem trajectory_bounds (p : ℝ) (m : ℕ) (U : Array N) (n : ℕ) (i : Fin N) :
    -((n : ℤ)) ≤ (trajectory p m U n).pos i ∧ (trajectory p m U n).pos i ≤ (n : ℤ) := by
  induction n with
  | zero =>
      rw [trajectory_zero]
      simp [initialWalkState]
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [trajectory_step]
      rcases drivenStep_eq_one_or_neg (U (departureCoord p m U n i))
        (rightProbability p m (trajectory p m U n).ell i ((trajectory p m U n).pos i)) with h | h
      · rw [h]; push_cast; omega
      · rw [h]; push_cast; omega

theorem two_t_add_one_not_le {t : ℕ} (h : t ≠ 0) : ¬ (2 * t + 1 ≤ t + 1) := by omega

theorem two_t_add_one_sub (t : ℕ) : 2 * t + 1 - (t + 1) = t := by omega

/-- Local times are monotone in time. -/
theorem localTime_mono {σ : Type*} [DecidableEq σ] (X : ℕ → σ) (x : σ) {n m : ℕ} (h : n ≤ m) :
    localTime X n x ≤ localTime X m x := by
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  exact ⟨by omega, hk.2⟩

/-! ### The seed probability -/

/-- **`P(V) > 0`** for the actual i.i.d. array law: the fresh path is strictly positive at every
positive time with positive probability. -/
theorem strictPos_measure_ne_zero {p : ℝ} (hp0 : 1 / 2 < p) (hp1 : p < 1) {m : ℕ} (hm : 2 ≤ m)
    (hN : 2 ≤ N) :
    (arrayMeasure N) {U : Array N | posPath p m U ∈ strictPos (N := N)} ≠ 0 := by
  obtain ⟨t, γ, hγ⟩ := exists_prefix_state (N := N) (p := p) (m := m) hp0 hp1 hm hN
  have hnonempty : (Pref (N := N) p m γ ∩ FutureGe p m (pathState γ) 0).Nonempty := by
    refine Set.nonempty_iff_ne_empty.mpr ?_
    intro h
    exact hγ (by rw [h]; simp)
  obtain ⟨U₀, hU₀⟩ := hnonempty
  obtain ⟨hPref, hFut⟩ := hU₀
  -- the extended finite path and the prescribed path
  set γe : ℕ → Fin N → ℤ :=
    fun u i => if h : u ≤ t then γ ⟨u, Nat.lt_succ_of_le h⟩ i
      else γ ⟨t, Nat.lt_succ_self t⟩ i + (((u - t : ℕ)) : ℤ) with hγe
  set η : ℕ → Fin N → ℤ := fun n i => Swarming.Paths.prescribed (fun u => γe u i) t n with hη
  set K : ℤ := (t : ℤ) + 1 with hK
  set L : ℕ := 2 * t + 1 with hL
  set sC : WalkState N := ⟨η L, dt η L⟩ with hsC
  -- the finite path agrees with the actual trajectory up to `t`
  have hγe_traj : ∀ (u : ℕ), u ≤ t → ∀ i, γe u i = (trajectory p m U₀ u).pos i := by
    intro u hu i
    simp only [hγe, dif_pos hu]
    exact (hPref ⟨u, Nat.lt_succ_of_le hu⟩ i).symm
  have hγe_zero : ∀ i, γe 0 i = 0 := by
    intro i
    rw [hγe_traj 0 (Nat.zero_le t) i, trajectory_zero]
    rfl
  have hγeext : ∀ (u : ℕ), u ≤ t → ∀ i, γe u i = extendPath γ u i := by
    intro u hu i
    rw [hγe_traj u hu i, extendPath, dif_pos hu]
    exact hPref ⟨u, Nat.lt_succ_of_le hu⟩ i
  -- nearest-neighbour steps of the extended path
  have hγe_step : ∀ (u : ℕ) (i : Fin N),
      γe (u + 1) i = γe u i + 1 ∨ γe (u + 1) i = γe u i - 1 := by
    intro u i
    rcases Nat.lt_or_ge u t with hu | hu
    · rw [hγe_traj u (le_of_lt hu) i, hγe_traj (u + 1) hu i, trajectory_step]
      rcases drivenStep_eq_one_or_neg (U₀ (departureCoord p m U₀ u i))
        (rightProbability p m (trajectory p m U₀ u).ell i
          ((trajectory p m U₀ u).pos i)) with h | h
      · rw [h]; left; ring
      · rw [h]; right; ring
    · have h1 : γe u i = γ ⟨t, Nat.lt_succ_self t⟩ i + (((u - t : ℕ)) : ℤ) := by
        by_cases hut : u ≤ t
        · rw [show u = t from le_antisymm hut hu]
          simp only [hγe, dif_pos le_rfl, Nat.sub_self]
          push_cast
          ring
        · simp only [hγe, dif_neg hut]
      have hnu : ¬ (u + 1 ≤ t) := by omega
      have h2 : γe (u + 1) i = γ ⟨t, Nat.lt_succ_self t⟩ i + ((((u + 1) - t : ℕ)) : ℤ) := by
        simp only [hγe, dif_neg hnu]
      rw [h1, h2]
      have hidx : ((u + 1) - t : ℕ) = (u - t) + 1 := by omega
      rw [hidx]
      push_cast
      left
      ring
  -- the prescribed path starts at the origin
  have hη0 : ∀ i, η 0 i = 0 := by
    intro i
    simp only [hη, Swarming.Paths.prescribed, if_pos (by omega : 0 ≤ t + 1)]
    simp
  -- the prescribed path has nearest-neighbour steps
  have hηstep : ∀ (n : ℕ), n < L → ∀ i : Fin N,
      η (n + 1) i = η n i + 1 ∨ η (n + 1) i = η n i - 1 := by
    intro n _ i
    by_cases hle : n + 1 ≤ t + 1
    · have h1 : η n i = ((n : ℕ) : ℤ) := by
        simp only [hη, Swarming.Paths.prescribed, if_pos (by omega : n ≤ t + 1)]
      have h2 : η (n + 1) i = (((n + 1 : ℕ)) : ℤ) := by
        simp only [hη, Swarming.Paths.prescribed, if_pos hle]
      rw [h1, h2]
      push_cast
      left
      ring
    · have h1 : η n i = K + γe (n - (t + 1)) i := by
        by_cases hnt : n ≤ t + 1
        · have hn' : n = t + 1 := by omega
          subst hn'
          simp only [hη, Swarming.Paths.prescribed, if_pos le_rfl, hK]
          have hz : (t + 1 - (t + 1) : ℕ) = 0 := by omega
          rw [hz, hγe_zero i]
          push_cast
          ring
        · simp only [hη, Swarming.Paths.prescribed, if_neg hnt, hK]
      have h2 : η (n + 1) i = K + γe (n + 1 - (t + 1)) i := by
        simp only [hη, Swarming.Paths.prescribed, if_neg (by omega : ¬ n + 1 ≤ t + 1), hK]
      rw [h1, h2]
      have hidx : n + 1 - (t + 1) = (n - (t + 1)) + 1 := by omega
      rw [hidx]
      rcases hγe_step (n - (t + 1)) i with hs | hs
      · rw [hs]; left; ring
      · rw [hs]; right; ring
  -- the prescribed path is at least `1` at positive times up to `L`
  have hη_ge_one : ∀ (n : ℕ), 1 ≤ n → n ≤ L → ∀ i, 1 ≤ η n i := by
    intro n hn1 hnL i
    by_cases hnt : n ≤ t + 1
    · have h1 : η n i = ((n : ℕ) : ℤ) := by
        simp only [hη, Swarming.Paths.prescribed, if_pos hnt]
      rw [h1]
      exact_mod_cast hn1
    · have h1 : η n i = K + γe (n - (t + 1)) i := by
        simp only [hη, Swarming.Paths.prescribed, if_neg hnt, hK]
      have hu : n - (t + 1) ≤ t := by omega
      have h2 : γe (n - (t + 1)) i = (trajectory p m U₀ (n - (t + 1))).pos i :=
        hγe_traj _ hu i
      have hb : -(((n - (t + 1) : ℕ)) : ℤ)
          ≤ (trajectory p m U₀ (n - (t + 1))).pos i :=
        (trajectory_bounds p m U₀ (n - (t + 1)) i).1
      have hu2 : (((n - (t + 1) : ℕ)) : ℤ) ≤ (t : ℤ) := by
        exact_mod_cast hu
      have hstep1 : η n i = K + (trajectory p m U₀ (n - (t + 1))).pos i := by rw [h1, h2]
      rw [hstep1, hK]
      have hb' : -((t : ℤ)) ≤ (trajectory p m U₀ (n - (t + 1))).pos i := by omega
      omega
  -- the state at time `L` is the translated state `s`
  have hshift : ShiftAgree K sC (pathState γ) := by
    constructor
    · intro i
      have h1 : η L i = K + γe (t) i := by
        rw [hL, hη]
        by_cases h0 : t = 0
        · subst h0
          simp only [Swarming.Paths.prescribed, if_pos le_rfl, hγe_zero i, hK]
          push_cast
        · simp only [Swarming.Paths.prescribed, if_neg (two_t_add_one_not_le h0),
            two_t_add_one_sub t, hK]
      have hγet : γe t i = γ ⟨t, Nat.lt_succ_self t⟩ i := by
        simp only [hγe, dif_pos le_rfl]
      show η L i = K + (pathState γ).pos i
      rw [h1, hγet, pathState_pos]
    · intro i x hx
      have hpath : (fun u => η u i) = Swarming.Paths.prescribed (fun u => γe u i) t := by
        funext u
        simp only [hη]
      have hpres := Swarming.Paths.localTime_prescribed (fun u => γe u i) (hγe_zero i)
        (t := t) (x := x) hx
      have h2 : Swarming.localTime (fun u => η u i) L (K + x)
          = Swarming.localTime (fun u => γe u i) t x := by
        rw [hpath]
        exact hpres.symm
      have h3 : Swarming.localTime (fun u => γe u i) t x = dt (extendPath γ) t i x := by
        have hleft : Swarming.localTime (fun u => γe u i) t x
            = ((Finset.range (t + 1)).filter (fun u => γe u i = x)).card := rfl
        have hright : dt (extendPath γ) t i x
            = ((Finset.range (t + 1)).filter (fun u => extendPath γ u i = x)).card := rfl
        rw [hleft, hright]
        congr 1
        apply Finset.filter_congr
        intro u hu
        rw [Finset.mem_range] at hu
        have hu' : u ≤ t := by omega
        simp only [hγeext u hu' i]
      show dt η L i (K + x) = (pathState γ).ell i x
      simp only [hsC, dt, pathState]
      rw [h2, h3]
      rfl
  -- the coordinate bookkeeping for the block factorisation
  have hQ : ∀ (i : Fin N) (x : ℤ) (k : ℕ), (i, x, k) ∈ dcoordSet η L → 0 ≤ x →
      k ≤ sC.ell i x := by
    intro i x k hmem _
    obtain ⟨⟨n, i'⟩, -, heq⟩ := Finset.mem_image.mp hmem
    have hi : i = i' := by
      have h := congrArg (fun c : Fin N × ℤ × ℕ => c.1) heq
      simpa only [dcoord] using h.symm
    have hx : x = η n i' := by
      have h := congrArg (fun c : Fin N × ℤ × ℕ => c.2.1) heq
      simpa only [dcoord] using h.symm
    have hk : k = dt η n i' (η n i') := by
      have h := congrArg (fun c : Fin N × ℤ × ℕ => c.2.2) heq
      simpa only [dcoord] using h.symm
    rw [hx, hk, hi]
    simp only [hsC, dt]
    exact localTime_mono (fun u => η u i') (η n i') (Nat.le_of_lt n.isLt)
  have hQ0 : ∀ i : Fin N, (i, sC.pos i, sC.ell i (sC.pos i)) ∉ dcoordSet η L := by
    intro i hmem
    obtain ⟨⟨n, i'⟩, -, heq⟩ := Finset.mem_image.mp hmem
    have hcoord : dcoord η (n : ℕ) i' = dcoord η L i := by
      rw [heq]
      simp only [hsC, dcoord]
    obtain ⟨hn, -⟩ := dcoord_inj hcoord
    omega
  -- the factorisation and the transplant
  have hfac := cylinder_factor (C := follows p m η L) (Φ := FutureGe p m sC K)
    (measurableSet_follows p m η L) (measurableSet_FutureGe p m sC K)
    (Q := dcoordSet η L)
    (fun U U' h => follows_determined h)
    (fun U U' h => future_determined (Q := dcoordSet η L) (d := K) (by rw [hK]; positivity) hQ hQ0 h)
  have htrans := future_ge_transfer (p := p) (m := m) (d := K) (a := sC) (b := pathState γ) hshift
  have hne0 : (arrayMeasure N) (FutureGe p m (pathState γ) 0) ≠ 0 := by
    intro h0
    refine hγ (le_antisymm ?_ (bot_le))
    rw [← h0]
    exact measure_mono (fun U hU => hU.2)
  have hneF : (arrayMeasure N) (FutureGe p m sC K) ≠ 0 := by
    rw [← htrans]
    exact hne0
  have hprod : (arrayMeasure N) (follows p m η L ∩ FutureGe p m sC K) ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero (measure_follows_ne_zero hp0 hp1 m η L) hneF
  -- the intersection is contained in `strictPos`
  have hsub : follows p m η L ∩ FutureGe p m sC K ⊆
      {U : Array N | posPath p m U ∈ strictPos (N := N)} := by
    intro U hU
    obtain ⟨hfol, hfut⟩ := hU
    have hposL : ∀ n, n ≤ L → ∀ i, (trajectory p m U n).pos i = η n i := by
      have h := hfol
      rw [trajectory_eq_of_follows (p := p) (m := m) (η := η) (L := L) hη0 hηstep] at h
      exact h
    have hstate : trajectory p m U L = sC := by
      refine walkState_ext ?_ ?_
      · funext i
        rw [hposL L le_rfl i, hsC]
      · funext i y
        have hell := ell_eq_dt (p := p) (m := m) (η := η) (U := U) (n := L) hposL
        rw [hell i y, hsC]
    have hK1 : (1 : ℤ) ≤ K := by rw [hK]; omega
    refine mem_strictPos.mpr ⟨fun i => ?_, fun n hn i => ?_⟩
    · show (trajectory p m U 0).pos i = 0
      rw [hposL 0 (by omega) i, hη0 i]
    · show 0 < (trajectory p m U n).pos i
      rcases Nat.lt_or_ge n (L + 1) with hlt | hge
      · rw [hposL n (by omega) i]
        exact hη_ge_one n (by omega) (by omega) i
      · have hfu := hfut (n - L) i
        have htr : (trajectory p m U n).pos i = (trajFrom p m U sC (n - L)).pos i := by
          conv_lhs => rw [show n = L + (n - L) from by omega]
          rw [trajectory_add, hstate]
        rw [htr]
        omega
  intro hzero
  exact hprod (le_antisymm (hzero ▸ measure_mono hsub) (bot_le))

end SwarmSeed
