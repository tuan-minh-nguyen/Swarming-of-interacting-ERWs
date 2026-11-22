import SwarmDiameter.TwoWalkerPassage
import SwarmDiameter.RecordDownwardCrossing
import SwarmDiameter.PathDiameter
import Swarm.RestartRecord
import Swarm.SepWindow

open Finset Set Swarming.Uniform Swarming.Trajectory Swarming.Enl SwarmRecordMeas.Actual SwarmRestart

set_option autoImplicit false

namespace Swarming.Diameter

/-- A large diameter after both walkers reach the initial record entails
an ordered pair of passages, provided no downward crossing occurs. -/
theorem exists_passage_order_of_large_diameter {p : ℝ} {m r H x k η t : ℕ} {U : Array 2}
    (hU : U ∈ ReachAll p m) (hx : 1 ≤ x) (hk : k < x) (hr : 5 * x ≤ r)
    (hη : recTimeA p m U r ≤ η) (ht : η ≤ t) (hT : t ≤ recTimeA p m U r + H)
    (hinit : ∀ i : Fin 2, ((r - x : ℕ) : ℤ) ≤ (trajectory p m U η).pos i ∧
      (r : ℤ) ≤ runMax p m U i η ∧ runMax p m U i η ≤ (r : ℤ) + (x : ℤ))
    (hmax : ∀ (i : Fin 2) (u : ℕ), η ≤ u → u ≤ t → runMax p m U i u ≤ ((r + H : ℕ) : ℤ))
    (hno : U ∉ recordDownwardExcursion p m r (r - x) (r + H) H k)
    (hdiam : 4 * (x : ℝ) + (k : ℝ) < pathDiameter t (posPath p m U)) :
    ∃ (i j : Fin 2) (v h : ℕ), i ≠ j ∧ v ≤ H ∧ r ≤ h ∧ h ≤ r + H ∧
      U ∈ frontReachesBeforeExit p m r v (h - 5 * x) (h - 1) i j (x : ℝ) := by
  classical
  let σ := recTimeA p m U r
  let X (i : Fin 2) (s : ℕ) := (trajectory p m U s).pos i
  let M (i : Fin 2) (s : ℕ) := runMax p m U i s
  have hησ : σ ≤ η := hη
  have htσ : t ≤ σ + H := hT
  have hdStep (i j : Fin 2) (s : ℕ) : M i (s + 1) - M j (s + 1) ≤ M i s - M j s + 1 := by
    have hi : M i (s + 1) ≤ M i s + 1 := LocSepWindow.runMax_succ_le p m U i s
    have hj : M j s ≤ M j (s + 1) := runMax_mono p m U j (Nat.le_succ _)
    omega
  have hinitGap (i j : Fin 2) : M i η - M j η ≤ (x : ℤ) := by
    have hi : M i η ≤ (r : ℤ) + (x : ℤ) := (hinit i).2.2
    have hj : (r : ℤ) ≤ M j η := (hinit j).2.1
    omega
  have hdown (i j : Fin 2) (hij : i ≠ j) (z s u : ℕ) (hz : z ∈ Finset.Icc (r - x) (r + H))
      (hs : σ ≤ s) (hsu : s ≤ u) (hu : u ≤ t) (hX : (z : ℤ) ≤ X i s) (hM : (z : ℤ) ≤ M j s) :
      (z : ℤ) - (k : ℤ) ≤ X i u := by
    by_contra! h
    exact hno ⟨hU, i, j, hij, z, hz, s, u, hs, hsu, hu.trans htσ, hX, hM, h⟩
  have hlag (u : ℕ) (hηu : η ≤ u) (hut : u ≤ t)
      (hgap : ∀ s : ℕ, η ≤ s → s ≤ u → ∀ i j : Fin 2, M i s - M j s ≤ 2 * (x : ℤ))
      (i : Fin 2) : M i u - X i u ≤ 2 * (x : ℤ) + (k : ℤ) := by
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by decide : 1 < Fintype.card (Fin 2)) i
    have hjLo : ((r - x : ℕ) : ℤ) ≤ M j η := (hinit j).1.trans (le_runMax p m U j η)
    by_cases hi : M i u ≤ (r : ℤ) + (x : ℤ)
    · have hlo := hdown i j hji.symm (r - x) η u (mem_Icc.mpr ⟨le_rfl, by omega⟩)
        hησ hηu hut (hinit i).1 hjLo
      rw [Nat.cast_sub (by omega : x ≤ r)] at hlo
      omega
    · obtain ⟨s, hsu, heq⟩ := exists_eq_runMax p m U i u
      have heq : X i s = M i u := heq
      have hηs : η ≤ s := by
        by_contra! hs
        have hsmax : X i s ≤ M i η := (le_runMax p m U i s).trans (runMax_mono p m U i hs.le)
        have hinit' : M i η ≤ (r : ℤ) + (x : ℤ) := (hinit i).2.2
        omega
      have hes : X i s = M i s := le_antisymm (le_runMax p m U i s)
        (heq.symm ▸ runMax_mono p m U i hsu)
      let z : ℤ := min (M i s) (M j s)
      have hzM (a : Fin 2) : (r : ℤ) ≤ M a s := (hinit a).2.1.trans (runMax_mono p m U a hηs)
      have hz : (r : ℤ) ≤ z := le_min (hzM i) (hzM j)
      have hz' : (z.toNat : ℤ) = z := Int.toNat_of_nonneg ((Int.natCast_nonneg r).trans hz)
      have hzup : z ≤ ((r + H : ℕ) : ℤ) := (min_le_left _ _).trans (hmax i s hηs (hsu.trans hut))
      have hzI : z.toNat ∈ Finset.Icc (r - x) (r + H) :=
        mem_Icc.mpr ⟨by exact_mod_cast (show ((r - x : ℕ) : ℤ) ≤ (z.toNat : ℤ) by
          rw [hz']; exact (by exact_mod_cast Nat.sub_le r x : ((r - x : ℕ) : ℤ) ≤ (r : ℤ)).trans hz),
          by exact_mod_cast hz'.le.trans hzup⟩
      have hX : (z.toNat : ℤ) ≤ X i s := hz'.le.trans ((min_le_left _ _).trans_eq hes.symm)
      have hMj : (z.toNat : ℤ) ≤ M j s := hz'.le.trans (min_le_right _ _)
      have hl := hdown i j hji.symm z.toNat s u hzI (hησ.trans hηs) hsu hut hX hMj
      rw [hz'] at hl
      have hg := hgap s hηs hsu i j
      have hMi : M i u = M i s := heq.symm.trans hes
      change min (M i s) (M j s) - (k : ℤ) ≤ X i u at hl
      rw [hMi]
      omega
  have hex : ∃ u : ℕ, η ≤ u ∧ u ≤ t ∧ ∃ i j : Fin 2, 2 * (x : ℤ) ≤ M i u - M j u := by
    by_contra! h
    have hgap (s : ℕ) (hs : η ≤ s) (hst : s ≤ t) (i j : Fin 2) :
        M i s - M j s ≤ 2 * (x : ℤ) := (h s hs hst i j).le
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (X · t)
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (X · t)
    have hd : pathDiameter t (posPath p m U) = (X i t - X j t : ℤ) := by
      unfold pathDiameter LeaderDescent.spreadZ
      congr 1
      exact congrArg₂ (· - ·) hi hj
    have hle := hgap t ht le_rfl i j
    have hjlag := hlag t ht le_rfl hgap j
    have hiMax : X i t ≤ M i t := le_runMax p m U i t
    have hdist : X i t - X j t ≤ 4 * (x : ℤ) + (k : ℤ) := by omega
    rw [hd] at hdiam
    exact (not_lt_of_ge (by exact_mod_cast hdist)) hdiam
  let u := Nat.find hex
  have hu : η ≤ u ∧ u ≤ t ∧ ∃ i j : Fin 2, 2 * (x : ℤ) ≤ M i u - M j u := Nat.find_spec hex
  obtain ⟨i, j, hijU⟩ := hu.2.2
  have hηu : η < u := lt_of_le_of_ne hu.1 fun he => by
    have h := hinitGap i j
    rw [he] at h
    omega
  have hgBefore (w : ℕ) (hηw : η ≤ w) (hwu : w < u) (i j : Fin 2) :
      M i w - M j w < 2 * (x : ℤ) :=
    lt_of_not_ge fun h => Nat.find_min hex hwu ⟨hηw, hwu.le.trans hu.2.1, i, j, h⟩
  have hgU (w : ℕ) (hηw : η ≤ w) (hwu : w ≤ u) (a b : Fin 2) :
      M a w - M b w ≤ 2 * (x : ℤ) := by
    rcases hwu.eq_or_lt with rfl | hlt
    · have h := hgBefore (u - 1) (by omega) (by omega) a b
      have hstep := hdStep a b (u - 1)
      rw [show u - 1 + 1 = u by omega] at hstep
      omega
    · exact (hgBefore w hηw hlt a b).le
  have hij : i ≠ j := fun he => by rw [he, sub_self] at hijU; omega
  let S := (Finset.Icc η u).filter (fun w => M i w - M j w ≤ (x : ℤ))
  have hS : S.Nonempty := ⟨η, mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hu.1⟩, hinitGap i j⟩⟩
  let s := S.max' hS
  obtain ⟨hs, hgs⟩ := mem_filter.mp (S.max'_mem hS)
  obtain ⟨hηs, hsu⟩ := mem_Icc.mp hs
  change η ≤ s at hηs
  change s ≤ u at hsu
  change M i s - M j s ≤ (x : ℤ) at hgs
  have hsu' : s < u := lt_of_le_of_ne hsu (fun he => by rw [he] at hgs; omega)
  have hsep (w : ℕ) (hsw : s < w) (hwu : w ≤ u) : (x : ℤ) < M i w - M j w := by
    by_contra! h
    have hmem : w ∈ S := mem_filter.mpr ⟨mem_Icc.mpr ⟨hηs.trans hsw.le, hwu⟩, h⟩
    exact (not_le_of_gt hsw) (Finset.le_max' S w hmem)
  have hsEq : M i s - M j s = (x : ℤ) := by
    have h := hsep (s + 1) (by omega) (by omega)
    have hstep := hdStep i j s
    omega
  let h := (M i s).toNat
  have hrh : (r : ℤ) ≤ M i s := (hinit i).2.1.trans (runMax_mono p m U i hηs)
  have hh : (h : ℤ) = M i s := Int.toNat_of_nonneg ((Int.natCast_nonneg r).trans hrh)
  have hrh' : r ≤ h := by exact_mod_cast hrh.trans_eq hh.symm
  have hh' : h ≤ r + H := by exact_mod_cast hh.le.trans (hmax i s hηs (hsu.trans hu.2.1))
  have hjEq : M j s = (h : ℤ) - (x : ℤ) := by omega
  have hMu : (h : ℤ) + (x : ℤ) ≤ M i u := by
    have h := runMax_mono p m U j hsu
    change M j s ≤ M j u at h
    omega
  have hhit : ∃ v : ℕ, s ≤ v ∧ (h : ℤ) + (x : ℤ) ≤ M i v := ⟨u, hsu, hMu⟩
  let v := Nat.find hhit
  have hv : s ≤ v ∧ (h : ℤ) + (x : ℤ) ≤ M i v := Nat.find_spec hhit
  have hvu : v ≤ u := Nat.find_min' hhit ⟨hsu, hMu⟩
  have hsv : s < v := lt_of_le_of_ne hv.1 fun he => by
    have h := hv.2
    rw [← he] at h
    omega
  have hvEq : M i v = (h : ℤ) + (x : ℤ) := by
    have hb : M i (v - 1) < (h : ℤ) + (x : ℤ) :=
      lt_of_not_ge fun h => Nat.find_min hhit (by omega : v - 1 < v) ⟨by omega, h⟩
    have hstep : M i (v - 1 + 1) ≤ M i (v - 1) + 1 := LocSepWindow.runMax_succ_le p m U i _
    rw [show v - 1 + 1 = v by omega] at hstep
    omega
  have hvPos : X i v = M i v := by
    obtain ⟨w, hw, hwe⟩ := exists_eq_runMax p m U i v
    have hwe : X i w = M i v := hwe
    suffices w = v by simpa only [this] using hwe
    by_contra! hne
    have hwv : w < v := lt_of_le_of_ne hw hne
    have hMw : (h : ℤ) + (x : ℤ) ≤ M i w :=
      (hv.2.trans_eq hwe.symm).trans (le_runMax p m U i w)
    by_cases hsw : s ≤ w
    · exact Nat.find_min hhit hwv ⟨hsw, hMw⟩
    · have hms : M i w ≤ M i s := runMax_mono p m U i (le_of_not_ge hsw)
      omega
  let z := s - σ
  have hσs : σ ≤ s := hησ.trans hηs
  have hq : recTimeA p m U r + z = s := by change σ + z = s; dsimp only [z]; omega
  have hzH : z ≤ H := by have := hsu.trans hu.2.1; omega
  have hh₀ : 1 ≤ h := by omega
  have hb : h - 1 + 1 = h := by omega
  have hlow : (((h - 5 * x : ℕ) : ℤ)) = (h : ℤ) - 5 * (x : ℤ) := by
    rw [Nat.cast_sub (by omega : 5 * x ≤ h)]
    push_cast
    ring
  refine ⟨i, j, z, h, hij, hzH, hrh', hh', hU, ?_⟩
  dsimp only
  rw [hq, hb]
  have htrail : M j s < (h : ℤ) := by rw [hjEq]; omega
  refine ⟨(le_runMax p m U i s).trans_eq hh.symm, hh.le, htrail, v, hv.1, ?_, ?_⟩
  · rw [show ((trajectory p m U v).pos i) = (h : ℤ) + (x : ℤ) from hvPos.trans hvEq]
    push_cast
    rfl
  · apply mem_intervalSurvival_iff.mpr
    intro w hsw hwv
    have hwv' : w ≤ v := by omega
    have hwu := hwv'.trans hvu
    have hηw := hηs.trans hsw
    have hl := hlag w hηw (hwu.trans hu.2.1)
      (fun s hs hsw i j => hgU s hs (hsw.trans hwu) i j) j
    have hjM : M j s ≤ M j w := runMax_mono p m U j hsw
    have hXMj : X j w ≤ M j w := le_runMax p m U j w
    have hMi : M i w ≤ (h : ℤ) + (x : ℤ) := (runMax_mono p m U i hwv').trans_eq hvEq
    change ((h - 5 * x : ℕ) : ℤ) < X j w ∧ X j w < ((h - 1 + 1 : ℕ) : ℤ)
    rw [hlow, hb]
    refine ⟨by omega, ?_⟩
    rcases hsw.eq_or_lt with rfl | hlt
    · omega
    · have := hsep w hlt hwu
      omega

end Swarming.Diameter
