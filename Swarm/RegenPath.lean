/-
# The concrete first-regeneration identity `V ∩ {D = d, τ_D = t} = C_{d,t} ∩ V_{d,t}`

`main_1d_revised.tex` §3.2, proof of Proposition `regen`, introduces the record
times and regeneration events

* `τ_r = inf{n ≥ 0 : max_i X_n^i = r}`,
* `τ_r` is a *simultaneous record time* if `X_{τ_r}^i = r` for every `i`, and a
  *regeneration time* if in addition `X_n^i > r` for every `i` and every `n > τ_r`;
* `V = {X_n^i > 0 for every i, n ≥ 1}` and
  `D = inf{r ≥ 1 : τ_r is a regeneration time}`;
* `V_{d,t} = {X_{t+n}^i > d for every i, n ≥ 1}` and `C_{d,t}` is the event on which
  `τ_d = t`, `X_t^i = d` for all `i`, `min_{1≤n≤t} min_i X_n^i > 0`, and every
  earlier level `1 ≤ e < d` fails to be a regeneration,

and then states the identity

> `V ∩ {D = d, τ_D = t} = C_{d,t} ∩ V_{d,t}`   (equation `(firstblk)`),

which is the set-theoretic core of the regeneration factorization `(factor)`.

This file formalises that identity for an arbitrary nearest-neighbour path of `N`
walkers started at the origin — no probability is involved.  The only input from
the dynamics is `|X_{n+1}^i - X_n^i| = 1` and `X_0^i = 0`, which are used for the
discrete intermediate value property: the first visit to a level strictly below
`d` occurs strictly before the first visit to `d`.

Every declaration is checked by `verify.sh` and `Audit.lean` (`#print axioms`).
-/
import Swarm.Imports
import Swarm.KacDisjoint

open MeasureTheory Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

namespace RegenPath

variable {N : ℕ}

/-- A path of `N` nearest-neighbour walkers on `ℤ`. -/
abbrev Path (N : ℕ) := ℕ → (Fin N → ℤ)

/-- `tau X r` is the first time at which some walker is at `r`; since the walkers
start at `0` and move by `±1`, this is the paper's `τ_r = inf{n : max_i X_n^i = r}`
for `r ≥ 0`.  The value `⊤` means the level is never reached. -/
noncomputable def tau (X : Path N) (r : ℤ) : ℕ∞ :=
  if h : ∃ n : ℕ, ∃ i : Fin N, X n i = r then (Nat.find h : ℕ∞) else ⊤

/-- Characterization of `tau` as a first hitting time. -/
lemma tau_eq_iff {X : Path N} {r : ℤ} {t : ℕ} :
    tau X r = (t : ℕ∞) ↔ (∃ i, X t i = r) ∧ ∀ n, n < t → ∀ i, X n i ≠ r := by
  unfold tau
  split_ifs with h
  · constructor
    · intro he
      have ht : Nat.find h = t := by exact_mod_cast he
      subst ht
      exact ⟨Nat.find_spec h, fun n hn i hi => Nat.find_min h hn ⟨i, hi⟩⟩
    · rintro ⟨hs, hmin⟩
      have h1 : Nat.find h ≤ t := Nat.find_min' h hs
      have h2 : t ≤ Nat.find h := by
        by_contra hlt
        simp only [not_le] at hlt
        obtain ⟨i, hi⟩ := Nat.find_spec h
        exact hmin (Nat.find h) hlt i hi
      have : Nat.find h = t := le_antisymm h1 h2
      rw [this]
  · constructor
    · intro he
      exact absurd he (by simp)
    · rintro ⟨hs, -⟩
      exact absurd ⟨t, hs⟩ h

/-- **Discrete intermediate value property** for a `±1` walk started at `0`: before
reaching `d` it visits every level strictly between `0` and `d`. -/
lemma exists_lt_of_reaches {f : ℕ → ℤ} (h0 : f 0 = 0) (hstep : ∀ n, |f (n + 1) - f n| = 1)
    {s : ℕ} {d : ℤ} (hs : f s = d) {e : ℤ} (he0 : 0 ≤ e) (hed : e < d) :
    ∃ n, n < s ∧ f n = e := by
  have hne : ∃ n, n ≤ s ∧ e ≤ f n := ⟨s, le_rfl, by rw [hs]; linarith⟩
  set n₀ := Nat.find hne with hn₀def
  obtain ⟨hn₀le, hn₀ge⟩ := Nat.find_spec hne
  rw [← hn₀def] at hn₀le hn₀ge
  have hn₀min : ∀ m < n₀, ¬ (m ≤ s ∧ e ≤ f m) := by
    intro m hm
    rw [hn₀def] at hm
    exact Nat.find_min hne hm
  have hval : f n₀ = e := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · simp only [h] at hn₀ge ⊢
      rw [h0] at hn₀ge
      omega
    · have hprev : ¬ (n₀ - 1 ≤ s ∧ e ≤ f (n₀ - 1)) := hn₀min (n₀ - 1) (by omega)
      have hprev' : f (n₀ - 1) < e := by
        rcases not_and_or.mp hprev with h' | h'
        · omega
        · omega
      have hstep' : |f ((n₀ - 1) + 1) - f (n₀ - 1)| = 1 := hstep (n₀ - 1)
      rw [Nat.sub_add_cancel h] at hstep'
      have hcases := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp hstep'
      omega
  refine ⟨n₀, ?_, hval⟩
  rcases lt_or_ge n₀ s with hlt | hge
  · exact hlt
  · exfalso
    have : n₀ = s := le_antisymm hn₀le hge
    rw [this, hs] at hval
    omega

/-- At a first hitting time of level `d`, every level strictly between `0` and `d` is
hit strictly earlier. -/
lemma tau_lt_of_lt {X : Path N} (hX0 : ∀ i, X 0 i = 0)
    (hNN : ∀ n i, |X (n + 1) i - X n i| = 1)
    {e : ℤ} {d : ℤ} {t : ℕ} (het : tau X d = (t : ℕ∞))
    (he0 : 0 ≤ e) (hed : e < d) : tau X e < (t : ℕ∞) := by
  obtain ⟨⟨i, hi⟩, -⟩ := tau_eq_iff.mp het
  obtain ⟨n, hn, hfn⟩ :=
    exists_lt_of_reaches (f := fun m => X m i) (hX0 i) (fun m => hNN m i) hi he0 hed
  have hne : ∃ m : ℕ, ∃ j : Fin N, X m j = e := ⟨n, i, hfn⟩
  unfold tau
  rw [dif_pos hne]
  have h1 : Nat.find hne ≤ n := Nat.find_min' hne ⟨i, hfn⟩
  rw [ENat.natCast_lt_natCast]
  omega

/-- At the first hitting time of level `e`, no walker is above `e`. -/
lemma le_of_tau {X : Path N} (hX0 : ∀ i, X 0 i = 0)
    (hNN : ∀ n i, |X (n + 1) i - X n i| = 1)
    {e : ℤ} (he0 : 0 ≤ e) {te : ℕ} (hte : tau X e = (te : ℕ∞)) (i : Fin N) :
    X te i ≤ e := by
  by_contra hcon
  simp only [not_le] at hcon
  obtain ⟨n, hn, hfn⟩ := exists_lt_of_reaches (f := fun m => X m i) (hX0 i)
    (fun m => hNN m i) (s := te) (d := X te i) (e := e) rfl he0 hcon
  exact (tau_eq_iff.mp hte).2 n hn i hfn

/-- `V`: every walker stays strictly positive after time `0`. -/
def V (X : Path N) : Prop := ∀ i n, 0 < n → 0 < X n i

/-- `V_{d,t}`: after time `t` every walker stays strictly above `d`. -/
def Vdt (X : Path N) (d : ℤ) (t : ℕ) : Prop := ∀ i n, 0 < n → d < X (t + n) i

/-- `τ_r` is a *regeneration time*: at time `τ_r` every walker is at `r`, and after
`τ_r` every walker stays strictly above `r`. -/
def Reg (X : Path N) (r : ℤ) : Prop :=
  ∃ t : ℕ, tau X r = (t : ℕ∞) ∧ (∀ i, X t i = r) ∧ ∀ n, t < n → ∀ i, r < X n i

/-- `D`: the first regeneration level `≥ 1` (`⊤` if there is none). -/
noncomputable def D (X : Path N) : ℕ∞ :=
  if h : ∃ r : ℕ, 1 ≤ r ∧ Reg X (r : ℤ) then (Nat.find h : ℕ∞) else ⊤

/-- `C_{d,t}`: the event of the paper — `τ_d = t`, every walker is at `d` at time
`t`, no walker is negative on `1 ≤ n ≤ t`, and every level `1 ≤ e < d` fails to be a
regeneration. -/
def Cdt (X : Path N) (d : ℕ) (t : ℕ) : Prop :=
  tau X (d : ℤ) = (t : ℕ∞) ∧
    (∀ i, X t i = (d : ℤ)) ∧
    (∀ n, 0 < n → n ≤ t → ∀ i, 0 < X n i) ∧
    (∀ e : ℕ, 1 ≤ e → e < d →
      ∃ te : ℕ, tau X (e : ℤ) = (te : ℕ∞) ∧
        ((∃ i, X te i < (e : ℤ)) ∨ ∃ n, te < n ∧ n ≤ t ∧ ∃ i, X n i ≤ (e : ℤ)))

/-- **The first-regeneration identity** (equation `(firstblk)` of
`main_1d_revised.tex`):

`V ∩ {D = d, τ_D = t} = C_{d,t} ∩ V_{d,t}`.

This is the set-theoretic core of the regeneration factorization `(factor)`; it is
proved for an arbitrary nearest-neighbour path of `N` walkers started at the
origin. -/
theorem first_block_identity (X : Path N) (hX0 : ∀ i, X 0 i = 0)
    (hNN : ∀ n i, |X (n + 1) i - X n i| = 1) (d t : ℕ) (hd : 1 ≤ d) :
    (V X ∧ D X = (d : ℕ∞) ∧ tau X (d : ℤ) = (t : ℕ∞)) ↔ (Cdt X d t ∧ Vdt X d t) := by
  constructor
  · rintro ⟨hV, hD, htau⟩
    -- `D = d` means `d` is a regeneration level
    have hex : ∃ r : ℕ, 1 ≤ r ∧ Reg X (r : ℤ) := by
      by_contra hcon
      unfold D at hD
      rw [dif_neg hcon] at hD
      exact absurd hD.symm (by simp)
    have hfind : Nat.find hex = d := by
      unfold D at hD
      rw [dif_pos hex] at hD
      exact_mod_cast hD
    have hReg : Reg X (d : ℤ) := by
      have h := (Nat.find_spec hex).2
      rwa [hfind] at h
    obtain ⟨s, hτs, hXs, hafter⟩ := hReg
    have hst : s = t := by
      have : (s : ℕ∞) = (t : ℕ∞) := by rw [← hτs, htau]
      exact_mod_cast this
    have hXs' : ∀ i, X t i = (d : ℤ) := by rw [← hst]; exact hXs
    have hafter' : ∀ n, t < n → ∀ i, (d : ℤ) < X n i := by rw [← hst]; exact hafter
    have hearly' : ∀ e : ℕ, 1 ≤ e → e < d →
        ∃ te : ℕ, tau X (e : ℤ) = (te : ℕ∞) ∧
          ((∃ i, X te i < (e : ℤ)) ∨ ∃ n, te < n ∧ n ≤ t ∧ ∃ i, X n i ≤ (e : ℤ)) := by
      intro e he1 hed
      have hnot : ¬ Reg X (e : ℤ) := by
        intro hre
        have h1 : Nat.find hex ≤ e := Nat.find_min' hex ⟨he1, hre⟩
        omega
      have hlt : tau X (e : ℤ) < (t : ℕ∞) :=
        tau_lt_of_lt hX0 hNN htau (by omega) (by omega)
      have hne_top : tau X (e : ℤ) ≠ ⊤ := by
        intro h
        rw [h] at hlt
        exact absurd hlt (not_lt.mpr le_top)
      obtain ⟨te, hte0⟩ := ENat.ne_top_iff_exists.mp hne_top
      have hte : tau X (e : ℤ) = (te : ℕ∞) := hte0.symm
      have hspec := tau_eq_iff.mp hte
      have hfail : ¬ ((∀ i, X te i = (e : ℤ)) ∧ ∀ n, te < n → ∀ i, (e : ℤ) < X n i) := by
        intro hcon
        exact hnot ⟨te, hte, hcon.1, hcon.2⟩
      refine ⟨te, hte, ?_⟩
      rcases not_and_or.mp hfail with hnotall | hnotafter
      · push_neg at hnotall
        obtain ⟨i, hi⟩ := hnotall
        exact Or.inl ⟨i, lt_of_le_of_ne (le_of_tau hX0 hNN (by omega) hte i) hi⟩
      · push_neg at hnotafter
        obtain ⟨n, hn, i, hi⟩ := hnotafter
        exact Or.inr ⟨n, hn, by_contra (fun hcon => by
          push_neg at hcon
          exact absurd (hafter' n hcon i) (by omega)), i, hi⟩
    refine ⟨⟨htau, hXs', fun n hn _ i => hV i n hn, hearly'⟩, fun i n hn => hafter' (t + n) (by omega) i⟩
  · rintro ⟨⟨htau, hXt, hpos, hearly⟩, hVdt⟩
    have hafter : ∀ n, t < n → ∀ i, (d : ℤ) < X n i := by
      intro n hn i
      have heq : n = t + (n - t) := by omega
      rw [heq]
      exact hVdt i (n - t) (by omega)
    refine ⟨?_, ?_, htau⟩
    · -- `V`
      intro i n hn
      rcases le_or_gt n t with h | h
      · exact hpos n hn h i
      · have := hafter n h i
        omega
    · -- `D = d`
      have hRegd : Reg X (d : ℤ) := ⟨t, htau, hXt, hafter⟩
      have hnotsmall : ∀ e : ℕ, 1 ≤ e → e < d → ¬ Reg X (e : ℤ) := by
        intro e he1 hed hre
        obtain ⟨te', hte', hXe, haft⟩ := hre
        obtain ⟨te, hte, hdisj⟩ := hearly e he1 hed
        have hcast : (te : ℕ∞) = (te' : ℕ∞) := hte.symm.trans hte'
        have hteq : te = te' := by exact_mod_cast hcast
        subst hteq
        rcases hdisj with ⟨i, hi⟩ | ⟨n, hlt, hle, i, hi⟩
        · rw [hXe i] at hi
          omega
        · have := haft n hlt i
          omega
      have hex : ∃ r : ℕ, 1 ≤ r ∧ Reg X (r : ℤ) := ⟨d, hd, hRegd⟩
      unfold D
      rw [dif_pos hex]
      have hle : Nat.find hex ≤ d := Nat.find_min' hex ⟨hd, hRegd⟩
      have hge : d ≤ Nat.find hex := by
        by_contra hcon
        simp only [not_le] at hcon
        have h1 : 1 ≤ Nat.find hex := (Nat.find_spec hex).1
        exact hnotsmall (Nat.find hex) h1 hcon (Nat.find_spec hex).2
      rw [le_antisymm hle hge]

end RegenPath
