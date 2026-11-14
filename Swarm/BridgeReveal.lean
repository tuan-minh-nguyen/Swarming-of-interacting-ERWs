/-
# The mark family of `Swarm/Reveal.lean` is i.i.d. Bernoulli`((1-p)^(m-1))`

`Swarm/Swarm/Reveal.lean` (pre-existing, unchanged) proves the paper's deterministic
displays `(reveal)` and `(dominate)` for the strong trajectory, using its own
`Swarming.Trajectory.SiteMark`.  The paper's other statement in the same paragraph,

  "Then `(B_j(x))_{j,x}` are independent Bernoulli random variables with success probability
   `(1-p)^{m-1}`"   (`main_1d_revised.tex`, §2.1),

is *not* in `Swarm/Reveal.lean`: it is a statement about the law of the uniform array, and it is the
input `q = (1-p)^(m-1)` of the verified exponential-moment layer `areas/marks` (whose
`exists_exp_moment_hof` takes `q` as a parameter).

This file states that law for `Swarm/Reveal.lean`'s own definition of `B_j(x)`, so that the two
pieces compose:

* `siteMark_iff_reveal` — the two mark predicates (`Swarming.Trajectory.SiteMark` and the one
  used in `Marks`/`MarkOccupation`/`MarkEnv`) coincide;
* `reveal_siteMark_measure` — `P(B_j(x) = 1) = (1-p)^(m-1)` under `Uniform.arrayMeasure`;
* `reveal_marks_pair_measure` — two marks at distinct (walker, site) pairs have joint law
  `q^2`, i.e. they are independent;
* `reveal_familyMark_measure` — finite families at distinct pairs factorise with `q^{|s|}`.

Everything is proved; see `ConcreteMarkAudit.lean` for the axiom audit.
-/
import Swarm.Reveal
import Swarm.MarkEnv

namespace Swarming.Marks

open Swarming Swarming.Model Swarming.Uniform Swarming.Trajectory

variable {N : ℕ}

/-- **The two mark predicates coincide.**  `Swarm/Reveal.lean` writes `B_j(x)` as a conjunction over
`Finset.Icc 1 (m-1)`; the marking used in `Marks` writes it as a bounded `forall`. -/
theorem siteMark_iff_reveal (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℤ) :
    Swarming.Trajectory.SiteMark p m U j x ↔ SiteMark p m U j x := by
  simp only [Swarming.Trajectory.SiteMark, SiteMark, Finset.mem_Icc]
  constructor
  · intro h k hk1 hkm
    exact h k ⟨hk1, hkm⟩
  · intro h k hk
    exact h k hk.1 hk.2

/-- **`Swarm/Reveal.lean`'s environment is the `MarkEnv` environment.** -/
theorem omegaAt_eq_envOfMark (p : ℝ) (m : ℕ) (U : Array N) (j : Fin N) (x : ℤ) :
    Swarming.Trajectory.omegaAt p m U j x = envOfMark p m U j x := by
  classical
  simp only [Swarming.Trajectory.omegaAt, envOfMark]
  by_cases h : SiteMark p m U j x
  · have h' : Swarming.Trajectory.SiteMark p m U j x := (siteMark_iff_reveal p m U j x).mpr h
    rw [if_pos h', if_pos h]
  · have h' : ¬ Swarming.Trajectory.SiteMark p m U j x :=
      fun hc => h ((siteMark_iff_reveal p m U j x).mp hc)
    rw [if_neg h', if_neg h]

/-- **`P(B_j(x) = 1) = (1-p)^(m-1)`** for `Swarm/Reveal.lean`'s `B_j(x)`. -/
theorem reveal_siteMark_measure (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) (j : Fin N) (x : ℤ) :
    arrayMeasure N {U : Array N | Swarming.Trajectory.SiteMark p m U j x}
      = (ENNReal.ofReal (1 - p)) ^ (m - 1) := by
  have hset : {U : Array N | Swarming.Trajectory.SiteMark p m U j x}
      = {U : Array N | SiteMark p m U j x} := by
    ext U
    exact siteMark_iff_reveal p m U j x
  rw [hset, arrayMeasure_siteMark hp0 hp1]

/-- **Two marks at distinct (walker, site) pairs are independent Bernoulli`: the joint mass of
`B_{j}(x) = 1` and `B_{j'}(x') = 1` is `q^2` with `q = (1-p)^(m-1)`. -/
theorem reveal_marks_pair_measure (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ)
    {q₁ q₂ : Fin N × ℤ} (hne : q₁ ≠ q₂) :
    arrayMeasure N {U : Array N |
        Swarming.Trajectory.SiteMark p m U q₁.1 q₁.2 ∧
        Swarming.Trajectory.SiteMark p m U q₂.1 q₂.2}
      = (ENNReal.ofReal (1 - p)) ^ (2 * (m - 1)) := by
  classical
  set q : Fin 2 → Fin N × ℤ := fun k => if k = 0 then q₁ else q₂ with hq
  have hw : ∀ a ∈ (Finset.univ : Finset (Fin 2)), ∀ b ∈ (Finset.univ : Finset (Fin 2)),
      q a = q b → a = b := by
    intro a _ b _ hab
    fin_cases a <;> fin_cases b <;> simp_all [hq, hne]
  have hset1 : {U : Array N |
        Swarming.Trajectory.SiteMark p m U q₁.1 q₁.2 ∧
        Swarming.Trajectory.SiteMark p m U q₂.1 q₂.2}
      = {U : Array N | SiteMark p m U q₁.1 q₁.2 ∧ SiteMark p m U q₂.1 q₂.2} := by
    ext U
    simp only [Set.mem_setOf_eq, siteMark_iff_reveal p m U]
  have hset2 : {U : Array N | SiteMark p m U q₁.1 q₁.2 ∧ SiteMark p m U q₂.1 q₂.2}
      = familyMark (N := N) p m (Finset.univ : Finset (Fin 2)) q := by
    ext U
    constructor
    · rintro ⟨h1, h2⟩ a _
      fin_cases a
      · simpa [hq] using h1
      · simpa [hq] using h2
    · intro h
      exact ⟨by simpa [hq] using h 0 (Finset.mem_univ 0),
             by simpa [hq] using h 1 (Finset.mem_univ 1)⟩
  rw [hset1, hset2, arrayMeasure_marks_family hp0 hp1 m (Finset.univ : Finset (Fin 2)) q hw]
  norm_num

/-- **The paper's sentence "`(B_j(x))_{j,x}` are independent Bernoulli random variables with
success probability `(1-p)^{m-1}`"** in finite-dimensional form, for `Swarm/Reveal.lean`'s `B_j(x)`:
over any finite set of distinct (walker, site) pairs the joint mark probability is `q^{|s|}`. -/
theorem reveal_familyMark_measure (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) {ι : Type*}
    (s : Finset ι) (w : ι → Fin N × ℤ) (hw : ∀ a ∈ s, ∀ b ∈ s, w a = w b → a = b) :
    arrayMeasure N {U : Array N | ∀ a ∈ s, Swarming.Trajectory.SiteMark p m U (w a).1 (w a).2}
      = (ENNReal.ofReal (1 - p)) ^ (s.card * (m - 1)) := by
  have hset : {U : Array N | ∀ a ∈ s, Swarming.Trajectory.SiteMark p m U (w a).1 (w a).2}
      = familyMark (N := N) p m s w := by
    ext U
    exact ⟨fun h a ha => (siteMark_iff_reveal p m U (w a).1 (w a).2).mp (h a ha),
           fun h a ha => (siteMark_iff_reveal p m U (w a).1 (w a).2).mpr (h a ha)⟩
  rw [hset, arrayMeasure_marks_family hp0 hp1 m s w hw]

end Swarming.Marks


