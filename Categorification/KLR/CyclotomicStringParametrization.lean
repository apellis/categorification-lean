/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.StringParametrization
import Categorification.KLR.SymmetricFactorization

/-!
# String parametrizations of simple cyclotomic KLR modules

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §3.2 and Proposition 3.20, transported to the cyclotomic quotient `R^a(ν)`.
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Definition 5.16 and Propositions 5.17–5.18, order the simple modules of the cyclotomic factor of
a tensor product algebra by their string parametrization.

A module over `R^a(ν)` restricts to an `R(ν)`-module along the quotient map. Its support
`{s | 1_s M ≠ 0}` (`CycKLR.supp`) and its string-maximal sequence (`CycKLR.IsStrMax`) are those of
the restriction.

## Main results

* `CycKLR.exists_isStrMax`: every nonzero module has a string-maximal sequence.
* `CycKLR.nonempty_equiv_of_isStrMax`: two simple finite-dimensional modules on which the dots
  act nilpotently and which have the same string-maximal sequence are isomorphic.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra
universe u
variable {I k : Type*} [DecidableEq I] [Field k]
    (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k) (ν : Multiset I)

section Supp
variable (M : Type*) [AddCommGroup M] [Module k M] [Module (CycKLR k Q a ν) M]
  [IsScalarTower k (CycKLR k Q a ν) M]

/-- The support `{s | 1_s M ≠ 0}` of a module over the cyclotomic quotient. -/
def supp : Set (Seq ν) := {s | ∃ m : M, mk k Q a ν (e s) • m ≠ 0}

/-- `s` is the sequence of the support of `M` with the lexicographically largest string
sequence along `σ`. -/
def IsStrMax (σ : ℕ → I) (s : Seq ν) : Prop :=
  s ∈ supp Q a ν M ∧ ∀ t ∈ supp Q a ν M, strKey σ (List.ofFn t.1) ≤ strKey σ (List.ofFn s.1)

section Restriction
variable [Module (KLRAlgebra k Q ν) M]
  (hM : ∀ (r : KLRAlgebra k Q ν) (m : M), r • m = mk k Q a ν r • m)
include hM

omit [IsScalarTower k (CycKLR k Q a ν) M] in
theorem mem_seqSupp_iff_of_restrict [IsScalarTower k (KLRAlgebra k Q ν) M] {s : Seq ν} :
    s ∈ seqSupp Q ν M ↔ s ∈ supp Q a ν M := by
  rw [mem_seqSupp]
  constructor
  · intro h
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    refine ⟨m, ?_⟩
    have : (e s : KLRAlgebra k Q ν) • m = m := hm
    rw [← hM, this]
    exact hm0
  · rintro ⟨m, hm⟩ hbot
    refine hm ?_
    have hfix : (e s : KLRAlgebra k Q ν) • ((e s : KLRAlgebra k Q ν) • m) =
        (e s : KLRAlgebra k Q ν) • m := by
      rw [smul_smul, e_mul_self]
    have : (e s : KLRAlgebra k Q ν) • m ∈ fixSub k M (e s : KLRAlgebra k Q ν) := hfix
    rw [hbot, Submodule.mem_bot] at this
    rwa [← hM]

omit [IsScalarTower k (CycKLR k Q a ν) M] in
theorem isStrMax_iff_of_restrict [IsScalarTower k (KLRAlgebra k Q ν) M] (σ : ℕ → I)
    (s : Seq ν) : KLRAlgebra.IsStrMax Q σ ν M s ↔ IsStrMax Q a ν M σ s := by
  unfold KLRAlgebra.IsStrMax IsStrMax
  simp only [mem_seqSupp_iff_of_restrict Q a ν M hM]

theorem isScalarTower_of_restrict : IsScalarTower k (KLRAlgebra k Q ν) M :=
  ⟨fun c r m => by rw [hM, hM, map_smul, smul_assoc]⟩

omit [Module k M] [IsScalarTower k (CycKLR k Q a ν) M] in
theorem isSimpleModule_of_restrict [IsSimpleModule (CycKLR k Q a ν) M] :
    IsSimpleModule (KLRAlgebra k Q ν) M :=
  isSimpleModule_iff_toSpanSingleton_surjective.mpr
    ⟨IsSimpleModule.nontrivial (CycKLR k Q a ν) M, by
      intro m hm y
      obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective (CycKLR k Q a ν) hm y
      obtain ⟨r, rfl⟩ := mk_surjective (k := k) (Q := Q) (a := a) (ν := ν) b
      exact ⟨r, by simpa [hM] using hb⟩⟩

end Restriction

theorem exists_isStrMax [Nontrivial M] (σ : ℕ → I) : ∃ s, IsStrMax Q a ν M σ s := by
  let : Module (KLRAlgebra k Q ν) M := Module.compHom M (mk k Q a ν).toRingHom
  have hM : ∀ (r : KLRAlgebra k Q ν) (m : M), r • m = mk k Q a ν r • m := fun _ _ => rfl
  have := isScalarTower_of_restrict Q a ν M hM
  obtain ⟨s, hs⟩ := KLRAlgebra.exists_isStrMax (Q := Q) (ν := ν) (M := M) σ
  exact ⟨s, (isStrMax_iff_of_restrict Q a ν M hM σ s).1 hs⟩

end Supp

/-- **The string parametrization determines a simple cyclotomic module**: two simple
finite-dimensional modules over `R^a(ν)` on which the dots act nilpotently and with the same
string-maximal sequence are isomorphic (KL I, Proposition 3.20, via restriction to `R(ν)`). -/
theorem nonempty_equiv_of_isStrMax (hQ : KLRSymm Q)
    (hQ0 : ∀ i j : I, i ≠ j → Q i j ≠ 0)
    (hnil : ∀ b, IsNilpotent (mk k Q a ν (x b)))
    {σ : ℕ → I} (hσ : ∀ i m, ∃ r, m ≤ r ∧ σ r = i)
    (M M' : Type u) [AddCommGroup M] [Module k M] [Module (CycKLR k Q a ν) M]
    [IsScalarTower k (CycKLR k Q a ν) M] [FiniteDimensional k M]
    [IsSimpleModule (CycKLR k Q a ν) M]
    [AddCommGroup M'] [Module k M'] [Module (CycKLR k Q a ν) M']
    [IsScalarTower k (CycKLR k Q a ν) M'] [FiniteDimensional k M']
    [IsSimpleModule (CycKLR k Q a ν) M'] {s : Seq ν}
    (hs : IsStrMax Q a ν M σ s) (hs' : IsStrMax Q a ν M' σ s) :
    Nonempty (M ≃ₗ[CycKLR k Q a ν] M') := by
  let iM : Module (KLRAlgebra k Q ν) M := Module.compHom M (mk k Q a ν).toRingHom
  let iM' : Module (KLRAlgebra k Q ν) M' := Module.compHom M' (mk k Q a ν).toRingHom
  have hM : ∀ (r : KLRAlgebra k Q ν) (m : M), r • m = mk k Q a ν r • m := fun _ _ => rfl
  have hM' : ∀ (r : KLRAlgebra k Q ν) (m : M'), r • m = mk k Q a ν r • m := fun _ _ => rfl
  have := isScalarTower_of_restrict Q a ν M hM
  have := isScalarTower_of_restrict Q a ν M' hM'
  have := isSimpleModule_of_restrict Q a ν M hM
  have := isSimpleModule_of_restrict Q a ν M' hM'
  have hn : ∀ b, SmulNilpotent (x b : KLRAlgebra k Q ν) M := fun b => by
    obtain ⟨N, hN⟩ := hnil b
    exact ⟨N, fun v => by rw [hM, map_pow, hN, zero_smul]⟩
  have hn' : ∀ b, SmulNilpotent (x b : KLRAlgebra k Q ν) M' := fun b => by
    obtain ⟨N, hN⟩ := hnil b
    exact ⟨N, fun v => by rw [hM', map_pow, hN, zero_smul]⟩
  obtain ⟨-, h⟩ := isStrMax_aux (symmP_factor Q hQ) (symmP_ne_zero Q hQ0) _ ν rfl σ hσ M
    hn s ((isStrMax_iff_of_restrict Q a ν M hM σ s).2 hs)
  obtain ⟨f⟩ := h M' hn' ((isStrMax_iff_of_restrict Q a ν M' hM' σ s).2 hs')
  exact ⟨{ f.toAddEquiv with
    map_smul' := fun c m => by
      obtain ⟨r, rfl⟩ := mk_surjective (k := k) (Q := Q) (a := a) (ν := ν) c
      exact f.map_smul r m }⟩

end Categorification.KLR.CycKLR
