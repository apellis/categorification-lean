/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Spanning
import Categorification.KLR.PolyRep.Sound
import Categorification.KLR.PolyRep.Independence

/-!
# The basis theorem for KLR algebras

KL I (arXiv:0803.4121v2), Theorem 2.5 and Corollary 2.6, in the generality of KL II:
for an integral domain `k`, data `Q` admitting a factorisation
`Q i j (u, v) = P j i (u, v) · P i j (v, u)` with all `P i j ≠ 0` (`i ≠ j`), and **any**
choice of reduced words `ρ w` for the permutations `w ∈ S_m`,

* the elements `ψ_{ρ w} x^u e_i` (`i ∈ Seq ν`, `w ∈ S_m`, `u ∈ ℕ^m`) form a `k`-basis of
  `R(ν)` (`basis`);
* for fixed `i, j`, those with `w • i = j` form a basis of `_jR(ν)_i = e_j R(ν) e_i`
  (`cornerBasis`);
* the polynomial representation is faithful (`polyRep_injective`).

Spanning holds over any commutative ring (`KLRAlgebra.span_eq_top'`); linear independence is
proved by acting on the polynomial representation over the fraction field.
The KL I statement itself (over `ℤ`, for the data of a simple graph) is `KL1.basis`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA PolyRep

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] [IsDomain k]
  {Q : I → I → MvPolynomial (Fin 2) k} {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {ν : Multiset I}

local notation "m" => Multiset.card ν

namespace KLRAlgebra

omit [IsDomain k] in
theorem polyRep_ψw (ρ : List ℕ) :
    polyRep hPQ (ψw ρ : KLRAlgebra k Q ν) = opΨw P ρ := by
  simp [ψw, opΨw, map_list_prod, List.map_map, Function.comp_def]

omit [IsDomain k] in
theorem polyRep_pol (p : MvPolynomial (Fin m) k) :
    polyRep hPQ (pol p : KLRAlgebra k Q ν) = opMul ν p := by
  have : (polyRep hPQ).comp (pol (k := k) (Q := Q) (ν := ν)) = opMul ν := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, pol_X, polyRep_x]
    rfl
  exact congrArg (fun φ : MvPolynomial (Fin m) k →ₐ[k] _ => φ p) this

/-- The standard family `ψ_{ρ w} x^u e_i`. -/
noncomputable def stdElt (ρ : Perm (Fin m) → List ℕ)
    (b : Seq ν × Perm (Fin m) × (Fin m →₀ ℕ)) : KLRAlgebra k Q ν :=
  ψw (ρ b.2.1) * pol (monomial b.2.2 1) * e b.1

omit [IsDomain k] in
theorem polyRep_stdElt (ρ : Perm (Fin m) → List ℕ) (b : Seq ν × Perm (Fin m) × (Fin m →₀ ℕ)) :
    polyRep hPQ (stdElt ρ b) = opΨw P (ρ b.2.1) ∘ₗ mulMono b.2.2 ∘ₗ opE b.1 := by
  rw [stdElt, map_mul, map_mul, polyRep_ψw, polyRep_pol, polyRep_e]
  rfl

variable (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)

include hPQ hP hρ in
theorem linearIndependent_stdElt :
    LinearIndependent k (stdElt (k := k) (Q := Q) ρ) := by
  refine LinearIndependent.of_comp (polyRep hPQ).toLinearMap ?_
  have : (polyRep hPQ).toLinearMap ∘ stdElt (k := k) (Q := Q) ρ =
      fun b => opΨw P (ρ b.2.1) ∘ₗ mulMono b.2.2 ∘ₗ opE b.1 := by
    funext b; exact polyRep_stdElt hPQ ρ b
  rw [this]
  exact linearIndependent_opΨw hP ρ hρ

include hρ in
omit [IsDomain k] in
theorem span_stdElt : Submodule.span k (Set.range (stdElt (k := k) (Q := Q) ρ)) = ⊤ := by
  rw [← span_eq_top' ρ hρ]
  congr 1
  ext r
  simp only [Set.mem_range, Set.mem_setOf_eq, stdElt, Prod.exists]
  constructor
  · rintro ⟨i, w, u, rfl⟩; exact ⟨w, u, i, rfl⟩
  · rintro ⟨w, u, i, rfl⟩; exact ⟨i, w, u, rfl⟩

/-- **KL I, Theorem 2.5** (whole algebra): for any choice of reduced words, the elements
`ψ_{ρ w} x^u e_i` form a basis of `R(ν)`. -/
noncomputable def basis : Basis (Seq ν × Perm (Fin m) × (Fin m →₀ ℕ)) k (KLRAlgebra k Q ν) :=
  Basis.mk (linearIndependent_stdElt hPQ hP ρ hρ) (span_stdElt ρ hρ).ge

theorem basis_apply (b : Seq ν × Perm (Fin m) × (Fin m →₀ ℕ)) :
    basis hPQ hP ρ hρ b = ψw (ρ b.2.1) * pol (monomial b.2.2 1) * e b.1 := by
  simp [basis, stdElt]

/-- The corner `_jR(ν)_i = e_j R(ν) e_i`, as a submodule. -/
noncomputable def corner (j i : Seq ν) : Submodule k (KLRAlgebra k Q ν) :=
  LinearMap.range ((LinearMap.mulLeft k (e j)).comp (LinearMap.mulRight k (e i)))

omit [IsDomain k] in
theorem mem_corner_iff {j i : Seq ν} {r : KLRAlgebra k Q ν} :
    r ∈ corner j i ↔ e j * r * e i = r := by
  constructor
  · rintro ⟨s, rfl⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply]
    simp only [← mul_assoc, e_mul_self]
    rw [mul_assoc _ (e i), e_mul_self]
  · intro h; exact ⟨r, by simpa [mul_assoc] using h⟩

/-- Index set of the corner basis: pairs `(w, u)` with `w • i = j`. -/
abbrev CornerIdx (j i : Seq ν) : Type _ := {w : Perm (Fin m) // w • i = j} × (Fin m →₀ ℕ)

/-- The family `ψ_{ρ w} x^u e_i`, `w • i = j`, landing in `_jR(ν)_i`. -/
noncomputable def cornerElt (j i : Seq ν) (b : CornerIdx j i) : KLRAlgebra k Q ν :=
  stdElt ρ (i, b.1.1, b.2)

include hρ in
omit [IsDomain k] in
theorem cornerElt_mem (j i : Seq ν) (b : CornerIdx j i) :
    cornerElt (k := k) (Q := Q) ρ j i b ∈ corner j i := by
  rw [mem_corner_iff, cornerElt, stdElt]
  dsimp only
  rw [mul_assoc (e j), mul_assoc _ (e i) (e i), e_mul_self, e_mul_gen, if_pos]
  rw [(hρ b.1.1).2]
  obtain ⟨⟨w, hw⟩, u⟩ := b
  subst hw
  exact inv_smul_smul w i

include hρ in
omit [IsDomain k] in
theorem span_cornerElt (j i : Seq ν) :
    Submodule.span k (Set.range (cornerElt (k := k) (Q := Q) ρ j i)) = corner j i := by
  apply le_antisymm
  · exact Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact cornerElt_mem ρ hρ j i b)
  · intro r hr
    have := mem_span_corner' ρ hρ i j (mem_corner_iff.1 hr)
    refine Submodule.span_mono ?_ this
    rintro _ ⟨w, u, hw, rfl⟩
    exact ⟨(⟨w, hw⟩, u), rfl⟩

include hPQ hP hρ in
theorem linearIndependent_cornerElt (j i : Seq ν) :
    LinearIndependent k (cornerElt (k := k) (Q := Q) ρ j i) := by
  refine (linearIndependent_stdElt hPQ hP ρ hρ).comp _ ?_
  rintro ⟨⟨w, hw⟩, u⟩ ⟨⟨w', hw'⟩, u'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, rfl, rfl⟩ := h
  rfl

/-- **KL I, Theorem 2.5**: for any choice of reduced words `ρ w`, the elements
`ψ_{ρ w} x^u e_i` with `w • i = j` and `u ∈ ℕ^m` form a basis of `_jR(ν)_i`. -/
noncomputable def cornerBasis (j i : Seq ν) : Basis (CornerIdx j i) k (corner (Q := Q) j i) :=
  (Basis.span (linearIndependent_cornerElt hPQ hP ρ hρ j i)).map
    (LinearEquiv.ofEq _ _ (span_cornerElt ρ hρ j i))

theorem cornerBasis_apply (j i : Seq ν) (b : CornerIdx j i) :
    (cornerBasis hPQ hP ρ hρ j i b : KLRAlgebra k Q ν) =
      ψw (ρ b.1.1) * pol (monomial b.2 1) * e i := by
  simp [cornerBasis, Basis.span_apply, cornerElt, stdElt]

end KLRAlgebra

open KLRAlgebra in
include hP in
/-- **KL I, Corollary 2.6**: the polynomial representation is faithful. -/
theorem polyRep_injective : Function.Injective (polyRep hPQ : KLRAlgebra k Q ν → _) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Perm (Fin m) → List ℕ, ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w :=
    ⟨fun w => canWord m w, fun w => ⟨isReduced_canWord m w, wordProd_canWord m w⟩⟩
  show Function.Injective (polyRep hPQ).toLinearMap
  rw [← LinearMap.ker_eq_bot]
  have hli := linearIndependent_opΨw (ν := ν) hP ρ hρ
  refine LinearMap.ker_eq_bot'.2 fun r hr => ?_
  let B := basis hPQ hP ρ hρ
  rw [← B.linearCombination_repr r] at hr ⊢
  have h2 : (polyRep hPQ).toLinearMap ∘ B = fun b => opΨw P (ρ b.2.1) ∘ₗ mulMono b.2.2 ∘ₗ opE b.1 := by
    funext b; simp only [Function.comp_apply, B, basis_apply]; exact polyRep_stdElt hPQ ρ b
  rw [Finsupp.linearCombination_apply, map_finsuppSum] at hr
  simp only [map_smul] at hr
  have : B.repr r = 0 := by
    rw [linearIndependent_iff] at hli
    apply hli
    rw [Finsupp.linearCombination_apply, ← hr]
    refine Finsupp.sum_congr fun b _ => ?_
    rw [← congrFun h2 b]; rfl
  rw [this, map_zero]

end Categorification.KLR
