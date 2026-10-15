/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BasisTheorem
import Categorification.KLR.BaseChange
import Categorification.KLR.Symmetries
import Mathlib.RingTheory.TensorProduct.Free

/-!
# The KLR basis theorem over an arbitrary commutative ring

KL I (arXiv:0803.4121v2), Theorem 2.5, and its extension to arbitrary KLR data: for any
commutative ring `k` and symmetric data `Q` (`Q_{ba}(u, v) = Q_{ab}(v, u)` for `a ≠ b`,
`KLRSymm Q`), and any choice of reduced words `ρ w`, the elements `ψ_{ρ w} x^u e_i` form a
`k`-basis of `R(ν)` (`basisOfSymm`). This is the setting of Kang–Kashiwara, arXiv:1102.4677v4,
§3, which use the basis theorem over a commutative base ring.

`BasisTheorem.lean` proves the theorem over an integral domain with factorized data, through
the faithful polynomial representation. Here it is transported to any commutative ring by base
change from the universal symmetric data `univQ Q` over the domain `UnivRing I`
(`BaseChange.lean`): for a ring map `φ : U → k` carrying `Q₀` to `Q`, and any ring map
`F : R_U(ν) → T` into a `k`-algebra compatible with `φ`, generators of `R_k(ν)` may be sent to
the `F`-images of generators (`liftAlong`). Applied to `T = k ⊗_U R_U(ν)`, the standard family
of `R_k(ν)` maps to the base change of the standard basis of `R_U(ν)`, which is linearly
independent. Spanning holds over any commutative ring (`span_stdElt`).
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace KLRAlgebra

section liftAlong

variable {U : Type*} [CommRing U] {T : Type*} [Ring T] [Algebra k T]
  (φ : U →+* k) {Q₀ : I → I → MvPolynomial (Fin 2) U} {Q : I → I → MvPolynomial (Fin 2) k}
  (hQ : ∀ a b, a ≠ b → MvPolynomial.map φ (Q₀ a b) = Q a b) {ν : Multiset I}
  (F : KLRAlgebra U Q₀ ν →+* T) (hF : ∀ c, F (algebraMap U _ c) = algebraMap k T (φ c))

/-- The `F`-images of the generators of `R_U(ν)`. -/
noncomputable def genAlong : Gen ν → T
  | .idem i => F (e i)
  | .dot a => F (x a)
  | .cross j => F (ψ j)

/-- The free `k`-algebra on the generators maps to `T` through `genAlong`. -/
noncomputable def freeAlong : FreeAlgebra k (Gen ν) →ₐ[k] T :=
  FreeAlgebra.lift k (genAlong F)

include hQ hF in
theorem freeAlong_rel ⦃u v : FreeAlgebra k (Gen ν)⦄ (h : Rel k Q ν u v) :
    freeAlong F u = freeAlong F v := by
  have hfe : ∀ i, freeAlong F (fe k ν i) = F (e i) := fun i => FreeAlgebra.lift_ι_apply _ _
  have hfx : ∀ a, freeAlong F (fx k ν a) = F (x a) := fun a => FreeAlgebra.lift_ι_apply _ _
  have hfψ : ∀ j, freeAlong F (fψ k ν j) = F (ψ j) := fun j => FreeAlgebra.lift_ι_apply _ _
  have hev {n : ℕ} (y : Fin n → FreeAlgebra k (Gen ν)) (p : MvPolynomial (Fin n) k) :
      freeAlong F (ncEval y p) = ncEval (fun a => freeAlong F (y a)) p := by
    have := map_ncEval (RingHom.id k) (freeAlong F).toRingHom
      (fun c => (freeAlong F).commutes c) y p
    rw [MvPolynomial.map_id] at this
    exact this
  have hevF {n : ℕ} (y : Fin n → KLRAlgebra U Q₀ ν) (p : MvPolynomial (Fin n) U) :
      F (ncEval y p) = ncEval (fun a => F (y a)) (MvPolynomial.map φ p) :=
    map_ncEval φ F hF y p
  cases h with
  | idem_mul i j =>
    rw [map_mul, hfe, hfe, ← map_mul, e_mul_e]
    split_ifs <;> simp [hfe]
  | idem_sum =>
    rw [map_sum, map_one]; simp only [hfe]; rw [← map_sum, sum_e, map_one]
  | dot_idem a i => rw [map_mul, map_mul, hfe, hfx, ← map_mul, ← map_mul, x_mul_e]
  | cross_idem j i => rw [map_mul, map_mul, hfe, hfe, hfψ, ← map_mul, ← map_mul, ψ_mul_e]
  | cross_zero j h => rw [map_zero, hfψ, ψ_eq_zero j h, map_zero]
  | dot_dot a b => rw [map_mul, map_mul, hfx, hfx, ← map_mul, ← map_mul, x_mul_x]
  | cross_cross j l h => rw [map_mul, map_mul, hfψ, hfψ, ← map_mul, ← map_mul, ψ_mul_ψ j l h]
  | dot_cross a j h₁ h₂ =>
    rw [map_mul, map_mul, hfx, hfψ, ← map_mul, ← map_mul, x_mul_ψ a j h₁ h₂]
  | dot_cross_left j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, hfx, hfx, hfψ, hfe, ← map_mul, ← map_mul,
      ← map_sub, ← map_mul, dot_cross_left]
    split_ifs <;> simp [hfe]
  | dot_cross_right j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, hfx, hfx, hfψ, hfe, ← map_mul, ← map_mul,
      ← map_sub, ← map_mul, dot_cross_right]
    split_ifs <;> simp [hfe]
  | cross_sq j h i =>
    rw [map_mul, map_mul, hfψ, hfe, ← map_mul, ← map_mul, ψ_sq j h i]
    split_ifs with hc
    · simp
    · rw [map_mul, map_mul, hfe, hev, hevF, hQ _ _ hc]
      congr 2
      funext a; fin_cases a <;> simp [hfx]
  | braid j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, map_mul, map_mul, hfψ, hfψ, hfe, ← map_mul,
      ← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_mul, braid j h i]
    split_ifs with hc
    · rw [map_mul, map_mul, hfe, hev, hevF, map_qbar, hQ _ _ hc.2]
      congr 2
      funext a; fin_cases a <;> simp [hfx]
    · simp

/-- Generators of `R_k(ν)` go to the `F`-images of the generators of `R_U(ν)`. -/
noncomputable def liftAlong : KLRAlgebra k Q ν →ₐ[k] T :=
  RingQuot.liftAlgHom k ⟨freeAlong F, freeAlong_rel φ hQ F hF⟩

theorem liftAlong_mk (u : FreeAlgebra k (Gen ν)) :
    liftAlong φ hQ F hF (mk k Q ν u) = freeAlong F u :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem liftAlong_e (i : Seq ν) : liftAlong φ hQ F hF (e i) = F (e i) := by
  rw [e, liftAlong_mk]; exact FreeAlgebra.lift_ι_apply _ _

@[simp] theorem liftAlong_x (a : Fin (Multiset.card ν)) :
    liftAlong φ hQ F hF (x a) = F (x a) := by
  rw [x, liftAlong_mk]; exact FreeAlgebra.lift_ι_apply _ _

@[simp] theorem liftAlong_ψ (j : ℕ) : liftAlong φ hQ F hF (ψ j) = F (ψ j) := by
  rw [ψ, liftAlong_mk]; exact FreeAlgebra.lift_ι_apply _ _

theorem liftAlong_ψw (ρ : List ℕ) : liftAlong φ hQ F hF (ψw ρ) = F (ψw ρ) := by
  simp [ψw, map_list_prod, List.map_map, Function.comp_def]

theorem liftAlong_pol_map (p : MvPolynomial (Fin (Multiset.card ν)) U) :
    liftAlong φ hQ F hF (pol (MvPolynomial.map φ p)) = F (pol p) := by
  have h : ((liftAlong φ hQ F hF).toRingHom.comp (pol (k := k) (Q := Q) (ν := ν)).toRingHom).comp
      (MvPolynomial.map φ) = F.comp (pol (k := U) (Q := Q₀) (ν := ν)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.map_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes, ← hF,
        ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    · intro a
      simp [pol_X]
  exact congrArg (fun G => G p) h

theorem liftAlong_stdElt (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
    (b : Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) :
    liftAlong φ hQ F hF (stdElt ρ b) = F (stdElt ρ b) := by
  have hm : (monomial b.2.2 (1 : k)) = MvPolynomial.map φ (monomial b.2.2 1) := by
    rw [MvPolynomial.map_monomial, φ.map_one]
  simp only [stdElt, map_mul, liftAlong_ψw, liftAlong_e]
  rw [hm, liftAlong_pol_map]

end liftAlong

variable {ν : Multiset I} {Q : I → I → MvPolynomial (Fin 2) k} (hsym : KLRSymm Q)
  (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)

include hsym hρ in
/-- **KL I, Theorem 2.5** (linear independence), over any commutative ring for symmetric
`Q`, by base change from the universal symmetric data. -/
theorem linearIndependent_stdElt_of_symm : LinearIndependent k (stdElt (k := k) (Q := Q) ρ) := by
  let _ : Algebra (UnivRing I) k := (univMap Q).toAlgebra
  let bU := basis (univQ_factor Q) (fun a b _ => univP_ne_zero Q a b) ρ hρ
  let bT := Algebra.TensorProduct.basis k bU
  let F : KLRAlgebra (UnivRing I) (univQ Q) ν →+*
      k ⊗[UnivRing I] KLRAlgebra (UnivRing I) (univQ Q) ν :=
    (Algebra.TensorProduct.includeRight :
      KLRAlgebra (UnivRing I) (univQ Q) ν →ₐ[UnivRing I] _).toRingHom
  have hF : ∀ c, F (algebraMap (UnivRing I) _ c) =
      algebraMap k (k ⊗[UnivRing I] KLRAlgebra (UnivRing I) (univQ Q) ν) (univMap Q c) := by
    intro c
    change Algebra.TensorProduct.includeRight (algebraMap (UnivRing I) _ c) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (UnivRing I) k]
    rfl
  let Ψ := liftAlong (univMap Q) (fun a b hab => map_univQ Q hsym a b hab) F hF
  refine LinearIndependent.of_comp Ψ.toLinearMap ?_
  have : Ψ.toLinearMap ∘ stdElt (k := k) (Q := Q) ρ = bT := by
    funext b
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply, Ψ, liftAlong_stdElt, bT,
      Algebra.TensorProduct.basis_apply, bU, basis_apply]
    rfl
  rw [this]
  exact bT.linearIndependent

/-- **KL I, Theorem 2.5**, over any commutative ring for symmetric `Q`: the elements
`ψ_{ρ w} x^u e_i` form a basis of `R(ν)`. -/
noncomputable def basisOfSymm :
    Module.Basis (Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) k
      (KLRAlgebra k Q ν) :=
  Module.Basis.mk (linearIndependent_stdElt_of_symm hsym ρ hρ) (span_stdElt ρ hρ).ge

theorem basisOfSymm_apply (b : Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) :
    basisOfSymm hsym ρ hρ b = ψw (ρ b.2.1) * pol (monomial b.2.2 1) * e b.1 := by
  simp [basisOfSymm, stdElt]

end KLRAlgebra

end Categorification.KLR

namespace Categorification.KLR

/-- Factorized data `Q_{ab}(u,v) = P_{ba}(u,v) P_{ab}(v,u)` are symmetric. -/
theorem KLRSymm.of_factor {k : Type*} [CommRing k] {I : Type*}
    {Q P : I → I → MvPolynomial (Fin 2) k}
    (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b)) : KLRSymm Q := by
  intro a b hab
  rw [hPQ a b hab, hPQ b a hab.symm, map_mul, rename_swap_rename_swap, mul_comm]

/-- `KLRSymm.of_factor` with the full factorization hypotheses `hPQ`, `hP` of `basis` as
arguments (`hP` is not needed). Results stated under these hypotheses that rely on results
stated under `KLRSymm Q` pass both through this lemma. -/
theorem KLRSymm.of_factorization {k : Type*} [CommRing k] {I : Type*}
    {Q P : I → I → MvPolynomial (Fin 2) k}
    (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
    (_hP : ∀ a b, a ≠ b → P a b ≠ 0) : KLRSymm Q :=
  KLRSymm.of_factor hPQ

end Categorification.KLR
