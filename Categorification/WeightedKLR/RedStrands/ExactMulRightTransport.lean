/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerCopresentationCriteria
import Categorification.WeightedKLR.RedStrands.RedBlackCrossingTransport

set_option backward.isDefEq.respectTransparency false

/-!
# Transporting embeddings of cokernels along inductions

Background for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Corollary 5.32 (v2: Corollary 5.29): the cokernels of the red-black crossings
used in Lemma 5.23 embed into free modules. A crossing at the end of a loading is induced from
one at fewer strands, along adding a black strand (`appendBlackNU`) or a red strand
(`emptyRedHom`) on the right. Both inductions are exact, so they carry an exact sequence
`A → A → Aⁿ`, `z ↦ z c`, `w ↦ (w gⱼ)ⱼ` (`IsExactMulRight c g`) to the exact sequence
`B → B → Bⁿ⁺¹` for `φ(c)` and the maps `φ(gⱼ)` together with `1 - φ(1)`.

## Main results

* `InductionAlong.isExactMulRight_map`: the transport, given exactness of the induced sequence.
* `Stendhal.isExactMulRight_appendBlack`, `Stendhal.isExactMulRight_emptyRed`: the two cases.
-/

noncomputable section

namespace Categorification.InductionAlong

universe u w

variable {A : Type u} [Ring A] {B : Type u} [Ring B] {φ : A →ₙ+* B}

namespace Ind

variable {N : Type w} [AddCommGroup N] [Module A N] {N' : Type w} [AddCommGroup N']
  [Module A N']

theorem map_add (g g' : N →ₗ[A] N') : map (φ := φ) (g + g') = map g + map g' :=
  ext fun z n => by
    simp only [map_tmul, LinearMap.add_apply, tmul_add]

theorem map_zero' : map (φ := φ) (0 : N →ₗ[A] N') = 0 :=
  ext fun z n => by
    simp only [map_tmul, LinearMap.zero_apply, tmul_zero]

theorem map_sum {ι : Type*} (s : Finset ι) (g : ι → N →ₗ[A] N') :
    map (φ := φ) (∑ j ∈ s, g j) = ∑ j ∈ s, map (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using map_zero'
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, map_add, ih]

/-- An element of the induction of a finite product vanishes when all its components do. -/
theorem eq_zero_of_map_proj {n : ℕ} (y : Ind (Fin n → N) φ)
    (h : ∀ j, map (LinearMap.proj (R := A) (φ := fun _ : Fin n => N) j) y = 0) : y = 0 := by
  have hid : (LinearMap.id : (Fin n → N) →ₗ[A] (Fin n → N)) =
      ∑ j, (LinearMap.single A (fun _ : Fin n => N) j).comp (LinearMap.proj j) := by
    ext x i
    simp [Finset.sum_apply, Pi.single_apply]
  have hy : y = map (φ := φ) LinearMap.id y := by rw [map_id]; rfl
  rw [hy, hid, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_comp, LinearMap.comp_apply, h j, _root_.map_zero]

end Ind

/-- The map `w ↦ (w gⱼ)ⱼ`, from `A` to `Aⁿ`. -/
def rmulPi {n : ℕ} (g : Fin n → A) : lIdeal (1 : A) →ₗ[A] (Fin n → lIdeal (1 : A)) :=
  LinearMap.pi fun j => rmulLIdeal 1 (g j)

theorem exact_rmulLIdeal_rmulPi {n : ℕ} {c : A} {g : Fin n → A} (h : IsExactMulRight c g) :
    Function.Exact (rmulLIdeal 1 c) (rmulPi g) := by
  intro w
  constructor
  · intro hw
    obtain ⟨z, hz⟩ := h.2 w.1 fun j => congrArg Subtype.val (congrFun hw j)
    exact ⟨⟨z, by rw [mem_lIdeal, mul_one]⟩, Subtype.ext hz.symm⟩
  · rintro ⟨z, rfl⟩
    funext j
    exact Subtype.ext (by
      change z.1 * c * g j = 0
      rw [mul_assoc, h.1 j, mul_zero])

/-- **Transport of an embedding of the cokernel**: if induction along `φ` keeps
`A → A → Aⁿ` exact, then `B → B → Bⁿ⁺¹`, `z ↦ z φ(c)`, `w ↦ (w (1 - φ(1)), w φ(gⱼ))`, is
exact. -/
theorem isExactMulRight_map {n : ℕ} {c : A} {g : Fin n → A} (h : IsExactMulRight c g)
    (hex : Function.Exact (Ind.map (φ := φ) (rmulLIdeal 1 c)) (Ind.map (φ := φ) (rmulPi g))) :
    IsExactMulRight (φ c) (Fin.cons (1 - φ 1) fun j => φ (g j)) := by
  constructor
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Fin.cons_zero, mul_sub, mul_one, ← _root_.map_mul, mul_one, sub_self]
    · rw [Fin.cons_succ, ← _root_.map_mul, h.1 j, _root_.map_zero]
  intro w hw
  have hw1 : w * φ 1 = w := by
    have := hw 0
    rw [Fin.cons_zero, mul_sub, mul_one, sub_eq_zero] at this
    exact this.symm
  have hwg : ∀ j, w * φ (g j) = 0 := fun j => by simpa using hw j.succ
  let x := (indLIdealEquiv φ IsIdempotentElem.one).symm ⟨w, hw1⟩
  have hx : Ind.map (rmulPi g) x = 0 := by
    refine Ind.eq_zero_of_map_proj _ fun j => ?_
    rw [← LinearMap.comp_apply, ← Ind.map_comp]
    have hpj : (LinearMap.proj j).comp (rmulPi g) = rmulLIdeal 1 (g j) := rfl
    rw [hpj]
    apply (indLIdealEquiv φ IsIdempotentElem.one).injective
    apply Subtype.ext
    rw [indLIdealEquiv_map_rmulLIdeal φ IsIdempotentElem.one, LinearEquiv.apply_symm_apply,
      _root_.map_zero]
    exact hwg j
  obtain ⟨x', hx'⟩ := (hex x).1 hx
  refine ⟨(indLIdealEquiv φ IsIdempotentElem.one x').1, ?_⟩
  rw [← indLIdealEquiv_map_rmulLIdeal φ IsIdempotentElem.one, hx', LinearEquiv.apply_symm_apply]

end Categorification.InductionAlong

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong

section Black

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

/-- **Adding a black strand on the right** carries an embedding of the cokernel of `z ↦ z c`
into a free module. -/
theorem isExactMulRight_appendBlack (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    {n : ℕ} {c : TensorProductAlgebra k Q Λ ν} {g : Fin n → TensorProductAlgebra k Q Λ ν}
    (h : IsExactMulRight c g) :
    IsExactMulRight (appendBlackNU (Q := Q) (Λ := Λ) i ν c)
      (Fin.cons (1 - appendBlackNU (Q := Q) (Λ := Λ) i ν 1)
        fun j => appendBlackNU (Q := Q) (Λ := Λ) i ν (g j)) :=
  isExactMulRight_map h (appendBlack_ind_map_exact C hQ (exact_rmulLIdeal_rmulPi h))

end Black

section Red

open MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ : Multiset I)

local notation "L₀" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (θ + 0)


section Natural

variable {N N' N'' : Type} [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ 0) N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N]
  [AddCommGroup N'] [Module k N'] [Module (parabolicFactorAlgebra Q Λ θ 0) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N'] [AddCommGroup N''] [Module k N'']
  [Module (parabolicFactorAlgebra Q Λ θ 0) N'']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N'']

variable (hQ : KLRSymm Q)

include hQ in
/-- **Induction along adding the last red strand is exact** on modules over the factor algebra
at `β = ∅`. -/
theorem emptyRed_ind_map_exact (f : N →ₗ[parabolicFactorAlgebra Q Λ θ 0] N')
    (g : N' →ₗ[parabolicFactorAlgebra Q Λ θ 0] N'') (h : Function.Exact f g) :
    Function.Exact (Ind.map (φ := emptyRedHom Q Λ θ) (emptyInputMap Q Λ θ f))
      (Ind.map (φ := emptyRedHom Q Λ θ) (emptyInputMap Q Λ θ g)) := by
  have hS := parabolicStandardMap_exact Q Λ θ 0 hQ f g h
  intro y
  obtain ⟨m, rfl⟩ := emptyRedStandard_surjective Q Λ θ N' hQ y
  rw [← emptyRedStandard_map]
  constructor
  · intro hy
    have h0 : parabolicStandardMap Q Λ θ 0 g m = 0 :=
      emptyRedStandard_injective Q Λ θ N'' hQ (hy.trans (_root_.map_zero _).symm)
    obtain ⟨m', rfl⟩ := (hS m).1 h0
    exact ⟨emptyRedStandard Q Λ θ N hQ m', (emptyRedStandard_map Q Λ θ hQ f m').symm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨m', rfl⟩ := emptyRedStandard_surjective Q Λ θ N hQ x
    rw [← emptyRedStandard_map] at hx
    have hm := emptyRedStandard_injective Q Λ θ N' hQ hx
    rw [← hm, (hS _).2 ⟨m', rfl⟩, _root_.map_zero]

end Natural

section Wrap

variable (P : Type) [AddCommGroup P]
  [Module (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (θ + 0)) P] [Module k P]
  [IsScalarTower k (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (θ + 0)) P]

/-- The module structure on a `T^{λ'}`-module over the factor algebra at `β = ∅`. -/
abbrev oldFactorInst : Module (parabolicFactorAlgebra Q Λ θ 0) P :=
  Module.compHom _ (emptyFactorToOld Q Λ θ).toAlgHom.toRingHom

/-- A `T^{λ'}`-module as a module over `T^{λ'} ⊗ R^{λ_ℓ}_0`. -/
def oldFactorModule : FactorModule Q Λ θ 0 :=
  letI := oldFactorInst Q Λ θ P
  { carrier := P
    tower := ⟨fun c t n => by
      change (emptyFactorToOld Q Λ θ (c • t)) • n = c • (emptyFactorToOld Q Λ θ t • n)
      rw [map_smul, smul_assoc]⟩ }

/-- The input of `EmptyRedInd` for a `T^{λ'}`-module `P` is `P`. -/
def oldInputEquiv : EmptyRedInput Q Λ θ (oldFactorModule Q Λ θ P).carrier ≃ₗ[L₀] P where
  toFun n := n
  invFun n := n
  map_add' _ _ := rfl
  map_smul' t n := by
    rw [RingHom.id_apply]
    change emptyFactorToOld Q Λ θ ((emptyFactorToOld Q Λ θ).symm t) • (show P from n) =
      t • (show P from n)
    rw [AlgEquiv.apply_symm_apply]
  left_inv _ := rfl
  right_inv _ := rfl

variable {P} {P' : Type} [AddCommGroup P']
  [Module (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (θ + 0)) P'] [Module k P']
  [IsScalarTower k (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (θ + 0)) P']

/-- A map of `T^{λ'}`-modules as a map of modules over the factor algebra. -/
def oldFactorMap (h : P →ₗ[L₀] P') :
    (oldFactorModule Q Λ θ P).carrier →ₗ[parabolicFactorAlgebra Q Λ θ 0]
      (oldFactorModule Q Λ θ P').carrier where
  toFun y := h (show P from y)
  map_add' y y' := map_add h (show P from y) (show P from y')
  map_smul' d y := h.map_smul (emptyFactorToOld Q Λ θ d) (show P from y)

variable {P'' : Type} [AddCommGroup P'']
  [Module (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (θ + 0)) P''] [Module k P'']
  [IsScalarTower k (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (θ + 0)) P'']

include Λ in
/-- **Induction along adding the last red strand is exact** on `T^{λ'}`-modules. -/
theorem emptyRed_ind_map_exact' (hQ : KLRSymm Q) {f : P →ₗ[L₀] P'} {g : P' →ₗ[L₀] P''}
    (h : Function.Exact f g) :
    Function.Exact (Ind.map (φ := emptyRedHom Q Λ θ) f) (Ind.map (φ := emptyRedHom Q Λ θ) g) := by
  have hw : Function.Exact (oldFactorMap Q Λ θ f) (oldFactorMap Q Λ θ g) := h
  exact Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := Ind.mapEquiv (oldInputEquiv Q Λ θ P)) (e₂ := Ind.mapEquiv (oldInputEquiv Q Λ θ P'))
    (e₃ := Ind.mapEquiv (oldInputEquiv Q Λ θ P''))
    (Ind.ext fun _ _ => rfl) (Ind.ext fun _ _ => rfl)
    (emptyRed_ind_map_exact Q Λ θ hQ _ _ hw)

end Wrap

/-- **Adding the last red strand** carries an embedding of the cokernel of `z ↦ z c` into a free
module. -/
theorem isExactMulRight_emptyRed (hQ : KLRSymm Q) {n : ℕ} {c : L₀} {g : Fin n → L₀}
    (h : IsExactMulRight c g) :
    IsExactMulRight (emptyRedHom Q Λ θ c)
      (Fin.cons (1 - emptyRedHom Q Λ θ 1) fun j => emptyRedHom Q Λ θ (g j)) :=
  isExactMulRight_map h (emptyRed_ind_map_exact' Q Λ θ hQ (exact_rmulLIdeal_rmulPi h))

end Red

end Categorification.Stendhal
