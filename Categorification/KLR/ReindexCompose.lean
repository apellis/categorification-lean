/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ReindexConcat

/-!
# Composing relabellings of KLR algebras

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the intertwining
of the bottom corners); Khovanov–Lauda I (arXiv:0803.4121v2), §2.6.

An algebra map out of a KLR algebra is determined by its values on the generators `e(𝐢)`,
`x_a` and `ψ_k` (`KLRAlgebra.algHom_ext_of_gen`). Hence the isomorphisms attached to
relabellings compose as the bijections of sequences do (`relabelHom_relabelHom`): only the
bijection `Seq ν₁ ≃ Seq ν₂` matters, not how the relabelling was built. Two auxiliary
relabellings: `SeqRelabel.castLeft` (source cast) and `SeqRelabel.ofParams` (the identity of
sequences between parameters that agree at distinct labels).

No new hypothesis.

## Main definitions

* `KLR.SeqRelabel.castLeft`, `KLR.SeqRelabel.ofParams`.

## Main results

* `KLR.KLRAlgebra.algHom_ext_of_gen`, `KLR.KLRAlgebra.relabelHom_relabelHom`,
  `KLR.KLRAlgebra.relabelHom_eq_of_equiv`, `KLR.KLRAlgebra.castKLR_concat_one_tmul_ofParams`,
  `KLR.KLRAlgebra.relabelHom_castLeft`, `KLR.KLRAlgebra.relabelHom_ofParams_self`.
-/

noncomputable section

namespace Categorification.KLR

variable {k : Type*} [CommRing k] {I₁ I₂ I₃ : Type*} [DecidableEq I₁] [DecidableEq I₂]
  [DecidableEq I₃]

namespace SeqRelabel

variable {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}

/-- A relabelling `Seq ν₁ ≃ Seq ν₂` read with source `ν₀ = ν₁`. -/
def castLeft {ν₀ ν₁ : Multiset I₁} {ν₂ : Multiset I₂} (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂)
    (h : ν₀ = ν₁) : SeqRelabel k Q₁ Q₂ ν₀ ν₂ := by
  subst h; exact R

omit [DecidableEq I₁] [DecidableEq I₂] in
theorem castLeft_equiv {ν₀ ν₁ : Multiset I₁} {ν₂ : Multiset I₂} (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂)
    (h : ν₀ = ν₁) (i : Seq ν₀) :
    (R.castLeft h).equiv i = R.equiv (KLRAlgebra.seqCast h i) := by
  subst h; rfl

/-- The identity of sequences, between parameters agreeing at distinct labels. -/
def ofParams {Q₁' : I₁ → I₁ → MvPolynomial (Fin 2) k}
    (hQ : ∀ a b, a ≠ b → Q₁' a b = Q₁ a b) (ν : Multiset I₁) : SeqRelabel k Q₁ Q₁' ν ν where
  card_eq := rfl
  equiv := Equiv.refl _
  equiv_smul _ _ := rfl
  lbl_eq_iff _ _ _ := Iff.rfl
  Q_eq _ _ _ h := hQ _ _ h

omit [DecidableEq I₁] in
@[simp] theorem ofParams_equiv {Q₁' : I₁ → I₁ → MvPolynomial (Fin 2) k}
    (hQ : ∀ a b, a ≠ b → Q₁' a b = Q₁ a b) (ν : Multiset I₁) (i : Seq ν) :
    (ofParams hQ ν).equiv i = i := rfl

end SeqRelabel

namespace KLRAlgebra

variable {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
  {Q₃ : I₃ → I₃ → MvPolynomial (Fin 2) k}

/-- **An algebra map out of a KLR algebra is determined on the generators** `e(𝐢)`, `x_a`,
`ψ_k`. -/
theorem algHom_ext_of_gen {ν : Multiset I₁} {B : Type*} [Semiring B] [Algebra k B]
    {f g : KLRAlgebra k Q₁ ν →ₐ[k] B} (he : ∀ i, f (e i) = g (e i))
    (hx : ∀ a, f (x a) = g (x a)) (hψ : ∀ j, f (ψ j) = g (ψ j)) : f = g := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext t
  cases t with
  | idem i => exact he i
  | dot a => exact hx a
  | cross j => exact hψ j

/-- **Relabellings compose as their bijections of sequences do.** -/
theorem relabelHom_relabelHom {ν₁ : Multiset I₁} {ν₂ : Multiset I₂} {ν₃ : Multiset I₃}
    (R₁ : SeqRelabel k Q₁ Q₂ ν₁ ν₂) (R₂ : SeqRelabel k Q₂ Q₃ ν₂ ν₃)
    (R₃ : SeqRelabel k Q₁ Q₃ ν₁ ν₃) (h : ∀ i, R₃.equiv i = R₂.equiv (R₁.equiv i))
    (z : KLRAlgebra k Q₁ ν₁) :
    relabelHom R₂ (relabelHom R₁ z) = relabelHom R₃ z := by
  have hc : (relabelHom R₂).comp (relabelHom R₁) = relabelHom R₃ :=
    algHom_ext_of_gen (fun i => by simp [h]) (fun a => by simp [Fin.cast_cast])
      (fun j => by simp)
  exact DFunLike.congr_fun hc z

/-- **The isomorphism of a relabelling depends only on its bijection of sequences.** -/
theorem relabelHom_eq_of_equiv {ν₁ : Multiset I₁} {ν₂ : Multiset I₂}
    (R R' : SeqRelabel k Q₁ Q₂ ν₁ ν₂) (h : ∀ i, R.equiv i = R'.equiv i)
    (z : KLRAlgebra k Q₁ ν₁) : relabelHom R z = relabelHom R' z := by
  have hc : relabelHom R = relabelHom R' :=
    algHom_ext_of_gen (fun i => by simp [h]) (fun a => by simp) (fun j => by simp)
  exact DFunLike.congr_fun hc z

/-- Relabelling along `castLeft` is relabelling after the cast. -/
theorem relabelHom_castLeft {ν₀ ν₁ : Multiset I₁} {ν₂ : Multiset I₂}
    (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂) (h : ν₀ = ν₁) (z : KLRAlgebra k Q₁ ν₀) :
    relabelHom (R.castLeft h) z = relabelHom R (castKLR Q₁ h z) := by
  subst h; rfl

/-- The identity relabelling of the same parameters is the identity. -/
theorem relabelHom_ofParams_self {ν : Multiset I₁} (hQ : ∀ a b, a ≠ b → Q₁ a b = Q₁ a b)
    (z : KLRAlgebra k Q₁ ν) : relabelHom (SeqRelabel.ofParams hQ ν) z = z := by
  have hc : relabelHom (SeqRelabel.ofParams hQ ν) = AlgHom.id k (KLRAlgebra k Q₁ ν) :=
    algHom_ext_of_gen (fun i => by simp) (fun a => by simp) (fun j => by simp)
  exact DFunLike.congr_fun hc z

omit [DecidableEq I₂] [DecidableEq I₃] in
/-- `ι_{α,γ}(1 ⊗ ·)` commutes with the identity relabelling between parameters. -/
theorem castKLR_concat_one_tmul_ofParams {Q₁' : I₁ → I₁ → MvPolynomial (Fin 2) k}
    (hQ : ∀ a b, a ≠ b → Q₁' a b = Q₁ a b) {α γ μ : Multiset I₁} (h : α + γ = μ)
    (c : KLRAlgebra k Q₁ γ) :
    castKLR Q₁' h (concat Q₁' α γ (1 ⊗ₜ relabelHom (SeqRelabel.ofParams hQ γ) c)) =
      relabelHom (SeqRelabel.ofParams hQ μ) (castKLR Q₁ h (concat Q₁ α γ (1 ⊗ₜ c))) := by
  subst h
  simp only [castKLR_rfl]
  rw [relabelHom_concat (SeqRelabel.ofParams hQ α) (SeqRelabel.ofParams hQ γ)
    (SeqRelabel.ofParams hQ (α + γ)) (fun _ _ => rfl), Algebra.TensorProduct.map_tmul, map_one]

end KLRAlgebra

end Categorification.KLR
