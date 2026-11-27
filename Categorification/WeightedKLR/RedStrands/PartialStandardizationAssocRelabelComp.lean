/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocCutRelabel

/-!
# Composing relabellings of red strands

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. To compare
the two nestings of the cuts of an iterated partial standardization, whose one-step models live
over the alphabets `Fin ((a + m) + r)` and `Fin (a + (m + r))` of red strands, the affine input
quotients of the blocks are compared along relabellings of red strands. Relabellings compose
(`relabelHom_comp_cast`), the affine input quotient of a block is natural for relabellings of
the ambient alphabet (`redSubfamilyProjection_relabel`), and changing the inclusion of the
block for an equal one changes the quotient by the identification of the tensor product
algebras of equal labels (`redSubfamilyProjection_congr`).

## Main definitions

* `Stendhal.tensorProductAlgebraCast`: `T^{Λ₁}(ν) ≃ T^{Λ₂}(ν)` for equal labels `Λ₁ = Λ₂`.
-/

noncomputable section

namespace Categorification.KLR

namespace KLRAlgebra

variable {I₁ I₂ I₃ : Type*} [DecidableEq I₁] [DecidableEq I₂] [DecidableEq I₃]
  {k : Type*} [CommRing k]
  {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
  {Q₃ : I₃ → I₃ → MvPolynomial (Fin 2) k}
  {ν₁ : Multiset I₁} {ν₂ : Multiset I₂} {ν₃ ν₃' : Multiset I₃}

/-- **Relabellings compose**: if the composite of two relabellings of sequences is a third one
followed by the identification of equal weights, so is the composite of the relabellings of
KLR algebras. -/
theorem relabelHom_comp_cast (R₁ : SeqRelabel k Q₁ Q₂ ν₁ ν₂) (R₂ : SeqRelabel k Q₂ Q₃ ν₂ ν₃)
    (R₃ : SeqRelabel k Q₁ Q₃ ν₁ ν₃') (h : ν₃' = ν₃)
    (hR : ∀ s, R₂.equiv (R₁.equiv s) = Seq.cast h (R₃.equiv s)) (z : KLRAlgebra k Q₁ ν₁) :
    relabelHom R₂ (relabelHom R₁ z) = castKLR Q₃ h (relabelHom R₃ z) := by
  have H := ext_of_mul ((relabelHom R₂).toLinearMap ∘ₗ (relabelHom R₁).toLinearMap)
    ((castKLR Q₃ h).toAlgHom.toLinearMap ∘ₗ (relabelHom R₃).toLinearMap)
    (fun a b => by simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      map_mul])
    (fun a b => by simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      map_mul])
    (by simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_one])
    (fun s => by
      change relabelHom R₂ (relabelHom R₁ (e s)) = castKLR Q₃ h (relabelHom R₃ (e s))
      rw [relabelHom_e, relabelHom_e, relabelHom_e, castKLR_e, hR])
    (fun a => by
      change relabelHom R₂ (relabelHom R₁ (x a)) = castKLR Q₃ h (relabelHom R₃ (x a))
      rw [relabelHom_x, relabelHom_x, relabelHom_x, castKLR_x]
      exact congrArg x (Fin.ext rfl))
    (fun j _ => by
      change relabelHom R₂ (relabelHom R₁ (ψ j)) = castKLR Q₃ h (relabelHom R₃ (ψ j))
      rw [relabelHom_ψ, relabelHom_ψ, relabelHom_ψ, castKLR_ψ])
  exact LinearMap.congr_fun H z

end KLRAlgebra

end Categorification.KLR

namespace Categorification.Stendhal

open KLR KLRAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {m n₁ n₂ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k)

/-- The tensor product algebras of equal labels are identified. -/
def tensorProductAlgebraCast {Λ₁ Λ₂ : Fin n₂ → I →₀ ℕ} (h : Λ₁ = Λ₂) (ν : Multiset I) :
    TensorProductAlgebra k Q Λ₁ ν ≃ₐ[k] TensorProductAlgebra k Q Λ₂ ν := by
  subst h; exact AlgEquiv.refl

@[simp] theorem tensorProductAlgebraCast_rfl (Λ : Fin n₂ → I →₀ ℕ) (ν : Multiset I)
    (t : TensorProductAlgebra k Q Λ ν) : tensorProductAlgebraCast Q (rfl : Λ = Λ) ν t = t :=
  rfl

variable (Λ : Fin n₂ → I →₀ ℕ)

omit [DecidableEq I] in
/-- Relabelling the red strands of a weight along `f₁` and then along `e` is relabelling along
`e ∘ f₁`. -/
theorem map_sumMap_comp {n₀ : ℕ} (e : Fin n₁ → Fin n₂) (f₁ : Fin n₀ → Fin n₁)
    (μ : Multiset (I ⊕ Fin n₀)) :
    μ.map (Sum.map (id : I → I) (e ∘ f₁)) =
      (μ.map (Sum.map (id : I → I) f₁)).map (Sum.map (id : I → I) e) := by
  rw [Multiset.map_map, Sum.map_comp_map]
  rfl

/-- **Relabellings of red strands compose.** -/
theorem stendhalRelabel_comp {n₀ : ℕ} (e : Fin n₁ → Fin n₂) (he : Function.Injective e)
    (f₁ : Fin n₀ → Fin n₁) (hf₁ : Function.Injective f₁) (μ : Multiset (I ⊕ Fin n₀))
    (z : KLRAlgebra k (stendhalQ Q (Λ ∘ e ∘ f₁)) μ) :
    relabelEquiv (stendhalRelabel Q Λ e he (μ.map (Sum.map (id : I → I) f₁)))
        (relabelEquiv (stendhalRelabel Q (Λ ∘ e) f₁ hf₁ μ) z) =
      castKLR (stendhalQ Q Λ) (map_sumMap_comp e f₁ μ)
        (relabelEquiv (stendhalRelabel Q Λ (e ∘ f₁) (he.comp hf₁) μ) z) :=
  relabelHom_comp_cast _ _ _ _ (fun _ => Subtype.ext (funext fun _ =>
    Sum.map_map _ _ _ _ _)) z

variable {Λ}

/-- **The affine input quotient of a block is natural for relabellings of the ambient alphabet**:
the quotient of the block `f₁` of the alphabet `Fin n₁`, relabelled along `e`, is the quotient of
the block `e ∘ f₁`. -/
theorem redSubfamilyProjection_relabel (e : Fin n₁ → Fin n₂) (he : Function.Injective e)
    (f₁ : Fin m → Fin n₁) (hf₁ : Function.Injective f₁) (ν : Multiset I)
    (w : KLRAlgebra k (stendhalQ Q (Λ ∘ e))
      ((stendhalWeight m ν).map (Sum.map (id : I → I) f₁))) :
    redSubfamilyProjection Q (Λ ∘ e) f₁ hf₁ ν w =
      redSubfamilyProjection Q Λ (e ∘ f₁) (he.comp hf₁) ν
        (castKLR (stendhalQ Q Λ) (map_sumMap_comp e f₁ _).symm
          (relabelEquiv (stendhalRelabel Q Λ e he _) w)) := by
  obtain ⟨u, rfl⟩ := (relabelEquiv (redSubfamilyRelabel Q (Λ ∘ e) f₁ hf₁ ν)).surjective w
  have hc := stendhalRelabel_comp Q Λ e he f₁ hf₁ (stendhalWeight m ν) u
  change relabelEquiv (stendhalRelabel Q Λ e he _)
      (relabelEquiv (redSubfamilyRelabel Q (Λ ∘ e) f₁ hf₁ ν) u) = _ at hc
  rw [hc, castKLR_symm_castAlg]
  change _ = redSubfamilyProjection Q Λ (e ∘ f₁) (he.comp hf₁) ν
    (relabelEquiv (redSubfamilyRelabel Q Λ (e ∘ f₁) (he.comp hf₁) ν) u)
  simp only [redSubfamilyProjection, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]
  rfl

/-- **Equal inclusions of a block give the same affine input quotient**, up to the
identification of the tensor product algebras of equal labels. -/
theorem redSubfamilyProjection_congr {f f' : Fin m → Fin n₂} (h : f = f')
    (hf : Function.Injective f) (hf' : Function.Injective f') (ν : Multiset I)
    (w : KLRAlgebra k (stendhalQ Q Λ) ((stendhalWeight m ν).map (Sum.map (id : I → I) f))) :
    tensorProductAlgebraCast Q (congrArg (Λ ∘ ·) h) ν (redSubfamilyProjection Q Λ f hf ν w) =
      redSubfamilyProjection Q Λ f' hf' ν
        (castKLR (stendhalQ Q Λ)
          (congrArg (fun g => (stendhalWeight m ν).map (Sum.map (id : I → I) g)) h) w) := by
  subst h; rfl

end Categorification.Stendhal
