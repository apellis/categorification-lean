/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockJuxtapositionCuts
import Categorification.WeightedKLR.RedStrands.BraidedViolatedQuotient
import Categorification.WeightedKLR.RedStrands.ParabolicAffineQuotients
import Mathlib.Algebra.Category.AlgCat.Basic

/-!
# Horizontal products of Stendhal diagrams

Webster, arXiv:1309.3796v2, §5.1 after Definition 5.4 and §6.1, Lemma 6.8.
Juxtapose the diagrams in a list of blocks, allowing a red crossing inside a block.
To descend this map to the exterior product of the violated quotients, it suffices to
kill the juxtaposed loading idempotents with one locally violated component. In particular
no flatness of either the algebras or their quotients over the ground ring is needed.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra BraidedStendhalAlgebra
open scoped TensorProduct

universe u v
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

abbrev diagramAlgebra (B : RedBlock I ℓ) := BraidedStendhalAlgebra k Q (Λ ∘ B.label) B.black
abbrev quotientAlgebra (B : RedBlock I ℓ) := ViolQuotient k Q (Λ ∘ B.label) B.black

/-- Right-associated external product; the empty product is the scalar algebra. -/
abbrev external (F : RedBlock I ℓ → AlgCat.{max u v} k) : List (RedBlock I ℓ) → AlgCat.{max u v} k
  | [] => AlgCat.of k (ULift.{u} k)
  | B :: Bs => AlgCat.of k (F B ⊗[k] external F Bs)

abbrev diagrams := external (fun B : RedBlock I ℓ => AlgCat.of k (diagramAlgebra Q Λ B))
abbrev quotients := external (fun B : RedBlock I ℓ => AlgCat.of k (quotientAlgebra Q Λ B))

/-- Impose the violated diagrams in every component of the exterior product. -/
def projection : (Bs : List (RedBlock I ℓ)) → diagrams Q Λ Bs →ₐ[k] quotients Q Λ Bs
  | [] => AlgHom.id k _
  | B :: Bs => Algebra.TensorProduct.map (violMk k Q (Λ ∘ B.label) B.black) (projection Bs)

theorem projection_surjective : ∀ Bs, Function.Surjective (projection Q Λ Bs)
  | [] => Function.surjective_id
  | _ :: Bs => Algebra.TensorProduct.map_surjective _ _ violMk_surjective (projection_surjective Bs)

/-- The tensor of the idempotents at the individual loadings. -/
def loadingIdem : (Bs : List (RedBlock I ℓ)) → Loadings Bs → diagrams Q Λ Bs
  | [], _ => 1
  | B :: Bs, s => ofKLR k Q (Λ ∘ B.label) B.black (e s.1) ⊗ₜ loadingIdem Bs s.2

private theorem sum_idem (B : RedBlock I ℓ) :
    ∑ s : Seq B.localWeight, ofKLR k Q (Λ ∘ B.label) B.black (e s) = 1 := by
  rw [← map_sum, sum_e, map_one]

private theorem zero_on_one {C : Type*} [AddCommGroup C] [Module k C] :
    ∀ Bs (g : diagrams Q Λ Bs →ₗ[k] C), (∀ s, g (loadingIdem Q Λ Bs s) = 0) → g 1 = 0
  | [], g, hg => hg PUnit.unit
  | B :: Bs, g, hg => by
    change g ((1 : diagramAlgebra Q Λ B) ⊗ₜ (1 : diagrams Q Λ Bs)) = 0
    rw [← sum_idem Q Λ B, TensorProduct.sum_tmul, map_sum]
    apply Finset.sum_eq_zero
    intro s _
    exact zero_on_one Bs (g ∘ₗ TensorProduct.mk k _ _ _) (fun t => hg (s,t))

/-- The juxtaposed top projector is spanned by the individual loading projectors. -/
theorem one_mem_span_loadingIdem (Bs : List (RedBlock I ℓ)) :
    (1 : diagrams Q Λ Bs) ∈ Submodule.span k (Set.range (loadingIdem Q Λ Bs)) := by
  let U := Submodule.span k (Set.range (loadingIdem Q Λ Bs))
  apply (Submodule.Quotient.mk_eq_zero U).1
  exact zero_on_one Q Λ Bs U.mkQ (fun s => (Submodule.Quotient.mk_eq_zero U).2
    (Submodule.subset_span ⟨s,rfl⟩))

/-- Descent from the actual local violated ideals, using their loading generators. -/
theorem exists_factor {C : Type*} [Ring C] [Algebra k C] :
    ∀ Bs (F : diagrams Q Λ Bs →ₐ[k] C),
    (∀ s, Violated Bs s → F (loadingIdem Q Λ Bs s) = 0) →
    ∃ G : quotients Q Λ Bs →ₐ[k] C, ∀ x, G (projection Q Λ Bs x) = F x
  | [], F, _ => ⟨F, fun _ => rfl⟩
  | B :: Bs, F, hF => by
    let fl : diagramAlgebra Q Λ B →ₐ[k] C := F.comp Algebra.TensorProduct.includeLeft
    let fr : diagrams Q Λ Bs →ₐ[k] C := F.comp Algebra.TensorProduct.includeRight
    have hl : (violIdeal k Q (Λ ∘ B.label) B.black).ringCon ≤ RingCon.ker fl.toRingHom := by
      apply (TwoSidedIdeal.ringCon_le_iff (J := TwoSidedIdeal.ker fl.toRingHom)).mp
      apply TwoSidedIdeal.span_le.mpr
      rintro _ ⟨s,hs,rfl⟩
      exact (TwoSidedIdeal.mem_ker _).2 (zero_on_one Q Λ Bs
        (F.toLinearMap ∘ₗ TensorProduct.mk k _ _ _) (fun t => hF (s,t) (.inl hs)))
    let gl := (violIdeal k Q (Λ ∘ B.label) B.black).ringCon.liftₐ fl hl
    obtain ⟨gr,hgr⟩ := exists_factor Bs fr (fun t ht => by
      change F ((1 : diagramAlgebra Q Λ B) ⊗ₜ loadingIdem Q Λ Bs t) = 0
      rw [← sum_idem Q Λ B, TensorProduct.sum_tmul, map_sum]
      exact Finset.sum_eq_zero fun s _ => hF (s,t) (.inr ht))
    have hcomm : ∀ x y, Commute (gl x) (gr y) := by
      intro x y
      obtain ⟨x,rfl⟩ := violMk_surjective x
      obtain ⟨y,rfl⟩ := projection_surjective Q Λ Bs y
      rw [hgr]; change Commute (F (x ⊗ₜ 1)) (F (1 ⊗ₜ y))
      apply Commute.map _ F
      simp [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul]
    refine ⟨Algebra.TensorProduct.lift gl gr hcomm, ?_⟩
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      rw [projection, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, hgr]
      change F (x ⊗ₜ 1) * F (1 ⊗ₜ y) = F (x ⊗ₜ y)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

local notation "S" => stendhalQ Q Λ

/-- Read a local braided diagram in the common KLR alphabet, with only black dots. -/
def readBlock (B : RedBlock I ℓ) : diagramAlgebra Q Λ B →ₐ[k] KLRAlgebra k S B.weight :=
  (relabelEquiv (redSubfamilyRelabel Q Λ B.label B.label.injective B.black)).toAlgHom.comp
    (toKLR k Q (Λ ∘ B.label) B.black)

theorem readBlock_idem (B : RedBlock I ℓ) (s : Seq B.localWeight) :
    readBlock Q Λ B (ofKLR k Q (Λ ∘ B.label) B.black (e s)) = e (Seq.map B.colour s) := by
  rw [readBlock, AlgHom.comp_apply, toKLR_ofKLR_e]
  exact relabelHom_e _ _

/-- Concatenate local diagrams using the KLR horizontal inclusions. The unit is the sum
of the idempotents of the concatenated loadings, not the unit of the ambient algebra. -/
def juxtapose : (Bs : List (RedBlock I ℓ)) → diagrams Q Λ Bs →ₗ[k] KLRAlgebra k S (weightSum Bs)
  | [] => (Algebra.ofId k _).toLinearMap ∘ₗ ULift.algEquiv.toLinearMap
  | B :: Bs => concat S _ _ ∘ₗ TensorProduct.map (readBlock Q Λ B).toLinearMap (juxtapose Bs)

theorem juxtapose_tmul (B : RedBlock I ℓ) (Bs) (x : diagramAlgebra Q Λ B) (y : diagrams Q Λ Bs) :
    juxtapose Q Λ (B :: Bs) (x ⊗ₜ y) = concat S _ _ (readBlock Q Λ B x ⊗ₜ juxtapose Q Λ Bs y) :=
  congrArg (concat S _ _) (TensorProduct.map_tmul _ _ x y)

theorem juxtapose_mul : ∀ Bs (x y : diagrams Q Λ Bs),
    juxtapose Q Λ Bs (x*y) = juxtapose Q Λ Bs x * juxtapose Q Λ Bs y
  | [], x, y => map_mul ((Algebra.ofId k _).comp ULift.algEquiv.toAlgHom) x y
  | B :: Bs, x, y => by
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => rw [add_mul, map_add, map_add, add_mul, hx, hz]
    | tmul x z =>
      induction y using TensorProduct.inductionOn with
      | add y w hy hw => rw [mul_add, map_add, map_add, mul_add, hy, hw]
      | tmul y w => rw [Algebra.TensorProduct.tmul_mul_tmul, juxtapose_tmul, juxtapose_tmul,
          juxtapose_tmul, map_mul, juxtapose_mul Bs, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul]

theorem juxtapose_loadingIdem : ∀ Bs (s : Loadings Bs),
    juxtapose Q Λ Bs (loadingIdem Q Λ Bs s) = e (place Bs s)
  | [], _ => by
    change algebraMap k _ 1 = e (default : Seq (0 : Multiset (I ⊕ Fin ℓ)))
    rw [map_one, ← sum_e (Q := S) (ν := 0), Fintype.sum_subsingleton _ default]
  | _ :: Bs, s => by
    rw [loadingIdem, juxtapose_tmul, readBlock_idem, juxtapose_loadingIdem Bs, concat_e_tmul_e]; rfl

end Categorification.Stendhal.RedBlock
