/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleAllDownBoundary
import Categorification.WeightedKLR.RedStrands.DoubleContent
import Categorification.WeightedKLR.RedStrands.DoubleMorita
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# The signed boundary right module over the all-down corner

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Theorem 4.29 and §4.7, Definition 4.34. In a fixed signed-content block the
all-down objects form a finite family. Morphisms from their sum to a signed
boundary carry the right action of the all-down matrix ring by precomposition.
The factorization of the signed identity makes this module a summand of a
finite free right module.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive QuantumGroup QuantumGroup.UDot
  StringDiagrams KLR KLR.Diagram
open scoped Classical

section Sum

variable {D : Type*} [Category* D] [Preadditive D] {ι : Type*} [Fintype ι]

/-- A finite family as an object of the additive envelope. Its finite indexing type in
`Mat_` is small even if the original family was indexed in a larger universe. -/
private def familySum (X : ι → D) : Mat_ D :=
  ⟨Fin (Fintype.card ι), fun i => X ((Fintype.equivFin ι).symm i)⟩

private def familyMatrixEquiv (X : ι → D) : MatEnd X ≃+* End (familySum X) :=
  let e := Fintype.equivFin ι
  { (Equiv.piCongrLeft' (fun i => ∀ j, X i ⟶ X j) e).trans
      (Equiv.piCongrRight fun i => Equiv.piCongrLeft' (fun j => X (e.symm i) ⟶ X j) e) with
    map_add' := fun _ _ => rfl
    map_mul' := fun f g => by
      exact funext fun i => funext fun j =>
        (Equiv.sum_comp e.symm (fun z => g (e.symm i) z ≫ f z (e.symm j))).symm }

private def summandRetract (X : ι → D) (i : ι) :
    Retract ((Mat_.embedding D).obj (X i)) (familySum X) := by
  let M := familySum X
  let j := Fintype.equivFin ι i
  have h : X i = M.X j := congrArg X ((Fintype.equivFin ι).symm_apply_apply i).symm
  let emb := Mat_.embedding D
  let f := fun j => emb.obj (M.X j)
  let r : Retract (f j) (⨁ f) := ⟨biproduct.ι f j, biproduct.π f j, biproduct.ι_π_self f j⟩
  exact ((Retract.ofIso (eqToIso (congrArg emb.obj h))).trans r).trans
    (Retract.ofIso (Mat_.isoBiproductEmbedding M).symm)

private theorem hom_finite_projective {A B : D} {n : ℕ} (u : Fin n → (B ⟶ A))
    (v : Fin n → (A ⟶ B)) (h : ∑ i, u i ≫ v i = 𝟙 B) :
    Module.Finite (End A)ᵐᵒᵖ (A ⟶ B) ∧ Module.Projective (End A)ᵐᵒᵖ (A ⟶ B) := by
  let e := Preadditive.homSelfLinearEquivEndMulOpposite A
  let H := preadditiveCoyonedaObj A
  let incl : (A ⟶ B) →ₗ[(End A)ᵐᵒᵖ] (Fin n → (End A)ᵐᵒᵖ) :=
    LinearMap.pi (fun i => e.toLinearMap.comp (H.map (u i)).hom)
  let proj : (Fin n → (End A)ᵐᵒᵖ) →ₗ[(End A)ᵐᵒᵖ] (A ⟶ B) := ∑ i,
    ((H.map (v i)).hom.comp e.symm.toLinearMap).comp (LinearMap.proj i)
  have hp : proj.comp incl = LinearMap.id := by
    apply LinearMap.ext
    intro f
    change proj (incl f) = f
    calc
      proj (incl f) = ∑ i, (f ≫ u i) ≫ v i :=
        LinearMap.sum_apply Finset.univ
          (fun i => ((H.map (v i)).hom.comp e.symm.toLinearMap).comp (LinearMap.proj i)) (incl f)
      _ = f := by simp only [Category.assoc, ← comp_sum, h, Category.comp_id]
  exact ⟨Module.Finite.of_surjective proj (fun f => ⟨incl f, DFunLike.congr_fun hp f⟩),
    Module.Projective.of_split incl proj hp⟩

end Sum

universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
    {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
    (ν : Multiset I)

local notation "rightWt" => downRightWeight RD Λ ν
local notation "T" => DoubleStendhalTriple RD Λ 0 rightWt

/-- The sum of all ordered downward boundary objects with ordinary black multiset `ν`. -/
def downSum : Mat_ (ViolatingCategory P rightWt) := familySum (downObj P (ν := ν))

/-- The endomorphisms of the all-down sum are precisely the matrices of morphisms between
its summands. Matrix multiplication and categorical composition use the same order. -/
def downwardMatrixEquivEnd : downwardMatrix P ν ≃+* End (downSum P ν) :=
  familyMatrixEquiv (downObj P (ν := ν))

/-- The right module of a signed boundary: morphisms from the all-down sum, with the
matrix ring acting by precomposition (Webster, arXiv:1309.3796v2, §4.7, Definition 4.34). -/
def boundaryRightModule [DecidableEq I] (b : T) : ModuleCat (downwardMatrix P ν)ᵐᵒᵖ :=
  let H := downSum P ν ⟶ (Mat_.embedding _).obj ((violatingFunctor P rightWt).obj b)
  letI := Module.compHom H (RingEquiv.op (downwardMatrixEquivEnd P ν)).toRingHom
  ModuleCat.of (downwardMatrix P ν)ᵐᵒᵖ H

private theorem downSumRetract (d : T) (hd : d.val.AllDown ∧ d.val.blackContent = ν) :
    Nonempty (Retract ((Mat_.embedding _).obj ((violatingFunctor P rightWt).obj d)) (downSum P ν)) := by
  obtain ⟨s, hs⟩ := (DoubleBoundary.allDownEquiv ν).surjective ⟨d.val, hd⟩
  have he : DoubleBoundary.ofDown s.val s.property = d.val :=
    congrArg (fun z : {x : DoubleBoundary I ℓ // x.AllDown ∧ x.blackContent = ν} => z.val) hs
  have htr : downTriple RD Λ s = d := Subtype.ext he
  cases htr
  exact ⟨summandRetract (downObj P (ν := ν)) s⟩

variable (t : I → I → kˣ)
local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

/-- The signed boundary Hom is a finite projective right module over the endomorphisms of
its all-down sum. This is the projectivity step of Webster, arXiv:1309.3796v2, §§4.5, 4.7,
Theorem 4.29 and Definition 4.34. -/
theorem boundaryHom_finite_projective (b : T) (hb : b.val.signedContent = contentVector ν) :
    let H := downSum Q ν ⟶ (Mat_.embedding _).obj ((violatingFunctor Q rightWt).obj b)
    Module.Finite (End (downSum Q ν))ᵐᵒᵖ H ∧ Module.Projective (End (downSum Q ν))ᵐᵒᵖ H := by
  let π := violatingFunctor Q rightWt
  let E := Mat_.embedding (ViolatingCategory Q rightWt)
  let S : ObjectProperty (ViolatingCategory Q rightWt) := fun d =>
    d.as.val.AllDown ∧ d.as.val.blackContent = ν
  have hle : factorSpan k π.obj (fun d => d.val.AllDown ∧ d.val.blackContent = ν) b b ≤
      factorSpan k id S (π.obj b) (π.obj b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, a, c, rfl⟩
    exact Submodule.subset_span ⟨π.obj d, hd, a, c, rfl⟩
  obtain ⟨n, c, u, v, huv⟩ := finiteFactorization S (hle (id_mem_allDownContentFactorSpan P t b ν hb))
  let r (i : Fin n) := (downSumRetract Q ν (c i).obj.as (c i).property).some
  apply hom_finite_projective (fun i => E.map (u i) ≫ (r i).i) (fun i => (r i).r ≫ E.map (v i))
  calc
    _ = ∑ i, E.map (u i ≫ v i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Category.assoc, (r i).retract_assoc, E.map_comp]
    _ = 𝟙 _ := by rw [← E.map_sum, huv, E.map_id]

/-- Finite projectivity of the signed boundary right module over its all-down matrix
corner (Webster, arXiv:1309.3796v2, §§4.5, 4.7, Theorem 4.29 and Definition 4.34). -/
theorem boundaryRightModule_finite_projective [DecidableEq I] (b : T) (hb : b.val.signedContent = contentVector ν) :
    Module.Finite (downwardMatrix Q ν)ᵐᵒᵖ (boundaryRightModule Q ν b) ∧
      Module.Projective (downwardMatrix Q ν)ᵐᵒᵖ (boundaryRightModule Q ν b) := by
  let H := downSum Q ν ⟶ (Mat_.embedding _).obj ((violatingFunctor Q rightWt).obj b)
  let e := RingEquiv.op (downwardMatrixEquivEnd Q ν)
  have forward : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  have backward : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let f : H ≃ₛₗ[e.symm.toRingHom] (boundaryRightModule Q ν b) :=
    { Equiv.refl H with
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change r • x = e (e.symm r) • x
        rw [e.apply_symm_apply] }
  obtain ⟨hf, hp⟩ := boundaryHom_finite_projective P ν t b hb
  let : Module.Finite (End (downSum Q ν))ᵐᵒᵖ H := hf
  let : Module.Projective (End (downSum Q ν))ᵐᵒᵖ H := hp
  exact ⟨Module.Finite.of_surjective f.toLinearMap f.surjective, Module.Projective.of_equiv f⟩

end Categorification.Stendhal.DoubleDiagram
