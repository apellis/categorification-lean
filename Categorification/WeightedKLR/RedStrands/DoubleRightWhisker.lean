/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleViolatingQuotient

/-!
# Right whiskering of double Stendhal diagrams by red-free words

Webster, arXiv:1309.3796v3, §4.5, before Theorem 4.28. The 2-category `𝒰` acts on the
violating quotient of Definition 4.27 by attaching black diagrams on the right. This file
constructs the underlying functors: appending a word `v` without red strands to every
boundary, and whiskering every diagram on the right by the identity of `v`. Appending keeps
the leftmost strand, so violated boundaries stay violated and the functor descends to the
violating quotient. A morphism `v ⟶ v'` of the presented category gives a natural
transformation by left whiskering, by the interchange law.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

variable {I : Type*} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type*}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

/-- Concatenation of words is the tensor product of the region-labelled objects. -/
theorem obj_tensor_obj (μ : X) (w v : List (DoubleStrand I ℓ)) :
    (obj RD (fun r => (Λ r).val) μ w).tensor
        (obj RD (fun r => (Λ r).val) (endWeight RD (fun r => (Λ r).val) μ w) v) =
      obj RD (fun r => (Λ r).val) μ (w ++ v) := by
  simp only [obj, Obj.tensor, colours_append]

theorem obj_tensor_obj_of_eq {μ μ' : X} {w : List (DoubleStrand I ℓ)}
    (h : endWeight RD (fun r => (Λ r).val) μ w = μ') (v : List (DoubleStrand I ℓ)) :
    (obj RD (fun r => (Λ r).val) μ w).tensor (obj RD (fun r => (Λ r).val) μ' v) =
      obj RD (fun r => (Λ r).val) μ (w ++ v) := by
  subst h; exact obj_tensor_obj μ w v

/-- A word without red strands. -/
def RedFree (v : List (DoubleStrand I ℓ)) : Prop := v.filterMap DoubleStrand.redLabel = []

/-- Append a red-free word on the right of a double Stendhal triple. -/
def appendRight {μ ν : X} (v : List (DoubleStrand I ℓ)) (hv : RedFree v)
    (hν : endWeight RD (fun r => (Λ r).val) μ v = ν) (b : DoubleStendhalTriple RD Λ 0 μ) :
    DoubleStendhalTriple RD Λ 0 ν :=
  ⟨⟨b.val.word ++ v, by rw [List.filterMap_append, b.val.redOrder, hv, List.append_nil]⟩, by
    have h := b.property
    rw [← hν]
    simp only [DoubleBoundary.rightWeight, endWeight, List.map_append, List.sum_append] at h ⊢
    rw [← add_assoc, h]⟩

theorem appendRight_isViolated {μ ν : X} (v : List (DoubleStrand I ℓ)) (hv : RedFree v)
    (hν : endWeight RD (fun r => (Λ r).val) μ v = ν)
    {b : DoubleStendhalTriple RD Λ 0 μ} (hb : b.val.IsViolated) :
    (appendRight v hv hν b).val.IsViolated := by
  obtain ⟨s, hs⟩ := hb
  refine ⟨s, ?_⟩
  change (b.val.word ++ v).head? = _
  cases h : b.val.word with
  | nil => simp [h] at hs
  | cons a w => simpa [h] using hs

/-- The right weight of a triple is the end weight of its word. -/
theorem endWeight_word {μ : X} (b : DoubleStendhalTriple RD Λ 0 μ) :
    endWeight RD (fun r => (Λ r).val) 0 b.val.word = μ :=
  b.property

/-- The boundary object of an appended triple is the tensor product. -/
theorem tripleObj_appendRight {μ ν : X} (v : List (DoubleStrand I ℓ)) (hv : RedFree v)
    (hν : endWeight RD (fun r => (Λ r).val) μ v = ν)
    (b : DoubleStendhalTriple RD Λ 0 μ) :
    tripleObj P (appendRight v hv hν b) =
      P.obj ((obj RD (fun r => (Λ r).val) 0 b.val.word).tensor
        (obj RD (fun r => (Λ r).val) μ v)) := by
  rw [obj_tensor_obj_of_eq (endWeight_word b)]; rfl

/-- `appendRight` on the objects of the boundary category. -/
abbrev appendRightObj {μ ν : X} (v : List (DoubleStrand I ℓ)) (hv : RedFree v)
    (hν : endWeight RD (fun r => (Λ r).val) μ v = ν)
    (x : BoundaryCategory P μ) : BoundaryCategory P ν :=
  appendRight v hv hν x

/-- Right whiskering of diagrams by the identity of a red-free word. -/
def whiskerRightHom {μ ν : X} (v : List (DoubleStrand I ℓ)) (hv : RedFree v)
    (hν : endWeight RD (fun r => (Λ r).val) μ v = ν)
    {x y : BoundaryCategory P μ} (f : x ⟶ y) :
    appendRightObj P v hv hν x ⟶ appendRightObj P v hv hν y :=
  InducedCategory.homMk (eqToHom (tripleObj_appendRight P v hv hν x) ≫
    P.wRAt (0 : X) f.hom (obj RD (fun r => (Λ r).val) μ v) rfl rfl ≫
      eqToHom (tripleObj_appendRight P v hv hν y).symm)

theorem ok_endR {μ : X} (x : BoundaryCategory P μ) (v : List (DoubleStrand I ℓ)) :
    (signature RD (fun r => (Λ r).val)).ok (obj RD (fun r => (Λ r).val) (0 : X) x.val.word).endR
      (obj RD (fun r => (Λ r).val) μ v).word := by
  change (signature RD (fun r => (Λ r).val)).ok
    ((signature RD (fun r => (Λ r).val)).endR (0 : X)
      (colours RD (fun r => (Λ r).val) 0 x.val.word))
    (colours RD (fun r => (Λ r).val) μ v)
  rw [colours_endR, endWeight_word]
  exact colours_ok ..

/-- Right whiskering by the identity of a red-free word, as a functor between boundary
categories (Webster, arXiv:1309.3796v3, §4.5, before Theorem 4.28). -/
@[simps obj]
def whiskerRight {μ ν : X} (v : List (DoubleStrand I ℓ)) (hv : RedFree v)
    (hν : endWeight RD (fun r => (Λ r).val) μ v = ν) :
    BoundaryCategory P μ ⥤ BoundaryCategory P ν where
  obj := appendRightObj P v hv hν
  map := whiskerRightHom P v hv hν
  map_id x := by
    ext
    have h := P.wRAt_id (r := (0 : X)) rfl _ (ok_endR P x v)
    simp only [whiskerRightHom, InducedCategory.homMk_hom, InducedCategory.id_hom]
    erw [h]
    simp
  map_comp f g := by
    ext
    simp only [whiskerRightHom, InducedCategory.homMk_hom, InducedCategory.comp_hom]
    erw [P.wRAt_comp (r := (0 : X)) rfl rfl rfl]
    simp

instance {μ ν : X} (v : List (DoubleStrand I ℓ)) (hv : RedFree v)
    (hν : endWeight RD (fun r => (Λ r).val) μ v = ν) :
    (whiskerRight P v hv hν (μ := μ)).Additive where
  map_add {_ _ f g} := by
    ext
    show eqToHom _ ≫ P.wRAt (0 : X) (f.hom + g.hom) _ rfl rfl ≫ eqToHom _ =
      (eqToHom _ ≫ P.wRAt (0 : X) f.hom _ rfl rfl ≫ eqToHom _) +
        (eqToHom _ ≫ P.wRAt (0 : X) g.hom _ rfl rfl ≫ eqToHom _)
    rw [P.wRAt_add, Preadditive.add_comp, Preadditive.comp_add]

instance {μ ν : X} (v : List (DoubleStrand I ℓ)) (hv : RedFree v)
    (hν : endWeight RD (fun r => (Λ r).val) μ v = ν) :
    (whiskerRight P v hv hν (μ := μ)).Linear k where
  map_smul {_ _} f a := by
    ext
    show eqToHom _ ≫ P.wRAt (0 : X) (a • f.hom) _ rfl rfl ≫ eqToHom _ =
      a • (eqToHom _ ≫ P.wRAt (0 : X) f.hom _ rfl rfl ≫ eqToHom _)
    rw [P.wRAt_smul, Linear.smul_comp, Linear.comp_smul]

/-- Right whiskering by a red-free word on the violating quotients. It is well defined
because appending a word keeps the leftmost strand. -/
def violatingWhiskerRight {μ ν : X} (v : List (DoubleStrand I ℓ)) (hv : RedFree v)
    (hν : endWeight RD (fun r => (Λ r).val) μ v = ν) :
    ViolatingCategory P μ ⥤ ViolatingCategory P ν :=
  DoubleViolatingQuotient.lift k _ (whiskerRight P v hv hν ⋙ violatingFunctor P _) fun x hx => by
    exact DoubleViolatingQuotient.id_eq_zero k _ (appendRight_isViolated v hv hν hx)

theorem violatingFunctor_comp_violatingWhiskerRight {μ ν : X} (v : List (DoubleStrand I ℓ))
    (hv : RedFree v) (hν : endWeight RD (fun r => (Λ r).val) μ v = ν) :
    violatingFunctor P μ ⋙ violatingWhiskerRight P v hv hν =
      whiskerRight P v hv hν ⋙ violatingFunctor P ν :=
  rfl

theorem composable {μ : X} (x : BoundaryCategory P μ) (v : List (DoubleStrand I ℓ)) :
    (obj RD (fun r => (Λ r).val) (0 : X) x.val.word).Composable
      (obj RD (fun r => (Λ r).val) μ v) :=
  ⟨colours_ok .., (colours_endR ..).trans (endWeight_word x), colours_ok ..⟩

section Natural

variable {μ ν : X} {v v' : List (DoubleStrand I ℓ)} (hv : RedFree v) (hv' : RedFree v')
  (hν : endWeight RD (fun r => (Λ r).val) μ v = ν)
  (hν' : endWeight RD (fun r => (Λ r).val) μ v' = ν)
  (φ : P.obj (obj RD (fun r => (Λ r).val) μ v) ⟶ P.obj (obj RD (fun r => (Λ r).val) μ v'))

/-- A diagram between red-free words, placed to the right of a boundary. -/
def whiskerLeftApp (x : BoundaryCategory P μ) :
    (whiskerRight P v hv hν).obj x ⟶ (whiskerRight P v' hv' hν').obj x :=
  InducedCategory.homMk (eqToHom (tripleObj_appendRight P v hv hν x) ≫
    P.wL (obj RD (fun r => (Λ r).val) (0 : X) x.val.word) φ ≫
      eqToHom (tripleObj_appendRight P v' hv' hν' x).symm)

/-- A diagram between red-free words gives a natural transformation between right
whiskerings, by the interchange law. -/
def whiskerLeft : whiskerRight P v hv hν ⟶ whiskerRight P v' hv' hν' where
  app := whiskerLeftApp P hv hv' hν hν' φ
  naturality x y f := by
    ext
    simp only [InducedCategory.comp_hom, whiskerRight, whiskerRightHom, whiskerLeftApp,
      InducedCategory.homMk_hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    erw [reassoc_of% (P.wRAt_comp_wL (r := (0 : X))
      (a' := obj RD (fun r => (Λ r).val) (0 : X) y.val.word) (composable P x v) f.hom φ rfl rfl)]

@[simp] theorem whiskerLeft_app_hom (x : BoundaryCategory P μ) :
    ((whiskerLeft P hv hv' hν hν' φ).app x).hom =
      eqToHom (tripleObj_appendRight P v hv hν x) ≫
        P.wL (obj RD (fun r => (Λ r).val) (0 : X) x.val.word) φ ≫
          eqToHom (tripleObj_appendRight P v' hv' hν' x).symm :=
  rfl

theorem whiskerLeft_id :
    whiskerLeft P hv hv hν hν (𝟙 _) = 𝟙 (whiskerRight P v hv hν) := by
  ext x
  rw [whiskerLeft_app_hom, P.wL_id_of_composable (composable P x v)]
  simp
  rfl

theorem whiskerLeft_comp {v'' : List (DoubleStrand I ℓ)} (hv'' : RedFree v'')
    (hν'' : endWeight RD (fun r => (Λ r).val) μ v'' = ν)
    (φ' : P.obj (obj RD (fun r => (Λ r).val) μ v') ⟶
      P.obj (obj RD (fun r => (Λ r).val) μ v'')) :
    whiskerLeft P hv hv'' hν hν'' (φ ≫ φ') =
      whiskerLeft P hv hv' hν hν' φ ≫ whiskerLeft P hv' hv'' hν' hν'' φ' := by
  ext x
  rw [NatTrans.comp_app, InducedCategory.comp_hom, whiskerLeft_app_hom, whiskerLeft_app_hom,
    whiskerLeft_app_hom, P.wL_comp]
  simp

/-- A diagram between red-free words gives a natural transformation between right
whiskerings on the violating quotients (Webster, arXiv:1309.3796v3, §4.5, before
Theorem 4.28). -/
def violatingWhiskerLeft :
    violatingWhiskerRight P v hv hν ⟶ violatingWhiskerRight P v' hv' hν' :=
  CategoryTheory.Quotient.natTransLift _
    (Functor.whiskerRight (whiskerLeft P hv hv' hν hν' φ) (violatingFunctor P ν))

theorem violatingWhiskerLeft_id :
    violatingWhiskerLeft P hv hv hν hν (𝟙 _) = 𝟙 (violatingWhiskerRight P v hv hν) := by
  rw [violatingWhiskerLeft, whiskerLeft_id, Functor.whiskerRight_id']
  exact CategoryTheory.Quotient.natTransLift_id _ _

theorem violatingWhiskerLeft_comp {v'' : List (DoubleStrand I ℓ)} (hv'' : RedFree v'')
    (hν'' : endWeight RD (fun r => (Λ r).val) μ v'' = ν)
    (φ' : P.obj (obj RD (fun r => (Λ r).val) μ v') ⟶
      P.obj (obj RD (fun r => (Λ r).val) μ v'')) :
    violatingWhiskerLeft P hv hv'' hν hν'' (φ ≫ φ') =
      violatingWhiskerLeft P hv hv' hν hν' φ ≫
        violatingWhiskerLeft P hv' hv'' hν' hν'' φ' := by
  rw [violatingWhiskerLeft, violatingWhiskerLeft, violatingWhiskerLeft,
    CategoryTheory.Quotient.comp_natTransLift, whiskerLeft_comp, Functor.whiskerRight_comp]

end Natural

end Categorification.Stendhal.DoubleDiagram
