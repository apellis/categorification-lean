/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionPseudofunctor
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionWhiskerQ
import Categorification.Diagrams.KL3.SymmetryOmega
import Categorification.Diagrams.CLQ.SymmetryOmega
import Categorification.Diagrams.RevBicat
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Category.Cat

/-!
# The black action as a strict pseudofunctor

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28. The Khovanov–Lauda 2-category acts on the
violating quotients: a word `s` acts by right whiskering with its mirror word, and a diagram
acts by the mirror diagram. Since reflection reverses the order of 1-morphisms, the action is
a strict pseudofunctor from the reverse of the Khovanov–Lauda bicategory to `Cat`.

This is the version of `DoubleBlackActionPseudofunctor` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

section Append

variable {μ ν₁ ν₂ : X} {v₁ v₂ : List (DoubleStrand I ℓ)} (hv₁ : RedFree v₁)
  (hv₂ : RedFree v₂) (h₁ : endWeight RD (fun r => (Λ r).val) μ v₁ = ν₁)
  (h₂ : endWeight RD (fun r => (Λ r).val) ν₁ v₂ = ν₂)

end Append

section Nil

variable {μ : X} (hv : RedFree ([] : List (DoubleStrand I ℓ)))
  (h : endWeight RD (fun r => (Λ r).val) μ [] = μ)

end Nil

section Words

variable {μ ν₁ ν₂ : X} (s t : List (Letter I)) (ht : wt RD μ t = ν₁)
  (hs : wt RD ν₁ s = ν₂) (hst : wt RD μ (s ++ t) = ν₂)

end Words

end Categorification.Stendhal.DoubleDiagram

namespace Categorification.RevBicat

open CategoryTheory Bicategory

universe w' v' u'

variable {B : Type u'} [Bicategory.{w', v'} B]

/-- The 1-cell dual of a strict bicategory is strict. -/
instance [Bicategory.Strict B] : Bicategory.Strict (RevBicat B) where
  id_comp f := Bicategory.Strict.comp_id (B := B) f
  comp_id f := Bicategory.Strict.id_comp (B := B) f
  assoc f g h := (Bicategory.Strict.assoc (B := B) h g f).symm
  leftUnitor_eqToIso f := Bicategory.Strict.rightUnitor_eqToIso (B := B) f
  rightUnitor_eqToIso f := Bicategory.Strict.leftUnitor_eqToIso (B := B) f
  associator_eqToIso {a b c d} f g h := by
    change (@Bicategory.associator B _ d.as c.as b.as a.as h g f).symm = _
    rw [Bicategory.Strict.associator_eqToIso]; ext; simp

end Categorification.RevBicat

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel,
    P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)

section Transport

variable {μ ν₁ ν₂ : X} {s s' t t' u u' : List (Letter I)}

/-- A diagram whiskered on the right, read through equalities of its boundary objects with
objects `ob μ s`, acts by left whiskering (the generic form of `blackMap_wRObQ`). -/
theorem blackMap_wRAt_of_eqQ {A A' B : Obj (psig RD)} (hA : A = ob RD ν₁ s)
    (hA' : A' = ob RD ν₁ s') (hB : B = ob RD μ t) {r : X} (hr : A.start = r)
    (hr' : A'.start = r) (η : (CLQ.pres RD k sc).obj A ⟶ (CLQ.pres RD k sc).obj A')
    (hc : A.tensor B = ob RD μ u) (hc' : A'.tensor B = ob RD μ u') (hu : u = s ++ t)
    (hu' : u' = s' ++ t) (ht : wt RD μ t = ν₁) (hs : wt RD ν₁ s = ν₂)
    (hs' : wt RD ν₁ s' = ν₂) (hU : wt RD μ u = ν₂) (hU' : wt RD μ u' = ν₂)
    (E : blackAct P u hU = blackAct P t ht ⋙ blackAct P s hs)
    (E' : blackAct P u' hU' = blackAct P t ht ⋙ blackAct P s' hs') :
    blackMapQ P hP hU hU' (eqToHom (congrArg (CLQ.pres RD k sc).obj hc).symm ≫
        (CLQ.pres RD k sc).wRAt r η B hr hr' ≫ eqToHom (congrArg (CLQ.pres RD k sc).obj hc')) =
      eqToHom E ≫ Functor.whiskerLeft (blackAct P t ht)
          (blackMapQ P hP hs hs' (eqToHom (congrArg (CLQ.pres RD k sc).obj hA).symm ≫ η ≫
            eqToHom (congrArg (CLQ.pres RD k sc).obj hA'))) ≫ eqToHom E'.symm := by
  subst hu hu' hA hA' hB hr hs
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← blackActAppend_hom_eq P s t ht rfl hU, ← blackActAppend_inv_eq P s' t ht hs' hU']
  exact blackMap_wRObQ P hP ht rfl hs' η hU hU'

/-- A diagram whiskered on the left, read through equalities of its boundary objects with
objects `ob μ s`, acts by right whiskering (the generic form of `blackMap_wLObQ`). -/
theorem blackMap_wL_of_eqQ {A B B' : Obj (psig RD)} (hA : A = ob RD ν₁ s)
    (hB : B = ob RD μ t) (hB' : B' = ob RD μ t')
    (ψ : (CLQ.pres RD k sc).obj B ⟶ (CLQ.pres RD k sc).obj B')
    (hc : A.tensor B = ob RD μ u) (hc' : A.tensor B' = ob RD μ u') (hu : u = s ++ t)
    (hu' : u' = s ++ t') (ht : wt RD μ t = ν₁) (ht' : wt RD μ t' = ν₁)
    (hs : wt RD ν₁ s = ν₂) (hU : wt RD μ u = ν₂) (hU' : wt RD μ u' = ν₂)
    (E : blackAct P u hU = blackAct P t ht ⋙ blackAct P s hs)
    (E' : blackAct P u' hU' = blackAct P t' ht' ⋙ blackAct P s hs) :
    blackMapQ P hP hU hU' (eqToHom (congrArg (CLQ.pres RD k sc).obj hc).symm ≫
        (CLQ.pres RD k sc).wL A ψ ≫ eqToHom (congrArg (CLQ.pres RD k sc).obj hc')) =
      eqToHom E ≫ Functor.whiskerRight
          (blackMapQ P hP ht ht' (eqToHom (congrArg (CLQ.pres RD k sc).obj hB).symm ≫ ψ ≫
            eqToHom (congrArg (CLQ.pres RD k sc).obj hB'))) (blackAct P s hs) ≫
        eqToHom E'.symm := by
  subst hu hu' hA hB hB'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← blackActAppend_hom_eq P s t ht hs hU, ← blackActAppend_inv_eq P s t' ht' hs hU']
  exact blackMap_wLObQ P hP ht ht' ψ hs hU hU'

end Transport

section Bicat

open Presentation

variable {l m n : (CLQ.pres RD k sc).Bicat}

/-- The letters of a 1-morphism of the Khovanov–Lauda bicategory. -/
def homLettersQ (f : l ⟶ m) : List (Letter I) := (Bicat.Hom.obj f).word.map Col.l

theorem homObj_eqQ (f : l ⟶ m) : Bicat.Hom.obj f = ob RD m.region (homLettersQ f) := by
  have he : Sig.eR (RD := RD) (Bicat.Hom.obj f).start (Bicat.Hom.obj f).word = m.region :=
    Bicat.Hom.endR_eq f
  exact (wf_eq_ob (Bicat.Hom.obj f) (Bicat.Hom.wf f)).trans
    (congrArg (fun r => ob RD r (homLettersQ f)) he)

theorem homWtQ (f : l ⟶ m) : wt RD m.region (homLettersQ f) = l.region :=
  (congrArg Obj.start (homObj_eqQ f)).symm.trans (Bicat.Hom.start_eq f)

theorem homLetters_compQ (f : l ⟶ m) (g : m ⟶ n) :
    homLettersQ (f ≫ g) = homLettersQ f ++ homLettersQ g := by
  exact List.map_append ..

theorem homLetters_idQ (l : (CLQ.pres RD k sc).Bicat) : homLettersQ (𝟙 l) = [] := rfl

variable {f g h : l ⟶ m}

/-- A 2-morphism of the Khovanov–Lauda bicategory, as a diagram between objects `ob μ s`. -/
def homTrQ (η : f ⟶ g) :
    (CLQ.pres RD k sc).obj (ob RD m.region (homLettersQ f)) ⟶
      (CLQ.pres RD k sc).obj (ob RD m.region (homLettersQ g)) :=
  eqToHom (congrArg (CLQ.pres RD k sc).obj (homObj_eqQ f)).symm ≫
    (η : (CLQ.pres RD k sc).obj (Bicat.Hom.obj f) ⟶ (CLQ.pres RD k sc).obj (Bicat.Hom.obj g)) ≫
      eqToHom (congrArg (CLQ.pres RD k sc).obj (homObj_eqQ g))

theorem homTr_idQ (f : l ⟶ m) : homTrQ (𝟙 f) = 𝟙 _ := by
  simp only [homTrQ]
  erw [Category.id_comp, eqToHom_trans, eqToHom_refl]

theorem homTr_compQ (η : f ⟶ g) (θ : g ⟶ h) : homTrQ (η ≫ θ) = homTrQ η ≫ homTrQ θ := by
  simp only [homTrQ, Category.assoc]
  erw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact congrArg _ (Category.assoc (obj := (CLQ.pres RD k sc).Presented) _ _ _)

end Bicat

section Pseudofunctor

/-- A composite of 1-morphisms acts by the composite of their actions, in the reverse order. -/
theorem blackAct_homLetters_compQ {l m n : (CLQ.pres RD k sc).Bicat} (f : l ⟶ m) (g : m ⟶ n) :
    blackAct P (homLettersQ (f ≫ g)) (homWtQ (f ≫ g)) =
      blackAct P (homLettersQ g) (homWtQ g) ⋙ blackAct P (homLettersQ f) (homWtQ f) :=
  (blackAct_congr P (homLetters_compQ f g) _ (by rw [← homLetters_compQ]; exact homWtQ _)).trans
    (blackAct_append_eq P _ _ (homWtQ g) (homWtQ f) _)

open Bicategory

/-- The black action of the Khovanov–Lauda 2-category on the violating quotients, as a strict
pseudofunctor from its 1-cell dual to `Cat` (Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28):
a region `μ` goes to the violating quotient with right weight `μ`, a word `s` to right
whiskering by its mirror word, and a diagram to the action of its mirror diagram. -/
def blackActionPseudofunctorQ :
    StrictPseudofunctor (RevBicat (CLQ.pres RD k sc).Bicat) Cat.{max u v w, u} :=
  StrictPseudofunctor.mk''
    { obj := fun a => Cat.of (ViolatingCategory P a.as.region)
      map := fun {a b} f =>
        (blackAct P (homLettersQ (f : b.as ⟶ a.as)) (homWtQ f)).toCatHom
      map₂ := fun {_ _ f g} η => (blackMapQ P hP (homWtQ f) (homWtQ g) (homTrQ η)).toCatHom₂
      map₂_id := fun f => by
        ext1
        exact (congrArg (blackMapQ P hP (homWtQ f) (homWtQ f)) (homTr_idQ f)).trans
          (blackMap_idQ P hP (homWtQ f))
      map₂_comp := fun {_ _ f g h} η θ => by
        ext1
        exact (congrArg (blackMapQ P hP (homWtQ f) (homWtQ h)) (homTr_compQ η θ)).trans
          (blackMap_compQ P hP (homWtQ f) (homWtQ g) (homWtQ h) _ _)
      map_id := fun a => congrArg Functor.toCatHom (blackAct_nil P (homWtQ (𝟙 a.as)))
      map_comp := fun {a b c} f g => congrArg Functor.toCatHom
        (blackAct_homLetters_compQ P (g : c.as ⟶ b.as) f)
      map₂_whisker_left := fun {a b c} f {g g'} η => by
        ext1
        simp only [Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
          Cat.whiskerLeft_toNatTrans, NatTrans.toCatHom₂_toNatTrans]
        exact blackMap_wRAt_of_eqQ P hP (homObj_eqQ g) (homObj_eqQ g') (homObj_eqQ f) _ _ η
          (homObj_eqQ ((g : c.as ⟶ b.as) ≫ (f : b.as ⟶ a.as)))
          (homObj_eqQ ((g' : c.as ⟶ b.as) ≫ (f : b.as ⟶ a.as))) (homLetters_compQ _ _)
          (homLetters_compQ _ _) (homWtQ f) (homWtQ g) (homWtQ g') _ _
          (blackAct_homLetters_compQ P (g : c.as ⟶ b.as) f)
          (blackAct_homLetters_compQ P (g' : c.as ⟶ b.as) f)
      map₂_whisker_right := fun {a b c} {f f'} η g => by
        ext1
        simp only [Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
          Cat.whiskerRight_toNatTrans, NatTrans.toCatHom₂_toNatTrans]
        exact blackMap_wL_of_eqQ P hP (homObj_eqQ g) (homObj_eqQ f) (homObj_eqQ f') η
          (homObj_eqQ ((g : c.as ⟶ b.as) ≫ (f : b.as ⟶ a.as)))
          (homObj_eqQ ((g : c.as ⟶ b.as) ≫ (f' : b.as ⟶ a.as))) (homLetters_compQ _ _)
          (homLetters_compQ _ _) (homWtQ f) (homWtQ f') (homWtQ g) _ _
          (blackAct_homLetters_compQ P (g : c.as ⟶ b.as) f)
          (blackAct_homLetters_compQ P (g : c.as ⟶ b.as) f') }

end Pseudofunctor

end Categorification.Stendhal.DoubleDiagram
