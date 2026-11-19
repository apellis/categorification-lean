/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackContext

/-!
# The cover functor on whiskered relations

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The reflected image of a double
diagram placed between two words is the reflected image of the diagram, whiskered by the
reflected words, with the two sides exchanged (`coverLin_whisker`). Consequently, if a class
of 2-morphisms of the target presentation is closed under composition, linear combinations
and whiskering by reflected words, and contains the images of the relations of a presentation
of double diagrams, then it contains the image of the whole tensor ideal
(`coverLin_mem_of_mem_ideal`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams TwoRep

universe w u v v' v₁

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)
  {k : Type w} [CommRing k] (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k)

local notation "RD" => blackDatum W hC
local notation "Λ" => redWeight W
local notation "κ" => coverColourMap W hC o
local notation "CM" => coverMirror W hC o

/-- **Reflection of a whiskered double linear combination.** Placing `f` between `u` and `v`
and then reflecting it gives the reflection of `f`, placed between the reflections of `v`
and of `u`. -/
theorem coverLin_whisker {a b : Obj (signature RD Λ)} (f : LinDiagram k a b) (ha : a.WF)
    {u : Obj (signature RD Λ)} {v : List (signature RD Λ).Colour} (hw : a.WhiskerOK u v)
    (hb : Nonempty (a ⟶ b)) :
    ∃ (e₁ : Q.obj ((κ).obj ((CM).obj (a.whisker u v))) =
        Q.obj (((κ).obj ((CM).obj a)).whisker ((κ).obj ((CM).leftObj a v)) ((κ).word ((CM).word u.word))))
      (e₂ : Q.obj (((κ).obj ((CM).obj b)).whisker ((κ).obj ((CM).leftObj a v))
        ((κ).word ((CM).word u.word))) = Q.obj ((κ).obj ((CM).obj (b.whisker u v)))),
      coverLin W hC o Q σ (LinDiagram.whisker f u v hw) =
        eqToHom e₁ ≫ Q.whisk (coverLin W hC o Q σ f) ((κ).obj ((CM).leftObj a v))
          ((κ).word ((CM).word u.word)) ≫ eqToHom e₂ := by
  let P := coverZero W hC o Q σ
  have hwf := coverZero_wfDom W hC o Q σ
  have hP : ∀ r, coverLin W hC o Q σ (P.rel r) = 0 := fun r => r.2.2.2.2
  have e := coverFunctor_lin W hC o P Q σ hwf hP (LinDiagram.whisker f u v hw)
  rw [← LinDiagram.whisk_of_ok f hw, ← Presentation.whisk_lin] at e
  unfold coverFunctor at e
  rw [Functor.comp_map, SigMirror.lift_whisk _ _ _ _ _ ha hw hb] at e
  simp only [Functor.map_comp, eqToHom_map] at e
  have hw' := (CM).toMirrorColourMap.whiskerOK ha hw
  have hb' : Nonempty ((CM).obj a ⟶ (CM).obj b) := hb.map (CM).toLayerMap.functor.map
  unfold coverKernelFunctor at e
  erw [LocalMap.liftGen_whisk (hw := hw') (hb := hb')] at e
  rw [LinDiagram.whisk_of_ok f hw] at e
  have hf := coverFunctor_lin W hC o P Q σ hwf hP f
  unfold coverFunctor coverKernelFunctor at hf
  rw [Functor.comp_map] at hf
  erw [hf] at e
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc] at e
  exact ⟨_, _, e.symm⟩

end Categorification.Stendhal.DoubleDiagram
