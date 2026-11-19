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

/-- The colours of a cover word lie in the image of `coverColour`. -/
theorem mem_range_coverColour_of_mem_word {w : List (signature RD Λ).Colour}
    {x : (psig W).Colour} (hx : x ∈ (κ).word ((CM).word w)) :
    x ∈ Set.range (coverColour (I := I) (ℓ := ℓ) o) := by
  change x ∈ (w.map (coverColour o)).reverse at hx
  simp only [List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact ⟨y, rfl⟩

theorem coverLin_zero {a b : Obj (signature RD Λ)} :
    coverLin W hC o Q σ (0 : LinDiagram k a b) = 0 := by
  simpa using coverLin_smul W hC o Q σ (0 : k) (0 : LinDiagram k a b)

/-- **The cover functor on the tensor ideal.** Let `N` be a property of morphisms of `Q`
closed under linear combinations, composition on either side with arbitrary morphisms, and
whiskering by words of cover colours. If `N` holds for the images of the relations of a
presentation `P` with well-formed domains, it holds for the images of every element of the
tensor ideal of `P`. -/
theorem coverLin_mem_of_mem_ideal (P : Presentation.{w, v₁} (signature RD Λ) k)
    (hwf : P.WFDom) (N : ∀ {c d : Obj (psig W)}, (Q.obj c ⟶ Q.obj d) → Prop)
    (hzero : ∀ {c d : Obj (psig W)}, N (0 : Q.obj c ⟶ Q.obj d))
    (hadd : ∀ {c d : Obj (psig W)} {f g : Q.obj c ⟶ Q.obj d}, N f → N g → N (f + g))
    (hsmul : ∀ {c d : Obj (psig W)} (r : k) {f : Q.obj c ⟶ Q.obj d}, N f → N (r • f))
    (hpre : ∀ {c d e : Obj (psig W)} (g : Q.obj c ⟶ Q.obj d) {f : Q.obj d ⟶ Q.obj e},
      N f → N (g ≫ f))
    (hpost : ∀ {c d e : Obj (psig W)} {f : Q.obj c ⟶ Q.obj d} (g : Q.obj d ⟶ Q.obj e),
      N f → N (f ≫ g))
    (hwhisk : ∀ {c d : Obj (psig W)} {f : Q.obj c ⟶ Q.obj d} (U : Obj (psig W))
      (V : List (psig W).Colour), N f →
      (∀ x ∈ U.word, x ∈ Set.range (coverColour (I := I) (ℓ := ℓ) o)) →
      (∀ x ∈ V, x ∈ Set.range (coverColour (I := I) (ℓ := ℓ) o)) → N (Q.whisk f U V))
    (hrel : ∀ i, Nonempty (P.dom i ⟶ P.cod i) → N (coverLin W hC o Q σ (P.rel i)))
    {a b : Obj (signature RD Λ)} {f : LinDiagram k a b} (hf : f ∈ P.ideal a b) :
    N (coverLin W hC o Q σ f) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨kk, u, v, hw, pre, post⟩ := hg
    rw [coverLin_comp, coverLin_comp]
    refine hpre _ (hpost _ ?_)
    cases kk with
    | user i =>
      by_cases hb : Nonempty (P.dom i ⟶ P.cod i)
      · obtain ⟨e₁, e₂, e⟩ := coverLin_whisker W hC o Q σ (P.rel i) (hwf i) hw hb
        rw [show Presentation.AllRel.rel (Presentation.AllRel.user i : P.AllRel) = P.rel i
          from rfl, e]
        refine hpre _ (hpost _ (hwhisk _ _ (hrel i hb) ?_ ?_))
        · intro x hx; exact mem_range_coverColour_of_mem_word W hC o hx
        · intro x hx; exact mem_range_coverColour_of_mem_word W hC o hx
      · have : IsEmpty (P.dom i ⟶ P.cod i) := not_nonempty_iff.mp hb
        have h0 : P.rel i = 0 :=
          Subsingleton.elim (α := (P.dom i ⟶ P.cod i) →₀ k) (P.rel i) 0
        rw [show Presentation.AllRel.rel (Presentation.AllRel.user i : P.AllRel) = P.rel i
          from rfl, h0, LinDiagram.whisker_zero, coverLin_zero]
        exact hzero
    | interchange x hx =>
      erw [coverLin_eq_zero_of_coverZero W hC o Q σ _
        ((coverZero W hC o Q σ).lin_interchange x hx u v hw)]
      exact hzero
  | zero => rw [coverLin_zero]; exact hzero
  | add x y _ _ hx hy => rw [coverLin_add]; exact hadd hx hy
  | smul r x _ hx => rw [coverLin_smul]; exact hsmul r hx

end Categorification.Stendhal.DoubleDiagram
