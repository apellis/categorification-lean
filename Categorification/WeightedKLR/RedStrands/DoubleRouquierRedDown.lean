/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedUpSlide
import Categorification.WeightedKLR.RedStrands.DoubleDownRelations
import Categorification.WeightedKLR.RedStrands.DoubleDownContext
import Categorification.WeightedKLR.RedStrands.DoubleDownWhisker

/-!
# Downward dots slide through red strands in a Rouquier family

Webster, arXiv:1309.3796v3, proof of Theorem 4.25. The red/down crossings `a′` (`redDownQuot`)
and `b′` (`redDownDot`) are the mates of the red/up crossings. If the red/up crossings are
natural for upward dots (`UpIsoDotNatural`), then the red/down crossings are natural for
downward dots: these are the downward dot slides past a red strand in the KLR relations of
Definition 4.5 imposed on downward strands (Definition 4.24).

Every instance of these downward relations in a signed context is the whiskering of the bare
relation (`admissibleMap_downRelation_of_bare`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))

section Context

variable {B' : Type*} [Bicategory B'] [∀ a b : B', Preadditive (a ⟶ b)] [AdditiveWhiskering B']
  {k : Type w} [CommRing k] [∀ a b : B', Linear k (a ⟶ b)]
  [∀ (a b c : B') (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B') (g : b ⟶ c), (postcomp a g).Linear k]
  {M : Model (signature RD Λ) B'} (G : GenImg M)
  (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)

theorem rel_cod_perm (r : KLR.Diagram.Rel (I ⊕ Fin ℓ)) : r.cod.word.Perm r.dom.word := by
  cases r <;> simp [KLR.Diagram.Rel.dom, KLR.Diagram.Rel.cod, KLR.Diagram.ob]
  all_goals first
    | exact List.Perm.swap _ _ _
    | exact (List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _) |>.trans
        (List.Perm.swap _ _ _)

/-- **A downward relation in a signed context is killed once the bare relation is.** -/
theorem admissibleMap_downRelation_of_bare (P : Presentation.{w, max u v} (signature RD Λ) k)
    (a : DownRelation X I ℓ)
    (hbare : ∀ (m : X) {x y : X} (ha : Cond x y (downContextObj RD Λ m [] [] a.rel.dom))
      (hb : Cond x y (downContextObj RD Λ m [] [] a.rel.cod)),
      admissibleMap G ha hb (downLinear RD Λ k m [] [] (KLR.Diagram.relation k Q a.rel)) = 0)
    {x y : X} (ha : Cond x y ((addDownRelations RD Λ Q P).dom (.inr a)))
    (hb : Cond x y ((addDownRelations RD Λ Q P).cod (.inr a))) :
    admissibleMap G ha hb ((addDownRelations RD Λ Q P).rel (.inr a)) = 0 := by
  obtain ⟨μ, u, v, r, a', b'⟩ := a
  change admissibleMap G ha hb (downLinear RD Λ k μ u v
    (LinDiagram.whisker (KLR.Diagram.relation k Q r) a' b' _)) = 0
  rw [downLinear_whisker]
  refine admissibleMap_cast_eq_zero G _ _ _ ha hb ?_
  set u' := u ++ a'.word.map DoubleStrand.down
  set v' := b'.map DoubleStrand.down ++ v
  set τ := endWeight RD Λ (endWeight RD Λ μ u') (r.dom.word.map DoubleStrand.down)
  have hτ : endWeight RD Λ (endWeight RD Λ μ u') (r.cod.word.map DoubleStrand.down) = τ :=
    endWeight_map_down_of_perm RD Λ _ (rel_cod_perm r)
  rw [downLinear_eq_whisker RD Λ μ u' v' τ k _ rfl hτ]
  refine admissibleMap_cast_eq_zero G _ _ _ _ _ ?_
  exact admissibleMap_whisker_eq_zero G _ _ _ _ (fun ha' hb' => hbare _ ha' hb') _ _

end Context

/-- The red/down crossing `a′` is natural for downward dots. -/
theorem redDownQuot_dot (hdot : UpIsoDotNatural S red upIso) (r : Fin ℓ) (i : I)
    {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁) (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃)
    (h₄ : μ₂ + RD.iX i = μ₃) :
    red r h₂ ◁ S.dot i h₁ ≫ redDownQuot S red upIso r i h₁ h₂ h₃ h₄ =
      redDownQuot S red upIso r i h₁ h₂ h₃ h₄ ≫ S.dot i h₄ ▷ red r h₃ := by
  apply (mateEquiv (S.adj i h₄) (S.adj i h₁)).injective
  have e₁ := mateEquiv_conjugateEquiv_vcomp (S.adj i h₄) (S.adj i h₁) (S.adj i h₁)
    (redDownQuot S red upIso r i h₁ h₂ h₃ h₄) (S.dot i h₁)
  have e₂ := conjugateEquiv_mateEquiv_vcomp (S.adj i h₄) (S.adj i h₄) (S.adj i h₁)
    (S.dot i h₄) (redDownQuot S red upIso r i h₁ h₂ h₃ h₄)
  simp only [leftAdjointSquareConjugate.vcomp, rightAdjointSquareConjugate.vcomp,
    leftAdjointConjugateSquare.vcomp, rightAdjointConjugateSquare.vcomp] at e₁ e₂
  rw [e₁, e₂, redDownQuot, Equiv.apply_symm_apply, ← S.dotDn_eq_rightMate,
    ← S.dotDn_eq_rightMate]
  exact (hdot r i h₁ h₂ h₃ h₄).symm

/-- The red/down crossing `b′` is natural for downward dots. -/
theorem redDownDot_dot (hdot : UpIsoDotNatural S red upIso) (r : Fin ℓ) (i : I)
    {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁) (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃)
    (h₄ : μ₂ + RD.iX i = μ₃) :
    S.dot i h₄ ▷ red r h₃ ≫ redDownDot S red upIso r i h₁ h₂ h₃ h₄ =
      redDownDot S red upIso r i h₁ h₂ h₃ h₄ ≫ red r h₂ ◁ S.dot i h₁ := by
  have hinv : red r h₃ ◁ S.dotDn i h₁ ≫ (upIso r i h₁ h₂ h₃ h₄).inv =
      (upIso r i h₁ h₂ h₃ h₄).inv ≫ S.dotDn i h₄ ▷ red r h₂ := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, hdot r i h₁ h₂ h₃ h₄]
  have e₁ := mateEquiv_conjugateEquiv_vcomp (S.adjL i h₄) (S.adjL i h₁) (S.adjL i h₁)
    (upIso r i h₁ h₂ h₃ h₄).inv (S.dotDn i h₁)
  have e₂ := conjugateEquiv_mateEquiv_vcomp (S.adjL i h₄) (S.adjL i h₄) (S.adjL i h₁)
    (S.dotDn i h₄) (upIso r i h₁ h₂ h₃ h₄).inv
  simp only [leftAdjointSquareConjugate.vcomp, rightAdjointSquareConjugate.vcomp,
    leftAdjointConjugateSquare.vcomp, rightAdjointConjugateSquare.vcomp] at e₁ e₂
  have hc : ∀ (j : I) {x y : X} (h : x + RD.iX j = y),
      conjugateEquiv (S.adjL j h) (S.adjL j h) (S.dotDn j h) = S.dot j h := fun j _ _ h => by
    rw [RouqFamily.dotDn, Equiv.apply_symm_apply]
  rw [hc, hinv] at e₁
  rw [hc] at e₂
  rw [redDownDot, ← e₂, e₁]
