/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCrossingBigon
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBraidBlackQ
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentationQ

/-!
# Removing a bigon beside a signed cap

Webster, arXiv:1309.3796v2, §4.5, Definition 4.24 and Lemma 4.28.
A black bigon is a lower crossing term by the reflected Reidemeister II
step in Khovanov–Lauda III, arXiv:0807.3250v1, proof of Proposition 3.11.
Red bigons are the identity or the red dot power according to orientation.

This is the version of `DoubleSignedCrossingBigon` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k) (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (L R : List (DoubleStrand I ℓ))

local notation "W" => obj RD Λ μ
local notation "B" => DoubleStrand I ℓ
local notation "bl(" x ")" => (Sum.inl x : B)
local notation "η" => endWeight RD Λ μ L

/-- The black bigon is in crossing degree at most one, with arbitrary signed
strands on either side of its black rectangle. -/
theorem signedBigon_blackQ
    (hP : ∀ r : (CLQ.pres RD k sc).Rel, P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel r)) = 0)
    (x y : Letter I) :
    let s := L ++ [bl(x),bl(y)] ++ R
    signedDg RD Λ P μ s s (signedBigonLayers L R bl(x) bl(y)) ∈ signedCrossingSpan RD Λ P μ s s 1 := by
  classical
  let s := [y,x]
  let A := xLay y x ++ xLay x y
  have hA : SChain s A s := (sChain_xLay y x).append (sChain_xLay x y)
  let F := blackRectangleHomQ RD Λ sc μ L R s P hP s rfl rfl
  have hm := blackRectangleHom_mem_signedCrossingSpanQ RD Λ sc P hP μ L R rfl rfl
    (CLQ.r2 (RD := RD) (k := k) η y x)
  change F (NF.dg (CLQ.pres RD k sc) η s s A) ∈ _ at hm
  dsimp only [F] at hm
  rw [NF.dg_of hA, ← Presentation.lin_of, blackRectangleHom_linQ, blackLinear_of, Presentation.lin_of] at hm
  change signedDg RD Λ P μ (L ++ [bl(x),bl(y)] ++ R) (L ++ [bl(x),bl(y)] ++ R)
    (signedBigonLayers L R bl(x) bl(y)) ∈ _
  rw [signedDg_eq_diag_of_layers RD Λ P μ (signedBigonLayers_chain L R
    (show CanCross bl(x) bl(y) from trivial)) (blackDiagram RD Λ μ L R (mkD RD η A hA))]
  · exact hm
  · rw [layers_blackDiagram_mkD]
    obtain ⟨_ | _,i⟩ := x <;> obtain ⟨_ | _,j⟩ := y <;>
      simp [A, xLay, crosslL, crossrL, signedBigonLayers, signedCrossLayers, crossBlackLeft,
        upwardMateLayers, signedLayers, Sig.shape, blackWord]

section Red

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)

local notation "U" => addRedUpRelations RD Λ k P
local notation "D" => addDownRelations RD Λ (affineCoverQ Q exponents) (U)
local notation "T" => signedCapPassPresentation RD Λ P Q exponents
local notation "C'" => signedCapKLPresentationQ RD Λ sc P Q exponents t

private theorem diag_pow {a : Obj (signature RD Λ)} (d : End a) (n : ℕ) :
    (D).diag (d ^ n) = End.of ((D).diag d) ^ n := by
  induction n with
  | zero => exact (D).diag_id _
  | succ n ih => rw [pow_succ, End.mul_def, Presentation.diag_comp, ih, pow_succ, End.mul_def]

private theorem diagram_pow_zero_crossings {a : Obj (signature RD Λ)} (d : End a)
    (h : crossingNumber d = 0) (n : ℕ) : crossingNumber (d ^ n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, End.mul_def, crossingNumber_comp, h, ih]

private theorem signedBigon_redLeft (r : Fin ℓ) (l : Letter I) :
    let s := L ++ [Sum.inr r, bl(l)] ++ R
    signedDg RD Λ (T) μ s s (signedBigonLayers L R (Sum.inr r) bl(l)) ∈
      signedCrossingSpan RD Λ (T) μ s s 0 := by
  let s := L ++ [Sum.inr r, bl(l)] ++ R
  let raw : End (W s) := moveDiagram RD Λ μ L (.redBlack r l) R ≫
    moveDiagram RD Λ μ L (.blackRed l r) R
  change signedDg RD Λ (T) μ s s _ ∈ _
  rw [signedDg_eq_diag_of_layers RD Λ (T) μ (signedBigonLayers_chain L R
    (show CanCross (Sum.inr r) bl(l) from trivial)) raw rfl]
  obtain ⟨ε,i⟩ := l
  cases ε
  · let d : End (W s) := redDownDotRedLeft RD Λ μ L r i R
    have h : (D).diag raw = (D).diag (d ^ exponents r i) :=
      (redDown_bigon_redLeft RD Λ Q exponents (U) μ L r i R).trans
        (diag_pow RD Λ P Q exponents d _).symm
    rw [show (T).diag raw = (T).diag (d ^ exponents r i) from diag_eq_addRels (D) h]
    exact Submodule.subset_span ⟨d ^ exponents r i,
      (diagram_pow_zero_crossings RD Λ d rfl _).le, rfl⟩
  · have h := (redUpCrossingIso RD Λ P μ L r i R).hom_inv_id
    change (U).diag _ ≫ (U).diag _ = _ at h
    rw [← Presentation.diag_comp, ← (U).diag_id] at h
    have hu : (T).diag raw = (T).diag (𝟙 (W s)) := diag_eq_addRels (D) (diag_eq_addRels (U) h)
    rw [hu]
    exact Submodule.subset_span ⟨𝟙 _, le_rfl, rfl⟩

private theorem signedBigon_redRight (r : Fin ℓ) (l : Letter I) :
    let s := L ++ [bl(l), Sum.inr r] ++ R
    signedDg RD Λ (T) μ s s (signedBigonLayers L R bl(l) (Sum.inr r)) ∈
      signedCrossingSpan RD Λ (T) μ s s 0 := by
  let s := L ++ [bl(l), Sum.inr r] ++ R
  let raw : End (W s) := moveDiagram RD Λ μ L (.blackRed l r) R ≫
    moveDiagram RD Λ μ L (.redBlack r l) R
  change signedDg RD Λ (T) μ s s _ ∈ _
  rw [signedDg_eq_diag_of_layers RD Λ (T) μ (signedBigonLayers_chain L R
    (show CanCross bl(l) (Sum.inr r) from trivial)) raw rfl]
  obtain ⟨ε,i⟩ := l
  cases ε
  · let d : End (W s) := redDownDotBlackLeft RD Λ μ L r i R
    have h : (D).diag raw = (D).diag (d ^ exponents r i) :=
      (redDown_bigon_blackLeft RD Λ Q exponents (U) μ L r i R).trans
        (diag_pow RD Λ P Q exponents d _).symm
    rw [show (T).diag raw = (T).diag (d ^ exponents r i) from diag_eq_addRels (D) h]
    exact Submodule.subset_span ⟨d ^ exponents r i,
      (diagram_pow_zero_crossings RD Λ d rfl _).le, rfl⟩
  · have h := (redUpCrossingIso RD Λ P μ L r i R).inv_hom_id
    change (U).diag _ ≫ (U).diag _ = _ at h
    rw [← Presentation.diag_comp, ← (U).diag_id] at h
    have hu : (T).diag raw = (T).diag (𝟙 (W s)) := diag_eq_addRels (D) (diag_eq_addRels (U) h)
    rw [hu]
    exact Submodule.subset_span ⟨𝟙 _, le_rfl, rfl⟩

/-- Every admissible bigon in the common signed presentation is in crossing
degree at most one. The red cases use only the identity and dot-power bigons. -/
theorem signedCapKL_bigonQ (x y : B) (hxy : CanCross x y) :
    let s := L ++ [x,y] ++ R
    signedDg RD Λ (C') μ s s (signedBigonLayers L R x y) ∈
      signedCrossingSpan RD Λ (C') μ s s 1 := by
  have hT (a b : Obj (signature RD Λ)) : (T).ideal a b ≤ (C').ideal a b :=
    (signedCapPass_ideal_le RD Λ P Q exponents t a b).trans (signedCap_ideal_le_KLQ RD Λ sc P Q exponents t a b)
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      exact signedBigon_blackQ RD Λ sc (C') μ L R
        (signedCapKL_reflectedBlackQ RD Λ sc P Q exponents t) x y
    | inr r =>
      exact signedCrossingSpan_mono RD Λ (C') μ _ _ (Nat.zero_le _) <|
        signedDg_mem_signedCrossingSpan_of_ideal_le RD Λ (T) μ (C') hT _ _
          (signedBigon_redRight RD Λ P μ L R Q exponents r x)
  | inr r =>
    cases y with
    | inl y =>
      exact signedCrossingSpan_mono RD Λ (C') μ _ _ (Nat.zero_le _) <|
        signedDg_mem_signedCrossingSpan_of_ideal_le RD Λ (T) μ (C') hT _ _
          (signedBigon_redLeft RD Λ P μ L R Q exponents r y)
    | inr s => exact hxy.elim

end Red

end Categorification.Stendhal.DoubleDiagram
