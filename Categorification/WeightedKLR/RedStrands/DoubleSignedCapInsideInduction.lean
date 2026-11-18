/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapInside
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBlockInduction

/-!
# Interior crossings in the signed cap induction

The signed cap-block braid equation of the KL spanning argument used in
Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28 is a successor case of the
crossing-filtered induction after projection to the violating quotient.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k) (μ : X)
local notation "S" => signature RD Λ
local notation "B" => DoubleStrand I ℓ

private theorem forward_signedCross {a b c : Obj S} (p : a ⟶ b) (hp : ForwardPath a p)
    (g : b ⟶ c) (L : List B) {x y : B} (h : CanCross x y) (R : List B)
    (hg : Diagram.layers g = signedLayers RD Λ b.start (signedCrossLayers L x y R)) : ForwardPath a (p ≫ g) := by
  cases y with
  | inl l => exact hp.crossBlackLeft g L x l R hg
  | inr r =>
    cases x with
    | inl l => exact .single hp g _ hg (fun h => h)
    | inr => exact False.elim h

/-- The local three-strand braid differs by diagrams with at most two crossings. -/
def HasCapBraidBound (L : List B) (x y : B) (l : Letter I) (R : List B) : Prop :=
  let s := L ++ [x,y,Sum.inl l] ++ R
  let t := L ++ [Sum.inl l,y,x] ++ R
  signedDg RD Λ P μ s t (signedCapBraidLeft L x y l R) -
    signedDg RD Λ P μ s t (signedCapBraidRight L x y l R) ∈ signedCrossingSpan RD Λ P μ s t 2

local notation "capSource" => fun (L U : List B) (l : Letter I) (R : List B) =>
  L ++ [Sum.inl (Letter.dual l)] ++ U ++ [Sum.inl l] ++ R

/-- A bounded three-strand correction discharges the interior crossing
successor case for any linear projection of the actual signed presentation. -/
theorem capBlock_push_crossInside (L U V R : List (DoubleStrand I ℓ))
    (x y : DoubleStrand I ℓ) (l : Letter I) (d : ℕ) (hxy : CanCross x y)
    (hbraid : HasCapBraidBound RD Λ P μ (L ++ [.inl l.dual] ++ U) x y l (V ++ R))
    {a t : Obj S} {M : Type*} [AddCommGroup M] [Module k M]
    (π : (P.obj a ⟶ P.obj t) →ₗ[k] M)
    (p : a ⟶ obj RD Λ μ (capSource L (U ++ [x,y] ++ V) l R))
    (ih : ResolvesSignedCapBlocks k (fun f => π (P.diag f)) p)
    (tail : obj RD Λ μ (L ++ (U ++ [y,x] ++ V) ++ R) ⟶ t) :
    π (P.diag p ≫ signedDg RD Λ P μ (capSource L (U ++ [x,y] ++ V) l R) (L ++ (U ++ [y,x] ++ V) ++ R)
        (signedCrossLayers (L ++ [.inl l.dual] ++ U) x y (V ++ [.inl l] ++ R) ++
          signedCapBlock L (U ++ [y,x] ++ V) l R d) ≫ P.diag tail) ∈
      forwardSpan k (fun f => π (P.diag f)) tail (crossingNumber p + U.length + 3 + V.length) ⊔
      fewerCrossings k (fun f => π (P.diag f)) tail (crossingNumber p + U.length + 3 + V.length) := by
  let blk := signedCapBlock L (U ++ [x,y] ++ V) l R d
  let above := signedCrossLayers (L ++ U) x y (V ++ R)
  have hc : signedChain (capSource L (U ++ [x,y] ++ V) l R) blk (L ++ (U ++ [x,y] ++ V) ++ R) := signedCapBlock_chain ..
  have hg : signedChain (L ++ (U ++ [x,y] ++ V) ++ R) above (L ++ (U ++ [y,x] ++ V) ++ R) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append, above] using
      signedCrossLayers_chain (L ++ U) hxy (V ++ R)
  let f := Diagram.mk _ (chain_signedLayers RD Λ μ hc)
  let g := Diagram.mk _ (chain_signedLayers RD Λ μ hg)
  have he : signedDg RD Λ P μ (capSource L (U ++ [x,y] ++ V) l R) (L ++ (U ++ [y,x] ++ V) ++ R)
      (blk ++ above) = P.diag (f ≫ g) := by
    rw [← signedDg_comp RD Λ P μ hc hg, signedDg_of RD Λ P μ hc, signedDg_of RD Λ P μ hg, P.diag_comp]
  have hex := signedCapBlock_crossInside RD Λ P μ L U V R l d hxy hbraid
  change _ - signedDg RD Λ P μ (capSource L (U ++ [x,y] ++ V) l R)
    (L ++ (U ++ [y,x] ++ V) ++ R) (blk ++ above) ∈ _ at hex
  rw [he] at hex
  have hnum : crossingNumber g = 1 :=
    (crossingNumber_of_signedLayers RD Λ μ g above rfl).trans (signedCrossLayers_crossings _ hxy _)
  apply capBlock_push_of_exchange k (fun f => π (P.diag f)) p ih f L (U ++ [x,y] ++ V) l R d
    rfl rfl g (fun q hq => forward_signedCross RD Λ q hq g _ hxy _ rfl) tail _
    (by simp only [hnum, List.length_append, List.length_cons, List.length_nil]; omega)
  have hsmall := signedCrossingSpan_in_fewerCrossings RD Λ P μ p
    (𝟙 (obj RD Λ μ (L ++ (U ++ [y,x] ++ V) ++ R))) tail π hex
    (m := crossingNumber p + U.length + 3 + V.length) (by
      have h0 : crossingNumber (𝟙 (obj RD Λ μ (L ++ (U ++ [y,x] ++ V) ++ R))) = 0 := rfl
      omega)
  simpa only [Category.id_comp, Preadditive.sub_comp, Preadditive.comp_sub, map_sub,
    P.diag_comp, Category.assoc] using hsmall

end Categorification.Stendhal.DoubleDiagram
