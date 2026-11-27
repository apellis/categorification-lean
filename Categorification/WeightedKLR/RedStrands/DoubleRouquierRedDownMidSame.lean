/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownBraidQ
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownBigon
import Categorification.TwoRep.RouqMixedNonpositive
import Categorification.KLR.CyclotomicAction.GlobalNilpotent

/-!
# A red strand between two downward strands of the same colour

Webster, arXiv:1309.3796v3, (4.1) read downward with the red strand in the middle, proof of
Theorem 4.25. For two downward strands of the same colour `i`, the two ways of moving the
strands of `[i, r, i]` past each other differ by `∑_{t < n} y₀^t y₂^{n-1-t}`
(`DownMidSame`). We derive this from the other relations: precomposed with the quotient crossing
`a′` on the left strand, the left side becomes, by the naturality (4.4d) of `a′` for the
downward crossing and the bigon (4.2), the crossing followed by the `n`-th power of the right
dot; the right side becomes, by the bigon and the naturality of `a′` for dots, the `n`-th power
of the left dot followed by the crossing, plus the correction. These agree by the nilHecke
relation of the Rouquier family (`tau_comp_powComp`). So `DownMidSame` holds when the whiskered
quotient crossing is an epimorphism (`downMidSame_of_epi`).
-/

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram
open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot TwoRep

section Generic
variable {𝒞 : Type*} [Bicategory 𝒞] {x₀ x₁ x₁' x₂ x₃ : 𝒞}
  {a : x₀ ⟶ x₁} {b : x₁ ⟶ x₂} {c : x₀ ⟶ x₁'} {d : x₁' ⟶ x₂} {e e' : x₂ ⟶ x₃}

/-- A conjugated right whiskering commutes with a left whiskering by naturality. -/
theorem whiskerConj_whiskerLeft (Qa : a ≫ b ⟶ c ≫ d) (Y : e ⟶ e') :
    (α_ a b e).inv ≫ Qa ▷ e ≫ (α_ c d e).hom ≫ c ◁ d ◁ Y =
      a ◁ b ◁ Y ≫ (α_ a b e').inv ≫ Qa ▷ e' ≫ (α_ c d e').hom := by
  rw [← associator_naturality_right, ← whisker_exchange_assoc, associator_inv_naturality_right_assoc]

/-- Two conjugated right whiskerings compose to the whiskering of their composite. -/
theorem whiskerConj_comp (Qa : a ≫ b ⟶ c ≫ d) (Da : c ≫ d ⟶ a ≫ b) (Y : b ⟶ b)
    (h : Qa ≫ Da = a ◁ Y) :
    (α_ a b e).inv ≫ Qa ▷ e ≫ (α_ c d e).hom ≫ (α_ c d e).inv ≫ Da ▷ e ≫ (α_ a b e).hom =
      a ◁ (Y ▷ e) := by
  simp only [Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, h, whisker_assoc]
  simp

/-- A conjugated right whiskering of `Qa` slides past `U ▷ e ≫ b ◁ W` when `U` slides
through `Qa`. -/
theorem whiskerConj_slide (Qa : a ≫ b ⟶ c ≫ d) (U : b ⟶ b) (V : c ⟶ c) (W : e ⟶ e)
    (hU : a ◁ U ≫ Qa = Qa ≫ V ▷ d) :
    (α_ a b e).inv ≫ Qa ▷ e ≫ (α_ c d e).hom ≫ (α_ c d e).inv ≫ (V ▷ d) ▷ e ≫
        (c ≫ d) ◁ W ≫ (α_ c d e).hom =
      a ◁ (U ▷ e ≫ b ◁ W) ≫ (α_ a b e).inv ≫ Qa ▷ e ≫ (α_ c d e).hom := by
  simp only [Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, ← hU, comp_whiskerRight_assoc, ← whisker_exchange_assoc,
    whiskerLeft_comp, Category.assoc, ← associator_inv_naturality_middle_assoc,
    ← associator_inv_naturality_right_assoc]

end Generic

section NilHecke
variable {D : Type*} [Category D] [Preadditive D]

/-- The nilHecke relation `τ y₂ⁿ = y₁ⁿ τ + ∑_{t<n} y₁^{n-1-t} y₂^t`, from `τ y₂ - y₁ τ = 1`. -/
theorem tau_comp_powComp_add {Z : D} (τ p q : Z ⟶ Z) (hs : τ ≫ q - p ≫ τ = 𝟙 Z) (n : ℕ) :
    τ ≫ powComp q n =
      powComp p n ≫ τ + ∑ t ∈ Finset.range n, powComp p (n - 1 - t) ≫ powComp q t := by
  have h := tau_comp_powComp (-τ) p q (by rw [← hs]; simp; abel) n
  simp only [Preadditive.neg_comp, Preadditive.comp_neg] at h
  rw [← Finset.sum_range_reflect] 
  have e : ∀ t ∈ Finset.range n, powComp p (n - 1 - (n - 1 - t)) ≫ powComp q (n - 1 - t) =
      powComp p t ≫ powComp q (n - 1 - t) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [show n - 1 - (n - 1 - t) = t by omega]
  rw [Finset.sum_congr rfl e]
  rw [neg_eq_iff_eq_neg.mp h]
  abel

end NilHecke
universe u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}
  {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))

private theorem endPow_mul_endPow {E : Type*} [Category E] {Z : E} (f g : End Z) (s t : ℕ) :
    f ^ t * g ^ s = powComp g s ≫ powComp f t := by
  rw [powComp_eq_endPow, powComp_eq_endPow]
  rfl

private theorem endSum_comp {E : Type*} [Category E] [Preadditive E] {Z W : E} {ι : Type*}
    (s : Finset ι) (F : ι → End Z) (g : Z ⟶ W) :
    (∑ t ∈ s, F t : End Z) ≫ g = ∑ t ∈ s, (F t ≫ g) :=
  Preadditive.sum_comp s F g

private theorem whiskerLeft_finsetSum {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} {ι : Type*}
    (s : Finset ι) (θ : ι → (g ⟶ h)) : f ◁ (∑ j ∈ s, θ j) = ∑ j ∈ s, f ◁ θ j :=
  map_sum (AdditiveWhiskering.whiskerLeftAddHom f g h) θ s

/-- **A red strand between two downward strands of the same colour**, from (4.4d), the bigons
(4.2), the naturality of `a′` for dots and the nilHecke relation, when the quotient crossing
`a′` whiskered by a downward strand is an epimorphism. -/
theorem downMidSame_of_epi (n : Fin ℓ → I → ℕ) (hB : DownBigon S red upIso n)
    (hq : DownQuotCrossNatural S red upIso)
    (hdot : ∀ (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁)
      (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃),
      red r h₂ ◁ S.dot i h₁ ≫ redDownQuot S red upIso r i h₁ h₂ h₃ h₄ =
        redDownQuot S red upIso r i h₁ h₂ h₃ h₄ ≫ S.dot i h₄ ▷ red r h₃)
    (hepi : ∀ (r : Fin ℓ) (i : I) {μ μi μij ρi T : X} (f₁ : μi + RD.iX i = μ)
      (f₂ : μij + RD.iX i = μi) (hR : μi + Λ r = ρi) (e₁ : μij + Λ r = T)
      (q : T + RD.iX i = ρi),
      Epi ((α_ _ _ _).inv ≫ redDownQuot S red upIso r i f₂ e₁ hR q ▷ S.E i f₁ ≫
        (α_ _ _ _).hom)) :
    DownMidSame S red upIso n := by
  intro r i μ μi μij ρ ρi T f₁ f₂ hR e₁ q hr q₃
  have := hepi r i f₁ f₂ hR e₁ q
  refine (cancel_epi ((α_ _ _ _).inv ≫ redDownQuot S red upIso r i f₂ e₁ hR q ▷ S.E i f₁ ≫
    (α_ _ _ _).hom)).1 ?_
  have hnil := tau_comp_powComp_add _ _ _ (S.loc i f₂ f₁).slide_right (n r i)
  have hqi := hq r i i f₁ f₂ e₁ hR q hr q₃ q₃ q f₁ f₂ hR
  have hL := whiskerConj_whiskerLeft (redDownQuot S red upIso r i f₂ e₁ hR q)
    (powComp (S.dot i f₁) (n r i))
  have hb₁ := (hB r i f₁ hR hr q₃).1
  have hb₂ := (hB r i f₂ e₁ hR q).1
  rw [← powComp_eq_endPow] at hb₁ hb₂
  have h1 := whiskerConj_comp (e := S.E i f₁) _ _ _ hb₂
  have h2 : ∀ s t, _ := fun s t => whiskerConj_slide (e := S.E i f₁) _ (powComp (S.dot i f₂) s)
    (powComp (S.dot i q) s) (powComp (S.dot i f₁) t)
    (by rw [whiskerLeft_powComp, RouqFamily.powComp_slide _ _ _ (hdot r i f₂ e₁ hR q), powComp_whiskerRight])
  rw [Preadditive.comp_add]
  simp only [Category.assoc] at hqi ⊢
  rw [reassoc_of% hqi, ← whiskerLeft_comp, hb₁, hL, ← whiskerLeft_comp_assoc,
    whiskerLeft_powComp (S.E i f₂), hnil, AdditiveWhiskering.whiskerLeft_add, Preadditive.add_comp]
  congr 1
  · rw [reassoc_of% h1, powComp_whiskerRight, whiskerLeft_comp_assoc]
  · rw [Finset.sum_congr rfl (fun t _ => endPow_mul_endPow _ _ _ _), whiskerLeft_finsetSum]
    rw [endSum_comp _ _ (α_ (S.E i q) (red r hR) (S.E i f₁)).hom]
    simp only [Preadditive.sum_comp, Preadditive.comp_sum]
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [← powComp_whiskerRight, ← powComp_whiskerRight, ← whiskerLeft_powComp,
      ← powComp_whiskerRight (S.dot i q), ← whiskerLeft_powComp (S.E i q ≫ red r hR)]
    simp only [Category.assoc]
    rw [h2]

end Categorification.Stendhal.DoubleDiagram
