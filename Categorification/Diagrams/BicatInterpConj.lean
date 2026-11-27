/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpChain

/-!
# Images of short chains of layers read through free isomorphisms

The image of a chain of one, two or three layers, whose pieces agree with canonical ones up to
equality of regions and heterogeneous equality, is the composite of the whiskered canonical
generator images `midK M p q γ`, joined by images of arbitrary free 2-morphisms of one's choice
(`admissibleChain₁_conj`, `admissibleChain₂_conj`, `admissibleChain₃_conj`). Since the free
bicategory on a quiver is thin, the joining free 2-morphisms do not matter. These forms let a
polynomial in the images of single layers be compared with the image of a longer chain.
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

variable {S : Signature} {C : Type*} [Bicategory C] (M : Model S C)

/-- **The image of one layer** with canonical pieces, read through free 2-morphisms. -/
theorem admissibleChain₁_conj (G : GenImg M) {s t : S.Region} {a b : Obj S} {L₁ : Layer S}
    (h : Chain a [L₁] b) (ha : Cond s t a) (hb : Cond s t b)
    {b₁ c₁ : FB S} {p₁ : fo (S := S) t ⟶ b₁} {q₁ : c₁ ⟶ fo (S := S) s} {x₁ y₁ : b₁ ⟶ c₁}
    (γ₁ : M.lift.map x₁ ⟶ M.lift.map y₁)
    (N0 : fw s a.word t ha.1 ha.2.1 ⟶ p₁ ≫ (x₁ ≫ q₁))
    (N1 : p₁ ≫ (y₁ ≫ q₁) ⟶ fw s b.word t hb.1 hb.2.1)
    (hn1 : fo (S := S) (S.right L₁.gen) = b₁) (hm1 : fo (S := S) (S.left L₁.gen) = c₁)
    (hr1 : ∀ h e, fw (S.right L₁.gen) L₁.right t h e ≍ p₁)
    (hl1 : ∀ h e, fw s L₁.left (S.left L₁.gen) h e ≍ q₁)
    (hd1 : ∀ h e, fw (S.left L₁.gen) (S.dom L₁.gen) (S.right L₁.gen) h e ≍ x₁)
    (he1 : ∀ h e, fw (S.left L₁.gen) (S.cod L₁.gen) (S.right L₁.gen) h e ≍ y₁)
    (hg1 : ∀ hd hde hc hce, G.gen L₁.gen (S.left L₁.gen) (S.right L₁.gen) rfl rfl hd hde hc hce ≍
      γ₁) :
    admissibleChain G a [L₁] b h ha hb =
      M.lift.map₂ N0 ≫ midK M p₁ q₁ γ₁ ≫ M.lift.map₂ N1 := by
  rw [admissibleChain_cons]
  simp only [admissibleChain]
  have hc : L₁.cod = b := h.2.2
  rw [eqToHom_lift M (fw_eq (congrArg Obj.word hc) _ _ _ _) _]
  simp only [coreC_eq]
  unfold core
  obtain ⟨A₁, B₁, e₁⟩ := layer_canon M hn1 hm1 (hr1 _ _) (hl1 _ _) (hd1 _ _) (he1 _ _) _ γ₁
    (hg1 _ _ _ _) _ _
  rw [e₁]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  rw [lift_map₂_eq M _ N0, lift_map₂_eq M (B₁ ≫ _) N1]

/-- **The image of two layers** with canonical pieces, read through free 2-morphisms. -/
theorem admissibleChain₂_conj (G : GenImg M) {s t : S.Region} {a b : Obj S} {L₁ L₂ : Layer S}
    (h : Chain a [L₁, L₂] b) (ha : Cond s t a) (hb : Cond s t b)
    {b₁ c₁ : FB S} {p₁ : fo (S := S) t ⟶ b₁} {q₁ : c₁ ⟶ fo (S := S) s} {x₁ y₁ : b₁ ⟶ c₁}
    {b₂ c₂ : FB S} {p₂ : fo (S := S) t ⟶ b₂} {q₂ : c₂ ⟶ fo (S := S) s} {x₂ y₂ : b₂ ⟶ c₂}
    (γ₁ : M.lift.map x₁ ⟶ M.lift.map y₁) (γ₂ : M.lift.map x₂ ⟶ M.lift.map y₂)
    (N0 : fw s a.word t ha.1 ha.2.1 ⟶ p₁ ≫ (x₁ ≫ q₁))
    (N1 : p₁ ≫ (y₁ ≫ q₁) ⟶ p₂ ≫ (x₂ ≫ q₂))
    (N2 : p₂ ≫ (y₂ ≫ q₂) ⟶ fw s b.word t hb.1 hb.2.1)
    (hn1 : fo (S := S) (S.right L₁.gen) = b₁) (hm1 : fo (S := S) (S.left L₁.gen) = c₁)
    (hr1 : ∀ h e, fw (S.right L₁.gen) L₁.right t h e ≍ p₁)
    (hl1 : ∀ h e, fw s L₁.left (S.left L₁.gen) h e ≍ q₁)
    (hd1 : ∀ h e, fw (S.left L₁.gen) (S.dom L₁.gen) (S.right L₁.gen) h e ≍ x₁)
    (he1 : ∀ h e, fw (S.left L₁.gen) (S.cod L₁.gen) (S.right L₁.gen) h e ≍ y₁)
    (hg1 : ∀ hd hde hc hce, G.gen L₁.gen (S.left L₁.gen) (S.right L₁.gen) rfl rfl hd hde hc hce ≍
      γ₁)
    (hn2 : fo (S := S) (S.right L₂.gen) = b₂) (hm2 : fo (S := S) (S.left L₂.gen) = c₂)
    (hr2 : ∀ h e, fw (S.right L₂.gen) L₂.right t h e ≍ p₂)
    (hl2 : ∀ h e, fw s L₂.left (S.left L₂.gen) h e ≍ q₂)
    (hd2 : ∀ h e, fw (S.left L₂.gen) (S.dom L₂.gen) (S.right L₂.gen) h e ≍ x₂)
    (he2 : ∀ h e, fw (S.left L₂.gen) (S.cod L₂.gen) (S.right L₂.gen) h e ≍ y₂)
    (hg2 : ∀ hd hde hc hce, G.gen L₂.gen (S.left L₂.gen) (S.right L₂.gen) rfl rfl hd hde hc hce ≍
      γ₂) :
    admissibleChain G a [L₁, L₂] b h ha hb =
      M.lift.map₂ N0 ≫ midK M p₁ q₁ γ₁ ≫ M.lift.map₂ N1 ≫ midK M p₂ q₂ γ₂ ≫
        M.lift.map₂ N2 := by
  rw [admissibleChain_pair]
  simp only [coreC_eq]
  unfold core
  obtain ⟨A₁, B₁, e₁⟩ := layer_canon M hn1 hm1 (hr1 _ _) (hl1 _ _) (hd1 _ _) (he1 _ _) _ γ₁
    (hg1 _ _ _ _) _ _
  obtain ⟨A₂, B₂, e₂⟩ := layer_canon M hn2 hm2 (hr2 _ _) (hl2 _ _) (hd2 _ _) (he2 _ _) _ γ₂
    (hg2 _ _ _ _) _ _
  rw [e₁, e₂]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  rw [lift_map₂_eq M _ N0, lift_map₂_eq M (B₁ ≫ _) N1, lift_map₂_eq M (B₂ ≫ _) N2]

/-- **The image of three layers** with canonical pieces, read through free 2-morphisms. -/
theorem admissibleChain₃_conj (G : GenImg M) {s t : S.Region} {a b : Obj S}
    {L₁ L₂ L₃ : Layer S}
    (h : Chain a [L₁, L₂, L₃] b) (ha : Cond s t a) (hb : Cond s t b)
    {b₁ c₁ : FB S} {p₁ : fo (S := S) t ⟶ b₁} {q₁ : c₁ ⟶ fo (S := S) s} {x₁ y₁ : b₁ ⟶ c₁}
    {b₂ c₂ : FB S} {p₂ : fo (S := S) t ⟶ b₂} {q₂ : c₂ ⟶ fo (S := S) s} {x₂ y₂ : b₂ ⟶ c₂}
    {b₃ c₃ : FB S} {p₃ : fo (S := S) t ⟶ b₃} {q₃ : c₃ ⟶ fo (S := S) s} {x₃ y₃ : b₃ ⟶ c₃}
    (γ₁ : M.lift.map x₁ ⟶ M.lift.map y₁) (γ₂ : M.lift.map x₂ ⟶ M.lift.map y₂)
    (γ₃ : M.lift.map x₃ ⟶ M.lift.map y₃)
    (N0 : fw s a.word t ha.1 ha.2.1 ⟶ p₁ ≫ (x₁ ≫ q₁))
    (N1 : p₁ ≫ (y₁ ≫ q₁) ⟶ p₂ ≫ (x₂ ≫ q₂))
    (N2 : p₂ ≫ (y₂ ≫ q₂) ⟶ p₃ ≫ (x₃ ≫ q₃))
    (N3 : p₃ ≫ (y₃ ≫ q₃) ⟶ fw s b.word t hb.1 hb.2.1)
    (hn1 : fo (S := S) (S.right L₁.gen) = b₁) (hm1 : fo (S := S) (S.left L₁.gen) = c₁)
    (hr1 : ∀ h e, fw (S.right L₁.gen) L₁.right t h e ≍ p₁)
    (hl1 : ∀ h e, fw s L₁.left (S.left L₁.gen) h e ≍ q₁)
    (hd1 : ∀ h e, fw (S.left L₁.gen) (S.dom L₁.gen) (S.right L₁.gen) h e ≍ x₁)
    (he1 : ∀ h e, fw (S.left L₁.gen) (S.cod L₁.gen) (S.right L₁.gen) h e ≍ y₁)
    (hg1 : ∀ hd hde hc hce, G.gen L₁.gen (S.left L₁.gen) (S.right L₁.gen) rfl rfl hd hde hc hce ≍
      γ₁)
    (hn2 : fo (S := S) (S.right L₂.gen) = b₂) (hm2 : fo (S := S) (S.left L₂.gen) = c₂)
    (hr2 : ∀ h e, fw (S.right L₂.gen) L₂.right t h e ≍ p₂)
    (hl2 : ∀ h e, fw s L₂.left (S.left L₂.gen) h e ≍ q₂)
    (hd2 : ∀ h e, fw (S.left L₂.gen) (S.dom L₂.gen) (S.right L₂.gen) h e ≍ x₂)
    (he2 : ∀ h e, fw (S.left L₂.gen) (S.cod L₂.gen) (S.right L₂.gen) h e ≍ y₂)
    (hg2 : ∀ hd hde hc hce, G.gen L₂.gen (S.left L₂.gen) (S.right L₂.gen) rfl rfl hd hde hc hce ≍
      γ₂)
    (hn3 : fo (S := S) (S.right L₃.gen) = b₃) (hm3 : fo (S := S) (S.left L₃.gen) = c₃)
    (hr3 : ∀ h e, fw (S.right L₃.gen) L₃.right t h e ≍ p₃)
    (hl3 : ∀ h e, fw s L₃.left (S.left L₃.gen) h e ≍ q₃)
    (hd3 : ∀ h e, fw (S.left L₃.gen) (S.dom L₃.gen) (S.right L₃.gen) h e ≍ x₃)
    (he3 : ∀ h e, fw (S.left L₃.gen) (S.cod L₃.gen) (S.right L₃.gen) h e ≍ y₃)
    (hg3 : ∀ hd hde hc hce, G.gen L₃.gen (S.left L₃.gen) (S.right L₃.gen) rfl rfl hd hde hc hce ≍
      γ₃) :
    admissibleChain G a [L₁, L₂, L₃] b h ha hb =
      M.lift.map₂ N0 ≫ midK M p₁ q₁ γ₁ ≫ M.lift.map₂ N1 ≫ midK M p₂ q₂ γ₂ ≫
        M.lift.map₂ N2 ≫ midK M p₃ q₃ γ₃ ≫ M.lift.map₂ N3 := by
  rw [admissibleChain_cons, admissibleChain_pair]
  simp only [coreC_eq]
  unfold core
  obtain ⟨A₁, B₁, e₁⟩ := layer_canon M hn1 hm1 (hr1 _ _) (hl1 _ _) (hd1 _ _) (he1 _ _) _ γ₁
    (hg1 _ _ _ _) _ _
  obtain ⟨A₂, B₂, e₂⟩ := layer_canon M hn2 hm2 (hr2 _ _) (hl2 _ _) (hd2 _ _) (he2 _ _) _ γ₂
    (hg2 _ _ _ _) _ _
  obtain ⟨A₃, B₃, e₃⟩ := layer_canon M hn3 hm3 (hr3 _ _) (hl3 _ _) (hd3 _ _) (he3 _ _) _ γ₃
    (hg3 _ _ _ _) _ _
  rw [e₁, e₂, e₃]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  rw [lift_map₂_eq M _ N0, lift_map₂_eq M (B₁ ≫ _) N1, lift_map₂_eq M (B₂ ≫ _) N2,
    lift_map₂_eq M (B₃ ≫ _) N3]

end Categorification.Diagrams.BicatInterp
