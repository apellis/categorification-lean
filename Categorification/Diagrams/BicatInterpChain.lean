/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpMate

/-!
# Chains of layer images in canonical form

The image of a chain of layers under the interpretation of diagrams by generator images is a
composite of whiskered generator images `midK M p q g`, joined by images of free 2-morphisms.
The pieces `p`, `q` of a layer and the boundary words of its generator are only equal to
canonical ones up to equality of regions (`layer_canon`). Once they are canonical, two chains of
two or of three layers have the same image as soon as the corresponding composites in the target
bicategory agree, read through free isomorphisms with a common source and target of one's
choice (`chain₂_eq`, `chain₃_eq`). Since the free bicategory on a quiver is thin, the joining
free 2-morphisms do not matter.
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

variable {S : Signature} {C : Type*} [Bicategory C] (M : Model S C)

/-- **A layer image with canonical pieces.** If the pieces of a layer are equal to canonical ones
after an equality of their regions, and its generator image is heterogeneously equal to a
canonical 2-morphism, the layer image between images of free 2-morphisms can be written with the
canonical pieces. -/
theorem layer_canon {a₀ a₁ b c n m : FB S} {p' : a₀ ⟶ b} {q' : c ⟶ a₁} {x y : b ⟶ c}
    {p : a₀ ⟶ n} {q : m ⟶ a₁} {d e : n ⟶ m} (hn : n = b) (hm : m = c)
    (hp : p ≍ p') (hq : q ≍ q') (hd : d ≍ x) (he : e ≍ y)
    (g : M.lift.map d ⟶ M.lift.map e) (γ : M.lift.map x ⟶ M.lift.map y) (hg : g ≍ γ)
    {P Q : a₀ ⟶ a₁} (A : P ⟶ p ≫ (d ≫ q)) (B : p ≫ (e ≫ q) ⟶ Q) :
    ∃ (A' : P ⟶ p' ≫ (x ≫ q')) (B' : p' ≫ (y ≫ q') ⟶ Q),
      M.lift.map₂ A ≫ midK M p q g ≫ M.lift.map₂ B =
        M.lift.map₂ A' ≫ midK M p' q' γ ≫ M.lift.map₂ B' := by
  subst hn hm
  obtain rfl := eq_of_heq hp; obtain rfl := eq_of_heq hq; obtain rfl := eq_of_heq hd
  obtain rfl := eq_of_heq he; obtain rfl := eq_of_heq hg
  exact ⟨A, B, rfl⟩

/-- **The image of a chain of layers with a first layer** `L`: the transport to the boundary word
of `L`, the image of `L`, and the image of the remaining chain. -/
theorem admissibleChain_cons (G : GenImg M) {s t : S.Region} {a b : Obj S} (L : Layer S)
    (ls : List (Layer S)) (h : Chain a (L :: ls) b) (ha : Cond s t a) (hb : Cond s t b) :
    admissibleChain G a (L :: ls) b h ha hb =
      M.lift.map₂ (eqToHom (fw_eq (congrArg Obj.word h.2.1.symm) ha.1 ha.2.1
          (h.2.1 ▸ ha).1 (h.2.1 ▸ ha).2.1)) ≫
        coreC G h.1 (h.2.1 ▸ ha) ≫ admissibleChain G L.cod ls b h.2.2 ((h.2.1 ▸ ha).cod h.1) hb := by
  rw [admissibleChain, eqToHom_lift _ _]

variable {a₀ a₁ : FB S}

/-- Replacing the image of a free 2-morphism into the source of a free isomorphism. -/
theorem map₂_through_iso {P W R : a₀ ⟶ a₁} (E : P ⟶ R) (N : W ≅ R) :
    M.lift.map₂ E = M.lift.map₂ (E ≫ N.inv) ≫ M.lift.map₂ N.hom := by
  rw [← PrelaxFunctor.map₂_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Replacing the image of a free 2-morphism out of the target of a free isomorphism. -/
theorem map₂_through_iso' {R W Q : a₀ ⟶ a₁} (E : R ⟶ Q) (N : R ≅ W) :
    M.lift.map₂ E = M.lift.map₂ N.hom ≫ M.lift.map₂ (N.inv ≫ E) := by
  rw [← PrelaxFunctor.map₂_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

section Two

variable {b₁ c₁ b₂ c₂ b₃ c₃ b₄ c₄ : FB S}
  {p₁ : a₀ ⟶ b₁} {q₁ : c₁ ⟶ a₁} {x₁ y₁ : b₁ ⟶ c₁}
  {p₂ : a₀ ⟶ b₂} {q₂ : c₂ ⟶ a₁} {x₂ y₂ : b₂ ⟶ c₂}
  {p₃ : a₀ ⟶ b₃} {q₃ : c₃ ⟶ a₁} {x₃ y₃ : b₃ ⟶ c₃}
  {p₄ : a₀ ⟶ b₄} {q₄ : c₄ ⟶ a₁} {x₄ y₄ : b₄ ⟶ c₄}

/-- **Two chains of two canonical layers** have the same image if the composites agree after
free isomorphisms from a common source `W` and to a common target `W'`. -/
theorem chain₂_eq (γ₁ : M.lift.map x₁ ⟶ M.lift.map y₁) (γ₂ : M.lift.map x₂ ⟶ M.lift.map y₂)
    (γ₃ : M.lift.map x₃ ⟶ M.lift.map y₃) (γ₄ : M.lift.map x₄ ⟶ M.lift.map y₄)
    {W W' : a₀ ⟶ a₁}
    (N₀ : W ≅ p₁ ≫ (x₁ ≫ q₁)) (N₁ : p₁ ≫ (y₁ ≫ q₁) ⟶ p₂ ≫ (x₂ ≫ q₂))
    (N₂ : p₂ ≫ (y₂ ≫ q₂) ≅ W')
    (N₀' : W ≅ p₃ ≫ (x₃ ≫ q₃)) (N₁' : p₃ ≫ (y₃ ≫ q₃) ⟶ p₄ ≫ (x₄ ≫ q₄))
    (N₂' : p₄ ≫ (y₄ ≫ q₄) ≅ W')
    (h : M.lift.map₂ N₀.hom ≫ midK M p₁ q₁ γ₁ ≫ M.lift.map₂ N₁ ≫ midK M p₂ q₂ γ₂ ≫
        M.lift.map₂ N₂.hom =
      M.lift.map₂ N₀'.hom ≫ midK M p₃ q₃ γ₃ ≫ M.lift.map₂ N₁' ≫ midK M p₄ q₄ γ₄ ≫
        M.lift.map₂ N₂'.hom)
    {P Q : a₀ ⟶ a₁}
    (E₀ : P ⟶ p₁ ≫ (x₁ ≫ q₁)) (E₁ : p₁ ≫ (y₁ ≫ q₁) ⟶ p₂ ≫ (x₂ ≫ q₂))
    (E₂ : p₂ ≫ (y₂ ≫ q₂) ⟶ Q)
    (F₀ : P ⟶ p₃ ≫ (x₃ ≫ q₃)) (F₁ : p₃ ≫ (y₃ ≫ q₃) ⟶ p₄ ≫ (x₄ ≫ q₄))
    (F₂ : p₄ ≫ (y₄ ≫ q₄) ⟶ Q) :
    M.lift.map₂ E₀ ≫ midK M p₁ q₁ γ₁ ≫ M.lift.map₂ E₁ ≫ midK M p₂ q₂ γ₂ ≫ M.lift.map₂ E₂ =
      M.lift.map₂ F₀ ≫ midK M p₃ q₃ γ₃ ≫ M.lift.map₂ F₁ ≫ midK M p₄ q₄ γ₄ ≫
        M.lift.map₂ F₂ := by
  rw [map₂_through_iso M E₀ N₀, map₂_through_iso M F₀ N₀', map₂_through_iso' M E₂ N₂,
    map₂_through_iso' M F₂ N₂', lift_map₂_eq M E₁ N₁, lift_map₂_eq M F₁ N₁',
    lift_map₂_eq M (E₀ ≫ N₀.inv) (F₀ ≫ N₀'.inv), lift_map₂_eq M (N₂.inv ≫ E₂) (N₂'.inv ≫ F₂)]
  simp only [Category.assoc]
  rw [reassoc_of% h]

/-- `chain₂_eq` for layers whose pieces agree with canonical ones up to equality of regions and
heterogeneous equality, in the form produced by unfolding the image of a chain of layers. -/
theorem chain₂_heq (γ₁ : M.lift.map x₁ ⟶ M.lift.map y₁) (γ₂ : M.lift.map x₂ ⟶ M.lift.map y₂) (γ₃ : M.lift.map x₃ ⟶ M.lift.map y₃) (γ₄ : M.lift.map x₄ ⟶ M.lift.map y₄)
    {W W' : a₀ ⟶ a₁} (N0 : W ≅ p₁ ≫ (x₁ ≫ q₁)) (N1 : p₁ ≫ (y₁ ≫ q₁) ⟶ p₂ ≫ (x₂ ≫ q₂)) (N2 : p₂ ≫ (y₂ ≫ q₂) ≅ W') (N'0 : W ≅ p₃ ≫ (x₃ ≫ q₃)) (N'1 : p₃ ≫ (y₃ ≫ q₃) ⟶ p₄ ≫ (x₄ ≫ q₄)) (N'2 : p₄ ≫ (y₄ ≫ q₄) ≅ W')
    (h : M.lift.map₂ N0.hom ≫ midK M p₁ q₁ γ₁ ≫ M.lift.map₂ N1 ≫ midK M p₂ q₂ γ₂ ≫ M.lift.map₂ N2.hom =
      M.lift.map₂ N'0.hom ≫ midK M p₃ q₃ γ₃ ≫ M.lift.map₂ N'1 ≫ midK M p₄ q₄ γ₄ ≫ M.lift.map₂ N'2.hom)
    {n1 m1 : FB S} {P1_ Q1_ : a₀ ⟶ a₁} {r1 : a₀ ⟶ n1} {l1 : m1 ⟶ a₁} {d1 e1 : n1 ⟶ m1} {n2 m2 : FB S} {P2_ Q2_ : a₀ ⟶ a₁} {r2 : a₀ ⟶ n2} {l2 : m2 ⟶ a₁} {d2 e2 : n2 ⟶ m2} {n3 m3 : FB S} {P3_ Q3_ : a₀ ⟶ a₁} {r3 : a₀ ⟶ n3} {l3 : m3 ⟶ a₁} {d3 e3 : n3 ⟶ m3} {n4 m4 : FB S} {P4_ Q4_ : a₀ ⟶ a₁} {r4 : a₀ ⟶ n4} {l4 : m4 ⟶ a₁} {d4 e4 : n4 ⟶ m4} (hn1 : n1 = b₁) (hm1 : m1 = c₁) (hr1 : r1 ≍ p₁) (hl1 : l1 ≍ q₁) (hd1 : d1 ≍ x₁) (he1 : e1 ≍ y₁) (g1 : M.lift.map d1 ⟶ M.lift.map e1) (hg1 : g1 ≍ γ₁) (A1 : P1_ ⟶ r1 ≫ (d1 ≫ l1)) (B1 : r1 ≫ (e1 ≫ l1) ⟶ Q1_)
    (hn2 : n2 = b₂) (hm2 : m2 = c₂) (hr2 : r2 ≍ p₂) (hl2 : l2 ≍ q₂) (hd2 : d2 ≍ x₂) (he2 : e2 ≍ y₂) (g2 : M.lift.map d2 ⟶ M.lift.map e2) (hg2 : g2 ≍ γ₂) (A2 : P2_ ⟶ r2 ≫ (d2 ≫ l2)) (B2 : r2 ≫ (e2 ≫ l2) ⟶ Q2_)
    (hn3 : n3 = b₃) (hm3 : m3 = c₃) (hr3 : r3 ≍ p₃) (hl3 : l3 ≍ q₃) (hd3 : d3 ≍ x₃) (he3 : e3 ≍ y₃) (g3 : M.lift.map d3 ⟶ M.lift.map e3) (hg3 : g3 ≍ γ₃) (A3 : P3_ ⟶ r3 ≫ (d3 ≫ l3)) (B3 : r3 ≫ (e3 ≫ l3) ⟶ Q3_)
    (hn4 : n4 = b₄) (hm4 : m4 = c₄) (hr4 : r4 ≍ p₄) (hl4 : l4 ≍ q₄) (hd4 : d4 ≍ x₄) (he4 : e4 ≍ y₄) (g4 : M.lift.map d4 ⟶ M.lift.map e4) (hg4 : g4 ≍ γ₄) (A4 : P4_ ⟶ r4 ≫ (d4 ≫ l4)) (B4 : r4 ≫ (e4 ≫ l4) ⟶ Q4_)
    {P Q : a₀ ⟶ a₁} (E0 : P ⟶ P1_) (E1 : Q1_ ⟶ P2_) (E2 : Q2_ ⟶ Q) (F0 : P ⟶ P3_) (F1 : Q3_ ⟶ P4_) (F2 : Q4_ ⟶ Q) :
    M.lift.map₂ E0 ≫ (M.lift.map₂ A1 ≫ midK M r1 l1 g1 ≫ M.lift.map₂ B1) ≫ M.lift.map₂ E1 ≫ (M.lift.map₂ A2 ≫ midK M r2 l2 g2 ≫ M.lift.map₂ B2) ≫ M.lift.map₂ E2 =
      M.lift.map₂ F0 ≫ (M.lift.map₂ A3 ≫ midK M r3 l3 g3 ≫ M.lift.map₂ B3) ≫ M.lift.map₂ F1 ≫ (M.lift.map₂ A4 ≫ midK M r4 l4 g4 ≫ M.lift.map₂ B4) ≫ M.lift.map₂ F2 := by
  obtain ⟨A1', B1', e1'⟩ := layer_canon M hn1 hm1 hr1 hl1 hd1 he1 g1 γ₁ hg1 A1 B1
  obtain ⟨A2', B2', e2'⟩ := layer_canon M hn2 hm2 hr2 hl2 hd2 he2 g2 γ₂ hg2 A2 B2
  obtain ⟨A3', B3', e3'⟩ := layer_canon M hn3 hm3 hr3 hl3 hd3 he3 g3 γ₃ hg3 A3 B3
  obtain ⟨A4', B4', e4'⟩ := layer_canon M hn4 hm4 hr4 hl4 hd4 he4 g4 γ₄ hg4 A4 B4
  rw [e1', e2', e3', e4']
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact chain₂_eq M γ₁ γ₂ γ₃ γ₄ _  _  _  _  _  _  h _  _  _  _  _  _ 

end Two

section Three

variable {b₁ c₁ b₂ c₂ b₃ c₃ b₄ c₄ b₅ c₅ b₆ c₆ : FB S}
  {p₁ : a₀ ⟶ b₁} {q₁ : c₁ ⟶ a₁} {x₁ y₁ : b₁ ⟶ c₁}
  {p₂ : a₀ ⟶ b₂} {q₂ : c₂ ⟶ a₁} {x₂ y₂ : b₂ ⟶ c₂}
  {p₃ : a₀ ⟶ b₃} {q₃ : c₃ ⟶ a₁} {x₃ y₃ : b₃ ⟶ c₃}
  {p₄ : a₀ ⟶ b₄} {q₄ : c₄ ⟶ a₁} {x₄ y₄ : b₄ ⟶ c₄}
  {p₅ : a₀ ⟶ b₅} {q₅ : c₅ ⟶ a₁} {x₅ y₅ : b₅ ⟶ c₅}
  {p₆ : a₀ ⟶ b₆} {q₆ : c₆ ⟶ a₁} {x₆ y₆ : b₆ ⟶ c₆}

/-- **Two chains of three canonical layers** have the same image if the composites agree after
free isomorphisms from a common source `W` and to a common target `W'`. -/
theorem chain₃_eq (γ₁ : M.lift.map x₁ ⟶ M.lift.map y₁) (γ₂ : M.lift.map x₂ ⟶ M.lift.map y₂)
    (γ₃ : M.lift.map x₃ ⟶ M.lift.map y₃) (γ₄ : M.lift.map x₄ ⟶ M.lift.map y₄)
    (γ₅ : M.lift.map x₅ ⟶ M.lift.map y₅) (γ₆ : M.lift.map x₆ ⟶ M.lift.map y₆)
    {W W' : a₀ ⟶ a₁}
    (N₀ : W ≅ p₁ ≫ (x₁ ≫ q₁)) (N₁ : p₁ ≫ (y₁ ≫ q₁) ⟶ p₂ ≫ (x₂ ≫ q₂))
    (N₂ : p₂ ≫ (y₂ ≫ q₂) ⟶ p₃ ≫ (x₃ ≫ q₃)) (N₃ : p₃ ≫ (y₃ ≫ q₃) ≅ W')
    (N₀' : W ≅ p₄ ≫ (x₄ ≫ q₄)) (N₁' : p₄ ≫ (y₄ ≫ q₄) ⟶ p₅ ≫ (x₅ ≫ q₅))
    (N₂' : p₅ ≫ (y₅ ≫ q₅) ⟶ p₆ ≫ (x₆ ≫ q₆)) (N₃' : p₆ ≫ (y₆ ≫ q₆) ≅ W')
    (h : M.lift.map₂ N₀.hom ≫ midK M p₁ q₁ γ₁ ≫ M.lift.map₂ N₁ ≫ midK M p₂ q₂ γ₂ ≫
        M.lift.map₂ N₂ ≫ midK M p₃ q₃ γ₃ ≫ M.lift.map₂ N₃.hom =
      M.lift.map₂ N₀'.hom ≫ midK M p₄ q₄ γ₄ ≫ M.lift.map₂ N₁' ≫ midK M p₅ q₅ γ₅ ≫
        M.lift.map₂ N₂' ≫ midK M p₆ q₆ γ₆ ≫ M.lift.map₂ N₃'.hom)
    {P Q : a₀ ⟶ a₁}
    (E₀ : P ⟶ p₁ ≫ (x₁ ≫ q₁)) (E₁ : p₁ ≫ (y₁ ≫ q₁) ⟶ p₂ ≫ (x₂ ≫ q₂))
    (E₂ : p₂ ≫ (y₂ ≫ q₂) ⟶ p₃ ≫ (x₃ ≫ q₃)) (E₃ : p₃ ≫ (y₃ ≫ q₃) ⟶ Q)
    (F₀ : P ⟶ p₄ ≫ (x₄ ≫ q₄)) (F₁ : p₄ ≫ (y₄ ≫ q₄) ⟶ p₅ ≫ (x₅ ≫ q₅))
    (F₂ : p₅ ≫ (y₅ ≫ q₅) ⟶ p₆ ≫ (x₆ ≫ q₆)) (F₃ : p₆ ≫ (y₆ ≫ q₆) ⟶ Q) :
    M.lift.map₂ E₀ ≫ midK M p₁ q₁ γ₁ ≫ M.lift.map₂ E₁ ≫ midK M p₂ q₂ γ₂ ≫ M.lift.map₂ E₂ ≫
        midK M p₃ q₃ γ₃ ≫ M.lift.map₂ E₃ =
      M.lift.map₂ F₀ ≫ midK M p₄ q₄ γ₄ ≫ M.lift.map₂ F₁ ≫ midK M p₅ q₅ γ₅ ≫
        M.lift.map₂ F₂ ≫ midK M p₆ q₆ γ₆ ≫ M.lift.map₂ F₃ := by
  rw [map₂_through_iso M E₀ N₀, map₂_through_iso M F₀ N₀', map₂_through_iso' M E₃ N₃,
    map₂_through_iso' M F₃ N₃', lift_map₂_eq M E₁ N₁, lift_map₂_eq M F₁ N₁',
    lift_map₂_eq M E₂ N₂, lift_map₂_eq M F₂ N₂',
    lift_map₂_eq M (E₀ ≫ N₀.inv) (F₀ ≫ N₀'.inv), lift_map₂_eq M (N₃.inv ≫ E₃) (N₃'.inv ≫ F₃)]
  simp only [Category.assoc]
  rw [reassoc_of% h]

/-- `chain₃_eq` for layers whose pieces agree with canonical ones up to equality of regions and
heterogeneous equality, in the form produced by unfolding the image of a chain of layers. -/
theorem chain₃_heq (γ₁ : M.lift.map x₁ ⟶ M.lift.map y₁) (γ₂ : M.lift.map x₂ ⟶ M.lift.map y₂) (γ₃ : M.lift.map x₃ ⟶ M.lift.map y₃) (γ₄ : M.lift.map x₄ ⟶ M.lift.map y₄) (γ₅ : M.lift.map x₅ ⟶ M.lift.map y₅) (γ₆ : M.lift.map x₆ ⟶ M.lift.map y₆)
    {W W' : a₀ ⟶ a₁} (N0 : W ≅ p₁ ≫ (x₁ ≫ q₁)) (N1 : p₁ ≫ (y₁ ≫ q₁) ⟶ p₂ ≫ (x₂ ≫ q₂)) (N2 : p₂ ≫ (y₂ ≫ q₂) ⟶ p₃ ≫ (x₃ ≫ q₃)) (N3 : p₃ ≫ (y₃ ≫ q₃) ≅ W') (N'0 : W ≅ p₄ ≫ (x₄ ≫ q₄)) (N'1 : p₄ ≫ (y₄ ≫ q₄) ⟶ p₅ ≫ (x₅ ≫ q₅)) (N'2 : p₅ ≫ (y₅ ≫ q₅) ⟶ p₆ ≫ (x₆ ≫ q₆)) (N'3 : p₆ ≫ (y₆ ≫ q₆) ≅ W')
    (h : M.lift.map₂ N0.hom ≫ midK M p₁ q₁ γ₁ ≫ M.lift.map₂ N1 ≫ midK M p₂ q₂ γ₂ ≫ M.lift.map₂ N2 ≫ midK M p₃ q₃ γ₃ ≫ M.lift.map₂ N3.hom =
      M.lift.map₂ N'0.hom ≫ midK M p₄ q₄ γ₄ ≫ M.lift.map₂ N'1 ≫ midK M p₅ q₅ γ₅ ≫ M.lift.map₂ N'2 ≫ midK M p₆ q₆ γ₆ ≫ M.lift.map₂ N'3.hom)
    {n1 m1 : FB S} {P1_ Q1_ : a₀ ⟶ a₁} {r1 : a₀ ⟶ n1} {l1 : m1 ⟶ a₁} {d1 e1 : n1 ⟶ m1} {n2 m2 : FB S} {P2_ Q2_ : a₀ ⟶ a₁} {r2 : a₀ ⟶ n2} {l2 : m2 ⟶ a₁} {d2 e2 : n2 ⟶ m2} {n3 m3 : FB S} {P3_ Q3_ : a₀ ⟶ a₁} {r3 : a₀ ⟶ n3} {l3 : m3 ⟶ a₁} {d3 e3 : n3 ⟶ m3} {n4 m4 : FB S} {P4_ Q4_ : a₀ ⟶ a₁} {r4 : a₀ ⟶ n4} {l4 : m4 ⟶ a₁} {d4 e4 : n4 ⟶ m4} {n5 m5 : FB S} {P5_ Q5_ : a₀ ⟶ a₁} {r5 : a₀ ⟶ n5} {l5 : m5 ⟶ a₁} {d5 e5 : n5 ⟶ m5} {n6 m6 : FB S} {P6_ Q6_ : a₀ ⟶ a₁} {r6 : a₀ ⟶ n6} {l6 : m6 ⟶ a₁} {d6 e6 : n6 ⟶ m6} (hn1 : n1 = b₁) (hm1 : m1 = c₁) (hr1 : r1 ≍ p₁) (hl1 : l1 ≍ q₁) (hd1 : d1 ≍ x₁) (he1 : e1 ≍ y₁) (g1 : M.lift.map d1 ⟶ M.lift.map e1) (hg1 : g1 ≍ γ₁) (A1 : P1_ ⟶ r1 ≫ (d1 ≫ l1)) (B1 : r1 ≫ (e1 ≫ l1) ⟶ Q1_)
    (hn2 : n2 = b₂) (hm2 : m2 = c₂) (hr2 : r2 ≍ p₂) (hl2 : l2 ≍ q₂) (hd2 : d2 ≍ x₂) (he2 : e2 ≍ y₂) (g2 : M.lift.map d2 ⟶ M.lift.map e2) (hg2 : g2 ≍ γ₂) (A2 : P2_ ⟶ r2 ≫ (d2 ≫ l2)) (B2 : r2 ≫ (e2 ≫ l2) ⟶ Q2_)
    (hn3 : n3 = b₃) (hm3 : m3 = c₃) (hr3 : r3 ≍ p₃) (hl3 : l3 ≍ q₃) (hd3 : d3 ≍ x₃) (he3 : e3 ≍ y₃) (g3 : M.lift.map d3 ⟶ M.lift.map e3) (hg3 : g3 ≍ γ₃) (A3 : P3_ ⟶ r3 ≫ (d3 ≫ l3)) (B3 : r3 ≫ (e3 ≫ l3) ⟶ Q3_)
    (hn4 : n4 = b₄) (hm4 : m4 = c₄) (hr4 : r4 ≍ p₄) (hl4 : l4 ≍ q₄) (hd4 : d4 ≍ x₄) (he4 : e4 ≍ y₄) (g4 : M.lift.map d4 ⟶ M.lift.map e4) (hg4 : g4 ≍ γ₄) (A4 : P4_ ⟶ r4 ≫ (d4 ≫ l4)) (B4 : r4 ≫ (e4 ≫ l4) ⟶ Q4_)
    (hn5 : n5 = b₅) (hm5 : m5 = c₅) (hr5 : r5 ≍ p₅) (hl5 : l5 ≍ q₅) (hd5 : d5 ≍ x₅) (he5 : e5 ≍ y₅) (g5 : M.lift.map d5 ⟶ M.lift.map e5) (hg5 : g5 ≍ γ₅) (A5 : P5_ ⟶ r5 ≫ (d5 ≫ l5)) (B5 : r5 ≫ (e5 ≫ l5) ⟶ Q5_)
    (hn6 : n6 = b₆) (hm6 : m6 = c₆) (hr6 : r6 ≍ p₆) (hl6 : l6 ≍ q₆) (hd6 : d6 ≍ x₆) (he6 : e6 ≍ y₆) (g6 : M.lift.map d6 ⟶ M.lift.map e6) (hg6 : g6 ≍ γ₆) (A6 : P6_ ⟶ r6 ≫ (d6 ≫ l6)) (B6 : r6 ≫ (e6 ≫ l6) ⟶ Q6_)
    {P Q : a₀ ⟶ a₁} (E0 : P ⟶ P1_) (E1 : Q1_ ⟶ P2_) (E2 : Q2_ ⟶ P3_) (E3 : Q3_ ⟶ Q) (F0 : P ⟶ P4_) (F1 : Q4_ ⟶ P5_) (F2 : Q5_ ⟶ P6_) (F3 : Q6_ ⟶ Q) :
    M.lift.map₂ E0 ≫ (M.lift.map₂ A1 ≫ midK M r1 l1 g1 ≫ M.lift.map₂ B1) ≫ M.lift.map₂ E1 ≫ (M.lift.map₂ A2 ≫ midK M r2 l2 g2 ≫ M.lift.map₂ B2) ≫ M.lift.map₂ E2 ≫ (M.lift.map₂ A3 ≫ midK M r3 l3 g3 ≫ M.lift.map₂ B3) ≫ M.lift.map₂ E3 =
      M.lift.map₂ F0 ≫ (M.lift.map₂ A4 ≫ midK M r4 l4 g4 ≫ M.lift.map₂ B4) ≫ M.lift.map₂ F1 ≫ (M.lift.map₂ A5 ≫ midK M r5 l5 g5 ≫ M.lift.map₂ B5) ≫ M.lift.map₂ F2 ≫ (M.lift.map₂ A6 ≫ midK M r6 l6 g6 ≫ M.lift.map₂ B6) ≫ M.lift.map₂ F3 := by
  obtain ⟨A1', B1', e1'⟩ := layer_canon M hn1 hm1 hr1 hl1 hd1 he1 g1 γ₁ hg1 A1 B1
  obtain ⟨A2', B2', e2'⟩ := layer_canon M hn2 hm2 hr2 hl2 hd2 he2 g2 γ₂ hg2 A2 B2
  obtain ⟨A3', B3', e3'⟩ := layer_canon M hn3 hm3 hr3 hl3 hd3 he3 g3 γ₃ hg3 A3 B3
  obtain ⟨A4', B4', e4'⟩ := layer_canon M hn4 hm4 hr4 hl4 hd4 he4 g4 γ₄ hg4 A4 B4
  obtain ⟨A5', B5', e5'⟩ := layer_canon M hn5 hm5 hr5 hl5 hd5 he5 g5 γ₅ hg5 A5 B5
  obtain ⟨A6', B6', e6'⟩ := layer_canon M hn6 hm6 hr6 hl6 hd6 he6 g6 γ₆ hg6 A6 B6
  rw [e1', e2', e3', e4', e5', e6']
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact chain₃_eq M γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ _  _  _  _  _  _  _  _  h _  _  _  _  _  _  _  _ 

end Three

/-- **Two chains of 2 layers** with pieces equal to canonical ones up to equality of regions and
heterogeneous equality have the same image as soon as the canonical composites agree after free
isomorphisms from a common source `W` and to a common target `W'`. -/
theorem admissibleChain₂_heq (G : GenImg M) {s t : S.Region} {a b : Obj S}
    {L₁ L₂ L₃ L₄ : Layer S}
    (h : Chain a [L₁, L₂] b) (h' : Chain a [L₃, L₄] b) (ha : Cond s t a) (hb : Cond s t b)
    (ht : fo (S := S) t = a₀) (hs : fo (S := S) s = a₁)
    {b₁ c₁ : FB S} {p₁ : a₀ ⟶ b₁} {q₁ : c₁ ⟶ a₁} {x₁ y₁ : b₁ ⟶ c₁} {b₂ c₂ : FB S} {p₂ : a₀ ⟶ b₂} {q₂ : c₂ ⟶ a₁} {x₂ y₂ : b₂ ⟶ c₂} {b₃ c₃ : FB S} {p₃ : a₀ ⟶ b₃} {q₃ : c₃ ⟶ a₁} {x₃ y₃ : b₃ ⟶ c₃} {b₄ c₄ : FB S} {p₄ : a₀ ⟶ b₄} {q₄ : c₄ ⟶ a₁} {x₄ y₄ : b₄ ⟶ c₄}
    (γ₁ : M.lift.map x₁ ⟶ M.lift.map y₁) (γ₂ : M.lift.map x₂ ⟶ M.lift.map y₂) (γ₃ : M.lift.map x₃ ⟶ M.lift.map y₃) (γ₄ : M.lift.map x₄ ⟶ M.lift.map y₄)
    {W W' : a₀ ⟶ a₁}
    (N0 : W ≅ p₁ ≫ (x₁ ≫ q₁))
    (N1 : p₁ ≫ (y₁ ≫ q₁) ⟶ p₂ ≫ (x₂ ≫ q₂))
    (N2 : p₂ ≫ (y₂ ≫ q₂) ≅ W')
    (N'0 : W ≅ p₃ ≫ (x₃ ≫ q₃))
    (N'1 : p₃ ≫ (y₃ ≫ q₃) ⟶ p₄ ≫ (x₄ ≫ q₄))
    (N'2 : p₄ ≫ (y₄ ≫ q₄) ≅ W')
    (hmain : M.lift.map₂ N0.hom ≫
        midK M p₁ q₁ γ₁ ≫
        M.lift.map₂ N1 ≫
        midK M p₂ q₂ γ₂ ≫
        M.lift.map₂ N2.hom =
      M.lift.map₂ N'0.hom ≫
        midK M p₃ q₃ γ₃ ≫
        M.lift.map₂ N'1 ≫
        midK M p₄ q₄ γ₄ ≫
        M.lift.map₂ N'2.hom)
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
      γ₃)
    (hn4 : fo (S := S) (S.right L₄.gen) = b₄) (hm4 : fo (S := S) (S.left L₄.gen) = c₄)
    (hr4 : ∀ h e, fw (S.right L₄.gen) L₄.right t h e ≍ p₄)
    (hl4 : ∀ h e, fw s L₄.left (S.left L₄.gen) h e ≍ q₄)
    (hd4 : ∀ h e, fw (S.left L₄.gen) (S.dom L₄.gen) (S.right L₄.gen) h e ≍ x₄)
    (he4 : ∀ h e, fw (S.left L₄.gen) (S.cod L₄.gen) (S.right L₄.gen) h e ≍ y₄)
    (hg4 : ∀ hd hde hc hce, G.gen L₄.gen (S.left L₄.gen) (S.right L₄.gen) rfl rfl hd hde hc hce ≍
      γ₄) :
    admissibleChain G a [L₁, L₂] b h ha hb = admissibleChain G a [L₃, L₄] b h' ha hb := by
  subst ht hs
  rw [admissibleChain_pair, admissibleChain_pair]
  simp only [coreC_eq]
  unfold core
  exact chain₂_heq M γ₁ γ₂ γ₃ γ₄ N0 N1 N2 N'0 N'1 N'2 hmain (hn1) (hm1) (hr1 _ _) (hl1 _ _) (hd1 _ _) (he1 _ _) _ (hg1 _ _ _ _) _ _ (hn2) (hm2) (hr2 _ _) (hl2 _ _) (hd2 _ _) (he2 _ _) _ (hg2 _ _ _ _) _ _ (hn3) (hm3) (hr3 _ _) (hl3 _ _) (hd3 _ _) (he3 _ _) _ (hg3 _ _ _ _) _ _ (hn4) (hm4) (hr4 _ _) (hl4 _ _) (hd4 _ _) (he4 _ _) _ (hg4 _ _ _ _) _ _ _ _ _ _ _ _

/-- **Two chains of 3 layers** with pieces equal to canonical ones up to equality of regions and
heterogeneous equality have the same image as soon as the canonical composites agree after free
isomorphisms from a common source `W` and to a common target `W'`. -/
theorem admissibleChain₃_heq (G : GenImg M) {s t : S.Region} {a b : Obj S}
    {L₁ L₂ L₃ L₄ L₅ L₆ : Layer S}
    (h : Chain a [L₁, L₂, L₃] b) (h' : Chain a [L₄, L₅, L₆] b) (ha : Cond s t a) (hb : Cond s t b)
    (ht : fo (S := S) t = a₀) (hs : fo (S := S) s = a₁)
    {b₁ c₁ : FB S} {p₁ : a₀ ⟶ b₁} {q₁ : c₁ ⟶ a₁} {x₁ y₁ : b₁ ⟶ c₁} {b₂ c₂ : FB S} {p₂ : a₀ ⟶ b₂} {q₂ : c₂ ⟶ a₁} {x₂ y₂ : b₂ ⟶ c₂} {b₃ c₃ : FB S} {p₃ : a₀ ⟶ b₃} {q₃ : c₃ ⟶ a₁} {x₃ y₃ : b₃ ⟶ c₃} {b₄ c₄ : FB S} {p₄ : a₀ ⟶ b₄} {q₄ : c₄ ⟶ a₁} {x₄ y₄ : b₄ ⟶ c₄} {b₅ c₅ : FB S} {p₅ : a₀ ⟶ b₅} {q₅ : c₅ ⟶ a₁} {x₅ y₅ : b₅ ⟶ c₅} {b₆ c₆ : FB S} {p₆ : a₀ ⟶ b₆} {q₆ : c₆ ⟶ a₁} {x₆ y₆ : b₆ ⟶ c₆}
    (γ₁ : M.lift.map x₁ ⟶ M.lift.map y₁) (γ₂ : M.lift.map x₂ ⟶ M.lift.map y₂) (γ₃ : M.lift.map x₃ ⟶ M.lift.map y₃) (γ₄ : M.lift.map x₄ ⟶ M.lift.map y₄) (γ₅ : M.lift.map x₅ ⟶ M.lift.map y₅) (γ₆ : M.lift.map x₆ ⟶ M.lift.map y₆)
    {W W' : a₀ ⟶ a₁}
    (N0 : W ≅ p₁ ≫ (x₁ ≫ q₁))
    (N1 : p₁ ≫ (y₁ ≫ q₁) ⟶ p₂ ≫ (x₂ ≫ q₂))
    (N2 : p₂ ≫ (y₂ ≫ q₂) ⟶ p₃ ≫ (x₃ ≫ q₃))
    (N3 : p₃ ≫ (y₃ ≫ q₃) ≅ W')
    (N'0 : W ≅ p₄ ≫ (x₄ ≫ q₄))
    (N'1 : p₄ ≫ (y₄ ≫ q₄) ⟶ p₅ ≫ (x₅ ≫ q₅))
    (N'2 : p₅ ≫ (y₅ ≫ q₅) ⟶ p₆ ≫ (x₆ ≫ q₆))
    (N'3 : p₆ ≫ (y₆ ≫ q₆) ≅ W')
    (hmain : M.lift.map₂ N0.hom ≫
        midK M p₁ q₁ γ₁ ≫
        M.lift.map₂ N1 ≫
        midK M p₂ q₂ γ₂ ≫
        M.lift.map₂ N2 ≫
        midK M p₃ q₃ γ₃ ≫
        M.lift.map₂ N3.hom =
      M.lift.map₂ N'0.hom ≫
        midK M p₄ q₄ γ₄ ≫
        M.lift.map₂ N'1 ≫
        midK M p₅ q₅ γ₅ ≫
        M.lift.map₂ N'2 ≫
        midK M p₆ q₆ γ₆ ≫
        M.lift.map₂ N'3.hom)
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
      γ₃)
    (hn4 : fo (S := S) (S.right L₄.gen) = b₄) (hm4 : fo (S := S) (S.left L₄.gen) = c₄)
    (hr4 : ∀ h e, fw (S.right L₄.gen) L₄.right t h e ≍ p₄)
    (hl4 : ∀ h e, fw s L₄.left (S.left L₄.gen) h e ≍ q₄)
    (hd4 : ∀ h e, fw (S.left L₄.gen) (S.dom L₄.gen) (S.right L₄.gen) h e ≍ x₄)
    (he4 : ∀ h e, fw (S.left L₄.gen) (S.cod L₄.gen) (S.right L₄.gen) h e ≍ y₄)
    (hg4 : ∀ hd hde hc hce, G.gen L₄.gen (S.left L₄.gen) (S.right L₄.gen) rfl rfl hd hde hc hce ≍
      γ₄)
    (hn5 : fo (S := S) (S.right L₅.gen) = b₅) (hm5 : fo (S := S) (S.left L₅.gen) = c₅)
    (hr5 : ∀ h e, fw (S.right L₅.gen) L₅.right t h e ≍ p₅)
    (hl5 : ∀ h e, fw s L₅.left (S.left L₅.gen) h e ≍ q₅)
    (hd5 : ∀ h e, fw (S.left L₅.gen) (S.dom L₅.gen) (S.right L₅.gen) h e ≍ x₅)
    (he5 : ∀ h e, fw (S.left L₅.gen) (S.cod L₅.gen) (S.right L₅.gen) h e ≍ y₅)
    (hg5 : ∀ hd hde hc hce, G.gen L₅.gen (S.left L₅.gen) (S.right L₅.gen) rfl rfl hd hde hc hce ≍
      γ₅)
    (hn6 : fo (S := S) (S.right L₆.gen) = b₆) (hm6 : fo (S := S) (S.left L₆.gen) = c₆)
    (hr6 : ∀ h e, fw (S.right L₆.gen) L₆.right t h e ≍ p₆)
    (hl6 : ∀ h e, fw s L₆.left (S.left L₆.gen) h e ≍ q₆)
    (hd6 : ∀ h e, fw (S.left L₆.gen) (S.dom L₆.gen) (S.right L₆.gen) h e ≍ x₆)
    (he6 : ∀ h e, fw (S.left L₆.gen) (S.cod L₆.gen) (S.right L₆.gen) h e ≍ y₆)
    (hg6 : ∀ hd hde hc hce, G.gen L₆.gen (S.left L₆.gen) (S.right L₆.gen) rfl rfl hd hde hc hce ≍
      γ₆) :
    admissibleChain G a [L₁, L₂, L₃] b h ha hb = admissibleChain G a [L₄, L₅, L₆] b h' ha hb := by
  subst ht hs
  rw [admissibleChain_cons, admissibleChain_pair, admissibleChain_cons, admissibleChain_pair]
  simp only [coreC_eq]
  unfold core
  exact chain₃_heq M γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ N0 N1 N2 N3 N'0 N'1 N'2 N'3 hmain (hn1) (hm1) (hr1 _ _) (hl1 _ _) (hd1 _ _) (he1 _ _) _ (hg1 _ _ _ _) _ _ (hn2) (hm2) (hr2 _ _) (hl2 _ _) (hd2 _ _) (he2 _ _) _ (hg2 _ _ _ _) _ _ (hn3) (hm3) (hr3 _ _) (hl3 _ _) (hd3 _ _) (he3 _ _) _ (hg3 _ _ _ _) _ _ (hn4) (hm4) (hr4 _ _) (hl4 _ _) (hd4 _ _) (he4 _ _) _ (hg4 _ _ _ _) _ _ (hn5) (hm5) (hr5 _ _) (hl5 _ _) (hd5 _ _) (he5 _ _) _ (hg5 _ _ _ _) _ _ (hn6) (hm6) (hr6 _ _) (hl6 _ _) (hd6 _ _) (he6 _ _) _ (hg6 _ _ _ _) _ _ _ _ _ _ _ _ _ _

section Slides

variable {a₀ a₁ b c : FB S}

/-- The composite equation of `chain₂_eq` for a 2-morphism `γd` on the right strand of a word
`U ≫ R` that slides through a crossing `γu : U ≫ R ⟶ R' ≫ U'` to `γd'` on the left strand
`U'`, given the naturality of the crossing in the target bicategory. -/
theorem slide_right_hyp {U : a₀ ⟶ b} {R : b ⟶ a₁} {R' : a₀ ⟶ c} {U' : c ⟶ a₁}
    (γd : M.lift.map U ⟶ M.lift.map U)
    (γu : M.lift.map U ≫ M.lift.map R ⟶ M.lift.map R' ≫ M.lift.map U')
    (γd' : M.lift.map U' ⟶ M.lift.map U')
    (e : γd ▷ M.lift.map R ≫ γu = γu ≫ M.lift.map R' ◁ γd') :
    M.lift.map₂ (λ_ (U ≫ R)).symm.hom ≫ midK M (𝟙 a₀) R γd ≫
        M.lift.map₂ (𝟙 a₀ ◁ (ρ_ (U ≫ R)).inv) ≫
        midK M (𝟙 a₀) (𝟙 a₁) (x := U ≫ R) (y := R' ≫ U') γu ≫
        M.lift.map₂ (λ_ _ ≪≫ ρ_ (R' ≫ U')).hom =
      M.lift.map₂ ((ρ_ (U ≫ R)).symm ≪≫ (λ_ _).symm).hom ≫
        midK M (𝟙 a₀) (𝟙 a₁) (x := U ≫ R) (y := R' ≫ U') γu ≫
        M.lift.map₂ ((λ_ _).hom ≫ (α_ R' U' (𝟙 a₁)).hom) ≫ midK M R' (𝟙 a₁) γd' ≫
        M.lift.map₂ (whiskerLeftIso R' (ρ_ U')).hom := by
  simp only [midK, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, PrelaxFunctor.map₂_comp,
    lift_map₂_whiskerLeft, lift_map₂_associator_hom, lift_map₂_leftUnitor_hom,
    lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom, lift_map₂_rightUnitor_inv,
    lift_map_comp]
  calc _ = 𝟙 _ ⊗≫ (γd ▷ M.lift.map R ≫ γu) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (γu ≫ M.lift.map R' ◁ γd') ⊗≫ 𝟙 _ := by rw [e]
    _ = _ := by bicategory

/-- The mirror of `slide_right_hyp`: a 2-morphism `γd` on the left strand of `R ≫ U` slides
through `γu : R ≫ U ⟶ U'' ≫ R''` to `γd'` on the right strand `U''`. -/
theorem slide_left_hyp {R : a₀ ⟶ c} {U : c ⟶ a₁} {U'' : a₀ ⟶ b} {R'' : b ⟶ a₁}
    (γd : M.lift.map U ⟶ M.lift.map U)
    (γu : M.lift.map R ≫ M.lift.map U ⟶ M.lift.map U'' ≫ M.lift.map R'')
    (γd' : M.lift.map U'' ⟶ M.lift.map U'')
    (e : M.lift.map R ◁ γd ≫ γu = γu ≫ γd' ▷ M.lift.map R'') :
    M.lift.map₂ (whiskerLeftIso R (ρ_ U).symm).hom ≫ midK M R (𝟙 a₁) γd ≫
        M.lift.map₂ ((α_ R U (𝟙 a₁)).inv ≫ (λ_ _).inv) ≫
        midK M (𝟙 a₀) (𝟙 a₁) (x := R ≫ U) (y := U'' ≫ R'') γu ≫
        M.lift.map₂ (λ_ _ ≪≫ ρ_ (U'' ≫ R'')).hom =
      M.lift.map₂ ((ρ_ (R ≫ U)).symm ≪≫ (λ_ _).symm).hom ≫
        midK M (𝟙 a₀) (𝟙 a₁) (x := R ≫ U) (y := U'' ≫ R'') γu ≫
        M.lift.map₂ (𝟙 a₀ ◁ (ρ_ (U'' ≫ R'')).hom) ≫ midK M (𝟙 a₀) R'' γd' ≫
        M.lift.map₂ (λ_ (U'' ≫ R'')).hom := by
  simp only [midK, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, PrelaxFunctor.map₂_comp,
    lift_map₂_whiskerLeft,
    lift_map₂_associator_inv, lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv,
    lift_map₂_rightUnitor_hom, lift_map₂_rightUnitor_inv, lift_map_comp]
  calc _ = 𝟙 _ ⊗≫ (M.lift.map R ◁ γd ≫ γu) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (γu ≫ γd' ▷ M.lift.map R'') ⊗≫ 𝟙 _ := by rw [e]
    _ = _ := by bicategory

section Three

variable {ρ ρi ρj μj μij μi : FB S}
  {R0 : ρ ⟶ a₁} {Ui : ρi ⟶ ρ} {Uj : a₀ ⟶ ρi} {Ui2 : a₀ ⟶ ρj} {Uj2 : ρj ⟶ ρ}
  {R3 : ρj ⟶ μj} {Uj3 : μj ⟶ a₁} {R4 : a₀ ⟶ μij} {Ui4 : μij ⟶ μj} {R5 : ρi ⟶ μi}
  {Ui5 : μi ⟶ a₁} {Uj6 : μij ⟶ μi}

/-- The composite equation of `chain₃_eq` for a crossing `τ` of the two strands to the right of
a strand `R0`, which then moves to the right through both, against `R0` moving first and the
crossing `τ'` happening to its left. -/
theorem slide3_right_hyp
    (τ : M.lift.map Uj ≫ M.lift.map Ui ⟶ M.lift.map Ui2 ≫ M.lift.map Uj2)
    (γ₂ : M.lift.map Uj2 ≫ M.lift.map R0 ⟶ M.lift.map R3 ≫ M.lift.map Uj3)
    (γ₃ : M.lift.map Ui2 ≫ M.lift.map R3 ⟶ M.lift.map R4 ≫ M.lift.map Ui4)
    (γ₄ : M.lift.map Ui ≫ M.lift.map R0 ⟶ M.lift.map R5 ≫ M.lift.map Ui5)
    (γ₅ : M.lift.map Uj ≫ M.lift.map R5 ⟶ M.lift.map R4 ≫ M.lift.map Uj6)
    (τ' : M.lift.map Uj6 ≫ M.lift.map Ui5 ⟶ M.lift.map Ui4 ≫ M.lift.map Uj3)
    (e : (α_ _ _ _).inv ≫ τ ▷ M.lift.map R0 ≫ (α_ _ _ _).hom ≫ M.lift.map Ui2 ◁ γ₂ ≫
        (α_ _ _ _).inv ≫ γ₃ ▷ M.lift.map Uj3 ≫ (α_ _ _ _).hom =
      M.lift.map Uj ◁ γ₄ ≫ (α_ _ _ _).inv ≫ γ₅ ▷ M.lift.map Ui5 ≫ (α_ _ _ _).hom ≫
        M.lift.map R4 ◁ τ') :
    M.lift.map₂ ((α_ Uj Ui R0).symm ≪≫ (λ_ _).symm).hom ≫ midK M (𝟙 a₀) R0 (x := Uj ≫ Ui) (y := Ui2 ≫ Uj2) τ ≫
        M.lift.map₂ ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Ui2 ◁ (ρ_ _).inv) ≫
        midK M Ui2 (𝟙 a₁) (x := Uj2 ≫ R0) (y := R3 ≫ Uj3) γ₂ ≫
        M.lift.map₂ (Ui2 ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) ≫
        midK M (𝟙 a₀) Uj3 (x := Ui2 ≫ R3) (y := R4 ≫ Ui4) γ₃ ≫
        M.lift.map₂ (λ_ _ ≪≫ α_ R4 Ui4 Uj3).hom =
      M.lift.map₂ (whiskerLeftIso Uj (ρ_ (Ui ≫ R0)).symm).hom ≫
        midK M Uj (𝟙 a₁) (x := Ui ≫ R0) (y := R5 ≫ Ui5) γ₄ ≫
        M.lift.map₂ (Uj ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) ≫
        midK M (𝟙 a₀) Ui5 (x := Uj ≫ R5) (y := R4 ≫ Uj6) γ₅ ≫
        M.lift.map₂ ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ R4 ◁ (ρ_ _).inv) ≫
        midK M R4 (𝟙 a₁) (x := Uj6 ≫ Ui5) (y := Ui4 ≫ Uj3) τ' ≫ M.lift.map₂ (whiskerLeftIso R4 (ρ_ (Ui4 ≫ Uj3))).hom := by
  simp only [midK, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, PrelaxFunctor.map₂_comp,
    lift_map₂_whiskerLeft, lift_map₂_associator_hom,
    lift_map₂_associator_inv, lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv,
    lift_map₂_rightUnitor_hom, lift_map₂_rightUnitor_inv, lift_map_comp]
  calc _ = 𝟙 _ ⊗≫ ((α_ _ _ _).inv ≫ τ ▷ M.lift.map R0 ≫ (α_ _ _ _).hom ≫
          M.lift.map Ui2 ◁ γ₂ ≫ (α_ _ _ _).inv ≫ γ₃ ▷ M.lift.map Uj3 ≫ (α_ _ _ _).hom) ⊗≫
          𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (M.lift.map Uj ◁ γ₄ ≫ (α_ _ _ _).inv ≫ γ₅ ▷ M.lift.map Ui5 ≫
          (α_ _ _ _).hom ≫ M.lift.map R4 ◁ τ') ⊗≫ 𝟙 _ := by rw [e]
    _ = _ := by bicategory

end Three

section ThreeMirror

variable {si sij sir sr srj sj : FB S}
  {R : a₀ ⟶ sij} {Uj : sij ⟶ si} {Ui : si ⟶ a₁} {Uj' : a₀ ⟶ sir} {R' : sir ⟶ si}
  {Ui'' : sir ⟶ sr} {R'' : sr ⟶ a₁} {Ui3 : a₀ ⟶ srj} {Uj3 : srj ⟶ sr}
  {Ui4 : sij ⟶ sj} {Uj4 : sj ⟶ a₁} {R5 : srj ⟶ sj}

/-- The mirror of `slide3_right_hyp`: a strand `R` to the right of two strands moves to the left
through both and then the two strands cross, against the crossing happening first. -/
theorem slide3_left_hyp
    (γ₁ : M.lift.map R ≫ M.lift.map Uj ⟶ M.lift.map Uj' ≫ M.lift.map R')
    (γ₂ : M.lift.map R' ≫ M.lift.map Ui ⟶ M.lift.map Ui'' ≫ M.lift.map R'')
    (γ₃ : M.lift.map Uj' ≫ M.lift.map Ui'' ⟶ M.lift.map Ui3 ≫ M.lift.map Uj3)
    (γ₄ : M.lift.map Uj ≫ M.lift.map Ui ⟶ M.lift.map Ui4 ≫ M.lift.map Uj4)
    (γ₅ : M.lift.map R ≫ M.lift.map Ui4 ⟶ M.lift.map Ui3 ≫ M.lift.map R5)
    (γ₆ : M.lift.map R5 ≫ M.lift.map Uj4 ⟶ M.lift.map Uj3 ≫ M.lift.map R'')
    (e : (α_ _ _ _).inv ≫ γ₁ ▷ M.lift.map Ui ≫ (α_ _ _ _).hom ≫ M.lift.map Uj' ◁ γ₂ ≫
        (α_ _ _ _).inv ≫ γ₃ ▷ M.lift.map R'' ≫ (α_ _ _ _).hom =
      M.lift.map R ◁ γ₄ ≫ (α_ _ _ _).inv ≫ γ₅ ▷ M.lift.map Uj4 ≫ (α_ _ _ _).hom ≫
        M.lift.map Ui3 ◁ γ₆) :
    M.lift.map₂ ((α_ R Uj Ui).symm ≪≫ (λ_ _).symm).hom ≫ midK M (𝟙 a₀) Ui (x := R ≫ Uj) (y := Uj' ≫ R') γ₁ ≫
        M.lift.map₂ ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Uj' ◁ (ρ_ _).inv) ≫
        midK M Uj' (𝟙 a₁) (x := R' ≫ Ui) (y := Ui'' ≫ R'') γ₂ ≫
        M.lift.map₂ (Uj' ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) ≫
        midK M (𝟙 a₀) R'' (x := Uj' ≫ Ui'') (y := Ui3 ≫ Uj3) γ₃ ≫
        M.lift.map₂ (λ_ _ ≪≫ α_ Ui3 Uj3 R'').hom =
      M.lift.map₂ (whiskerLeftIso R (ρ_ (Uj ≫ Ui)).symm).hom ≫
        midK M R (𝟙 a₁) (x := Uj ≫ Ui) (y := Ui4 ≫ Uj4) γ₄ ≫
        M.lift.map₂ (R ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) ≫
        midK M (𝟙 a₀) Uj4 (x := R ≫ Ui4) (y := Ui3 ≫ R5) γ₅ ≫
        M.lift.map₂ ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Ui3 ◁ (ρ_ _).inv) ≫
        midK M Ui3 (𝟙 a₁) (x := R5 ≫ Uj4) (y := Uj3 ≫ R'') γ₆ ≫ M.lift.map₂ (whiskerLeftIso Ui3 (ρ_ (Uj3 ≫ R''))).hom := by
  simp only [midK, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, PrelaxFunctor.map₂_comp,
    lift_map₂_whiskerLeft, lift_map₂_associator_hom,
    lift_map₂_associator_inv, lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv,
    lift_map₂_rightUnitor_hom, lift_map₂_rightUnitor_inv, lift_map_comp]
  calc _ = 𝟙 _ ⊗≫ ((α_ _ _ _).inv ≫ γ₁ ▷ M.lift.map Ui ≫ (α_ _ _ _).hom ≫
          M.lift.map Uj' ◁ γ₂ ≫ (α_ _ _ _).inv ≫ γ₃ ▷ M.lift.map R'' ≫ (α_ _ _ _).hom) ⊗≫
          𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (M.lift.map R ◁ γ₄ ≫ (α_ _ _ _).inv ≫ γ₅ ▷ M.lift.map Uj4 ≫
          (α_ _ _ _).hom ≫ M.lift.map Ui3 ◁ γ₆) ⊗≫ 𝟙 _ := by rw [e]
    _ = _ := by bicategory

end ThreeMirror

end Slides

end Categorification.Diagrams.BicatInterp
