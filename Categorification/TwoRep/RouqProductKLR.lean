/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqProduct
import Categorification.KLR.KL1

/-!
# Upward KLR relations and mixed inversion on categories of 1-morphisms

For Rouquier families `W` and `T` and the Rouquier family `RouqFamily.homProduct W T` on
`Hom_B(T(-x₂), W(x₁))`, the mixed upward KLR relations (J. Brundan, *On the definition of
Kac–Moody 2-category*, arXiv:1501.00350v1, (1.2)–(1.4)) hold for the parameters `Q` of `W` on
its colours, those of `T` on its colours, and `Q = 1` between colours of different sides
(`RouqFamily.homProduct_upKLR`). The relations between the two sides hold because the crossings
between them are associators: in components they are coherence identities in `B`.

Brundan's mixed inversion (1.7) holds as well (`RouqFamily.homProduct_mixedInversion`): on one
side it is that of `W`, or that of the reverse of `T`; between the two sides the mixed sideways
crossing is an associator, hence invertible.

This is the relation part of the test representations in B. Webster, *Unfurling
Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of Theorem `nondegenerate`, where
the labels `Ĩ₋` and `Ĩ₊` are orthogonal (`Q̃ = 1` between them).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w' w v u u₁

namespace RouqFamily

/-! ## Coherence identities in components

In components, a mixed braid relation is an identity between associators and one whiskered
crossing. `L` marks a colour acting by postcomposition and `R` a colour acting by
precomposition; the pattern lists the colours `i, j, c` of `RouqUpKLR.braid`. -/

section Coherence

variable {B : Type u} [Bicategory.{w, v} B]

theorem mixedBraid_LLR {t₁ t₀ w₀ w₁ w₂ w₃ : B} (f : t₁ ⟶ t₀) (X : t₀ ⟶ w₀) (Ej : w₀ ⟶ w₁)
    (Ei : w₁ ⟶ w₂) (Ei' : w₀ ⟶ w₃) (Ej' : w₃ ⟶ w₂) (τ : Ej ≫ Ei ⟶ Ei' ≫ Ej') :
    ((α_ (f ≫ X) Ej Ei).hom ≫ (f ≫ X) ◁ τ ≫ (α_ (f ≫ X) Ei' Ej').inv) ≫
        (𝟙 _ ≫ (α_ f X Ei').hom ▷ Ej' ≫ 𝟙 _) ≫ (α_ f (X ≫ Ei') Ej').hom =
      (𝟙 _ ≫ (α_ f X Ej).hom ▷ Ei ≫ 𝟙 _) ≫ (α_ f (X ≫ Ej) Ei).hom ≫
        (𝟙 _ ≫ f ◁ ((α_ X Ej Ei).hom ≫ X ◁ τ ≫ (α_ X Ei' Ej').inv) ≫ 𝟙 _) := by
  simp only [Category.id_comp, Category.comp_id]
  bicategory

theorem mixedBraid_LRL {t₁ t₀ w₀ w₁ w₂ w₃ : B} (g : t₁ ⟶ t₀) (X : t₀ ⟶ w₀) (Ec : w₀ ⟶ w₁)
    (Ei : w₁ ⟶ w₂) (Ei' : w₀ ⟶ w₃) (Ec' : w₃ ⟶ w₂) (τ : Ec ≫ Ei ⟶ Ei' ≫ Ec') :
    (α_ g (X ≫ Ec) Ei).hom ≫
        (𝟙 _ ≫ g ◁ ((α_ X Ec Ei).hom ≫ X ◁ τ ≫ (α_ X Ei' Ec').inv) ≫ 𝟙 _) ≫
        (α_ g (X ≫ Ei') Ec').inv =
      (𝟙 _ ≫ (α_ g X Ec).inv ▷ Ei ≫ 𝟙 _) ≫
        ((α_ (g ≫ X) Ec Ei).hom ≫ (g ≫ X) ◁ τ ≫ (α_ (g ≫ X) Ei' Ec').inv) ≫
        (𝟙 _ ≫ (α_ g X Ei').hom ▷ Ec' ≫ 𝟙 _) := by
  simp only [Category.id_comp, Category.comp_id]
  bicategory

theorem mixedBraid_RLL {t₁ t₀ w₀ w₁ w₂ w₃ : B} (f : t₁ ⟶ t₀) (X : t₀ ⟶ w₀) (Ec : w₀ ⟶ w₁)
    (Ej : w₁ ⟶ w₂) (Ej' : w₀ ⟶ w₃) (Ec' : w₃ ⟶ w₂) (τ : Ec ≫ Ej ⟶ Ej' ≫ Ec') :
    (α_ f (X ≫ Ec) Ej).inv ≫ (𝟙 _ ≫ (α_ f X Ec).inv ▷ Ej ≫ 𝟙 _) ≫
        ((α_ (f ≫ X) Ec Ej).hom ≫ (f ≫ X) ◁ τ ≫ (α_ (f ≫ X) Ej' Ec').inv) =
      (𝟙 _ ≫ f ◁ ((α_ X Ec Ej).hom ≫ X ◁ τ ≫ (α_ X Ej' Ec').inv) ≫ 𝟙 _) ≫
        (α_ f (X ≫ Ej') Ec').inv ≫ (𝟙 _ ≫ (α_ f X Ej').inv ▷ Ec' ≫ 𝟙 _) := by
  simp only [Category.id_comp, Category.comp_id]
  bicategory

theorem mixedBraid_LRR {T₂ T₁ T₀ T₃ w₀ w₁ : B} (tj : T₂ ⟶ T₁) (tc : T₁ ⟶ T₀) (tc' : T₂ ⟶ T₃)
    (tj' : T₃ ⟶ T₀) (X : T₀ ⟶ w₀) (Ei : w₀ ⟶ w₁) (ρ : tj ≫ tc ⟶ tc' ≫ tj') :
    (α_ tj (tc ≫ X) Ei).hom ≫ (𝟙 _ ≫ tj ◁ (α_ tc X Ei).hom ≫ 𝟙 _) ≫
        ((α_ tj tc (X ≫ Ei)).inv ≫ ρ ▷ (X ≫ Ei) ≫ (α_ tc' tj' (X ≫ Ei)).hom) =
      (𝟙 _ ≫ ((α_ tj tc X).inv ≫ ρ ▷ X ≫ (α_ tc' tj' X).hom) ▷ Ei ≫ 𝟙 _) ≫
        (α_ tc' (tj' ≫ X) Ei).hom ≫ (𝟙 _ ≫ tc' ◁ (α_ tj' X Ei).hom ≫ 𝟙 _) := by
  simp only [Category.id_comp, Category.comp_id]
  bicategory

theorem mixedBraid_RLR {T₂ T₁ T₀ T₃ w₀ w₁ : B} (ti : T₂ ⟶ T₁) (tc : T₁ ⟶ T₀) (tc' : T₂ ⟶ T₃)
    (ti' : T₃ ⟶ T₀) (X : T₀ ⟶ w₀) (Ej : w₀ ⟶ w₁) (ρ : ti ≫ tc ⟶ tc' ≫ ti') :
    (α_ ti (tc ≫ X) Ej).inv ≫
        (𝟙 _ ≫ ((α_ ti tc X).inv ≫ ρ ▷ X ≫ (α_ tc' ti' X).hom) ▷ Ej ≫ 𝟙 _) ≫
        (α_ tc' (ti' ≫ X) Ej).hom =
      (𝟙 _ ≫ ti ◁ (α_ tc X Ej).hom ≫ 𝟙 _) ≫
        ((α_ ti tc (X ≫ Ej)).inv ≫ ρ ▷ (X ≫ Ej) ≫ (α_ tc' ti' (X ≫ Ej)).hom) ≫
        (𝟙 _ ≫ tc' ◁ (α_ ti' X Ej).inv ≫ 𝟙 _) := by
  simp only [Category.id_comp, Category.comp_id]
  bicategory

theorem mixedBraid_RRL {T₂ T₁ T₀ T₃ w₀ w₁ : B} (ti : T₂ ⟶ T₁) (tj : T₁ ⟶ T₀) (tj' : T₂ ⟶ T₃)
    (ti' : T₃ ⟶ T₀) (X : T₀ ⟶ w₀) (Ec : w₀ ⟶ w₁) (ρ : ti ≫ tj ⟶ tj' ≫ ti') :
    ((α_ ti tj (X ≫ Ec)).inv ≫ ρ ▷ (X ≫ Ec) ≫ (α_ tj' ti' (X ≫ Ec)).hom) ≫
        (𝟙 _ ≫ tj' ◁ (α_ ti' X Ec).inv ≫ 𝟙 _) ≫ (α_ tj' (ti' ≫ X) Ec).inv =
      (𝟙 _ ≫ ti ◁ (α_ tj X Ec).inv ≫ 𝟙 _) ≫ (α_ ti (tj ≫ X) Ec).inv ≫
        (𝟙 _ ≫ ((α_ ti tj X).inv ≫ ρ ▷ X ≫ (α_ tj' ti' X).hom) ▷ Ec ≫ 𝟙 _) := by
  simp only [Category.id_comp, Category.comp_id]
  bicategory

theorem mixedMate_LR {t₁ t₀ w₀ w₁ : B} (t : t₁ ⟶ t₀) (X : t₀ ⟶ w₁) {e : w₀ ⟶ w₁}
    {f : w₁ ⟶ w₀} (A : e ⊣ f) :
    ((𝟙 _ ≫ (((ρ_ (t ≫ (X ≫ f))).inv ≫ (t ≫ (X ≫ f)) ◁ A.unit ≫
        (α_ (t ≫ (X ≫ f)) e f).inv) ≫ 𝟙 _ ≫ (α_ t (X ≫ f) e).hom ▷ f)) ≫ 𝟙 _) ≫
      𝟙 _ ≫ (t ◁ ((α_ X f e).hom ≫ X ◁ A.counit ≫ (ρ_ X).hom)) ▷ f ≫ 𝟙 _ =
      (α_ t X f).inv := by
  simp only [Category.id_comp, Category.comp_id]
  calc _ = 𝟙 _ ⊗≫ t ◁ X ◁ rightZigzag A.unit A.counit ⊗≫ 𝟙 _ := by
        rw [rightZigzag]; bicategory
    _ = (α_ t X f).inv := by rw [A.right_triangle]; bicategory

theorem mixedMate_RL {s₀ s₁ w₀ w₁ : B} {f : s₀ ⟶ s₁} {e : s₁ ⟶ s₀} (A : f ⊣ e) (X : s₁ ⟶ w₀)
    (w : w₀ ⟶ w₁) :
    ((𝟙 _ ≫ (((λ_ ((f ≫ X) ≫ w)).inv ≫ A.unit ▷ ((f ≫ X) ≫ w) ≫
        (α_ f e ((f ≫ X) ≫ w)).hom) ≫ 𝟙 _ ≫ f ◁ (α_ e (f ≫ X) w).inv)) ≫ 𝟙 _) ≫
      𝟙 _ ≫ f ◁ (((α_ e f X).inv ≫ A.counit ▷ X ≫ (λ_ X).hom) ▷ w) ≫ 𝟙 _ =
      (α_ f X w).hom := by
  simp only [Category.id_comp, Category.comp_id]
  calc _ = 𝟙 _ ⊗≫ leftZigzag A.unit A.counit ▷ X ▷ w ⊗≫ 𝟙 _ := by
        rw [leftZigzag]; bicategory
    _ = (α_ f X w).hom := by rw [A.left_triangle]; bicategory

end Coherence

/-- Identify the unchanged weight components along the given edges. -/
syntax "subst_weights" (ppSpace colGt ident)* : tactic

set_option hygiene false in
macro_rules
  | `(tactic| subst_weights $hs*) => do
    let tacs ← hs.mapM fun h =>
      `(tactic| ((try obtain rfl := inl_snd _ $h:ident); (try obtain rfl := inr_fst _ $h:ident)))
    `(tactic| ($[$tacs]*))

section Relations

open QuantumGroup UDot

variable {k : Type w'} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  {I₁ I₂ : Type*} {C₁ : CartanDatum I₁} {C₂ : CartanDatum I₂}
  {X₁ Y₁ X₂ Y₂ : Type u₁} [AddCommGroup X₁] [AddCommGroup Y₁] [AddCommGroup X₂]
  [AddCommGroup Y₂] {RD₁ : WeightDatum C₁ X₁ Y₁} {RD₂ : WeightDatum C₂ X₂ Y₂}
  {W : RouqFamily (B := B) RD₁} {T : RouqFamily (B := B) RD₂}

theorem fst_step' (i : I₁) {a₁ b₁ : X₁} {a₂ b₂ : X₂}
    (h : (a₁, a₂) + (RD₁.prod RD₂).iX (.inl i) = (b₁, b₂)) : a₁ + RD₁.iX i = b₁ :=
  congrArg Prod.fst h

theorem snd_step' (i : I₂) {a₁ b₁ : X₁} {a₂ b₂ : X₂}
    (h : (a₁, a₂) + (RD₁.prod RD₂).iX (.inr i) = (b₁, b₂)) : a₂ + RD₂.iX i = b₂ :=
  congrArg Prod.snd h

theorem ncEval_zero_eq {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) :
    KLR.ncEval y (0 : MvPolynomial (Fin n) k) = 0 := by
  unfold KLR.ncEval
  exact Finsupp.sum_zero_index

theorem ncEval_one_eq {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) :
    KLR.ncEval y (1 : MvPolynomial (Fin n) k) = 1 := by
  unfold KLR.ncEval
  rw [show (1 : MvPolynomial (Fin n) k).coeff = Finsupp.single 0 1 from rfl,
    Finsupp.sum_single_index (by simp)]
  simp

/-- The parameters of the product: those of `W` and of `T` on their colours, and `1` between
colours of different sides. -/
def prodQ (Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k) (Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k) :
    I₁ ⊕ I₂ → I₁ ⊕ I₂ → MvPolynomial (Fin 2) k
  | .inl i, .inl j => Q₁ i j
  | .inr i, .inr j => Q₂ i j
  | _, _ => 1

/-- The braid relation of `RouqUpKLR.braid` for a Rouquier family, as a proposition. -/
def braidEq {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
    {RD : WeightDatum C X Y} {B' : Type*} [Bicategory B'] [∀ a b : B', Preadditive (a ⟶ b)]
    (S : RouqFamily (B := B') RD)
    (i j c : I) {l w₁ w₂ w₃ w₄ w₅ w₆ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX j = w₂)
    (e3 : w₂ + RD.iX i = m) (e4 : w₁ + RD.iX i = w₃) (e5 : w₃ + RD.iX j = m)
    (e6 : l + RD.iX i = w₄) (e7 : w₄ + RD.iX c = w₃) (e8 : w₄ + RD.iX j = w₅)
    (e9 : w₅ + RD.iX c = m) (e10 : l + RD.iX j = w₆) (e11 : w₆ + RD.iX c = w₂)
    (e12 : w₆ + RD.iX i = w₅) : Prop :=
  S.E c e1 ◁ S.cross i j e2 e3 e4 e5 ≫
      ((α_ (S.E c e1) (S.E i e4) (S.E j e5)).inv ≫ S.cross i c e1 e4 e6 e7 ▷ S.E j e5 ≫
        (α_ (S.E i e6) (S.E c e7) (S.E j e5)).hom) ≫
      S.E i e6 ◁ S.cross j c e7 e5 e8 e9 =
    ((α_ (S.E c e1) (S.E j e2) (S.E i e3)).inv ≫ S.cross j c e1 e2 e10 e11 ▷ S.E i e3 ≫
        (α_ (S.E j e10) (S.E c e11) (S.E i e3)).hom) ≫
      S.E j e10 ◁ S.cross i c e11 e3 e12 e9 ≫
      ((α_ (S.E j e10) (S.E i e12) (S.E c e9)).inv ≫ S.cross i j e10 e12 e6 e8 ▷ S.E c e9 ≫
        (α_ (S.E i e6) (S.E j e8) (S.E c e9)).hom)

variable (W T) in
theorem homProduct_braid_LLL {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k}
    (H₁ : RouqUpKLR W Q₁) (i : I₁) (j : I₁) (c : I₁) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X₁ × X₂} (e1 : l + (RD₁.prod RD₂).iX (.inl c) = w₁)
    (e2 : w₁ + (RD₁.prod RD₂).iX (.inl j) = w₂) (e3 : w₂ + (RD₁.prod RD₂).iX (.inl i) = m)
    (e4 : w₁ + (RD₁.prod RD₂).iX (.inl i) = w₃) (e5 : w₃ + (RD₁.prod RD₂).iX (.inl j) = m)
    (e6 : l + (RD₁.prod RD₂).iX (.inl i) = w₄) (e7 : w₄ + (RD₁.prod RD₂).iX (.inl c) = w₃)
    (e8 : w₄ + (RD₁.prod RD₂).iX (.inl j) = w₅) (e9 : w₅ + (RD₁.prod RD₂).iX (.inl c) = m)
    (e10 : l + (RD₁.prod RD₂).iX (.inl j) = w₆) (e11 : w₆ + (RD₁.prod RD₂).iX (.inl c) = w₂)
    (e12 : w₆ + (RD₁.prod RD₂).iX (.inl i) = w₅) :
    braidEq (homProduct k W T) (Sum.inl i) (Sum.inl j) (Sum.inl c)
      e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 := by
  obtain ⟨l₁, l₂⟩ := l
  obtain ⟨p₁, p₂⟩ := w₁
  obtain ⟨q₁, q₂⟩ := w₂
  obtain ⟨r₁, r₂⟩ := w₃
  obtain ⟨s₁, s₂⟩ := w₄
  obtain ⟨t₁, t₂⟩ := w₅
  obtain ⟨u₁, u₂⟩ := w₆
  obtain ⟨m₁, m₂⟩ := m
  subst_weights e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  exact (yoneda_upKLR W (T.obj (-l₂)) H₁).braid i j c hb
    (fst_step' c e1) (fst_step' j e2) (fst_step' i e3)
    (fst_step' i e4) (fst_step' j e5) (fst_step' i e6)
    (fst_step' c e7) (fst_step' j e8) (fst_step' c e9)
    (fst_step' j e10) (fst_step' c e11) (fst_step' i e12)

variable (W T) in
theorem homProduct_braid_LLR
    (i : I₁) (j : I₁) (c : I₂) 
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X₁ × X₂} (e1 : l + (RD₁.prod RD₂).iX (.inr c) = w₁)
    (e2 : w₁ + (RD₁.prod RD₂).iX (.inl j) = w₂) (e3 : w₂ + (RD₁.prod RD₂).iX (.inl i) = m)
    (e4 : w₁ + (RD₁.prod RD₂).iX (.inl i) = w₃) (e5 : w₃ + (RD₁.prod RD₂).iX (.inl j) = m)
    (e6 : l + (RD₁.prod RD₂).iX (.inl i) = w₄) (e7 : w₄ + (RD₁.prod RD₂).iX (.inr c) = w₃)
    (e8 : w₄ + (RD₁.prod RD₂).iX (.inl j) = w₅) (e9 : w₅ + (RD₁.prod RD₂).iX (.inr c) = m)
    (e10 : l + (RD₁.prod RD₂).iX (.inl j) = w₆) (e11 : w₆ + (RD₁.prod RD₂).iX (.inr c) = w₂)
    (e12 : w₆ + (RD₁.prod RD₂).iX (.inl i) = w₅) :
    braidEq (homProduct k W T) (Sum.inl i) (Sum.inl j) (Sum.inr c)
      e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 := by
  obtain ⟨l₁, l₂⟩ := l
  obtain ⟨p₁, p₂⟩ := w₁
  obtain ⟨q₁, q₂⟩ := w₂
  obtain ⟨r₁, r₂⟩ := w₃
  obtain ⟨s₁, s₂⟩ := w₄
  obtain ⟨t₁, t₂⟩ := w₅
  obtain ⟨u₁, u₂⟩ := w₆
  obtain ⟨m₁, m₂⟩ := m
  subst_weights e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  apply ObjectProperty.hom_ext
  ext X
  exact mixedBraid_LLR (T.E c (neg_reg c (snd_step' c e1))) X (W.E j (fst_step' j e2))
    (W.E i (fst_step' i e3)) (W.E i (fst_step' i e4)) (W.E j (fst_step' j e5))
    (W.cross i j (fst_step' j e2) (fst_step' i e3) (fst_step' i e4) (fst_step' j e5))

variable (W T) in
theorem homProduct_braid_LRL
    (i : I₁) (j : I₂) (c : I₁)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X₁ × X₂} (e1 : l + (RD₁.prod RD₂).iX (.inl c) = w₁)
    (e2 : w₁ + (RD₁.prod RD₂).iX (.inr j) = w₂) (e3 : w₂ + (RD₁.prod RD₂).iX (.inl i) = m)
    (e4 : w₁ + (RD₁.prod RD₂).iX (.inl i) = w₃) (e5 : w₃ + (RD₁.prod RD₂).iX (.inr j) = m)
    (e6 : l + (RD₁.prod RD₂).iX (.inl i) = w₄) (e7 : w₄ + (RD₁.prod RD₂).iX (.inl c) = w₃)
    (e8 : w₄ + (RD₁.prod RD₂).iX (.inr j) = w₅) (e9 : w₅ + (RD₁.prod RD₂).iX (.inl c) = m)
    (e10 : l + (RD₁.prod RD₂).iX (.inr j) = w₆) (e11 : w₆ + (RD₁.prod RD₂).iX (.inl c) = w₂)
    (e12 : w₆ + (RD₁.prod RD₂).iX (.inl i) = w₅) :
    braidEq (homProduct k W T) (Sum.inl i) (Sum.inr j) (Sum.inl c)
      e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 := by
  obtain ⟨l₁, l₂⟩ := l
  obtain ⟨p₁, p₂⟩ := w₁
  obtain ⟨q₁, q₂⟩ := w₂
  obtain ⟨r₁, r₂⟩ := w₃
  obtain ⟨s₁, s₂⟩ := w₄
  obtain ⟨t₁, t₂⟩ := w₅
  obtain ⟨u₁, u₂⟩ := w₆
  obtain ⟨m₁, m₂⟩ := m
  subst_weights e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  apply ObjectProperty.hom_ext
  ext X
  exact mixedBraid_LRL (T.E j (neg_reg j (snd_step' j e2))) X (W.E c (fst_step' c e1))
    (W.E i (fst_step' i e4)) (W.E i (fst_step' i e6)) (W.E c (fst_step' c e7))
    (W.cross i c (fst_step' c e1) (fst_step' i e4) (fst_step' i e6) (fst_step' c e7))

variable (W T) in
theorem homProduct_braid_LRR
    (i : I₁) (j : I₂) (c : I₂) 
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X₁ × X₂} (e1 : l + (RD₁.prod RD₂).iX (.inr c) = w₁)
    (e2 : w₁ + (RD₁.prod RD₂).iX (.inr j) = w₂) (e3 : w₂ + (RD₁.prod RD₂).iX (.inl i) = m)
    (e4 : w₁ + (RD₁.prod RD₂).iX (.inl i) = w₃) (e5 : w₃ + (RD₁.prod RD₂).iX (.inr j) = m)
    (e6 : l + (RD₁.prod RD₂).iX (.inl i) = w₄) (e7 : w₄ + (RD₁.prod RD₂).iX (.inr c) = w₃)
    (e8 : w₄ + (RD₁.prod RD₂).iX (.inr j) = w₅) (e9 : w₅ + (RD₁.prod RD₂).iX (.inr c) = m)
    (e10 : l + (RD₁.prod RD₂).iX (.inr j) = w₆) (e11 : w₆ + (RD₁.prod RD₂).iX (.inr c) = w₂)
    (e12 : w₆ + (RD₁.prod RD₂).iX (.inl i) = w₅) :
    braidEq (homProduct k W T) (Sum.inl i) (Sum.inr j) (Sum.inr c)
      e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 := by
  obtain ⟨l₁, l₂⟩ := l
  obtain ⟨p₁, p₂⟩ := w₁
  obtain ⟨q₁, q₂⟩ := w₂
  obtain ⟨r₁, r₂⟩ := w₃
  obtain ⟨s₁, s₂⟩ := w₄
  obtain ⟨t₁, t₂⟩ := w₅
  obtain ⟨u₁, u₂⟩ := w₆
  obtain ⟨m₁, m₂⟩ := m
  subst_weights e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  apply ObjectProperty.hom_ext
  ext X
  exact mixedBraid_LRR (T.E j (neg_reg j (snd_step' j e2))) (T.E c (neg_reg c
    (snd_step' c e1))) (T.E c (neg_reg c (snd_step' c e11))) (T.E j
    (neg_reg j (snd_step' j e10))) X (W.E i (fst_step' i e3))
    (T.reverse.cross j c (snd_step' c e7) (snd_step' j e5) (snd_step' j e8) (snd_step' c e9))

variable (W T) in
theorem homProduct_braid_RLL
    (i : I₂) (j : I₁) (c : I₁) 
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X₁ × X₂} (e1 : l + (RD₁.prod RD₂).iX (.inl c) = w₁)
    (e2 : w₁ + (RD₁.prod RD₂).iX (.inl j) = w₂) (e3 : w₂ + (RD₁.prod RD₂).iX (.inr i) = m)
    (e4 : w₁ + (RD₁.prod RD₂).iX (.inr i) = w₃) (e5 : w₃ + (RD₁.prod RD₂).iX (.inl j) = m)
    (e6 : l + (RD₁.prod RD₂).iX (.inr i) = w₄) (e7 : w₄ + (RD₁.prod RD₂).iX (.inl c) = w₃)
    (e8 : w₄ + (RD₁.prod RD₂).iX (.inl j) = w₅) (e9 : w₅ + (RD₁.prod RD₂).iX (.inl c) = m)
    (e10 : l + (RD₁.prod RD₂).iX (.inl j) = w₆) (e11 : w₆ + (RD₁.prod RD₂).iX (.inl c) = w₂)
    (e12 : w₆ + (RD₁.prod RD₂).iX (.inr i) = w₅) :
    braidEq (homProduct k W T) (Sum.inr i) (Sum.inl j) (Sum.inl c)
      e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 := by
  obtain ⟨l₁, l₂⟩ := l
  obtain ⟨p₁, p₂⟩ := w₁
  obtain ⟨q₁, q₂⟩ := w₂
  obtain ⟨r₁, r₂⟩ := w₃
  obtain ⟨s₁, s₂⟩ := w₄
  obtain ⟨t₁, t₂⟩ := w₅
  obtain ⟨u₁, u₂⟩ := w₆
  obtain ⟨m₁, m₂⟩ := m
  subst_weights e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  apply ObjectProperty.hom_ext
  ext X
  exact mixedBraid_RLL (T.E i (neg_reg i (snd_step' i e3))) X (W.E c (fst_step' c e7))
    (W.E j (fst_step' j e5)) (W.E j (fst_step' j e8)) (W.E c (fst_step' c e9))
    (W.cross j c (fst_step' c e7) (fst_step' j e5) (fst_step' j e8) (fst_step' c e9))

variable (W T) in
theorem homProduct_braid_RLR
    (i : I₂) (j : I₁) (c : I₂)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X₁ × X₂} (e1 : l + (RD₁.prod RD₂).iX (.inr c) = w₁)
    (e2 : w₁ + (RD₁.prod RD₂).iX (.inl j) = w₂) (e3 : w₂ + (RD₁.prod RD₂).iX (.inr i) = m)
    (e4 : w₁ + (RD₁.prod RD₂).iX (.inr i) = w₃) (e5 : w₃ + (RD₁.prod RD₂).iX (.inl j) = m)
    (e6 : l + (RD₁.prod RD₂).iX (.inr i) = w₄) (e7 : w₄ + (RD₁.prod RD₂).iX (.inr c) = w₃)
    (e8 : w₄ + (RD₁.prod RD₂).iX (.inl j) = w₅) (e9 : w₅ + (RD₁.prod RD₂).iX (.inr c) = m)
    (e10 : l + (RD₁.prod RD₂).iX (.inl j) = w₆) (e11 : w₆ + (RD₁.prod RD₂).iX (.inr c) = w₂)
    (e12 : w₆ + (RD₁.prod RD₂).iX (.inr i) = w₅) :
    braidEq (homProduct k W T) (Sum.inr i) (Sum.inl j) (Sum.inr c)
      e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 := by
  obtain ⟨l₁, l₂⟩ := l
  obtain ⟨p₁, p₂⟩ := w₁
  obtain ⟨q₁, q₂⟩ := w₂
  obtain ⟨r₁, r₂⟩ := w₃
  obtain ⟨s₁, s₂⟩ := w₄
  obtain ⟨t₁, t₂⟩ := w₅
  obtain ⟨u₁, u₂⟩ := w₆
  obtain ⟨m₁, m₂⟩ := m
  subst_weights e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  apply ObjectProperty.hom_ext
  ext X
  exact mixedBraid_RLR (T.E i (neg_reg i (snd_step' i e4))) (T.E c (neg_reg c
    (snd_step' c e1))) (T.E c (neg_reg c (snd_step' c e7))) (T.E i
    (neg_reg i (snd_step' i e6))) X (W.E j (fst_step' j e2))
    (T.reverse.cross i c (snd_step' c e1) (snd_step' i e4) (snd_step' i e6) (snd_step' c e7))

variable (W T) in
theorem homProduct_braid_RRL
    (i : I₂) (j : I₂) (c : I₁) 
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X₁ × X₂} (e1 : l + (RD₁.prod RD₂).iX (.inl c) = w₁)
    (e2 : w₁ + (RD₁.prod RD₂).iX (.inr j) = w₂) (e3 : w₂ + (RD₁.prod RD₂).iX (.inr i) = m)
    (e4 : w₁ + (RD₁.prod RD₂).iX (.inr i) = w₃) (e5 : w₃ + (RD₁.prod RD₂).iX (.inr j) = m)
    (e6 : l + (RD₁.prod RD₂).iX (.inr i) = w₄) (e7 : w₄ + (RD₁.prod RD₂).iX (.inl c) = w₃)
    (e8 : w₄ + (RD₁.prod RD₂).iX (.inr j) = w₅) (e9 : w₅ + (RD₁.prod RD₂).iX (.inl c) = m)
    (e10 : l + (RD₁.prod RD₂).iX (.inr j) = w₆) (e11 : w₆ + (RD₁.prod RD₂).iX (.inl c) = w₂)
    (e12 : w₆ + (RD₁.prod RD₂).iX (.inr i) = w₅) :
    braidEq (homProduct k W T) (Sum.inr i) (Sum.inr j) (Sum.inl c)
      e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 := by
  obtain ⟨l₁, l₂⟩ := l
  obtain ⟨p₁, p₂⟩ := w₁
  obtain ⟨q₁, q₂⟩ := w₂
  obtain ⟨r₁, r₂⟩ := w₃
  obtain ⟨s₁, s₂⟩ := w₄
  obtain ⟨t₁, t₂⟩ := w₅
  obtain ⟨u₁, u₂⟩ := w₆
  obtain ⟨m₁, m₂⟩ := m
  subst_weights e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  apply ObjectProperty.hom_ext
  ext X
  exact mixedBraid_RRL (T.E i (neg_reg i (snd_step' i e3))) (T.E j (neg_reg j
    (snd_step' j e2))) (T.E j (neg_reg j (snd_step' j e5))) (T.E i
    (neg_reg i (snd_step' i e4))) X (W.E c (fst_step' c e1))
    (T.reverse.cross i j (snd_step' j e2) (snd_step' i e3) (snd_step' i e4) (snd_step' j e5))

variable (W T) in
theorem homProduct_braid_RRR
    {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k} (H₂ : RouqUpKLR T Q₂)
    (hQ₂ : KLR.KLRSymm Q₂) (i : I₂) (j : I₂) (c : I₂) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X₁ × X₂} (e1 : l + (RD₁.prod RD₂).iX (.inr c) = w₁)
    (e2 : w₁ + (RD₁.prod RD₂).iX (.inr j) = w₂) (e3 : w₂ + (RD₁.prod RD₂).iX (.inr i) = m)
    (e4 : w₁ + (RD₁.prod RD₂).iX (.inr i) = w₃) (e5 : w₃ + (RD₁.prod RD₂).iX (.inr j) = m)
    (e6 : l + (RD₁.prod RD₂).iX (.inr i) = w₄) (e7 : w₄ + (RD₁.prod RD₂).iX (.inr c) = w₃)
    (e8 : w₄ + (RD₁.prod RD₂).iX (.inr j) = w₅) (e9 : w₅ + (RD₁.prod RD₂).iX (.inr c) = m)
    (e10 : l + (RD₁.prod RD₂).iX (.inr j) = w₆) (e11 : w₆ + (RD₁.prod RD₂).iX (.inr c) = w₂)
    (e12 : w₆ + (RD₁.prod RD₂).iX (.inr i) = w₅) :
    braidEq (homProduct k W T) (Sum.inr i) (Sum.inr j) (Sum.inr c)
      e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 := by
  obtain ⟨l₁, l₂⟩ := l
  obtain ⟨p₁, p₂⟩ := w₁
  obtain ⟨q₁, q₂⟩ := w₂
  obtain ⟨r₁, r₂⟩ := w₃
  obtain ⟨s₁, s₂⟩ := w₄
  obtain ⟨t₁, t₂⟩ := w₅
  obtain ⟨u₁, u₂⟩ := w₆
  obtain ⟨m₁, m₂⟩ := m
  subst_weights e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  exact (yoneda_upKLR T.reverse (HOp.mk (W.obj l₁))
    (T.reverse_upKLR Q₂ hQ₂ H₂)).braid i j c hb
    (snd_step' c e1) (snd_step' j e2) (snd_step' i e3)
    (snd_step' i e4) (snd_step' j e5) (snd_step' i e6)
    (snd_step' c e7) (snd_step' j e8) (snd_step' c e9)
    (snd_step' j e10) (snd_step' c e11) (snd_step' i e12)

variable (W T) in
theorem homProduct_braid {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k}
    {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k} (H₁ : RouqUpKLR W Q₁) (H₂ : RouqUpKLR T Q₂)
    (hQ₂ : KLR.KLRSymm Q₂) (i j c : I₁ ⊕ I₂) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X₁ × X₂} (e1 : l + (RD₁.prod RD₂).iX c = w₁)
    (e2 : w₁ + (RD₁.prod RD₂).iX j = w₂) (e3 : w₂ + (RD₁.prod RD₂).iX i = m)
    (e4 : w₁ + (RD₁.prod RD₂).iX i = w₃) (e5 : w₃ + (RD₁.prod RD₂).iX j = m)
    (e6 : l + (RD₁.prod RD₂).iX i = w₄) (e7 : w₄ + (RD₁.prod RD₂).iX c = w₃)
    (e8 : w₄ + (RD₁.prod RD₂).iX j = w₅) (e9 : w₅ + (RD₁.prod RD₂).iX c = m)
    (e10 : l + (RD₁.prod RD₂).iX j = w₆) (e11 : w₆ + (RD₁.prod RD₂).iX c = w₂)
    (e12 : w₆ + (RD₁.prod RD₂).iX i = w₅) :
    braidEq (homProduct k W T) i j c e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 := by
  rcases i with i | i <;> rcases j with j | j <;> rcases c with c | c
  · exact homProduct_braid_LLL W T H₁ i j c (fun h => hb (congrArg _ h)) _ _ _ _ _ _ _ _ _ _ _ _
  · exact homProduct_braid_LLR W T i j c _ _ _ _ _ _ _ _ _ _ _ _
  · exact homProduct_braid_LRL W T i j c _ _ _ _ _ _ _ _ _ _ _ _
  · exact homProduct_braid_LRR W T i j c _ _ _ _ _ _ _ _ _ _ _ _
  · exact homProduct_braid_RLL W T i j c _ _ _ _ _ _ _ _ _ _ _ _
  · exact homProduct_braid_RLR W T i j c _ _ _ _ _ _ _ _ _ _ _ _
  · exact homProduct_braid_RRL W T i j c _ _ _ _ _ _ _ _ _ _ _ _
  · exact homProduct_braid_RRR W T H₂ hQ₂ i j c (fun h => hb (congrArg _ h)) _ _ _ _ _ _ _ _ _ _ _ _

variable (W T) in
theorem homProduct_braidQ {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k}
    {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k} (H₁ : RouqUpKLR W Q₁) (H₂ : RouqUpKLR T Q₂)
    (hQ₂ : KLR.KLRSymm Q₂) (i j : I₁ ⊕ I₂) (hij : i ≠ j) {a b c d e f : X₁ × X₂}
    (h₁ : a + (RD₁.prod RD₂).iX i = b) (h₂ : b + (RD₁.prod RD₂).iX j = c)
    (h₃ : c + (RD₁.prod RD₂).iX i = f) (h₄ : b + (RD₁.prod RD₂).iX i = d)
    (h₅ : d + (RD₁.prod RD₂).iX j = f) (h₆ : a + (RD₁.prod RD₂).iX j = e)
    (h₇ : e + (RD₁.prod RD₂).iX i = c) :
    let S := homProduct k W T
    (S.E i h₁ ◁ S.cross i j h₂ h₃ h₄ h₅ ≫
      ((α_ (S.E i h₁) (S.E i h₄) (S.E j h₅)).inv ≫
        S.cross i i h₁ h₄ h₁ h₄ ▷ S.E j h₅ ≫
        (α_ (S.E i h₁) (S.E i h₄) (S.E j h₅)).hom) ≫
      S.E i h₁ ◁ S.cross j i h₄ h₅ h₂ h₃) -
    (((α_ (S.E i h₁) (S.E j h₂) (S.E i h₃)).inv ≫
      S.cross j i h₁ h₂ h₆ h₇ ▷ S.E i h₃ ≫
      (α_ (S.E j h₆) (S.E i h₇) (S.E i h₃)).hom) ≫
      S.E j h₆ ◁ S.cross i i h₇ h₃ h₇ h₃ ≫
      ((α_ (S.E j h₆) (S.E i h₇) (S.E i h₃)).inv ≫
        S.cross i j h₆ h₇ h₁ h₂ ▷ S.E i h₃ ≫
        (α_ (S.E i h₁) (S.E j h₂) (S.E i h₃)).hom)) =
      KLR.ncEval (A := End (S.E i h₁ ≫ (S.E j h₂ ≫ S.E i h₃)))
        ![S.E i h₁ ◁ (S.E j h₂ ◁ S.dot i h₃),
          S.E i h₁ ◁ (S.dot j h₂ ▷ S.E i h₃),
          S.dot i h₁ ▷ (S.E j h₂ ≫ S.E i h₃)] (KLR.qbar (prodQ Q₁ Q₂ i j)) := by
  intro S
  rcases i with i | i <;> rcases j with j | j
  · obtain ⟨a₁, a₂⟩ := a
    obtain ⟨b₁, b₂⟩ := b
    obtain ⟨c₁, c₂⟩ := c
    obtain ⟨d₁, d₂⟩ := d
    obtain ⟨e₁, e₂⟩ := e
    obtain ⟨f₁, f₂⟩ := f
    subst_weights h₁ h₂ h₃ h₄ h₅ h₆ h₇
    exact (yoneda_upKLR W (T.obj (-a₂)) H₁).braidQ i j (fun h => hij (congrArg _ h))
      (fst_step' i h₁) (fst_step' j h₂) (fst_step' i h₃) (fst_step' i h₄) (fst_step' j h₅)
      (fst_step' j h₆) (fst_step' i h₇)
  · rw [show prodQ Q₁ Q₂ (.inl i) (.inr j) = 1 from rfl, KLR.qbar_one, ncEval_zero_eq,
      sub_eq_zero]
    exact homProduct_braid_LRL W T i j i h₁ h₂ h₃ h₄ h₅ h₁ h₄ h₂ h₃ h₆ h₇ h₇
  · rw [show prodQ Q₁ Q₂ (.inr i) (.inl j) = 1 from rfl, KLR.qbar_one, ncEval_zero_eq,
      sub_eq_zero]
    exact homProduct_braid_RLR W T i j i h₁ h₂ h₃ h₄ h₅ h₁ h₄ h₂ h₃ h₆ h₇ h₇
  · obtain ⟨a₁, a₂⟩ := a
    obtain ⟨b₁, b₂⟩ := b
    obtain ⟨c₁, c₂⟩ := c
    obtain ⟨d₁, d₂⟩ := d
    obtain ⟨e₁, e₂⟩ := e
    obtain ⟨f₁, f₂⟩ := f
    subst_weights h₁ h₂ h₃ h₄ h₅ h₆ h₇
    exact (yoneda_upKLR T.reverse (HOp.mk (W.obj a₁)) (T.reverse_upKLR Q₂ hQ₂ H₂)).braidQ i j
      (fun h => hij (congrArg _ h))
      (snd_step' i h₁) (snd_step' j h₂) (snd_step' i h₃) (snd_step' i h₄) (snd_step' j h₅)
      (snd_step' j h₆) (snd_step' i h₇)

variable (W T) in
/-- **The mixed upward KLR relations on `Hom_B(T(-x₂), W(x₁))`** (Brundan (1.2)–(1.4)), for
the parameters of `W` and `T` on their colours and `1` between colours of different sides. The
parameters of `T` satisfy `Q_ji(u, v) = Q_ij(v, u)`, as needed for the reverse of `T`
(`RouqFamily.reverse_upKLR`). -/
theorem homProduct_upKLR {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k}
    {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k} (H₁ : RouqUpKLR W Q₁) (H₂ : RouqUpKLR T Q₂)
    (hQ₂ : KLR.KLRSymm Q₂) : RouqUpKLR (homProduct k W T) (prodQ Q₁ Q₂) where
  square := by
    rintro (i | i) (j | j) hij ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ h₁ h₂ h₃ h₄
    all_goals subst_weights h₁ h₂ h₃ h₄
    · exact (yoneda_upKLR W (T.obj (-a₂)) H₁).square i j (fun h => hij (congrArg _ h))
        (fst_step' j h₁) (fst_step' i h₂)
        (fst_step' i h₃) (fst_step' j h₄)
    · rw [show prodQ Q₁ Q₂ (.inl i) (.inr j) = 1 from rfl, ncEval_one_eq]
      apply ObjectProperty.hom_ext
      ext X
      exact Iso.hom_inv_id (α_ _ _ _)
    · rw [show prodQ Q₁ Q₂ (.inr i) (.inl j) = 1 from rfl, ncEval_one_eq]
      apply ObjectProperty.hom_ext
      ext X
      exact Iso.inv_hom_id (α_ _ _ _)
    · exact (yoneda_upKLR T.reverse (HOp.mk (W.obj a₁)) (T.reverse_upKLR Q₂ hQ₂ H₂)).square
        i j (fun h => hij (congrArg _ h))
        (snd_step' j h₁) (snd_step' i h₂)
        (snd_step' i h₃) (snd_step' j h₄)
  slide_left := by
    rintro (i | i) (j | j) hij ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ h₁ h₂ h₃ h₄
    all_goals subst_weights h₁ h₂ h₃ h₄
    · exact (yoneda_upKLR W (T.obj (-a₂)) H₁).slide_left i j (fun h => hij (congrArg _ h))
        (fst_step' j h₁) (fst_step' i h₂)
        (fst_step' i h₃) (fst_step' j h₄)
    · apply ObjectProperty.hom_ext
      ext X
      exact associator_naturality_right _ _ _
    · apply ObjectProperty.hom_ext
      ext X
      exact associator_inv_naturality_left _ _ _
    · exact (yoneda_upKLR T.reverse (HOp.mk (W.obj a₁))
        (T.reverse_upKLR Q₂ hQ₂ H₂)).slide_left i j (fun h => hij (congrArg _ h))
        (snd_step' j h₁) (snd_step' i h₂)
        (snd_step' i h₃) (snd_step' j h₄)
  slide_right := by
    rintro (i | i) (j | j) hij ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ h₁ h₂ h₃ h₄
    all_goals subst_weights h₁ h₂ h₃ h₄
    · exact (yoneda_upKLR W (T.obj (-a₂)) H₁).slide_right i j (fun h => hij (congrArg _ h))
        (fst_step' j h₁) (fst_step' i h₂)
        (fst_step' i h₃) (fst_step' j h₄)
    · apply ObjectProperty.hom_ext
      ext X
      exact associator_naturality_left _ _ _
    · apply ObjectProperty.hom_ext
      ext X
      exact associator_inv_naturality_right _ _ _
    · exact (yoneda_upKLR T.reverse (HOp.mk (W.obj a₁))
        (T.reverse_upKLR Q₂ hQ₂ H₂)).slide_right i j (fun h => hij (congrArg _ h))
        (snd_step' j h₁) (snd_step' i h₂)
        (snd_step' i h₃) (snd_step' j h₄)
  braid := homProduct_braid W T H₁ H₂ hQ₂
  braidQ := homProduct_braidQ W T H₁ H₂ hQ₂

/-- The mixed sideways crossing of a `W` colour past a `T` colour is the associator
`t ≫ (X ≫ f) ≅ (t ≫ X) ≫ f`. -/
theorem homProduct_mixedSigma_inl_inr (a : I₁) (b : I₂) {x₁ y₁ : X₁} {x₂ y₂ : X₂}
    (hj : (x₁, x₂) + (RD₁.prod RD₂).iX (.inr b) = (x₁, y₂))
    (hi' : (x₁, y₂) + (RD₁.prod RD₂).iX (.inl a) = (y₁, y₂))
    (hi : (x₁, x₂) + (RD₁.prod RD₂).iX (.inl a) = (y₁, x₂))
    (hj' : (y₁, x₂) + (RD₁.prod RD₂).iX (.inr b) = (y₁, y₂)) :
    (homProduct k W T).mixedSigma (.inl a) (.inr b) hj hi' hi hj' =
      ObjectProperty.homMk (associatorNatIsoMiddle (T.E b (neg_reg b (snd_step' b hj)))
        (W.F a (fst_step' a hi))).inv := by
  apply ObjectProperty.hom_ext
  ext X
  simp only [RouqFamily.mixedSigma, Bicategory.mateEquiv_apply, Adjunction.homEquiv₁_apply,
    Adjunction.homEquiv₂_apply]
  exact mixedMate_LR (T.E b (neg_reg b (snd_step' b hj))) X (W.adj a (fst_step' a hi))

/-- The mixed sideways crossing of a `T` colour past a `W` colour is the associator
`(f ≫ X) ≫ w ≅ f ≫ (X ≫ w)`. -/
theorem homProduct_mixedSigma_inr_inl (a : I₂) (b : I₁) {x₁ y₁ : X₁} {x₂ y₂ : X₂}
    (hj : (x₁, x₂) + (RD₁.prod RD₂).iX (.inl b) = (y₁, x₂))
    (hi' : (y₁, x₂) + (RD₁.prod RD₂).iX (.inr a) = (y₁, y₂))
    (hi : (x₁, x₂) + (RD₁.prod RD₂).iX (.inr a) = (x₁, y₂))
    (hj' : (x₁, y₂) + (RD₁.prod RD₂).iX (.inl b) = (y₁, y₂)) :
    (homProduct k W T).mixedSigma (.inr a) (.inl b) hj hi' hi hj' =
      ObjectProperty.homMk (associatorNatIsoMiddle (T.F a (neg_reg a (snd_step' a hi)))
        (W.E b (fst_step' b hj))).hom := by
  apply ObjectProperty.hom_ext
  ext X
  simp only [RouqFamily.mixedSigma, Bicategory.mateEquiv_apply, Adjunction.homEquiv₁_apply,
    Adjunction.homEquiv₂_apply]
  exact mixedMate_RL (T.adjL a (neg_reg a (snd_step' a hi))) X (W.E b (fst_step' b hj))

variable (W T) in
/-- **Brundan's mixed inversion (1.7) on `Hom_B(T(-x₂), W(x₁))`**: for two colours of one side
it is that of `W`, or of the reverse of `T` (from Brundan's scalars for `T`); for colours of
different sides the mixed sideways crossing is an associator. -/
theorem homProduct_mixedInversion (M₁ : BrundanMixedInversion W)
    (Sc : KL3.Diagram.CL.CLScalars C₂ k) (H₂ : BrundanUpKLR T Sc)
    (M₂ : BrundanMixedInversion T) : BrundanMixedInversion (homProduct k W T) := by
  rintro (i | i) (j | j) hij ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ hj hi' hi hj'
  all_goals subst_weights hj hi' hi hj'
  · exact yoneda_mixedInversion (k := k) W (T.obj (-a₂)) M₁ i j (fun h => hij (congrArg _ h))
      (fst_step' j hj) (fst_step' i hi') (fst_step' i hi) (fst_step' j hj')
  · rw [homProduct_mixedSigma_inl_inr]
    exact ⟨ObjectProperty.homMk (associatorNatIsoMiddle _ _).hom,
      ObjectProperty.hom_ext _ (Iso.inv_hom_id _), ObjectProperty.hom_ext _ (Iso.hom_inv_id _)⟩
  · rw [homProduct_mixedSigma_inr_inl]
    exact ⟨ObjectProperty.homMk (associatorNatIsoMiddle _ _).inv,
      ObjectProperty.hom_ext _ (Iso.hom_inv_id _), ObjectProperty.hom_ext _ (Iso.inv_hom_id _)⟩
  · exact yoneda_mixedInversion (k := k) T.reverse (HOp.mk (W.obj a₁))
      (T.reverse_mixedInversion Sc H₂ M₂) i j (fun h => hij (congrArg _ h))
      (snd_step' j hj) (snd_step' i hi') (snd_step' i hi) (snd_step' j hj')

end Relations

end RouqFamily

end Categorification.TwoRep
