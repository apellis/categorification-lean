/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqProductKLR
import Categorification.TwoRep.FurlingIntertwine
import Categorification.KLR.Reindex

/-!
# The left colours of a product family

Let `W`, `T` be Rouquier families for root data `RD₁`, `RD₂` and let
`P = RouqFamily.homProduct W T` be the Rouquier family on `Hom_B(T(-x₂), W(x₁))` for the product
root datum. On words all of whose letters are colours of `RD₁` (the labels `Ĩ₋` of B. Webster,
*Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of Theorem
`nondegenerate`), the second weight `x₂` does not change, and `P` acts as the family
`leftFamily x₂ = W.yoneda (T(-x₂))` of postcomposition with `W`.

This file proves the comparison on words and on the action of the KLR algebra: for
`r ∈ R_{Q₁}(ν)`, the action of the reindexed element `r ∈ R_{prodQ Q₁ Q₂}(ν.map inl)`
(`KLR.KLRAlgebra.reindexEquiv`) on the words of `P` with letters `inl t`, conjugated along the
identification of the words, is the action of `r` on the words of `leftFamily x₂`
(`klrActAt_reindex_inl`).

## Main declarations

* `RouqFamily.inlWord`: the weighted word of the product with the letters of a weighted word of
  `RD₁`, at the second weight `μ₂`;
* `RouqFamily.wcell_inlWord`, `wdot_inlWord'`, `wcrossTo_inlWord'`: the words, dots and
  crossings of `P` on these words are those of `leftFamily μ₂`;
* `KLR.Diagram.MatEnd.conjAlg`: conjugation of matrix algebras along a bijection of the indices
  and identifications of the objects;
* `RouqFamily.leftCast`: the identification of the hom categories of `P` and of `leftFamily μ₂`;
* `RouqFamily.klrActAt_reindex_inl`: the action of the KLR algebra.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w' w v u u₁

namespace RouqFamily

open QuantumGroup UDot KLR

section Words

variable {k : Type w'} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  {I₁ I₂ : Type*} {C₁ : CartanDatum I₁} {C₂ : CartanDatum I₂}
  {X₁ Y₁ X₂ Y₂ : Type u₁} [AddCommGroup X₁] [AddCommGroup Y₁] [AddCommGroup X₂]
  [AddCommGroup Y₂] {RD₁ : WeightDatum C₁ X₁ Y₁} {RD₂ : WeightDatum C₂ X₂ Y₂}
  {W : RouqFamily (B := B) RD₁} {T : RouqFamily (B := B) RD₂}

/-- The weighted word of the product root datum with the letters `inl c` of a weighted word of
`RD₁`, at the second weight `μ₂`. -/
def inlWord (μ₂ : X₂) (L : List (I₁ × X₁)) : List ((I₁ ⊕ I₂) × (X₁ × X₂)) :=
  L.map fun p => (Sum.inl p.1, (p.2, μ₂))

omit [AddCommGroup X₁] [AddCommGroup X₂] in
@[simp] theorem inlWord_nil (μ₂ : X₂) : inlWord (I₂ := I₂) μ₂ ([] : List (I₁ × X₁)) = [] := rfl

omit [AddCommGroup X₁] [AddCommGroup X₂] in
@[simp] theorem inlWord_cons (μ₂ : X₂) (c : I₁) (ν : X₁) (L : List (I₁ × X₁)) :
    inlWord (I₂ := I₂) μ₂ ((c, ν) :: L) = (Sum.inl c, (ν, μ₂)) :: inlWord μ₂ L := rfl

theorem inl_step (c : I₁) {ν μ' : X₁} (μ₂ : X₂) (h : ν + RD₁.iX c = μ') :
    (ν, μ₂) + (RD₁.prod RD₂).iX (.inl c) = (μ', μ₂) :=
  Prod.ext (by simp [← h]) (by simp)

theorem wValid_inlWord (μ₂ : X₂) : ∀ (L : List (I₁ × X₁)) {μ₁ μ' : X₁},
    wValid RD₁ μ₁ L μ' → wValid (RD₁.prod RD₂) (μ₁, μ₂) (inlWord μ₂ L) (μ', μ₂)
  | [], _, _, h => by subst h; rfl
  | (c, _) :: L, _, _, h => ⟨wValid_inlWord μ₂ L h.1, inl_step c μ₂ h.2⟩

theorem inlWord_wswap (μ₂ : X₂) : ∀ (j : ℕ) (L : List (I₁ × X₁)),
    wswap (RD₁.prod RD₂) j (inlWord μ₂ L) = inlWord μ₂ (wswap RD₁ j L)
  | 0, (c, ν₁) :: (d, ν₂) :: L => by
    simp only [inlWord_cons, wswap, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    exact Prod.ext (by simp) (by simp)
  | j + 1, (c, ν) :: L => by
    simp only [inlWord_cons, wswap, List.cons.injEq, true_and]
    exact inlWord_wswap μ₂ j L
  | 0, [] => rfl
  | 0, [_] => rfl
  | _ + 1, [] => rfl

theorem ctop_map_inl (μ₁ : X₁) (μ₂ : X₂) : ∀ l : List I₁,
    ctop (RD₁.prod RD₂) (μ₁, μ₂) (l.map Sum.inl) = (ctop RD₁ μ₁ l, μ₂)
  | [] => rfl
  | c :: l => by
    rw [List.map_cons, ctop, ctop_map_inl μ₁ μ₂ l, ctop]
    exact Prod.ext (by simp) (by simp)

theorem canon_map_inl (μ₁ : X₁) (μ₂ : X₂) : ∀ l : List I₁,
    canon (RD₁.prod RD₂) (μ₁, μ₂) (l.map Sum.inl) = inlWord μ₂ (canon RD₁ μ₁ l)
  | [] => rfl
  | c :: l => by
    rw [List.map_cons, canon, canon, inlWord_cons, ctop_map_inl, canon_map_inl μ₁ μ₂ l]

theorem word_map_inl {ν : Multiset I₁} (t : Seq ν) :
    Diagram.word (Seq.map (Sum.inl (β := I₂)) t) = (Diagram.word t).map Sum.inl := by
  unfold Diagram.word
  rw [List.map_ofFn]
  exact List.ofFn_congr (Multiset.card_map _ ν) _

theorem wordL_map_inl (μ₁ : X₁) (μ₂ : X₂) {ν : Multiset I₁} (t : Seq ν) :
    wordL (RD₁.prod RD₂) (μ₁, μ₂) (Seq.map Sum.inl t) = inlWord μ₂ (wordL RD₁ μ₁ t) := by
  unfold wordL
  rw [word_map_inl, canon_map_inl]

theorem wtop_map_inl (μ₁ : X₁) (μ₂ : X₂) (ν : Multiset I₁) :
    wtop (RD₁.prod RD₂) (μ₁, μ₂) (ν.map Sum.inl) = (wtop RD₁ μ₁ ν, μ₂) := by
  unfold wtop
  rw [Multiset.map_map]
  have hs : ∀ ν : Multiset I₁, (Multiset.map ((RD₁.prod RD₂).iX ∘ Sum.inl) ν).sum =
      ((Multiset.map RD₁.iX ν).sum, (0 : X₂)) := by
    intro ν
    induction ν using Multiset.induction_on with
    | empty => rfl
    | cons a ν ih => rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.sum_cons, ih]; exact Prod.ext (by simp) (by simp)
  rw [hs]
  exact Prod.ext rfl (add_zero μ₂)

variable (W T)

/-- The words of the product on letters of `RD₁` are the words of `leftFamily μ₂`; the word of
the product is given as any list equal to `inlWord μ₂ L`. -/
theorem wcell_inlWord' (μ₂ : X₂) : ∀ (L : List (I₁ × X₁)) (L' : List ((I₁ ⊕ I₂) × (X₁ × X₂)))
    (_ : inlWord μ₂ L = L') {μ₁ μ' : X₁}
    (h : wValid RD₁ μ₁ L μ') (h' : wValid (RD₁.prod RD₂) (μ₁, μ₂) L' (μ', μ₂)),
    (homProduct k W T).wcell (μ₁, μ₂) L' (μ', μ₂) h' = (leftFamily k W T μ₂).wcell μ₁ L μ' h
  | [], _, hL, _, _, h, _ => by subst hL; subst h; rfl
  | (c, ν) :: L, _, hL, μ₁, _, h, h' => by
    rw [inlWord_cons] at hL
    subst hL
    change (homProduct k W T).wcell (μ₁, μ₂) (inlWord μ₂ L) (ν, μ₂) h'.1 ≫
        (homProduct k W T).E (.inl c) h'.2 = (leftFamily k W T μ₂).wcell μ₁ L ν h.1 ≫ _
    rw [wcell_inlWord' μ₂ L _ rfl h.1 h'.1]
    rfl

/-- The words of the product on letters of `RD₁` are the words of `leftFamily μ₂`. -/
theorem wcell_inlWord (μ₂ : X₂) (L : List (I₁ × X₁)) {μ₁ μ' : X₁}
    (h : wValid RD₁ μ₁ L μ') (h' : wValid (RD₁.prod RD₂) (μ₁, μ₂) (inlWord μ₂ L) (μ', μ₂)) :
    (homProduct k W T).wcell (μ₁, μ₂) (inlWord μ₂ L) (μ', μ₂) h' =
      (leftFamily k W T μ₂).wcell μ₁ L μ' h :=
  wcell_inlWord' W T μ₂ L _ rfl h h'

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem whiskerLeft_eq_eqToHom {a b c : B} {f g : a ⟶ b} (e : f = g) {h h' : b ⟶ c}
    (D : h ⟶ h') :
    f ◁ D = eqToHom (congrArg (· ≫ h) e) ≫ g ◁ D ≫ eqToHom (congrArg (· ≫ h') e).symm := by
  subst e; simp

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem associator_whiskerLeft_eq_eqToHom {a b c c' d : B} {f g : a ⟶ b} (e : f = g)
    {p : b ⟶ c} {q : c ⟶ d} {p' : b ⟶ c'} {q' : c' ⟶ d} (D : p ≫ q ⟶ p' ≫ q') :
    (α_ f p q).hom ≫ f ◁ D ≫ (α_ f p' q').inv =
      eqToHom (congrArg (fun x => (x ≫ p) ≫ q) e) ≫
        ((α_ g p q).hom ≫ g ◁ D ≫ (α_ g p' q').inv) ≫
          eqToHom (congrArg (fun x => (x ≫ p') ≫ q') e).symm := by
  subst e; simp

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem eqToHom_conj_whiskerRight {a b c : B} {f f' g g' : a ⟶ b} (p : f = f') (X : f' ⟶ g')
    (q : g' = g) (h : b ⟶ c) :
    (eqToHom p ≫ X ≫ eqToHom q) ▷ h =
      eqToHom (congrArg (· ≫ h) p) ≫ X ▷ h ≫ eqToHom (congrArg (· ≫ h) q) := by
  subst p q; simp

theorem eqToHom_conj_conj {𝒞 : Type*} [Category 𝒞] {A A' Z Z' : 𝒞} (p : A = A') (q : A' = A)
    (X : A ⟶ Z) (r : Z = Z') (s : Z' = Z) :
    eqToHom p ≫ (eqToHom q ≫ X ≫ eqToHom r) ≫ eqToHom s = X := by
  subst p r; simp

theorem eqToHom_conj_conj' {𝒞 : Type*} [Category 𝒞] {A A' Z Z' Z₂ Z₃ : 𝒞} (p : A = A')
    (q : A' = A) (X : A ⟶ Z) (r : Z = Z') (s : Z' = Z₂) (s' : Z₂ = Z₃) (t : Z = Z₃) :
    eqToHom p ≫ (eqToHom q ≫ X ≫ eqToHom r) ≫ eqToHom s ≫ eqToHom s' = X ≫ eqToHom t := by
  subst p r s s'; simp

theorem eqToHom_id_eqToHom {𝒞 : Type*} [Category 𝒞] {A Z : 𝒞} (p : A = Z) (q : Z = A) :
    eqToHom p ≫ 𝟙 Z ≫ eqToHom q = 𝟙 A := by
  subst p; simp

theorem eqToHom_zero_eqToHom {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {A A' Z Z' Z'' : 𝒞}
    (p : A = A') (q : Z' = Z) (r : Z = Z'') :
    eqToHom p ≫ (0 : A' ⟶ Z') ≫ eqToHom q ≫ eqToHom r = 0 := by
  simp

theorem zero_eq_eqToHom_zero {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {A A' Z Z' : 𝒞}
    (p : A = A') (q : Z' = Z) : (0 : A ⟶ Z) = eqToHom p ≫ (0 : A' ⟶ Z') ≫ eqToHom q := by
  simp

/-- The dots of the product on letters of `RD₁` are those of `leftFamily μ₂`. -/
theorem wdot_inlWord' (μ₂ : X₂) : ∀ (a : ℕ) (L : List (I₁ × X₁))
    (L' : List ((I₁ ⊕ I₂) × (X₁ × X₂))) (hL : inlWord μ₂ L = L') {μ₁ μ' : X₁}
    (h : wValid RD₁ μ₁ L μ') (h' : wValid (RD₁.prod RD₂) (μ₁, μ₂) L' (μ', μ₂)),
    (homProduct k W T).wdot (μ₁, μ₂) a L' (μ', μ₂) h' =
      eqToHom (wcell_inlWord' W T μ₂ L L' hL h h') ≫ (leftFamily k W T μ₂).wdot μ₁ a L μ' h ≫
        eqToHom (wcell_inlWord' W T μ₂ L L' hL h h').symm
  | 0, (c, ν) :: L, _, hL, μ₁, _, h, h' => by
    rw [inlWord_cons] at hL
    subst hL
    exact whiskerLeft_eq_eqToHom (wcell_inlWord W T μ₂ L h.1 h'.1)
      ((leftFamily k W T μ₂).dot c h.2)
  | a + 1, (c, ν) :: L, _, hL, μ₁, _, h, h' => by
    rw [inlWord_cons] at hL
    subst hL
    change (homProduct k W T).wdot (μ₁, μ₂) a (inlWord μ₂ L) (ν, μ₂) h'.1 ▷
      (homProduct k W T).E (.inl c) h'.2 = _
    exact (congrArg (· ▷ _) (wdot_inlWord' μ₂ a L _ rfl h.1 h'.1)).trans
      (eqToHom_conj_whiskerRight _ _ _ _)
  | 0, [], _, hL, _, _, _, _ => by
    rw [inlWord_nil] at hL
    subst hL
    exact zero_eq_eqToHom_zero _ _
  | _ + 1, [], _, hL, _, _, _, _ => by
    rw [inlWord_nil] at hL
    subst hL
    exact zero_eq_eqToHom_zero _ _

/-- The crossings of the product on letters of `RD₁` are those of `leftFamily μ₂`. -/
theorem wcrossTo_inlWord' (μ₂ : X₂) : ∀ (j : ℕ) (L : List (I₁ × X₁))
    (L' M' : List ((I₁ ⊕ I₂) × (X₁ × X₂))) (hL : inlWord μ₂ L = L')
    (hM : inlWord μ₂ (wswap RD₁ j L) = M') {μ₁ μ' : X₁}
    (h : wValid RD₁ μ₁ L μ') (h' : wValid (RD₁.prod RD₂) (μ₁, μ₂) L' (μ', μ₂))
    (hM' : wValid (RD₁.prod RD₂) (μ₁, μ₂) M' (μ', μ₂))
    (e' : wswap (RD₁.prod RD₂) j L' = M'),
    (homProduct k W T).wcrossTo (μ₁, μ₂) j L' M' (μ', μ₂) e' h' hM' =
      eqToHom (wcell_inlWord' W T μ₂ L L' hL h h') ≫ (leftFamily k W T μ₂).wcross μ₁ j L μ' h ≫
        eqToHom (wcell_inlWord' W T μ₂ _ M' hM (wValid_wswap j L h) hM').symm
  | 0, (c, ν₁) :: (d, ν₂) :: R, _, _, hL, hM, μ₁, μ', h, h', hM', e' => by
    simp only [inlWord_cons, wswap] at hL hM
    subst hL hM
    refine ((homProduct k W T).wcrossTo_zero (μ₁, μ₂) (.inl c) (.inl d) (ν₁, μ₂) (ν₂, μ₂)
      (ν₂ + RD₁.iX c, μ₂) (inlWord μ₂ R) (μ', μ₂) e' h' hM' (inl_step c μ₂ rfl)).trans ?_
    exact associator_whiskerLeft_eq_eqToHom (wcell_inlWord W T μ₂ R h.1.1 h'.1.1)
      ((leftFamily k W T μ₂).cross c d h.1.2 h.2 rfl (wValid_wswap 0 _ h).2)
  | j + 1, (c, ν) :: L, _, _, hL, hM, μ₁, μ', h, h', hM', e' => by
    simp only [inlWord_cons, wswap] at hL hM
    subst hL hM
    refine ((homProduct k W T).wcrossTo_succ (μ₁, μ₂) j (.inl c) (ν, μ₂) (inlWord μ₂ L)
      (inlWord μ₂ (wswap RD₁ j L)) (μ', μ₂) e' h' hM').trans ?_
    exact (congrArg (· ▷ _) (wcrossTo_inlWord' μ₂ j L _ _ rfl rfl h.1 h'.1 hM'.1 _)).trans
      (eqToHom_conj_whiskerRight _ _ _ _)
  | 0, [], _, _, hL, hM, _, _, _, _, _, _ => by
    simp only [inlWord_nil, wswap] at hL hM
    subst hL hM
    exact (Limits.zero_comp).trans (zero_eq_eqToHom_zero _ _)
  | 0, [_], _, _, hL, hM, _, _, _, _, _, _ => by
    simp only [inlWord_cons, inlWord_nil, wswap] at hL hM
    subst hL hM
    exact (Limits.zero_comp).trans (zero_eq_eqToHom_zero _ _)
  | _ + 1, [], _, _, hL, hM, _, _, _, _, _, _ => by
    simp only [inlWord_nil, wswap] at hL hM
    subst hL hM
    exact (Limits.zero_comp).trans (zero_eq_eqToHom_zero _ _)

end Words

end RouqFamily

end Categorification.TwoRep

namespace Categorification.KLR.Diagram.MatEnd

open CategoryTheory

variable {k : Type*} [CommRing k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
  {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ] {Y : ι → C} {Z : τ → C}

/-- Conjugation of matrices along a bijection `d` of the index sets and equalities
`Z s = Y (d s)` of the entries. -/
def conjₗ (d : τ ≃ ι) (G : ∀ s, Z s = Y (d s)) : MatEnd Y →ₗ[k] MatEnd Z where
  toFun f s t := eqToHom (G s) ≫ f (d s) (d t) ≫ eqToHom (G t).symm
  map_add' f g := by
    ext s t
    change eqToHom (G s) ≫ (f + g) (d s) (d t) ≫ eqToHom (G t).symm = _
    rw [add_apply, Preadditive.add_comp, Preadditive.comp_add]
    rfl
  map_smul' r f := by
    ext s t
    change eqToHom (G s) ≫ (r • f) (d s) (d t) ≫ eqToHom (G t).symm = _
    rw [smul_apply, Linear.smul_comp, Linear.comp_smul]
    rfl

variable (k) in
/-- Conjugation of matrices along a bijection `d` of the index sets and equalities
`Z s = Y (d s)` of the entries, as an algebra homomorphism. -/
def conjAlg (d : τ ≃ ι) (G : ∀ s, Z s = Y (d s)) : MatEnd Y →ₐ[k] MatEnd Z :=
  AlgHom.ofLinearMap (conjₗ d G)
    (by
      ext s t
      change eqToHom (G s) ≫ (1 : MatEnd Y) (d s) (d t) ≫ eqToHom (G t).symm = _
      by_cases h : s = t
      · subst h; simp
      · rw [one_apply_of_ne (fun e => h (d.injective e)), one_apply_of_ne h]; simp)
    (by
      intro f g
      ext s t
      change eqToHom (G s) ≫ (∑ j, g (d s) j ≫ f j (d t)) ≫ eqToHom (G t).symm =
        ∑ u, (eqToHom (G s) ≫ g (d s) (d u) ≫ eqToHom (G u).symm) ≫
          (eqToHom (G u) ≫ f (d u) (d t) ≫ eqToHom (G t).symm)
      rw [← d.sum_comp, Preadditive.sum_comp, Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp)

theorem conjAlg_apply (d : τ ≃ ι) (G : ∀ s, Z s = Y (d s)) (f : MatEnd Y) (s t : τ) :
    conjAlg k d G f s t = eqToHom (G s) ≫ f (d s) (d t) ≫ eqToHom (G t).symm := rfl

theorem conjAlg_single (d : τ ≃ ι) (G : ∀ s, Z s = Y (d s)) (s₀ t₀ : τ)
    (f : Y (d s₀) ⟶ Y (d t₀)) :
    conjAlg k d G (single (d s₀) (d t₀) f) =
      single s₀ t₀ (eqToHom (G s₀) ≫ f ≫ eqToHom (G t₀).symm) := by
  ext s t
  rw [conjAlg_apply]
  by_cases h : s = s₀ ∧ t = t₀
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [single_apply_of_ne _ (fun e => h ⟨d.injective e.1, d.injective e.2⟩),
      single_apply_of_ne _ h]
    simp

end Categorification.KLR.Diagram.MatEnd

namespace Categorification.TwoRep.RouqFamily

open CategoryTheory CategoryTheory.Bicategory QuantumGroup UDot KLR KLR.Diagram KLR.Diagram.MatEnd
  TypeA

section KLRActAt

variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] [AdditiveWhiskering B]
  {I : Type*} [DecidableEq I] {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X]
  [AddCommGroup Y] {RD : WeightDatum C X Y}
  {S : RouqFamily (B := B) RD} {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
  (μ : X) {ν : Multiset I} (x' : X) (e : wtop RD μ ν = x')

theorem klrActAt_x (a : Fin (Multiset.card ν)) :
    klrActAt H μ x' e (KLRAlgebra.x a : KLRAlgebra k Q ν) =
      ∑ t, single t t (S.wordDotAt μ x' e t a) := by
  subst e; exact klrAct_dot H a

end KLRActAt

section Action

variable {k : Type w'} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  {I₁ I₂ : Type*} {C₁ : CartanDatum I₁} {C₂ : CartanDatum I₂}
  {X₁ Y₁ X₂ Y₂ : Type u₁} [AddCommGroup X₁] [AddCommGroup Y₁] [AddCommGroup X₂]
  [AddCommGroup Y₂] {RD₁ : WeightDatum C₁ X₁ Y₁} {RD₂ : WeightDatum C₂ X₂ Y₂}
  (W : RouqFamily (B := B) RD₁) (T : RouqFamily (B := B) RD₂)

/-- The word of `inl ∘ s` in the product is the word of `s` in `leftFamily μ₂`. -/
theorem wordCellAt_map_inl (μ₁ : X₁) (μ₂ : X₂) {ν : Multiset I₁} (s : Seq ν) :
    (leftFamily k W T μ₂).wordCell μ₁ s =
      (homProduct k W T).wordCellAt (μ₁, μ₂) (wtop RD₁ μ₁ ν, μ₂) (wtop_map_inl μ₁ μ₂ ν)
        (Seq.map Sum.inl s) :=
  (wcell_inlWord' W T μ₂ (wordL RD₁ μ₁ s) _ (wordL_map_inl μ₁ μ₂ s).symm (wValid_wordL μ₁ s)
    (wValid_of_eq (wValid_wordL (μ₁, μ₂) _) (wtop_map_inl μ₁ μ₂ ν))).symm

theorem wordDotAt_map_inl (μ₁ : X₁) (μ₂ : X₂) {ν : Multiset I₁} (s : Seq ν)
    (a : Fin (Multiset.card ν)) :
    eqToHom (wordCellAt_map_inl W T μ₁ μ₂ s) ≫
        (homProduct k W T).wordDotAt (μ₁, μ₂) (wtop RD₁ μ₁ ν, μ₂) (wtop_map_inl μ₁ μ₂ ν)
          (Seq.map Sum.inl s) (Fin.cast (Multiset.card_map Sum.inl ν).symm a) ≫
        eqToHom (wordCellAt_map_inl W T μ₁ μ₂ s).symm =
      (leftFamily k W T μ₂).wordDot μ₁ s a := by
  have h := wdot_inlWord' (k := k) W T μ₂ a (wordL RD₁ μ₁ s) _ (wordL_map_inl μ₁ μ₂ s).symm
    (wValid_wordL μ₁ s) (wValid_of_eq (wValid_wordL (μ₁, μ₂) _) (wtop_map_inl μ₁ μ₂ ν))
  simp only [wordDotAt, Fin.val_cast]
  rw [h]
  exact eqToHom_conj_conj _ _ _ _ _

theorem map_inl_sadj {ν : Multiset I₁} (s : Seq ν) (j : ℕ) :
    sadj (Multiset.card (ν.map (Sum.inl (β := I₂)))) j • Seq.map (Sum.inl (β := I₂)) s =
      Seq.map (Sum.inl (β := I₂)) (sadj (Multiset.card ν) j • s) :=
  (Subtype.ext (funext fun b => by
    change Sum.inl (s.1 ((sadj _ j).symm (Fin.cast _ b))) =
      Sum.inl (s.1 (Fin.cast _ ((sadj _ j).symm b)))
    rw [cast_sadj_symm])).symm

theorem wordCrossAt_map_inl (μ₁ : X₁) (μ₂ : X₂) {ν : Multiset I₁} (s : Seq ν) (j : ℕ) :
    eqToHom (wordCellAt_map_inl W T μ₁ μ₂ s) ≫
        (homProduct k W T).wordCrossAt (μ₁, μ₂) (wtop RD₁ μ₁ ν, μ₂) (wtop_map_inl μ₁ μ₂ ν)
          (Seq.map Sum.inl s) j ≫
        eqToHom (congrArg (fun t => (homProduct k W T).wordCellAt (μ₁, μ₂)
          (wtop RD₁ μ₁ ν, μ₂) (wtop_map_inl μ₁ μ₂ ν) t) (map_inl_sadj s j)) ≫
        eqToHom (wordCellAt_map_inl W T μ₁ μ₂ (sadj _ j • s)).symm =
      (leftFamily k W T μ₂).wordCross μ₁ s j := by
  by_cases hj : j + 1 < Multiset.card ν
  · have hj' : j + 1 < Multiset.card (ν.map (Sum.inl (β := I₂))) := by simpa using hj
    have hM : inlWord μ₂ (wswap RD₁ j (wordL RD₁ μ₁ s)) =
        wordL (RD₁.prod RD₂) (μ₁, μ₂)
          (sadj (Multiset.card (ν.map (Sum.inl (β := I₂)))) j • Seq.map Sum.inl s) := by
      rw [wswap_wordL μ₁ s hj, map_inl_sadj, wordL_map_inl]
    have h := wcrossTo_inlWord' (k := k) W T μ₂ j (wordL RD₁ μ₁ s) _ _
      (wordL_map_inl μ₁ μ₂ s).symm hM (wValid_wordL μ₁ s) (wValid_of_eq (wValid_wordL (μ₁, μ₂) _) (wtop_map_inl μ₁ μ₂ ν))
      (wValid_of_eq (wValid_wordL (μ₁, μ₂) _) (wtop_map_inl μ₁ μ₂ ν))
      (wswap_wordL (μ₁, μ₂) (Seq.map Sum.inl s) hj')
    rw [wordCrossAt, dite_eq_left hj', h, RouqData.wordCross_def _ _ _ hj,
      RouqData.wcrossTo]
    exact eqToHom_conj_conj' _ _ _ _ _ _ _
  · have hj' : ¬ j + 1 < Multiset.card (ν.map (Sum.inl (β := I₂))) := by simpa using hj
    rw [wordCrossAt, dite_eq_right_iff.2 (fun h => absurd h hj'),
      RouqData.wordCross_of_le _ _ _ (by omega)]
    exact eqToHom_zero_eqToHom _ _ _

variable (k) in
/-- The 2-morphisms of the product between the objects `(μ₁, μ₂)`, `(x, μ₂)` are those of
`leftFamily μ₂` between `μ₁`, `x`: the identity functor between the two hom categories. -/
def leftCast (μ₁ : X₁) (μ₂ : X₂) (x : X₁) :
    ((homProduct k W T).obj (μ₁, μ₂) ⟶ (homProduct k W T).obj (x, μ₂)) ⥤
      ((leftFamily k W T μ₂).obj μ₁ ⟶ (leftFamily k W T μ₂).obj x) where
  obj f := f
  map η := η

instance (μ₁ : X₁) (μ₂ : X₂) (x : X₁) : (leftCast k W T μ₁ μ₂ x).Additive where
  map_add := rfl

instance (μ₁ : X₁) (μ₂ : X₂) (x : X₁) : (leftCast k W T μ₁ μ₂ x).Linear k where
  map_smul _ _ := rfl

@[simp] theorem leftCast_map (μ₁ : X₁) (μ₂ : X₂) (x : X₁) {f g : (homProduct k W T).obj (μ₁, μ₂) ⟶
    (homProduct k W T).obj (x, μ₂)} (η : f ⟶ g) : (leftCast k W T μ₁ μ₂ x).map η = η := rfl

/-- `wordCellAt_map_inl`, stated in the hom category of `leftFamily μ₂` through `leftCast`. -/
theorem wordCell_eq_leftCast (μ₁ : X₁) (μ₂ : X₂) (ν : Multiset I₁) (s : Seq ν) :
    (leftFamily k W T μ₂).wordCell μ₁ s = (leftCast k W T μ₁ μ₂ (wtop RD₁ μ₁ ν)).obj
      ((homProduct k W T).wordCellAt (μ₁, μ₂) (wtop RD₁ μ₁ ν, μ₂) (wtop_map_inl μ₁ μ₂ ν)
        (Seq.mapEquiv (Sum.inl_injective (β := I₂)) ν s)) :=
  wordCellAt_map_inl W T μ₁ μ₂ s

variable [DecidableEq I₁] [DecidableEq I₂] {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k}
  {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}

omit [DecidableEq I₂] in
/-- Algebra maps out of `R(ν)` agreeing on the generators are equal. -/
private theorem klr_algHom_ext {I : Type*} [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    {ν : Multiset I} {B' : Type*} [Semiring B'] [Algebra k B'] {f g : KLRAlgebra k Q ν →ₐ[k] B'}
    (he : ∀ t, f (KLRAlgebra.e t) = g (KLRAlgebra.e t))
    (hx : ∀ a, f (KLRAlgebra.x a) = g (KLRAlgebra.x a))
    (hψ : ∀ j, f (KLRAlgebra.ψ j) = g (KLRAlgebra.ψ j)) : f = g := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext gen
  simp only [Function.comp_apply]
  cases gen with
  | idem i => exact he i
  | dot a => exact hx a
  | cross j => exact hψ j

/-- **The left colours of the product act as `leftFamily`** (B. Webster, *Unfurling
Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of Theorem `nondegenerate`: the
action of `R_Q(ν)` on the labels `Ĩ₋`). For `r ∈ R_{Q₁}(ν)`, the action of
`r ∈ R_{prodQ Q₁ Q₂}(ν.map inl)` (`KLRAlgebra.reindexEquiv`) on the words of
`homProduct W T` at `(μ₁, μ₂)` with letters `inl ∘ s`, conjugated along
`wordCellAt_map_inl`, is the action of `r` on the words of `leftFamily μ₂ = W.yoneda (T(-μ₂))`
at `μ₁`. (The parameters `prodQ Q₁ Q₂ (inl a) (inl b)` are `Q₁ a b`.) -/
theorem klrActAt_reindex_inl (H₁ : RouqUpKLR W Q₁) (H₂ : RouqUpKLR T Q₂) (hQ₂ : KLRSymm Q₂)
    (μ₁ : X₁) (μ₂ : X₂) (ν : Multiset I₁) :
    (conjAlg k (Y := fun t : Seq (ν.map (Sum.inl (β := I₂))) => (leftCast k W T μ₁ μ₂
          (wtop RD₁ μ₁ ν)).obj ((homProduct k W T).wordCellAt (μ₁, μ₂) (wtop RD₁ μ₁ ν, μ₂)
            (wtop_map_inl μ₁ μ₂ ν) t))
        (Z := fun s => (leftFamily k W T μ₂).wordCell μ₁ s)
        (Seq.mapEquiv Sum.inl_injective ν) (wordCell_eq_leftCast W T μ₁ μ₂ ν)).comp
      ((mapAlg k (leftCast k W T μ₁ μ₂ (wtop RD₁ μ₁ ν)) _).comp
        ((klrActAt (homProduct_upKLR (k := k) W T H₁ H₂ hQ₂) (μ₁, μ₂) (wtop RD₁ μ₁ ν, μ₂)
          (wtop_map_inl μ₁ μ₂ ν)).comp
          (KLRAlgebra.reindexEquiv (Sum.inl_injective (β := I₂)) (prodQ Q₁ Q₂) ν).toAlgHom)) =
      klrAct (Q := fun a b => prodQ Q₁ Q₂ (Sum.inl a) (Sum.inl b))
        (yoneda_upKLR (k := k) W (T.obj (-μ₂))
          (show RouqUpKLR W (fun a b => prodQ Q₁ Q₂ (Sum.inl a) (Sum.inl b)) from H₁)) μ₁ := by
  refine klr_algHom_ext (fun t => ?_) (fun a => ?_) (fun j => ?_)
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
    rw [KLRAlgebra.reindexEquiv_e, klrActAt_e, klrAct_e, RouqData.wordE_eq]
    erw [conjAlg_single (Seq.mapEquiv Sum.inl_injective ν) _ t t]
    exact congrArg _ (eqToHom_id_eqToHom _ _)
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
    rw [KLRAlgebra.reindexEquiv_x, klrActAt_x, klrAct_dot, RouqData.wordX, map_sum, map_sum,
      ← (Seq.mapEquiv Sum.inl_injective ν).sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    erw [conjAlg_single (Seq.mapEquiv Sum.inl_injective ν) _ s s]
    exact congrArg _ (wordDotAt_map_inl W T μ₁ μ₂ s a)
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
    rw [KLRAlgebra.reindexEquiv_ψ, klrActAt_cross, klrAct_cross, RouqData.wordΨ, map_sum,
      map_sum, ← (Seq.mapEquiv Sum.inl_injective ν).sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    erw [← single_eqToHom _ (map_inl_sadj s j)]
    erw [conjAlg_single (Seq.mapEquiv Sum.inl_injective ν) _ s (sadj (Multiset.card ν) j • s)]
    exact congrArg _ ((congrArg (eqToHom _ ≫ ·) (Category.assoc _ _ _)).trans
      (wordCrossAt_map_inl (k := k) W T μ₁ μ₂ s j))

end Action

end Categorification.TwoRep.RouqFamily
