/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Vacuum
import Categorification.TwoRep.RouqYonedaEval
import Categorification.TwoRep.RouqKLRCompletion

/-!
# The left colours of a product family at the vacuum

Let `W`, `T` be Rouquier families in `LinearCat k` and `P = homProduct W T` the product family
on `Hom(T(-x₂), W(x₁))`. On the words with letters `inl t` (the labels `Ĩ₋` of B. Webster,
*Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, used in the proof of the
theorem with label `nondegenerate`), the action of the KLR algebra of `P`, evaluated at an
object `V : T(-μ₂) → W(μ₁)` of `P` and an object `z` of `T(-μ₂)`, is the action of the KLR
algebra of `W` at `V(z)` (`klrActAt_reindex_inl_app`). This composes the two comparisons
`klrActAt_reindex_inl` (the left colours act as `W.yoneda (T(-μ₂))`) and `klrAct_yoneda_eval`
(evaluating the Yoneda family).

If `W` is the cyclotomic family and `V(z)` is a vacuum module, the generators `wgen` of the words
at the vacuum read the action off the cyclotomic quotient: the coordinate at `s` of the `(t, s)`
entry applied to the generator at `t` is `hflip (σ (e(s) r e(t)))` in `R^Λ(ν)`
(`wcoord_klrActAt_inl_wgen`, from `wcoord_klrAct_wgen`). With nilpotent dots the completed action
is the action of a truncation (`RouqFamily.klrComplAt_eq_klrActAt_trunc`), which gives the same
statement for elements of the completion (`wcoord_klrComplAt_inl_wgen`).

## Main results

* `RouqFamily.klrActAt_reindex_inl_app`: the left colours of the product, evaluated at `V` and
  `z`.
* `CyclotomicAction.wcoord_klrActAt_inl_wgen`: the coordinates at the vacuum.
* `CyclotomicAction.wcoord_klrComplAt_inl_wgen`: the same for the completed action.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w' v u u₁

namespace RouqFamily

open QuantumGroup UDot KLR KLR.Diagram KLR.Diagram.MatEnd

/-- Conjugating by identifications of objects: if `X` and `Y` agree after conjugation, they agree
after the conjugation that removes the identifications. -/
theorem eqToHom_conj_of_eq {C : Type*} [Category C] {A₁ A₂ A B₁ B₂ B : C} {X : A₁ ⟶ B₁}
    {Y : A ⟶ B} (a : A₂ = A₁) (b : B₁ = B₂) (c : A₂ = A) (d : B = B₂)
    (h : eqToHom a ≫ X ≫ eqToHom b = eqToHom c ≫ Y ≫ eqToHom d) (p : A = A₁) (q : B₁ = B) :
    eqToHom p ≫ X ≫ eqToHom q = Y := by
  subst p q a d
  simpa using h

/-- A functor applied to a morphism conjugated by identifications of objects. -/
theorem map_eqToHom_conj {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A A' B B' : C}
    (p : A = A') (q : B' = B) (X : A' ⟶ B') :
    F.map (eqToHom p ≫ X ≫ eqToHom q) =
      eqToHom (congrArg F.obj p) ≫ F.map X ≫ eqToHom (congrArg F.obj q) := by
  subst p q
  simp

variable {k : Type w'} [CommRing k] {I₁ I₂ : Type*} {C₁ : CartanDatum I₁} {C₂ : CartanDatum I₂}
  {X₁ Y₁ X₂ Y₂ : Type u₁} [AddCommGroup X₁] [AddCommGroup Y₁] [AddCommGroup X₂]
  [AddCommGroup Y₂] {RD₁ : WeightDatum C₁ X₁ Y₁} {RD₂ : WeightDatum C₂ X₂ Y₂}
  (W : RouqFamily (B := LinearCat.{w', v, u} k) RD₁)
  (T : RouqFamily (B := LinearCat.{w', v, u} k) RD₂)
  (μ₁ : X₁) (μ₂ : X₂) {ν : Multiset I₁} (V : (homProduct k W T).obj (μ₁, μ₂))
  (z : (T.obj (-μ₂) : Type u))

/-- The word of `inl ∘ t` of the product, evaluated at `V` and `z`, is the word of `t` of `W`
at `V(z)`. -/
theorem wordCellAt_map_inl_eval (t : Seq ν) :
    (((homProduct k W T).wordCellAt (μ₁, μ₂) (wtop RD₁ μ₁ ν, μ₂) (wtop_map_inl μ₁ μ₂ ν)
      (Seq.map Sum.inl t)).obj.obj V).obj.obj z = (W.wordCell μ₁ t).obj.obj (V.obj.obj z) :=
  (congrArg (fun G => (G.obj.obj V).obj.obj z) (wordCellAt_map_inl W T μ₁ μ₂ t)).symm.trans
    (W.wordCell_yoneda_eval (T.obj (-μ₂)) μ₁ V z t)

variable [DecidableEq I₁] [DecidableEq I₂] {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k}
  {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}

/-- **The left colours of the product at an object** (B. Webster, arXiv:1603.06311v3, used in the
proof of the theorem with label `nondegenerate`). For `r ∈ R_{Q₁}(ν)` and an object `N = V(z)`,
the `(inl ∘ t, inl ∘ s)` entry of the action of `r ∈ R_{prodQ Q₁ Q₂}(ν.map inl)` on the words of
`homProduct W T`, evaluated at `V` and `z` and conjugated along `wordCellAt_map_inl_eval`, is the
`(t, s)` entry of the action of `r` on the words of `W`, evaluated at `N`. -/
theorem klrActAt_reindex_inl_app (H₁ : RouqUpKLR W Q₁) (H₂ : RouqUpKLR T Q₂)
    (hQ₂ : KLRSymm Q₂) (r : KLRAlgebra k Q₁ ν) (t s : Seq ν) {N : (W.obj μ₁ : Type u)}
    (hN : V.obj.obj z = N) :
    eqToHom ((wordCellAt_map_inl_eval W T μ₁ μ₂ V z t).trans
          (congrArg (W.wordCell μ₁ t).obj.obj hN)).symm ≫
        (((klrActAt (homProduct_upKLR (k := k) W T H₁ H₂ hQ₂) (μ₁, μ₂) (wtop RD₁ μ₁ ν, μ₂)
          (wtop_map_inl μ₁ μ₂ ν) (KLRAlgebra.reindexEquiv Sum.inl_injective (prodQ Q₁ Q₂) ν r))
            (Seq.map Sum.inl t) (Seq.map Sum.inl s)).hom.app V).hom.app z ≫
        eqToHom ((wordCellAt_map_inl_eval W T μ₁ μ₂ V z s).trans
          (congrArg (W.wordCell μ₁ s).obj.obj hN)) =
      (klrAct H₁ μ₁ r t s).hom.app N := by
  subst hN
  have h1 : eqToHom (wordCell_eq_leftCast W T μ₁ μ₂ ν t) ≫
      (klrActAt (homProduct_upKLR (k := k) W T H₁ H₂ hQ₂) (μ₁, μ₂) (wtop RD₁ μ₁ ν, μ₂)
        (wtop_map_inl μ₁ μ₂ ν) (KLRAlgebra.reindexEquiv Sum.inl_injective (prodQ Q₁ Q₂) ν r))
          (Seq.map Sum.inl t) (Seq.map Sum.inl s) ≫
      eqToHom (wordCell_eq_leftCast W T μ₁ μ₂ ν s).symm =
      klrAct (Q := fun a b => prodQ Q₁ Q₂ (Sum.inl a) (Sum.inl b))
        (yoneda_upKLR (k := k) W (T.obj (-μ₂))
          (show RouqUpKLR W (fun a b => prodQ Q₁ Q₂ (Sum.inl a) (Sum.inl b)) from H₁)) μ₁ r t s :=
    congrArg (fun F => F r t s) (klrActAt_reindex_inl W T H₁ H₂ hQ₂ μ₁ μ₂ ν)
  have h2 : (yEval k W (T.obj (-μ₂)) μ₁ V z (wtop RD₁ μ₁ ν)).map
      (klrAct (yoneda_upKLR (k := k) W (T.obj (-μ₂)) H₁) μ₁ r t s) =
      eqToHom (W.wordCell_yoneda_eval (T.obj (-μ₂)) μ₁ V z t) ≫
        (klrAct H₁ μ₁ r t s).hom.app (V.obj.obj z) ≫
        eqToHom (W.wordCell_yoneda_eval (T.obj (-μ₂)) μ₁ V z s).symm :=
    congrArg (fun F => F r t s) (klrAct_yoneda_eval W (T.obj (-μ₂)) μ₁ V z H₁ ν)
  exact eqToHom_conj_of_eq _ _ _ _ ((map_eqToHom_conj _ _ _ _).symm.trans
    ((congrArg (yEval k W (T.obj (-μ₂)) μ₁ V z (wtop RD₁ μ₁ ν)).map h1).trans h2)) _ _

end RouqFamily

end Categorification.TwoRep

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory QuantumGroup UDot TwoRep TwoRep.RouqFamily KLRAlgebra

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y} {Λ : X}
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg

variable {I₂ : Type*} [DecidableEq I₂] {C₂ : CartanDatum I₂} {X₂ Y₂ : Type u₁} [AddCommGroup X₂]
  [AddCommGroup Y₂] {RD₂ : WeightDatum C₂ X₂ Y₂}
  {T : RouqFamily (B := LinearCat.{v, max (max u v) w, max (max u v) w + 1} k) RD₂}
  {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k} (H₂ : RouqUpKLR T Q₂) (hQ₂ : KLRSymm Q₂)
  {μ : X} (μ₂ : X₂) (V₀ : weightSpace.{u, v, w} Q a RD Λ μ)
  (h0 : blockWeight RD Λ 0 = μ) (v₀ : V₀ ⟨0, h0⟩)
  (Ψ₀ : V₀ ⟨0, h0⟩ →ₗ[CycKLR k Q a 0] CycKLR k Q a 0)
  (V : (homProduct k (S) T).obj (μ, μ₂)) (z : (T.obj (-μ₂) : Type _))
  (hz : V.obj.obj z = familyObj hQ hlead ha hΛ hdeg V₀) {ν : Multiset I}

omit [DecidableEq I₂] in
include hz in
/-- The word of `inl ∘ t` of the product at `V` and `z`, when `V(z)` is the vacuum module, is the
word of `t` of the cyclotomic family applied to the vacuum. -/
theorem wordCellAt_map_inl_vacuum (t : Seq ν) :
    (((homProduct k (S) T).wordCellAt (μ, μ₂) (wtop RD μ ν, μ₂) (wtop_map_inl μ μ₂ ν)
      (Seq.map Sum.inl t)).obj.obj V).obj.obj z =
      (RouqData.wordCell (S).toRouqData μ t).obj.obj (familyObj hQ hlead ha hΛ hdeg V₀) :=
  (wordCellAt_map_inl_eval (S) T μ μ₂ V z t).trans
    (congrArg (RouqData.wordCell (S).toRouqData μ t).obj.obj hz)

variable {Ψ₀} in
/-- **The left colours of the product at the vacuum** (B. Webster, arXiv:1603.06311v3, used in the
proof of the theorem with label `nondegenerate`). Let `W` be the cyclotomic family, `T` a
Rouquier family, and `V`, `z` an object of `homProduct W T` and of `T(-μ₂)` with `V(z)` the vacuum
module. For `r ∈ R(ν)`, the `(inl ∘ t, inl ∘ s)` entry of the action of
`r ∈ R_{prodQ Q Q₂}(ν.map inl)` on the words of the product, evaluated at `V` and `z` and read
through the generators `wgen` and the coordinates `wcoord` of the words at the vacuum, is
`hflip (σ (e(s) r e(t)))` in `R^Λ(ν)`. -/
theorem wcoord_klrActAt_inl_wgen (hΨ₀ : Ψ₀ v₀ = 1) (r : KLRAlgebra k Q ν) (t s : Seq ν) :
    wcoord hQ hlead ha hΛ hdeg V₀ h0 Ψ₀ s
        (((eqToHom (wordCellAt_map_inl_vacuum hQ hlead ha hΛ hdeg μ₂ V₀ V z hz t).symm ≫
          (((klrActAt (homProduct_upKLR (k := k) (S) T
              (cyclotomicFamily_upKLR hQ hlead ha RD Λ hΛ hdeg) H₂ hQ₂) (μ, μ₂)
              (wtop RD μ ν, μ₂) (wtop_map_inl μ μ₂ ν)
              (KLRAlgebra.reindexEquiv Sum.inl_injective (prodQ Q Q₂) ν r))
            (Seq.map Sum.inl t) (Seq.map Sum.inl s)).hom.app V).hom.app z ≫
          eqToHom (wordCellAt_map_inl_vacuum hQ hlead ha hΛ hdeg μ₂ V₀ V z hz s))
          (topBlk h0)).hom (wgen hQ hlead ha hΛ hdeg V₀ h0 v₀ t)) =
      CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (hflip (sigma hQ (e s * r * e t))) := by
  rw [klrActAt_reindex_inl_app (S) T μ μ₂ V z (cyclotomicFamily_upKLR hQ hlead ha RD Λ hΛ hdeg)
    H₂ hQ₂ r t s hz]
  exact wcoord_klrAct_wgen hQ hlead ha hΛ hdeg V₀ h0 v₀ hΨ₀ r t s

variable {Ψ₀} in
/-- **The completed action of the left colours at the vacuum.** If the dots of the product act
nilpotently, then for every element `f` of the completion of `R_{prodQ Q Q₂}(ν.map inl)` and every
`N` beyond a bound, the entries of the completed action of `f`, read at the vacuum as in
`wcoord_klrActAt_inl_wgen`, are `hflip (σ (e(s) r e(t)))` for the truncation
`r = trunc N f ∈ R(ν)` (pulled back along `KLRAlgebra.reindexEquiv`). -/
theorem wcoord_klrComplAt_inl_wgen (hΨ₀ : Ψ₀ v₀ = 1)
    (hnil : ∀ (c : I ⊕ I₂) {x y : X × X₂} (h : x + (RD.prod RD₂).iX c = y),
      IsNilpotent (End.of ((homProduct k (S) T).dot c h)))
    (G : GradingDatum (prodQ Q Q₂)) :
    ∃ N₀ : ℤ, ∀ N, N₀ ≤ N → ∀ (f : G.completion (ν.map Sum.inl)) (t s : Seq ν),
      wcoord hQ hlead ha hΛ hdeg V₀ h0 Ψ₀ s
        (((eqToHom (wordCellAt_map_inl_vacuum hQ hlead ha hΛ hdeg μ₂ V₀ V z hz t).symm ≫
          (((klrComplAt (homProduct_upKLR (k := k) (S) T
              (cyclotomicFamily_upKLR hQ hlead ha RD Λ hΛ hdeg) H₂ hQ₂) (μ, μ₂)
              (wtop RD μ ν, μ₂) (wtop_map_inl μ μ₂ ν) hnil G f)
            (Seq.map Sum.inl t) (Seq.map Sum.inl s)).hom.app V).hom.app z ≫
          eqToHom (wordCellAt_map_inl_vacuum hQ hlead ha hΛ hdeg μ₂ V₀ V z hz s))
          (topBlk h0)).hom (wgen hQ hlead ha hΛ hdeg V₀ h0 v₀ t)) =
      CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (hflip (sigma hQ (e s *
        (KLRAlgebra.reindexEquiv Sum.inl_injective (prodQ Q Q₂) ν).symm (G.trunc N f) * e t))) := by
  obtain ⟨N₀, hN₀⟩ := klrComplAt_eq_klrActAt_trunc (homProduct_upKLR (k := k) (S) T
    (cyclotomicFamily_upKLR hQ hlead ha RD Λ hΛ hdeg) H₂ hQ₂) (μ, μ₂) (wtop RD μ ν, μ₂)
    (wtop_map_inl μ μ₂ ν) hnil G
  refine ⟨N₀, fun N hN f t s => ?_⟩
  have h := wcoord_klrActAt_inl_wgen hQ hlead ha hΛ hdeg H₂ hQ₂ μ₂ V₀ h0 v₀ V z hz hΨ₀
    ((KLRAlgebra.reindexEquiv Sum.inl_injective (prodQ Q Q₂) ν).symm (G.trunc N f)) t s
  rw [AlgEquiv.apply_symm_apply] at h
  rw [hN₀ N hN f]
  exact h

end Categorification.KLR.CyclotomicAction
