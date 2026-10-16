/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SpanningPhi
import Categorification.TwoRep.RouqUpWords

/-!
# Bubble evaluation in a Rouquier family

Supporting the bubble action in Webster, *Unfurling KLR algebras*, arXiv:1603.06311v3,
proof of the theorem labelled `nondegenerate`, “Triviality of a relation”.

`bubbleEval` interprets the algebra of empty-word endomorphisms, and `bubbleMap` composes it
with the polynomial bubble map. The diagrammatic and local Rouquier orientation names are
opposite: `cwU` maps to `RouqLoc.ccw`, and `ccwU` maps to `RouqLoc.cw`. This agrees with the
real-bubble calculations in `RouqBubbles` and their recursive extensions in `RouqFakeBubbles`.
`bubbleMap_X` records the resulting weight-dependent orientation and dot shift.

`upEval_bubAt` and `upEval_bubMap` identify placement to the right of upward strands with
right whiskering. These statements are generic in the Rouquier family, under the same
explicit upward-KLR and mixed-inversion hypotheses as `upEval`; they do not assume any
vacuum formula or independence assertion.
-/

noncomputable section
namespace Categorification.Diagrams.BicatInterp
open CategoryTheory Bicategory StringDiagrams
universe w₁ w₂ u₀ u₁ u₂ v₂
variable {S : Signature.{u₀, u₁, u₂}} {C : Type w₁} [Bicategory.{w₂, v₂} C]
  {M : Model S C}
variable {k : Type*} [CommRing k] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C, Linear k (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k]
variable (G : GenImg M) (P : Presentation S k)
  (hrel : ∀ (i : P.Rel) {s t : S.Region} (ha : Cond s t (P.dom i))
    (hb : Cond s t (P.cod i)), admissibleMap G ha hb (P.rel i) = 0)
  (heven : ∀ g, S.odd g = false)

private theorem quotientMap_bubble_whisk {s t : S.Region} (u : Obj S) (hu : Cond s t u)
    (a : Obj S) (ha : Cond t t a) (he : a.word = [])
    (e : a.whisker u [] = u) (β : End (P.obj a)) :
    admissibleQuotientMap G P hrel heven hu hu
      (eqToHom (congrArg P.obj e.symm) ≫ P.whisk β u [] ≫ eqToHom (congrArg P.obj e)) =
      (λ_ (M.word s u.word t hu.1 hu.2.1)).inv ≫
        (eqToHom (congrArg M.lift.map (fw_eq he ha.1 ha.2.1 (S.ok_nil t) (S.endR_nil t))).symm ≫
          admissibleQuotientMap G P hrel heven ha ha β ≫
          eqToHom (congrArg M.lift.map (fw_eq he ha.1 ha.2.1 (S.ok_nil t) (S.endR_nil t)))) ▷
        M.word s u.word t hu.1 hu.2.1 ≫ (λ_ _).hom := by
  obtain ⟨ar, aw⟩ := a
  dsimp at he
  subst aw
  have har : ar = t := ha.2.2
  subst ar
  have hus : u.start = s := hu.2.2
  have hwa : Cond s t ((⟨t, []⟩ : Obj S).whisker u []) := e.symm ▸ hu
  rw [admissibleQuotientMap_comp G P hrel heven hu hwa hu,
    admissibleQuotientMap_comp G P hrel heven hwa hwa hu,
    admissibleQuotientMap_eqToHom G P hrel heven hu hwa e.symm,
    admissibleQuotientMap_eqToHom G P hrel heven hwa hu e]
  rw [admissibleQuotientMap_whisk_coherent G P hrel heven (v := []) β ha ha hus hu.1 hu.2.1
    (S.ok_nil t) (S.endR_nil t) hwa hwa
    (eqToHom (fw_eq (congrArg Obj.word e) hwa.1 hwa.2.1 hu.1 hu.2.1) ≫
      (λ_ _).inv ≫ (λ_ _).inv)
    ((λ_ _).hom ≫ (λ_ _).hom ≫
      eqToHom (fw_eq (congrArg Obj.word e.symm) hu.1 hu.2.1 hwa.1 hwa.2.1))]
  refine (conj_regroup M _ _ _ _ _
    ((λ_ (fw s u.word t hu.1 hu.2.1)).inv ≫ (λ_ _).inv)
    ((λ_ _).hom ≫ (λ_ (fw s u.word t hu.1 hu.2.1)).hom)).trans ?_
  simp only [PrelaxFunctor.map₂_comp, lift_map₂_leftUnitor_inv,
    lift_map₂_leftUnitor_hom, eqToHom_refl, Category.id_comp, Category.comp_id]
  change ((λ_ (M.word s u.word t hu.1 hu.2.1)).inv ≫ (λ_ _).inv) ≫
    (𝟙 _ ◁ (admissibleQuotientMap G P hrel heven ha ha β ▷
      M.word s u.word t hu.1 hu.2.1)) ≫ (λ_ _).hom ≫ (λ_ _).hom = _
  bicategory
end Categorification.Diagrams.BicatInterp
noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
private theorem eqToHom_sandwich {D : Type*} [Category D]
    {a b c d e f : D} (p : a = b) (q : b = c) (r : d = e) (s : e = f)
    (t : a = c) (u : d = f) (g : c ⟶ d) :
    eqToHom p ≫ (eqToHom q ≫ g ≫ eqToHom r) ≫ eqToHom s =
      eqToHom t ≫ g ≫ eqToHom u := by
  simp

private theorem iso_conj_rightBubble {D : Type*} [Bicategory D] {a b : D}
    {f g : a ⟶ b} (e : f ≅ g) (β : End (𝟙 a)) :
    e.inv ≫ ((λ_ f).inv ≫ β ▷ f ≫ (λ_ f).hom) ≫ e.hom =
      (λ_ g).inv ≫ β ▷ g ≫ (λ_ g).hom := by
  simp only [Category.assoc]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    leftUnitor_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

namespace RouqFamily
variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [AdditiveWhiskering B]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}
variable (S : RouqFamily (B := B) RD)
  (H : BrundanUpKLR S (CL.CLScalars.kl : CL.CLScalars C k)) (M : BrundanMixedInversion S)

/-- The algebra action of endomorphisms of the empty diagrammatic word. -/
def bubbleEval (μ : X) : EndOne RD k μ →ₐ[k] End (𝟙 (S.obj μ)) where
  toFun β := admissibleQuotientMap (S.genImg (CL.CLScalars.kl : CL.CLScalars C k))
    (pres RD k) (S.pres_rel_kl k H M) Signature.IsEven.odd_eq_false
    (bubbleNil μ).property (bubbleNil μ).property β.val
  map_one' := admissibleQuotientMap_id _ _ _ _ _
  map_mul' f g := admissibleQuotientMap_comp _ _ _ _ _ (bubbleNil μ).property _ g.val f.val
  map_zero' := by
    change admissibleMap _ _ _ 0 = 0
    exact map_zero _
  map_add' f g := admissibleQuotientMap_add _ _ _ _ _ _ f.val g.val
  commutes' r := by
    rw [EndOne.val_algebraMap]
    exact (admissibleQuotientMap_smul _ _ _ _ _ _ r _).trans
      ((congrArg (r • ·) (admissibleQuotientMap_id _ _ _ _ _)).trans
        (show r • (1 : End (𝟙 (S.obj μ))) = algebraMap k _ r from
          (Algebra.algebraMap_eq_smul_one r).symm))

/-- Clockwise diagrammatic bubbles evaluate to the local counterclockwise convention,
including fake bubbles. -/
theorem bubbleEval_cwU (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) (m : ℤ) :
    S.bubbleEval H M b (EndOne.of (cwU RD k b i m)) = (S.loc i h₁ h₂).ccw m :=
  S.bubble_cwL _ i h₁ h₂ m

/-- Counterclockwise diagrammatic bubbles evaluate to the local clockwise convention,
including fake bubbles. -/
theorem bubbleEval_ccwU (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) (m : ℤ) :
    S.bubbleEval H M b (EndOne.of (ccwU RD k b i m)) = (S.loc i h₁ h₂).cw m :=
  S.bubble_ccwL _ i h₁ h₂ m

/-- The orientation chosen by the polynomial bubble generators after evaluation. -/
theorem bubbleEval_bubGen (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) (n : ℕ) :
    S.bubbleEval H M b (EndOne.of (bubGen RD k b i n)) =
      if 0 ≤ ip RD i b then (S.loc i h₁ h₂).ccw (ip RD i b - 1 + n)
      else (S.loc i h₁ h₂).cw (-ip RD i b - 1 + n) := by
  unfold bubGen
  split_ifs
  · exact S.bubbleEval_cwU H M i h₁ h₂ _
  · exact S.bubbleEval_ccwU H M i h₁ h₂ _
/-- The polynomial bubble action induced by the quotient interpretation. -/
def bubbleMap (μ : X) : PiLam I k →ₐ[k] End (𝟙 (S.obj μ)) :=
  (S.bubbleEval H M μ).comp (bubMap RD k μ)

/-- The image of a polynomial bubble variable, with its orientation and dot shift explicit. -/
theorem bubbleMap_X (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) (n : ℕ) :
    S.bubbleMap H M b (MvPolynomial.X (i, n)) =
      if 0 ≤ ip RD i b then (S.loc i h₁ h₂).ccw (ip RD i b - 1 + (n + 1 : ℕ))
      else (S.loc i h₁ h₂).cw (-ip RD i b - 1 + (n + 1 : ℕ)) := by
  change S.bubbleEval H M b (bubMap RD k b (MvPolynomial.X (i, n))) = _
  rw [bubMap, MvPolynomial.aeval_X]
  exact S.bubbleEval_bubGen H M i h₁ h₂ _

private theorem dg_nil_eqToHom (μ : X) (s t : List (Letter I)) (h : s = t) :
    dg RD k μ s t [] = eqToHom (congrArg (fun s => (pres RD k).obj (ob RD μ s)) h) := by
  subst t
  exact dg_nil (RD := RD) (k := k) μ s

private theorem bubAt_eq_whisk (μ : X) (s : List (Letter I))
    (β : End ((pres RD k).obj (ob RD μ []))) :
    bubAt RD k μ s β =
      eqToHom (congrArg (pres RD k).obj (by
        apply Obj.ext
        · rfl
        · change (ob RD μ s).word = (ob RD μ s).word ++ [] ++ []
          simp only [List.append_nil])) ≫
      (pres RD k).whisk β (ob RD μ s) [] ≫
      eqToHom (congrArg (pres RD k).obj (by
        apply Obj.ext
        · rfl
        · change (ob RD μ s).word ++ [] ++ [] = (ob RD μ s).word
          simp only [List.append_nil])) := by
  change dg RD k μ s (s ++ [] ++ []) [] ≫ plcL RD k μ s [] [] [] β ≫
    dg RD k μ (s ++ [] ++ []) s [] = _
  erw [plcL, dite_eq_left rfl]
  simp only [plc, LinearMap.coe_mk, AddHom.coe_mk]
  erw [dg_nil_eqToHom μ s (s ++ [] ++ []) (by simp),
    dg_nil_eqToHom μ (s ++ [] ++ []) s (by simp)]
  change eqToHom _ ≫ (eqToHom _ ≫ (pres RD k).whisk β (ob RD μ s) [] ≫ eqToHom _) ≫
    eqToHom _ = _
  exact eqToHom_sandwich _ _ _ _ _ _ _

/-- Evaluation commutes with placing an empty-word endomorphism to the right of an
upward word. The right whiskering is conjugated by the left unitor. -/
theorem upEval_bubAt {ν : Multiset I} (μ : X) (t : KLR.Seq ν)
    (β : EndOne RD k μ) :
    S.upEval H M μ (bubAt RD k μ (ups (KLR.Diagram.word t)) β.val) =
      (λ_ (S.wordCell μ t)).inv ≫ S.bubbleEval H M μ β ▷ S.wordCell μ t ≫
        (λ_ (S.wordCell μ t)).hom := by
  let hu := cond_word (RD := RD) μ t
  let q := S.model.word (wtop RD μ ν : X) (ob RD μ (ups (KLR.Diagram.word t))).word μ hu.1 hu.2.1
  have h : admissibleQuotientMap (S.genImg (CL.CLScalars.kl : CL.CLScalars C k))
      (pres RD k) (S.pres_rel_kl k H M) Signature.IsEven.odd_eq_false hu hu
      (bubAt RD k μ (ups (KLR.Diagram.word t)) β.val) =
      (λ_ q).inv ≫ S.bubbleEval H M μ β ▷ q ≫ (λ_ q).hom := by
    rw [bubAt_eq_whisk]
    have h := quotientMap_bubble_whisk (S.genImg (CL.CLScalars.kl : CL.CLScalars C k))
      (pres RD k) (S.pres_rel_kl k H M) Signature.IsEven.odd_eq_false
      (ob RD μ (ups (KLR.Diagram.word t))) hu (bubbleNil μ).obj (bubbleNil μ).property
      rfl (by
        apply Obj.ext
        · rfl
        · change (ob RD μ (ups (KLR.Diagram.word t))).word ++ [] ++ [] = _
          simp only [List.append_nil]) β.val
    change _ = (λ_ q).inv ≫ (𝟙 _ ≫ S.bubbleEval H M μ β ≫ 𝟙 _) ▷ q ≫ (λ_ q).hom at h
    exact h.trans (congrArg (fun b : End (𝟙 (S.obj μ)) =>
      (λ_ q).inv ≫ b ▷ q ≫ (λ_ q).hom) (by simp))
  change (S.upIso μ t hu).inv ≫ _ ≫ (S.upIso μ t hu).hom = _
  exact (congrArg (fun f => (S.upIso μ t hu).inv ≫ f ≫ (S.upIso μ t hu).hom) h).trans
    (iso_conj_rightBubble (S.upIso μ t hu) (S.bubbleEval H M μ β))

/-- Polynomial bubbles on the right evaluate by right whiskering their polynomial action. -/
theorem upEval_bubMap {ν : Multiset I} (μ : X) (t : KLR.Seq ν) (p : PiLam I k) :
    S.upEval H M μ (bubAt RD k μ (ups (KLR.Diagram.word t)) (bubMap RD k μ p).val) =
      (λ_ (S.wordCell μ t)).inv ≫ S.bubbleMap H M μ p ▷ S.wordCell μ t ≫
        (λ_ (S.wordCell μ t)).hom :=
  S.upEval_bubAt H M μ t (bubMap RD k μ p)

end RouqFamily
end Categorification.TwoRep
