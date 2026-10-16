/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingKLR

/-!
# The corner of a furled action: projections onto paths

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2.3, Lemma with
label `lem:g-action`, and the proof of the theorem with label `nondegenerate`. A word of `g`
applied to an object `M`, at a block `δ`, is the direct sum over the paths of relevant edges into
`δ` of the words of `g̃` of these paths applied to `M`. `Furling.pgen` is the inclusion of the
summand of a path; this file constructs the projection onto it (`Furling.pproj`) and proves that
for a fixed source block these are the projections of a direct sum decomposition:
`pgen ≫ pproj = 𝟙` on the same path and `0` on different paths (`pgen_pproj`,
`pgen_pproj_of_ne`).

Together with `MatEnd.comp_proj_of_intertw` and `intertw_freeGamma`, these projections extract
the matrix entries of the action of `R(ν)` on the words of `g` between two summands as those of
the action of `γ(r)` on the words of `g̃`. This is the step of Webster's proof in which the
action of `𝒰` on `𝕍` is computed on the summands `Ẽ_t 𝕍`.

## Main definitions and results

* `MatEnd.comp_proj_of_intertw`: entries of intertwined matrices against a left inverse family.
* `Furling.projE`, `Furling.pproj`, `Furling.pgen_pproj`, `Furling.pgen_pproj_of_ne`.
* `Furling.lproj`, `Furling.lgen_lproj`: the projections onto the summands of lifts, a left
  inverse family of the generators `lgen`.
* `Furling.lgen_actG_lproj`: the entries of the action of `R(ν)` on the words of `g` between
  lifts are the entries of the action of `γ(r)` on the words of `g̃`.
-/

noncomputable section

namespace Categorification.KLR.Diagram.MatEnd

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {τ : Type*} [Fintype τ] [DecidableEq τ] {Y : ι → C} {Z : τ → C} (d : τ → ι)
  (G : ∀ s, Z s ⟶ Y (d s))

omit [Fintype ι] in
/-- **Entries of intertwined matrices**: if `G` intertwines `A` and `B`, and the maps
`P u : Y t ⟶ Z u` are a left inverse family of the `G u` with `d u = t`
(`G u ≫ P u' = δ_{u u'}`), then `G s ≫ A (d s) t ≫ P u = B s u` for `d u = t`. -/
theorem comp_proj_of_intertw {A : MatEnd Y} {B : MatEnd Z} (h : Intertw d G A B) (t : ι)
    (P : ∀ u, Y t ⟶ Z u)
    (horth : ∀ u u' (hu : d u = t), G u ≫ eqToHom (congrArg Y hu) ≫ P u' =
      if h : u = u' then eqToHom (congrArg Z h) else 0)
    (s u : τ) (hu : d u = t) :
    G s ≫ A (d s) t ≫ P u = B s u := by
  rw [← Category.assoc, h s t, Preadditive.sum_comp, Finset.sum_eq_single u]
  · rw [rect, dite_eq_left_of_eq_true (eq_true hu), Category.assoc, Category.assoc, horth u u hu,
      dite_eq_left_of_eq_true (eq_true rfl), eqToHom_refl, Category.comp_id]
  · intro v _ hv
    rw [rect]
    split_ifs with hv'
    · rw [Category.assoc, Category.assoc, horth v u hv', dite_eq_right_of_eq_false (eq_false hv),
        Limits.comp_zero]
    · simp
  · simp

end Categorification.KLR.Diagram.MatEnd

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits KLR KLR.Diagram

universe u₁ u₂ v₁ wk u₃ u₄

namespace Furling

variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc} {RD : QuantumGroup.UDot.WeightDatum C X Y}
  (Φ : Furling RDc RD)
  (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc)
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {P : I → I → MvPolynomial (Fin 2) k} (D : KLR.Unfurling.UnfurlingDatum k P J)

/-! ## Projections onto paths -/

/-- The projection of `E_i M` onto the summand of an edge. -/
abbrev projE (i : I) {l l' : X} (h : l + RD.iX i = l') (M : ∀ β : Φ.Blk l, blkCat Φ S β.1)
    {γ : Φ.Blk l'} (p : {e : Φ.Edge i l // e.tgt h = γ}) :
    (E Φ S i h).obj.obj M γ ⟶ (Ea Φ S h p.1 γ p.2).obj (M p.1.src) :=
  biproduct.π (fun p : {e : Φ.Edge i l // e.tgt h = γ} =>
    (Ea Φ S h p.1 γ p.2).obj ((blockRes Edge.src (resSrc Φ S)).obj M p.1)) p

omit [DecidableEq I] [DecidableEq J] in
theorem genE_projE (i : I) {l l' : X} (h : l + RD.iX i = l')
    (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) {γ : Φ.Blk l'} (p : {e : Φ.Edge i l // e.tgt h = γ}) :
    genE Φ S i h M p ≫ projE Φ S i h M p = 𝟙 _ :=
  biproduct.ι_π_self _ p

omit [DecidableEq I] [DecidableEq J] in
theorem genE_projE_of_ne (i : I) {l l' : X} (h : l + RD.iX i = l')
    (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) {γ : Φ.Blk l'} {p q : {e : Φ.Edge i l // e.tgt h = γ}}
    (hpq : p ≠ q) : genE Φ S i h M p ≫ projE Φ S i h M q = 0 :=
  biproduct.ι_π_ne _ hpq

variable {μ : X} (M : ∀ β : Φ.Blk μ, blkCat Φ S β.1)

/-- **The projection of a word of `g` onto the summand of a path**: from the word of `g` applied
to `M` at the endpoint `δ` of the path from `β` with labels `Ps`, to the word of `g̃` of the path
applied to `M β`. -/
def pproj (β : Φ.Blk μ) : ∀ (L : List (I × X)) (Ps : List J) (μ' : X) (hL : wValid RD μ L μ')
    (_ : IsPath Φ β.1 L Ps) (δ : Φ.Blk μ') (hδ : endBlk β.1 Ps = δ.1),
    (((rouqData Φ S D).wcell μ L μ' hL).obj.obj M) δ ⟶
      (S.wcell (Φ.wtT β.1) (liftL Φ β.1 Ps) (Φ.wtT δ.1)
        (wValid_liftL_of_eq Φ β.1 Ps hδ)).obj.obj (M β)
  | [], [], μ', hL, _, δ, hδ => by
    obtain rfl : μ = μ' := hL
    obtain rfl : β = δ := Subtype.ext hδ
    exact 𝟙 _
  | (c, ν) :: L, a :: Ps, _, hL, hP, δ, hδ =>
    projE Φ S c hL.2 (((rouqData Φ S D).wcell μ L ν hL.1).obj.obj M)
        ⟨pathEdge Φ β c ν L a Ps hL.1 hP, Subtype.ext hδ⟩ ≫
      (Ea Φ S hL.2 (pathEdge Φ β c ν L a Ps hL.1 hP) δ (Subtype.ext hδ)).map
        (pproj β L Ps ν hL.1 hP.1 (pathEdge Φ β c ν L a Ps hL.1 hP).src rfl)
  | [], _ :: _, _, _, hP, _, _ => hP.elim
  | _ :: _, [], _, _, hP, _, _ => hP.elim

theorem pproj_cons (β : Φ.Blk μ) (c : I) (ν : X) (L : List (I × X)) (a : J) (Ps : List J)
    {μ' : X} (hL : wValid RD μ ((c, ν) :: L) μ') (hP : IsPath Φ β.1 ((c, ν) :: L) (a :: Ps))
    (δ : Φ.Blk μ') (hδ : endBlk β.1 (a :: Ps) = δ.1) :
    pproj Φ S D M β ((c, ν) :: L) (a :: Ps) μ' hL hP δ hδ =
      projE Φ S c hL.2 (((rouqData Φ S D).wcell μ L ν hL.1).obj.obj M)
          ⟨pathEdge Φ β c ν L a Ps hL.1 hP, Subtype.ext hδ⟩ ≫
        (Ea Φ S hL.2 (pathEdge Φ β c ν L a Ps hL.1 hP) δ (Subtype.ext hδ)).map
          (pproj Φ S D M β L Ps ν hL.1 hP.1 (pathEdge Φ β c ν L a Ps hL.1 hP).src rfl) := rfl

/-- The projection onto a path is a left inverse of its generator. -/
theorem pgen_pproj (β : Φ.Blk μ) : ∀ (L : List (I × X)) (Ps : List J) (μ' : X)
    (hL : wValid RD μ L μ') (hP : IsPath Φ β.1 L Ps) (δ : Φ.Blk μ') (hδ : endBlk β.1 Ps = δ.1),
    pgen Φ S D M β L Ps μ' hL hP δ hδ ≫ pproj Φ S D M β L Ps μ' hL hP δ hδ = 𝟙 _
  | [], [], μ', hL, hP, δ, hδ => by
    obtain rfl : μ = μ' := hL
    obtain rfl : β = δ := Subtype.ext hδ
    exact Category.id_comp _
  | (c, ν) :: L, a :: Ps, μ', hL, hP, δ, hδ => by
    rw [pgen_cons, pproj_cons]
    erw [Category.assoc, reassoc_of% (genE_projE Φ S c hL.2 _ _)]
    erw [← Functor.map_comp, pgen_pproj β L Ps ν hL.1 hP.1 _ rfl, CategoryTheory.Functor.map_id]
    rfl
  | [], _ :: _, _, _, hP, _, _ => hP.elim
  | _ :: _, [], _, _, hP, _, _ => hP.elim

/-- The generator of a path followed by the projection onto a different path from the same
block is zero. -/
theorem pgen_pproj_of_ne (β : Φ.Blk μ) : ∀ (L : List (I × X)) (Ps Ps' : List J) (μ' : X)
    (hL : wValid RD μ L μ') (hP : IsPath Φ β.1 L Ps) (hP' : IsPath Φ β.1 L Ps') (δ : Φ.Blk μ')
    (hδ : endBlk β.1 Ps = δ.1) (hδ' : endBlk β.1 Ps' = δ.1), Ps ≠ Ps' →
    pgen Φ S D M β L Ps μ' hL hP δ hδ ≫ pproj Φ S D M β L Ps' μ' hL hP' δ hδ' = 0
  | [], [], [], _, _, _, _, _, _, _, hne => absurd rfl hne
  | (c, ν) :: L, a :: Ps, a' :: Ps', μ', hL, hP, hP', δ, hδ, hδ', hne => by
    rw [pgen_cons, pproj_cons]
    erw [Category.assoc]
    have key : ∀ (q : {e : Φ.Edge c ν // e.tgt hL.2 = δ}) (hq : endBlk β.1 Ps' = q.1.src.1)
        (hP'' : IsPath Φ β.1 L Ps'), q.1.lbl = a' →
        (Ea Φ S hL.2 (pathEdge Φ β c ν L a Ps hL.1 hP) δ (Subtype.ext hδ)).map
            (pgen Φ S D M β L Ps ν hL.1 hP.1 (pathEdge Φ β c ν L a Ps hL.1 hP).src rfl) ≫
          genE Φ S c hL.2 (((rouqData Φ S D).wcell μ L ν hL.1).obj.obj M)
            ⟨pathEdge Φ β c ν L a Ps hL.1 hP, Subtype.ext hδ⟩ ≫
          projE Φ S c hL.2 (((rouqData Φ S D).wcell μ L ν hL.1).obj.obj M) q ≫
          (Ea Φ S hL.2 q.1 δ q.2).map (pproj Φ S D M β L Ps' ν hL.1 hP'' q.1.src hq) = 0 := by
      intro q hq hP'' hqa
      by_cases hpq : (⟨pathEdge Φ β c ν L a Ps hL.1 hP, Subtype.ext hδ⟩ :
          {e : Φ.Edge c ν // e.tgt hL.2 = δ}) = q
      · subst hpq
        have ha : a = a' := hqa
        subst ha
        have hne' : Ps ≠ Ps' := fun h => hne (by rw [h])
        erw [reassoc_of% (genE_projE Φ S c hL.2 _ _)]
        erw [← Functor.map_comp, pgen_pproj_of_ne β L Ps Ps' ν hL.1 hP.1 hP'' _ rfl hq hne',
          CategoryTheory.Functor.map_zero]
      · erw [reassoc_of% (genE_projE_of_ne Φ S c hL.2 _ hpq)]
        rw [Limits.zero_comp,
          Limits.comp_zero]
    exact key ⟨pathEdge Φ β c ν L a' Ps' hL.1 hP', Subtype.ext hδ'⟩ rfl hP'.1 rfl
  | [], [], _ :: _, _, _, _, hP', _, _, _, _ => hP'.elim
  | [], _ :: _, _, _, _, hP, _, _, _, _, _ => hP.elim
  | _ :: _, [], _, _, _, hP, _, _, _, _, _ => hP.elim
  | _ :: _, _ :: _, [], _, _, _, hP', _, _, _, _ => hP'.elim

/-! ## Projections onto the summands of lifts -/

section Lift

variable {Φ D} (hπ : ∀ a, Φ.π a = D.π a) {ν : Multiset I} (δ : Φ.Blk (wtop RD μ ν))
  (β : Φ.Blk μ) (ν' : Unfurling.Lift D ν) (hδ : β.1 + blkSum ν'.1 = δ.1)

open Classical in
/-- **The projection onto the summand of a lift**: from the word of `g` of `t` applied to `M`, at
the block `δ`, to the word of `g̃` of a lift `s` of `t` applied to `M β`. It is the projection
`pproj` onto the path of the labels of `s` if `s` lies over `t` and its edges are relevant, and
zero otherwise. It is a left inverse family of the generators `lgen` (`lgen_lproj`). -/
def lproj (t : Seq ν) (s : Seq ν'.1) :
    (evalBlk Φ S M δ).obj ((rouqData Φ S D).wordCell μ t) ⟶
      (S.wordCellAt (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) s).obj.obj (M β) :=
  if h : Unfurling.down D.π ν'.2 s = t ∧ IsRel Φ β.1 (word s) then
    pproj Φ S D M β (wordL RD μ t) (word s) (wtop RD μ ν) (wValid_wordL μ t)
        (h.1 ▸ isPath_down hπ μ ν'.2 β.1 s h.2) δ ((endBlk_word β.1 s).trans hδ) ≫
      (eqToHom (S.wcell_congr (Φ.wtT β.1) (liftL_eq_canon Φ β.1 (word s)) _
        (wValid_of_eq (wValid_wordL _ s) (wtop_lift μ δ β ν' hδ)))).hom.app (M β)
  else 0

open Classical in
theorem lproj_of_not (t : Seq ν) (s : Seq ν'.1)
    (h : ¬ (Unfurling.down D.π ν'.2 s = t ∧ IsRel Φ β.1 (word s))) :
    lproj S M hπ δ β ν' hδ t s = 0 := by
  unfold lproj; rw [dite_eq_right h]

variable (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
include hzero

/-- **The projections onto lifts are a left inverse family of the generators of lifts**: for a
lift `u` of `t`, `lgen u ≫ lproj t u'` is the identity if `u = u'` and zero otherwise. -/
theorem lgen_lproj (u u' : Seq ν'.1) {t : Seq ν} (hu : Unfurling.down D.π ν'.2 u = t) :
    lgen S hπ μ M δ β ν' hδ u ≫
        eqToHom (congrArg (fun t : Seq ν => (evalBlk Φ S M δ).obj
          ((rouqData Φ S D).wordCell μ t)) hu) ≫ lproj S M hπ δ β ν' hδ t u' =
      if h : u = u' then eqToHom (congrArg (fun s : Seq ν'.1 =>
        (S.wordCellAt (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) s).obj.obj (M β)) h)
      else 0 := by
  classical
  subst hu
  rw [eqToHom_refl, Category.id_comp]
  by_cases hr : IsRel Φ β.1 (word u)
  · rw [lgen_of_isRel S hπ μ M δ β ν' hδ u hr]
    by_cases h : u = u'
    · subst h
      rw [lproj, dite_eq_left ⟨rfl, hr⟩, dite_eq_left rfl, eqToHom_refl]
      refine (Category.assoc _ _ _).trans ?_
      erw [reassoc_of% (pgen_pproj Φ S D M β _ _ _ _ _ _ _)]
      rw [LinearCat.eqToHom_hom_app, LinearCat.eqToHom_hom_app, eqToHom_trans, eqToHom_refl]
    · rw [dite_eq_right h]
      by_cases h' : Unfurling.down D.π ν'.2 u' = Unfurling.down D.π ν'.2 u ∧
          IsRel Φ β.1 (word u')
      · rw [lproj, dite_eq_left h']
        refine (Category.assoc _ _ _).trans ?_
        erw [reassoc_of% (pgen_pproj_of_ne Φ S D M β _ _ _ _ _ _ _ _ _ _
          (fun e => h (word_injective e)))]
        rw [Limits.zero_comp, Limits.comp_zero]
      · rw [lproj_of_not S M hπ δ β ν' hδ _ _ h']; exact Limits.comp_zero
  · have hl : lgen S hπ μ M δ β ν' hδ u = 0 := by unfold lgen; rw [dite_eq_right hr]
    rw [hl, Limits.zero_comp]
    split_ifs
    · exact (isZero_wordCellAt S μ M δ β ν' hδ hzero u hr).eq_of_src _ _
    · rfl

variable {S} (H : RouqUpKLR S (Unfurling.unfQ (k := k) D.arrows))
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))

/-- **The entries of the action of `g` between lifts** (Webster, arXiv:1603.06311v3, Lemma
`lem:g-action` (label)): for lifts `s`, `u` with `u` over `t`, the composite of the generator of `s`,
the `(down s, t)` entry of the action of `r` on the words of `g`, and the projection onto `u`, is
the `(s, u)` entry of the action of `γ(r)` on the words of `g̃`. -/
theorem lgen_actG_lproj (r : FreeAlgebra k (KLR.Gen ν)) (s u : Seq ν'.1) {t : Seq ν}
    (hu : Unfurling.down D.π ν'.2 u = t) :
    lgen S hπ μ M δ β ν' hδ s ≫ actG S μ M δ r (Unfurling.down D.π ν'.2 s) t ≫
        lproj S M hπ δ β ν' hδ t u =
      actT μ M δ β ν' hδ H hnil r s u :=
  MatEnd.comp_proj_of_intertw _ _ (intertw_freeGamma hπ μ M δ β ν' hδ H hnil hzero r) t
    (lproj S M hπ δ β ν' hδ t) (fun u u' hu => lgen_lproj S M hπ δ β ν' hδ hzero u u' hu) s u hu

end Lift

end Furling

end Categorification.TwoRep
