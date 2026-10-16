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

end Furling

end Categorification.TwoRep
