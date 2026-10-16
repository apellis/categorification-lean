/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingSigma
import Categorification.TwoRep.RouqKLRAction

/-!
# Furling: the words of `g` on paths of the cover

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2.3, Lemma with
label `lem:g-action`. The generators of `g` constructed in `Furling`, `FurlingCross` (the
1-morphisms `E_i = ⊕_{a over i} E_a`, the dots `ϖ_a(y)` and the crossings, the image of `ψ`
under the unfurling homomorphism) form a `RouqData` (`Furling.rouqData`), so the weighted words
of `RouqData` apply to them.

A word `E_{c_0} ∘ ⋯ ∘ E_{c_{n-1}}` of `g` applied to `M` is, at a block `δ`, the sum over the
paths `β →a_{n-1}→ ⋯ →a_0→ δ` of relevant edges with labels over the colours of the word of the
corresponding words `E_{a_0} ∘ ⋯ ∘ E_{a_{n-1}}` of `g̃` applied to `M β`. This file constructs
the generator of a path (`Furling.pgen`), shows that maps out of a word of `g` are determined on
these generators (`Furling.pgen_ext`), and computes the dots of `g` on them (`Furling.pgen_wdot`):
on the path of labels `a`, the dot on the `r`-th letter is `ϖ_{a_r}(y)` with `y` the dot on the
`r`-th letter of the word of `g̃`.

## Main definitions and results

* `Furling.rouqData`: the generators of `g` as a `RouqData`.
* `Furling.endBlk`, `Furling.liftL`, `Furling.IsPath`: the endpoint, the weighted word of `g̃`
  and the relevance condition of a path given by its labels.
* `Furling.pgen`, `Furling.pgen_ext`, `Furling.pgen_wdot`.
* `KLR.isUnit_ncEval`: a polynomial with unit constant term evaluated at pairwise commuting
  nilpotent elements is a unit.
-/

noncomputable section

namespace Categorification.KLR

open MvPolynomial

open scoped IsMulCommutative in
/-- A polynomial whose constant term is a unit, evaluated at pairwise commuting nilpotent
elements, is a unit. -/
theorem isUnit_ncEval {k A : Type*} [CommRing k] [Ring A] [Algebra k A] {n : ℕ}
    (y : Fin n → A) (hc : ∀ a b, Commute (y a) (y b)) (hn : ∀ a, IsNilpotent (y a))
    (p : MvPolynomial (Fin n) k) (hp : IsUnit (constantCoeff p)) : IsUnit (ncEval y p) := by
  set R := Algebra.adjoin k (Set.range y)
  have := Algebra.isMulCommutative_adjoin k (s := Set.range y)
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _; exact hc a b)
  let y' : Fin n → R := fun a => ⟨y a, Algebra.subset_adjoin ⟨a, rfl⟩⟩
  have hval : ncEval y p = R.val (ncEval y' p) := by
    simp only [ncEval, Finsupp.sum, map_sum, map_mul, AlgHom.commutes, map_list_prod,
      List.map_ofFn, Function.comp_def, map_pow]
    rfl
  have haeval : ncEval y' p = aeval y' p := by
    simp only [ncEval, aeval_def, eval₂]
    refine Finsupp.sum_congr fun s _ => ?_
    rw [List.prod_ofFn, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [hval, haeval]
  refine IsUnit.map R.val ?_
  let N := nilradical R
  have hX : ((Ideal.Quotient.mkₐ k N).comp (aeval y')) = aeval (fun _ => 0) := by
    refine MvPolynomial.algHom_ext fun a => ?_
    simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_nilradical.2 (by
      obtain ⟨m, hm⟩ := hn a
      exact ⟨m, Subtype.ext (by simpa using hm)⟩))
  have hmem : aeval y' p - algebraMap k R (constantCoeff p) ∈ N := by
    rw [← Ideal.Quotient.eq]
    have := congrArg (· p) hX
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, aeval_zero'] at this
    rw [this, ← Ideal.Quotient.mkₐ_eq_mk k, AlgHom.commutes]
  have hu : IsUnit (algebraMap k R (constantCoeff p)) := hp.map _
  have := (mem_nilradical.1 hmem).isUnit_add_left_of_commute hu (Commute.all _ _)
  rwa [add_sub_cancel] at this

end Categorification.KLR

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

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

/-! ## The generators of `g` -/

/-- **The generators of `g`** (Webster, arXiv:1603.06311v3, Lemma `lem:g-action`): the
categories `Furling.obj`, the 1-morphisms `E_i = ⊕_{a over i} E_a`, the dots `ϖ_a(y)` and the
crossings `Furling.cross`. -/
abbrev rouqData : RouqData (B := LinearCat.{wk, max u₁ v₁, max u₁ u₂} k) RD where
  obj := obj Φ S
  E i _ _ h := E Φ S i h
  dot i _ _ h := dot Φ S D.pw i h
  cross _ _ _ _ _ _ h₁ h₂ h₃ h₄ := cross Φ S D h₁ h₂ h₃ h₄

/-! ## Paths -/

/-- The endpoint `β + a_{n-1} + ⋯ + a_0` of the path from `β` with labels `a_0, …, a_{n-1}`
(the head of the list is the last edge). -/
def endBlk (β : J →₀ ℤ) : List J → J →₀ ℤ
  | [] => β
  | a :: Ps => endBlk β Ps + Finsupp.single a 1

/-- The weighted word of `g̃` of the path from `β` with labels `Ps`. -/
def liftL (β : J →₀ ℤ) : List J → List (J × Xc)
  | [] => []
  | a :: Ps => (a, Φ.wtT (endBlk β Ps)) :: liftL β Ps

omit [DecidableEq I] [DecidableEq J] in
theorem wValid_liftL (β : J →₀ ℤ) :
    ∀ (Ps : List J), wValid RDc (Φ.wtT β) (liftL Φ β Ps) (Φ.wtT (endBlk β Ps))
  | [] => rfl
  | a :: Ps => ⟨wValid_liftL β Ps, Φ.wtT_add_single _ a⟩

omit [DecidableEq I] [DecidableEq J] in
theorem wValid_liftL_of_eq (β : J →₀ ℤ) (Ps : List J) {x : J →₀ ℤ} (hx : endBlk β Ps = x) :
    wValid RDc (Φ.wtT β) (liftL Φ β Ps) (Φ.wtT x) := by
  subst hx; exact wValid_liftL Φ β Ps

/-- The path from `β` with labels `Ps` follows the colours of the weighted word `L` of `g` and
consists of relevant edges. -/
def IsPath (β : J →₀ ℤ) : List (I × X) → List J → Prop
  | [], [] => True
  | (c, _) :: L, a :: Ps => IsPath β L Ps ∧ Φ.π a = c ∧ Φ.rel (endBlk β Ps) a
  | [], _ :: _ => False
  | _ :: _, [] => False

omit [DecidableEq I] [DecidableEq J] in
theorem wtG_endBlk (β : J →₀ ℤ) {μ : X} (hβ : Φ.wtG β = μ) :
    ∀ (L : List (I × X)) (Ps : List J) {μ' : X}, wValid RD μ L μ' → IsPath Φ β L Ps →
      Φ.wtG (endBlk β Ps) = μ'
  | [], [], _, hL, _ => hβ.trans hL
  | (_, _) :: L, _ :: Ps, _, hL, hP => by
    rw [endBlk, ← Φ.wtG_add_single, wtG_endBlk β hβ L Ps hL.1 hP.1, hP.2.1, hL.2]
  | [], _ :: _, _, _, hP => hP.elim
  | _ :: _, [], _, _, hP => hP.elim

/-- The edge `endBlk β Ps →a→` of a path. -/
abbrev pathEdge {μ : X} (β : Φ.Blk μ) (c : I) (ν : X) (L : List (I × X)) (a : J)
    (Ps : List J) (hL : wValid RD μ L ν) (hP : IsPath Φ β.1 ((c, ν) :: L) (a :: Ps)) :
    Φ.Edge c ν :=
  ⟨(⟨endBlk β.1 Ps, wtG_endBlk Φ β.1 β.2 L Ps hL hP.1⟩, a), hP.2.1, hP.2.2⟩

variable {μ : X} (M : ∀ β : Φ.Blk μ, blkCat Φ S β.1)

/-- **The generator of a word of `g` on the summand of a path**: from the word of `g̃` of the
path from `β` with labels `Ps` applied to `M β`, to the word of `g` applied to `M`, at the
endpoint `δ` of the path. -/
def pgen (β : Φ.Blk μ) : ∀ (L : List (I × X)) (Ps : List J) (μ' : X) (hL : wValid RD μ L μ')
    (_ : IsPath Φ β.1 L Ps) (δ : Φ.Blk μ') (hδ : endBlk β.1 Ps = δ.1),
    (S.wcell (Φ.wtT β.1) (liftL Φ β.1 Ps) (Φ.wtT δ.1)
        (wValid_liftL_of_eq Φ β.1 Ps hδ)).obj.obj (M β) ⟶
      (((rouqData Φ S D).wcell μ L μ' hL).obj.obj M) δ
  | [], [], μ', hL, _, δ, hδ => by
    obtain rfl : μ = μ' := hL
    obtain rfl : β = δ := Subtype.ext hδ
    exact 𝟙 _
  | (c, ν) :: L, a :: Ps, _, hL, hP, δ, hδ =>
    (Ea Φ S hL.2 (pathEdge Φ β c ν L a Ps hL.1 hP) δ (Subtype.ext hδ)).map
        (pgen β L Ps ν hL.1 hP.1 (pathEdge Φ β c ν L a Ps hL.1 hP).src rfl) ≫
      genE Φ S c hL.2 (((rouqData Φ S D).wcell μ L ν hL.1).obj.obj M)
        ⟨pathEdge Φ β c ν L a Ps hL.1 hP, Subtype.ext hδ⟩
  | [], _ :: _, _, _, hP, _, _ => hP.elim
  | _ :: _, [], _, _, hP, _, _ => hP.elim

theorem pgen_nil (β : Φ.Blk μ) :
    pgen Φ S D M β [] [] μ rfl trivial β rfl = 𝟙 _ := rfl

theorem pgen_cons (β : Φ.Blk μ) (c : I) (ν : X) (L : List (I × X)) (a : J) (Ps : List J)
    {μ' : X} (hL : wValid RD μ ((c, ν) :: L) μ') (hP : IsPath Φ β.1 ((c, ν) :: L) (a :: Ps))
    (δ : Φ.Blk μ') (hδ : endBlk β.1 (a :: Ps) = δ.1) :
    pgen Φ S D M β ((c, ν) :: L) (a :: Ps) μ' hL hP δ hδ =
      (Ea Φ S hL.2 (pathEdge Φ β c ν L a Ps hL.1 hP) δ (Subtype.ext hδ)).map
          (pgen Φ S D M β L Ps ν hL.1 hP.1 (pathEdge Φ β c ν L a Ps hL.1 hP).src rfl) ≫
        genE Φ S c hL.2 (((rouqData Φ S D).wcell μ L ν hL.1).obj.obj M)
          ⟨pathEdge Φ β c ν L a Ps hL.1 hP, Subtype.ext hδ⟩ := rfl

/-- **Maps out of a word of `g` are determined on the generators of paths**, also after an
additive functor. -/
theorem pgen_ext {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] :
    ∀ (L : List (I × X)) {μ' : X} (hL : wValid RD μ L μ') (δ : Φ.Blk μ')
      (F : blkCat Φ S δ.1 ⥤ 𝒟) [F.Additive] {W : 𝒟}
      {g g' : F.obj ((((rouqData Φ S D).wcell μ L μ' hL).obj.obj M) δ) ⟶ W},
      (∀ (β : Φ.Blk μ) (Ps : List J) (hP : IsPath Φ β.1 L Ps) (hδ : endBlk β.1 Ps = δ.1),
        F.map (pgen Φ S D M β L Ps μ' hL hP δ hδ) ≫ g =
          F.map (pgen Φ S D M β L Ps μ' hL hP δ hδ) ≫ g') → g = g'
  | [], μ', hL, δ, F, _, W, g, g', h => by
    obtain rfl : μ = μ' := hL
    have := h δ [] trivial rfl
    erw [pgen_nil, F.map_id, Category.id_comp, Category.id_comp] at this
    exact this
  | (c, ν) :: L, μ', hL, δ, F, _, W, g, g', h => by
    refine map_biproduct_hom_ext F _ fun p => ?_
    obtain ⟨⟨⟨⟨s, hs⟩, a⟩, hπ, hr⟩, he⟩ := p
    refine pgen_ext L hL.1 ⟨s, hs⟩ (Ea Φ S hL.2 ⟨(⟨s, hs⟩, a), hπ, hr⟩ δ he ⋙ F)
      (g := F.map (genE Φ S c hL.2 _ ⟨⟨(⟨s, hs⟩, a), hπ, hr⟩, he⟩) ≫ g)
      (g' := F.map (genE Φ S c hL.2 _ ⟨⟨(⟨s, hs⟩, a), hπ, hr⟩, he⟩) ≫ g') ?_
    intro β Ps hP hδ
    obtain rfl : endBlk β.1 Ps = s := hδ
    have := h β (a :: Ps) ⟨hP, hπ, hr⟩ (congrArg Subtype.val he)
    refine Eq.trans ?_ (this.trans ?_)
    · exact (Category.assoc _ _ _).symm.trans (eq_whisker (F.map_comp _ _).symm g)
    · exact (eq_whisker (F.map_comp _ _) g').trans (Category.assoc _ _ _)

/-- **The dots of `g` on the generators of paths**: on the path with labels `Ps`, the dot of
`g` on the `r`-th letter is `ϖ_{Ps_r}(y)`, with `y` the dot on the `r`-th letter of the word of
`g̃` of the path. -/
theorem pgen_wdot (β : Φ.Blk μ) : ∀ (r : ℕ) (L : List (I × X)) (Ps : List J) (μ' : X)
    (hL : wValid RD μ L μ') (hP : IsPath Φ β.1 L Ps) (δ : Φ.Blk μ')
    (hδ : endBlk β.1 Ps = δ.1) (hr : r < Ps.length),
    pgen Φ S D M β L Ps μ' hL hP δ hδ ≫ ((rouqData Φ S D).wdot μ r L μ' hL).hom.app M δ =
      (Polynomial.aeval (End.of (S.wdot (Φ.wtT β.1) r (liftL Φ β.1 Ps) (Φ.wtT δ.1)
          (wValid_liftL_of_eq Φ β.1 Ps hδ))) (D.pw Ps[r])).hom.app (M β) ≫
        pgen Φ S D M β L Ps μ' hL hP δ hδ
  | 0, (c, ν) :: L, a :: Ps, μ', hL, hP, δ, hδ, _ => by
    have hw : Polynomial.aeval (End.of (S.wdot (Φ.wtT β.1) 0 (liftL Φ β.1 (a :: Ps))
        (Φ.wtT δ.1) (wValid_liftL_of_eq Φ β.1 (a :: Ps) hδ))) (D.pw (a :: Ps)[0]) =
        endWL k (S.wcell (Φ.wtT β.1) (liftL Φ β.1 Ps) (Φ.wtT (endBlk β.1 Ps))
          (wValid_liftL Φ β.1 Ps)) (S.E a (wt_tgt hL.2 (pathEdge Φ β c ν L a Ps hL.1 hP)
            (Subtype.ext hδ))) (Polynomial.aeval (End.of (S.dot a _)) (D.pw a)) :=
      Polynomial.aeval_algHom_apply (endWL k _ _) (End.of (S.dot a _)) (D.pw a)
    rw [hw, endWL_apply]
    refine (eq_whisker (pgen_cons Φ S D M β c ν L a Ps hL hP δ hδ) _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    have hd : ((rouqData Φ S D).wdot μ 0 ((c, ν) :: L) μ' hL).hom.app M δ =
        (dot Φ S D.pw c hL.2).hom.app (((rouqData Φ S D).wcell μ L ν hL.1).obj.obj M) δ := rfl
    refine (whisker_eq _ (whisker_eq _ hd)).trans ?_
    refine (whisker_eq _ (genE_dot Φ S D.pw c hL.2
      (((rouqData Φ S D).wcell μ L ν hL.1).obj.obj M)
      ⟨pathEdge Φ β c ν L a Ps hL.1 hP, Subtype.ext hδ⟩)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (eq_whisker
      ((Polynomial.aeval (End.of (S.dot a _)) (D.pw a)).hom.naturality _) _).trans ?_
    exact Category.assoc _ _ _
  | r + 1, (c, ν) :: L, a :: Ps, μ', hL, hP, δ, hδ, hr => by
    have hr' : r < Ps.length := Nat.lt_of_succ_lt_succ hr
    have hw : Polynomial.aeval (End.of (S.wdot (Φ.wtT β.1) (r + 1) (liftL Φ β.1 (a :: Ps))
        (Φ.wtT δ.1) (wValid_liftL_of_eq Φ β.1 (a :: Ps) hδ))) (D.pw (a :: Ps)[r + 1]) =
        endWR k (S.wcell (Φ.wtT β.1) (liftL Φ β.1 Ps) (Φ.wtT (endBlk β.1 Ps))
          (wValid_liftL Φ β.1 Ps)) (S.E a (wt_tgt hL.2 (pathEdge Φ β c ν L a Ps hL.1 hP)
            (Subtype.ext hδ)))
          (Polynomial.aeval (End.of (S.wdot (Φ.wtT β.1) r (liftL Φ β.1 Ps) _
            (wValid_liftL Φ β.1 Ps))) (D.pw Ps[r])) :=
      Polynomial.aeval_algHom_apply (endWR k _ _) (End.of (S.wdot (Φ.wtT β.1) r
        (liftL Φ β.1 Ps) _ (wValid_liftL Φ β.1 Ps))) (D.pw Ps[r])
    rw [hw, endWR_apply]
    refine (eq_whisker (pgen_cons Φ S D M β c ν L a Ps hL hP δ hδ) _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    have hd : ((rouqData Φ S D).wdot μ (r + 1) ((c, ν) :: L) μ' hL).hom.app M δ =
        (E Φ S c hL.2).obj.map (((rouqData Φ S D).wdot μ r L ν hL.1).hom.app M) δ := rfl
    refine (whisker_eq _ (whisker_eq _ hd)).trans ?_
    refine (whisker_eq _ (genE_natural Φ S hL.2
      (((rouqData Φ S D).wdot μ r L ν hL.1).hom.app M)
      ⟨pathEdge Φ β c ν L a Ps hL.1 hP, Subtype.ext hδ⟩)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (eq_whisker (Functor.map_comp _ _ _).symm _).trans ?_
    refine (eq_whisker ((Ea Φ S hL.2 (pathEdge Φ β c ν L a Ps hL.1 hP) δ
      (Subtype.ext hδ)).congr_map (pgen_wdot β r L Ps ν hL.1 hP.1 _ rfl hr')) _).trans ?_
    refine (eq_whisker (Functor.map_comp _ _ _) _).trans ?_
    exact Category.assoc _ _ _
  | 0, [], [], _, _, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | _ + 1, [], [], _, _, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | _, [], _ :: _, _, _, hP, _, _, _ => hP.elim
  | _, _ :: _, [], _, _, hP, _, _, _ => hP.elim

end Furling

end Categorification.TwoRep
