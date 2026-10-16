/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingIntertwine
import Categorification.KLR.Symmetries

/-!
# Furling: the KLR algebra of `g` through the unfurling homomorphism

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2.3, Lemma with
label `lem:g-action`, and §3.3, Lemma with label `lem:gamma-homo`. The generators of `g`
(`Furling.rouqData`) act on the words of weight `ν` through the free algebra on the generators
of `R(ν)` (`RouqData.klrActFree`). On the summand of a word of `g̃` of weight `ν̃` over `ν`
(a lift `s` of a word of `ν`, whose labels form a path of relevant edges from a block `β`), this
action is the action of the completed KLR algebra `R̂(ν̃)` of `g̃` on the image `γ(r)` under the
unfurling homomorphism `γ` (`Unfurling.freeGamma`): the generators of paths `Furling.pgen`
intertwine the two (`Furling.intertw_freeGamma`).

## Main definitions and results

* `Furling.evalBlk`: evaluation of the 1-morphisms of `g` at an object and a block.
* `Furling.lgen`: the generator of a path, on the summand of a lift of a word.
* `Furling.actG`, `Furling.actT`: the free algebra on the generators of `R(ν)` acting on the
  words of `g`, and through `γ` on the words of `g̃` of a lift.
* `KLR.ncEval_rename_of_commute`, `KLR.ncEval_pwAt_of_commute`: `ncEval` at pairwise commuting
  elements.
-/

noncomputable section

namespace Categorification.KLR

open MvPolynomial

open scoped IsMulCommutative in
/-- Evaluation of polynomials at pairwise commuting elements is an algebra homomorphism. -/
theorem exists_algHom_ncEval {k A : Type*} [CommRing k] [Ring A] [Algebra k A] {n : ℕ}
    (y : Fin n → A) (hc : ∀ a b, Commute (y a) (y b)) :
    ∃ φ : MvPolynomial (Fin n) k →ₐ[k] A, (∀ a, φ (X a) = y a) ∧ ∀ p, ncEval y p = φ p := by
  set R := Algebra.adjoin k (Set.range y)
  have := Algebra.isMulCommutative_adjoin k (s := Set.range y)
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _; exact hc a b)
  let y' : Fin n → R := fun a => ⟨y a, Algebra.subset_adjoin ⟨a, rfl⟩⟩
  refine ⟨R.val.comp (aeval y'), fun a => by simp [y'], fun p => ?_⟩
  have hval : ncEval y p = R.val (ncEval y' p) := by
    simp only [ncEval, Finsupp.sum, map_sum, map_mul, AlgHom.commutes, map_list_prod,
      List.map_ofFn, Function.comp_def, map_pow]
    rfl
  have haeval : ncEval y' p = aeval y' p := by
    simp only [ncEval, aeval_def, eval₂]
    refine Finsupp.sum_congr fun s _ => ?_
    rw [List.prod_ofFn, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [hval, haeval]
  rfl

/-- Renaming the variables of a polynomial evaluated at pairwise commuting elements. -/
theorem ncEval_rename_of_commute {k A : Type*} [CommRing k] [Ring A] [Algebra k A] {n n' : ℕ}
    (y : Fin n → A) (hc : ∀ a b, Commute (y a) (y b)) (f : Fin n' → Fin n)
    (p : MvPolynomial (Fin n') k) : ncEval y (rename f p) = ncEval (fun a => y (f a)) p := by
  obtain ⟨φ, hX, hφ⟩ := exists_algHom_ncEval (k := k) y hc
  rw [hφ, ← ncEval_algHom_X]
  simp only [hX]

/-- A one-variable polynomial in the `a`-th of pairwise commuting elements. -/
theorem ncEval_pwAt_of_commute {k A J : Type*} [CommRing k] [Ring A] [Algebra k A] {n : ℕ}
    (y : Fin n → A) (hc : ∀ a b, Commute (y a) (y b)) (pw : J → Polynomial k) (j : J)
    (a : Fin n) : ncEval y (Unfurling.pwAt pw j a) = Polynomial.aeval (y a) (pw j) := by
  obtain ⟨φ, hX, hφ⟩ := exists_algHom_ncEval (k := k) y hc
  rw [hφ, Unfurling.pwAt, ← Polynomial.aeval_algHom_apply, hX]

end Categorification.KLR

namespace Categorification.KLR.Diagram.MatEnd

open CategoryTheory

/-! ## Rows of matrices with one nonzero entry -/

section Plc

variable {C : Type*} [Category C] [Preadditive C] {ι : Type*} [DecidableEq ι] {Y : ι → C}

/-- The row with the single entry `f` in the column `c`. -/
def plc {W : C} (c : ι) (f : W ⟶ Y c) (t : ι) : W ⟶ Y t :=
  if h : c = t then f ≫ eqToHom (congrArg Y h) else 0

@[simp] theorem plc_self {W : C} (c : ι) (f : W ⟶ Y c) : plc c f c = f := by
  simp [plc]

theorem plc_of_ne {W : C} {c t : ι} (f : W ⟶ Y c) (h : c ≠ t) : plc c f t = 0 :=
  dite_eq_right h

theorem comp_plc {W W' : C} (x : W' ⟶ W) (c : ι) (f : W ⟶ Y c) (t : ι) :
    x ≫ plc c f t = plc c (x ≫ f) t := by
  unfold plc; split_ifs <;> simp

theorem plc_add {W : C} (c : ι) (f g : W ⟶ Y c) (t : ι) :
    plc c (f + g) t = plc c f t + plc c g t := by
  unfold plc; split_ifs <;> simp

theorem plc_neg {W : C} (c : ι) (f : W ⟶ Y c) (t : ι) : plc c (-f) t = -plc c f t := by
  unfold plc; split_ifs <;> simp

@[simp] theorem plc_zero {W : C} (c : ι) (t : ι) : plc c (0 : W ⟶ Y c) t = 0 := by
  unfold plc; split_ifs <;> simp

theorem plc_congr {W : C} {c c' : ι} (h : c = c') (f : W ⟶ Y c) (t : ι) :
    plc c f t = plc c' (f ≫ eqToHom (congrArg Y h)) t := by
  subst h; simp

theorem map_plc {D : Type*} [Category D] [Preadditive D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {W : C} (c : ι) (f : W ⟶ Y c) (t : ι) :
    F.map (plc c f t) = plc (Y := fun i => F.obj (Y i)) c (F.map f) t := by
  unfold plc; split_ifs <;> simp [eqToHom_map]

omit [DecidableEq ι] in
theorem rect_eq_plc [DecidableEq ι] {τ : Type*} {Z : τ → C} (d : τ → ι)
    (G : ∀ s, Z s ⟶ Y (d s)) (s : τ) (t : ι) : rect d G s t = plc (d s) (G s) t := rfl

theorem single_apply_plc (i j : ι) (f : Y i ⟶ Y j) (i' t : ι) :
    single i j f i' t = if h : i' = i then plc j (eqToHom (congrArg Y h) ≫ f) t else 0 := by
  unfold single plc
  by_cases h₁ : i' = i
  · subst h₁; by_cases h₂ : t = j
    · subst h₂; simp
    · simp [h₂, Ne.symm h₂]
  · simp [h₁]

theorem sum_single_apply [Fintype ι] (g : ι → ι) (a : ∀ i, Y i ⟶ Y (g i)) (i' t : ι) :
    (∑ i, single i (g i) (a i)) i' t = plc (g i') (a i') t := by
  rw [sum_apply, Finset.sum_eq_single i']
  · rw [single_apply_plc, dite_eq_left rfl, eqToHom_refl, Category.id_comp]
  · intro i _ hi; rw [single_apply_plc, dite_eq_right (Ne.symm hi)]
  · simp

theorem sum_filter_single_apply [Fintype ι] (T : Finset ι) (g : ι → ι)
    (a : ∀ i, Y i ⟶ Y (g i)) (i' t : ι) :
    (∑ i ∈ T, single i (g i) (a i)) i' t = if i' ∈ T then plc (g i') (a i') t else 0 := by
  rw [sum_apply]
  split_ifs with hT
  · rw [Finset.sum_eq_single i']
    · rw [single_apply_plc, dite_eq_left rfl, eqToHom_refl, Category.id_comp]
    · intro i _ hi; rw [single_apply_plc, dite_eq_right (Ne.symm hi)]
    · intro h; exact absurd hT h
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [single_apply_plc, dite_eq_right (fun (h : i' = i) => hT (by rw [h]; exact hi))]

theorem sum_plc_comp_rect {τ : Type*} [Fintype τ] [DecidableEq τ] {Z : τ → C} (d : τ → ι)
    (G : ∀ s, Z s ⟶ Y (d s)) {W : C} (c : τ) (x : W ⟶ Z c) (t : ι) :
    ∑ u, plc c x u ≫ rect d G u t = plc (d c) (x ≫ G c) t := by
  rw [Finset.sum_eq_single c]
  · rw [plc_self, rect_eq_plc, comp_plc]
  · intro u _ hu; rw [plc_of_ne _ (Ne.symm hu), Limits.zero_comp]
  · simp

end Plc

section MapAlg

variable {k : Type*} [CommRing k] {C D : Type*} [Category C] [Preadditive C] [Linear k C]
  [Category D] [Preadditive D] [Linear k D] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mapAlg_single (F : C ⥤ D) [F.Additive] [F.Linear k] (X : ι → C) (i j : ι)
    (f : X i ⟶ X j) : mapAlg k F X (single i j f) = single i j (F.map f) := by
  ext i' j'
  simp only [mapAlg_apply, single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp

end MapAlg

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

/-! ## Evaluation at a block -/

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem _root_.Categorification.TwoRep.LinearCat.id_hom_app {C D' : LinearCat k}
    (F : C ⟶ D') (x : (C : Type _)) : (𝟙 F : F ⟶ F).hom.app x = 𝟙 _ := rfl

/-- The evaluation of the 1-morphisms `obj λ ⟶ obj λ'` of `g` at an object `M` and a block
`δ` of weight `λ'`. -/
@[simps] def evalBlk {l l' : X} (M : (obj Φ S l : Type _)) (δ : Φ.Blk l') :
    (obj Φ S l ⟶ obj Φ S l') ⥤ (blkCat Φ S δ.1 : Type u₂) where
  obj F := (F.obj.obj M) δ
  map η := η.hom.app M δ
  map_id _ := rfl
  map_comp _ _ := rfl

instance {l l' : X} (M : (obj Φ S l : Type _)) (δ : Φ.Blk l') : (evalBlk Φ S M δ).Additive where
  map_add := rfl

instance {l l' : X} (M : (obj Φ S l : Type _)) (δ : Φ.Blk l') :
    (evalBlk Φ S M δ).Linear k where
  map_smul _ _ := rfl

/-- The evaluation of the 1-morphisms of `g̃` with target a block category at an object. -/
@[simps] def evalSrc {x : Xc} {β' : J →₀ ℤ} (N : (S.obj x : Type u₂)) :
    (S.obj x ⟶ blkCat Φ S β') ⥤ (blkCat Φ S β' : Type u₂) where
  obj F := F.obj.obj N
  map η := η.hom.app N
  map_id _ := rfl
  map_comp _ _ := rfl

instance {x : Xc} {β' : J →₀ ℤ} (N : (S.obj x : Type u₂)) : (evalSrc Φ S (β' := β') N).Additive where
  map_add := rfl

instance {x : Xc} {β' : J →₀ ℤ} (N : (S.obj x : Type u₂)) :
    (evalSrc Φ S (β' := β') N).Linear k where
  map_smul _ _ := rfl

/-! ## Lifts of words -/

section Lifts

variable {Φ D} (hπ : ∀ a, Φ.π a = D.π a)
include hπ

omit [DecidableEq I] [DecidableEq J] in
theorem word_down {ν : Multiset I} {ν' : Multiset J} (hν : ν'.map D.π = ν) (s : Seq ν') :
    word (Unfurling.down D.π hν s) = (word s).map Φ.π := by
  apply List.ext_getElem (by simp [Unfurling.card_eq D.π hν])
  intro n h₁ h₂
  simp [hπ]

omit [DecidableEq I] [DecidableEq J] in
theorem wordL_down (μ : X) {ν : Multiset I} {ν' : Multiset J} (hν : ν'.map D.π = ν)
    (s : Seq ν') :
    wordL RD μ (Unfurling.down D.π hν s) = canon RD μ ((word s).map Φ.π) := by
  rw [wordL, word_down hπ]

omit [DecidableEq I] [DecidableEq J] in
theorem isPath_down (μ : X) {ν : Multiset I} {ν' : Multiset J} (hν : ν'.map D.π = ν)
    (β : J →₀ ℤ) (s : Seq ν') (h : IsRel Φ β (word s)) :
    IsPath Φ β (wordL RD μ (Unfurling.down D.π hν s)) (word s) := by
  rw [wordL_down hπ]; exact (isPath_canon_iff Φ β μ _).2 h

end Lifts

/-! ## Irrelevant paths -/

section Zero

variable {Φ S}
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
include hzero

omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] [DecidableEq I] [DecidableEq J] in
/-- The word of `g̃` of a path with an irrelevant edge vanishes, if the 1-morphisms of the
irrelevant edges do. -/
theorem isZero_wcell_liftL (β : J →₀ ℤ) (N : (S.obj (Φ.wtT β) : Type u₂)) :
    ∀ (Ps : List J) {x' : Xc} (h : wValid RDc (Φ.wtT β) (liftL Φ β Ps) x'),
      ¬ IsRel Φ β Ps → IsZero ((S.wcell (Φ.wtT β) (liftL Φ β Ps) x' h).obj.obj N)
  | [], _, _, hr => absurd trivial hr
  | a :: Ps, _, h, hr => by
    by_cases h₁ : IsRel Φ β Ps
    · exact Functor.map_isZero (LinearCat.evalAt _) (hzero _ a h.2 fun h₂ => hr ⟨h₁, h₂⟩)
    · exact Functor.map_isZero (S.E a h.2).obj (isZero_wcell_liftL β N Ps h.1 h₁)

end Zero

/-! ## The generators of the summands of lifts -/

section Gen

variable {Φ D} (hπ : ∀ a, Φ.π a = D.π a) (μ : X) {ν : Multiset I}
  (M : ∀ β : Φ.Blk μ, blkCat Φ S β.1) (δ : Φ.Blk (wtop RD μ ν)) (β : Φ.Blk μ)
  (ν' : Unfurling.Lift D ν) (hδ : β.1 + blkSum ν'.1 = δ.1)

omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] [DecidableEq I] [DecidableEq J] in
include hδ in
/-- The target weight of the words of `g̃` of a lift. -/
theorem wtop_lift : wtop RDc (Φ.wtT β.1) ν'.1 = Φ.wtT δ.1 :=
  (wtT_add_blkSum Φ β.1 ν'.1).symm.trans (congrArg Φ.wtT hδ)

open Classical in
/-- **The generator of the summand of a lift**: for a lift `s` of weight `ν̃` whose labels form
a path of relevant edges from `β` to `δ`, the generator `pgen` of that path, from the word of
`g̃` of `s` applied to `M β` to the word of `g` of `down s` applied to `M`, at `δ`; zero if an
edge is irrelevant. -/
def lgen (s : Seq ν'.1) :
    (S.wordCellAt (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) s).obj.obj (M β) ⟶
      (evalBlk Φ S M δ).obj ((rouqData Φ S D).wordCell μ (Unfurling.down D.π ν'.2 s)) :=
  if h : IsRel Φ β.1 (word s) then
    (eqToHom (S.wcell_congr (Φ.wtT β.1) (liftL_eq_canon Φ β.1 (word s)).symm _
        (wValid_liftL_of_eq Φ β.1 (word s) ((endBlk_word β.1 s).trans hδ)))).hom.app (M β) ≫
      pgen Φ S D M β (wordL RD μ (Unfurling.down D.π ν'.2 s)) (word s) (wtop RD μ ν)
        (wValid_wordL μ _) (isPath_down hπ μ ν'.2 β.1 s h) δ ((endBlk_word β.1 s).trans hδ)
  else 0

open Classical in
theorem lgen_of_isRel (s : Seq ν'.1) (h : IsRel Φ β.1 (word s)) :
    lgen S hπ μ M δ β ν' hδ s =
      (eqToHom (S.wcell_congr (Φ.wtT β.1) (liftL_eq_canon Φ β.1 (word s)).symm _
          (wValid_liftL_of_eq Φ β.1 (word s) ((endBlk_word β.1 s).trans hδ)))).hom.app (M β) ≫
        pgen Φ S D M β (wordL RD μ (Unfurling.down D.π ν'.2 s)) (word s) (wtop RD μ ν)
          (wValid_wordL μ _) (isPath_down hπ μ ν'.2 β.1 s h) δ ((endBlk_word β.1 s).trans hδ) :=
  by unfold lgen; split_ifs; rfl

omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] [DecidableEq I] [DecidableEq J] in
include hδ in
theorem isZero_wordCellAt
    (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
      IsZero (S.E a h)) (s : Seq ν'.1) (h : ¬ IsRel Φ β.1 (word s)) :
    IsZero ((S.wordCellAt (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) s).obj.obj (M β)) := by
  have := isZero_wcell_liftL hzero β.1 (M β) (word s)
    (wValid_liftL_of_eq Φ β.1 (word s) ((endBlk_word β.1 s).trans hδ)) h
  rwa [S.wcell_congr (Φ.wtT β.1) (liftL_eq_canon Φ β.1 (word s))] at this

/-! ## The two actions -/

/-- The free algebra on the generators of `R(ν)` acting on the words of `g` at `M`, `δ`. -/
def actG : FreeAlgebra k (KLR.Gen ν) →ₐ[k]
    MatEnd (fun t : Seq ν => (evalBlk Φ S M δ).obj ((rouqData Φ S D).wordCell μ t)) :=
  (MatEnd.mapAlg k (evalBlk Φ S M δ) _).comp ((rouqData Φ S D).klrActFree k μ ν)

variable {S} (H : RouqUpKLR S (Unfurling.unfQ (k := k) D.arrows))
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))

/-- The free algebra on the generators of `R(ν)` acting through `γ` on the words of `g̃` of the
lifts of weight `ν̃`, at `M β`. -/
def actT : FreeAlgebra k (KLR.Gen ν) →ₐ[k]
    MatEnd (fun s : Seq ν'.1 =>
      (S.wordCellAt (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) s).obj.obj (M β)) :=
  (MatEnd.mapAlg k (evalSrc Φ S (β' := δ.1) (M β)) _).comp
    ((RouqFamily.klrComplAt H (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) hnil
        (Unfurling.unfGrading (k := k) D.arrows)).comp
      ((Pi.evalAlgHom k _ ν').comp (Unfurling.freeGamma D)))

theorem actG_ι (g : KLR.Gen ν) :
    actG S μ M δ (FreeAlgebra.ι k g) =
      MatEnd.mapAlg k (evalBlk Φ S M δ) _ ((rouqData Φ S D).klrGen μ ν g) := by
  simp [actG, RouqData.klrActFree]

omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] in
theorem actT_ι (g : KLR.Gen ν) :
    actT μ M δ β ν' hδ H hnil (FreeAlgebra.ι k g) =
      MatEnd.mapAlg k (evalSrc Φ S (β' := δ.1) (M β)) _
        (RouqFamily.klrComplAt H (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) hnil
          (Unfurling.unfGrading (k := k) D.arrows) (Unfurling.genImage D ν'.2 g)) := by
  change MatEnd.mapAlg k (evalSrc Φ S (β' := δ.1) (M β)) _
    (RouqFamily.klrComplAt H (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) hnil
      (Unfurling.unfGrading (k := k) D.arrows) (Unfurling.freeGamma D (FreeAlgebra.ι k g) ν')) = _
  rw [Unfurling.freeGamma, FreeAlgebra.lift_ι_apply]

variable (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
include hzero

/-- The idempotents of `R(ν)` (Webster, `lem:gamma-homo`, `e_i ↦ ∑_{π ∘ t = i} e_t`). -/
theorem intertw_idem (i : Seq ν) :
    MatEnd.Intertw (Unfurling.down D.π ν'.2) (lgen S hπ μ M δ β ν' hδ)
      (actG S μ M δ (FreeAlgebra.ι k (.idem i))) (actT μ M δ β ν' hδ H hnil (FreeAlgebra.ι k (.idem i))) := by
  intro s t
  by_cases hr : IsRel Φ β.1 (word s)
  swap
  · exact (isZero_wordCellAt S μ M δ β ν' hδ hzero s hr).eq_of_src _ _
  rw [actG_ι, actT_ι, MatEnd.mapAlg_apply]
  simp only [RouqData.klrGen, RouqData.wordE, Unfurling.genImage, map_sum,
    RouqFamily.klrComplAt_toCompletion, RouqFamily.klrActAt_e, MatEnd.mapAlg_single,
    MatEnd.sum_filter_single_apply (g := fun x => x),
    MatEnd.single_apply_plc, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hd : Unfurling.down D.π ν'.2 s = i
  · subst hd
    simp only [dite_true, ite_true, eqToHom_refl, Category.id_comp]
    rw [MatEnd.map_plc (evalBlk Φ S M δ), MatEnd.comp_plc, CategoryTheory.Functor.map_id,
      Category.comp_id]
    erw [CategoryTheory.Functor.map_id, MatEnd.sum_plc_comp_rect, Category.id_comp]
  · simp only [hd, dite_false, ite_false, Functor.map_zero, Limits.comp_zero]
    exact (Finset.sum_eq_zero fun _ _ => Limits.zero_comp).symm

end Gen

end Furling

end Categorification.TwoRep
