/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingIntertwine
import Categorification.KLR.Symmetries
import Categorification.TwoRep.RouqKLRRelations

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
* `Furling.intertw_freeGamma`: the generators of lifts intertwine the two actions.
* `Furling.klrActFree_rel`, `Furling.klrAct` (Webster, `lem:g-action`): the action of `g`
  respects the relations of `R(ν)`, hence `R(ν)` acts on the words of `g`. The hypotheses are
  those of the cover: the mixed relations `RouqUpKLR` of `g̃` for the matrices of the unfurling
  datum, nilpotent dots, and vanishing of the generators of `g̃` along irrelevant edges.
* `Furling.respectsKLR`, `Furling.rouqUpKLR`: the same statement as `RouqData.RespectsKLR`;
  hence every Rouquier family with the generators of `g` satisfies the mixed relations
  `RouqUpKLR` for `Q` (Brundan, Definition 1.1, (1.2)–(1.4)).
* `KLR.ncEval_rename_of_commute`, `KLR.ncEval_pwAt_of_commute`: `ncEval` at pairwise commuting
  elements.
-/

noncomputable section

namespace Categorification.KLR

open MvPolynomial

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

theorem single_self_mul_apply [Fintype ι] (i : ι) (c : Y i ⟶ Y i) (g : MatEnd Y) (s t : ι) :
    (single i i c * g) s t = plc i (g s i ≫ c) t := by
  rw [mul_apply, Finset.sum_eq_single i]
  · rw [single_apply_plc, dite_eq_left rfl, eqToHom_refl, Category.id_comp, comp_plc]
  · intro u _ hu; rw [single_apply_plc, dite_eq_right hu, Limits.comp_zero]
  · simp

theorem sum_plc_comp_plc [Fintype ι] {W : C} (c : ι) (f : W ⟶ Y c) (g : ∀ u, Y u ⟶ Y u)
    (t : ι) : ∑ u, plc u (plc c f u ≫ g u) t = plc c (f ≫ g c) t := by
  rw [Finset.sum_eq_single c]
  · rw [plc_self]
  · intro u _ hu; rw [plc_of_ne _ (Ne.symm hu), Limits.zero_comp, plc_zero]
  · simp

theorem sum_map_plc_add_comp_rect {D : Type*} [Category D] [Preadditive D] (F : C ⥤ D)
    [F.Additive] {τ : Type*} [Fintype τ] [DecidableEq τ] {Z : τ → C} {Y' : ι → D} (d : τ → ι)
    (G : ∀ s, F.obj (Z s) ⟶ Y' (d s)) {W : C} (a b : τ) (f : W ⟶ Z a) (g : W ⟶ Z b) (t : ι) :
    ∑ u, F.map (plc a f u + plc b g u) ≫ rect d G u t =
      plc (d a) (F.map f ≫ G a) t + plc (d b) (F.map g ≫ G b) t := by
  simp only [Functor.map_add, map_plc, Preadditive.add_comp, Finset.sum_add_distrib,
    sum_plc_comp_rect]

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

/-! ## The crossings of `g̃` under the unfurling homomorphism -/

section CrossImage

open RouqFamily

variable (H : RouqUpKLR S (Unfurling.unfQ (k := k) D.arrows))
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
  (μ : Xc) {ν' : Multiset J} (x' : Xc) (e : wtop RDc μ ν' = x')
  {ν : Multiset I} (hν : ν'.map D.π = ν) {j : ℕ} (h : j + 1 < Multiset.card ν)

/-- The dots on the strands `j`, `j + 1` of the word of `u`. -/
def dotPair (u : Seq ν') : Fin 2 → End (S.wordCellAt μ x' e u) :=
  ![S.wordDotAt μ x' e u (Unfurling.posL D hν h), S.wordDotAt μ x' e u (Unfurling.posR D hν h)]

/-- The coefficient of the crossing in `γ(ψ_j)` on the output summand `u`. -/
def swapCoef (u : Seq ν') : End (S.wordCellAt μ x' e u) :=
  Unfurling.swapW D (D.π (u.lbl (Unfurling.posL D hν h)) = D.π (u.lbl (Unfurling.posR D hν h)))
    (u.lbl (Unfurling.posL D hν h)) (u.lbl (Unfurling.posR D hν h)) (dotPair S D μ x' e hν h u)

open Classical in
/-- The coefficient of the idempotent in `γ(ψ_j)` on the output summand `u`: nonzero only for
distinct labels of the same colour. -/
def selfCoef (u : Seq ν') : End (S.wordCellAt μ x' e u) :=
  if D.π (u.lbl (Unfurling.posL D hν h)) = D.π (u.lbl (Unfurling.posR D hν h)) ∧
      u.lbl (Unfurling.posL D hν h) ≠ u.lbl (Unfurling.posR D hν h) then
    Unfurling.selfW D (u.lbl (Unfurling.posL D hν h)) (u.lbl (Unfurling.posR D hν h))
      (dotPair S D μ x' e hν h u)
  else 0

omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] [DecidableEq I] [DecidableEq J] in
theorem commute_wordDotAt (u : Seq ν') (a b : Fin (Multiset.card ν')) :
    Commute (S.wordDotAt μ x' e u a) (S.wordDotAt μ x' e u b) := by
  exact RouqData.wdot_comm _ _ _ _ _ _ _

omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] [DecidableEq I] [DecidableEq J] in
theorem ncEval_rename_posLR (u : Seq ν') (p : MvPolynomial (Fin 2) k) :
    ncEval (fun a => S.wordDotAt μ x' e u a)
        (MvPolynomial.rename ![Unfurling.posL D hν h, Unfurling.posR D hν h] p) =
      ncEval (dotPair S D μ x' e hν h u) p := by
  rw [ncEval_rename_of_commute _ (commute_wordDotAt S μ x' e u)]
  congr 1
  funext a; fin_cases a <;> rfl

omit [DecidableEq I] [DecidableEq J] in
theorem rename_pwAt_sub (a b : J) :
    MvPolynomial.rename ![Unfurling.posL D hν h, Unfurling.posR D hν h]
        (Unfurling.pwAt D.pw a 0 - Unfurling.pwAt D.pw b 1 : MvPolynomial (Fin 2) k) =
      Unfurling.pwAt D.pw a (Unfurling.posL D hν h) - Unfurling.pwAt D.pw b (Unfurling.posR D hν h) := by
  simp only [Unfurling.pwAt, map_sub, ← Polynomial.aeval_algHom_apply, MvPolynomial.rename_X]
  rfl

omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] in
include H hnil in
/-- The image of `γ(ψ_j)` on the output summand `u` (`Unfurling.crossImage`): the crossing
followed by `swapCoef`, plus `selfCoef` on `u`. -/
theorem klrComplAt_crossImage (u : Seq ν') :
    klrComplAt H μ x' e hnil (Unfurling.unfGrading (k := k) D.arrows)
        (Unfurling.crossImage D hν h u) =
      MatEnd.single u u (swapCoef S D μ x' e hν h u) * klrActAt H μ x' e (KLRAlgebra.ψ j) +
        MatEnd.single u u (selfCoef S D μ x' e hν h u) := by
  have hX := Unfurling.unf_degX_pos (k := k) D
  unfold Unfurling.crossImage swapCoef selfCoef Unfurling.swapW
  by_cases hc : D.π (u.lbl (Unfurling.posL D hν h)) = D.π (u.lbl (Unfurling.posR D hν h))
  · by_cases hab : u.lbl (Unfurling.posL D hν h) = u.lbl (Unfurling.posR D hν h)
    · simp only [hab, dite_true, ite_true, ne_eq, not_true_eq_false, and_false, ite_false,
        MatEnd.single_zero, add_zero]
      rw [map_mul, klrComplAt_toCompletion,
        (klrComplAt_seriesAt_invOfUnit H μ x' e hnil hX u _ _ ?_).2, ncEval_rename_posLR]
      rw [Units.val_mk0, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        MvPolynomial.coeff_coe, ← MvPolynomial.constantCoeff_eq,
        MvPolynomial.constantCoeff_rename]
    · simp only [hc, dite_true, ite_true, hab, dite_false, ite_false, ne_eq, not_false_eq_true,
        and_self, Unfurling.selfW]
      have hr := rename_pwAt_sub (k := k) D hν h (u.lbl (Unfurling.posL D hν h))
        (u.lbl (Unfurling.posR D hν h))
      rw [map_mul, (klrComplAt_seriesAt_invOfUnit H μ x' e hnil hX u _ _ ?_).2, map_sub, map_sub,
        klrComplAt_toCompletion, klrComplAt_toCompletion, klrActAt_e, mul_sub,
        MatEnd.single_mul_single_self, Category.id_comp, ← hr, ncEval_rename_posLR,
        MatEnd.single_neg, neg_mul]
      · abel
      · rw [Units.val_mk0, ← hr, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          MvPolynomial.coeff_coe, ← MvPolynomial.constantCoeff_eq,
          MvPolynomial.constantCoeff_rename, Unfurling.constantCoeff_pwAt_sub]
  · simp only [hc, dite_false, ite_false, false_and, MatEnd.single_zero, add_zero]
    rw [klrComplAt_toCompletion, map_mul (klrActAt H μ x' e) _ (KLRAlgebra.ψ j),
      klrActAt_pol_mul_e, ncEval_rename_posLR]

omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] in
include H hnil in
/-- The row of `γ(ψ_j)` at the word of `s`: the crossing to `sadj j • s` followed by
`swapCoef`, plus `selfCoef` on `s`. -/
theorem klrComplAt_sum_crossImage_apply (s u' : Seq ν') :
    klrComplAt H μ x' e hnil (Unfurling.unfGrading (k := k) D.arrows)
        (∑ u, Unfurling.crossImage D hν h u) s u' =
      MatEnd.plc (TypeA.sadj (Multiset.card ν') j • s)
          (S.wordCrossAt μ x' e s j ≫ swapCoef S D μ x' e hν h (TypeA.sadj (Multiset.card ν') j • s)) u' +
        MatEnd.plc s (selfCoef S D μ x' e hν h s) u' := by
  rw [map_sum, Finset.sum_congr rfl fun u _ => klrComplAt_crossImage S D H hnil μ x' e hν h u,
    Finset.sum_add_distrib, MatEnd.add_apply, MatEnd.sum_single_apply (g := fun x => x),
    MatEnd.sum_apply]
  simp only [MatEnd.single_self_mul_apply, klrActAt_cross,
    MatEnd.sum_single_apply (g := fun t => TypeA.sadj (Multiset.card ν') j • t)]
  rw [MatEnd.sum_plc_comp_plc]

end CrossImage

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

/-! ## The two terms of a crossing, transported -/

section CrossTerms

variable {Φ S D} {μ : X} (M : ∀ β : Φ.Blk μ, blkCat Φ S β.1)

/-- The term of the crossing of `g` to the swapped path (`pcrossSwap`), after an identification
of the word of `g̃` of the source with `Lc`, as the crossing of `Lc` with the coefficient
`swapW` in the dots of the swapped word `Lc'`. -/
theorem pcrossSwap_eq (β : Φ.Blk μ) (j : ℕ) (L : List (I × X)) (Ps : List J) (μ' : X)
    (hL : wValid RD μ L μ') (δ : Φ.Blk μ') (hδ : endBlk β.1 Ps = δ.1) (hj : j + 1 < Ps.length)
    (Lc : List (J × Xc)) (eS : Lc = liftL Φ β.1 Ps) (hc : wValid RDc (Φ.wtT β.1) Lc (Φ.wtT δ.1))
    (Lc' : List (J × Xc)) (eC : wswap RDc j Lc = Lc') (hc' : wValid RDc (Φ.wtT β.1) Lc' (Φ.wtT δ.1))
    (L' : List (I × X)) (eL : wswap RD j L = L') (hL' : wValid RD μ L' μ')
    (Ps' : List J) (eP : lswap j Ps = Ps') (hP' : IsPath Φ β.1 L' Ps')
    (hδ' : endBlk β.1 Ps' = δ.1) (eLift : Lc' = liftL Φ β.1 Ps')
    (same : Prop) [Decidable same] (hsame : same ↔ Φ.π Ps[j] = Φ.π Ps[j + 1]) (p₀ p₁ : J)
    (hp₀ : Ps[j + 1] = p₀) (hp₁ : Ps[j] = p₁) (T : (blkCat Φ S δ.1 : Type u₂))
    (hW : (((rouqData Φ S D).wcell μ (wswap RD j L) μ' (wValid_wswap j L hL)).obj.obj M) δ = T)
    (hW' : (((rouqData Φ S D).wcell μ L' μ' hL').obj.obj M) δ = T) :
    (evalSrc Φ S (β' := δ.1) (M β)).map
        (eqToHom (S.wcell_congr (Φ.wtT β.1) eS hc (wValid_liftL_of_eq Φ β.1 Ps hδ))) ≫
      pcrossSwap Φ S D M β j L Ps μ' hL δ hδ hj ≫ eqToHom hW =
    (evalSrc Φ S (β' := δ.1) (M β)).map
        (S.wcross (Φ.wtT β.1) j Lc (Φ.wtT δ.1) hc ≫
          eqToHom (S.wcell_congr (Φ.wtT β.1) eC (wValid_wswap j Lc hc) hc') ≫
          (KLR.Unfurling.swapW (A := End (S.wcell (Φ.wtT β.1) Lc' (Φ.wtT δ.1) hc')) D same p₀ p₁
            ![End.of (S.wdot (Φ.wtT β.1) j Lc' (Φ.wtT δ.1) hc'),
              End.of (S.wdot (Φ.wtT β.1) (j + 1) Lc' (Φ.wtT δ.1) hc')] : _ ⟶ _)) ≫
      (evalSrc Φ S (β' := δ.1) (M β)).map
        (eqToHom (S.wcell_congr (Φ.wtT β.1) eLift hc' (wValid_liftL_of_eq Φ β.1 Ps' hδ'))) ≫
      pgen Φ S D M β L' Ps' μ' hL' hP' δ hδ' ≫ eqToHom hW' := by
  subst eS eC eL eP hp₀ hp₁
  rw [pcrossSwap, dite_eq_left hP', KLR.Unfurling.swapW_congr D hsame]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ _) ((evalSrc Φ S (M β)).map_comp _ _))
  refine Eq.trans ?_
    (congrArg (fun f => (evalSrc Φ S (M β)).map f ≫ _) (Category.assoc _ _ _).symm)
  rfl

/-- The term of the crossing of `g` to the same labels (`pcrossSelf`), for distinct labels of
the same colour, after an identification of the word of `g̃` of the source with `Lc`, as the
coefficient `selfW` in the dots of `Lc`. -/
theorem pcrossSelf_eq (β : Φ.Blk μ) (j : ℕ) (L : List (I × X)) (Ps : List J) (μ' : X)
    (hL : wValid RD μ L μ') (hP : IsPath Φ β.1 L Ps) (δ : Φ.Blk μ')
    (hδ : endBlk β.1 Ps = δ.1) (hj : j + 1 < Ps.length)
    (Lc : List (J × Xc)) (eS : Lc = liftL Φ β.1 Ps) (hc : wValid RDc (Φ.wtT β.1) Lc (Φ.wtT δ.1))
    (L' : List (I × X)) (eL : wswap RD j L = L') (hL' : wValid RD μ L' μ')
    (hP' : IsPath Φ β.1 L' Ps) (hs : Φ.π Ps[j] = Φ.π Ps[j + 1] ∧ Ps[j] ≠ Ps[j + 1])
    (p₀ p₁ : J) (hp₀ : Ps[j] = p₀) (hp₁ : Ps[j + 1] = p₁) (T : (blkCat Φ S δ.1 : Type u₂))
    (hW : (((rouqData Φ S D).wcell μ (wswap RD j L) μ' (wValid_wswap j L hL)).obj.obj M) δ = T)
    (hW' : (((rouqData Φ S D).wcell μ L' μ' hL').obj.obj M) δ = T) :
    (evalSrc Φ S (β' := δ.1) (M β)).map
        (eqToHom (S.wcell_congr (Φ.wtT β.1) eS hc (wValid_liftL_of_eq Φ β.1 Ps hδ))) ≫
      pcrossSelf Φ S D M β j L Ps μ' hL hP δ hδ hj ≫ eqToHom hW =
    (evalSrc Φ S (β' := δ.1) (M β)).map
        (KLR.Unfurling.selfW (A := End (S.wcell (Φ.wtT β.1) Lc (Φ.wtT δ.1) hc)) D p₀ p₁
          ![End.of (S.wdot (Φ.wtT β.1) j Lc (Φ.wtT δ.1) hc),
            End.of (S.wdot (Φ.wtT β.1) (j + 1) Lc (Φ.wtT δ.1) hc)] : _ ⟶ _) ≫
      (evalSrc Φ S (β' := δ.1) (M β)).map
        (eqToHom (S.wcell_congr (Φ.wtT β.1) eS hc (wValid_liftL_of_eq Φ β.1 Ps hδ))) ≫
      pgen Φ S D M β L' Ps μ' hL' hP' δ hδ ≫ eqToHom hW' := by
  subst eS eL hp₀ hp₁
  rw [pcrossSelf, dite_eq_left hs]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  refine (Category.assoc _ _ _).trans ?_
  rfl

end CrossTerms

/-! ## The generators of the summands of lifts -/

omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] [DecidableEq I] [DecidableEq J] in
/-- Polynomials in a dot commute with the identification of words with equal letters. -/
theorem eqToHom_aeval_wdot (x : Xc) (r : ℕ) {L L' : List (J × Xc)} (e : L = L') {x' : Xc}
    (h : wValid RDc x L x') (h' : wValid RDc x L' x') (p : Polynomial k) :
    eqToHom (S.wcell_congr x e h h') ≫ Polynomial.aeval (End.of (S.wdot x r L' x' h')) p =
      Polynomial.aeval (End.of (S.wdot x r L x' h)) p ≫ eqToHom (S.wcell_congr x e h h') := by
  subst e; simp

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

/-- The dots of `R(ν)` (Webster, `lem:gamma-homo`, `x_a e_{π ∘ t} ↦ ϖ_{t_a}(y_a) e_t`). -/
theorem intertw_dot (a : Fin (Multiset.card ν)) :
    MatEnd.Intertw (Unfurling.down D.π ν'.2) (lgen S hπ μ M δ β ν' hδ)
      (actG S μ M δ (FreeAlgebra.ι k (.dot a))) (actT μ M δ β ν' hδ H hnil (FreeAlgebra.ι k (.dot a))) := by
  intro s t
  by_cases hr : IsRel Φ β.1 (word s)
  swap
  · exact (isZero_wordCellAt S μ M δ β ν' hδ hzero s hr).eq_of_src _ _
  rw [actG_ι, actT_ι, MatEnd.mapAlg_apply]
  simp only [RouqData.klrGen, RouqData.wordX, Unfurling.genImage, map_sum,
    RouqFamily.klrComplAt_toCompletion, RouqFamily.klrActAt_pol_mul_e, MatEnd.mapAlg_single,
    MatEnd.sum_single_apply (g := fun x => x)]
  rw [MatEnd.map_plc (evalBlk Φ S M δ), MatEnd.comp_plc]
  erw [MatEnd.sum_plc_comp_rect]
  refine congrArg (fun f => MatEnd.plc _ f t) ?_
  have ha : (a : ℕ) < (word s).length := by
    rw [length_word, ← Unfurling.card_eq D.π ν'.2]; exact a.2
  rw [lgen_of_isRel S hπ μ M δ β ν' hδ s hr, evalBlk_map, evalSrc_map, RouqData.wordDot]
  refine (Category.assoc _ _ _).trans ?_
  erw [pgen_wdot Φ S D M β a _ _ _ _ _ _ _ ha]
  rw [ncEval_pwAt_of_commute _ (fun _ _ => by exact RouqData.wdot_comm _ _ _ _ _ _ _)]
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
  refine congrArg (· ≫ _) ?_
  have hl : (word s)[(a : ℕ)] = s.lbl (Fin.cast (Unfurling.card_eq D.π ν'.2) a) := by
    simp only [getElem_word]; rfl
  rw [hl]
  have key := eqToHom_aeval_wdot S (x' := Φ.wtT δ.1) (Φ.wtT β.1) a
    (liftL_eq_canon Φ β.1 (word s)).symm (wValid_of_eq (wValid_wordL _ s) (wtop_lift μ δ β ν' hδ))
    (wValid_liftL_of_eq Φ β.1 (word s) ((endBlk_word β.1 s).trans hδ))
    (D.pw (s.lbl (Fin.cast (Unfurling.card_eq D.π ν'.2) a)))
  exact congrArg (fun f => f.hom.app (M β)) key

/-- The crossings of `R(ν)` (Webster, `lem:gamma-homo`, formulas `com0new`–`com0newerer`). -/
theorem intertw_cross (j : ℕ) :
    MatEnd.Intertw (Unfurling.down D.π ν'.2) (lgen S hπ μ M δ β ν' hδ)
      (actG S μ M δ (FreeAlgebra.ι k (.cross j)))
      (actT μ M δ β ν' hδ H hnil (FreeAlgebra.ι k (.cross j))) := by
  intro s t
  by_cases hr : IsRel Φ β.1 (word s)
  swap
  · exact (isZero_wordCellAt S μ M δ β ν' hδ hzero s hr).eq_of_src _ _
  rw [actG_ι, actT_ι, MatEnd.mapAlg_apply]
  by_cases h : j + 1 < Multiset.card ν
  swap
  · simp only [RouqData.klrGen, RouqData.wordΨ_of_le (not_lt.1 h), Unfurling.genImage, h,
      dite_false, map_zero]
    simp only [MatEnd.zero_apply, Functor.map_zero, Limits.comp_zero]
    exact (Finset.sum_eq_zero fun _ _ => Limits.zero_comp).symm
  simp only [RouqData.klrGen, RouqData.wordΨ, Unfurling.genImage, h, dite_true,
    MatEnd.sum_single_apply (g := fun t => TypeA.sadj (Multiset.card ν) j • t),
    MatEnd.mapAlg_apply, klrComplAt_sum_crossImage_apply S D H hnil _ _ _ ν'.2 h s]
  erw [MatEnd.sum_map_plc_add_comp_rect]
  rw [MatEnd.map_plc (evalBlk Φ S M δ), MatEnd.comp_plc]
  have hj' : j + 1 < Multiset.card ν'.1 := Unfurling.lt_card_of_lt D ν'.2 h
  have hjs : j + 1 < (word s).length := by rw [length_word]; exact hj'
  have hP := isPath_down hπ μ ν'.2 β.1 s hr
  rw [lgen_of_isRel S hπ μ M δ β ν' hδ s hr, RouqData.wordCross_def _ _ _ h, RouqData.wcrossTo,
    Functor.map_comp, eqToHom_map, evalBlk_map]
  refine Eq.trans (congrArg (fun f => MatEnd.plc _ f t) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
      (pgen_wcross Φ S D M hnil hπ β j _ _ _ _ hP δ _ hjs)))))) ?_
  erw [Preadditive.add_comp, Preadditive.comp_add, MatEnd.plc_add]
  have hw0 : (word s)[j]'(by omega) = s.lbl (Unfurling.posL D ν'.2 h) := by
    simp only [getElem_word]; rfl
  have hw1 : (word s)[j + 1] = s.lbl (Unfurling.posR D ν'.2 h) := by
    simp only [getElem_word]; rfl
  refine congrArg₂ (· + ·) ?_ ?_
  · have hd := Unfurling.down_sadj_smul D.π ν'.2 j s
    rw [MatEnd.plc_congr hd.symm]
    refine congrArg (fun f => MatEnd.plc _ f t) ?_
    simp only [Category.assoc]
    refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (eqToHom_trans _ _)))).trans ?_
    have eP : lswap j (word s) = word (TypeA.sadj (Multiset.card ν'.1) j • s) := by
      rw [lswap_eq _ _ hjs, Diagram.word_sadj s hj']
      simp only [getElem_word]
    have eL : wswap RD j (wordL RD μ (Unfurling.down D.π ν'.2 s)) =
        wordL RD μ (Unfurling.down D.π ν'.2 (TypeA.sadj (Multiset.card ν'.1) j • s)) :=
      (wswap_wordL μ _ h).trans (congrArg _ hd.symm)
    by_cases hr' : IsRel Φ β.1 (word (TypeA.sadj (Multiset.card ν'.1) j • s))
    · rw [lgen_of_isRel S hπ μ M δ β ν' hδ _ hr']
      have hl0 : (TypeA.sadj (Multiset.card ν'.1) j • s).lbl (Unfurling.posL D ν'.2 h) =
          s.lbl (Unfurling.posR D ν'.2 h) := by
        show s.lbl ((TypeA.sadj _ j).symm _) = _
        rw [← Equiv.Perm.inv_def, TypeA.sadj_inv, Unfurling.posL, TypeA.sadj_apply_left hj']
        rfl
      have hl1 : (TypeA.sadj (Multiset.card ν'.1) j • s).lbl (Unfurling.posR D ν'.2 h) =
          s.lbl (Unfurling.posL D ν'.2 h) := by
        show s.lbl ((TypeA.sadj _ j).symm _) = _
        rw [← Equiv.Perm.inv_def, TypeA.sadj_inv, Unfurling.posR, TypeA.sadj_apply_right hj']
        rfl
      have hsame : D.π ((TypeA.sadj (Multiset.card ν'.1) j • s).lbl (Unfurling.posL D ν'.2 h)) =
            D.π ((TypeA.sadj (Multiset.card ν'.1) j • s).lbl (Unfurling.posR D ν'.2 h)) ↔
          Φ.π (word s)[j] = Φ.π (word s)[j + 1] := by
        rw [hl0, hl1, hw0, hw1, hπ, hπ]; exact eq_comm
      refine (pcrossSwap_eq M β j _ (word s) _ (wValid_wordL μ _) δ ((endBlk_word β.1 s).trans hδ)
        hjs _ (liftL_eq_canon Φ β.1 (word s)).symm
        (wValid_of_eq (wValid_wordL _ s) (wtop_lift μ δ β ν' hδ)) _
        (wswap_wordL (Φ.wtT β.1) s hj') (wValid_of_eq (wValid_wordL _ _) (wtop_lift μ δ β ν' hδ))
        _ eL (wValid_wordL μ _) _ eP (isPath_down hπ μ ν'.2 β.1 _ hr')
        ((endBlk_word β.1 _).trans hδ) (liftL_eq_canon Φ β.1 (word _)).symm _ hsame _ _
        (hw1.trans hl0.symm) (hw0.trans hl1.symm) _ _ rfl).trans ?_
      erw [eqToHom_refl, Category.comp_id]
      rw [RouqFamily.wordCrossAt, dite_eq_left hj']
      exact congrArg (fun f => (evalSrc Φ S (M β)).map f ≫ _) (Category.assoc _ _ _).symm
    · have hl : lgen S hπ μ M δ β ν' hδ (TypeA.sadj (Multiset.card ν'.1) j • s) = 0 := by
        unfold lgen; split_ifs; rfl
      have hnp : ¬ IsPath Φ β.1 (wswap RD j (wordL RD μ (Unfurling.down D.π ν'.2 s)))
          (lswap j (word s)) := fun hp =>
        hr' ((isPath_canon_iff Φ β.1 μ _).1 (by rwa [eL, eP, wordL_down hπ] at hp))
      rw [hl, pcrossSwap, dite_eq_right hnp]
      erw [Limits.zero_comp, Limits.comp_zero]
      exact Limits.comp_zero.symm
  · by_cases hs : D.π (s.lbl (Unfurling.posL D ν'.2 h)) = D.π (s.lbl (Unfurling.posR D ν'.2 h)) ∧
        s.lbl (Unfurling.posL D ν'.2 h) ≠ s.lbl (Unfurling.posR D ν'.2 h)
    · have hc : TypeA.sadj (Multiset.card ν) j • Unfurling.down D.π ν'.2 s =
          Unfurling.down D.π ν'.2 s := Unfurling.sadj_smul_down_eq D.π ν'.2 s h hs.1
      rw [MatEnd.plc_congr hc]
      refine congrArg (fun f => MatEnd.plc _ f t) ?_
      simp only [Category.assoc]
      refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (eqToHom_trans _ _)))).trans ?_
      rw [selfCoef, ite_eq_left hs]
      have eL : wswap RD j (wordL RD μ (Unfurling.down D.π ν'.2 s)) =
          wordL RD μ (Unfurling.down D.π ν'.2 s) :=
        (wswap_wordL μ _ h).trans (congrArg _ hc)
      have hs' : Φ.π (word s)[j] = Φ.π (word s)[j + 1] ∧ (word s)[j] ≠ (word s)[j + 1] := by
        rw [hw0, hw1, hπ, hπ]; exact hs
      refine (pcrossSelf_eq M β j _ (word s) _ (wValid_wordL μ _) hP δ
        ((endBlk_word β.1 s).trans hδ) hjs _ (liftL_eq_canon Φ β.1 (word s)).symm
        (wValid_of_eq (wValid_wordL _ s) (wtop_lift μ δ β ν' hδ)) _ eL (wValid_wordL μ _) hP hs'
        _ _ hw0 hw1 _ _ rfl).trans ?_
      erw [eqToHom_refl, Category.comp_id]
      rfl
    · have hs' : ¬ (Φ.π (word s)[j] = Φ.π (word s)[j + 1] ∧ (word s)[j] ≠ (word s)[j + 1]) := by
        rw [hw0, hw1, hπ, hπ]; exact hs
      rw [pcrossSelf, dite_eq_right hs', selfCoef, ite_eq_right hs, Functor.map_zero]
      erw [Limits.zero_comp, Limits.comp_zero, Limits.zero_comp, MatEnd.plc_zero, MatEnd.plc_zero]
      rfl

/-- **The generators of lifts intertwine the two actions** (Webster, `lem:g-action`): on the
summand of the lift `ν̃`, the action of `r` on the words of `g` is the action of `γ(r)` on the
words of `g̃`. -/
theorem intertw_freeGamma (r : FreeAlgebra k (KLR.Gen ν)) :
    MatEnd.Intertw (Unfurling.down D.π ν'.2) (lgen S hπ μ M δ β ν' hδ)
      (actG S μ M δ r) (actT μ M δ β ν' hδ H hnil r) := by
  change (actG S μ M δ r, actT μ M δ β ν' hδ H hnil r) ∈ MatEnd.intertwSubalgebra k _ _
  induction r using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (MatEnd.intertwSubalgebra k _ _).algebraMap_mem c
  | grade1 g =>
    cases g with
    | idem i => exact intertw_idem hπ μ M δ β ν' hδ H hnil hzero i
    | dot a => exact intertw_dot hπ μ M δ β ν' hδ H hnil hzero a
    | cross j => exact intertw_cross hπ μ M δ β ν' hδ H hnil hzero j
  | mul a b ha hb =>
    rw [map_mul, map_mul]
    exact (MatEnd.intertwSubalgebra k _ _).mul_mem ha hb
  | add a b ha hb =>
    rw [map_add, map_add]
    exact (MatEnd.intertwSubalgebra k _ _).add_mem ha hb

end Gen

/-! ## Descent of the action of `g` to `R(ν)` -/

section Descent

omit [DecidableEq I] [DecidableEq J] in
/-- Every list of colours is the word of a sequence. -/
theorem exists_word_eq (l : List J) : ∃ (ν' : Multiset J) (s : Seq ν'), word s = l := by
  have hc : Multiset.card (l : Multiset J) = l.length := Multiset.coe_card l
  refine ⟨l, ⟨fun a => l.get (Fin.cast hc a), ?_⟩, ?_⟩
  · rw [Fin.univ_val_map, ← List.ofFn_congr hc.symm l.get, List.ofFn_get]
  · change List.ofFn (fun a => l.get (Fin.cast hc a)) = l
    rw [← List.ofFn_congr hc.symm l.get, List.ofFn_get]

omit [DecidableEq I] [DecidableEq J] in
theorem coe_word_I {ν : Multiset I} (t : KLR.Seq ν) : (word t : Multiset I) = ν := by
  rw [word, ← Fin.univ_val_map]; exact t.2

variable {Φ D} {S} (hπ : ∀ a, Φ.π a = D.π a) (μ : X) {ν : Multiset I}
  (H : RouqUpKLR S (Unfurling.unfQ (k := k) D.arrows))
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
  {Q : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))

include hπ H hnil hzero hPQ in
/-- **The action of `g` respects the relations of `R(ν)`** (Webster, `lem:g-action`): if `x` and
`y` are related by a defining relation of `R(ν)`, they act equally on the words of `g` at every
object and block. The generators of paths into a word of `g` are the generators of the lifts of
its words (`Furling.lgen`), on which the two actions are those of `γ(x) = γ(y)`. -/
theorem actG_eq_of_rel (M : ∀ β : Φ.Blk μ, blkCat Φ S β.1) (δ : Φ.Blk (wtop RD μ ν))
    {x y : FreeAlgebra k (KLR.Gen ν)} (h : Rel k Q ν x y) :
    actG (D := D) S μ M δ x = actG (D := D) S μ M δ y := by
  ext t' t
  refine pgen_ext Φ S D M (wordL RD μ t') (wValid_wordL μ t') δ (𝟭 _)
    (g := actG (D := D) S μ M δ x t' t) (g' := actG (D := D) S μ M δ y t' t) fun β Ps hP hδ => ?_
  obtain ⟨ν'', s, rfl⟩ := exists_word_eq Ps
  have hw : word t' = (word s).map Φ.π := by
    rw [← map_fst_of_isPath Φ β.1 _ _ hP, wordL, map_fst_canon]
  have hν : ν''.map D.π = ν := by
    rw [← coe_word_I t', hw, ← Multiset.map_coe, coe_word]
    exact Multiset.map_congr rfl fun a _ => (hπ a).symm
  obtain rfl : Unfurling.down D.π hν s = t' :=
    word_injective ((word_down hπ hν s).trans hw.symm)
  have hδ' : β.1 + blkSum ν'' = δ.1 := (endBlk_word β.1 s).symm.trans hδ
  have hr : IsRel Φ β.1 (word s) := by
    have := hP; rw [wordL_down hπ] at this; exact (isPath_canon_iff Φ β.1 μ _).1 this
  have hT : actT μ M δ β ⟨ν'', hν⟩ hδ' H hnil x = actT μ M δ β ⟨ν'', hν⟩ hδ' H hnil y := by
    have hg := Unfurling.freeGamma_rel D hPQ h
    unfold actT
    erw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, hg]
    rfl
  have key := (intertw_freeGamma hπ μ M δ β ⟨ν'', hν⟩ hδ' H hnil hzero x s t).trans
    (hT ▸ (intertw_freeGamma hπ μ M δ β ⟨ν'', hν⟩ hδ' H hnil hzero y s t).symm)
  rw [lgen_of_isRel S hπ μ M δ β ⟨ν'', hν⟩ hδ' s hr] at key
  exact (cancel_epi _).1 ((Category.assoc _ _ _).symm.trans (key.trans (Category.assoc _ _ _)))

include hπ H hnil hzero hPQ in
/-- **Webster, arXiv:1603.06311v3, §2.3, Lemma label `lem:g-action`** (the relations): the
generators of `g` satisfy the defining relations of `R(ν)` for the matrices `Q` of `P`, that is,
`RouqData.klrActFree` of `g` factors through `R(ν)`. -/
theorem klrActFree_rel {x y : FreeAlgebra k (KLR.Gen ν)} (h : Rel k Q ν x y) :
    (rouqData Φ S D).klrActFree k μ ν x = (rouqData Φ S D).klrActFree k μ ν y := by
  ext t' t
  apply ObjectProperty.hom_ext
  ext M δ
  have := congrFun (congrFun (actG_eq_of_rel hπ μ H hnil hzero hPQ M δ h) t') t
  simp only [actG, AlgHom.comp_apply, MatEnd.mapAlg_apply, evalBlk_map] at this
  exact this

/-- **Webster, arXiv:1603.06311v3, §2.3, Lemma label `lem:g-action`**: the KLR algebra `R(ν)`
of the matrices `Q` of `P` acts on the words of weight `ν` of `g`, the generators acting by
the idempotents, dots and crossings of `g`. -/
def klrAct : KLRAlgebra k Q ν →ₐ[k] (rouqData Φ S D).WordEnd μ ν :=
  RingQuot.liftAlgHom k ⟨(rouqData Φ S D).klrActFree k μ ν,
    fun _ _ h => klrActFree_rel hπ μ H hnil hzero hPQ h⟩

theorem klrAct_mk (a : FreeAlgebra k (KLR.Gen ν)) :
    klrAct hπ μ H hnil hzero hPQ (KLRAlgebra.mk k Q ν a) = (rouqData Φ S D).klrActFree k μ ν a :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ a

include hπ H hnil hzero hPQ in
/-- **Webster, `lem:g-action`**, as a property of the Rouquier data of `g`: the action of the free
algebra on the generators of `R(ν)` respects the relations of `R(ν)` for `Q`. -/
theorem respectsKLR : (rouqData Φ S D).RespectsKLR k Q :=
  fun μ _ _ _ h => klrActFree_rel hπ μ H hnil hzero hPQ h

include hπ H hnil hzero hPQ in
/-- **The mixed KLR relations for `g`** (Brundan, arXiv:1501.00350v1, Definition 1.1,
(1.2)–(1.4), for distinct colours): every Rouquier family whose generators are those of `g`
satisfies `RouqUpKLR` for the matrices `Q` of `P`. -/
theorem rouqUpKLR (T : RouqFamily (B := LinearCat k) RD)
    (hT : T.toRouqData = rouqData Φ S D) : RouqUpKLR T Q :=
  RouqFamily.rouqUpKLR_of_respectsKLR (hT ▸ respectsKLR hπ H hnil hzero hPQ)

end Descent

end Furling

end Categorification.TwoRep
