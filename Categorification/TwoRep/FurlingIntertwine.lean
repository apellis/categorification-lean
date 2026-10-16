/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingWords
import Categorification.TwoRep.RouqKLRCompletion
import Categorification.KLR.Unfurling.GammaHomo

/-!
# Furling: the crossings of `g` on paths of the cover

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2.3, Lemma with
label `lem:g-action`. On the generators of the paths of the cover (`Furling.pgen`), the dots of
`g` act by `ϖ_a(y)` (`Furling.pgen_wdot`). This file computes the crossings: the crossing of `g`
on the letters `j`, `j+1` of a word, on the generator of the path with labels `Ps`, is the image
`γ(ψ_j)` of the crossing under the unfurling homomorphism, acting through the dots and the
crossings of `g̃`. It has two terms (`Furling.pgen_wcross`):

* to the path with the labels `Ps_j`, `Ps_{j+1}` exchanged, when it is a path: the crossing of
  `g̃` followed by the coefficient `swapW` of the swapped term of `γ(ψ)` (`h_a(y)⁻¹` for equal
  labels, `-(ϖ_a(y) - ϖ_b(y'))⁻¹` for distinct labels of the same colour, `P°_{ab}(y, y')` for
  distinct colours), `Furling.pcrossSwap`;
* to the same labels, for distinct labels of the same colour: the coefficient
  `(ϖ_a(y) - ϖ_b(y'))⁻¹`, `Furling.pcrossSelf`.

## Main definitions and results

* `Unfurling.swapW`, `Unfurling.selfW`: the coefficients of `γ(ψ)` in two commuting nilpotent
  elements, and their compatibility with algebra maps (`map_swapW`, `map_selfW`).
* `Diagram.MatEnd.mapAlg`, `Diagram.MatEnd.intertwSubalgebra`: entrywise linear functors on
  matrix endomorphism algebras, and the subalgebra of pairs intertwined by a rectangular family.
* `Furling.pcrossSwap`, `Furling.pcrossSelf`, `Furling.pgen_wcross`.
-/

noncomputable section

namespace Categorification.KLR.Unfurling

open MvPolynomial

variable {I J : Type*} {k : Type*} [Field k] {P : I → I → MvPolynomial (Fin 2) k}
  (D : UnfurlingDatum k P J)

/-- The coefficient of the term of `γ(ψ)` to the swapped labels, at the dots `y 0`, `y 1` of
the two strands (output labels `p₀`, `p₁`, the first on the left strand): `h_{p₀}(y)⁻¹` for
`p₀ = p₁`, `-(ϖ_{p₀}(y 0) - ϖ_{p₁}(y 1))⁻¹` for distinct labels of the same colour, and
`P°_{p₀ p₁}(y)` for distinct colours (`crossImage`). -/
def swapW [DecidableEq J] (same : Prop) [Decidable same] (p₀ p₁ : J) {A : Type*} [Ring A] [Algebra k A]
    (y : Fin 2 → A) : A :=
  if same then
    if p₀ = p₁ then Ring.inverse (ncEval y (pwDiff D p₀))
    else -Ring.inverse (ncEval y (pwAt D.pw p₀ 0 - pwAt D.pw p₁ 1))
  else ncEval y (D.unit p₀ p₁)

/-- The coefficient `(ϖ_{p₀}(y 0) - ϖ_{p₁}(y 1))⁻¹` of the term of `γ(ψ)` on the same labels,
for distinct labels of the same colour (`crossImage`). -/
def selfW (p₀ p₁ : J) {A : Type*} [Ring A] [Algebra k A] (y : Fin 2 → A) : A :=
  Ring.inverse (ncEval y (pwAt D.pw p₀ 0 - pwAt D.pw p₁ 1))

theorem swapW_congr [DecidableEq J] {same same' : Prop} [Decidable same] [Decidable same'] (h : same ↔ same')
    (p₀ p₁ : J) {A : Type*} [Ring A] [Algebra k A] (y : Fin 2 → A) :
    swapW D same p₀ p₁ y = swapW D same' p₀ p₁ y := by
  unfold swapW; by_cases hs : same
  · simp only [hs, (h.1 hs), ite_true]
  · simp only [hs, (show ¬same' from fun h' => hs (h.2 h')), ite_false]

theorem constantCoeff_pwAt_sub (p₀ p₁ : J) :
    constantCoeff (pwAt D.pw p₀ 0 - pwAt D.pw p₁ 1 : MvPolynomial (Fin 2) k) =
      (D.pw p₀).coeff 0 - (D.pw p₁).coeff 0 := by
  rw [map_sub, pwAt, pwAt, constantCoeff_aeval_X, constantCoeff_aeval_X]

theorem isUnit_constantCoeff_pwAt_sub {p₀ p₁ : J} (hc : D.π p₀ = D.π p₁) (hne : p₀ ≠ p₁) :
    IsUnit (constantCoeff (pwAt D.pw p₀ 0 - pwAt D.pw p₁ 1 : MvPolynomial (Fin 2) k)) := by
  rw [constantCoeff_pwAt_sub]
  exact isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun e => hne (D.pw_coeff_zero_inj _ _ hc e))

variable {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]

theorem map_swapW [DecidableEq J] (φ : A →ₐ[k] B) {same : Prop} [Decidable same] {p₀ p₁ : J}
    (hs : same → D.π p₀ = D.π p₁) (y : Fin 2 → A) (hc : Commute (y 0) (y 1))
    (hn : ∀ a, IsNilpotent (y a)) :
    φ (swapW D same p₀ p₁ y) = swapW D same p₀ p₁ (fun a => φ (y a)) := by
  have hc' : ∀ a b, Commute (y a) (y b) := by
    intro a b; fin_cases a <;> fin_cases b
    exacts [Commute.refl _, hc, hc.symm, Commute.refl _]
  unfold swapW
  split_ifs with h₁ h₂
  · rw [TwoRep.Ring.map_inverse φ (isUnit_ncEval y hc' hn _ (isUnit_iff_ne_zero.2
      (constantCoeff_pwDiff_ne_zero D p₀))), AlgHom.map_ncEval]
  · rw [map_neg, TwoRep.Ring.map_inverse φ (isUnit_ncEval y hc' hn _
      (isUnit_constantCoeff_pwAt_sub D (hs h₁) h₂)), AlgHom.map_ncEval]
  · rw [AlgHom.map_ncEval]

theorem map_selfW (φ : A →ₐ[k] B) {p₀ p₁ : J} (hs : D.π p₀ = D.π p₁) (hne : p₀ ≠ p₁)
    (y : Fin 2 → A) (hc : Commute (y 0) (y 1)) (hn : ∀ a, IsNilpotent (y a)) :
    φ (selfW D p₀ p₁ y) = selfW D p₀ p₁ (fun a => φ (y a)) := by
  have hc' : ∀ a b, Commute (y a) (y b) := by
    intro a b; fin_cases a <;> fin_cases b
    exacts [Commute.refl _, hc, hc.symm, Commute.refl _]
  rw [selfW, selfW, TwoRep.Ring.map_inverse φ (isUnit_ncEval y hc' hn _
    (isUnit_constantCoeff_pwAt_sub D hs hne)), AlgHom.map_ncEval]

end Categorification.KLR.Unfurling

namespace Categorification.KLR.Diagram.MatEnd

open CategoryTheory Preadditive

variable {k : Type*} [CommRing k] {C D : Type*} [Category C] [Preadditive C] [Linear k C]
  [Category D] [Preadditive D] [Linear k D] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (k) in
/-- A linear functor applied entrywise to matrices of morphisms. -/
def mapAlg (F : C ⥤ D) [F.Additive] [F.Linear k] (X : ι → C) :
    MatEnd X →ₐ[k] MatEnd (fun i => F.obj (X i)) where
  toFun f i j := F.map (f i j)
  map_one' := by
    funext i j
    change F.map ((1 : MatEnd X) i j) = (1 : MatEnd (fun i => F.obj (X i))) i j
    rw [one_apply, one_apply]
    split_ifs with h
    · subst h; simp
    · exact F.map_zero _ _
  map_mul' f g := by
    funext i l
    change F.map ((f * g) i l) = ∑ j, F.map (g i j) ≫ F.map (f j l)
    rw [mul_apply, F.map_sum]
    exact Finset.sum_congr rfl fun j _ => F.map_comp _ _
  map_zero' := by funext i j; exact F.map_zero _ _
  map_add' f g := by funext i j; exact F.map_add
  commutes' r := by
    funext i j
    change F.map ((r • (1 : MatEnd X)) i j) = (r • (1 : MatEnd (fun i => F.obj (X i)))) i j
    rw [smul_apply, smul_apply, F.map_smul]
    congr 1
    rw [one_apply, one_apply]
    split_ifs with h
    · subst h; simp
    · exact F.map_zero _ _

@[simp] theorem mapAlg_apply (F : C ⥤ D) [F.Additive] [F.Linear k] (X : ι → C) (f : MatEnd X)
    (i j : ι) : mapAlg k F X f i j = F.map (f i j) := rfl

/-! ### Intertwining matrices along a rectangular family of maps -/

section Intertw

variable {τ : Type*} [Fintype τ] [DecidableEq τ] {Y : ι → C} {Z : τ → C} (d : τ → ι)
  (G : ∀ s, Z s ⟶ Y (d s))

/-- The rectangular matrix with entries `G s` at `(s, d s)`. -/
def rect (s : τ) (t : ι) : Z s ⟶ Y t :=
  if h : d s = t then G s ≫ eqToHom (congrArg Y h) else 0

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in
@[simp] theorem rect_self (s : τ) : rect d G s (d s) = G s := by
  simp [rect]

omit [Fintype τ] [DecidableEq τ] in
theorem sum_rect_comp {W : C} (s : τ) (f : ∀ t, Y t ⟶ W) :
    ∑ t, rect d G s t ≫ f t = G s ≫ f (d s) := by
  rw [Finset.sum_eq_single (d s)]
  · rw [rect_self]
  · intro t _ ht
    rw [rect, dite_eq_right_iff.2 (fun h => absurd h (Ne.symm ht)), Limits.zero_comp]
  · simp

/-- `A ∈ MatEnd Y` and `B ∈ MatEnd Z` are intertwined by `G`: `G ∘ A = B ∘ G` as rectangular
matrices. -/
def Intertw (A : MatEnd Y) (B : MatEnd Z) : Prop :=
  ∀ s t, G s ≫ A (d s) t = ∑ u, B s u ≫ rect d G u t

variable (k) in
/-- The pairs intertwined by `G` form a subalgebra. -/
def intertwSubalgebra : Subalgebra k (MatEnd Y × MatEnd Z) where
  carrier := {p | Intertw d G p.1 p.2}
  mul_mem' {p q} hp hq := by
    intro s t
    change G s ≫ (∑ v, q.1 (d s) v ≫ p.1 v t) = ∑ u, (∑ w, q.2 s w ≫ p.2 w u) ≫ rect d G u t
    calc G s ≫ (∑ v, q.1 (d s) v ≫ p.1 v t)
        = ∑ v, (G s ≫ q.1 (d s) v) ≫ p.1 v t := by
          rw [Preadditive.comp_sum]; simp only [Category.assoc]
      _ = ∑ v, (∑ w, q.2 s w ≫ rect d G w v) ≫ p.1 v t := by simp only [hq s]
      _ = ∑ w, q.2 s w ≫ ∑ v, rect d G w v ≫ p.1 v t := by
          simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
          exact Finset.sum_comm
      _ = ∑ w, q.2 s w ≫ ∑ u, p.2 w u ≫ rect d G u t := by
          simp only [sum_rect_comp, hp _ t]
      _ = ∑ u, (∑ w, q.2 s w ≫ p.2 w u) ≫ rect d G u t := by
          simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
          exact Finset.sum_comm
  add_mem' {p q} hp hq := by
    intro s t
    change G s ≫ (p.1 (d s) t + q.1 (d s) t) = ∑ u, (p.2 s u + q.2 s u) ≫ rect d G u t
    simp only [Preadditive.comp_add, Preadditive.add_comp, Finset.sum_add_distrib, hp s t,
      hq s t]
  algebraMap_mem' r := by
    intro s t
    change G s ≫ (r • (1 : MatEnd Y)) (d s) t = ∑ u, (r • (1 : MatEnd Z)) s u ≫ rect d G u t
    simp only [smul_apply, Linear.comp_smul, Linear.smul_comp, ← Finset.smul_sum]
    congr 1
    rw [Finset.sum_eq_single s]
    · rw [one_apply_self, Category.id_comp, one_apply]
      unfold rect
      split_ifs with h
      · rfl
      · exact Limits.comp_zero
    · intro u _ hu; rw [one_apply_of_ne (Ne.symm hu), Limits.zero_comp]
    · simp

theorem mem_intertwSubalgebra {A : MatEnd Y} {B : MatEnd Z} :
    (A, B) ∈ intertwSubalgebra k d G ↔ Intertw d G A B := Iff.rfl

end Intertw

end Categorification.KLR.Diagram.MatEnd

namespace Categorification.TwoRep.LinearCat

open CategoryTheory

variable {k : Type*} [CommRing k]

/-- Evaluation of the 2-morphisms between two 1-morphisms at an object. -/
@[simps] def evalAt {C D : LinearCat k} (x : (C : Type _)) : (C ⟶ D) ⥤ (D : Type _) where
  obj F := F.obj.obj x
  map η := η.hom.app x

instance {C D : LinearCat k} (x : (C : Type _)) : (evalAt (D := D) x).Additive where
  map_add := rfl

instance {C D : LinearCat k} (x : (C : Type _)) : (evalAt (D := D) x).Linear k where
  map_smul _ _ := rfl

theorem eqToHom_hom_app {C D : LinearCat k} {F G : C ⟶ D} (p : F = G) (x : (C : Type _)) :
    (eqToHom p).hom.app x = eqToHom (congrArg (fun H : C ⟶ D => H.obj.obj x) p) := by
  subst p; rfl

theorem comp_hom_app {C D : LinearCat k} {F G H : C ⟶ D} (η : F ⟶ G) (θ : G ⟶ H)
    (x : (C : Type _)) : (η ≫ θ).hom.app x = η.hom.app x ≫ θ.hom.app x := rfl

theorem whiskerRight_hom_app {C D E : LinearCat k} {F G : C ⟶ D} (η : F ⟶ G) (H : D ⟶ E)
    (x : (C : Type _)) :
    (Bicategory.whiskerRight η H).hom.app x = H.obj.map (η.hom.app x) := rfl

end Categorification.TwoRep.LinearCat

namespace Categorification.TwoRep.LinearCat

open CategoryTheory

variable (k : Type*) [CommRing k]

/-- The components at an object of the endomorphisms of a 1-morphism, as an algebra
homomorphism. -/
def appAlg {C D : LinearCat k} (F : C ⟶ D) (x : (C : Type _)) :
    End F →ₐ[k] End (F.obj.obj x) where
  toFun η := (η : F ⟶ F).hom.app x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    rfl

variable {k}

@[simp] theorem appAlg_apply {C D : LinearCat k} (F : C ⟶ D) (x : (C : Type _)) (η : End F) :
    appAlg k F x η = (η : F ⟶ F).hom.app x := rfl

end Categorification.TwoRep.LinearCat

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

/-! ## Paths and weighted words -/

omit [DecidableEq I] [DecidableEq J] in
theorem ctop_eq_wtT_endBlk (β : J →₀ ℤ) :
    ∀ Ps : List J, ctop RDc (Φ.wtT β) Ps = Φ.wtT (endBlk β Ps)
  | [] => rfl
  | a :: Ps => by rw [ctop, ctop_eq_wtT_endBlk β Ps, endBlk, Φ.wtT_add_single]

omit [DecidableEq I] [DecidableEq J] in
theorem liftL_eq_canon (β : J →₀ ℤ) :
    ∀ Ps : List J, liftL Φ β Ps = canon RDc (Φ.wtT β) Ps
  | [] => rfl
  | a :: Ps => by rw [liftL, canon, ctop_eq_wtT_endBlk, liftL_eq_canon β Ps]

omit [DecidableEq I] [DecidableEq J] in
theorem endBlk_lswap (β : J →₀ ℤ) :
    ∀ (j : ℕ) (Ps : List J), endBlk β (lswap j Ps) = endBlk β Ps
  | 0, a :: b :: Ps => by simp only [lswap, endBlk]; rw [add_right_comm]
  | j + 1, a :: Ps => by simp only [lswap, endBlk]; rw [endBlk_lswap β j Ps]
  | 0, [] => rfl
  | 0, [_] => rfl
  | _ + 1, [] => rfl

omit [DecidableEq I] [DecidableEq J] in
theorem wswap_liftL (β : J →₀ ℤ) (j : ℕ) (Ps : List J) :
    wswap RDc j (liftL Φ β Ps) = liftL Φ β (lswap j Ps) := by
  rw [liftL_eq_canon, liftL_eq_canon, wswap_canon]

/-- The sum `Σ_{a ∈ ν̃} a` of a multiset of labels, as a block. -/
def blkSum (ν' : Multiset J) : J →₀ ℤ := (ν'.map fun a => Finsupp.single a (1 : ℤ)).sum

omit [DecidableEq I] [DecidableEq J] in
theorem endBlk_eq (β : J →₀ ℤ) :
    ∀ Ps : List J, endBlk β Ps = β + blkSum (Ps : Multiset J)
  | [] => by simp [endBlk, blkSum]
  | a :: Ps => by
    rw [endBlk, endBlk_eq β Ps, blkSum, blkSum, ← Multiset.cons_coe, Multiset.map_cons,
      Multiset.sum_cons]
    abel

omit [DecidableEq I] [DecidableEq J] in
theorem coe_word {ν' : Multiset J} (t : KLR.Seq ν') : (KLR.Diagram.word t : Multiset J) = ν' := by
  rw [KLR.Diagram.word, ← Fin.univ_val_map]; exact t.2

omit [DecidableEq I] [DecidableEq J] in
theorem endBlk_word (β : J →₀ ℤ) {ν' : Multiset J} (t : KLR.Seq ν') :
    endBlk β (KLR.Diagram.word t) = β + blkSum ν' := by
  rw [endBlk_eq, coe_word]

omit [DecidableEq I] [DecidableEq J] in
theorem wtT_add_blkSum (β : J →₀ ℤ) (ν' : Multiset J) :
    Φ.wtT (β + blkSum ν') = wtop RDc (Φ.wtT β) ν' := by
  induction ν' using Multiset.induction_on with
  | empty => simp [blkSum, wtop]
  | cons a s ih =>
    rw [blkSum, Multiset.map_cons, Multiset.sum_cons, ← blkSum, add_comm (Finsupp.single a 1),
      ← add_assoc, ← Φ.wtT_add_single, ih, wtop, wtop, Multiset.map_cons, Multiset.sum_cons]
    abel

omit [DecidableEq I] [DecidableEq J] in
theorem wtG_add_blkSum (β : J →₀ ℤ) (ν' : Multiset J) :
    Φ.wtG (β + blkSum ν') = wtop RD (Φ.wtG β) (ν'.map Φ.π) := by
  induction ν' using Multiset.induction_on with
  | empty => simp [blkSum, wtop]
  | cons a s ih =>
    rw [blkSum, Multiset.map_cons, Multiset.sum_cons, ← blkSum, add_comm (Finsupp.single a 1),
      ← add_assoc, ← Φ.wtG_add_single, ih, wtop, wtop, Multiset.map_cons, Multiset.map_cons,
      Multiset.sum_cons]
    abel

/-- All edges of the path from `β` with labels `Ps` are relevant. -/
def IsRel (β : J →₀ ℤ) : List J → Prop
  | [] => True
  | a :: Ps => IsRel β Ps ∧ Φ.rel (endBlk β Ps) a

omit [DecidableEq I] [DecidableEq J] in
theorem isPath_canon_iff (β : J →₀ ℤ) (μ : X) :
    ∀ Ps : List J, IsPath Φ β (canon RD μ (Ps.map Φ.π)) Ps ↔ IsRel Φ β Ps
  | [] => Iff.rfl
  | a :: Ps => by
    simp only [List.map_cons, canon, IsPath, IsRel, isPath_canon_iff β μ Ps, true_and]

omit [DecidableEq I] [DecidableEq J] in
theorem map_fst_of_isPath (β : J →₀ ℤ) :
    ∀ (L : List (I × X)) (Ps : List J), IsPath Φ β L Ps → L.map Prod.fst = Ps.map Φ.π
  | [], [], _ => rfl
  | (c, _) :: L, a :: Ps, hP => by
    rw [List.map_cons, List.map_cons, map_fst_of_isPath β L Ps hP.1, hP.2.1]
  | [], _ :: _, hP => hP.elim
  | _ :: _, [], hP => hP.elim


/-! ## Crossings of `g` on the generators of paths -/

theorem wl2_hom_app {C₁ C₂ C₃ C₃' C₄ : LinearCat.{wk, v₁, u₂} k} (W : C₁ ⟶ C₂) {f : C₂ ⟶ C₃}
    {g : C₂ ⟶ C₃'} {f' : C₃ ⟶ C₄} {g' : C₃' ⟶ C₄} (η : f ≫ f' ⟶ g ≫ g') (x : C₁) :
    (wl2 W η).hom.app x = η.hom.app (W.obj.obj x) := by
  change 𝟙 _ ≫ η.hom.app (W.obj.obj x) ≫ 𝟙 _ = _
  simp

section Cross

variable (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc)
  {P : I → I → MvPolynomial (Fin 2) k} (D : KLR.Unfurling.UnfurlingDatum k P J)

omit [DecidableEq I] [DecidableEq J] in
theorem eqToHom_wl2 {C₀ : LinearCat.{wk, v₁, u₂} k} {a b : J} {x y' y'' z : Xc}
    (W : C₀ ⟶ S.obj x) (h₃ : x + RDc.iX b = y') (h₄ : y' + RDc.iX a = z)
    (h₃' : x + RDc.iX b = y'') (h₄' : y'' + RDc.iX a = z)
    (p : (W ≫ S.E b h₃) ≫ S.E a h₄ = (W ≫ S.E b h₃') ≫ S.E a h₄')
    (p' : S.E b h₃ ≫ S.E a h₄ = S.E b h₃' ≫ S.E a h₄') :
    eqToHom p = wl2 W (eqToHom p') := by
  subst h₃ h₃'
  rw [eqToHom_refl, eqToHom_refl, wl2_id]

omit [DecidableEq I] in
theorem cross_swapW_eqToHom (same : Prop) [Decidable same] {a b : J} {x y z y' y'' : Xc}
    (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z) (h₃ : x + RDc.iX b = y')
    (h₄ : y' + RDc.iX a = z) (h₃' : x + RDc.iX b = y'') (h₄' : y'' + RDc.iX a = z)
    (p : S.E b h₃ ≫ S.E a h₄ = S.E b h₃' ≫ S.E a h₄') :
    S.cross b a h₁ h₂ h₃ h₄ ≫ (KLR.Unfurling.swapW (A := End (S.E b h₃ ≫ S.E a h₄)) D same a b
        ![End.of (S.E b h₃ ◁ S.dot a h₄), End.of (S.dot b h₃ ▷ S.E a h₄)] : _ ⟶ _) ≫
        eqToHom p =
      S.cross b a h₁ h₂ h₃' h₄' ≫ (KLR.Unfurling.swapW (A := End (S.E b h₃' ≫ S.E a h₄')) D same
        a b ![End.of (S.E b h₃' ◁ S.dot a h₄'), End.of (S.dot b h₃' ▷ S.E a h₄')] : _ ⟶ _) := by
  subst h₃ h₃'
  rw [eqToHom_refl, Category.comp_id]

omit [DecidableEq I] [DecidableEq J] in
theorem pair_dots_commute {a b : J} {x y z : Xc} (h₁ : x + RDc.iX a = y)
    (h₂ : y + RDc.iX b = z) :
    Commute (End.of (S.E a h₁ ◁ S.dot b h₂)) (End.of (S.dot a h₁ ▷ S.E b h₂)) :=
  (whisker_exchange _ _).symm

omit [DecidableEq I] [DecidableEq J] in
theorem pair_dots_nilpotent
    (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
    {a b : J} {x y z : Xc} (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z) :
    ∀ t, IsNilpotent (![End.of (S.E a h₁ ◁ S.dot b h₂), End.of (S.dot a h₁ ▷ S.E b h₂)] t) := by
  intro t
  fin_cases t
  · obtain ⟨N, hN⟩ := hnil b h₂
    refine ⟨N, ?_⟩
    change End.of (S.E a h₁ ◁ S.dot b h₂) ^ N = 0
    rw [whiskerLeft_pow]
    erw [hN]
    exact AdditiveWhiskering.whiskerLeft_zero _ _ _
  · obtain ⟨N, hN⟩ := hnil a h₁
    refine ⟨N, ?_⟩
    change End.of (S.dot a h₁ ▷ S.E b h₂) ^ N = 0
    rw [whiskerRight_pow]
    erw [hN]
    exact AdditiveWhiskering.zero_whiskerRight _ _ _

omit [DecidableEq I] in
/-- The crossing of `g̃` on the first two letters of a weighted word, followed by the
coefficient `swapW` of the swapped term of `γ(ψ)` in its dots and a comparison of words, is the
crossing of the two letters with the coefficient in their dots, at the object of the rest. -/
theorem wcross_swapW_eqToHom_app
    (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
    (same : Prop) [Decidable same] {μ μ' : Xc} (c d : J) (hs : same → D.π d = D.π c)
    (ν₁ ν₂ y'' : Xc) (L : List (J × Xc))
    (h : wValid RDc μ ((c, ν₁) :: (d, ν₂) :: L) μ')
    (e : wswap RDc 0 ((c, ν₁) :: (d, ν₂) :: L) = (d, y'') :: (c, ν₂) :: L)
    (h₂ : wValid RDc μ ((d, y'') :: (c, ν₂) :: L) μ') (x : (S.obj μ : Type u₂)) :
    (S.wcross μ 0 _ μ' h ≫
      (KLR.Unfurling.swapW (A := End (S.wcell μ (wswap RDc 0 ((c, ν₁) :: (d, ν₂) :: L)) μ'
          (wValid_wswap 0 _ h))) D same d c
        ![End.of (S.wdot μ 0 _ μ' (wValid_wswap 0 _ h)),
          End.of (S.wdot μ 1 _ μ' (wValid_wswap 0 _ h))] : _ ⟶ _) ≫
      eqToHom (S.wcell_congr μ e _ h₂)).hom.app x =
    (S.cross c d h.1.2 h.2 h₂.1.2 h₂.2 ≫
      (KLR.Unfurling.swapW (A := End (S.E c h₂.1.2 ≫ S.E d h₂.2)) D same d c
        ![End.of (S.E c h₂.1.2 ◁ S.dot d h₂.2), End.of (S.dot c h₂.1.2 ▷ S.E d h₂.2)] :
          _ ⟶ _)).hom.app ((S.wcell μ L ν₂ h.1.1).obj.obj x) := by
  have h1 : S.wcross μ 0 _ μ' h = wl2 (S.wcell μ L ν₂ h.1.1)
      (S.cross c d h.1.2 h.2 rfl (by rw [← h.2, ← h.1.2, add_right_comm])) := rfl
  have h2 : (KLR.Unfurling.swapW (A := End (S.wcell μ (wswap RDc 0 ((c, ν₁) :: (d, ν₂) :: L)) μ'
          (wValid_wswap 0 _ h))) D same d c
        ![End.of (S.wdot μ 0 _ μ' (wValid_wswap 0 _ h)),
          End.of (S.wdot μ 1 _ μ' (wValid_wswap 0 _ h))] : _ ⟶ _) =
      wl2 (S.wcell μ L ν₂ h.1.1) (KLR.Unfurling.swapW
        (A := End (S.E c (rfl : ν₂ + RDc.iX c = _) ≫ S.E d (wValid_wswap 0 _ h).2)) D same d c
        ![End.of (S.E c (rfl : ν₂ + RDc.iX c = _) ◁ S.dot d (wValid_wswap 0 _ h).2),
          End.of (S.dot c (rfl : ν₂ + RDc.iX c = _) ▷ S.E d (wValid_wswap 0 _ h).2)] :
          _ ⟶ _) := by
    rw [← wl2Alg_apply (k := k), KLR.Unfurling.map_swapW D _ hs _
      (pair_dots_commute S _ _) (pair_dots_nilpotent S hnil _ _)]
    congr 1
    funext t
    fin_cases t
    · exact (wl2_whiskerLeft _ _ _).symm
    · exact (wl2_whiskerRight _ _ _).symm
  have p' : S.E c (rfl : ν₂ + RDc.iX c = _) ≫ S.E d (wValid_wswap 0 _ h).2 =
      S.E c h₂.1.2 ≫ S.E d h₂.2 := by
    obtain rfl : ν₂ + RDc.iX c = y'' := h₂.1.2
    rfl
  refine (congrArg (fun η : S.wcell μ ((c, ν₁) :: (d, ν₂) :: L) μ' h ⟶
    S.wcell μ ((d, y'') :: (c, ν₂) :: L) μ' h₂ => η.hom.app x) ?_).trans (wl2_hom_app _ _ _)
  rw [h1, h2]
  refine (whisker_eq _ (whisker_eq _ (eqToHom_wl2 S (S.wcell μ L ν₂ h.1.1) rfl
    (wValid_wswap 0 _ h).2 h₂.1.2 h₂.2 _ p'))).trans ?_
  refine (whisker_eq _ (wl2_comp _ _ _)).trans ((wl2_comp _ _ _).trans ?_)
  exact congrArg (wl2 (S.wcell μ L ν₂ h.1.1)) (cross_swapW_eqToHom S D same _ _ _ _ _ _ p')

omit [DecidableEq I] [DecidableEq J] in
/-- The coefficient `selfW` of the term of `γ(ψ)` on the same labels, in the dots of the first
two letters of a weighted word, at an object: the coefficient in the dots of the two letters at
the object of the rest. -/
theorem selfW_wdot_app
    (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
    {μ μ' : Xc} (c d : J) (hs : D.π c = D.π d) (hne : c ≠ d) (ν₁ ν₂ : Xc) (L : List (J × Xc))
    (h : wValid RDc μ ((c, ν₁) :: (d, ν₂) :: L) μ') (x : (S.obj μ : Type u₂)) :
    (KLR.Unfurling.selfW (A := End (S.wcell μ ((c, ν₁) :: (d, ν₂) :: L) μ' h)) D c d
        ![End.of (S.wdot μ 0 _ μ' h), End.of (S.wdot μ 1 _ μ' h)] : _ ⟶ _).hom.app x =
    (KLR.Unfurling.selfW (A := End (S.E d h.1.2 ≫ S.E c h.2)) D c d
        ![End.of (S.E d h.1.2 ◁ S.dot c h.2), End.of (S.dot d h.1.2 ▷ S.E c h.2)] :
          _ ⟶ _).hom.app ((S.wcell μ L ν₂ h.1.1).obj.obj x) := by
  have h2 : (KLR.Unfurling.selfW (A := End (S.wcell μ ((c, ν₁) :: (d, ν₂) :: L) μ' h)) D c d
        ![End.of (S.wdot μ 0 _ μ' h), End.of (S.wdot μ 1 _ μ' h)] : _ ⟶ _) =
      wl2 (S.wcell μ L ν₂ h.1.1) (KLR.Unfurling.selfW (A := End (S.E d h.1.2 ≫ S.E c h.2)) D c d
        ![End.of (S.E d h.1.2 ◁ S.dot c h.2), End.of (S.dot d h.1.2 ▷ S.E c h.2)] :
          _ ⟶ _) := by
    rw [← wl2Alg_apply (k := k), KLR.Unfurling.map_selfW D _ hs hne _
      (pair_dots_commute S _ _) (pair_dots_nilpotent S hnil _ _)]
    congr 1
    funext t
    fin_cases t
    · exact (wl2_whiskerLeft _ _ _).symm
    · exact (wl2_whiskerRight _ _ _).symm
  exact (congrArg (fun η : S.wcell μ ((c, ν₁) :: (d, ν₂) :: L) μ' h ⟶
    S.wcell μ ((c, ν₁) :: (d, ν₂) :: L) μ' h => η.hom.app x) h2).trans (wl2_hom_app _ _ _)

omit [DecidableEq I] in
theorem swapCell_eq (same : Prop) [Decidable same] {a b : J} {x y y' z : Xc}
    (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z) (h₃ : x + RDc.iX b = y')
    (h₄ : y' + RDc.iX a = z) :
    swapCell S D same h₁ h₂ h₃ h₄ = S.cross b a h₁ h₂ h₃ h₄ ≫
      (KLR.Unfurling.swapW (A := End (S.E b h₃ ≫ S.E a h₄)) D same a b
        ![End.of (S.E b h₃ ◁ S.dot a h₄), End.of (S.dot b h₃ ▷ S.E a h₄)] : _ ⟶ _) := rfl

omit [DecidableEq I] in
/-- The crossing followed by the coefficient `swapW` in the dots is the cell `swapCell`, for an
equivalent condition on the colours. -/
theorem cross_swapW_app_eq_swapCell (same same' : Prop) [Decidable same] [Decidable same']
    (hiff : same ↔ same') {a b : J} {x y y' z : Xc}
    (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z) (h₃ : x + RDc.iX b = y')
    (h₄ : y' + RDc.iX a = z) (o : (S.obj x : Type u₂)) :
    (S.cross b a h₁ h₂ h₃ h₄ ≫
      (KLR.Unfurling.swapW (A := End (S.E b h₃ ≫ S.E a h₄)) D same a b
        ![End.of (S.E b h₃ ◁ S.dot a h₄), End.of (S.dot b h₃ ▷ S.E a h₄)] : _ ⟶ _)).hom.app o =
      (swapCell S D same' h₁ h₂ h₃ h₄).hom.app o := by
  rw [swapCell_eq, KLR.Unfurling.swapW_congr D hiff]

omit [DecidableEq I] [DecidableEq J] in
theorem wcross_succ_cons {μ μ' : Xc} (j : ℕ) (a : J) (w : Xc) (W' : List (J × Xc))
    (h : wValid RDc μ ((a, w) :: W') μ') :
    S.wcross μ (j + 1) ((a, w) :: W') μ' h = S.wcross μ j W' w h.1 ▷ S.E a h.2 := rfl

omit [DecidableEq I] in
/-- The coefficient `swapW` in the dots of two letters of a weighted word not at its head is
the coefficient in the dots of the tail, whiskered by the head letter. -/
theorem swapW_wdot_succ
    (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
    (same : Prop) [Decidable same] {p q : J} (hs : same → D.π p = D.π q) {μ μ' : Xc} (j : ℕ)
    (a : J) (w : Xc) (W' : List (J × Xc)) (h : wValid RDc μ ((a, w) :: W') μ') :
    (KLR.Unfurling.swapW (A := End (S.wcell μ ((a, w) :: W') μ' h)) D same p q
        ![End.of (S.wdot μ (j + 1) _ μ' h), End.of (S.wdot μ (j + 2) _ μ' h)] : _ ⟶ _) =
      (KLR.Unfurling.swapW (A := End (S.wcell μ W' w h.1)) D same p q
        ![End.of (S.wdot μ j _ w h.1), End.of (S.wdot μ (j + 1) _ w h.1)] : _ ⟶ _) ▷
        S.E a h.2 := by
  rw [← endWR_apply (k := k), KLR.Unfurling.map_swapW D _ hs
    ![End.of (S.wdot μ j _ w h.1), End.of (S.wdot μ (j + 1) _ w h.1)]
    (S.toRouqData.wdot_comm μ j (j + 1) W' w h.1).symm
    (fun t => by fin_cases t <;> exact S.wdot_nilpotent μ hnil _ W' w h.1)]
  congr 1
  funext t
  fin_cases t <;> rfl

omit [DecidableEq I] [DecidableEq J] in
/-- The coefficient `selfW` in the dots of two letters of a weighted word not at its head is
the coefficient in the dots of the tail, whiskered by the head letter. -/
theorem selfW_wdot_succ
    (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
    {p q : J} (hs : D.π p = D.π q) (hne : p ≠ q) {μ μ' : Xc} (j : ℕ)
    (a : J) (w : Xc) (W' : List (J × Xc)) (h : wValid RDc μ ((a, w) :: W') μ') :
    (KLR.Unfurling.selfW (A := End (S.wcell μ ((a, w) :: W') μ' h)) D p q
        ![End.of (S.wdot μ (j + 1) _ μ' h), End.of (S.wdot μ (j + 2) _ μ' h)] : _ ⟶ _) =
      (KLR.Unfurling.selfW (A := End (S.wcell μ W' w h.1)) D p q
        ![End.of (S.wdot μ j _ w h.1), End.of (S.wdot μ (j + 1) _ w h.1)] : _ ⟶ _) ▷
        S.E a h.2 := by
  rw [← endWR_apply (k := k), KLR.Unfurling.map_selfW D _ hs hne
    ![End.of (S.wdot μ j _ w h.1), End.of (S.wdot μ (j + 1) _ w h.1)]
    (S.toRouqData.wdot_comm μ j (j + 1) W' w h.1).symm
    (fun t => by fin_cases t <;> exact S.wdot_nilpotent μ hnil _ W' w h.1)]
  congr 1
  funext t
  fin_cases t <;> rfl

omit [DecidableEq I] in
/-- The crossing of `g̃` on two letters of a weighted word not at its head, followed by the
coefficient `swapW` and a comparison of words, at an object. -/
theorem wcross_swapW_succ_app
    (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
    (same : Prop) [Decidable same] {p q : J} (hs : same → D.π p = D.π q) {μ μ' : Xc} (j : ℕ)
    (a : J) (w : Xc) (W' W₂ : List (J × Xc)) (h : wValid RDc μ ((a, w) :: W') μ')
    (e : wswap RDc (j + 1) ((a, w) :: W') = W₂) (h₂ : wValid RDc μ W₂ μ')
    (x : (S.obj μ : Type u₂)) :
    (S.wcross μ (j + 1) ((a, w) :: W') μ' h ≫
      (KLR.Unfurling.swapW (A := End (S.wcell μ ((a, w) :: wswap RDc j W') μ'
          (wValid_wswap (j + 1) _ h))) D same p q
        ![End.of (S.wdot μ (j + 1) ((a, w) :: wswap RDc j W') μ' (wValid_wswap (j + 1) _ h)),
          End.of (S.wdot μ (j + 2) ((a, w) :: wswap RDc j W') μ' (wValid_wswap (j + 1) _ h))] :
          _ ⟶ _) ≫ eqToHom (S.wcell_congr μ e (wValid_wswap (j + 1) _ h) h₂)).hom.app x =
      (S.E a h.2).obj.map ((S.wcross μ j W' w h.1 ≫
        (KLR.Unfurling.swapW (A := End (S.wcell μ (wswap RDc j W') w (wValid_wswap j _ h.1))) D
          same p q
          ![End.of (S.wdot μ j _ w (wValid_wswap j _ h.1)),
            End.of (S.wdot μ (j + 1) _ w (wValid_wswap j _ h.1))] : _ ⟶ _)).hom.app x) ≫
        (eqToHom (S.wcell_congr μ e (wValid_wswap (j + 1) _ h) h₂)).hom.app x := by
  rw [wcross_succ_cons, swapW_wdot_succ S D hnil same hs j a w (wswap RDc j W')
    (wValid_wswap (j + 1) _ h)]
  exact (Category.assoc _ _ _).symm.trans (eq_whisker ((S.E a h.2).obj.map_comp _ _).symm _)

end Cross

/-! ## Crossings of `g` on the generators of paths -/

section PathCross

variable (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc)
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {P : I → I → MvPolynomial (Fin 2) k} (D : KLR.Unfurling.UnfurlingDatum k P J)
  {μ : X} (M : ∀ β : Φ.Blk μ, blkCat Φ S β.1)

omit [DecidableEq I] [DecidableEq J] in
/-- Exchanging two letters of the same colour of a weighted word of `g` keeps a path. -/
theorem isPath_wswap_of_same (β : J →₀ ℤ) : ∀ (j : ℕ) (L : List (I × X)) (Ps : List J)
    (hj : j + 1 < Ps.length), IsPath Φ β L Ps → Φ.π Ps[j] = Φ.π Ps[j + 1] →
      IsPath Φ β (wswap RD j L) Ps
  | 0, (_, _) :: (_, _) :: _, _ :: _ :: _, _, hP, hs =>
    ⟨⟨hP.1.1, hs.symm.trans hP.2.1, hP.1.2.2⟩, hs.trans hP.1.2.1, hP.2.2⟩
  | j + 1, (_, _) :: L, _ :: Ps, hj, hP, hs =>
    ⟨isPath_wswap_of_same β j L Ps (by simp at hj; omega) hP.1 hs, hP.2.1, hP.2.2⟩
  | 0, [], _ :: _ :: _, _, hP, _ => hP.elim
  | 0, [_], _ :: _ :: _, _, hP, _ => hP.1.elim
  | j + 1, [], _ :: _, _, hP, _ => hP.elim
  | 0, _, [], hj, _, _ => absurd hj (by simp)
  | 0, _, [_], hj, _, _ => absurd hj (by simp)
  | _ + 1, _, [], hj, _, _ => absurd hj (by simp)

omit [DecidableEq I] [DecidableEq J] in
/-- The exchange of two letters of a path: the swapped labels form a path of the swapped word
iff both new edges are relevant. -/
theorem isPath_cons_wswap_iff (β : J →₀ ℤ) (j : ℕ) (c : I) (ν : X) (L : List (I × X))
    (a : J) (Ps : List J) (hP : IsPath Φ β ((c, ν) :: L) (a :: Ps)) :
    IsPath Φ β ((c, ν) :: wswap RD j L) (a :: lswap j Ps) ↔
      IsPath Φ β (wswap RD j L) (lswap j Ps) := by
  refine ⟨fun h => h.1, fun h => ⟨h, hP.2.1, ?_⟩⟩
  rw [endBlk_lswap]; exact hP.2.2

/-- The generator of a path after a comparison of weighted words of `g̃` in the tail, with
the last edge from an arbitrary block `γ`. -/
theorem pgen_cons_transport (β : Φ.Blk μ) (c : I) (ν : X) (L : List (I × X)) (a : J)
    (Ps : List J) {μ' : X} (hL : wValid RD μ ((c, ν) :: L) μ')
    (hP : IsPath Φ β.1 ((c, ν) :: L) (a :: Ps)) (δ : Φ.Blk μ')
    (hδ : endBlk β.1 (a :: Ps) = δ.1) (γ : Φ.Blk ν) (he : endBlk β.1 Ps = γ.1)
    (L' : List (J × Xc)) (hL' : wValid RDc (Φ.wtT β.1) L' (Φ.wtT γ.1))
    (e₁ : L' = liftL Φ β.1 Ps) (h₂ : Φ.wtT γ.1 + RDc.iX a = Φ.wtT δ.1)
    (e₂ : (a, Φ.wtT γ.1) :: L' = liftL Φ β.1 (a :: Ps)) :
    (eqToHom (S.wcell_congr (Φ.wtT β.1) e₂ ⟨hL', h₂⟩
        (wValid_liftL_of_eq Φ β.1 (a :: Ps) hδ))).hom.app (M β) ≫
        pgen Φ S D M β ((c, ν) :: L) (a :: Ps) μ' hL hP δ hδ =
      (S.E a h₂).obj.map ((eqToHom (S.wcell_congr (Φ.wtT β.1) e₁ hL'
          (wValid_liftL_of_eq Φ β.1 Ps he))).hom.app (M β)) ≫
        (Ea Φ S hL.2 ⟨(γ, a), hP.2.1, he ▸ hP.2.2⟩ δ
            (Subtype.ext (show γ.1 + Finsupp.single a 1 = δ.1 from he ▸ hδ))).map
          (pgen Φ S D M β L Ps ν hL.1 hP.1 γ he) ≫
        genE Φ S c hL.2 (((rouqData Φ S D).wcell μ L ν hL.1).obj.obj M)
          ⟨⟨(γ, a), hP.2.1, he ▸ hP.2.2⟩, Subtype.ext (show γ.1 + Finsupp.single a 1 = δ.1 from he ▸ hδ)⟩ := by
  obtain ⟨γ, hγ⟩ := γ
  change endBlk β.1 Ps = γ at he
  subst he e₁
  rw [LinearCat.eqToHom_hom_app, LinearCat.eqToHom_hom_app]
  erw [eqToHom_refl, eqToHom_refl]
  refine (Category.id_comp _).trans ?_
  refine Eq.trans ?_ (eq_whisker ((S.E a h₂).obj.map_id _) _).symm
  refine Eq.trans ?_ (Category.id_comp _).symm
  rfl

open Classical in
/-- The term of the crossing of `g` on the generator of a path to the swapped path: the
crossing of `g̃` with the coefficient `swapW` in its dots, if the swapped labels form a path.
-/
def pcrossSwap (β : Φ.Blk μ) (j : ℕ) (L : List (I × X)) (Ps : List J) (μ' : X)
    (hL : wValid RD μ L μ') (δ : Φ.Blk μ') (hδ : endBlk β.1 Ps = δ.1)
    (hj : j + 1 < Ps.length) :
    (S.wcell (Φ.wtT β.1) (liftL Φ β.1 Ps) (Φ.wtT δ.1)
        (wValid_liftL_of_eq Φ β.1 Ps hδ)).obj.obj (M β) ⟶
      (((rouqData Φ S D).wcell μ (wswap RD j L) μ' (wValid_wswap j L hL)).obj.obj M) δ :=
  if hP' : IsPath Φ β.1 (wswap RD j L) (lswap j Ps) then
    (S.wcross (Φ.wtT β.1) j (liftL Φ β.1 Ps) (Φ.wtT δ.1) (wValid_liftL_of_eq Φ β.1 Ps hδ) ≫
      (KLR.Unfurling.swapW (A := End (S.wcell (Φ.wtT β.1) (wswap RDc j (liftL Φ β.1 Ps))
          (Φ.wtT δ.1) (wValid_wswap j _ (wValid_liftL_of_eq Φ β.1 Ps hδ)))) D
        (Φ.π Ps[j] = Φ.π Ps[j + 1]) Ps[j + 1] Ps[j]
        ![End.of (S.wdot (Φ.wtT β.1) j _ (Φ.wtT δ.1)
            (wValid_wswap j _ (wValid_liftL_of_eq Φ β.1 Ps hδ))),
          End.of (S.wdot (Φ.wtT β.1) (j + 1) _ (Φ.wtT δ.1)
            (wValid_wswap j _ (wValid_liftL_of_eq Φ β.1 Ps hδ)))] : _ ⟶ _) ≫
      eqToHom (S.wcell_congr (Φ.wtT β.1) (wswap_liftL Φ β.1 j Ps) _
        (wValid_liftL_of_eq Φ β.1 (lswap j Ps) ((endBlk_lswap β.1 j Ps).trans hδ)))).hom.app
        (M β) ≫
      pgen Φ S D M β (wswap RD j L) (lswap j Ps) μ' (wValid_wswap j L hL) hP' δ
        ((endBlk_lswap β.1 j Ps).trans hδ)
  else 0

/-- The term of the crossing of `g` on the generator of a path to the same labels, for
distinct labels of the same colour: the coefficient `selfW` in the dots. -/
def pcrossSelf (β : Φ.Blk μ) (j : ℕ) (L : List (I × X)) (Ps : List J) (μ' : X)
    (hL : wValid RD μ L μ') (hP : IsPath Φ β.1 L Ps) (δ : Φ.Blk μ')
    (hδ : endBlk β.1 Ps = δ.1) (hj : j + 1 < Ps.length) :
    (S.wcell (Φ.wtT β.1) (liftL Φ β.1 Ps) (Φ.wtT δ.1)
        (wValid_liftL_of_eq Φ β.1 Ps hδ)).obj.obj (M β) ⟶
      (((rouqData Φ S D).wcell μ (wswap RD j L) μ' (wValid_wswap j L hL)).obj.obj M) δ :=
  if hs : Φ.π Ps[j] = Φ.π Ps[j + 1] ∧ Ps[j] ≠ Ps[j + 1] then
    (KLR.Unfurling.selfW (A := End (S.wcell (Φ.wtT β.1) (liftL Φ β.1 Ps) (Φ.wtT δ.1)
        (wValid_liftL_of_eq Φ β.1 Ps hδ))) D Ps[j] Ps[j + 1]
      ![End.of (S.wdot (Φ.wtT β.1) j _ (Φ.wtT δ.1) (wValid_liftL_of_eq Φ β.1 Ps hδ)),
        End.of (S.wdot (Φ.wtT β.1) (j + 1) _ (Φ.wtT δ.1) (wValid_liftL_of_eq Φ β.1 Ps hδ))] :
        _ ⟶ _).hom.app (M β) ≫
      pgen Φ S D M β (wswap RD j L) Ps μ' (wValid_wswap j L hL)
        (isPath_wswap_of_same Φ β.1 j L Ps hj hP hs.1) δ hδ
  else 0

/-- The generator of a path of length at least two, through the generator of its last two
edges. -/
theorem pgen_cons_cons (β : Φ.Blk μ) (c d : I) (ν₁ ν₂ : X) (L : List (I × X)) (a b : J)
    (Ps : List J) {μ' : X} (hL : wValid RD μ ((c, ν₁) :: (d, ν₂) :: L) μ')
    (hP : IsPath Φ β.1 ((c, ν₁) :: (d, ν₂) :: L) (a :: b :: Ps)) (δ : Φ.Blk μ')
    (hδ : endBlk β.1 (a :: b :: Ps) = δ.1) :
    pgen Φ S D M β _ _ μ' hL hP δ hδ =
      (Ea Φ S hL.2 (pathEdge Φ β c ν₁ ((d, ν₂) :: L) a (b :: Ps) hL.1 hP) δ
          (Subtype.ext hδ)).map
        ((Ea Φ S hL.1.2 (pathEdge Φ β d ν₂ L b Ps hL.1.1 hP.1)
            (pathEdge Φ β c ν₁ ((d, ν₂) :: L) a (b :: Ps) hL.1 hP).src rfl).map
          (pgen Φ S D M β L Ps ν₂ hL.1.1 hP.1.1 (pathEdge Φ β d ν₂ L b Ps hL.1.1 hP.1).src
            rfl)) ≫
        gen₂ Φ S hL.1.2 hL.2 (((rouqData Φ S D).wcell μ L ν₂ hL.1.1).obj.obj M)
          (pathEdge Φ β d ν₂ L b Ps hL.1.1 hP.1)
          (pathEdge Φ β c ν₁ ((d, ν₂) :: L) a (b :: Ps) hL.1 hP) rfl (Subtype.ext hδ) := by
  rw [pgen_cons, pgen_cons]
  exact (eq_whisker (Functor.map_comp _ _ _) _).trans (Category.assoc _ _ _)

/-- The crossing of `g` on the first two letters of a weighted word, at a block. -/
theorem rouqData_wcross_zero_app (c d : I) (ν₁ ν₂ : X) (L : List (I × X)) {μ' : X}
    (hL : wValid RD μ ((c, ν₁) :: (d, ν₂) :: L) μ') (δ : Φ.Blk μ') :
    ((rouqData Φ S D).wcross μ 0 _ μ' hL).hom.app M δ =
      (cross Φ S D hL.1.2 hL.2 (rfl : ν₂ + RD.iX c = _)
        (by rw [← hL.2, ← hL.1.2, add_right_comm])).hom.app
        (((rouqData Φ S D).wcell μ L ν₂ hL.1.1).obj.obj M) δ :=
  congrArg (fun f => f δ) (wl2_hom_app (((rouqData Φ S D).wcell μ L ν₂ hL.1.1))
    (cross Φ S D hL.1.2 hL.2 (rfl : ν₂ + RD.iX c = _)
      (by rw [← hL.2, ← hL.1.2, add_right_comm])) M)

/-- **The crossing of `g` on the generator of a path**, at the first two letters. -/
theorem pgen_wcross_zero
    (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
    (hπ : ∀ a, Φ.π a = D.π a) (β : Φ.Blk μ) (c d : I) (ν₁ ν₂ : X) (L : List (I × X))
    (a b : J) (Ps : List J) {μ' : X} (hL : wValid RD μ ((c, ν₁) :: (d, ν₂) :: L) μ')
    (hP : IsPath Φ β.1 ((c, ν₁) :: (d, ν₂) :: L) (a :: b :: Ps)) (δ : Φ.Blk μ')
    (hδ : endBlk β.1 (a :: b :: Ps) = δ.1) :
    pgen Φ S D M β _ _ μ' hL hP δ hδ ≫ ((rouqData Φ S D).wcross μ 0 _ μ' hL).hom.app M δ =
      pcrossSwap Φ S D M β 0 _ _ μ' hL δ hδ (by simp) +
        pcrossSelf Φ S D M β 0 _ _ μ' hL hP δ hδ (by simp) := by
  refine (eq_whisker (pgen_cons_cons Φ S D M β c d ν₁ ν₂ L a b Ps hL hP δ hδ) _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ ((whisker_eq _ (rouqData_wcross_zero_app Φ S D M c d ν₁ ν₂ L hL δ)).trans
    (gen₂_cross Φ S D _ _ _ _ _ _ _ _ _))).trans ?_
  refine (whisker_eq _ (crossK_next Φ S D hL.1.2 hL.2 (rfl : ν₂ + RD.iX c = _)
    (by rw [← hL.2, ← hL.1.2, add_right_comm]) (((rouqData Φ S D).wcell μ L ν₂ hL.1.1).obj.obj M)
    (pathEdge Φ β d ν₂ L b Ps hL.1.1 hP.1) a hP.2.1 hP.2.2 (Subtype.ext hδ))).trans ?_
  unfold crossNext
  refine (Preadditive.comp_add _ _ _ _ _ _).trans (congrArg₂ (· + ·) ?_ ?_)
  · unfold crossSwap pcrossSwap
    split_ifs with h1 h2 h2
    · refine (Category.assoc _ _ _).symm.trans ?_
      refine (eq_whisker (comp_cell_natural _ _) _).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (whisker_eq _ (pgen_cons_cons Φ S D M β d c (ν₂ + RD.iX c) ν₂ L b a Ps
        (wValid_wswap 0 _ hL) h2 δ ((endBlk_lswap β.1 0 _).trans hδ)).symm)
      refine (eq_whisker ?_ _).symm
      refine (wcross_swapW_eqToHom_app S D hnil _ a b
        (fun h => (hπ b).symm.trans (h.symm.trans (hπ a))) _ _ _ (liftL Φ β.1 Ps) _
        (wswap_liftL Φ β.1 0 (a :: b :: Ps)) _ (M β)).trans ?_
      exact cross_swapW_app_eq_swapCell S D _ _ (show Φ.π a = Φ.π b ↔ c = d from
        ⟨fun h => hP.2.1.symm.trans (h.trans hP.1.2.1),
          fun h => hP.2.1.trans (h.trans hP.1.2.1.symm)⟩) _ _ _ _ _
    · exact absurd ⟨⟨hP.1.1, hP.2.1, h1.1⟩, hP.1.2.1, h1.2⟩ h2
    · exact absurd ⟨h2.1.2.2, h2.2.2⟩ h1
    · exact comp_zero
  · unfold crossSelf pcrossSelf
    split_ifs with h1 h2 h3 h3 h3
    · exact absurd h2.symm h3.2
    · exact comp_zero
    · refine (Category.assoc _ _ _).symm.trans ?_
      refine (eq_whisker (comp_cell_natural _ _) _).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (congrArg₂ (· ≫ ·) (selfW_wdot_app S D hnil a b
        ((hπ a).symm.trans (h3.1.trans (hπ b))) h3.2 (Φ.wtT (endBlk β.1 (b :: Ps)))
        (Φ.wtT (endBlk β.1 Ps)) (liftL Φ β.1 Ps)
        (show wValid RDc (Φ.wtT β.1) ((a, Φ.wtT (endBlk β.1 (b :: Ps))) ::
          (b, Φ.wtT (endBlk β.1 Ps)) :: liftL Φ β.1 Ps) (Φ.wtT δ.1) from
          wValid_liftL_of_eq Φ β.1 (a :: b :: Ps) hδ) (M β)).symm
        (pgen_cons_cons Φ S D M β d c (ν₂ + RD.iX c) ν₂ L a b Ps
          (show wValid RD μ ((d, ν₂ + RD.iX c) :: (c, ν₂) :: L) μ' from wValid_wswap 0 _ hL)
          (show Φ.IsPath β.1 ((d, ν₂ + RD.iX c) :: (c, ν₂) :: L) (a :: b :: Ps) from
            isPath_wswap_of_same Φ β.1 0 _ _ (by simp) hP h3.1) δ hδ).symm)
      subst h1
      rfl
    · exact absurd ⟨hP.2.1.trans (h1.trans hP.1.2.1.symm), fun e => h2 e.symm⟩ h3
    · exact absurd (hP.2.1.symm.trans (h3.1.trans hP.1.2.1)) h1
    · exact comp_zero

/-- The swapped term of the crossing of `g` on a path, after the generator of its last edge. -/
theorem pcrossSwap_cons
    (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
    (hπ : ∀ a, Φ.π a = D.π a) (β : Φ.Blk μ) (j : ℕ) (c : I) (ν : X) (L : List (I × X))
    (a : J) (Ps : List J) {μ' : X} (hL : wValid RD μ ((c, ν) :: L) μ')
    (hP : IsPath Φ β.1 ((c, ν) :: L) (a :: Ps)) (δ : Φ.Blk μ')
    (hδ : endBlk β.1 (a :: Ps) = δ.1) (hj : j + 1 < Ps.length) :
    (Ea Φ S hL.2 (pathEdge Φ β c ν L a Ps hL.1 hP) δ (Subtype.ext hδ)).map
        (pcrossSwap Φ S D M β j L Ps ν hL.1 (pathEdge Φ β c ν L a Ps hL.1 hP).src rfl hj) ≫
      genE Φ S c hL.2
        (((rouqData Φ S D).wcell μ (wswap RD j L) ν (wValid_wswap j L hL.1)).obj.obj M)
        ⟨pathEdge Φ β c ν L a Ps hL.1 hP, Subtype.ext hδ⟩ =
      pcrossSwap Φ S D M β (j + 1) ((c, ν) :: L) (a :: Ps) μ' hL δ hδ
        (Nat.succ_lt_succ hj) := by
  unfold pcrossSwap
  split_ifs with h1 h2 h2
  · refine Eq.trans ?_ (eq_whisker (wcross_swapW_succ_app S D hnil (Φ.π Ps[j] = Φ.π Ps[j + 1])
      (fun h => (hπ _).symm.trans (h.symm.trans (hπ _))) j a (Φ.wtT (endBlk β.1 Ps))
      (liftL Φ β.1 Ps) _ (wValid_liftL_of_eq Φ β.1 (a :: Ps) hδ)
      (wswap_liftL Φ β.1 (j + 1) (a :: Ps))
      (wValid_liftL_of_eq Φ β.1 (lswap (j + 1) (a :: Ps))
        ((endBlk_lswap β.1 (j + 1) (a :: Ps)).trans hδ)) (M β)).symm _)
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (whisker_eq _ (pgen_cons_transport Φ S D M β c ν (wswap RD j L) a
      (lswap j Ps) (wValid_wswap (j + 1) _ hL) h2 δ ((endBlk_lswap β.1 (j + 1) (a :: Ps)).trans hδ)
      (pathEdge Φ β c ν L a Ps hL.1 hP).src (endBlk_lswap β.1 j Ps)
      (wswap RDc j (liftL Φ β.1 Ps)) (wValid_wswap j _ (wValid_liftL Φ β.1 Ps))
      (wswap_liftL Φ β.1 j Ps) (wValid_liftL_of_eq Φ β.1 (a :: Ps) hδ).2
      (wswap_liftL Φ β.1 (j + 1) (a :: Ps))).symm)
    refine (eq_whisker (Functor.map_comp _ _ _) _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine eq_whisker ?_ _
    refine Eq.trans ?_ (Functor.map_comp _ _ _)
    exact congrArg _ (Category.assoc _ _ _).symm
  · exact absurd ((isPath_cons_wswap_iff Φ β.1 j c ν L a Ps hP).2 h1) h2
  · exact absurd ((isPath_cons_wswap_iff Φ β.1 j c ν L a Ps hP).1 h2) h1
  · exact (eq_whisker (Functor.map_zero _ _ _) _).trans zero_comp

/-- The term on the same labels of the crossing of `g` on a path, after the generator of its
last edge. -/
theorem pcrossSelf_cons
    (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
    (hπ : ∀ a, Φ.π a = D.π a) (β : Φ.Blk μ) (j : ℕ) (c : I) (ν : X) (L : List (I × X))
    (a : J) (Ps : List J) {μ' : X} (hL : wValid RD μ ((c, ν) :: L) μ')
    (hP : IsPath Φ β.1 ((c, ν) :: L) (a :: Ps)) (δ : Φ.Blk μ')
    (hδ : endBlk β.1 (a :: Ps) = δ.1) (hj : j + 1 < Ps.length) :
    (Ea Φ S hL.2 (pathEdge Φ β c ν L a Ps hL.1 hP) δ (Subtype.ext hδ)).map
        (pcrossSelf Φ S D M β j L Ps ν hL.1 hP.1 (pathEdge Φ β c ν L a Ps hL.1 hP).src rfl hj) ≫
      genE Φ S c hL.2
        (((rouqData Φ S D).wcell μ (wswap RD j L) ν (wValid_wswap j L hL.1)).obj.obj M)
        ⟨pathEdge Φ β c ν L a Ps hL.1 hP, Subtype.ext hδ⟩ =
      pcrossSelf Φ S D M β (j + 1) ((c, ν) :: L) (a :: Ps) μ' hL hP δ hδ
        (Nat.succ_lt_succ hj) := by
  unfold pcrossSelf
  split_ifs with h1 h2 h2
  · refine Eq.trans ?_ (congrArg₂ (· ≫ ·)
      (congrArg (fun η => η.hom.app (M β)) (selfW_wdot_succ S D hnil
        ((hπ _).symm.trans (h1.1.trans (hπ _))) h1.2 j a (Φ.wtT (endBlk β.1 Ps))
        (liftL Φ β.1 Ps) (wValid_liftL_of_eq Φ β.1 (a :: Ps) hδ))).symm
      (pgen_cons Φ S D M β c ν (wswap RD j L) a Ps (wValid_wswap (j + 1) _ hL)
        (isPath_wswap_of_same Φ β.1 (j + 1) ((c, ν) :: L) (a :: Ps) (Nat.succ_lt_succ hj) hP h1.1) δ hδ).symm)
    exact (eq_whisker (Functor.map_comp _ _ _) _).trans (Category.assoc _ _ _)
  · exact absurd h1 h2
  · exact absurd h2 h1
  · exact (eq_whisker (Functor.map_zero _ _ _) _).trans zero_comp

/-- **The crossings of `g` on the generators of paths**: the crossing of `g` on the `j`-th and
`(j+1)`-th letters, on the generator of the path with labels `Ps`, is the sum of the term to
the swapped path and the term to the same labels (`pcrossSwap`, `pcrossSelf`). -/
theorem pgen_wcross
    (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
    (hπ : ∀ a, Φ.π a = D.π a) (β : Φ.Blk μ) : ∀ (j : ℕ) (L : List (I × X)) (Ps : List J)
    (μ' : X) (hL : wValid RD μ L μ') (hP : IsPath Φ β.1 L Ps) (δ : Φ.Blk μ')
    (hδ : endBlk β.1 Ps = δ.1) (hj : j + 1 < Ps.length),
    pgen Φ S D M β L Ps μ' hL hP δ hδ ≫ ((rouqData Φ S D).wcross μ j L μ' hL).hom.app M δ =
      pcrossSwap Φ S D M β j L Ps μ' hL δ hδ hj + pcrossSelf Φ S D M β j L Ps μ' hL hP δ hδ hj
  | 0, (c, ν₁) :: (d, ν₂) :: L, a :: b :: Ps, _, hL, hP, δ, hδ, _ =>
    pgen_wcross_zero Φ S D M hnil hπ β c d ν₁ ν₂ L a b Ps hL hP δ hδ
  | j + 1, (c, ν) :: L, a :: Ps, μ', hL, hP, δ, hδ, hj => by
    have hj' : j + 1 < Ps.length := Nat.lt_of_succ_lt_succ hj
    refine (eq_whisker (pgen_cons Φ S D M β c ν L a Ps hL hP δ hδ) _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    have hd : ((rouqData Φ S D).wcross μ (j + 1) ((c, ν) :: L) μ' hL).hom.app M δ =
        (E Φ S c hL.2).obj.map (((rouqData Φ S D).wcross μ j L ν hL.1).hom.app M) δ := rfl
    refine (whisker_eq _ (whisker_eq _ hd)).trans ?_
    refine (whisker_eq _ (genE_natural Φ S hL.2
      (((rouqData Φ S D).wcross μ j L ν hL.1).hom.app M)
      ⟨pathEdge Φ β c ν L a Ps hL.1 hP, Subtype.ext hδ⟩)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (eq_whisker (Functor.map_comp _ _ _).symm _).trans ?_
    refine (eq_whisker ((Ea Φ S hL.2 (pathEdge Φ β c ν L a Ps hL.1 hP) δ
      (Subtype.ext hδ)).congr_map (pgen_wcross hnil hπ β j L Ps ν hL.1 hP.1 _ rfl hj')) _).trans ?_
    refine (eq_whisker (Functor.map_add _) _).trans ?_
    refine (Preadditive.add_comp _ _ _ _ _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · exact pcrossSwap_cons Φ S D M hnil hπ β j c ν L a Ps hL hP δ hδ hj'
    · exact pcrossSelf_cons Φ S D M hnil hπ β j c ν L a Ps hL hP δ hδ hj'
  | 0, [], _ :: _ :: _, _, _, hP, _, _, _ => hP.elim
  | 0, [_], _ :: _ :: _, _, _, hP, _, _, _ => hP.1.elim
  | _ + 1, [], _ :: _, _, _, hP, _, _, _ => hP.elim
  | 0, _, [], _, _, _, _, _, hj => absurd hj (by simp)
  | 0, _, [_], _, _, _, _, _, hj => absurd hj (by simp)
  | _ + 1, _, [], _, _, _, _, _, hj => absurd hj (by simp)

end PathCross

end Furling

end Categorification.TwoRep
