/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingMixed
import Categorification.TwoRep.RouqReparam
import Categorification.TwoRep.FurlingIntertwine
import Categorification.TwoRep.FurlingKLR
import Categorification.TwoRep.RouqCoproductNeg

/-!
# Reparametrized label data for the shift-zero block

The labelwise data and teleporters in Webster, *Unfurling Khovanov–Lauda–Rouquier
algebras*, arXiv:1603.06311v3, §2.3, equation `a-auto` and Lemma `many-sl2`.
The constant part of each spectral polynomial is separated from its nilpotent part.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe wk v₁ u₁ u₂ u₃ u₄

/-- A polynomial with zero constant coefficient preserves nilpotence. -/
theorem isNilpotent_aeval_of_coeff_zero {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
    {x : A} (hx : IsNilpotent x) {f : Polynomial k} (hf : f.coeff 0 = 0) :
    IsNilpotent (Polynomial.aeval x f) := by
  obtain ⟨g, rfl⟩ := Polynomial.X_dvd_iff.mpr hf
  rw [map_mul, Polynomial.aeval_X]
  have hc : Commute x (Polynomial.aeval x g) := by
    simpa using (Commute.all (Polynomial.X : Polynomial k) g).map (Polynomial.aeval x)
  exact hc.isNilpotent_mul_right hx

private theorem shifted_sub {A : Type*} [AddCommGroup A] (a b x y : A) :
    (a + x) - (b + y) = a - b + x - y := by abel

private theorem unit_map_comp_chain {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {W X Y : A} {Z : B} (u : Z ⟶ F.obj W) (f : W ⟶ X) (g : X ⟶ Y) :
    u ≫ F.map (f ≫ g) = u ≫ F.map f ≫ F.map g := by rw [F.map_comp]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

namespace Furling

variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*}
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc} {RD : QuantumGroup.UDot.WeightDatum C X Y}
  {Φ : Furling RDc RD}
  (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc)
  {P : I → I → MvPolynomial (Fin 2) k} (D : KLR.Unfurling.UnfurlingDatum k P J)

/-- The zero-constant part of the spectral polynomial. -/
def zeroPw (a : J) : Polynomial k := D.pw a - Polynomial.C ((D.pw a).coeff 0)

@[simp] theorem zeroPw_coeff_zero (a : J) : (zeroPw D a).coeff 0 = 0 := by
  simp [zeroPw]

@[simp] theorem zeroPw_coeff_one (a : J) : (zeroPw D a).coeff 1 = (D.pw a).coeff 1 := by
  simp [zeroPw]

/-- Removing a constant does not change the divided difference. -/
theorem ddiff_zeroPw (a : J) :
    ddiff 0 1 (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (zeroPw D a)) =
      KLR.Unfurling.pwDiff D a := by
  simp [zeroPw, KLR.Unfurling.pwDiff, KLR.Unfurling.pwAt, map_sub]

variable (hnil : ∀ (a : J) {x y : Xc} (h : x + RDc.iX a = y),
  IsNilpotent (End.of (S.dot a h)))

include hnil in
/-- The two dots around a weight admit a common nilpotence exponent. -/
theorem exists_dot_bound (a : J) {x y z : Xc} (h₁ : x + RDc.iX a = y)
    (h₂ : y + RDc.iX a = z) :
    ∃ n, powComp (S.dot a h₁) n = 0 ∧ powComp (S.dot a h₂) n = 0 := by
  obtain ⟨n, hn⟩ := hnil a h₁
  obtain ⟨m, hm⟩ := hnil a h₂
  refine ⟨n + m, powComp_eq_zero_of_le ?_ (Nat.le_add_right _ _),
    powComp_eq_zero_of_le ?_ (Nat.le_add_left _ _)⟩
  · simpa only [powComp_eq_pow'] using hn
  · simpa only [powComp_eq_pow'] using hm

variable [DecidableEq J]

/-- Webster's reparametrization on a single cover label, with its constant shift removed. -/
def zeroLoc (a : J) {x y z : Xc} (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX a = z) :
    RouqLoc (S.adj a h₁) (S.adj a h₂)
      (Polynomial.aeval (End.of (S.dot a h₁)) (zeroPw D a))
      (Polynomial.aeval (End.of (S.dot a h₂)) (zeroPw D a))
      (swapCell S D True h₁ h₂ h₁ h₂) (RDc.pair (RDc.iY a) y) := by
  let H := exists_dot_bound S hnil a h₁ h₂
  have hn := H.choose_spec.1
  have hm := H.choose_spec.2
  have L := (S.loc a h₁ h₂).reparam hn hm (zeroPw_coeff_zero D a)
    (by simpa using D.pw_coeff_one a)
  convert L using 1
  simp only [swapCell, ite_true, RouqLoc.reparamCross, ddiff_zeroPw, pairEval]

omit [DecidableEq J] in
include hnil in
/-- The reparametrized dot is nilpotent. -/
theorem zeroDot_nilpotent (a : J) {x y : Xc} (h : x + RDc.iX a = y) :
    IsNilpotent (Polynomial.aeval (End.of (S.dot a h)) (zeroPw D a)) :=
  isNilpotent_aeval_of_coeff_zero (hnil a h) (zeroPw_coeff_zero D a)

omit [DecidableEq J] in
include hnil in
/-- The distinct-label position-preserving crossing inverts its spectral difference. -/
theorem selfCell_comp_difference {a b : J} (hab : a ≠ b) (hπ : D.π a = D.π b)
    {x y z : Xc} (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z) :
    selfCell S D h₁ h₂ ≫
      pairEval S h₁ h₂ (KLR.Unfurling.pwAt D.pw b 0 - KLR.Unfurling.pwAt D.pw a 1) = 𝟙 _ := by
  have hu := KLR.isUnit_ncEval _ (commute_vecTwo (pair_dots_commute S h₁ h₂))
    (pair_dots_nilpotent S hnil h₁ h₂) _
    (KLR.Unfurling.isUnit_constantCoeff_pwAt_sub D hπ.symm hab.symm)
  exact Ring.mul_inverse_cancel _ hu

omit [DecidableEq J] in
/-- Evaluation separates a spectral polynomial into its eigenvalue and nilpotent part. -/
theorem aeval_pw_eq {A : Type*} [Ring A] [Algebra k A] (x : A) (a : J) :
    Polynomial.aeval x (D.pw a) = (D.pw a).coeff 0 • (1 : A) +
      Polynomial.aeval x (zeroPw D a) := by
  simp only [zeroPw, map_sub, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  abel

omit [DecidableEq J] in
/-- The spectral difference is precisely the shifted difference in the coproduct theorem. -/
theorem pairEval_difference {a b : J} {x y z : Xc}
    (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z) :
    pairEval S h₁ h₂ (KLR.Unfurling.pwAt D.pw b 0 - KLR.Unfurling.pwAt D.pw a 1) =
      ((D.pw b).coeff 0 - (D.pw a).coeff 0) • 𝟙 _ +
        S.E a h₁ ◁ Polynomial.aeval (End.of (S.dot b h₂)) (zeroPw D b) -
        Polynomial.aeval (End.of (S.dot a h₁)) (zeroPw D a) ▷ S.E b h₂ := by
  rw [pairEval, ncEval_eq_evalTwo _ _ (pair_dots_commute S h₁ h₂), map_sub]
  simp only [KLR.Unfurling.pwAt, ← Polynomial.aeval_algHom_apply,
    evalTwo_X_zero, evalTwo_X_one]
  rw [aeval_pw_eq D _ b, aeval_pw_eq D _ a]
  have hl := Polynomial.aeval_algHom_apply (endWL k (S.E a h₁) (S.E b h₂))
    (End.of (S.dot b h₂)) (zeroPw D b)
  have hr := Polynomial.aeval_algHom_apply (endWR k (S.E a h₁) (S.E b h₂))
    (End.of (S.dot a h₁)) (zeroPw D a)
  change Polynomial.aeval (End.of (S.E a h₁ ◁ S.dot b h₂)) (zeroPw D b) = _ at hl
  change Polynomial.aeval (End.of (S.dot a h₁ ▷ S.E b h₂)) (zeroPw D a) = _ at hr
  rw [hl, hr, sub_smul]
  exact shifted_sub _ _ _ _

omit [DecidableEq J] in
include hnil in
/-- The off-diagonal teleporter relation, now in the exact form of the coproduct theorem. -/
theorem selfCell_teleporter {a b : J} (hab : a ≠ b) (hπ : D.π a = D.π b)
    {x y z : Xc} (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z) :
    selfCell S D h₁ h₂ ≫
      (((D.pw b).coeff 0 - (D.pw a).coeff 0) • 𝟙 _ +
        S.E a h₁ ◁ Polynomial.aeval (End.of (S.dot b h₂)) (zeroPw D b) -
        Polynomial.aeval (End.of (S.dot a h₁)) (zeroPw D a) ▷ S.E b h₂) = 𝟙 _ := by
  rw [← pairEval_difference S D]
  exact selfCell_comp_difference S D hnil hab hπ h₁ h₂

section Block

variable (Φ) (i : I) (β : J →₀ ℤ)

/-- The reparametrized local family indexed by the relevant labels at a block. -/
abbrev blockZeroLoc (t : Fin (nLbl Φ i β)) :=
  zeroLoc S D hnil (lab Φ i β t) (wtT_sub_add (Φ := Φ) β _) (Φ.wtT_add_single β _)

omit [DecidableEq J] in
include hnil in
/-- The finite family of zero-constant dots admits one nilpotence bound. -/
theorem blockZero_bound : ∃ n,
    (∀ t : Fin (nLbl Φ i β), powComp
      (Polynomial.aeval (End.of (S.dot (lab Φ i β t) (wtT_sub_add (Φ := Φ) β _)))
        (zeroPw D (lab Φ i β t))) n = 0) ∧
    (∀ t : Fin (nLbl Φ i β), powComp
      (Polynomial.aeval (End.of (S.dot (lab Φ i β t) (Φ.wtT_add_single β _)))
        (zeroPw D (lab Φ i β t))) n = 0) := by
  let H₁ := fun t : Fin (nLbl Φ i β) => zeroDot_nilpotent S D hnil (lab Φ i β t)
    (wtT_sub_add (Φ := Φ) β _)
  let H₂ := fun t : Fin (nLbl Φ i β) => zeroDot_nilpotent S D hnil (lab Φ i β t)
    (Φ.wtT_add_single β _)
  let n₁ := fun t => (H₁ t).choose
  let n₂ := fun t => (H₂ t).choose
  refine ⟨∑ t, (n₁ t + n₂ t), ?_, ?_⟩
  · intro t
    apply powComp_eq_zero_of_le (by simpa only [powComp_eq_pow'] using (H₁ t).choose_spec)
    exact (Nat.le_add_right (n₁ t) (n₂ t)).trans (Finset.single_le_sum
      (f := fun t => n₁ t + n₂ t) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t))
  · intro t
    apply powComp_eq_zero_of_le (by simpa only [powComp_eq_pow'] using (H₂ t).choose_spec)
    exact (Nat.le_add_left (n₂ t) (n₁ t)).trans (Finset.single_le_sum
      (f := fun t => n₁ t + n₂ t) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t))

omit [DecidableEq J] in
/-- The spectral constants of the relevant labels of one base colour are distinct. -/
theorem blockZero_constants_injective (hπ : Φ.π = D.π) :
    Function.Injective (fun t : Fin (nLbl Φ i β) => (D.pw (lab Φ i β t)).coeff 0) := by
  intro t t' he
  apply lab_injective (Φ := Φ) β
  apply D.pw_coeff_zero_inj _ _ _ he
  rw [← hπ, lab_π β t, lab_π β t']

include hnil in
/-- The positive coproduct inverse for the shift-zero family, with teleporters constructed
from the spectral polynomials rather than supplied as hypotheses (Webster §2.3). -/
theorem isIso_blockZero_pos (hπ : Φ.π = D.π)
    (hh : 0 ≤ ∑ t : Fin (nLbl Φ i β), RDc.pair (RDc.iY (lab Φ i β t)) (Φ.wtT β)) :
    IsIso (biprod.lift
      (RouqCoproduct.rouqSig (blockZeroLoc (S := S) (D := D) (hnil := hnil) (Φ := Φ) (i := i) (β := β))
        (fun t t' => selfCell S D (wtT_sub_add (Φ := Φ) β (lab Φ i β t))
          (Φ.wtT_add_single β (lab Φ i β t'))))
      (RouqCoproduct.rouqCaps (blockZeroLoc (S := S) (D := D) (hnil := hnil) (Φ := Φ) (i := i) (β := β))
        (fun t => (D.pw (lab Φ i β t)).coeff 0)
        (∑ t : Fin (nLbl Φ i β), RDc.pair (RDc.iY (lab Φ i β t)) (Φ.wtT β)).toNat)) := by
  obtain ⟨n, hn, hm⟩ := blockZero_bound (S := S) (D := D) (hnil := hnil) (Φ := Φ) (i := i) (β := β)
  refine RouqCoproduct.isIso_rouqMap_of_nonneg (blockZeroLoc (S := S) (D := D) (hnil := hnil) (Φ := Φ) (i := i) (β := β))
    hn hm (blockZero_constants_injective (D := D) (Φ := Φ) (i := i) (β := β) hπ) _ ?_ hh
  intro t t' hne
  apply selfCell_teleporter S D hnil (fun h => hne (lab_injective (Φ := Φ) β h))
  rw [← hπ, lab_π β t, lab_π β t']

include hnil in
/-- The negative coproduct inverse for the same shift-zero family (Webster §2.3). -/
theorem isIso_blockZero_neg (hπ : Φ.π = D.π)
    (hh : (∑ t : Fin (nLbl Φ i β), RDc.pair (RDc.iY (lab Φ i β t)) (Φ.wtT β)) ≤ 0) :
    IsIso (biprod.desc
      (RouqCoproduct.rouqSig (blockZeroLoc (S := S) (D := D) (hnil := hnil) (Φ := Φ) (i := i) (β := β))
        (fun t t' => selfCell S D (wtT_sub_add (Φ := Φ) β (lab Φ i β t))
          (Φ.wtT_add_single β (lab Φ i β t'))))
      (RouqCoproduct.rouqCups (blockZeroLoc (S := S) (D := D) (hnil := hnil) (Φ := Φ) (i := i) (β := β))
        (fun t => (D.pw (lab Φ i β t)).coeff 0)
        (-(∑ t : Fin (nLbl Φ i β), RDc.pair (RDc.iY (lab Φ i β t)) (Φ.wtT β))).toNat)) := by
  obtain ⟨n, hn, hm⟩ := blockZero_bound (S := S) (D := D) (hnil := hnil) (Φ := Φ) (i := i) (β := β)
  refine RouqCoproduct.isIso_rouqMap_of_nonpos (blockZeroLoc (S := S) (D := D) (hnil := hnil) (Φ := Φ) (i := i) (β := β))
    hn hm (blockZero_constants_injective (D := D) (Φ := Φ) (i := i) (β := β) hπ) _ ?_ hh
  intro t t' hne
  apply selfCell_teleporter S D hnil (fun h => hne (lab_injective (Φ := Φ) β h))
  rw [← hπ, lab_π β t, lab_π β t']

end Block

section Entries

variable [DecidableEq I] [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {i : I} {l l' l'' : X} (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')
  (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1)

/-- The diagonal shift-zero entry on an edge is the reparametrized sideways crossing. -/
theorem genFE_self_sigma_diag (p : Φ.Edge i l) (hr : Φ.rel (p.tgt h₁).1 p.lbl) :
    genFE Φ S h₁ N p p.lbl p.π_lbl p.rel_src ≫ (sigma Φ S D h₁ h₂).hom.app N (p.tgt h₁) ≫
      (projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) (Edge.next h₁ p p.lbl p.π_lbl hr) ≫
        (Fa Φ S h₂ (Edge.next h₁ p p.lbl p.π_lbl hr) _ rfl).map
          (projEb S h₂ N ⟨Edge.next h₁ p p.lbl p.π_lbl hr, rfl⟩)) =
      (RightwardCrossing.sigma
        (S.adj p.lbl (wt_tgt h₂ (Edge.next h₁ p p.lbl p.π_lbl hr) rfl)).unit
        (swapCell S D True (wt_tgt h₁ p rfl)
          (wt_tgt h₂ (Edge.next h₁ p p.lbl p.π_lbl hr) rfl)
          (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p p.lbl p.π_lbl hr) rfl))
        (S.adj p.lbl (wt_tgt h₁ p rfl)).counit).hom.app (N (p.tgt h₁)) := by
  have H := genFE_sigma_swap_entry D h₁ h₂ N p p.lbl p.π_lbl p.rel_src hr hr
  calc
    _ = _ := H
    _ = _ := by
      rw [LinearCat.sigma_hom_app]
      simp only [swapCell, ite_true]
      exact unit_map_comp_chain
        (S.F p.lbl (wt_tgt h₂ (Edge.next h₁ p p.lbl p.π_lbl hr) rfl)).obj _ _ _

end Entries

end Furling
end Categorification.TwoRep
