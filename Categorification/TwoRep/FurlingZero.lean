/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingMixed
import Categorification.TwoRep.RouqReparam
import Categorification.TwoRep.FurlingIntertwine
import Categorification.TwoRep.FurlingKLR
import Categorification.TwoRep.RouqCoproductNeg
import Categorification.TwoRep.SumInvBiprod

/-!
# Reparametrized label data for the shift-zero block

The labelwise data and teleporters in Webster, *Unfurling Khovanov–Lauda–Rouquier
algebras*, arXiv:1603.06311v3, §2.3, equation `a-auto` and Lemma `many-sl2`.
The constant part of each spectral polynomial is separated from its nilpotent part.
The resulting coproduct crossing matrix, evaluated at an object of a weight block,
is the shift-zero block `desc sZ ≫ sigma ≫ lift rZ′` of the furled action.
The dotted cap and cup matrices agree as well; `zeroPos` and `zeroNeg` construct
the shift-zero sum inverses. The correction-summand count is transported along an
explicit pairing identity, which must be supplied by a cover specialization.
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

/-- The off-diagonal shift-zero entry is the sideways teleporter. -/
theorem genFE_self_sigma_offdiag (p : Φ.Edge i l) (c : J) (hc : Φ.π c = i)
    (hr : Φ.rel (p.tgt h₁).1 c) (hac : p.lbl ≠ c) :
    genFE Φ S h₁ N p p.lbl p.π_lbl p.rel_src ≫ (sigma Φ S D h₁ h₂).hom.app N (p.tgt h₁) ≫
      (projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) (Edge.next h₁ p c hc hr) ≫
        (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
          (projEb S h₂ N ⟨Edge.next h₁ p c hc hr, rfl⟩)) =
      (RightwardCrossing.sigma
        (S.adj c (wt_tgt h₂ (Edge.next h₁ p c hc hr) rfl)).unit
        (selfCell S D (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p c hc hr) rfl))
        (S.adj p.lbl (wt_tgt h₁ p rfl)).counit).hom.app (N (p.tgt h₁)) := by
  have H := chain_swap_id _ _ _ _ _ _ _ _ _
    (genFE_sigma_projF_self Φ S D h₁ h₂ N p c hc hr hac)
    (genE_projEb S h₂ N ⟨selfSnd Φ h₁ h₁ rfl p c hc hr,
      selfSnd_tgt Φ h₁ h₂ h₁ h₂ rfl p c hc hr rfl⟩)
  calc
    _ = _ := H
    _ = _ := by
      rw [LinearCat.sigma_hom_app]
      exact unit_map_comp_chain (S.F c (wt_tgt h₂ (Edge.next h₁ p c hc hr) rfl)).obj _ _ _

/-- The diagonal crossing entry with a specified incoming edge and its target block. -/
theorem self_sigma_diag (δ : Φ.Blk l') (p : {e : Φ.Edge i l // e.tgt h₁ = δ})
    (hr : Φ.rel δ.1 p.1.lbl) :
    ((Ea Φ S h₁ p.1 δ p.2).map ((trF S h₁ N p.1 p.2).hom ≫ incF Φ S h₁ N p.1) ≫
      genE Φ S i h₁ ((F Φ S i h₁).obj.obj N) p) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
      (projFq S h₂ ((E Φ S i h₂).obj.obj N) ⟨outEdge δ p.1.lbl p.1.π_lbl hr, rfl⟩ ≫
        (Fa Φ S h₂ (outEdge δ p.1.lbl p.1.π_lbl hr) _ rfl).map
          (projEb S h₂ N ⟨outEdge δ p.1.lbl p.1.π_lbl hr, rfl⟩)) =
      (RightwardCrossing.sigma (S.adj p.1.lbl (Φ.wtT_add_single δ.1 p.1.lbl)).unit
        (swapCell S D True (wt_tgt h₁ p.1 p.2) (Φ.wtT_add_single δ.1 p.1.lbl)
          (wt_tgt h₁ p.1 p.2) (Φ.wtT_add_single δ.1 p.1.lbl))
        (S.adj p.1.lbl (wt_tgt h₁ p.1 p.2)).counit).hom.app (N δ) := by
  obtain ⟨p, hp⟩ := p
  subst hp
  exact (map_id_comp_chain _ (trF S h₁ N p rfl).hom _ _ _ rfl).trans
    (genFE_self_sigma_diag S D h₁ h₂ N p hr)

/-- The diagonal entry on canonical block inclusions and projections. -/
theorem sZ_sigma_rZ'_diag (δ : Φ.Blk l') (t : Fin (nLbl Φ i δ.1))
    (hr₁ : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t))
    (hr₂ : Φ.rel δ.1 (lab Φ i δ.1 t)) :
    sZ h₁ N δ t ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫ rZ' h₂ N δ t =
      (RightwardCrossing.sigma
        (S.adj (lab Φ i δ.1 t) (Φ.wtT_add_single δ.1 _)).unit
        (swapCell S D True (wtT_sub_add (Φ := Φ) δ.1 _)
          (Φ.wtT_add_single δ.1 _) (wtT_sub_add (Φ := Φ) δ.1 _)
          (Φ.wtT_add_single δ.1 _))
        (S.adj (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _)).counit).hom.app (N δ) := by
  simp only [sZ, rZ', hr₁, hr₂, dite_true]
  exact self_sigma_diag S D h₁ h₂ N δ (pIn h₁ δ t hr₁) hr₂

/-- The off-diagonal crossing entry with a specified incoming edge and its target block. -/
theorem self_sigma_offdiag (δ : Φ.Blk l') (p : {e : Φ.Edge i l // e.tgt h₁ = δ})
    (c : J) (hc : Φ.π c = i) (hr : Φ.rel δ.1 c) (hac : p.1.lbl ≠ c) :
    ((Ea Φ S h₁ p.1 δ p.2).map ((trF S h₁ N p.1 p.2).hom ≫ incF Φ S h₁ N p.1) ≫
      genE Φ S i h₁ ((F Φ S i h₁).obj.obj N) p) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
      (projFq S h₂ ((E Φ S i h₂).obj.obj N) ⟨outEdge δ c hc hr, rfl⟩ ≫
        (Fa Φ S h₂ (outEdge δ c hc hr) _ rfl).map
          (projEb S h₂ N ⟨outEdge δ c hc hr, rfl⟩)) =
      (RightwardCrossing.sigma (S.adj c (Φ.wtT_add_single δ.1 c)).unit
        (selfCell S D (wt_tgt h₁ p.1 p.2) (Φ.wtT_add_single δ.1 c))
        (S.adj p.1.lbl (wt_tgt h₁ p.1 p.2)).counit).hom.app (N δ) := by
  obtain ⟨p, hp⟩ := p
  subst hp
  exact (map_id_comp_chain _ (trF S h₁ N p rfl).hom _ _ _ rfl).trans
    (genFE_self_sigma_offdiag S D h₁ h₂ N p c hc hr hac)

/-- The teleporter entry on canonical block inclusions and projections. -/
theorem sZ_sigma_rZ'_offdiag (δ : Φ.Blk l') (t t' : Fin (nLbl Φ i δ.1)) (hne : t ≠ t')
    (hr₁ : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t))
    (hr₂ : Φ.rel δ.1 (lab Φ i δ.1 t')) :
    sZ h₁ N δ t ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫ rZ' h₂ N δ t' =
      (RightwardCrossing.sigma
        (S.adj (lab Φ i δ.1 t') (Φ.wtT_add_single δ.1 _)).unit
        (selfCell S D (wtT_sub_add (Φ := Φ) δ.1 (lab Φ i δ.1 t))
          (Φ.wtT_add_single δ.1 (lab Φ i δ.1 t')))
        (S.adj (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _)).counit).hom.app (N δ) := by
  simp only [sZ, rZ', hr₁, hr₂, dite_true]
  exact self_sigma_offdiag S D h₁ h₂ N δ (pIn h₁ δ t hr₁) (lab Φ i δ.1 t')
    (lab_π δ.1 t') hr₂ (fun h => hne (lab_injective δ.1 h))

variable (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y),
    ¬ Φ.rel β a → IsZero (S.E a h))

private theorem diag_off_self {A : Type} [Fintype A] [DecidableEq A]
    {B : Type*} [Category B] [Preadditive B] {X Y : A → B}
    (f : ∀ a, X a ⟶ Y a) (g : ∀ a b, X a ⟶ Y b) (a : A) :
    ((RouqCoproduct.diagMat f : (⟨A, X⟩ : Mat_ B) ⟶ ⟨A, Y⟩) +
      (show (⟨A, X⟩ : Mat_ B) ⟶ ⟨A, Y⟩ from fun a b => if a = b then 0 else g a b)) a a = f a := by
  change (if h : a = a then f a ≫ eqToHom (congrArg Y h) else 0) +
    (if a = a then 0 else g a a) = f a
  simp

private theorem diag_off_ne {A : Type} [Fintype A] [DecidableEq A]
    {B : Type*} [Category B] [Preadditive B] {X Y : A → B}
    (f : ∀ a, X a ⟶ Y a) (g : ∀ a b, X a ⟶ Y b) (a b : A) (h : a ≠ b) :
    ((RouqCoproduct.diagMat f : (⟨A, X⟩ : Mat_ B) ⟶ ⟨A, Y⟩) +
      (show (⟨A, X⟩ : Mat_ B) ⟶ ⟨A, Y⟩ from fun a b => if a = b then 0 else g a b)) a b = g a b := by
  change (if h : a = b then f a ≫ eqToHom (congrArg Y h) else 0) +
    (if a = b then 0 else g a b) = g a b
  simp [h]

include hzero in
/-- Every shift-zero matrix entry is the evaluated coproduct crossing entry, including
labels whose incoming or outgoing edge is irrelevant. -/
theorem sZ_sigma_rZ' (δ : Φ.Blk l') (t t' : Fin (nLbl Φ i δ.1)) :
    sZ h₁ N δ t ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫ rZ' h₂ N δ t' =
      ((RouqCoproduct.rouqSig (blockZeroLoc Φ S D hnil i δ.1)
        (fun a b => selfCell S D (wtT_sub_add (Φ := Φ) δ.1 (lab Φ i δ.1 a))
          (Φ.wtT_add_single δ.1 (lab Φ i δ.1 b)))) t t').hom.app (N δ) := by
  by_cases hr₁ : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t)
  · by_cases hr₂ : Φ.rel δ.1 (lab Φ i δ.1 t')
    · by_cases ht : t = t'
      · subst ht
        have he : (RouqCoproduct.rouqSig (blockZeroLoc Φ S D hnil i δ.1)
            (fun a b => selfCell S D (wtT_sub_add (Φ := Φ) δ.1 (lab Φ i δ.1 a))
              (Φ.wtT_add_single δ.1 (lab Φ i δ.1 b)))) t t =
            (blockZeroLoc Φ S D hnil i δ.1 t).sig := by
          exact diag_off_self (fun a => (blockZeroLoc Φ S D hnil i δ.1 a).sig) _ t
        rw [he]
        exact sZ_sigma_rZ'_diag S D h₁ h₂ N δ t hr₁ hr₂
      · have he : (RouqCoproduct.rouqSig (blockZeroLoc Φ S D hnil i δ.1)
            (fun a b => selfCell S D (wtT_sub_add (Φ := Φ) δ.1 (lab Φ i δ.1 a))
              (Φ.wtT_add_single δ.1 (lab Φ i δ.1 b)))) t t' =
            RightwardCrossing.sigma
              (S.adj (lab Φ i δ.1 t') (Φ.wtT_add_single δ.1 _)).unit
              (selfCell S D (wtT_sub_add (Φ := Φ) δ.1 (lab Φ i δ.1 t))
                (Φ.wtT_add_single δ.1 (lab Φ i δ.1 t')))
              (S.adj (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _)).counit := by
          exact diag_off_ne (fun a => (blockZeroLoc Φ S D hnil i δ.1 a).sig) _ t t' ht
        rw [he]
        exact sZ_sigma_rZ'_offdiag S D h₁ h₂ N δ t t' ht hr₁ hr₂
    · exact (isZero_tgtZ N δ hzero t' hr₂).eq_of_tgt _ _
  · exact (isZero_srcZ N δ hzero t hr₁).eq_of_src _ _

private theorem desc_comp_lift_matrix {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] {A B : Type} [Fintype A] [Fintype B] {X : A → C} {Y : B → C}
    {U V : C}
    (s : ∀ a, X a ⟶ U) (r : ∀ b, V ⟶ Y b) (σ : U ⟶ V)
    (m : ∀ a b, X a ⟶ Y b) (hm : ∀ a b, s a ≫ σ ≫ r b = m a b) :
    biproduct.desc s ≫ σ ≫ biproduct.lift r = biproduct.matrix m := by
  apply biproduct.hom_ext'
  intro a
  apply biproduct.hom_ext
  intro b
  simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
    biproduct.matrix_π, biproduct.ι_desc]
  exact hm a b

include hzero in
/-- The shift-zero block is the evaluated spectral coproduct crossing matrix. -/
theorem sigma_zero_matrix (δ : Φ.Blk l') :
    biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
      biproduct.lift (rZ' h₂ N δ) =
      (matLift (LinearCat.evalAt (N δ))).map
        (RouqCoproduct.rouqSig (blockZeroLoc Φ S D hnil i δ.1)
          (fun a b => selfCell S D (wtT_sub_add (Φ := Φ) δ.1 (lab Φ i δ.1 a))
            (Φ.wtT_add_single δ.1 (lab Φ i δ.1 b)))) := by
  exact desc_comp_lift_matrix _ _ _ _
    (sZ_sigma_rZ' (S := S) (D := D) (h₁ := h₁) (h₂ := h₂) (N := N)
      (hnil := hnil) (hzero := hzero) δ)


private theorem counit_chain_id {C D : Type*} [Category C] [Category D]
    (K : C ⥤ D) {Y₀ Y₁ : C} {Z T : D} (i : Y₀ ⟶ Y₁) (g : K.obj Y₁ ⟶ Z)
    (θ : Z ⟶ Z) (eps : Z ⟶ T) (φ : K ⟶ K) (pr : Y₁ ⟶ Y₀) (c : K.obj Y₀ ⟶ T)
    (hg : g ≫ θ = φ.app Y₁ ≫ g) (hc : g ≫ eps = K.map pr ≫ c)
    (hi : i ≫ pr = 𝟙 _) : (K.map i ≫ g) ≫ (θ ≫ eps) = φ.app Y₀ ≫ c := by
  rw [Category.assoc, ← Category.assoc g, hg, Category.assoc, hc, ← Category.assoc,
    φ.naturality, Category.assoc, ← K.map_comp_assoc, hi, K.map_id, Category.id_comp]

private theorem powComp_hom {A B : LinearCat.{wk, v₁, u₂} k} {E : A ⟶ B}
    (θ : E ⟶ E) (n : ℕ) : (powComp θ n).hom = powComp θ.hom n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (powComp θ n).hom ≫ θ.hom = powComp θ.hom n ≫ θ.hom
    rw [ih]

/-- The dotted cap on the incoming self summand of an edge. -/
theorem self_pow_counit (p : Φ.Edge i l) (n : ℕ) :
    ((Ea Φ S h₁ p (p.tgt h₁) rfl).map (incF Φ S h₁ N p) ≫
      genE Φ S i h₁ ((F Φ S i h₁).obj.obj N) ⟨p, rfl⟩) ≫
      (F Φ S i h₁ ◁ powComp ((rouqData Φ S D).dot i h₁) n ≫
        (adj Φ S i h₁).counit).hom.app N (p.tgt h₁) =
      (S.F p.lbl (wt_tgt h₁ p rfl) ◁
        powComp (Polynomial.aeval (End.of (S.dot p.lbl (wt_tgt h₁ p rfl))) (D.pw p.lbl)) n ≫
        (S.adj p.lbl (wt_tgt h₁ p rfl)).counit).hom.app (N (p.tgt h₁)) := by
  rw [whisker_counit_app]
  have H := counit_chain_id (Ea Φ S h₁ p (p.tgt h₁) rfl) _ _ _ _ _ _ _
    (genE_powComp_dot D.pw i h₁ ((F Φ S i h₁).obj.obj N) ⟨p, rfl⟩ n)
    (genE_counit Φ S i h₁ N p) (incF_projF Φ S h₁ N p)
  refine H.trans ?_
  change (powComp (Polynomial.aeval (End.of (S.dot p.lbl (wt_tgt h₁ p rfl)))
    (D.pw p.lbl)).hom n).app _ ≫ _ = _
  rw [← powComp_hom]
  rfl

private theorem map_id_cap_chain {C D : Type*} [Category C] [Category D]
    (K : C ⥤ D) {A B : C} {Z T : D} (u : A ⟶ A) (v : A ⟶ B)
    (g : K.obj B ⟶ Z) (c : Z ⟶ T) (hu : u = 𝟙 A) :
    (K.map (u ≫ v) ≫ g) ≫ c = (K.map v ≫ g) ≫ c := by rw [hu, Category.id_comp]

/-- The dotted cap on a self summand specified by its target block. -/
theorem self_pow_counit_at (δ : Φ.Blk l') (p : {e : Φ.Edge i l // e.tgt h₁ = δ}) (n : ℕ) :
    ((Ea Φ S h₁ p.1 δ p.2).map ((trF S h₁ N p.1 p.2).hom ≫ incF Φ S h₁ N p.1) ≫
      genE Φ S i h₁ ((F Φ S i h₁).obj.obj N) p) ≫
      (F Φ S i h₁ ◁ powComp ((rouqData Φ S D).dot i h₁) n ≫
        (adj Φ S i h₁).counit).hom.app N δ =
      (S.F p.1.lbl (wt_tgt h₁ p.1 p.2) ◁
        powComp (Polynomial.aeval (End.of (S.dot p.1.lbl (wt_tgt h₁ p.1 p.2))) (D.pw p.1.lbl)) n ≫
        (S.adj p.1.lbl (wt_tgt h₁ p.1 p.2)).counit).hom.app (N δ) := by
  obtain ⟨p, hp⟩ := p
  subst hp
  exact (map_id_cap_chain _ (trF S h₁ N p rfl).hom _ _ _ rfl).trans
    (self_pow_counit S D h₁ N p n)


include hzero in
/-- Dotted caps on the canonical shift-zero summands. -/
theorem sZ_pow_counit (δ : Φ.Blk l') (t : Fin (nLbl Φ i δ.1)) (n : ℕ) :
    sZ h₁ N δ t ≫
      (F Φ S i h₁ ◁ powComp ((rouqData Φ S D).dot i h₁) n ≫
        (adj Φ S i h₁).counit).hom.app N δ =
      (S.F (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _) ◁
        powComp (Polynomial.aeval (End.of (S.dot (lab Φ i δ.1 t)
          (wtT_sub_add (Φ := Φ) δ.1 _))) (D.pw (lab Φ i δ.1 t))) n ≫
        (S.adj (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _)).counit).hom.app (N δ) := by
  by_cases hr : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t)
  · simp only [sZ, hr, dite_true]
    exact self_pow_counit_at S D h₁ N δ (pIn h₁ δ t hr) n
  · exact (isZero_srcZ N δ hzero t hr).eq_of_src _ _

private theorem unit_chain_id {C D : Type*} [Category C] [Category D]
    (K : C ⥤ D) {A B : D} {V W : C} (u : A ⟶ B) (t : B ⟶ B) (pr : B ⟶ K.obj W)
    (u' : A ⟶ K.obj V) (g : V ⟶ W) (θ : W ⟶ W) (φ : V ⟶ V) (m : W ⟶ V)
    (hn : t ≫ pr = pr ≫ K.map θ) (hu : u ≫ pr = u' ≫ K.map g)
    (hg : g ≫ θ = φ ≫ g) (hm : g ≫ m = 𝟙 _) :
    (u ≫ t) ≫ (pr ≫ K.map m) = u' ≫ K.map φ := by
  rw [Category.assoc, ← Category.assoc t, hn, Category.assoc, ← Category.assoc u, hu,
    Category.assoc, ← K.map_comp, ← K.map_comp, ← Category.assoc, hg,
    Category.assoc, hm, Category.comp_id]

/-- The dotted cup projected to the outgoing self summand of an edge. -/
theorem unit_pow_self (r : Φ.Edge i l') (n : ℕ) :
    ((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) n ▷ F Φ S i h₂).hom.app N r.src ≫
      (projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) r ≫
        (Fa Φ S h₂ r _ rfl).map (projEb S h₂ N ⟨r, rfl⟩)) =
      ((S.adj r.lbl (wt_tgt h₂ r rfl)).unit ≫
        powComp (Polynomial.aeval (End.of (S.dot r.lbl (wt_tgt h₂ r rfl))) (D.pw r.lbl)) n ▷
        S.F r.lbl (wt_tgt h₂ r rfl)).hom.app (N r.src) := by
  rw [unit_whisker_app]
  have H := unit_chain_id (Fa Φ S h₂ r _ rfl) _ _ _ _ _ _ _ _
    (projF_natural Φ S h₂ ((powComp ((rouqData Φ S D).dot i h₂) n).hom.app N) r)
    (unit_projF Φ S i h₂ N r)
    (genE_powComp_dot D.pw i h₂ N ⟨r, rfl⟩ n)
    (genE_projEb S h₂ N ⟨r, rfl⟩)
  refine H.trans ?_
  change _ ≫ (Fa Φ S h₂ r _ rfl).map ((powComp
    (Polynomial.aeval (End.of (S.dot r.lbl (wt_tgt h₂ r rfl))) (D.pw r.lbl)).hom n).app _) = _
  rw [← powComp_hom]
  rfl

include hzero in
/-- Dotted cups on the canonical shift-zero summands. -/
theorem unit_pow_rZ' (δ : Φ.Blk l') (t : Fin (nLbl Φ i δ.1)) (n : ℕ) :
    ((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) n ▷ F Φ S i h₂).hom.app N δ ≫
      rZ' h₂ N δ t =
      ((S.adj (lab Φ i δ.1 t) (Φ.wtT_add_single δ.1 _)).unit ≫
        powComp (Polynomial.aeval (End.of (S.dot (lab Φ i δ.1 t)
          (Φ.wtT_add_single δ.1 _))) (D.pw (lab Φ i δ.1 t))) n ▷
        S.F (lab Φ i δ.1 t) (Φ.wtT_add_single δ.1 _)).hom.app (N δ) := by
  by_cases hr : Φ.rel δ.1 (lab Φ i δ.1 t)
  · simp only [rZ', hr, dite_true]
    exact unit_pow_self S D h₂ N (rOut δ t hr).1 n
  · exact (isZero_tgtZ N δ hzero t hr).eq_of_tgt _ _


private theorem desc_comp_of_entries {C : Type*} [Category C] [Preadditive C]
    {A : Type} [Fintype A] [HasFiniteBiproducts C] {X : A → C} {U V : C}
    (s : ∀ a, X a ⟶ U) (c : U ⟶ V) (f : ∀ a, X a ⟶ V)
    (h : ∀ a, s a ≫ c = f a) : biproduct.desc s ≫ c = biproduct.desc f := by
  apply biproduct.hom_ext'
  intro a
  simpa using h a

private theorem comp_lift_of_entries {C : Type*} [Category C] [Preadditive C]
    {A : Type} [Fintype A] [HasFiniteBiproducts C] {X : A → C} {U V : C}
    (c : U ⟶ V) (r : ∀ a, V ⟶ X a) (f : ∀ a, U ⟶ X a)
    (h : ∀ a, c ≫ r a = f a) : c ≫ biproduct.lift r = biproduct.lift f := by
  apply biproduct.hom_ext
  intro a
  simpa using h a

include hzero in
/-- The projected dotted cap is a column of the evaluated spectral cap matrix. -/
theorem caps_zero_matrix (δ : Φ.Blk l') {M : ℕ} (m : Fin M) :
    biproduct.desc (sZ h₁ N δ) ≫
      (F Φ S i h₁ ◁ powComp ((rouqData Φ S D).dot i h₁) m ≫
        (adj Φ S i h₁).counit).hom.app N δ =
      (matLift (LinearCat.evalAt (N δ))).map
        (RouqCoproduct.rouqCaps (blockZeroLoc Φ S D hnil i δ.1)
          (fun t => (D.pw (lab Φ i δ.1 t)).coeff 0) M) ≫
      biproduct.π (fun _ : Fin M => N δ) m := by
  refine (desc_comp_of_entries _ _ _ (fun t => ?_)).trans
    (matLift_map_π (LinearCat.evalAt (N δ))
      (RouqCoproduct.rouqCaps (blockZeroLoc Φ S D hnil i δ.1)
        (fun t => (D.pw (lab Φ i δ.1 t)).coeff 0) M) m).symm
  refine (sZ_pow_counit S D h₁ N hzero δ t m).trans ?_
  exact congrArg (fun x : End (S.E (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _)) =>
    (S.F (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _) ◁ powComp x m ≫
      (S.adj (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _)).counit).hom.app (N δ))
    (aeval_pw_eq D _ _)

include hzero in
/-- The projected dotted cup is a row of the evaluated spectral cup matrix. -/
theorem cups_zero_matrix (δ : Φ.Blk l') {M : ℕ} (m : Fin M) :
    ((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) m ▷ F Φ S i h₂).hom.app N δ ≫
      biproduct.lift (rZ' h₂ N δ) =
      biproduct.ι (fun _ : Fin M => N δ) m ≫
      (matLift (LinearCat.evalAt (N δ))).map
        (RouqCoproduct.rouqCups (blockZeroLoc Φ S D hnil i δ.1)
          (fun t => (D.pw (lab Φ i δ.1 t)).coeff 0) M) := by
  refine (comp_lift_of_entries _ _ _ (fun t => ?_)).trans
    (ι_matLift_map (LinearCat.evalAt (N δ))
      (RouqCoproduct.rouqCups (blockZeroLoc Φ S D hnil i δ.1)
        (fun t => (D.pw (lab Φ i δ.1 t)).coeff 0) M) m).symm
  refine (unit_pow_rZ' S D h₂ N hzero δ t m).trans ?_
  exact congrArg (fun x : End (S.E (lab Φ i δ.1 t) (Φ.wtT_add_single δ.1 _)) =>
    ((S.adj (lab Φ i δ.1 t) (Φ.wtT_add_single δ.1 _)).unit ≫ powComp x m ▷
      S.F (lab Φ i δ.1 t) (Φ.wtT_add_single δ.1 _)).hom.app (N δ))
    (aeval_pw_eq D _ _)

private def sumInvToCongrOn {C : Type*} [Category C] [Preadditive C] {X Y Z : C}
    {f f₂ : X ⟶ Y} {g g₂ : ℕ → (X ⟶ Z)} {n : ℕ} (T : SumInvTo f g n)
    (hf : f = f₂) (hg : ∀ m, m < n → g m = g₂ m) : SumInvTo f₂ g₂ n := by
  subst hf
  exact {
    f' := T.f'
    g' := T.g'
    total := by
      rw [← T.total]
      congr 1
      exact Finset.sum_congr rfl fun m hm => by rw [hg m (Finset.mem_range.mp hm)]
    ff := T.ff
    fg := fun m hm => by rw [← hg m hm]; exact T.fg m hm
    gf := T.gf
    gg := fun m m' hm hm' => by rw [← hg m' hm']; exact T.gg m m' hm hm' }

private def sumInvFromCongrOn {C : Type*} [Category C] [Preadditive C] {X Y Z : C}
    {f f₂ : Y ⟶ X} {g g₂ : ℕ → (Z ⟶ X)} {n : ℕ} (T : SumInvFrom f g n)
    (hf : f = f₂) (hg : ∀ m, m < n → g m = g₂ m) : SumInvFrom f₂ g₂ n := by
  subst hf
  exact {
    f' := T.f'
    g' := T.g'
    total := by
      rw [← T.total]
      congr 1
      exact Finset.sum_congr rfl fun m hm => by rw [hg m (Finset.mem_range.mp hm)]
    ff := T.ff
    fg := T.fg
    gf := fun m hm => by rw [← hg m hm]; exact T.gf m hm
    gg := fun m m' hm hm' => by rw [← hg m hm]; exact T.gg m m' hm hm' }

/-- The positive shift-zero sum inverse, constructed from the spectral coproduct theorem.
The pairing identity is explicit because an arbitrary `Furling` does not include it. -/
def zeroPos (hπ : Φ.π = D.π) (δ : Φ.Blk l')
    (hpair : RD.pair (RD.iY i) l' =
      ∑ t : Fin (nLbl Φ i δ.1), RDc.pair (RDc.iY (lab Φ i δ.1 t)) (Φ.wtT δ.1))
    (hpos : 0 ≤ RD.pair (RD.iY i) l') :
    SumInvTo (biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
      biproduct.lift (rZ' h₂ N δ))
      (fun m => biproduct.desc (sZ h₁ N δ) ≫ (F Φ S i h₁ ◁
        powComp ((rouqData Φ S D).dot i h₁) m ≫ (adj Φ S i h₁).counit).hom.app N δ)
      (RD.pair (RD.iY i) l').toNat := by
  let T := SumInvTo.ofMat (LinearCat.evalAt (N δ)) _ _
    (isIso_blockZero_pos Φ S D hnil i δ.1 hπ (hpair ▸ hpos))
  refine (sumInvToCongrOn T
    (sigma_zero_matrix (S := S) (D := D) (hnil := hnil) (h₁ := h₁) (h₂ := h₂)
      (N := N) (hzero := hzero) δ).symm ?_).congr rfl rfl (congrArg Int.toNat hpair.symm)
  intro m hm
  simp only [finExt, hm, dite_true]
  exact (caps_zero_matrix (S := S) (D := D) (h₁ := h₁) (N := N) (hzero := hzero) (hnil := hnil) δ ⟨m, hm⟩).symm

/-- The negative shift-zero sum inverse, constructed from the spectral coproduct theorem.
The pairing identity is explicit because an arbitrary `Furling` does not include it. -/
def zeroNeg (hπ : Φ.π = D.π) (δ : Φ.Blk l')
    (hpair : RD.pair (RD.iY i) l' =
      ∑ t : Fin (nLbl Φ i δ.1), RDc.pair (RDc.iY (lab Φ i δ.1 t)) (Φ.wtT δ.1))
    (hneg : RD.pair (RD.iY i) l' ≤ 0) :
    SumInvFrom (biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
      biproduct.lift (rZ' h₂ N δ))
      (fun m => ((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) m ▷
        F Φ S i h₂).hom.app N δ ≫ biproduct.lift (rZ' h₂ N δ))
      (-RD.pair (RD.iY i) l').toNat := by
  let T := SumInvFrom.ofMat (LinearCat.evalAt (N δ)) _ _
    (isIso_blockZero_neg Φ S D hnil i δ.1 hπ (hpair ▸ hneg))
  refine (sumInvFromCongrOn T
    (sigma_zero_matrix (S := S) (D := D) (hnil := hnil) (h₁ := h₁) (h₂ := h₂)
      (N := N) (hzero := hzero) δ).symm ?_).congr rfl rfl
        (congrArg (fun z : ℤ => (-z).toNat) hpair.symm)
  intro m hm
  simp only [finExt, hm, dite_true]
  exact (cups_zero_matrix (S := S) (D := D) (h₂ := h₂) (N := N) (hzero := hzero) (hnil := hnil) δ ⟨m, hm⟩).symm


private theorem isZero_biprod_family {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] {A : Type} [Fintype A] {X : A → C} (hX : ∀ a, IsZero (X a)) :
    IsZero (⨁ X) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext'
  intro a
  exact (hX a).eq_of_src _ _

omit [DecidableEq I] [DecidableEq J] in
theorem isZero_srcSum (δ : Φ.Blk l') (hz : IsZero (N δ)) :
    IsZero (⨁ (srcZ (i := i) N δ)) :=
  isZero_biprod_family fun t => Functor.map_isZero
    (S.E (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _)).obj
    (Functor.map_isZero (S.F (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _)).obj hz)

omit [DecidableEq I] [DecidableEq J] in
theorem isZero_tgtSum (δ : Φ.Blk l') (hz : IsZero (N δ)) :
    IsZero (⨁ (tgtZ (i := i) N δ)) :=
  isZero_biprod_family fun t => Functor.map_isZero
    (S.F (lab Φ i δ.1 t) (Φ.wtT_add_single δ.1 _)).obj
    (Functor.map_isZero (S.E (lab Φ i δ.1 t) (Φ.wtT_add_single δ.1 _)).obj hz)

/-- The positive shift-zero sum inverse at a zero object, with any correction count. -/
def zeroPosOfIsZero (δ : Φ.Blk l') (hz : IsZero (N δ)) (n : ℕ) :
    SumInvTo (biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
      biproduct.lift (rZ' h₂ N δ))
      (fun m => biproduct.desc (sZ h₁ N δ) ≫ (F Φ S i h₁ ◁
        powComp ((rouqData Φ S D).dot i h₁) m ≫ (adj Φ S i h₁).counit).hom.app N δ) n where
  f' := 0
  g' _ := 0
  total := (isZero_srcSum (i := i) S N δ hz).eq_of_src _ _
  ff := (isZero_tgtSum (i := i) S N δ hz).eq_of_src _ _
  fg _ _ := (isZero_tgtSum (i := i) S N δ hz).eq_of_src _ _
  gf _ _ := hz.eq_of_src _ _
  gg _ _ _ _ := hz.eq_of_src _ _

/-- The negative shift-zero sum inverse at a zero object, with any correction count. -/
def zeroNegOfIsZero (δ : Φ.Blk l') (hz : IsZero (N δ)) (n : ℕ) :
    SumInvFrom (biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
      biproduct.lift (rZ' h₂ N δ))
      (fun m => ((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) m ▷
        F Φ S i h₂).hom.app N δ ≫ biproduct.lift (rZ' h₂ N δ)) n where
  f' := 0
  g' _ := 0
  total := (isZero_tgtSum (i := i) S N δ hz).eq_of_src _ _
  ff := (isZero_srcSum (i := i) S N δ hz).eq_of_src _ _
  fg _ _ := (isZero_srcSum (i := i) S N δ hz).eq_of_src _ _
  gf _ _ := hz.eq_of_src _ _
  gg _ _ _ _ := hz.eq_of_src _ _


end Entries

end Furling
end Categorification.TwoRep
