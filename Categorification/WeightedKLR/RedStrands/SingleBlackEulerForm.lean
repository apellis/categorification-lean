/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleBlackShapovalov

/-!
# The Euler pairing on all projective classes of the one-factor first weight

Webster, arXiv:1309.3796v2, §3.4, Corollary 3.22 and §4.7, Lemma 4.36.
With positive red multiplicity the shifted regular classes generate the whole
first lowering block, so the comparison on homogeneous Homs determines the
biadditive pairing on its Grothendieck group.
-/

noncomputable section

namespace Categorification.Stendhal.SingleBlack

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF Categorification.Graded
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
    {R : D.RootDatum Y} {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    {Λ : Fin 1 → I →₀ ℕ} (i : I) (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "𝒜" => tensorProductGrade G (Singleton.singleton i : Multiset I)
local notation "𝒯" => TensorProductAlgebra k Q Λ (Singleton.singleton i : Multiset I)
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ
local notation "reg" => GProj.regular 𝒜

private local instance : HasGdim 𝒜 := hasGdim_oneBlack i G

private theorem mem_of_regular_shifts (hi : 0 < Λ 0 i) (S : AddSubgroup (K0 𝒜))
    (hs : ∀ a : ℤ, K0.of ((reg).shift a) ∈ S) (x : K0 𝒜) : x ∈ S := by
  let c := oneBlackK0Equiv i G hi x
  have hc : c • K0.of (reg) = x := (oneBlackK0Equiv i G hi).injective (by
    rw [map_smul, oneBlackK0Equiv_regular, smul_eq_mul, mul_one])
  rw [← hc]
  induction c using AddMonoidAlgebra.induction_linear with
  | zero => rw [zero_smul]; exact S.zero_mem
  | add p q hp hq => rw [add_smul]; exact S.add_mem hp hq
  | single a m =>
    have hT : (AddMonoidAlgebra.single a m : LP) = m • (LaurentPolynomial.T a : LP) := by
      rw [LaurentPolynomial.T, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hT, smul_assoc, K0.T_smul_of]
    exact S.zsmul_mem (hs a) m

private def compatibleValues {M : Type*} [AddCommGroup M] (f : M →+ LaurentSeries ℤ) (g : M →+ 𝕂) :
    AddSubgroup M where
  carrier := {x | ∃ p : LP, toLaurentSeries p = f x ∧ integralLaurentEval p = g x}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨p, hp, hp'⟩ ⟨q, hq, hq'⟩
    exact ⟨p+q, by rw [map_add, map_add, hp, hq], by rw [map_add, map_add, hp', hq']⟩
  neg_mem' := by
    rintro x ⟨p, hp, hp'⟩
    exact ⟨-p, by rw [map_neg, map_neg, hp], by rw [map_neg, map_neg, hp']⟩

variable [Finite I] (highest : Dom R) (hR : R.IsXRegular)
    (hwt : highest.1 (R.coroot i) = (Λ 0 i : ℤ)) (hdeg : G.degX (.inl i) = 2 * (D.d i : ℤ))
    (hi : 0 < Λ 0 i)
local notation "η" => oneBlackLatticeEquiv highest i G hR hwt hi

local notation "V" => IrreducibleModule R (RatFunc.X : 𝕂) (Subtype.val highest)

private def websterAddForm : V →+ V →+ 𝕂 :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => websterForm highest hR x y)
    (fun y z => by simp [websterForm])) fun x y => by
      apply AddMonoidHom.ext
      intro z
      change websterForm highest hR (x+y) z = websterForm highest hR x z + websterForm highest hR y z
      simp [websterForm]

private abbrev inversion := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair inversion.toRingHom inversion.toRingHom := RingHomInvPair.of_ringEquiv inversion

private def latticePairing : K0 𝒜 →+ K0 𝒜 →+ 𝕂 :=
  let u := (firstLoweringLattice highest i).subtype.toAddMonoidHom.comp (η).toAddEquiv.toAddMonoidHom
  ((websterAddForm highest hR).comp u).compl₂ u

include hdeg in
/-- For every pair of classes in the one-red first lowering block, one Laurent
polynomial represents both the categorical Euler form and the normalized
Shapovalov form under the semilinear lattice isomorphism. Exchanging the
left-module Hom arguments implements the right-projective convention.
Webster, arXiv:1309.3796v2, Corollary 3.22, at positive red multiplicity. -/
theorem homForm_eq_shapovalov (x y : K0 𝒜) :
    ∃ p : LP, toLaurentSeries p = K0.homForm 𝒜 y x ∧
      integralLaurentEval p = websterForm highest hR (η x) (η y) := by
  let f := (K0.homForm 𝒜).flip
  let g := latticePairing i G highest hR hwt hi
  change x ∈ compatibleValues (f.flip y) (g.flip y)
  apply mem_of_regular_shifts i G hi
  intro a
  let xa := K0.of ((reg).shift a)
  change y ∈ compatibleValues (f xa) (g xa)
  apply mem_of_regular_shifts i G hi
  intro b
  refine ⟨gdimPoly (homGrade 𝒯 (shift 𝒜 b) (shift 𝒜 a)), ?_,
    regular_shift_homGdimPoly_eq_shapovalov highest hR i G hwt hdeg hi a b⟩
  change _ = K0.homForm 𝒜 (K0.of ((reg).shift b)) (K0.of ((reg).shift a))
  rw [K0.homForm_of, GProj.homGdim_shift_left, GProj.homGdim_shift_right,
    regular_shift_homGdimPoly, toLaurentSeries_T_mul, regular_homGdimPoly, map_sum, regular_homGdim]
  simp only [K0.toLaurentSeries_T, ← mul_assoc, HahnSeries.single_mul_single, one_mul]
  rw [show a-b = -b + a by abel]

end Categorification.Stendhal.SingleBlack
