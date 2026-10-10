/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicLowerSplitColumns
import Categorification.KLR.CyclotomicAB

/-!
# The actual cyclotomic matrix and connecting map

For `β = {i} + γ`, `eiP_split_matrix` expresses the actual map in the existing
split coordinates. Its polynomial entry is `(-1)^|β| • aMap`, not `aMap`:
`eiP` uses `τ = -ψ`, whereas the existing B and C coordinates are unchanged.
The off-diagonal entry uses the genuine polynomial section and lower decoder.

The connecting map lands in the concrete quotient by `range lowerP`.
`snakeDelta_decode_lift` and `snakeDelta_lift_independent` prove that any
actual lift gives the same class. `ker_snakeDelta` and `range_snakeDelta`
prove exactness at the polynomial kernel and the lower cokernel.
This is the k-linear connecting segment of Kang–Kashiwara,
arXiv:1102.4677v4, §5.2, not the source's graded bimodule inverse.
The existing domain/factorization hypotheses suffice for arbitrary cyclotomic
polynomials, including the constant-one family, and for `γ = 0`.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
variable (a : I → Polynomial k) [IsDomain k]
  {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ j l, j ≠ l → Q j l = P l j * MvPolynomial.rename ![1, 0] (P j l))
  (hP : ∀ j l, j ≠ l → P j l ≠ 0)
local notation "Rl" => CycKLR k Q a β

/-- The bottom polynomial arrow in the unchanged B/C coordinates. -/
def eiA : Polynomial Rl →ₗ[k] Polynomial Rl :=
  ((-1 : k) ^ Multiset.card β) •
    aMap i β a (by simp) (zero_lt_card_single_add i γ) hPQ hP

/-- The exact bottom square on the genuine cut tensors, including its sign. -/
theorem eiC_eiP (z : EIKOne Q i β a) :
    eiC Q i γ a hPQ hP (eiP Q i γ a z) =
      eiA Q i γ a hPQ hP (eiB Q i γ a hPQ hP z) := by
  change cMap i β hPQ hP a (zero_lt_card_single_add i γ)
    (lowerQuotientCast Q i γ a (((tensorToKZero Q i β a (by simp)
      (zero_lt_card_single_add i γ)).restrictScalars k) (((-1 : k) ^ Multiset.card β) •
        kZeroToTensor Q i β a (by simp) (zero_lt_card_single_add i γ)
          (lowerQuotientUncast Q i γ a
            (pMap a (zero_lt_card_single_add i β) (by simp) (Multiset.card β)
              (card_single_add i β).symm
              (tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ) z)))))) = _
  rw [map_smul, map_smul, map_smul]
  simp only [LinearMap.restrictScalars_apply]
  rw [tensorToKZero_kZeroToTensor,
    lowerQuotientCast_rightCut, lowerQuotientCast_uncast, cMap_act0]
  simp only [map_one, mul_one]
  exact congrArg (fun p : Polynomial Rl => ((-1 : k) ^ Multiset.card β) • p)
    (aMap_bMap i β a (zero_lt_card_single_add i γ) hPQ hP (by simp)
      (tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ) z)).symm

/-- Equality of the actual bottom composites. -/
theorem eiC_comp_eiP :
    (eiC Q i γ a hPQ hP).comp (eiP Q i γ a) =
      (eiA Q i γ a hPQ hP).comp (eiB Q i γ a hPQ hP) := by
  apply LinearMap.ext
  intro z
  exact eiC_eiP Q i γ a hPQ hP z

/-- The genuine off-diagonal entry, not a vanishing or unspecified correction. -/
def eiPOffDiagonal : Polynomial Rl →ₗ[k] KZeroPrime Q i γ a :=
  (eiCLowerProjection Q i γ a hPQ hP).comp
    ((eiP Q i γ a).comp (eiBSection Q i γ a))

/-- The lower correction is the actual middle image minus its polynomial component. -/
theorem lowerF_eiPOffDiagonal (p : Polynomial Rl) :
    lowerF Q i γ a (eiPOffDiagonal Q i γ a hPQ hP p) =
      eiP Q i γ a (eiBSection Q i γ a p) -
        eiCSection Q i γ a (eiA Q i γ a hPQ hP p) := by
  change lowerF Q i γ a (eiCLowerProjection Q i γ a hPQ hP
    (eiP Q i γ a (eiBSection Q i γ a p))) = _
  rw [lowerF_eiCLowerProjection, eiC_eiP, eiB_eiBSection]

/-- The matrix on an arbitrary lower tensor and polynomial coefficient. -/
theorem eiP_split_apply (t : KOnePrime Q i γ a) (p : Polynomial Rl) :
    (eiCSplitEquiv Q i γ a hPQ hP).symm
      (eiP Q i γ a (eiBSplitEquiv Q i γ a hPQ hP (t, p))) =
      (lowerP Q i γ a t + eiPOffDiagonal Q i γ a hPQ hP p,
        eiA Q i γ a hPQ hP p) := by
  rw [eiBSplitEquiv_apply, map_add, ← lowerP_tensor_square,
    eiCSplitEquiv_symm_apply]
  apply Prod.ext
  · simp only [map_add, eiCLowerProjection_lowerF]
    rfl
  · simp only [map_add, eiC_lowerF, zero_add, eiC_eiP, eiB_eiBSection]

/-- Conjugation by the actual split equivalences gives the triangular matrix. -/
theorem eiP_split_matrix :
    (eiCSplitEquiv Q i γ a hPQ hP).symm.toLinearMap.comp
      ((eiP Q i γ a).comp (eiBSplitEquiv Q i γ a hPQ hP).toLinearMap) =
    ((lowerP Q i γ a).comp (LinearMap.fst k _ _) +
      (eiPOffDiagonal Q i γ a hPQ hP).comp (LinearMap.snd k _ _)).prod
        ((eiA Q i γ a hPQ hP).comp (LinearMap.snd k _ _)) := by
  apply LinearMap.ext
  intro x
  exact eiP_split_apply Q i γ a hPQ hP x.1 x.2

/-- The actual cokernel of the lower horizontal map. -/
abbrev LowerPCoker := KZeroPrime Q i γ a ⧸ LinearMap.range (lowerP Q i γ a)

/-- The actual cokernel of the middle horizontal map. -/
abbrev EIPCoker := EIKZero Q i β a ⧸ LinearMap.range (eiP Q i γ a)

/-- Apply the actual middle map to the polynomial section of a kernel element. -/
def snakeSectionImage : LinearMap.ker (eiA Q i γ a hPQ hP) →ₗ[k]
    LinearMap.ker (eiC Q i γ a hPQ hP) :=
  ((eiP Q i γ a).comp ((eiBSection Q i γ a).comp
    (LinearMap.ker (eiA Q i γ a hPQ hP)).subtype)).codRestrict _ (by
      intro p
      change eiC Q i γ a hPQ hP (eiP Q i γ a (eiBSection Q i γ a p.val)) = 0
      rw [eiC_eiP, eiB_eiBSection]
      exact p.2)

/-- The canonical lower representative, using the existing explicit kernel decoder. -/
def snakeLift : LinearMap.ker (eiA Q i γ a hPQ hP) →ₗ[k] KZeroPrime Q i γ a :=
  (lowerFKernelInv Q i γ a hPQ hP).comp (snakeSectionImage Q i γ a hPQ hP)

theorem lowerF_snakeLift (p : LinearMap.ker (eiA Q i γ a hPQ hP)) :
    lowerF Q i γ a (snakeLift Q i γ a hPQ hP p) =
      eiP Q i γ a (eiBSection Q i γ a p.val) :=
  lowerF_kernelInv Q i γ a hPQ hP (snakeSectionImage Q i γ a hPQ hP p)

/-- On the polynomial kernel the off-diagonal entry is the actual lower lift. -/
theorem snakeLift_eq_offDiagonal (p : LinearMap.ker (eiA Q i γ a hPQ hP)) :
    snakeLift Q i γ a hPQ hP p = eiPOffDiagonal Q i γ a hPQ hP p.val := by
  rw [← eiCLowerProjection_lowerF Q i γ a hPQ hP (snakeLift Q i γ a hPQ hP p),
    lowerF_snakeLift]
  rfl

/-- The concrete connecting map, with sign fixed by `F u = P z`. -/
def snakeDelta : LinearMap.ker (eiA Q i γ a hPQ hP) →ₗ[k] LowerPCoker Q i γ a :=
  (LinearMap.range (lowerP Q i γ a)).mkQ.comp (snakeLift Q i γ a hPQ hP)

/-- Its quotient representative is the actual off-diagonal matrix entry. -/
theorem snakeDelta_offDiagonal (p : LinearMap.ker (eiA Q i γ a hPQ hP)) :
    snakeDelta Q i γ a hPQ hP p =
      Submodule.Quotient.mk (eiPOffDiagonal Q i γ a hPQ hP p.val) := by
  change Submodule.Quotient.mk (snakeLift Q i γ a hPQ hP p) = _
  rw [snakeLift_eq_offDiagonal]

/-- Any lift through B and any actual lower preimage compute the same class. -/
theorem snakeDelta_of_lift (p : LinearMap.ker (eiA Q i γ a hPQ hP))
    (z : EIKOne Q i β a) (hz : eiB Q i γ a hPQ hP z = p.val)
    (u : KZeroPrime Q i γ a) (hu : lowerF Q i γ a u = eiP Q i γ a z) :
    snakeDelta Q i γ a hPQ hP p = Submodule.Quotient.mk u := by
  change Submodule.Quotient.mk (snakeLift Q i γ a hPQ hP p) = Submodule.Quotient.mk u
  apply (Submodule.Quotient.eq _).2
  refine ⟨-eiBLowerProjection Q i γ a hPQ hP z, ?_⟩
  apply lowerF_injective Q i γ a hPQ hP
  rw [map_neg, map_neg, lowerP_tensor_square, lowerVertical_eiBLowerProjection,
    map_sub, hz, map_sub, lowerF_snakeLift, hu]
  abel

/-- Decode any lift through B; the result gives the same connecting class. -/
theorem snakeDelta_decode_lift (p : LinearMap.ker (eiA Q i γ a hPQ hP))
    (z : EIKOne Q i β a) (hz : eiB Q i γ a hPQ hP z = p.val) :
    snakeDelta Q i γ a hPQ hP p = Submodule.Quotient.mk
      (lowerFKernelInv Q i γ a hPQ hP
        ⟨eiP Q i γ a z, by rw [LinearMap.mem_ker, eiC_eiP, hz]; exact p.2⟩) :=
  snakeDelta_of_lift Q i γ a hPQ hP p z hz _
    (lowerF_kernelInv Q i γ a hPQ hP _)

/-- Adding a lower P-image to the canonical representative leaves its class unchanged. -/
theorem snakeDelta_representative (p : LinearMap.ker (eiA Q i γ a hPQ hP))
    (t : KOnePrime Q i γ a) :
    (Submodule.Quotient.mk (snakeLift Q i γ a hPQ hP p + lowerP Q i γ a t) :
      LowerPCoker Q i γ a) = snakeDelta Q i γ a hPQ hP p := by
  change Submodule.Quotient.mk (_ + _) = Submodule.Quotient.mk _
  rw [Submodule.Quotient.mk_add]
  have ht : (Submodule.Quotient.mk (lowerP Q i γ a t) : LowerPCoker Q i γ a) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 ⟨t, rfl⟩
  rw [ht, add_zero]

/-- In particular, changing both chosen lifts does not change the cokernel class. -/
theorem snakeDelta_lift_independent (p : LinearMap.ker (eiA Q i γ a hPQ hP))
    (z z' : EIKOne Q i β a)
    (hz : eiB Q i γ a hPQ hP z = p.val) (hz' : eiB Q i γ a hPQ hP z' = p.val)
    (u u' : KZeroPrime Q i γ a)
    (hu : lowerF Q i γ a u = eiP Q i γ a z)
    (hu' : lowerF Q i γ a u' = eiP Q i γ a z') :
    (Submodule.Quotient.mk u : LowerPCoker Q i γ a) = Submodule.Quotient.mk u' :=
  (snakeDelta_of_lift Q i γ a hPQ hP p z hz u hu).symm.trans
    (snakeDelta_of_lift Q i γ a hPQ hP p z' hz' u' hu')

/-- The actual B arrow restricted to the kernel of the middle P. -/
def eiBOnKernel : LinearMap.ker (eiP Q i γ a) →ₗ[k]
    LinearMap.ker (eiA Q i γ a hPQ hP) :=
  ((eiB Q i γ a hPQ hP).comp (LinearMap.ker (eiP Q i γ a)).subtype).codRestrict _ (by
    intro z
    change eiA Q i γ a hPQ hP (eiB Q i γ a hPQ hP z.val) = 0
    rw [← eiC_eiP, z.2, map_zero])

/-- Exactness at the polynomial kernel, without an assumed exactness hypothesis. -/
theorem ker_snakeDelta :
    LinearMap.ker (snakeDelta Q i γ a hPQ hP) =
      LinearMap.range (eiBOnKernel Q i γ a hPQ hP) := by
  ext p
  constructor
  · intro hp
    have hp' : snakeLift Q i γ a hPQ hP p ∈ LinearMap.range (lowerP Q i γ a) :=
      (Submodule.Quotient.mk_eq_zero _).1 hp
    obtain ⟨t, ht⟩ := hp'
    let z := eiBSection Q i γ a p.val - lowerVertical Q i γ a t
    have hz : eiP Q i γ a z = 0 := by
      change eiP Q i γ a (eiBSection Q i γ a p.val - lowerVertical Q i γ a t) = 0
      rw [map_sub, ← lowerP_tensor_square, ht, lowerF_snakeLift, sub_self]
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    change eiB Q i γ a hPQ hP z = p.val
    change eiB Q i γ a hPQ hP (eiBSection Q i γ a p.val - lowerVertical Q i γ a t) = p.val
    rw [map_sub, eiB_eiBSection, eiB_lowerVertical, sub_zero]
  · rintro ⟨z, rfl⟩
    change snakeDelta Q i γ a hPQ hP (eiBOnKernel Q i γ a hPQ hP z) = 0
    rw [snakeDelta_of_lift Q i γ a hPQ hP _ z.val rfl 0 (by rw [map_zero, z.2])]
    rfl

/-- The crossing induces a map between the actual cokernels. -/
def lowerFCoker : LowerPCoker Q i γ a →ₗ[k] EIPCoker Q i γ a :=
  (LinearMap.range (lowerP Q i γ a)).liftQ
    ((LinearMap.range (eiP Q i γ a)).mkQ.comp (lowerF Q i γ a)) (by
      rintro u ⟨t, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact ⟨lowerVertical Q i γ a t, (lowerP_tensor_square Q i γ a t).symm⟩)

omit [IsDomain k] in
@[simp] theorem lowerFCoker_mk (u : KZeroPrime Q i γ a) :
    lowerFCoker Q i γ a (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (lowerF Q i γ a u) := rfl

/-- The canonical connecting representative maps to zero in the middle cokernel. -/
theorem lowerFCoker_snakeDelta (p : LinearMap.ker (eiA Q i γ a hPQ hP)) :
    lowerFCoker Q i γ a (snakeDelta Q i γ a hPQ hP p) = 0 := by
  change Submodule.Quotient.mk (lowerF Q i γ a (snakeLift Q i γ a hPQ hP p)) = 0
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨eiBSection Q i γ a p.val, (lowerF_snakeLift Q i γ a hPQ hP p).symm⟩

/-- Exactness at the lower cokernel, using the genuine crossing-induced map. -/
theorem range_snakeDelta :
    LinearMap.range (snakeDelta Q i γ a hPQ hP) =
      LinearMap.ker (lowerFCoker Q i γ a) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact lowerFCoker_snakeDelta Q i γ a hPQ hP p
  · intro hq
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hu : lowerF Q i γ a u ∈ LinearMap.range (eiP Q i γ a) :=
      (Submodule.Quotient.mk_eq_zero _).1 hq
    obtain ⟨z, hz⟩ := hu
    have hp : eiA Q i γ a hPQ hP (eiB Q i γ a hPQ hP z) = 0 := by
      rw [← eiC_eiP, hz, eiC_lowerF]
    exact ⟨⟨eiB Q i γ a hPQ hP z, hp⟩,
      snakeDelta_of_lift Q i γ a hPQ hP _ z rfl u hz.symm⟩

end Categorification.KLR.KLRAlgebra
