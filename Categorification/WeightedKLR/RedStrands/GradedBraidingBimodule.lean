/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.CornerBimoduleGrading
import Categorification.WeightedKLR.RedStrands.BraidingFunctor
import Categorification.WeightedKLR.RedStrands.BraidedIdentityGrading
import Categorification.WeightedKLR.RedStrands.BraidedRelabelGrading
import Categorification.WeightedKLR.RedStrands.BraidingAuxiliaryDerived

/-!
# The braiding bimodule as a graded bimodule over tensor product algebras

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Definition 6.6. For a permutation `σ` of the red labels, the braiding bimodule
`B = e_{λ} B e_{σλ}` (`BraidedStendhalAlgebra.braidingBimodule`) of the quotient `V` of braided
Stendhal diagrams by violated idempotents is a bimodule over the corner at the order
`λ_1, …, λ_ℓ`, which is `T^λ` (`violCornerEquiv`), and the corner at the order
`λ_{σ 1}, …, λ_{σ ℓ}`, which is `T^{λ ∘ σ}` after relabelling the red strands
(`violCornerRedPermEquiv`). Here `B` is read as a graded `(T^λ, T^{λ ∘ σ})`-bimodule
(`braidBimod`), graded by the auxiliary grading of `V`, in which the red/red crossing has the
degree of the augmented KLR grading (`violAuxiliaryGrade`); Webster's grading of `B` differs
from it by a constant shift on each such bimodule.

## Main definitions

* `identityCornerMap` : `T^λ ≅ e_λ V e_λ ⊆ V`, a multiplicative `k`-linear map.
* `permCornerMap σ` : `T^{λ ∘ σ} ≅ e_{σλ} V e_{σλ} ⊆ V`.
* `braidBimod σ` : the bimodule `e_λ V e_{σλ}`, with these actions.
* `braidBimodGrading σ` : its auxiliary grading, a decomposition compatible with both actions.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv Categorification.Graded MulOpposite CornerEndomorphism

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "ord" => List.finRange ℓ

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q)

include hρ hQ in
/-- `violCornerEquiv` sends `c e_λ` to `c`. -/
theorem violCornerEquiv_symm_algebraMap_val (c : k) :
    ((violCornerEquiv hρ hQ).symm (algebraMap k (TensorProductAlgebra k Q Λ ν) c)).1 =
      algebraMap k (ViolQuotient k Q Λ ν) c * violMk k Q Λ ν (redProj k Q Λ ν ord) := by
  have hP := isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) ord
  let y : hP.Corner := ⟨algebraMap k _ c * redProj k Q Λ ν ord, algebraMap k _ c, by
    show redProj k Q Λ ν ord * algebraMap k _ c * redProj k Q Λ ν ord = _
    rw [← Algebra.commutes c (redProj k Q Λ ν ord), mul_assoc, hP.eq]⟩
  have hy : (violCornerHom k Q Λ ν y).1 =
      algebraMap k (ViolQuotient k Q Λ ν) c * violMk k Q Λ ν (redProj k Q Λ ν ord) := by
    rw [violCornerHom_val, map_mul, AlgHom.commutes]
  have hE : identityCornerHom k Q Λ ν y = @algebraMap k (StendhalAlgebra k Q Λ ν) _ _
      (IsIdempotentElem.instAlgebraCorner_categorification _) c := by
    apply Subtype.ext
    rw [identityCornerHom_val]
    change toAllOrders k Q Λ ν (algebraMap k _ c * redProj k Q Λ ν ord) =
      c • StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
    rw [map_mul, AlgHom.commutes, redProj, toAllOrders_redIdem, Algebra.smul_def]
  have key : violCornerEquiv hρ hQ (violCornerHom k Q Λ ν y) =
      algebraMap k (TensorProductAlgebra k Q Λ ν) c := by
    rw [violCornerEquiv_violCornerHom, hE]
    exact (TensorProductAlgebra.mk Q Λ ν).commutes c
  rw [← hy, ← key, RingEquiv.symm_apply_apply]

variable (Q Λ ν) in
include hρ hQ in
/-- `T^λ → V`, through the identification of `T^λ` with the corner at the order `λ_1, …, λ_ℓ`. -/
def identityCornerMap : TensorProductAlgebra k Q Λ ν →ₙₐ[k] ViolQuotient k Q Λ ν where
  toFun t := ((violCornerEquiv hρ hQ).symm t).1
  map_add' s t := by rw [map_add]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_mul' s t := by rw [map_mul]; rfl
  map_smul' c t := by
    change ((violCornerEquiv hρ hQ).symm (c • t)).1 = c • ((violCornerEquiv hρ hQ).symm t).1
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    change ((violCornerEquiv hρ hQ).symm (algebraMap k _ c)).1 *
      ((violCornerEquiv hρ hQ).symm t).1 = _
    rw [violCornerEquiv_symm_algebraMap_val hρ hQ, mul_assoc,
      corner_mul_left (isIdempotentElem_violRedProj k Q Λ ν)]

theorem identityCornerMap_apply (t : TensorProductAlgebra k Q Λ ν) :
    identityCornerMap Q Λ ν hρ hQ t = ((violCornerEquiv hρ hQ).symm t).1 := rfl

theorem identityCornerMap_one :
    identityCornerMap Q Λ ν hρ hQ 1 = violMk k Q Λ ν (redProj k Q Λ ν ord) := by
  rw [identityCornerMap_apply, map_one]
  rfl

variable (G : GradingDatum (stendhalQ Q Λ))

theorem identityCornerMap_mem_grade {d : ℤ} {t : TensorProductAlgebra k Q Λ ν}
    (ht : t ∈ tensorProductGrade G ν d) :
    identityCornerMap Q Λ ν hρ hQ t ∈ violAuxiliaryGrade (ν := ν) G d := by
  have := (violCornerEquiv_mem_tensorProductGrade_iff hρ hQ G (d := d)
    ((violCornerEquiv hρ hQ).symm t)).1
  rw [RingEquiv.apply_symm_apply] at this
  exact this ht

/-! ### The relabelled corner -/

variable (σ : Perm (Fin ℓ))

variable (Q Λ ν) in
include hρ hQ in
/-- `T^{λ ∘ σ} → V`, through the identification of `T^{λ ∘ σ}` with the corner of `V` at the
order `λ_{σ 1}, …, λ_{σ ℓ}` (relabelling the red strands, `violRedPermEquiv`). -/
def permCornerMap : TensorProductAlgebra k Q (Λ ∘ σ) ν →ₙₐ[k] ViolQuotient k Q Λ ν :=
  ((violRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ) (ν := ν) σ
    (fun _ => rfl)).toAlgHom.toNonUnitalAlgHom).comp (identityCornerMap Q (Λ ∘ σ) ν hρ hQ)

theorem permCornerMap_apply (u : TensorProductAlgebra k Q (Λ ∘ σ) ν) :
    permCornerMap Q Λ ν hρ hQ σ u = violRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ)
      (ν := ν) σ (fun _ => rfl) (identityCornerMap Q (Λ ∘ σ) ν hρ hQ u) := rfl

theorem permCornerMap_one :
    permCornerMap Q Λ ν hρ hQ σ 1 = violMk k Q Λ ν (redProj k Q Λ ν ((List.finRange ℓ).map σ)) := by
  rw [permCornerMap_apply, identityCornerMap_one, violRedPermEquiv_violMk,
    redPermAlgEquiv_redProj]

/-! ### Grading data -/

variable {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q)

variable (Q) in
/-- The grading datum of the tensor product algebras with red labels `Ω`, for a Rouquier `Q`. -/
abbrev rouquierGrading (Ω : Fin ℓ → I →₀ ℕ) : GradingDatum (stendhalQ Q Ω) :=
  stendhalGradingDatum Ω hR.gradingDatum (Categorification.QuantumGroup.UDot.di 𝔠)
    (fun i => (hR.gradingDatum_degX i).trans (Categorification.QuantumGroup.UDot.two_mul_di 𝔠 i).symm)

theorem permCornerMap_mem_grade {d : ℤ} {u : TensorProductAlgebra k Q (Λ ∘ σ) ν}
    (hu : u ∈ tensorProductGrade (rouquierGrading Q hR (Λ ∘ σ)) ν d) :
    permCornerMap Q Λ ν hρ hQ σ u ∈ violAuxiliaryGrade (ν := ν) (rouquierGrading Q hR Λ) d := by
  rw [permCornerMap_apply]
  exact (violRedPermEquiv_mem_grade_iff hR σ _).2 (identityCornerMap_mem_grade hρ hQ _ hu)

/-! ### The braiding bimodule -/

variable (Q Λ ν) in
/-- **The braiding bimodule** `B = e_λ V e_{σλ}` (Webster, arXiv:1309.3796v2, §6.1, Definition
6.6) as a bimodule over `T^λ` on the left and `T^{λ ∘ σ}` on the right
(`BraidedStendhalAlgebra.braidingBimodule` for the red orders `λ` and `σλ`). -/
abbrev braidBimod : Type :=
  RectBimod (identityCornerMap Q Λ ν hρ hQ) (permCornerMap Q Λ ν hρ hQ σ)

variable (Q Λ ν) in
/-- The auxiliary grading of the braiding bimodule. -/
abbrev braidBimodGrading : ℤ → Submodule k (braidBimod Q Λ ν hρ hQ σ) :=
  RectBimod.grading (violAuxiliaryGrade (ν := ν) (rouquierGrading Q hR Λ))
    (identityCornerMap Q Λ ν hρ hQ) (permCornerMap Q Λ ν hρ hQ σ)

/-- The auxiliary grading of `B` is a decomposition. -/
@[instance_reducible] def braidBimodDecomposition :
    DirectSum.Decomposition (braidBimodGrading Q Λ ν hρ hQ σ hR) :=
  RectBimod.decomposition _
    ((identityCornerMap_one hρ hQ).symm ▸ redProj_mem_violAuxiliaryGrade _ ord)
    ((permCornerMap_one hρ hQ σ).symm ▸ redProj_mem_violAuxiliaryGrade _ ((List.finRange ℓ).map σ))

/-- `T^λ` acts on `B` on the left by degree-preserving maps. -/
theorem braidBimod_gradedSMul_left :
    SetLike.GradedSMul (oppositeGrade (oppositeGrade
      (tensorProductGrade (rouquierGrading Q hR Λ) ν))) (braidBimodGrading Q Λ ν hρ hQ σ hR) :=
  RectBimod.gradedSMul_left _ fun _ _ ht => identityCornerMap_mem_grade hρ hQ _ ht

/-- `T^{λ ∘ σ}` acts on `B` on the right by degree-preserving maps. -/
theorem braidBimod_gradedSMul_right :
    SetLike.GradedSMul (oppositeGrade (tensorProductGrade (rouquierGrading Q hR (Λ ∘ σ)) ν))
      (braidBimodGrading Q Λ ν hρ hQ σ hR) :=
  RectBimod.gradedSMul_right _ fun _ _ hu => permCornerMap_mem_grade hρ hQ σ hR hu

/-! ### Finiteness -/

section Finite

local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "q" => fun a : R => violMk k Q Λ ν (ofKLR k Q Λ ν a)

/-- The corner of `V` at the order `σλ` is the image of `T^{λ ∘ σ}`. -/
theorem exists_permCornerMap_eq {y : ViolQuotient k Q Λ ν}
    (hy : violMk k Q Λ ν (redProj k Q Λ ν ((List.finRange ℓ).map σ)) * y = y ∧
      y * violMk k Q Λ ν (redProj k Q Λ ν ((List.finRange ℓ).map σ)) = y) :
    ∃ u, permCornerMap Q Λ ν hρ hQ σ u = y := by
  let y' : ((isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) ((List.finRange ℓ).map σ)).map
      (violMk k Q Λ ν)).Corner := ⟨y, y, by
        show violMk k Q Λ ν (redProj k Q Λ ν ((List.finRange ℓ).map σ)) * y *
          violMk k Q Λ ν (redProj k Q Λ ν ((List.finRange ℓ).map σ)) = y
        rw [hy.1, hy.2]⟩
  let z := (violCornerRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ) (ν := ν) σ
    (fun _ => rfl) (List.finRange ℓ)).symm y'
  refine ⟨violCornerEquiv hρ hQ z, ?_⟩
  rw [permCornerMap_apply, identityCornerMap_apply, RingEquiv.symm_apply_apply]
  exact congrArg Subtype.val ((violCornerRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ)
    (ν := ν) σ (fun _ => rfl) (List.finRange ℓ)).apply_symm_apply y')

/-- `permCornerMap` as a linear map. -/
def permCornerLinear : TensorProductAlgebra k Q (Λ ∘ σ) ν →ₗ[k] ViolQuotient k Q Λ ν :=
  ⟨⟨permCornerMap Q Λ ν hρ hQ σ, map_add _⟩, map_smul _⟩

/-- The span of the products `ψ_w e(i) t`, for `t` in the corner at `σλ`. -/
def braidGeneratorSpan : Submodule k (ViolQuotient k Q Λ ν) :=
  ⨆ wi : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) × Seq (stendhalWeight ℓ ν),
    (LinearMap.range (permCornerLinear hρ hQ σ)).map
      (LinearMap.mulLeft k (q (KLRAlgebra.ψw (ρ wi.1) * KLRAlgebra.e wi.2)))

theorem mul_redProj_mem_braidGeneratorSpan (x : ViolQuotient k Q Λ ν) :
    x * violMk k Q Λ ν (redProj k Q Λ ν ((List.finRange ℓ).map σ)) ∈ braidGeneratorSpan (Λ := Λ) hρ hQ σ := by
  let L : R →ₗ[k] ViolQuotient k Q Λ ν :=
    (LinearMap.mulRight k (violMk k Q Λ ν (redProj k Q Λ ν ((List.finRange ℓ).map σ)))).comp
      ((violMk k Q Λ ν).toLinearMap.comp (ofKLR k Q Λ ν).toLinearMap)
  obtain ⟨a, rfl⟩ := violMk_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) x
  obtain ⟨a, rfl⟩ := ofKLR_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) a
  have hspan : LinearMap.range L ≤ braidGeneratorSpan (Λ := Λ) hρ hQ σ := by
    rw [LinearMap.range_eq_map, ← KLRAlgebra.span_eq_top' (k := k) (Q := stendhalQ Q Λ)
      (ν := stendhalWeight ℓ ν) ρ hρ, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨w, u, i, rfl⟩, rfl⟩
    change violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.ψw (ρ w) *
      KLRAlgebra.pol (MvPolynomial.monomial u 1) * KLRAlgebra.e i)) *
      violMk k Q Λ ν (ofKLR k Q Λ ν (redIdem k Q Λ ((List.finRange ℓ).map σ))) ∈ _
    rw [← map_mul, ← map_mul]
    by_cases hi : redWord i = ((List.finRange ℓ).map σ)
    · have key : (KLRAlgebra.ψw (ρ w) * KLRAlgebra.pol (MvPolynomial.monomial u 1) *
          KLRAlgebra.e i * redIdem k Q Λ ((List.finRange ℓ).map σ) : R) =
          (KLRAlgebra.ψw (ρ w) * KLRAlgebra.e i) * (redIdem k Q Λ ((List.finRange ℓ).map σ) *
            (KLRAlgebra.pol (MvPolynomial.monomial u 1) * KLRAlgebra.e i) * redIdem k Q Λ ((List.finRange ℓ).map σ)) := by
        have h1 : (KLRAlgebra.e i * redIdem k Q Λ ((List.finRange ℓ).map σ) : R) =
            KLRAlgebra.e i := by simp [e_mul_redIdem, hi]
        have h2 : (redIdem k Q Λ ((List.finRange ℓ).map σ) * KLRAlgebra.e i : R) =
            KLRAlgebra.e i := by simp [redIdem_mul_e, hi]
        have hc : (KLRAlgebra.pol (MvPolynomial.monomial u 1) * KLRAlgebra.e i : R) =
            KLRAlgebra.e i * KLRAlgebra.pol (MvPolynomial.monomial u 1) :=
          ((KLRAlgebra.e_commute_pol i _).eq).symm
        have hmid : (redIdem k Q Λ ((List.finRange ℓ).map σ) *
            (KLRAlgebra.pol (MvPolynomial.monomial u 1) * KLRAlgebra.e i) *
            redIdem k Q Λ ((List.finRange ℓ).map σ) : R) =
            KLRAlgebra.pol (MvPolynomial.monomial u 1) * KLRAlgebra.e i := by
          rw [hc, ← mul_assoc, h2, ← hc, mul_assoc, h1]
        rw [hmid, mul_assoc (KLRAlgebra.ψw (ρ w) * _), h1, mul_assoc (KLRAlgebra.ψw (ρ w)), hc,
          mul_assoc (KLRAlgebra.ψw (ρ w)) (KLRAlgebra.e i), ← mul_assoc (KLRAlgebra.e i)
          (KLRAlgebra.e i), KLRAlgebra.e_mul_self]
      rw [key, map_mul, map_mul]
      obtain ⟨t, ht⟩ := exists_permCornerMap_eq hρ hQ σ
        (y := q (redIdem k Q Λ ((List.finRange ℓ).map σ) * (KLRAlgebra.pol (MvPolynomial.monomial u 1) *
          KLRAlgebra.e i) * redIdem k Q Λ ((List.finRange ℓ).map σ)))
        ⟨by simp only [redProj, ← map_mul, ← mul_assoc, redIdem_mul_redIdem],
         by simp only [redProj, ← map_mul, mul_assoc, redIdem_mul_redIdem]⟩
      exact Submodule.mem_iSup_of_mem (w, i)
        ⟨_, ⟨t, rfl⟩, by rw [LinearMap.mulLeft_apply]; exact congrArg _ ht⟩
    · have : (KLRAlgebra.ψw (ρ w) * KLRAlgebra.pol (MvPolynomial.monomial u 1) *
          KLRAlgebra.e i * redIdem k Q Λ ((List.finRange ℓ).map σ) : R) = 0 := by
        rw [mul_assoc, e_mul_redIdem]; simp [hi]
      rw [this, map_zero, map_zero]
      exact zero_mem _
  exact hspan ⟨a, rfl⟩

variable [Module.Finite k (TensorProductAlgebra k Q (Λ ∘ σ) ν)]

theorem finiteDimensional_braidGeneratorSpan :
    FiniteDimensional k (braidGeneratorSpan (Λ := Λ) hρ hQ σ) := by
  unfold braidGeneratorSpan
  infer_instance

/-- **The braiding bimodule is finite-dimensional.** -/
theorem finite_braidBimod : Module.Finite k (braidBimod Q Λ ν hρ hQ σ) := by
  have := finiteDimensional_braidGeneratorSpan (Λ := Λ) hρ hQ σ
  let M := (braidGeneratorSpan (Λ := Λ) hρ hQ σ).map
    (LinearMap.mulLeft k (identityCornerMap Q Λ ν hρ hQ 1))
  have hM : FiniteDimensional k M := inferInstance
  have hle : rectCorner (k := k) (identityCornerMap Q Λ ν hρ hQ 1)
      (permCornerMap Q Λ ν hρ hQ σ 1) ≤ M := by
    intro x hx
    refine ⟨x * permCornerMap Q Λ ν hρ hQ σ 1, ?_, ?_⟩
    · rw [permCornerMap_one]
      exact mul_redProj_mem_braidGeneratorSpan (Λ := Λ) hρ hQ σ x
    · change identityCornerMap Q Λ ν hρ hQ 1 * (x * _) = x
      rw [hx.2, hx.1]
  exact Submodule.finiteDimensional_of_le hle

end Finite

end Categorification.Stendhal.BraidedStendhalAlgebra
