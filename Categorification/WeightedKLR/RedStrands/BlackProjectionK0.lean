/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DividedProjectives
import Categorification.WeightedKLR.RedStrands.BlackAffineProjection
import Categorification.WeightedKLR.RedStrands.BlackPrincipal
import Categorification.KLR.CyclotomicSerreK0
/-!
# Projection of the affine lowering operator to Stendhal projectives

Webster, arXiv:1309.3796v2, §4.6 following Theorem 4.31 and Lemma 4.37.
Black induction corresponds to right multiplication by the affine singleton class
on the projective classes of each ordered violating quotient.
-/
noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup
open scoped TensorProduct DirectSum
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)
  (C : CartanDatum I) (hQ : IsRouquierQ C Q)
local notation "di" => fun i => C.dot i i / 2
local notation "H" => affineCoverGrading Λ hQ.gradingDatum di (dotDegree C hQ)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum di (dotDegree C hQ)
local notation "S" => affineCoverQ Q Λ
local notation "LP" => LaurentPolynomial ℤ
local notation "fam" => fun β : Multiset I => K0 (tensorProductGrade G β)

omit [DecidableEq I] in
private theorem stendhalWeight_inj : Function.Injective (stendhalWeight (I := I) ℓ) := by
  intro x y h
  exact Multiset.map_injective Sum.inl_injective (add_right_cancel h)

private def restrictWeights {R J K : Type*} [Semiring R] (M : J → Type*)
    [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)] (f : K → J) (hf : Function.Injective f) :
    DirectSum J M →ₗ[R] DirectSum K (fun k => M (f k)) where
  toFun := DFinsupp.comapDomain f hf
  map_add' := DFinsupp.comapDomain_add f hf
  map_smul' := DFinsupp.comapDomain_smul f hf

/-- Projection of all affine weight groups with one copy of every prescribed red colour
to their ordered violating quotients. -/
def totalProjectionK0 : (H).K0R →ₗ[LP] (⨁ ν : Multiset I, fam ν) :=
  (DirectSum.lmap (projectionK0 Λ C hQ)).comp
    (restrictWeights (R := LP) (H).K0fam (stendhalWeight ℓ) stendhalWeight_inj)

@[simp] theorem totalProjectionK0_lof (ν : Multiset I) (x : K0 ((H).grade (stendhalWeight ℓ ν))) :
    totalProjectionK0 Λ C hQ (DirectSum.lof LP _ (H).K0fam (stendhalWeight ℓ ν) x) =
      DirectSum.lof LP _ fam ν (projectionK0 Λ C hQ ν x) := by
  change DirectSum.lmap (projectionK0 Λ C hQ) (DFinsupp.comapDomain (stendhalWeight ℓ) stendhalWeight_inj (DFinsupp.single (β := (H).K0fam) (stendhalWeight ℓ ν) x)) = _
  rw [DFinsupp.comapDomain_single]
  exact DirectSum.lmap_lof ..

private theorem projection_lof_cast {δ : Multiset (I ⊕ Fin ℓ)} (ν : Multiset I) (h : δ = stendhalWeight ℓ ν)
    {e : KLRAlgebra k S δ} (he : IsIdempotentElem e) (he₀ : e ∈ (H).grade δ 0) :
    totalProjectionK0 Λ C hQ (DirectSum.lof LP _ (H).K0fam δ (K0.of (GProj.ofIdempotent e he he₀))) =
      DirectSum.lof LP _ fam ν (K0.of (GProj.ofIdempotent
        (affineTensorProjection (Q := Q) Λ ν (castKLR S h e)) ((he.map (castKLR S h)).map _)
        (projection_graded Λ C hQ ν ((H).castKLR_mem_grade h he₀)))) := by
  subst δ
  rw [totalProjectionK0_lof]
  exact projectionK0_ofIdempotent Λ C hQ ν he he₀ |> congrArg (DirectSum.lof LP _ fam ν)

variable (i : I) (ν : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "σ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin ℓ))
local notation "X" => GradingDatum.clsW (H) [Sum.inl i]
local notation "lift" => totalProjectionK0 Λ C hQ

private theorem cast_castKLR {J : Type*} [DecidableEq J] (P : J → J → MvPolynomial (Fin 2) k)
    {a b c : Multiset J} (h : a = b) (h' : b = c) (z : KLRAlgebra k P a) :
    castKLR P h' (castKLR P h z) = castKLR P (h.trans h') z := by subst c; subst b; rfl

private theorem blackLower_projection_principal {e : KLRAlgebra k S μ} (he : IsIdempotentElem e)
    (he₀ : e ∈ (H).grade μ 0) :
    blackLower G i (lift (DirectSum.lof LP _ (H).K0fam μ (K0.of (GProj.ofIdempotent e he he₀)))) =
      lift (DirectSum.of (H).K0fam μ (K0.of (GProj.ofIdempotent e he he₀)) * X) := by
  rw [totalProjectionK0_lof, blackLower_lof, projectionK0_ofIdempotent Λ C hQ ν he he₀,
    blackIndK0_ofIdempotent G i ν (he.map (affineTensorProjection Λ ν)) (projection_graded Λ C hQ ν he₀)]
  have hroot : X = DirectSum.of (H).K0fam σ (K0.of (GProj.ofIdempotent (𝒜 := (H).grade σ)
      1 IsIdempotentElem.one SetLike.GradedOne.one_mem)) := by
    rw [GradingDatum.clsW]
    apply congrArg (DirectSum.of (H).K0fam σ)
    exact K0.of_ofIdempotent_congr (𝒜 := (H).grade σ) (e_single (Q := S) (Sum.inl i) _) _ _ _ _
  rw [hroot, (H).K0R_of_mul_of, (H).indK0_ofIdempotent]
  let h := (add_comm μ σ).trans (stendhalWeight_black_cons (ℓ := ℓ) i ν)
  rw [show lift (DirectSum.of (H).K0fam (μ + σ) _) = _ from projection_lof_cast Λ C hQ νᵢ h
    (GradingDatum.concat_idem he IsIdempotentElem.one) ((H).concat_mem_grade_zero he₀ SetLike.GradedOne.one_mem)]
  apply congrArg (DirectSum.lof LP _ fam νᵢ)
  apply K0.of_ofIdempotent_congr
  rw [appendBlack_affineTensorProjection, cL_eq_cast, cast_castKLR]

/-- On each affine weight containing the prescribed red colours, the quotient
intertwines right multiplication by a black singleton with intrinsic lowering. -/
theorem blackLower_totalProjectionK0_lof (x : K0 ((H).grade μ)) :
    blackLower G i (lift (DirectSum.lof LP _ (H).K0fam μ x)) =
      lift (DirectSum.of (H).K0fam μ x * X) := by
  let W : Submodule LP (K0 ((H).grade μ)) :=
    { carrier := {z | blackLower G i (lift (DirectSum.lof LP _ (H).K0fam μ z)) =
        lift (DirectSum.of (H).K0fam μ z * X)}
      zero_mem' := by
        change blackLower G i (lift (DirectSum.lof LP _ (H).K0fam μ 0)) = _
        simp only [map_zero, zero_mul]
      add_mem' := fun {a b} ha hb => by
        change blackLower G i (lift (DirectSum.lof LP _ (H).K0fam μ (a + b))) = _
        simpa only [map_add, add_mul] using congrArg₂ (· + ·) ha hb
      smul_mem' := fun r a ha => by
        change blackLower G i (lift (DirectSum.lof LP _ (H).K0fam μ (r • a))) = _
        simpa only [map_smul, DirectSum.of_smul, smul_mul_assoc] using congrArg (r • ·) ha }
  have hs := affineCoverQ_symm Λ (fun a b hab => (hQ.symm a b hab).symm)
  have hX := affineCoverGrading_dot Λ hQ.gradingDatum di (dotDegree C hQ) C (fun _ => rfl)
  let := (H).hasGdim_grade' (ν := μ) hs (fun a => (hX a).symm ▸ (affineCoverCartan C ℓ).dot_self_pos a)
  have ht : ⊤ ≤ W := by
    rw [← K0.span_indec ((H).grade μ)]
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    obtain ⟨e, he, he₀, n, ⟨u⟩⟩ := b.isIndec_rep.exists_iso_ofIdempotent
    change K0.of b.rep ∈ W
    rw [K0.of_eq_of_iso u, ← K0.T_smul_of]
    exact W.smul_mem _ (blackLower_projection_principal Λ C hQ i ν he he₀)
  exact ht (Submodule.mem_top (x := x))

end Categorification.Stendhal
