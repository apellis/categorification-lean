/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.RestrictionTensor
import Categorification.WeightedKLR.GradedK0.TensorCoherence
import Categorification.WeightedKLR.GradedK0.Units

/-!
# Coassociativity of the graded restriction coproduct

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Proposition 2.18 and Theorem 2.19. The restriction isomorphism is degree-preserving
because it identifies both fixed submodules inside the same graded projective.
After the tensor comparison it gives coassociativity on the triple tensor of
Laurent-linear Grothendieck groups.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded Categorification.InductionAlong GalleryAlgebra Juxtapose
open scoped TensorProduct

universe u v w

variable {I : Type u} [DecidableEq I] {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type w}

section Restriction

variable [Field k] {Γ : WeightedGraph I 𝕜 k} (G : GradingDatum Γ)
  (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)

private abbrev juxtapose_mem (a b : I →₀ ℕ) :
    ∀ ⦃d : ℤ⦄ ⦃t : TensorW k Γ a b⦄,
      t ∈ tensorGrading (G.klrGrade a) (G.klrGrade b) d →
        inductionRingHom k Γ a b t ∈ G.klrGrade (a + b) d :=
  fun _ _ ht => G.inductionMap_mem_klrGrade ht

private theorem resK0_eq_resAlong (a b : I →₀ ℕ)
    [Module.Finite (TensorW k Γ a b) (Res (inductionRingHom k Γ a b)
      (WeightedKLRAlgebra k Γ (a + b)))]
    [Module.Projective (TensorW k Γ a b) (Res (inductionRingHom k Γ a b)
      (WeightedKLRAlgebra k Γ (a + b)))] (x : K0 (G.klrGrade (a + b))) :
    G.resK0 a b hD hZ hS x = K0.resAlong (inductionRingHom k Γ a b)
      (inductionRingHom_smul k Γ a b) (fun _ _ ht => G.juxtapose_mem a b ht) x := by
  induction x using K0.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | neg x hx => simp only [map_neg, hx]
  | of P =>
    rw [resK0_of, K0.resAlong_of]
    exact K0.of_eq_of_iso
      (GradedEquiv.ofPreserves (resIdemWEquivRes P.carrier) (fun _ _ hx => hx))

private def juxtaposeResProj (a b : I →₀ ℕ) (P : GProj (G.klrGrade (a + b))) :
    GProj (tensorGrading (G.klrGrade a) (G.klrGrade b)) :=
  haveI := res_finite Γ a b hD hZ hS (WeightedKLRAlgebra k Γ (a + b))
  haveI := res_projective Γ a b hD hZ hS (WeightedKLRAlgebra k Γ (a + b))
  P.resAlong (inductionRingHom k Γ a b) (inductionRingHom_smul k Γ a b)
    (fun _ _ ht => G.juxtapose_mem a b ht)

private theorem resK0_of_juxtaposeResProj (a b : I →₀ ℕ)
    (P : GProj (G.klrGrade (a + b))) :
    G.resK0 a b hD hZ hS (K0.of P) = K0.of (G.juxtaposeResProj hD hZ hS a b P) := by
  have := res_finite Γ a b hD hZ hS (WeightedKLRAlgebra k Γ (a + b))
  have := res_projective Γ a b hD hZ hS (WeightedKLRAlgebra k Γ (a + b))
  rw [G.resK0_eq_resAlong hD hZ hS a b, K0.resAlong_of]
  rfl

variable (a b c : I →₀ ℕ)

/-- Restrict on the left tensor factor along its juxtaposition map. -/
def resTensorLeftK0 :
    K0 (tensorGrading (G.klrGrade (a + b)) (G.klrGrade c)) →ₗ[LaurentPolynomial ℤ]
      K0 (k := k) (A := TensorW k Γ a b ⊗[k] WeightedKLRAlgebra k Γ c)
        (tensorGrading (tensorGrading (G.klrGrade a) (G.klrGrade b)) (G.klrGrade c)) :=
  haveI := res_finite Γ a b hD hZ hS (WeightedKLRAlgebra k Γ (a + b))
  haveI := res_projective Γ a b hD hZ hS (WeightedKLRAlgebra k Γ (a + b))
  K0.resTensorLeft (inductionRingHom k Γ a b) (inductionRingHom_smul k Γ a b)
    (fun _ _ ht => G.juxtapose_mem a b ht)

/-- Restrict on the right tensor factor along its juxtaposition map. -/
def resTensorRightK0 :
    K0 (tensorGrading (G.klrGrade a) (G.klrGrade (b + c))) →ₗ[LaurentPolynomial ℤ]
      K0 (k := k) (A := WeightedKLRAlgebra k Γ a ⊗[k] TensorW k Γ b c)
        (tensorGrading (G.klrGrade a) (tensorGrading (G.klrGrade b) (G.klrGrade c))) :=
  haveI := res_finite Γ b c hD hZ hS (WeightedKLRAlgebra k Γ (b + c))
  haveI := res_projective Γ b c hD hZ hS (WeightedKLRAlgebra k Γ (b + c))
  K0.resTensorRight (inductionRingHom k Γ b c) (inductionRingHom_smul k Γ b c)
    (fun _ _ ht => G.juxtapose_mem b c ht)

theorem resTensorLeftK0_extTensor (x : K0 (G.klrGrade (a + b))) (y : K0 (G.klrGrade c)) :
    G.resTensorLeftK0 hD hZ hS a b c (K0.extTensor (G.klrGrade (a + b)) (G.klrGrade c) x y) =
      K0.extTensor (tensorGrading (G.klrGrade a) (G.klrGrade b)) (G.klrGrade c)
        (G.resK0 a b hD hZ hS x) y := by
  have := res_finite Γ a b hD hZ hS (WeightedKLRAlgebra k Γ (a + b))
  have := res_projective Γ a b hD hZ hS (WeightedKLRAlgebra k Γ (a + b))
  rw [resTensorLeftK0, K0.resTensorLeft_extTensor, G.resK0_eq_resAlong hD hZ hS]

theorem resTensorRightK0_extTensor (x : K0 (G.klrGrade a)) (y : K0 (G.klrGrade (b + c))) :
    G.resTensorRightK0 hD hZ hS a b c (K0.extTensor (G.klrGrade a) (G.klrGrade (b + c)) x y) =
      K0.extTensor (G.klrGrade a) (tensorGrading (G.klrGrade b) (G.klrGrade c))
        x (G.resK0 b c hD hZ hS y) := by
  have := res_finite Γ b c hD hZ hS (WeightedKLRAlgebra k Γ (b + c))
  have := res_projective Γ b c hD hZ hS (WeightedKLRAlgebra k Γ (b + c))
  rw [resTensorRightK0, K0.resTensorRight_extTensor, G.resK0_eq_resAlong hD hZ hS]

private theorem resTensorK0_coassoc_of
    (P : GProj (G.klrGrade (a + b + c))) (Q : GProj (G.klrGrade (a + (b + c))))
    (e : P.carrier ≃+ Q.carrier)
    (he : ∀ (t : WeightedKLRAlgebra k Γ (a + b + c)) (m : P.carrier),
      e (t • m) = castW k Γ (add_assoc a b c) t • e m)
    (hg : ∀ ⦃d : ℤ⦄ ⦃m : P.carrier⦄, m ∈ P.grading d → e m ∈ Q.grading d)
    (hg' : ∀ ⦃d : ℤ⦄ ⦃m : Q.carrier⦄, m ∈ Q.grading d → e.symm m ∈ P.grading d) :
    K0.tensorAssoc (G.klrGrade a) (G.klrGrade b) (G.klrGrade c)
      (G.resTensorLeftK0 hD hZ hS a b c (K0.of (G.juxtaposeResProj hD hZ hS (a + b) c P))) =
      G.resTensorRightK0 hD hZ hS a b c (K0.of (G.juxtaposeResProj hD hZ hS a (b + c) Q)) := by
  rw [resTensorLeftK0, resTensorRightK0, K0.resTensorLeft_of, K0.resTensorRight_of]
  let E := resCoassocEquiv k Γ a b c P.carrier Q.carrier e he
  have hval (m : _) : (E m).val.val = e m.val.val := rfl
  refine K0.map_of_semilinear _ _ _ _ E
    (resCoassocEquiv_smul a b c P.carrier Q.carrier e he)
    (fun d m hx => ?_) (fun d y hy => ?_)
  · exact Eq.mpr (congrArg (· ∈ Q.grading d) (hval m)) (hg hx)
  · let y' : Res (resRightHom (k := k) (Γ := Γ) a b c) (res k Γ a (b + c) Q.carrier) := y
    have hE : (E (E.symm y')).val.val = y'.val.val :=
      congrArg (fun z => z.val.val) (E.apply_symm_apply y')
    have he' : (E.symm y').val.val = e.symm y'.val.val :=
      e.injective ((hval (E.symm y')).symm.trans (hE.trans (e.apply_symm_apply _).symm))
    exact Eq.mpr (congrArg (· ∈ P.grading d) he') (hg' hy)

private theorem resK0_coassoc_of (P : GProj (G.klrGrade (a + b + c))) :
    K0.tensorAssoc (G.klrGrade a) (G.klrGrade b) (G.klrGrade c)
      (G.resTensorLeftK0 hD hZ hS a b c (G.resK0 (a + b) c hD hZ hS (K0.of P))) =
      G.resTensorRightK0 hD hZ hS a b c
        (G.resK0 a (b + c) hD hZ hS (G.K0cast (add_assoc a b c) (K0.of P))) := by
  let h := add_assoc a b c
  let σ := castW k Γ h
  let Q := GProj.restrict σ (fun _ _ hx => G.castW_symm_mem_klrGrade h hx) P
  have hsemi (z : WeightedKLRAlgebra k Γ (a + b + c)) (m : P.carrier) :
      z • m = (σ z • (show Q.carrier from m) : Q.carrier) := by
    change z • m = σ.symm (σ z) • m
    rw [AlgEquiv.symm_apply_apply]
  have hQ : G.K0cast h (K0.of P) = K0.of Q :=
    G.K0cast_of_linearEquiv h P Q (LinearEquiv.refl k P.carrier) hsemi (fun _ _ hx => hx)
  rw [hQ, G.resK0_of_juxtaposeResProj hD hZ hS, G.resK0_of_juxtaposeResProj hD hZ hS]
  exact G.resTensorK0_coassoc_of hD hZ hS a b c P Q (AddEquiv.refl P.carrier) hsemi
    (fun _ _ hx => hx) (fun _ _ hx => hx)

/-- The iterated graded restrictions of Webster's Theorem 2.19 agree under the
three-factor associator, implementing §2.4, Proposition 2.18. -/
theorem resK0_coassoc (x : K0 (G.klrGrade (a + b + c))) :
    K0.tensorAssoc (G.klrGrade a) (G.klrGrade b) (G.klrGrade c)
      (G.resTensorLeftK0 hD hZ hS a b c (G.resK0 (a + b) c hD hZ hS x)) =
      G.resTensorRightK0 hD hZ hS a b c
        (G.resK0 a (b + c) hD hZ hS (G.K0cast (add_assoc a b c) x)) := by
  induction x using K0.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | neg x hx => simp only [map_neg, hx]
  | of P => exact G.resK0_coassoc_of hD hZ hS a b c P

end Restriction


section Coproduct

variable [Field k] {Γ : WeightedGraph I 𝕜 k} (G : GradingDatum Γ)
  (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
  (a b c : I →₀ ℕ) [∀ μ : I →₀ ℕ, HasGdim (G.klrGrade μ)]

local notation "L" => LaurentPolynomial ℤ

/-- Coassociativity of the graded coproduct components (Webster,
arXiv:1209.2463v4, §2.4, Proposition 2.18 and Theorem 2.19), under the
intermediate hypotheses for the two-factor tensor comparisons. -/
theorem coproductK0_coassoc_of_tensorK0Hyp
    (Hab : TensorK0Hyp (G.klrGrade a) (G.klrGrade b))
    (Hbc : TensorK0Hyp (G.klrGrade b) (G.klrGrade c))
    (Habc : TensorK0Hyp (G.klrGrade (a + b)) (G.klrGrade c))
    (Habc' : TensorK0Hyp (G.klrGrade a) (G.klrGrade (b + c)))
    (x : K0 (G.klrGrade (a + b + c))) :
    TensorProduct.assoc L _ _ _
      (TensorProduct.map (G.coproductK0 hD hZ hS a b Hab) LinearMap.id
        (G.coproductK0 hD hZ hS (a + b) c Habc x)) =
      TensorProduct.map LinearMap.id (G.coproductK0 hD hZ hS b c Hbc)
        (G.coproductK0 hD hZ hS a (b + c) Habc' (G.K0cast (add_assoc a b c) x)) := by
  have hL (t : K0 (G.klrGrade (a + b)) ⊗[L] K0 (G.klrGrade c)) :
      K0.extTensorLeft (G.klrGrade a) (G.klrGrade b) (G.klrGrade c)
        (TensorProduct.map (G.coproductK0 hD hZ hS a b Hab) LinearMap.id t) =
      G.resTensorLeftK0 hD hZ hS a b c (G.k0TensorEquiv (a + b) c Habc t) := by
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul y z =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, K0.extTensorLeft_tmul, k0TensorEquiv_tmul,
        G.resTensorLeftK0_extTensor, ← Hab.extTensorEquiv_toLinearMap]
      exact congrArg (fun u =>
        K0.extTensor (tensorGrading (G.klrGrade a) (G.klrGrade b)) (G.klrGrade c) u z)
        (G.k0TensorEquiv_coproductK0 hD hZ hS a b Hab y)
  have hR (t : K0 (G.klrGrade a) ⊗[L] K0 (G.klrGrade (b + c))) :
      K0.extTensorRight (G.klrGrade a) (G.klrGrade b) (G.klrGrade c)
        (TensorProduct.map LinearMap.id (G.coproductK0 hD hZ hS b c Hbc) t) =
      G.resTensorRightK0 hD hZ hS a b c (G.k0TensorEquiv a (b + c) Habc' t) := by
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul y z =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, K0.extTensorRight_tmul, k0TensorEquiv_tmul,
        G.resTensorRightK0_extTensor, ← Hbc.extTensorEquiv_toLinearMap]
      exact congrArg (K0.extTensor (G.klrGrade a)
        (tensorGrading (G.klrGrade b) (G.klrGrade c)) y)
        (G.k0TensorEquiv_coproductK0 hD hZ hS b c Hbc z)
  apply K0.extTensorRight_injective (G.klrGrade a) (G.klrGrade b) (G.klrGrade c) Hab Hbc
  rw [← K0.tensorAssoc_extTensorLeft, hL, hR, k0TensorEquiv_coproductK0, k0TensorEquiv_coproductK0]
  exact G.resK0_coassoc hD hZ hS a b c x

end Coproduct

end Categorification.WeightedKLR.GradingDatum
