/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.CoproductK0
import Categorification.WeightedKLR.GradedK0.Units
import Categorification.WeightedKLR.GradedK0.ZeroAlgebra

/-!
# The zero-weight components of the graded coproduct

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Proposition 2.18 and Theorem 2.19. Restriction to a splitting with an empty block
adjoins the regular zero-strand module on the corresponding side. On graded
Grothendieck groups these are the two endpoint terms of the coproduct.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded GalleryAlgebra Juxtapose
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  (G : GradingDatum Γ) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)

private def pullbackSum {a b ν : I →₀ ℕ} (h : a + b = ν) (P : GProj (G.klrGrade ν)) :
    GProj (G.klrGrade (a + b)) :=
  GProj.restrict (castW k Γ h).symm (fun _ _ hx => G.castW_mem_klrGrade h hx) P

private theorem K0cast_pullbackSum {a b ν : I →₀ ℕ} (h : a + b = ν)
    (P : GProj (G.klrGrade ν)) :
    G.K0cast h.symm (K0.of P) = K0.of (G.pullbackSum h P) := by
  refine G.K0cast_of_linearEquiv h.symm P (G.pullbackSum h P)
    (LinearEquiv.refl k P.carrier) ?_ ?_
  · intro t x
    change t • x = castW k Γ h (castW k Γ h.symm t) • x
    have hc : castW k Γ h.symm = (castW k Γ h).symm := by subst ν; rfl
    rw [hc, AlgEquiv.apply_symm_apply]
  · exact fun _ _ hx => hx

private def resUnitIso {a b ν : I →₀ ℕ} (h : a + b = ν)
    (h₁ : inductionMap k Γ a b 1 = 1) (P : GProj (G.klrGrade ν))
    (Q : GProj (tensorGrading (G.klrGrade a) (G.klrGrade b)))
    (e : Q.carrier ≃ₗ[k] P.carrier)
    (he : ∀ (t : TensorW k Γ a b) (p : P.carrier),
      e.symm (castW k Γ h (inductionMap k Γ a b t) • p) = t • e.symm p)
    (hg : ∀ ⦃d : ℤ⦄ ⦃p : P.carrier⦄, p ∈ P.grading d → e.symm p ∈ Q.grading d) :
    (G.resGProj a b hD hZ hS (G.pullbackSum h P)).Iso Q := by
  let L := G.pullbackSum h P
  let F : ResIdemW k Γ a b L.carrier ≃+ P.carrier :=
    { toFun := fun p => p.1
      invFun := fun p => ⟨p, by
        change inductionMap k Γ a b 1 • (show L.carrier from p) = (show L.carrier from p)
        rw [h₁, one_smul]⟩
      map_add' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E : (G.resGProj a b hD hZ hS L).carrier ≃ₗ[TensorW k Γ a b] Q.carrier :=
    { F.trans e.symm.toAddEquiv with
      map_smul' := fun t p => he t p.1 }
  exact GradedEquiv.ofPreserves E (fun _ _ hp => hg hp)

private theorem inductionMap_zero_left (ν : I →₀ ℕ) : inductionMap k Γ 0 ν 1 = 1 :=
  (castW k Γ (zero_add ν)).injective <|
    (inductionMap_one_tmul (1 : WeightedKLRAlgebra k Γ ν)).trans (map_one _).symm

private theorem inductionMap_zero_right (ν : I →₀ ℕ) : inductionMap k Γ ν 0 1 = 1 :=
  (castW k Γ (add_zero ν)).injective <|
    (inductionMap_tmul_one (1 : WeightedKLRAlgebra k Γ ν)).trans (map_one _).symm

private def resUnitLeftIso {ν : I →₀ ℕ} (P : GProj (G.klrGrade ν)) :
    (G.resGProj 0 ν hD hZ hS (G.pullbackSum (zero_add ν) P)).Iso
      ((GProj.regular (G.klrGrade 0)).extTensor P) := by
  let W₀ := WeightedKLRAlgebra k Γ 0
  let e₀ : W₀ ≃ₗ[k] k := (weightedKLRZeroEquiv (Γ := Γ)).symm.toLinearEquiv
  let e : ExtTensor k W₀ P.carrier ≃ₗ[k] P.carrier :=
    (TensorProduct.congr e₀ (LinearEquiv.refl k P.carrier)).trans (TensorProduct.lid k P.carrier)
  have hsymm (p : P.carrier) : e.symm p = ExtTensor.tmul (1 : W₀) p := by
    change (TensorProduct.congr e₀ (LinearEquiv.refl k P.carrier)).symm
      ((TensorProduct.lid k P.carrier).symm p) = _
    rw [TensorProduct.lid_symm_apply, TensorProduct.congr_symm_tmul]
    change weightedKLRZeroEquiv (Γ := Γ) 1 ⊗ₜ[k] p = _
    rw [map_one]
    rfl
  refine G.resUnitIso hD hZ hS (zero_add ν) (inductionMap_zero_left ν) P _ e ?_ ?_
  · intro t p
    change e.symm (castW k Γ (zero_add ν) (inductionMap k Γ 0 ν t) • p) =
      t • (e.symm p : ExtTensor k W₀ P.carrier)
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, add_smul, map_add, h₁, h₂, add_smul]
    | tmul a b =>
      obtain ⟨c, rfl⟩ := (weightedKLRZeroEquiv (Γ := Γ)).surjective a
      have ht : (weightedKLRZeroEquiv (Γ := Γ) c ⊗ₜ[k] b) = c • ((1 : W₀) ⊗ₜ[k] b) := by
        rw [weightedKLRZeroEquiv_apply, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
      rw [ht, map_smul (inductionMap k Γ 0 ν), map_smul (castW k Γ (zero_add ν)),
        inductionMap_one_tmul, smul_assoc, smul_assoc, map_smul e.symm]
      have hact := ExtTensor.smul_tmul (k := k) (1 : W₀) b (1 : W₀) p
      rw [one_smul] at hact
      simpa only [hsymm] using congrArg (c • ·) hact.symm
  · intro d p hp
    change e.symm p ∈ ExtTensor.grading (G.klrGrade 0) P.grading d
    rw [hsymm]
    simpa only [zero_add] using ExtTensor.tmul_mem_grading
      (SetLike.GradedOne.one_mem (A := G.klrGrade 0)) hp

private def resUnitRightIso {ν : I →₀ ℕ} (P : GProj (G.klrGrade ν)) :
    (G.resGProj ν 0 hD hZ hS (G.pullbackSum (add_zero ν) P)).Iso
      (P.extTensor (GProj.regular (G.klrGrade 0))) := by
  let W₀ := WeightedKLRAlgebra k Γ 0
  let e₀ : W₀ ≃ₗ[k] k := (weightedKLRZeroEquiv (Γ := Γ)).symm.toLinearEquiv
  let e : ExtTensor k P.carrier W₀ ≃ₗ[k] P.carrier :=
    (TensorProduct.congr (LinearEquiv.refl k P.carrier) e₀).trans (TensorProduct.rid k P.carrier)
  have hsymm (p : P.carrier) : e.symm p = ExtTensor.tmul p (1 : W₀) := by
    change (TensorProduct.congr (LinearEquiv.refl k P.carrier) e₀).symm
      ((TensorProduct.rid k P.carrier).symm p) = _
    rw [TensorProduct.rid_symm_apply, TensorProduct.congr_symm_tmul]
    change p ⊗ₜ[k] weightedKLRZeroEquiv (Γ := Γ) 1 = _
    rw [map_one]
    rfl
  refine G.resUnitIso hD hZ hS (add_zero ν) (inductionMap_zero_right ν) P _ e ?_ ?_
  · intro t p
    change e.symm (castW k Γ (add_zero ν) (inductionMap k Γ ν 0 t) • p) =
      t • (e.symm p : ExtTensor k P.carrier W₀)
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, add_smul, map_add, h₁, h₂, add_smul]
    | tmul a b =>
      obtain ⟨c, rfl⟩ := (weightedKLRZeroEquiv (Γ := Γ)).surjective b
      have ht : (a ⊗ₜ[k] weightedKLRZeroEquiv (Γ := Γ) c) = c • (a ⊗ₜ[k] (1 : W₀)) := by
        rw [weightedKLRZeroEquiv_apply, ← TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one]
      rw [ht, map_smul (inductionMap k Γ ν 0), map_smul (castW k Γ (add_zero ν)),
        inductionMap_tmul_one, smul_assoc, smul_assoc, map_smul e.symm]
      have hact := ExtTensor.smul_tmul (k := k) a (1 : W₀) p (1 : W₀)
      rw [one_smul] at hact
      simpa only [hsymm] using congrArg (c • ·) hact.symm
  · intro d p hp
    change e.symm p ∈ ExtTensor.grading P.grading (G.klrGrade 0) d
    rw [hsymm]
    simpa only [add_zero] using ExtTensor.tmul_mem_grading hp
      (SetLike.GradedOne.one_mem (A := G.klrGrade 0))

variable {ν : I →₀ ℕ} [HasGdim (G.klrGrade 0)] [HasGdim (G.klrGrade ν)]

/-- The `(0, ν)` component of Webster's coproduct is `x ↦ 1 ⊗ x`. -/
theorem coproductK0_zero_left (H : TensorK0Hyp (G.klrGrade 0) (G.klrGrade ν))
    (x : K0 (G.klrGrade ν)) :
    G.coproductK0 hD hZ hS 0 ν H (G.K0cast (zero_add ν).symm x) = G.K0one ⊗ₜ x := by
  induction x using K0.induction_on with
  | of P =>
    apply (G.k0TensorEquiv 0 ν H).injective
    rw [G.k0TensorEquiv_coproductK0, G.K0cast_pullbackSum (zero_add ν), G.resK0_of,
      k0TensorEquiv_tmul, K0one, K0.extTensor_of]
    exact K0.of_eq_of_iso (G.resUnitLeftIso hD hZ hS P)
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProduct.tmul_add]
  | neg x hx => rw [map_neg, map_neg, hx, TensorProduct.tmul_neg]

/-- The `(ν, 0)` component of Webster's coproduct is `x ↦ x ⊗ 1`. -/
theorem coproductK0_zero_right (H : TensorK0Hyp (G.klrGrade ν) (G.klrGrade 0))
    (x : K0 (G.klrGrade ν)) :
    G.coproductK0 hD hZ hS ν 0 H (G.K0cast (add_zero ν).symm x) = x ⊗ₜ G.K0one := by
  induction x using K0.induction_on with
  | of P =>
    apply (G.k0TensorEquiv ν 0 H).injective
    rw [G.k0TensorEquiv_coproductK0, G.K0cast_pullbackSum (add_zero ν), G.resK0_of,
      k0TensorEquiv_tmul, K0one, K0.extTensor_of]
    exact K0.of_eq_of_iso (G.resUnitRightIso hD hZ hS P)
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProduct.add_tmul]
  | neg x hx => rw [map_neg, map_neg, hx, TensorProduct.neg_tmul]

end Categorification.WeightedKLR.GradingDatum
