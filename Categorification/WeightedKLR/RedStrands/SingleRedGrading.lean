/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EraseRed
import Categorification.WeightedKLR.RedStrands.Projectives
import Categorification.KLR.CyclotomicGradedInduction
import Categorification.Algebra.Graded.K0Map

/-!
# Graded cyclotomic equivalence for one red strand

Webster, arXiv:1309.3796v2, §4.4, Theorem 4.20. Inserting a stationary red
strand on the left preserves diagram degrees and identifies the graded projective
Grothendieck groups in every weight.
-/

noncomputable section
namespace Categorification.Stendhal.SingleRed

open KLR KLRAlgebra Categorification.Graded
open scoped DirectSum

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin 1 → I →₀ ℕ)
  (G : GradingDatum Q) (d : I → ℤ) (hd : ∀ i, G.degX i = 2 * d i) (ν : Multiset I)

local notation "H" => stendhalGradingDatum Λ G d hd
local notation "src" => CycKLR.grade G (Λ 0) ν
local notation "dst" => tensorProductGrade H ν
local notation "σ" => cyclotomicEquiv Q Λ ν

section Reindex
variable {J : Type*} [DecidableEq J] {f : I → J} (hf : Function.Injective f)
  {P : J → J → MvPolynomial (Fin 2) k} (D : GradingDatum P)
  (B : GradingDatum (fun a b => P (f a) (f b)))
  (hx : ∀ a, B.degX a = D.degX (f a)) (hψ : ∀ a b, B.degΨ a b = D.degΨ (f a) (f b))
local notation "ρ" => reindexEquiv hf P ν

include hx hψ in
private theorem reindex_coaction (z : KLRAlgebra k (fun a b => P (f a) (f b)) ν) :
    D.coaction ((ρ) z) = AddMonoidAlgebra.mapAlgHom ℤ (ρ).toAlgHom (B.coaction z) := by
  classical
  induction z using klr_induction with
  | hr r => simp only [AlgEquiv.commutes, AlgHom.commutes]
  | hadd x y h₁ h₂ => simp only [map_add, h₁, h₂]
  | hmul x y h₁ h₂ => simp only [map_mul, h₁, h₂]
  | he s => simp only [reindexEquiv_e, GradingDatum.coaction_e, AddMonoidAlgebra.mapAlgHom_single,
      AlgEquiv.coe_toAlgHom]
  | hx a =>
    simp only [reindexEquiv_x, GradingDatum.coaction_x, map_sum, AddMonoidAlgebra.mapAlgHom_single,
      AlgEquiv.coe_toAlgHom, map_mul, reindexEquiv_e]
    symm
    apply Fintype.sum_equiv (Seq.mapEquiv hf ν)
    intro s
    simp only [Seq.mapEquiv_apply, GradingDatum.dx, Seq.map_lbl, Fin.cast_cast, Fin.cast_refl, id_eq, hx]
  | hψ j =>
    simp only [reindexEquiv_ψ, GradingDatum.coaction_ψ, map_sum, AddMonoidAlgebra.mapAlgHom_single,
      AlgEquiv.coe_toAlgHom, map_mul, reindexEquiv_e]
    symm
    apply Fintype.sum_equiv (Seq.mapEquiv hf ν)
    intro s
    simp only [Seq.mapEquiv_apply]
    congr 1
    by_cases hj : j + 1 < ν.card
    · have hj' : j + 1 < (ν.map f).card := by simpa using hj
      rw [B.dψ_of_lt hj, D.dψ_of_lt hj', hψ]
      rfl
    · simp [GradingDatum.dψ, hj]

include hx hψ in
private theorem reindex_mem_grade {n : ℤ} {z} (hz : z ∈ B.grade ν n) :
    (ρ) z ∈ D.grade (ν.map f) n := by
  rw [GradingDatum.mem_grade, reindex_coaction ν hf D B hx hψ, B.mem_grade.mp hz,
    AddMonoidAlgebra.mapAlgHom_single]
  rfl
end Reindex

/-- Inserting the one red strand preserves the degree of every cyclotomic diagram
(Webster, Definition 4.4 and Theorem 4.20). -/
theorem cyclotomicEquiv_mem_grade {n : ℤ} {z} (hz : z ∈ src n) : σ z ∈ dst n := by
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz
  change cyclotomicProjection Q Λ ν (CycKLR.mk k Q _ ν u) ∈ dst n
  rw [cyclotomicProjection, CycKLR.lift_mk]
  apply Graded.mem_map_of_mem
  change StendhalAlgebraAllOrders.ofKLR k Q Λ ν _ ∈ allOrdersGrade H ν n
  apply Graded.mem_map_of_mem
  apply (H).castKLR_mem_grade
  apply (blockR _ _).valHom_mem_grade
  exact reindex_mem_grade ν Sum.inl_injective H G (fun _ => rfl) (fun _ _ => rfl) hu

/-- Erasure preserves each homogeneous piece as well. -/
theorem cyclotomicEquiv_symm_mem_grade {n : ℤ} {z} (hz : z ∈ dst n) : (σ).symm z ∈ src n :=
  (GradedEquiv.ofPreserves (ℳ := src) (𝒩 := dst) (σ).toLinearEquiv
    (fun _ _ hx => cyclotomicEquiv_mem_grade Λ G d hd ν hx)).symm_map_mem' hz

universe u

private theorem map_symm_map {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} (f : A ≃ₐ[k] B)
    (h : ∀ ⦃i a⦄, a ∈ 𝒜 i → f a ∈ ℬ i) (h' : ∀ ⦃i b⦄, b ∈ ℬ i → f.symm b ∈ 𝒜 i)
    (x : K0 𝒜) : K0.map (𝒜 := ℬ) (𝒜' := 𝒜) f.symm h (K0.map (𝒜 := 𝒜) (𝒜' := ℬ) f h' x) = x := by
  induction x using K0.induction_on with
  | of P =>
    rw [K0.map_of]
    exact K0.map_of_semilinear f.symm h _ P (AddEquiv.refl _) (fun _ _ => rfl)
      (fun _ _ hx => hx) (fun _ _ hx => hx)
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | neg x hx => simp only [map_neg, hx]

/-- The weightwise Laurent-linear equivalence on graded projective classes induced by
Webster's Theorem 4.20. -/
def cyclotomicK0Equiv : K0 src ≃ₗ[LaurentPolynomial ℤ] K0 dst where
  __ := K0.map (𝒜 := src) (𝒜' := dst) σ
    (fun _ _ hx => cyclotomicEquiv_symm_mem_grade Λ G d hd ν hx)
  invFun := K0.map (𝒜 := dst) (𝒜' := src) (σ).symm
    (fun _ _ hx => cyclotomicEquiv_mem_grade Λ G d hd ν hx)
  left_inv := map_symm_map σ _ _
  right_inv := map_symm_map (σ).symm _ _

@[simp] theorem cyclotomicK0Equiv_of (P : GProj src) :
    cyclotomicK0Equiv Λ G d hd ν (K0.of P) =
      K0.of (GProj.restrict (𝒜 := src) (𝒜' := dst) σ
        (fun _ _ hx => cyclotomicEquiv_symm_mem_grade Λ G d hd ν hx) P) := K0.map_of ..

/-- Red insertion identifies the regular projective classes in each weight. -/
@[simp] theorem cyclotomicK0Equiv_regular :
    cyclotomicK0Equiv Λ G d hd ν (K0.of (GProj.regular src)) = K0.of (GProj.regular dst) :=
  K0.map_of_semilinear (σ) (fun _ _ hx => cyclotomicEquiv_symm_mem_grade Λ G d hd ν hx)
    (GProj.regular src) (GProj.regular dst) (σ).toRingEquiv.toAddEquiv
    (fun a x => map_mul (σ) a x) (fun _ _ hx => cyclotomicEquiv_mem_grade Λ G d hd ν hx)
    (fun _ _ hx => cyclotomicEquiv_symm_mem_grade Λ G d hd ν hx)

/-- The class of a homogeneous principal projective is carried to the principal
projective cut out by the image of its idempotent (Webster, §4.4, Theorem 4.20). -/
theorem cyclotomicK0Equiv_ofIdempotent {e} (he : IsIdempotentElem e) (h₀ : e ∈ src 0) :
    cyclotomicK0Equiv Λ G d hd ν (K0.of (GProj.ofIdempotent e he h₀)) =
      K0.of (GProj.ofIdempotent (σ e) (he.map (σ)) (cyclotomicEquiv_mem_grade Λ G d hd ν h₀)) := by
  let f : leftIdeal e ≃+ leftIdeal (σ e) :=
    { toFun := fun x => ⟨σ x.1, (map_mul (σ) x.1 e).symm.trans (congrArg (σ) x.2)⟩
      invFun := fun y => ⟨(σ).symm y.1, (σ).injective (by
        rw [map_mul, AlgEquiv.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext <| (σ).symm_apply_apply x.1
      right_inv := fun y => Subtype.ext <| (σ).apply_symm_apply y.1
      map_add' := fun x y => Subtype.ext <| map_add (σ) x.1 y.1 }
  apply K0.map_of_semilinear (e := f)
  · intro a x
    exact Subtype.ext <| map_mul (σ) a x.1
  · exact fun _ _ hx => cyclotomicEquiv_mem_grade Λ G d hd ν hx
  · exact fun _ _ hx => cyclotomicEquiv_symm_mem_grade Λ G d hd ν hx

/-- Cyclotomic induction transported to the one-red weight groups through Theorem 4.20. -/
def indK0 (i : I) : K0 dst →ₗ[LaurentPolynomial ℤ] K0 (tensorProductGrade H ({i} + ν)) where
  toFun x := cyclotomicK0Equiv Λ G d hd ({i} + ν)
    (CycKLR.indK0 G (Λ 0) i ν ((cyclotomicK0Equiv Λ G d hd ν).symm x))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by simp only [map_smul, RingHom.id_apply]

theorem indK0_cyclotomicK0Equiv (i : I) (x : K0 src) :
    indK0 Λ G d hd ν i (cyclotomicK0Equiv Λ G d hd ν x) =
      cyclotomicK0Equiv Λ G d hd ({i} + ν) (CycKLR.indK0 G (Λ 0) i ν x) := by
  change cyclotomicK0Equiv Λ G d hd _ (CycKLR.indK0 G (Λ 0) i ν
    ((cyclotomicK0Equiv Λ G d hd ν).symm (cyclotomicK0Equiv Λ G d hd ν x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The first transported lowering takes the one-red vacuum to the regular
projective in the one-black block (Webster, Definition 3.15 and Theorem 4.20). -/
theorem indK0_vacuum (i : I) :
    indK0 Λ G d hd 0 i (K0.of (GProj.regular (tensorProductGrade H 0))) =
      K0.of (GProj.regular (tensorProductGrade H ({i} + 0))) := by
  rw [← cyclotomicK0Equiv_regular Λ G d hd 0, indK0_cyclotomicK0Equiv, CycKLR.indK0_vacuum,
    cyclotomicK0Equiv_regular]

/-- The direct sum of the graded cyclotomic identifications in all black weights,
as needed for the one-factor case of Webster, §4.7, Theorem 4.38. -/
def totalCyclotomicK0Equiv : CycKLR.projectiveK0 G (Λ 0) ≃ₗ[LaurentPolynomial ℤ]
    ⨁ β : Multiset I, K0 (tensorProductGrade H β) :=
  DirectSum.congrLinearEquiv (cyclotomicK0Equiv Λ G d hd)

@[simp] theorem totalCyclotomicK0Equiv_lof (x : K0 src) :
    totalCyclotomicK0Equiv Λ G d hd
      (DirectSum.lof (LaurentPolynomial ℤ) _ (fun β => K0 (CycKLR.grade G (Λ 0) β)) ν x) =
      DirectSum.lof (LaurentPolynomial ℤ) _ (fun β => K0 (tensorProductGrade H β)) ν
        (cyclotomicK0Equiv Λ G d hd ν x) := by
  simp [totalCyclotomicK0Equiv, DirectSum.coe_congrLinearEquiv]

section Sequences

variable {J : Type} [DecidableEq J] {F : Type*} [Field F] {P : J → J → MvPolynomial (Fin 2) F}
  (Λ₁ : Fin 1 → J →₀ ℕ) (D : GradingDatum P) (δ : J → ℤ) (hδ : ∀ j, D.degX j = 2 * δ j)
  (β : Multiset J)

local notation "π" => CycKLR.mk F P (fun i => Polynomial.X ^ Λ₁ 0 i) β

/-- The principal projective on a black word corresponds to the Stendhal projective
on the same word preceded by its one red strand (Webster, Theorem 4.20 and §4.7). -/
theorem cyclotomicK0Equiv_sequenceProj (s : Seq β) :
    cyclotomicK0Equiv Λ₁ D δ hδ β
      (K0.of (GProj.ofIdempotent (π (e s)) (IsIdempotentElem.map (e_mul_self (Q := P) s) (π))
        (Graded.mem_map_of_mem (D.grade β) (π).toLinearMap (D.e_mem_grade s)))) =
      K0.of (sequenceProj (stendhalGradingDatum Λ₁ D δ hδ) (insertWord β s) (ordered β _)) := by
  refine (cyclotomicK0Equiv_ofIdempotent Λ₁ D δ hδ β
    (e := π (e s)) (IsIdempotentElem.map (e_mul_self (Q := P) s) (π))
    (Graded.mem_map_of_mem (D.grade β) (π).toLinearMap (D.e_mem_grade s))).trans ?_
  apply K0.of_ofIdempotent_congr
  change cyclotomicProjection P Λ₁ β (π (e s)) = mk P Λ₁ β (StendhalAlgebraAllOrders.e _)
  rw [cyclotomicProjection, CycKLR.lift_mk, insertRed_e]

end Sequences

end Categorification.Stendhal.SingleRed
