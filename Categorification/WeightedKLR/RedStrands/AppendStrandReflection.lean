/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection
import Categorification.WeightedKLR.RedStrands.LastRedBlackBimodule
import Categorification.KLR.CyclotomicSplit

/-!
# Adding a strand on the right commutes with horizontal reflection

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
Proposition 4.32. The `Eᵢ` part of Proposition 4.32 is the mirror image of the `Fᵢ` part
("a similar argument"). The mirror is the horizontal reflection `tensorFlip` of the tensor
product algebra `T^λ`, induced by the flip of KLR diagrams. This file shows that adding the last
red strand (`appendRed`, Proposition 4.18) and adding a black strand on the right (`appendBlack`,
the map `ν_i`) commute with it, so that the `Fᵢ` statements transport to their mirror images.

## Main results

* `tensorFlip`: the horizontal reflection of `T^λ`, an involutive anti-automorphism.
* `tensorFlip_comm_of_generators`: a multiplicative map that cuts every generator by `φ 1` to a
  reflection-symmetric diagram commutes with reflection.
* `tensorFlip_appendRed`, `tensorFlip_appendBlack`: the two strand-adding maps commute with
  reflection.

The reflection is constructed over a field `k`, as in Webster's paper.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

section Flip

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "π" => stendhalTensorProjection (Q := Q) Λ ν

/-- Horizontal reflection of the tensor product algebra, as a `k`-linear anti-automorphism. -/
def tensorFlip : T →ₗ[k] T :=
  (opLinearEquiv k).symm.toLinearMap ∘ₗ (tensorReflect (Q := Q) (Λ := Λ) (ν := ν)).toLinearMap

theorem tensorFlip_apply (z : T) :
    tensorFlip z = (tensorReflect (Q := Q) (Λ := Λ) (ν := ν) z).unop := rfl

theorem tensorFlip_mul (a b : T) : tensorFlip (a * b) = tensorFlip b * tensorFlip a := by
  rw [tensorFlip_apply, tensorFlip_apply, tensorFlip_apply, map_mul, unop_mul]

theorem tensorFlip_one : tensorFlip (1 : T) = 1 := by
  rw [tensorFlip_apply, map_one, unop_one]

theorem tensorFlip_tensorFlip (z : T) : tensorFlip (tensorFlip z) = z :=
  unop_tensorReflect_unop_tensorReflect z

theorem tensorFlip_projection (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    tensorFlip (π a) = π (hflip a) := by
  rw [tensorFlip_apply, tensorReflect_projection, unop_op]

theorem tensorFlip_mk_e (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    tensorFlip (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs)) =
      TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) := by
  rw [← stendhalTensorProjection_e, tensorFlip_projection, hflip_e]

theorem stendhalTensorProjection_surjective : Function.Surjective π := by
  intro z
  obtain ⟨y, rfl⟩ := (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk'_surjective z
  obtain ⟨w, rfl⟩ := orderProjection_surjective Q Λ ν y
  obtain ⟨a, rfl⟩ := StendhalAlgebraAllOrders.ofKLR_surjective (k := k) (Q := Q) (Λ := Λ)
    (ν := ν) w
  exact ⟨a, rfl⟩

end Flip

section Generic

variable {ℓ₀ ℓ₁ : ℕ} {Λ₀ : Fin ℓ₀ → I →₀ ℕ} {Λ₁ : Fin ℓ₁ → I →₀ ℕ} {ν₀ ν₁ : Multiset I}

local notation "T₀" => TensorProductAlgebra k Q Λ₀ ν₀
local notation "T₁" => TensorProductAlgebra k Q Λ₁ ν₁
local notation "A₀" => KLRAlgebra k (stendhalQ Q Λ₀) (stendhalWeight ℓ₀ ν₀)
local notation "A₁" => KLRAlgebra k (stendhalQ Q Λ₁) (stendhalWeight ℓ₁ ν₁)
local notation "π₀" => stendhalTensorProjection (Q := Q) Λ₀ ν₀
local notation "π₁" => stendhalTensorProjection (Q := Q) Λ₁ ν₁

/-- A strand-adding map commutes with horizontal reflection when it does so on the unit and it
sends each KLR generator to a reflection-symmetric diagram cut on both sides by `φ 1`. -/
theorem tensorFlip_comm_of_generators (φ : T₀ → T₁)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hmul : ∀ a b, φ (a * b) = φ a * φ b)
    (hsmul : ∀ (c : k) a, φ (c • a) = c • φ a) (hu : tensorFlip (φ 1) = φ 1)
    (hgen : ∀ g : A₀, ((∃ s, g = e s) ∨ (∃ b, g = x b) ∨ ∃ j, g = ψ j) →
      ∃ c : A₁, hflip c = c ∧ φ (π₀ g) = φ 1 * π₁ c * φ 1) (z : T₀) :
    tensorFlip (φ z) = φ (tensorFlip z) := by
  obtain ⟨a, rfl⟩ := stendhalTensorProjection_surjective z
  rw [tensorFlip_projection]
  have key : ∀ g : A₀, ((∃ s, g = e s) ∨ (∃ b, g = x b) ∨ ∃ j, g = ψ j) →
      hflip g = g → tensorFlip (φ (π₀ g)) = φ (π₀ (hflip g)) := by
    intro g hg hfl
    obtain ⟨c, hc, h⟩ := hgen g hg
    rw [hfl, h, tensorFlip_mul, tensorFlip_mul, hu, tensorFlip_projection, hc, mul_assoc]
  induction a using klr_induction with
  | hadd u v hu' hv' => rw [map_add, hadd, map_add, hflip_add, map_add, hadd, hu', hv']
  | hmul u v hu' hv' =>
    rw [map_mul, hmul, tensorFlip_mul, hu', hv', hflip_mul, map_mul, hmul]
  | hr r =>
    rw [hflip_algebraMap, Algebra.algebraMap_eq_smul_one, map_smul, map_one, hsmul,
      LinearMap.map_smul, hu]
  | he s => exact key _ (Or.inl ⟨s, rfl⟩) (hflip_e s)
  | hx b => exact key _ (Or.inr (Or.inl ⟨b, rfl⟩)) (hflip_x b)
  | hψ j => exact key _ (Or.inr (Or.inr ⟨j, rfl⟩)) (hflip_ψ j)

/-- A map of red-ordered algebras induced by a multiplicative map `F` on all orders sends an
ordered generator to `f 1 · c · f 1` in the violating quotient, when `F` sends it to `c · F 1`. -/
theorem mk_generator_cut (f : StendhalAlgebra k Q Λ₀ ν₀ → StendhalAlgebra k Q Λ₁ ν₁)
    (F : StendhalAlgebraAllOrders k Q Λ₀ ν₀ → StendhalAlgebraAllOrders k Q Λ₁ ν₁)
    (hf : ∀ z, (f z).val = F z.val) (hfm : ∀ a b, f (a * b) = f a * f b)
    (hF : ∀ a b, F (a * b) = F a * F b) (g : A₀) (c : A₁)
    (hg : F (StendhalAlgebraAllOrders.ofKLR k Q Λ₀ ν₀ g) =
      StendhalAlgebraAllOrders.ofKLR k Q Λ₁ ν₁ c * F 1) :
    TensorProductAlgebra.mk Q Λ₁ ν₁
        (f (orderProjection Q Λ₀ ν₀ (StendhalAlgebraAllOrders.ofKLR k Q Λ₀ ν₀ g))) =
      TensorProductAlgebra.mk Q Λ₁ ν₁ (f 1) * π₁ c * TensorProductAlgebra.mk Q Λ₁ ν₁ (f 1) := by
  set y := orderProjection Q Λ₀ ν₀ (StendhalAlgebraAllOrders.ofKLR k Q Λ₀ ν₀ g)
  have hP : F (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν₀) = (f 1).val := by
    rw [hf]; rfl
  have hy : (f y).val = StendhalAlgebraAllOrders.ofKLR k Q Λ₁ ν₁ c * (f 1).val := by
    rw [hf, show y.val = StendhalAlgebraAllOrders.ofKLR k Q Λ₀ ν₀ g *
      StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν₀ from rfl, hF, hg, mul_assoc, ← hF,
      one_mul, hP]
  have h1 : (1 : StendhalAlgebra k Q Λ₁ ν₁).val * (f 1).val = (f 1).val :=
    KLR.Corner.E_mul_val (f 1)
  have hfy : f y = f 1 * orderProjection Q Λ₁ ν₁ (StendhalAlgebraAllOrders.ofKLR k Q Λ₁ ν₁ c) *
      f 1 := by
    rw [← one_mul y, hfm]
    apply Subtype.ext
    change (f 1).val * (f y).val = (f 1).val *
      (StendhalAlgebraAllOrders.ofKLR k Q Λ₁ ν₁ c * (1 : StendhalAlgebra k Q Λ₁ ν₁).val) *
        (f 1).val
    rw [hy, mul_assoc (f 1).val, mul_assoc (StendhalAlgebraAllOrders.ofKLR k Q Λ₁ ν₁ c), h1]
  rw [hfy, map_mul, map_mul]
  rfl

end Generic

section AppendRed

variable {ℓ : ℕ} (Q) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "μ" => stendhalWeight ℓ ν

/-- The idempotent `e_ℓ` of the last red strand is reflection-symmetric. -/
theorem tensorFlip_lastRedIdem :
    tensorFlip (TensorProductAlgebra.lastRedIdem Q Λ ν) =
      TensorProductAlgebra.lastRedIdem Q Λ ν := by
  classical
  rw [TensorProductAlgebra.lastRedIdem, StendhalAlgebra.lastRedIdem]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact tensorFlip_mk_e s.1 s.2

/-- Adding the last red strand commutes with horizontal reflection. -/
theorem tensorFlip_appendRed (z : TensorProductAlgebra k Q Λ₀ ν) :
    tensorFlip (appendRed Q Λ ν z).val = (appendRed Q Λ ν (tensorFlip z)).val := by
  let F : StendhalAlgebraAllOrders k Q Λ₀ ν → StendhalAlgebraAllOrders k Q Λ ν :=
    fun a => (appendRedAllOrders Q Λ ν a).val
  have hF : ∀ a b, F (a * b) = F a * F b := fun a b => by
    simp only [F, map_mul, KLR.Corner.val_mul]
  have hcut := mk_generator_cut (appendRedStendhalValue Q Λ ν) F
    (appendRedStendhalValue_val Q Λ ν) (map_mul _) hF
  refine tensorFlip_comm_of_generators (fun z => (appendRed Q Λ ν z).val)
    (fun a b => by simp only [map_add, KLR.Corner.val_add])
    (fun a b => by simp only [map_mul, KLR.Corner.val_mul])
    (fun c a => by simp only [map_smul, KLR.Corner.val_smul])
    (by simp only [map_one]; exact tensorFlip_lastRedIdem Q Λ ν) ?_ z
  rintro g (⟨s, rfl⟩ | ⟨b, rfl⟩ | ⟨j, rfl⟩)
  · refine ⟨e (appendRedLoading s), hflip_e _, ?_⟩
    have h := hF (StendhalAlgebraAllOrders.e s) 1
    rw [mul_one] at h
    exact hcut _ _ (h.trans (congrArg (· * F 1) (appendRedAllOrders_e Q Λ ν s)))
  · refine ⟨x (appendRedPosition b), hflip_x _, ?_⟩
    exact hcut _ _ (appendRedAllOrders_x Q Λ ν b)
  · by_cases hj : j + 1 < Multiset.card μ
    · refine ⟨ψ j, hflip_ψ _, ?_⟩
      exact hcut _ _ (appendRedAllOrders_ψ Q Λ ν j hj)
    · refine ⟨0, hflip_zero, ?_⟩
      rw [ψ_eq_zero j (by omega), map_zero, map_zero, map_zero, KLR.Corner.val_zero, mul_zero,
        zero_mul]

end AppendRed

section AppendBlack

variable {ℓ : ℕ} (Q) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)

/-- Adding a black strand on the right (Webster's `ν_i`) commutes with horizontal reflection. -/
theorem tensorFlip_appendBlack (z : TensorProductAlgebra k Q Λ ν) :
    tensorFlip (appendBlack Q Λ i ν z) = appendBlack Q Λ i ν (tensorFlip z) := by
  classical
  let F : StendhalAlgebraAllOrders k Q Λ ν → StendhalAlgebraAllOrders k Q Λ νᵢ :=
    fun a => (appendBlackAllOrders Q Λ i ν a).val
  have hF : ∀ a b, F (a * b) = F a * F b := fun a b => by
    simp only [F, map_mul, KLR.Corner.val_mul]
  have hcut := mk_generator_cut (appendBlackStendhal Q Λ i ν) F
    (appendBlackStendhal_val Q Λ i ν) (map_mul _) hF
  refine tensorFlip_comm_of_generators (appendBlack Q Λ i ν) (map_add _) (map_mul _)
    (map_smul _) ?_ ?_ z
  · rw [appendBlack_one, map_sum]
    exact Finset.sum_congr rfl fun s _ => tensorFlip_mk_e _ _
  rintro g (⟨s, rfl⟩ | ⟨b, rfl⟩ | ⟨j, rfl⟩)
  · refine ⟨e (appendBlackLoading i ν s), hflip_e _, ?_⟩
    have h := hF (StendhalAlgebraAllOrders.e s) 1
    rw [mul_one] at h
    exact hcut _ _ (h.trans (congrArg (· * F 1) (appendBlackAllOrders_e Q Λ i ν s)))
  · exact ⟨_, hflip_x _, hcut _ _ (appendBlackAllOrders_x Q Λ i ν b)⟩
  · by_cases hj : j + 1 < Multiset.card μ
    · exact ⟨ψ j, hflip_ψ _, hcut _ _ (appendBlackAllOrders_ψ Q Λ i ν j hj)⟩
    · refine ⟨0, hflip_zero, ?_⟩
      rw [ψ_eq_zero j (by omega), map_zero, map_zero, map_zero, mul_zero, zero_mul]

end AppendBlack

end Categorification.Stendhal
