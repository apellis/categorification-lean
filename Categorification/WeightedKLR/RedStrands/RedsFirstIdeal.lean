/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ShuffleCompression
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Detection of ideals in the all-reds-first corner

Webster, arXiv:1309.3796v2, Lemma 4.26, last paragraph of the proof.
A nonzero affine diagram has a nonzero component between ordered boundaries.
Its red shuffles give a nonzero diagram between all-reds-first boundaries in
the same ideal. Choosing a coefficient in a basis of the left tensor factor
gives the same result for bubble algebras free over the coefficient ring.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
    {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
    {C : QuantumGroup.CartanDatum I}

local notation "T" => StendhalAlgebra k Q Λ ν
local notation "S" => OrdSeq ℓ ν
local notation "E" => (fun s : OrdSeq ℓ ν => StendhalAlgebra.e (Q := Q) (Λ := Λ) (Subtype.val s) (Subtype.property s))

private theorem exists_detecting_multipliers (hQ : IsRouquierQ C Q) {x : T} (hx : x ≠ 0) :
    ∃ (p q : S) (c d : T), RedsFirst p.val ∧ RedsFirst q.val ∧
      E p * c = c ∧ d * E q = d ∧ c * x * d ≠ 0 := by
  classical
  have hsum : (∑ s : S, E s) = 1 := by
    apply Subtype.ext
    rw [KLR.Corner.val_sum, KLR.Corner.val_one]
    change (∑ s : S, StendhalAlgebraAllOrders.e s.val) = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
    exact (Finset.sum_subtype _ (fun s => by simp) _).symm
  have hs : ∃ s t : S, E s * x * E t ≠ 0 := by
    by_contra! h
    apply hx
    calc x = (∑ s : S, E s) * x * (∑ t : S, E t) := by rw [hsum,one_mul,mul_one]
         _ = 0 := by simp only [Finset.sum_mul, Finset.mul_sum, h, Finset.sum_const_zero]
  obtain ⟨s,t,hst⟩ := hs
  obtain ⟨p,q,hp,hq,c,d,hpf,hqf,hpc,hcs,htd,hdq,hinj⟩ :=
    exists_redsFirst_compression (Λ := Λ) hQ s.val t.val s.property t.property
  refine ⟨⟨p,hp⟩,⟨q,hq⟩,c,d,hpf,hqf,hpc,hdq,?_⟩
  intro hz
  apply hst
  have idem (r : S) : E r * E r = E r := Subtype.ext (by
    change StendhalAlgebraAllOrders.e r.val * StendhalAlgebraAllOrders.e r.val = StendhalAlgebraAllOrders.e r.val
    simp [StendhalAlgebraAllOrders.e_mul_e])
  let y := E s * x * E t
  let Z := {y : T // E s * y = y ∧ y * E t = y}
  let y' : Z := ⟨y, by simp only [y, ← mul_assoc, idem], by simp only [y, mul_assoc, idem]⟩
  let zero' : Z := ⟨0, by simp, by simp⟩
  have hcomp : c * y'.val * d = c * zero'.val * d := by
    change c * (E s * x * E t) * d = c * 0 * d
    rw [← mul_assoc c, ← mul_assoc c, hcs, mul_assoc _ (E t), htd, hz, mul_zero, zero_mul]
  exact congrArg Subtype.val (hinj hcomp : y' = zero')

private theorem exists_mem_ne_zero {A : Type*} [Ring A]
    (J : TwoSidedIdeal A) (hJ : J ≠ ⊥) : ∃ x ∈ J, x ≠ 0 := by
  by_contra! h
  apply hJ
  apply le_antisymm _ bot_le
  intro x hx
  rw [h x hx]
  exact TwoSidedIdeal.zero_mem _

/-- The affine all-reds-first corner meets every nonzero two-sided ideal
(Webster, arXiv:1309.3796v2, proof of Lemma 4.26, using Lemma 4.17). -/
theorem exists_redsFirst_ideal_element (hQ : IsRouquierQ C Q) (J : TwoSidedIdeal T) (hJ : J ≠ ⊥) :
    ∃ (p q : S) (y : T), RedsFirst p.val ∧ RedsFirst q.val ∧
      y ∈ J ∧ y ≠ 0 ∧ E p * y = y ∧ y * E q = y := by
  obtain ⟨x,hx,hx'⟩ := exists_mem_ne_zero J hJ
  obtain ⟨p,q,c,d,hp,hq,hc,hd,hn⟩ := exists_detecting_multipliers hQ hx'
  exact ⟨p,q,c*x*d,hp,hq,J.mul_mem_right _ _ (J.mul_mem_left _ _ hx),hn,
    by rw [← mul_assoc, ← mul_assoc, hc], by rw [mul_assoc _ d, hd]⟩

section Tensor

variable {B : Type*} [Ring B] [Algebra k B]
local notation "BT" => B ⊗[k] T
local notation "ι" => (Algebra.TensorProduct.includeRight : T →ₐ[k] BT)

private theorem tensor_coefficient_mul {M : Type*} [DecidableEq M] (b : Module.Basis M k B)
    (i : M) (c d : T) (x : BT) :
    TensorProduct.equivFinsuppOfBasisLeft b (ι c * x * ι d) i =
      c * TensorProduct.equivFinsuppOfBasisLeft b x i * d := by
  induction x using TensorProduct.inductionOn with
  | tmul r t =>
    simp only [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
      mul_smul_comm, smul_mul_assoc]
  | add x y hx hy =>
    simp only [mul_add, add_mul, map_add, Finsupp.add_apply, hx, hy]

/-- The ideal-detection step of Webster, arXiv:1309.3796v2, Lemma 4.26
after tensoring with the algebra of bubbles at the left. The proof works
for every algebra `B` free as a module over the coefficient ring. -/
theorem exists_redsFirst_tensor_ideal_element [Module.Free k B] (hQ : IsRouquierQ C Q)
    (J : TwoSidedIdeal BT) (hJ : J ≠ ⊥) :
    ∃ (p q : S) (y : BT), RedsFirst p.val ∧ RedsFirst q.val ∧
      y ∈ J ∧ y ≠ 0 ∧ ι (E p) * y = y ∧ y * ι (E q) = y := by
  classical
  obtain ⟨x,hx,hx'⟩ := exists_mem_ne_zero J hJ
  let b := Module.Free.chooseBasis k B
  let coords := TensorProduct.equivFinsuppOfBasisLeft (N := T) b
  have hn : ∃ i, coords x i ≠ 0 := by
    by_contra! h
    exact hx' (coords.injective (by ext i; simpa using h i))
  obtain ⟨i,hi⟩ := hn
  obtain ⟨p,q,c,d,hp,hq,hc,hd,hne⟩ := exists_detecting_multipliers hQ hi
  refine ⟨p,q,ι c * x * ι d,hp,hq,J.mul_mem_right _ _ (J.mul_mem_left _ _ hx),?_,?_,?_⟩
  · intro hz
    apply hne
    rw [← tensor_coefficient_mul b i c d x, hz, map_zero]
    rfl
  · rw [← mul_assoc, ← mul_assoc, ← map_mul, hc]
  · rw [mul_assoc _ (ι d), ← map_mul, hd]

end Tensor

end Categorification.Stendhal
