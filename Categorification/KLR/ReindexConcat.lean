/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ReindexSymmetries
import Categorification.KLR.MackeySubquot
import Categorification.Algebra.BalancedTensorTransport

/-!
# Relabelling commutes with concatenation and induction

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5; Khovanov–Lauda I
(arXiv:0803.4121v2), §2.6.

Let `R₁ : Seq ν₁ ≃ Seq ν₂`, `R₂ : Seq ν₁' ≃ Seq ν₂'` and `R : Seq (ν₁ + ν₁') ≃ Seq (ν₂ + ν₂')`
be relabellings (`SeqRelabel`) with `R (i j) = R₁(i) R₂(j)` on concatenated sequences. Then the
attached isomorphisms of KLR algebras commute with the inclusions
`ι : R(ν) ⊗ R(ν') → R(ν + ν')` (`relabelHom_concat`), so `R` identifies the bimodules
`R(ν₁ + ν₁') 1_{ν₁,ν₁'}` and `R(ν₂ + ν₂') 1_{ν₂,ν₂'}` (`relabelIndBimod`), and a `k`-linear
isomorphism `N₁ ≅ N₂` intertwining `R₁ ⊗ R₂` induces `Ind_{ν₁,ν₁'} N₁ ≅ Ind_{ν₂,ν₂'} N₂`
(`relabelInd`), linear along `R` (`relabelInd_smul`). The last step is
`BalancedTensor.changeRingEquiv`.

`SeqRelabel.castRight` transports a relabelling along an equality of target weights; its
algebra map is the relabelling followed by `castAlg` (`relabelHom_castRight`).
`Seq.seqCast_map_append` is the compatibility of `𝐣 ↦ f ∘ 𝐣` with concatenation, read through
such casts.

No new hypothesis.

## Main definitions

* `KLR.SeqRelabel.castRight`, `KLR.KLRAlgebra.relabelIndBimod`, `KLR.KLRAlgebra.relabelInd`.

## Main results

* `KLR.KLRAlgebra.relabelHom_castRight`, `KLR.KLRAlgebra.relabelHom_oneConcat`,
  `KLR.KLRAlgebra.relabelHom_concat`, `KLR.KLRAlgebra.relabelInd_tmul`,
  `KLR.KLRAlgebra.relabelInd_smul`, `KLR.Seq.seqCast_map_append`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv TypeA MulOpposite
open scoped TensorProduct

variable {k : Type*} [CommRing k] {I₁ I₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]

/-! ### Casting the target of a relabelling -/

namespace SeqRelabel

variable {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
  {ν₁ : Multiset I₁} {ν₂ ν₃ : Multiset I₂}

/-- A relabelling `Seq ν₁ ≃ Seq ν₂` read with target `ν₃ = ν₂`. -/
def castRight (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂) (h : ν₂ = ν₃) : SeqRelabel k Q₁ Q₂ ν₁ ν₃ := by
  subst h; exact R

omit [DecidableEq I₁] [DecidableEq I₂] in
theorem castRight_equiv (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂) (h : ν₂ = ν₃) (i : Seq ν₁) :
    (R.castRight h).equiv i = KLRAlgebra.seqCast h (R.equiv i) := by
  subst h; rfl

end SeqRelabel

namespace KLRAlgebra

variable {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}

theorem relabelHom_castRight {ν₁ : Multiset I₁} {ν₂ ν₃ : Multiset I₂}
    (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂) (h : ν₂ = ν₃) (u : KLRAlgebra k Q₁ ν₁) :
    relabelHom (R.castRight h) u = castAlg Q₂ h (relabelHom R u) := by
  subst h; rfl

/-! ### Relabelling and concatenation -/

/-- Induction over the generators of a KLR algebra. -/
private theorem gen_induction {ν : Multiset I₁} {p : KLRAlgebra k Q₁ ν → Prop}
    (hadd : ∀ u v, p u → p v → p (u + v)) (hmul : ∀ u v, p u → p v → p (u * v))
    (hr : ∀ r : k, p (algebraMap k _ r)) (he : ∀ s, p (e s)) (hx : ∀ b, p (x b))
    (hψ : ∀ j, p (ψ j)) (b : KLRAlgebra k Q₁ ν) : p b := by
  obtain ⟨w, rfl⟩ := mk_surjective b
  induction w using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact hr r
  | grade1 g =>
    cases g with
    | idem s => exact he s
    | dot b => exact hx b
    | cross j => exact hψ j
  | mul u v hu hv => rw [map_mul]; exact hmul _ _ hu hv
  | add u v hu hv => rw [map_add]; exact hadd _ _ hu hv

variable {ν₁ ν₁' : Multiset I₁} {ν₂ ν₂' : Multiset I₂}
  (R₁ : SeqRelabel k Q₁ Q₂ ν₁ ν₂) (R₂ : SeqRelabel k Q₁ Q₂ ν₁' ν₂')
  (R : SeqRelabel k Q₁ Q₂ (ν₁ + ν₁') (ν₂ + ν₂'))

omit [DecidableEq I₁] [DecidableEq I₂] in
/-- The relabelling compatibility on concatenated sequences, for the inverse relabellings. -/
theorem symm_equiv_append
    (happ : ∀ i j, R.equiv (i.append j) = (R₁.equiv i).append (R₂.equiv j))
    (i : Seq ν₂) (j : Seq ν₂') :
    R.symm.equiv (i.append j) = (R₁.symm.equiv i).append (R₂.symm.equiv j) := by
  rw [SeqRelabel.symm_equiv, Equiv.symm_apply_eq, happ]
  simp

variable (happ : ∀ i j, R.equiv (i.append j) = (R₁.equiv i).append (R₂.equiv j))

include happ in
/-- **Relabelling preserves `1_{ν,ν'}`.** -/
theorem relabelHom_oneConcat :
    relabelHom R (oneConcat Q₁ ν₁ ν₁') = oneConcat Q₂ ν₂ ν₂' := by
  rw [oneConcat_eq, oneConcat_eq, map_sum]
  simp only [relabelHom_e, happ]
  exact Fintype.sum_equiv (R₁.equiv.prodCongr R₂.equiv) _ _ (fun p => rfl)

theorem concat_algebraMap_tmul_one (r : k) :
    concat Q₁ ν₁ ν₁' (algebraMap k (KLRAlgebra k Q₁ ν₁) r ⊗ₜ 1) =
      r • oneConcat Q₁ ν₁ ν₁' := by
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', map_smul,
    ← Algebra.TensorProduct.one_def, concat_one]

theorem concat_one_tmul_algebraMap (r : k) :
    concat Q₁ ν₁ ν₁' (1 ⊗ₜ algebraMap k (KLRAlgebra k Q₁ ν₁') r) =
      r • oneConcat Q₁ ν₁ ν₁' := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, map_smul,
    ← Algebra.TensorProduct.one_def, concat_one]

include happ in
theorem relabelHom_concat_tmul_one (a : KLRAlgebra k Q₁ ν₁) :
    relabelHom R (concat Q₁ ν₁ ν₁' (a ⊗ₜ 1)) = concat Q₂ ν₂ ν₂' (relabelHom R₁ a ⊗ₜ 1) := by
  induction a using gen_induction with
  | hadd u v hu hv => rw [TensorProduct.add_tmul, map_add, map_add, hu, hv, map_add,
      TensorProduct.add_tmul, map_add]
  | hmul u v hu hv =>
    rw [← mul_one (1 : KLRAlgebra k Q₁ ν₁'), ← Algebra.TensorProduct.tmul_mul_tmul,
      concat_mul, map_mul, hu, hv, map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one]
  | hr r =>
    rw [concat_algebraMap_tmul_one, map_smul, relabelHom_oneConcat R₁ R₂ R happ, AlgHom.commutes,
      concat_algebraMap_tmul_one]
  | he s =>
    rw [relabelHom_e, ← sum_e (Q := Q₁) (ν := ν₁'), ← sum_e (Q := Q₂) (ν := ν₂'),
      TensorProduct.tmul_sum, TensorProduct.tmul_sum, map_sum, map_sum, map_sum]
    simp only [concat_e_tmul_e, relabelHom_e, happ]
    exact Fintype.sum_equiv R₂.equiv _ _ (fun _ => rfl)
  | hx b =>
    rw [concat_x_tmul_one, map_mul, relabelHom_x, relabelHom_oneConcat R₁ R₂ R happ,
      relabelHom_x, concat_x_tmul_one]
    congr 2
  | hψ l =>
    by_cases hl : l + 1 < Multiset.card ν₁
    · have hl' : l + 1 < Multiset.card ν₂ := R₁.card_eq ▸ hl
      rw [concat_ψ_tmul_one hl, map_mul, relabelHom_ψ, relabelHom_oneConcat R₁ R₂ R happ,
        relabelHom_ψ, concat_ψ_tmul_one hl']
    · have hl' : ¬ l + 1 < Multiset.card ν₂ := R₁.card_eq ▸ hl
      rw [relabelHom_ψ, ψ_eq_zero (Q := Q₂) (ν := ν₂) l (by omega),
        ψ_eq_zero (Q := Q₁) (ν := ν₁) l (by omega),
        TensorProduct.zero_tmul, TensorProduct.zero_tmul]
      simp only [map_zero]

include happ in
theorem relabelHom_concat_one_tmul (b : KLRAlgebra k Q₁ ν₁') :
    relabelHom R (concat Q₁ ν₁ ν₁' (1 ⊗ₜ b)) = concat Q₂ ν₂ ν₂' (1 ⊗ₜ relabelHom R₂ b) := by
  induction b using gen_induction with
  | hadd u v hu hv => rw [TensorProduct.tmul_add, map_add, map_add, hu, hv, map_add,
      TensorProduct.tmul_add, map_add]
  | hmul u v hu hv =>
    rw [← mul_one (1 : KLRAlgebra k Q₁ ν₁), ← Algebra.TensorProduct.tmul_mul_tmul,
      concat_mul, map_mul, hu, hv, map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one]
  | hr r =>
    rw [concat_one_tmul_algebraMap, map_smul, relabelHom_oneConcat R₁ R₂ R happ,
      AlgHom.commutes, concat_one_tmul_algebraMap]
  | he s =>
    rw [relabelHom_e, ← sum_e (Q := Q₁) (ν := ν₁), ← sum_e (Q := Q₂) (ν := ν₂),
      TensorProduct.sum_tmul, TensorProduct.sum_tmul, map_sum, map_sum, map_sum]
    simp only [concat_e_tmul_e, relabelHom_e, happ]
    exact Fintype.sum_equiv R₁.equiv _ _ (fun _ => rfl)
  | hx b =>
    rw [concat_one_tmul_x, map_mul, relabelHom_x, relabelHom_oneConcat R₁ R₂ R happ,
      relabelHom_x, concat_one_tmul_x]
    congr 2
    exact Fin.ext (by simp [R₁.card_eq])
  | hψ l =>
    by_cases hl : l + 1 < Multiset.card ν₁'
    · have hl' : l + 1 < Multiset.card ν₂' := R₂.card_eq ▸ hl
      rw [concat_one_tmul_ψ hl, map_mul, relabelHom_ψ, relabelHom_oneConcat R₁ R₂ R happ,
        relabelHom_ψ, concat_one_tmul_ψ hl', R₁.card_eq]
    · have hl' : ¬ l + 1 < Multiset.card ν₂' := R₂.card_eq ▸ hl
      rw [relabelHom_ψ, ψ_eq_zero (Q := Q₂) (ν := ν₂') l (by omega),
        ψ_eq_zero (Q := Q₁) (ν := ν₁') l (by omega),
        TensorProduct.tmul_zero, TensorProduct.tmul_zero]
      simp only [map_zero]

include happ in
/-- **Relabelling commutes with `ι_{ν,ν'}`**: `R(ι(a ⊗ b)) = ι(R₁ a ⊗ R₂ b)`. -/
theorem relabelHom_concat (t : TensorKLR Q₁ ν₁ ν₁') :
    relabelHom R (concat Q₁ ν₁ ν₁' t) =
      concat Q₂ ν₂ ν₂' (Algebra.TensorProduct.map (relabelHom R₁) (relabelHom R₂) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    have hab : a ⊗ₜ[k] b = (a ⊗ₜ[k] (1 : KLRAlgebra k Q₁ ν₁')) * (1 ⊗ₜ[k] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Algebra.TensorProduct.map_tmul, hab, concat_mul, map_mul,
      relabelHom_concat_tmul_one R₁ R₂ R happ, relabelHom_concat_one_tmul R₁ R₂ R happ,
      ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

/-! ### Relabelling the induction bimodule -/

include happ in
theorem relabelHom_mem_indBimod (m : IndBimod Q₁ ν₁ ν₁') :
    relabelHom R (m : KLRAlgebra k Q₁ (ν₁ + ν₁')) ∈ Graded.leftIdeal (oneConcat Q₂ ν₂ ν₂') := by
  rw [Graded.mem_leftIdeal, ← relabelHom_oneConcat R₁ R₂ R happ, ← map_mul,
    Graded.mem_leftIdeal.1 m.2]

/-- **`R(ν₁ + ν₁') 1_{ν₁,ν₁'} ≅ R(ν₂ + ν₂') 1_{ν₂,ν₂'}`** along a relabelling compatible with
concatenation. -/
def relabelIndBimod : IndBimod Q₁ ν₁ ν₁' ≃ₗ[k] IndBimod Q₂ ν₂ ν₂' where
  toFun m := ⟨relabelHom R m, relabelHom_mem_indBimod R₁ R₂ R happ m⟩
  invFun m := ⟨relabelHom R.symm m,
    relabelHom_mem_indBimod R₁.symm R₂.symm R.symm (symm_equiv_append R₁ R₂ R happ) m⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' c m := Subtype.ext (map_smul (relabelHom R) c (m : KLRAlgebra k Q₁ (ν₁ + ν₁')))
  left_inv m := Subtype.ext ((relabelEquiv R).symm_apply_apply (m : KLRAlgebra k Q₁ _))
  right_inv m := Subtype.ext ((relabelEquiv R).apply_symm_apply (m : KLRAlgebra k Q₂ _))

theorem coe_relabelIndBimod (m : IndBimod Q₁ ν₁ ν₁') :
    (relabelIndBimod R₁ R₂ R happ m : KLRAlgebra k Q₂ (ν₂ + ν₂')) =
      relabelHom R (m : KLRAlgebra k Q₁ (ν₁ + ν₁')) := rfl

/-- The relabelling `R(ν₁) ⊗ R(ν₁') ≃ R(ν₂) ⊗ R(ν₂')`. -/
abbrev tensorRelabel : TensorKLR Q₁ ν₁ ν₁' ≃ₐ[k] TensorKLR Q₂ ν₂ ν₂' :=
  Algebra.TensorProduct.congr (relabelEquiv R₁) (relabelEquiv R₂)

theorem tensorRelabel_tmul (a : KLRAlgebra k Q₁ ν₁) (b : KLRAlgebra k Q₁ ν₁') :
    tensorRelabel R₁ R₂ (a ⊗ₜ b) = relabelHom R₁ a ⊗ₜ relabelHom R₂ b := rfl

theorem tensorRelabel_apply (t : TensorKLR Q₁ ν₁ ν₁') :
    tensorRelabel R₁ R₂ t = Algebra.TensorProduct.map (relabelHom R₁) (relabelHom R₂) t := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add s t hs ht => rw [map_add, map_add, hs, ht]

theorem relabelIndBimod_op_smul (t : TensorKLR Q₁ ν₁ ν₁') (m : IndBimod Q₁ ν₁ ν₁') :
    relabelIndBimod R₁ R₂ R happ (op t • m) =
      op (tensorRelabel R₁ R₂ t) • relabelIndBimod R₁ R₂ R happ m := by
  apply Subtype.ext
  rw [coe_relabelIndBimod, coe_op_smul, coe_op_smul, unop_op, unop_op, map_mul,
    relabelHom_concat R₁ R₂ R happ, tensorRelabel_apply, coe_relabelIndBimod]

theorem relabelIndBimod_smul (r : KLRAlgebra k Q₁ (ν₁ + ν₁')) (m : IndBimod Q₁ ν₁ ν₁') :
    relabelIndBimod R₁ R₂ R happ (r • m) = relabelHom R r • relabelIndBimod R₁ R₂ R happ m :=
  Subtype.ext (map_mul (relabelHom R) r (m : KLRAlgebra k Q₁ (ν₁ + ν₁')))

/-! ### Relabelling induced modules -/

variable {N₁ N₂ : Type*} [AddCommGroup N₁] [Module k N₁] [Module (TensorKLR Q₁ ν₁ ν₁') N₁]
  [AddCommGroup N₂] [Module k N₂] [Module (TensorKLR Q₂ ν₂ ν₂') N₂]
  (g : N₁ ≃ₗ[k] N₂) (hg : ∀ (t : TensorKLR Q₁ ν₁ ν₁') (n : N₁),
    g (t • n) = tensorRelabel R₁ R₂ t • g n)

/-- **`Ind_{ν₁,ν₁'} N₁ ≅ Ind_{ν₂,ν₂'} N₂`** along relabellings compatible with concatenation and
a `k`-linear isomorphism `N₁ ≅ N₂` intertwining `R₁ ⊗ R₂`. -/
def relabelInd : Ind Q₁ ν₁ ν₁' N₁ ≃ₗ[k] Ind Q₂ ν₂ ν₂' N₂ :=
  BalancedTensor.changeRingEquiv (B := KLRAlgebra k Q₁ (ν₁ + ν₁'))
    (B' := KLRAlgebra k Q₂ (ν₂ + ν₂')) (tensorRelabel R₁ R₂).toRingEquiv
    (relabelIndBimod R₁ R₂ R happ) g (relabelIndBimod_op_smul R₁ R₂ R happ) hg

theorem relabelInd_tmul (m : IndBimod Q₁ ν₁ ν₁') (n : N₁) :
    relabelInd R₁ R₂ R happ g hg (BalancedTensor.tmul m n) =
      BalancedTensor.tmul (relabelIndBimod R₁ R₂ R happ m) (g n) := rfl

/-- `relabelInd` is linear along the relabelling `R(ν₁ + ν₁') ≃ R(ν₂ + ν₂')`. -/
theorem relabelInd_smul (r : KLRAlgebra k Q₁ (ν₁ + ν₁')) (y : Ind Q₁ ν₁ ν₁' N₁) :
    relabelInd R₁ R₂ R happ g hg (r • y) = relabelHom R r • relabelInd R₁ R₂ R happ g hg y :=
  BalancedTensor.changeRingEquiv_smul _ _ _ _ _ (relabelEquiv R).toRingEquiv
    (relabelIndBimod_smul R₁ R₂ R happ) r y

end KLRAlgebra

/-! ### Mapping concatenated sequences -/

namespace Seq

variable {J I : Type*} {f : J → I}

omit [DecidableEq I₁] [DecidableEq I₂] in
/-- `𝐣 ↦ f ∘ 𝐣` commutes with concatenation, read through casts of the weights. -/
theorem seqCast_map_append {ν ν' : Multiset J} {μ μ' : Multiset I} (hμ : ν.map f = μ)
    (hμ' : ν'.map f = μ') (h : (ν + ν').map f = μ + μ') (i : Seq ν) (j : Seq ν') :
    KLRAlgebra.seqCast h (Seq.map f (i.append j)) =
      (KLRAlgebra.seqCast hμ (Seq.map f i)).append (KLRAlgebra.seqCast hμ' (Seq.map f j)) := by
  have hc : Multiset.card μ = Multiset.card ν := by rw [← hμ, Multiset.card_map]
  apply Subtype.ext
  funext a
  rw [seqCast_apply]
  change f ((i.append j).1 (Fin.cast _ (Fin.cast _ a))) = _
  by_cases ha : a.val < Multiset.card μ
  · rw [append_apply_lt _ _ _ (by simpa [hc] using ha), append_apply_lt _ _ _ ha, seqCast_apply]
    rfl
  · rw [append_apply_ge _ _ _ (by simp only [Fin.val_cast]; omega),
      append_apply_ge _ _ _ (by omega), seqCast_apply]
    change _ = f (j.1 _)
    exact congrArg f (congrArg j.1 (Fin.ext (by simp [hc])))

end Seq

end Categorification.KLR
