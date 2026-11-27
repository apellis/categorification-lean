/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicAffineQuotients
import Categorification.KLR.IndCast

/-!
# Induction along a relabelling of red strands

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1: to compare
iterated partial standardizations with the partial standardization with several blocks in one
step, the affine KLR algebras of a group of consecutive blocks, whose red strands are labelled
by `Fin n'`, are embedded in the affine KLR algebras of all red strands, labelled by `Fin n`,
along an increasing inclusion `f : Fin n' → Fin n`. Induction commutes with this relabelling.

## Main definitions

* `KLR.KLRAlgebra.indTransport`: induction transported along isomorphisms of KLR algebras
  intertwining the inclusions `ι_{ν,ν'}`.
* `Stendhal.stendhalRelabel`: the relabelling of the red strands of any weight along `f`.
* `Stendhal.stendhalRelabelAdd`: the relabelling of a sum of two weights, followed by the
  identification `(μ₁ + μ₂).map c = μ₁.map c + μ₂.map c`.

## Main results

* `Stendhal.stendhalRelabelAdd_concat`: the relabelling intertwines the inclusions
  `ι_{μ₁,μ₂}` and `ι_{μ₁.map c, μ₂.map c}`.
-/

noncomputable section

namespace Categorification.KLR

open scoped TensorProduct
open MulOpposite

namespace KLRAlgebra

/-! ### Transport of induced modules along isomorphisms of KLR algebras -/

section Transport

variable {I₁ I₂ : Type*} [DecidableEq I₁] [DecidableEq I₂] {k : Type*} [CommRing k]
  {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
  {ν₁ ν₁' : Multiset I₁} {ν₂ ν₂' : Multiset I₂}
  (σ : KLRAlgebra k Q₁ (ν₁ + ν₁') ≃ₐ[k] KLRAlgebra k Q₂ (ν₂ + ν₂'))
  (σ₀ : TensorKLR Q₁ ν₁ ν₁' ≃ₐ[k] TensorKLR Q₂ ν₂ ν₂')
  (hc : ∀ t, σ (concat Q₁ ν₁ ν₁' t) = concat Q₂ ν₂ ν₂' (σ₀ t))

include hc in
theorem transport_oneConcat : σ (oneConcat Q₁ ν₁ ν₁') = oneConcat Q₂ ν₂ ν₂' := by
  rw [← concat_one, hc, map_one, concat_one]

/-- The isomorphism of induction bimodules. -/
def bimodTransport : IndBimod Q₁ ν₁ ν₁' ≃ₗ[k] IndBimod Q₂ ν₂ ν₂' where
  toFun m := ⟨σ (m : KLRAlgebra k Q₁ (ν₁ + ν₁')), by
    change σ m * oneConcat Q₂ ν₂ ν₂' = σ m
    rw [← transport_oneConcat σ σ₀ hc, ← map_mul, m.2]⟩
  invFun m := ⟨σ.symm (m : KLRAlgebra k Q₂ (ν₂ + ν₂')), by
    change σ.symm m * oneConcat Q₁ ν₁ ν₁' = σ.symm m
    rw [show oneConcat Q₁ ν₁ ν₁' = σ.symm (oneConcat Q₂ ν₂ ν₂') from
      (σ.symm_apply_eq.2 (transport_oneConcat σ σ₀ hc).symm).symm, ← map_mul, m.2]⟩
  map_add' m m' := Subtype.ext (map_add σ (m : KLRAlgebra k Q₁ (ν₁ + ν₁')) m')
  map_smul' c m := Subtype.ext (map_smul σ c (m : KLRAlgebra k Q₁ (ν₁ + ν₁')))
  left_inv m := Subtype.ext (σ.symm_apply_apply _)
  right_inv m := Subtype.ext (σ.apply_symm_apply _)

theorem coe_bimodTransport (m : IndBimod Q₁ ν₁ ν₁') :
    ((bimodTransport σ σ₀ hc m : IndBimod Q₂ ν₂ ν₂') : KLRAlgebra k Q₂ (ν₂ + ν₂')) = σ m := rfl

theorem bimodTransport_op_smul (t : TensorKLR Q₁ ν₁ ν₁') (m : IndBimod Q₁ ν₁ ν₁') :
    bimodTransport σ σ₀ hc (op t • m) = op (σ₀ t) • bimodTransport σ σ₀ hc m :=
  Subtype.ext (by
    rw [coe_bimodTransport, coe_op_smul, coe_op_smul, unop_op, unop_op, map_mul, hc]; rfl)

theorem bimodTransport_smul (a : KLRAlgebra k Q₁ (ν₁ + ν₁')) (m : IndBimod Q₁ ν₁ ν₁') :
    bimodTransport σ σ₀ hc (a • m) = σ a • bimodTransport σ σ₀ hc m :=
  Subtype.ext (map_mul σ a m)

variable {N₁ N₂ : Type*} [AddCommGroup N₁] [Module k N₁] [Module (TensorKLR Q₁ ν₁ ν₁') N₁]
  [AddCommGroup N₂] [Module k N₂] [Module (TensorKLR Q₂ ν₂ ν₂') N₂]
  (g : N₁ ≃ₗ[k] N₂) (hg : ∀ (t : TensorKLR Q₁ ν₁ ν₁') (n : N₁), g (t • n) = σ₀ t • g n)

/-- **Transport of induced modules along isomorphisms of KLR algebras** intertwining the
inclusions `ι`: `Ind_{ν₁,ν₁'} N₁ ≃ Ind_{ν₂,ν₂'} N₂`, semilinear along `σ`. -/
def indTransport : Ind Q₁ ν₁ ν₁' N₁ ≃ₗ[k] Ind Q₂ ν₂ ν₂' N₂ :=
  BalancedTensor.changeRingEquiv σ₀.toRingEquiv (bimodTransport σ σ₀ hc) g
    (bimodTransport_op_smul σ σ₀ hc) hg

theorem indTransport_tmul (m : IndBimod Q₁ ν₁ ν₁') (n : N₁) :
    indTransport σ σ₀ hc g hg (BalancedTensor.tmul m n) =
      BalancedTensor.tmul (bimodTransport σ σ₀ hc m) (g n) := rfl

/-- `indTransport` is semilinear along `σ`. -/
theorem indTransport_smul (a : KLRAlgebra k Q₁ (ν₁ + ν₁')) (y : Ind Q₁ ν₁ ν₁' N₁) :
    indTransport σ σ₀ hc g hg (a • y) = σ a • indTransport σ σ₀ hc g hg y :=
  BalancedTensor.changeRingEquiv_smul _ _ _ _ _ σ.toRingEquiv (bimodTransport_smul σ σ₀ hc) a y

end Transport

end KLRAlgebra

end Categorification.KLR

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct

/-! ### Relabelling red strands along an inclusion -/

variable {I k : Type*} [DecidableEq I] [CommRing k] {n n' : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin n → I →₀ ℕ)
  (f : Fin n' → Fin n) (hf : Function.Injective f)

local notation "c" => Sum.map (id : I → I) f
local notation "S" => stendhalQ Q Λ
local notation "S'" => stendhalQ Q (Λ ∘ f)

omit [DecidableEq I] in
include hf in
theorem sumMap_injective : Function.Injective c :=
  Sum.map_injective.mpr ⟨Function.injective_id, hf⟩

include hf in
/-- **Relabelling the red strands of any weight along an inclusion `f`**, preserving the black
labels and the Stendhal parameters. -/
def stendhalRelabel (μ : Multiset (I ⊕ Fin n')) : SeqRelabel k S' S μ (μ.map c) :=
  let h := SeqRelabel.ofInjective (sumMap_injective f hf) S μ
  { h with
    Q_eq := fun s a b hab => by
      rw [h.Q_eq _ _ _ hab]
      cases s.lbl a <;> cases s.lbl b <;> rfl }

omit [DecidableEq I] in
theorem stendhalRelabel_equiv (μ : Multiset (I ⊕ Fin n')) (s : Seq μ) :
    (stendhalRelabel Q Λ f hf μ).equiv s = Seq.map c s := rfl

/-- Relabelling commutes with the identifications of equal weights. -/
theorem stendhalRelabel_castKLR {μ μ' : Multiset (I ⊕ Fin n')} (h : μ = μ')
    (u : KLRAlgebra k S' μ) :
    relabelEquiv (stendhalRelabel Q Λ f hf μ') (castKLR S' h u) =
      castKLR S (congrArg (Multiset.map c) h) (relabelEquiv (stendhalRelabel Q Λ f hf μ) u) := by
  subst h; rfl

omit [DecidableEq I] in
/-- Relabelling a concatenation of sequences. -/
theorem seq_map_append {J : Type*} (g : J → I ⊕ Fin n) {μ₁ μ₂ : Multiset J} (i : Seq μ₁)
    (j : Seq μ₂) : Seq.cast (Multiset.map_add g μ₁ μ₂) (Seq.map g (i.append j)) =
      (Seq.map g i).append (Seq.map g j) := by
  apply Subtype.ext
  funext p
  change g ((i.append j).1 (Fin.cast _ (Fin.cast _ p))) = ((Seq.map g i).append (Seq.map g j)).1 p
  by_cases hp : p.val < Multiset.card μ₁
  · rw [Seq.append_apply_lt _ _ _ (by simpa using hp),
      Seq.append_apply_lt _ _ _ (by simpa using hp)]
    rfl
  · rw [Seq.append_apply_ge _ _ _ (by simp; omega),
      Seq.append_apply_ge _ _ _ (by simp; omega)]
    change _ = g (j.1 _)
    exact congrArg g (Seq.apply_congr j (by simp))

/-- **The relabelling of a sum of two weights**, `R'(μ₁ + μ₂) ≃ R(μ₁.map c + μ₂.map c)`. -/
def stendhalRelabelAdd (μ₁ μ₂ : Multiset (I ⊕ Fin n')) :
    KLRAlgebra k S' (μ₁ + μ₂) ≃ₐ[k] KLRAlgebra k S (μ₁.map c + μ₂.map c) :=
  (relabelEquiv (stendhalRelabel Q Λ f hf (μ₁ + μ₂))).trans
    (castKLR S (Multiset.map_add c μ₁ μ₂))

/-- The relabellings of the two weights, on the tensor product. -/
def stendhalRelabelTensor (μ₁ μ₂ : Multiset (I ⊕ Fin n')) :
    TensorKLR S' μ₁ μ₂ ≃ₐ[k] TensorKLR S (μ₁.map c) (μ₂.map c) :=
  Algebra.TensorProduct.congr (relabelEquiv (stendhalRelabel Q Λ f hf μ₁))
    (relabelEquiv (stendhalRelabel Q Λ f hf μ₂))

variable {μ₁ μ₂ : Multiset (I ⊕ Fin n')}

theorem stendhalRelabelAdd_e (s : Seq (μ₁ + μ₂)) :
    stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (e s) =
      e (Seq.cast (Multiset.map_add c μ₁ μ₂) (Seq.map c s)) := by
  change castKLR S _ (relabelHom _ (e s)) = _
  rw [relabelHom_e, castKLR_e]
  rfl

theorem stendhalRelabelAdd_x (a : Fin (Multiset.card (μ₁ + μ₂))) :
    stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (x a) = x ⟨a.val, by
      have := a.2; simp only [Multiset.card_add, Multiset.card_map] at this ⊢; omega⟩ := by
  change castKLR S _ (relabelHom _ (x a)) = _
  rw [relabelHom_x, castKLR_x]
  rfl

theorem stendhalRelabelAdd_ψ (j : ℕ) : stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (ψ j) = ψ j := by
  change castKLR S _ (relabelHom _ (ψ j)) = _
  rw [relabelHom_ψ, castKLR_ψ]

theorem stendhalRelabelAdd_oneConcat :
    stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (oneConcat S' μ₁ μ₂) = oneConcat S (μ₁.map c) (μ₂.map c) := by
  simp only [oneConcat_eq', map_sum, stendhalRelabelAdd_e, seq_map_append]
  exact Fintype.sum_equiv (Seq.mapEquiv (sumMap_injective f hf) μ₁) _ _ fun i =>
    Fintype.sum_equiv (Seq.mapEquiv (sumMap_injective f hf) μ₂) _ _ fun j => rfl

private def leftSlot (Q₀ : I ⊕ Fin n → I ⊕ Fin n → MvPolynomial (Fin 2) k)
    (ν ν' : Multiset (I ⊕ Fin n)) : KLRAlgebra k Q₀ ν →ₗ[k] KLRAlgebra k Q₀ (ν + ν') :=
  concat Q₀ ν ν' ∘ₗ (TensorProduct.mk k _ _).flip 1

private def rightSlot (Q₀ : I ⊕ Fin n → I ⊕ Fin n → MvPolynomial (Fin 2) k)
    (ν ν' : Multiset (I ⊕ Fin n)) : KLRAlgebra k Q₀ ν' →ₗ[k] KLRAlgebra k Q₀ (ν + ν') :=
  concat Q₀ ν ν' ∘ₗ TensorProduct.mk k _ _ 1

private def leftSlot' (ν ν' : Multiset (I ⊕ Fin n')) :
    KLRAlgebra k S' ν →ₗ[k] KLRAlgebra k S' (ν + ν') :=
  concat S' ν ν' ∘ₗ (TensorProduct.mk k _ _).flip 1

private def rightSlot' (ν ν' : Multiset (I ⊕ Fin n')) :
    KLRAlgebra k S' ν' →ₗ[k] KLRAlgebra k S' (ν + ν') :=
  concat S' ν ν' ∘ₗ TensorProduct.mk k _ _ 1

private theorem left_slot_eq :
    (stendhalRelabelAdd Q Λ f hf μ₁ μ₂).toLinearMap ∘ₗ leftSlot' Q Λ f μ₁ μ₂ =
      leftSlot S (μ₁.map c) (μ₂.map c) ∘ₗ
        (relabelEquiv (stendhalRelabel Q Λ f hf μ₁)).toLinearMap := by
  refine ext_of_mul _ _ (fun u u' => ?_) (fun u u' => ?_) ?_ (fun i => ?_) (fun a => ?_)
    (fun j hj => ?_)
  · change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ ((u * u') ⊗ₜ 1)) =
      stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (u ⊗ₜ 1)) *
        stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (u' ⊗ₜ 1))
    rw [← map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  · change concat S _ _ (relabelEquiv _ (u * u') ⊗ₜ 1) =
      concat S _ _ (relabelEquiv _ u ⊗ₜ 1) * concat S _ _ (relabelEquiv _ u' ⊗ₜ 1)
    rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_mul]
  · change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (1 ⊗ₜ 1)) =
      concat S _ _ (relabelEquiv _ 1 ⊗ₜ 1)
    rw [map_one, concat_one_tmul_one, concat_one_tmul_one, stendhalRelabelAdd_oneConcat]
  · change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (e i ⊗ₜ 1)) =
      concat S _ _ (relabelEquiv _ (e i) ⊗ₜ 1)
    rw [relabelEquiv_apply, relabelHom_e, concat_e_tmul_one, concat_e_tmul_one, map_sum]
    simp only [stendhalRelabelAdd_e, seq_map_append]
    exact Fintype.sum_equiv (Seq.mapEquiv (sumMap_injective f hf) μ₂) _ _ fun j => rfl
  · change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (x a ⊗ₜ 1)) =
      concat S _ _ (relabelEquiv _ (x a) ⊗ₜ 1)
    rw [relabelEquiv_apply, relabelHom_x, concat_x_tmul_one, concat_x_tmul_one, map_mul,
      stendhalRelabelAdd_oneConcat, stendhalRelabelAdd_x]
    rfl
  · have hj' : j + 1 < Multiset.card (μ₁.map c) := by simpa using hj
    change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (ψ j ⊗ₜ 1)) =
      concat S _ _ (relabelEquiv _ (ψ j) ⊗ₜ 1)
    rw [relabelEquiv_apply, relabelHom_ψ, concat_ψ_tmul_one hj, concat_ψ_tmul_one hj', map_mul,
      stendhalRelabelAdd_oneConcat, stendhalRelabelAdd_ψ]

private theorem right_slot_eq :
    (stendhalRelabelAdd Q Λ f hf μ₁ μ₂).toLinearMap ∘ₗ rightSlot' Q Λ f μ₁ μ₂ =
      rightSlot S (μ₁.map c) (μ₂.map c) ∘ₗ
        (relabelEquiv (stendhalRelabel Q Λ f hf μ₂)).toLinearMap := by
  refine ext_of_mul _ _ (fun u u' => ?_) (fun u u' => ?_) ?_ (fun i => ?_) (fun a => ?_)
    (fun j hj => ?_)
  · change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (1 ⊗ₜ (u * u'))) =
      stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (1 ⊗ₜ u)) *
        stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (1 ⊗ₜ u'))
    rw [← map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  · change concat S _ _ (1 ⊗ₜ relabelEquiv _ (u * u')) =
      concat S _ _ (1 ⊗ₜ relabelEquiv _ u) * concat S _ _ (1 ⊗ₜ relabelEquiv _ u')
    rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_mul]
  · change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (1 ⊗ₜ 1)) =
      concat S _ _ (1 ⊗ₜ relabelEquiv _ 1)
    rw [map_one, concat_one_tmul_one, concat_one_tmul_one, stendhalRelabelAdd_oneConcat]
  · change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (1 ⊗ₜ e i)) =
      concat S _ _ (1 ⊗ₜ relabelEquiv _ (e i))
    rw [relabelEquiv_apply, relabelHom_e, concat_one_tmul_e, concat_one_tmul_e, map_sum]
    simp only [stendhalRelabelAdd_e, seq_map_append]
    exact Fintype.sum_equiv (Seq.mapEquiv (sumMap_injective f hf) μ₁) _ _ fun j => rfl
  · change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (1 ⊗ₜ x a)) =
      concat S _ _ (1 ⊗ₜ relabelEquiv _ (x a))
    rw [relabelEquiv_apply, relabelHom_x, concat_one_tmul_x, concat_one_tmul_x, map_mul,
      stendhalRelabelAdd_oneConcat, stendhalRelabelAdd_x]
    congr 2
    apply Fin.ext
    simp
  · have hj' : j + 1 < Multiset.card (μ₂.map c) := by simpa using hj
    change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (1 ⊗ₜ ψ j)) =
      concat S _ _ (1 ⊗ₜ relabelEquiv _ (ψ j))
    rw [relabelEquiv_apply, relabelHom_ψ, concat_one_tmul_ψ hj, concat_one_tmul_ψ hj', map_mul,
      stendhalRelabelAdd_oneConcat, stendhalRelabelAdd_ψ, Multiset.card_map]

/-- **Relabelling intertwines the inclusions `ι`.** -/
theorem stendhalRelabelAdd_concat (t : TensorKLR S' μ₁ μ₂) :
    stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ t) =
      concat S (μ₁.map c) (μ₂.map c) (stendhalRelabelTensor Q Λ f hf μ₁ μ₂ t) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]
  | tmul u v =>
    have hl := LinearMap.congr_fun (left_slot_eq Q Λ f hf (μ₁ := μ₁) (μ₂ := μ₂)) u
    have hr := LinearMap.congr_fun (right_slot_eq Q Λ f hf (μ₁ := μ₁) (μ₂ := μ₂)) v
    change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (u ⊗ₜ 1)) =
      concat S _ _ (relabelEquiv _ u ⊗ₜ 1) at hl
    change stendhalRelabelAdd Q Λ f hf μ₁ μ₂ (concat S' μ₁ μ₂ (1 ⊗ₜ v)) =
      concat S _ _ (1 ⊗ₜ relabelEquiv _ v) at hr
    rw [show u ⊗ₜ[k] v = (u ⊗ₜ[k] (1 : KLRAlgebra k S' μ₂)) * (1 ⊗ₜ v) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], concat_mul, map_mul, hl, hr,
      ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl

end Categorification.Stendhal
