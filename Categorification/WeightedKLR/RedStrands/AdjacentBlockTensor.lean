/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBlockSlide

/-!
# The fixed-top ordinary tensor and the adjacent-block relations

Webster, arXiv:1309.3796v2, proof of Lemma 6.8, ordinary tensor step used in Proposition 6.9.
Fix a top loading `t` and write `p,e,f` for its idempotent, its red order and the transposed
red order, respectively, in the quotient `V` by violated diagrams. In the ordinary tensor
`pVe ⊗_{eVe} eVf`, impose the higher-block relations in the first factor. The kernel of
multiplication followed by quotienting by higher block loadings of the *opposite* order
is exactly the subspace of relations just imposed (`ker_blockTensorMult`).

This computes the relations for a fixed projective generator. It does not construct the
action of the external tensor product of the block algebras, identify the two functors,
or assert higher Tor vanishing.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR

section Corners
variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A] {p e f : A}
  (hp : IsIdempotentElem p) (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
local notation "CT" => CornerTensor k A p e f

include he in
private theorem tmul_middle (x y : A) :
    (CornerTensor.tmul x (e * y) : CT) = CornerTensor.tmul x y := by
  rw [CornerTensor.tmul_corner x (e * y), CornerTensor.tmul_corner x y]
  simp only [← mul_assoc, he.eq]

/-- Cutting off the loading idempotent splits multiplication on a projective tensor. -/
private theorem tmul_mult_loading (hpe : e * p = p) (z : CT) :
    CornerTensor.tmul 1 (CornerTensor.mult hp he hf z) = z := by
  induction z using CornerTensor.induction_on with
  | add x y hx hy => rw [map_add, CornerTensor.tmul_add_right, hx, hy]
  | tmul x y =>
    let c := p * x * e
    have hc : e * c * e = c := by simp only [c, ← mul_assoc, hpe, CornerTensor.mul_idem he]
    have hd : p * x * e * y * f = c * (e * y * f) := by
      simp only [c, ← mul_assoc, CornerTensor.mul_idem he]
    rw [CornerTensor.mult_tmul, hd, ← CornerTensor.tmul_balance_of hc, one_mul]
    exact (CornerTensor.tmul_corner x y).symm

end Corners

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "pₛ" => fun s : Seq μ => π (KLRAlgebra.e s)
local notation "P" => fun κ => violMk k Q Λ ν (redProj k Q Λ ν κ)

private theorem idem_loading (t : Seq μ) : IsIdempotentElem (pₛ t) :=
  (show IsIdempotentElem (KLRAlgebra.e t : KLRAlgebra k (stendhalQ Q Λ) μ) from
    KLRAlgebra.e_mul_self _).map π

private theorem idem_order (κ : List (Fin ℓ)) : IsIdempotentElem (P κ) :=
  (isIdempotentElem_redProj κ).map _

private theorem order_loading {t : Seq μ} {κ : List (Fin ℓ)} (ht : redWord t = κ) :
    P κ * pₛ t = pₛ t := by
  change π (redIdem k Q Λ κ) * π (KLRAlgebra.e t) = π (KLRAlgebra.e t)
  rw [← map_mul, redIdem_mul_e, ite_eq_left ht]

private theorem loading_order {t : Seq μ} {κ : List (Fin ℓ)} (ht : redWord t = κ) :
    pₛ t * P κ = pₛ t := by
  change π (KLRAlgebra.e t) * π (redIdem k Q Λ κ) = π (KLRAlgebra.e t)
  rw [← map_mul, e_mul_redIdem, ite_eq_left ht]

variable (L M : List (Fin ℓ)) (a b : Fin ℓ) (t : KLR.Seq (stendhalWeight ℓ ν))
local notation "κ₁" => L ++ b :: a :: M
local notation "κ₀" => L ++ a :: b :: M
local notation "J" => blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t)
local notation "T" => CornerTensor k V (pₛ t) (P κ₁) (P κ₀)

variable (k Q Λ) in
/-- The relations obtained by tensoring the higher-block submodule of `pVe` with `eVf`:
classes `x ⊗ y` with `x` factoring through a higher loading in the top red order. -/
def blockTensorRelations : Submodule k T :=
  Submodule.span k {z | ∃ x y : V, x ∈ J κ₁ ∧ z = CornerTensor.tmul x y}

variable (k Q Λ) in
/-- Stack the two halves of the diagram, then impose the higher-block relations in the
bottom order. The braiding bimodule is the right factor of the ordinary corner tensor. -/
def blockTensorMult : T →ₗ[k] (J κ₀).ringCon.Quotient :=
  ((J κ₀).ringCon.mkₐ k).toLinearMap ∘ₗ
    CornerTensor.mult (idem_loading t) (idem_order κ₁) (idem_order κ₀)

private theorem tmul_one_mem_relations {z : V} (hz : z ∈ J κ₁) :
    CornerTensor.tmul 1 z ∈ blockTensorRelations k Q Λ L M a b t := by
  rw [blockUpperIdeal, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨_, ⟨c, -, _, ⟨s, hs, hlt, rfl⟩, rfl⟩, d, -, rfl⟩ := hz
    let x := P κ₁ * c * pₛ s
    have hx : P κ₁ * x * P κ₁ = x := by
      simp only [x, ← mul_assoc, (idem_order κ₁).eq]
      rw [mul_assoc _ (pₛ s), loading_order hs]
    have hxu : x ∈ J κ₁ := TwoSidedIdeal.mul_mem_left _ _ _
      (TwoSidedIdeal.subset_span ⟨s, hs, hlt, rfl⟩)
    apply Submodule.subset_span
    refine ⟨x, d, hxu, ?_⟩
    rw [← tmul_middle (idem_order κ₁) 1, ← mul_assoc, ← mul_assoc]
    exact (CornerTensor.tmul_balance_of hx 1 d).symm.trans (by rw [one_mul])
  | zero => rw [CornerTensor.tmul_zero_right]; exact zero_mem _
  | add _ _ _ _ hx hy => rw [CornerTensor.tmul_add_right]; exact add_mem hx hy
  | neg z _ hz =>
    rw [show -z = 0 - z by simp, CornerTensor.tmul_sub_right, CornerTensor.tmul_zero_right,
      zero_sub]
    exact neg_mem hz

/-- **The kernel in the fixed-top ordinary comparison** (Webster, arXiv:1309.3796v2,
proof of Lemma 6.8). The bottom-order partial standard relations kill exactly the image in
`P_t ⊗ B_j` of the top-order higher submodule tensored with `B_j`. -/
theorem ker_blockTensorMult (ht : redWord t = κ₁) :
    LinearMap.ker (blockTensorMult k Q Λ L M a b t) = blockTensorRelations k Q Λ L M a b t := by
  let mult := CornerTensor.mult (k := k) (idem_loading (Q := Q) (Λ := Λ) t)
    (idem_order κ₁) (idem_order κ₀)
  have hmem (z : T) : z ∈ LinearMap.ker (blockTensorMult k Q Λ L M a b t) ↔ mult z ∈ J κ₁ := by
    change (J κ₀).ringCon.mk' (mult z) = 0 ↔ _
    rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
    apply mem_blockUpperIdeal_iff
    · induction z using CornerTensor.induction_on with
      | tmul x y => simp only [mult, CornerTensor.mult_tmul, ← mul_assoc, order_loading ht]
      | add x y hx hy => rw [map_add, mul_add, hx, hy]
    · induction z using CornerTensor.induction_on with
      | tmul x y => simp only [mult, CornerTensor.mult_tmul, CornerTensor.mul_idem (idem_order κ₀)]
      | add x y hx hy => rw [map_add, add_mul, hx, hy]
  apply le_antisymm
  · intro z hz
    rw [← tmul_mult_loading (idem_loading t) (idem_order κ₁) (idem_order κ₀) (order_loading ht) z]
    exact tmul_one_mem_relations L M a b t ((hmem z).1 hz)
  · apply Submodule.span_le.2
    rintro _ ⟨x, y, hx, rfl⟩
    apply (hmem _).2
    rw [show mult (CornerTensor.tmul x y) = pₛ t * x * P κ₁ * y * P κ₀ from
      CornerTensor.mult_tmul _ _ _ _ _]
    iterate 3 apply TwoSidedIdeal.mul_mem_right
    exact TwoSidedIdeal.mul_mem_left _ _ _ hx

variable (k Q Λ) in
/-- The fixed-top corner `p (V / J_bottom) f`, with the block root of `t` as threshold. -/
def blockQuotientCorner : Submodule k (J κ₀).ringCon.Quotient :=
  LinearMap.range (((J κ₀).ringCon.mkₐ k).toLinearMap ∘ₗ LinearMap.mulLeft k (pₛ t) ∘ₗ
    LinearMap.mulRight k (P κ₀))

variable (k Q Λ) in
/-- **Fixed-top ordinary tensor comparison** (Webster, arXiv:1309.3796v2, §6.1, proof of
Lemma 6.8). Multiplication identifies the ordinary projective tensor modulo the top-order
block relations with the corner of diagrams modulo the bottom-order higher cuts. -/
def blockTensorEquiv (ht : redWord t = κ₁) :
    (T ⧸ blockTensorRelations k Q Λ L M a b t) ≃ₗ[k] blockQuotientCorner k Q Λ L M a b t := by
  let F := blockTensorMult k Q Λ L M a b t
  refine ((Submodule.quotEquivOfEq _ _ (ker_blockTensorMult L M a b t ht).symm).trans
    F.quotKerEquivRange).trans (LinearEquiv.ofEq _ _ ?_)
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    let h := idem_loading (Q := Q) (Λ := Λ) t
    let y := CornerTensor.mult h (idem_order κ₁) (idem_order κ₀) z
    refine ⟨y, ?_⟩
    change (J κ₀).ringCon.mkₐ k (pₛ t * (y * P κ₀)) = (J κ₀).ringCon.mkₐ k y
    rw [← mul_assoc, CornerTensor.mult_corner h (idem_order κ₁) (idem_order κ₀) z]
  · rintro _ ⟨y, rfl⟩
    refine ⟨CornerTensor.tmul 1 y, ?_⟩
    change (J κ₀).ringCon.mkₐ k (CornerTensor.mult _ _ _ _) =
      (J κ₀).ringCon.mkₐ k (pₛ t * (y * P κ₀))
    rw [CornerTensor.mult_tmul, mul_one, loading_order ht, mul_assoc]

/-- On elementary tensors the comparison is stacking, with the three boundary idempotents;
thus a chosen crossing diagram can be inserted in the right factor (Webster, §6.1,
Proposition 6.9, Figure 5). -/
theorem blockTensorEquiv_tmul (ht : redWord t = κ₁) (x y : V) :
    (blockTensorEquiv k Q Λ L M a b t ht
      ((blockTensorRelations k Q Λ L M a b t).mkQ (CornerTensor.tmul x y))).1 =
      (J κ₀).ringCon.mkₐ k (pₛ t * x * P κ₁ * y * P κ₀) := by
  change (J κ₀).ringCon.mkₐ k (CornerTensor.mult _ _ _ (CornerTensor.tmul x y)) = _
  rw [CornerTensor.mult_tmul]

end Categorification.Stendhal.BraidedStendhalAlgebra
