/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlong

/-!
# Induction along a map of quotient rings

Used for B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21, to pass from the algebras `T̃^λ` to their quotients `T^λ` by violated
diagrams. Let `φ : A → B` and `φ̄ : Ā → B̄` be nonunital ring maps and `π_A : A → Ā`,
`π_B : B → B̄` surjective ring maps with `φ̄ π_A = π_B φ`. For an `Ā`-module `N`, viewed as an
`A`-module through `π_A`, induction along `φ̄` is induction along `φ` modulo the kernel of `π_B`:
`Ind_{φ̄} N ≅ Ind_φ N / ker(π_B) · Ind_φ N` (`InductionAlong.indQuotEquiv`), the map being
`z ⊗ n ↦ π_B(z) ⊗ n`.

## Main definitions

* `InductionAlong.indKerSub`: the submodule `ker(π_B) · Ind_φ N`.
* `InductionAlong.indQuotHom`: `Ind_φ N → Ind_{φ̄} N`, `z ⊗ n ↦ π_B(z) ⊗ n`.
* `InductionAlong.indQuotEquiv`: `Ind_φ N / ker(π_B) · Ind_φ N ≅ Ind_{φ̄} N`.

## Main results

* `InductionAlong.indQuotHom_smul`, `InductionAlong.indQuotEquiv_mk`.
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u w

variable {A B A' B' : Type u} [Ring A] [Ring B] [Ring A'] [Ring B']
  {φ : A →ₙ+* B} {φ' : A' →ₙ+* B'} {πA : A →+* A'} {πB : B →+* B'}
  (hA : Function.Surjective πA) (hB : Function.Surjective πB)
  (hφ : ∀ a, φ' (πA a) = πB (φ a))
  {N : Type w} [AddCommGroup N] [Module A N] [Module A' N]
  (hN : ∀ (a : A) (n : N), a • n = πA a • n)

variable (φ πB N) in
/-- The submodule `ker(π_B) · Ind_φ N`. -/
def indKerSub : Submodule B (Ind N φ) :=
  Submodule.span B {x | ∃ b : B, πB b = 0 ∧ ∃ y : Ind N φ, x = b • y}

include hφ in
theorem quotCorner_mem (z : Corner φ) : πB z.1 ∈ lIdeal (φ' 1) := by
  change πB z.1 * φ' 1 = πB z.1
  rw [← map_one πA, hφ, ← map_mul, z.2]

/-- The corner of `φ` mapped to the corner of `φ̄`. -/
def quotCorner (z : Corner φ) : Corner φ' := ⟨πB z.1, quotCorner_mem hφ z⟩

theorem quotCorner_val (z : Corner φ) : (quotCorner hφ z).1 = πB z.1 := rfl

theorem quotCorner_op_smul (a : A) (z : Corner φ) :
    quotCorner hφ (op a • z) = op (πA a) • quotCorner hφ z :=
  Subtype.ext (by
    change πB (z.1 * φ a) = πB z.1 * φ' (πA a)
    rw [map_mul, hφ])

include hN in
/-- **The map `Ind_φ N → Ind_{φ̄} N`**, `z ⊗ n ↦ π_B(z) ⊗ n`. -/
def indQuotHom : Ind N φ →+ Ind N φ' :=
  Ind.liftAdd (fun z n => Ind.tmul (quotCorner hφ z) n)
    (fun z z' n => by
      rw [show quotCorner hφ (z + z') = quotCorner hφ z + quotCorner hφ z' from
        Subtype.ext (map_add πB _ _), Ind.add_tmul])
    (fun z n n' => Ind.tmul_add _ n n')
    (fun z a n => by rw [quotCorner_op_smul, Ind.op_smul_tmul, hN])

theorem indQuotHom_tmul (z : Corner φ) (n : N) :
    indQuotHom hφ hN (Ind.tmul z n) = Ind.tmul (quotCorner hφ z) n := rfl

theorem indQuotHom_smul (b : B) (x : Ind N φ) :
    indQuotHom hφ hN (b • x) = πB b • indQuotHom hφ hN x := by
  induction x using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul z n =>
    rw [Ind.smul_tmul, indQuotHom_tmul, indQuotHom_tmul, Ind.smul_tmul]
    congr 1
    exact Subtype.ext (map_mul πB b z.1)
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

theorem indQuotHom_of_mem {x : Ind N φ} (hx : x ∈ indKerSub φ πB N) :
    indQuotHom hφ hN x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, y, rfl⟩ := hx
    rw [indQuotHom_smul, hb, zero_smul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [indQuotHom_smul, hx, smul_zero]

/-- A lift of a corner element of `φ̄` to the corner of `φ`. -/
def quotLiftCorner (z : Corner φ') : Corner φ :=
  ⟨Function.surjInv hB z.1 * φ 1, mul_mem_corner φ _ 1⟩

include hφ in
theorem map_quotLiftCorner (z : Corner φ') : πB (quotLiftCorner (φ := φ) hB z).1 = z.1 := by
  rcases z with ⟨w, hw⟩
  change πB (Function.surjInv hB w * φ 1) = w
  rw [map_mul, ← hφ, map_one, Function.surjInv_eq hB]
  exact hw

theorem quotCorner_quotLiftCorner (z : Corner φ') : quotCorner hφ (quotLiftCorner hB z) = z :=
  Subtype.ext (map_quotLiftCorner hB hφ z)

/-- Two corner elements of `φ` with the same image differ by an element of `ker(π_B) · Ind`. -/
theorem tmul_sub_mem_indKerSub {z z' : Corner φ} (h : πB z.1 = πB z'.1) (n : N) :
    Ind.tmul z n - Ind.tmul z' n ∈ indKerSub φ πB N := by
  have hz : z - z' = (z.1 - z'.1) • unitGen φ := by
    apply Subtype.ext
    change z.1 - z'.1 = (z.1 - z'.1) * φ 1
    rw [sub_mul, z.2, z'.2]
  rw [sub_eq_add_neg, ← Ind.neg_tmul, ← Ind.add_tmul, ← sub_eq_add_neg, hz, ← Ind.smul_tmul]
  exact Submodule.subset_span ⟨_, by rw [map_sub, h, sub_self], _, rfl⟩

local notation "QK" => Ind N φ ⧸ indKerSub φ πB N

theorem mk_tmul_eq {z z' : Corner φ} (h : πB z.1 = πB z'.1) (n : N) :
    (Submodule.Quotient.mk (Ind.tmul z n) : QK) = Submodule.Quotient.mk (Ind.tmul z' n) :=
  (Submodule.Quotient.eq _).2 (tmul_sub_mem_indKerSub h n)

include hA hB hφ hN in
/-- **The inverse map `Ind_{φ̄} N → Ind_φ N / ker(π_B) · Ind_φ N`**, `z ⊗ n ↦ z̃ ⊗ n` for any
lift `z̃` of `z`. -/
def indQuotInv : Ind N φ' →+ QK :=
  Ind.liftAdd (fun z n => Submodule.Quotient.mk (Ind.tmul (quotLiftCorner hB z) n))
    (fun z z' n => by
      rw [← Submodule.Quotient.mk_add, ← Ind.add_tmul]
      refine mk_tmul_eq ?_ n
      change πB (quotLiftCorner hB (z + z')).1 =
        πB ((quotLiftCorner hB z).1 + (quotLiftCorner hB z').1)
      rw [map_add, map_quotLiftCorner hB hφ, map_quotLiftCorner hB hφ, map_quotLiftCorner hB hφ]
      rfl)
    (fun z n n' => by rw [Ind.tmul_add, Submodule.Quotient.mk_add])
    (fun z a' n => by
      obtain ⟨a, rfl⟩ := hA a'
      rw [← hN, ← Ind.op_smul_tmul]
      refine mk_tmul_eq ?_ n
      change πB (quotLiftCorner hB (op (πA a) • z)).1 = πB ((quotLiftCorner hB z).1 * φ a)
      rw [map_mul, map_quotLiftCorner hB hφ, map_quotLiftCorner hB hφ, ← hφ]
      rfl)

theorem indQuotInv_tmul (z : Corner φ') (n : N) :
    indQuotInv hA hB hφ hN (Ind.tmul z n) =
      Submodule.Quotient.mk (Ind.tmul (quotLiftCorner hB z) n) := rfl

theorem indQuotInv_indQuotHom (x : Ind N φ) :
    indQuotInv hA hB hφ hN (indQuotHom hφ hN x) = Submodule.Quotient.mk x := by
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero, Submodule.Quotient.mk_zero]
  | tmul z n =>
    rw [indQuotHom_tmul, indQuotInv_tmul]
    refine mk_tmul_eq ?_ n
    rw [map_quotLiftCorner hB hφ]
    rfl
  | add s t hs ht => rw [map_add, map_add, hs, ht, Submodule.Quotient.mk_add]

include hB in
theorem indQuotHom_surjective : Function.Surjective (indQuotHom hφ hN (N := N)) := by
  intro x
  induction x using Ind.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul z n => exact ⟨Ind.tmul (quotLiftCorner hB z) n, by
      rw [indQuotHom_tmul, quotCorner_quotLiftCorner]⟩
  | add s t hs ht =>
    obtain ⟨x, rfl⟩ := hs
    obtain ⟨y, rfl⟩ := ht
    exact ⟨x + y, map_add _ x y⟩

include hA hB in
theorem indQuotHom_eq_zero_iff (x : Ind N φ) :
    indQuotHom hφ hN x = 0 ↔ x ∈ indKerSub φ πB N := by
  refine ⟨fun h => ?_, indQuotHom_of_mem hφ hN⟩
  have := indQuotInv_indQuotHom hA hB hφ hN x
  rw [h, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at this
  exact this

include hA hB in
/-- **Induction along a map of quotient rings** (used for arXiv:1309.3796v3, §7.3):
`Ind_φ N / ker(π_B) · Ind_φ N ≅ Ind_{φ̄} N`, `z ⊗ n ↦ π_B(z) ⊗ n`. It is semilinear along `π_B`
(`InductionAlong.indQuotEquiv_smul`). -/
def indQuotEquiv : QK ≃+ Ind N φ' where
  toFun q := Quotient.liftOn' q (indQuotHom hφ hN) fun x y hxy => by
    rw [← sub_eq_zero, ← map_sub, indQuotHom_eq_zero_iff hA hB hφ hN]
    exact (Submodule.quotientRel_def _).1 hxy
  invFun := indQuotInv hA hB hφ hN
  left_inv q := by
    induction q using Submodule.Quotient.induction_on with
    | H x => exact indQuotInv_indQuotHom hA hB hφ hN x
  right_inv x := by
    obtain ⟨y, rfl⟩ := indQuotHom_surjective hB hφ hN x
    dsimp only
    rw [indQuotInv_indQuotHom]
    rfl
  map_add' q q' := by
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      induction q' using Submodule.Quotient.induction_on with
      | H y => exact map_add (indQuotHom hφ hN) x y

theorem indQuotEquiv_mk (x : Ind N φ) :
    indQuotEquiv hA hB hφ hN (Submodule.Quotient.mk x) = indQuotHom hφ hN x := rfl

theorem indQuotEquiv_smul (b : B) (q : QK) :
    indQuotEquiv hA hB hφ hN (b • q) = πB b • indQuotEquiv hA hB hφ hN q := by
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, indQuotEquiv_mk, indQuotEquiv_mk, indQuotHom_smul]

end InductionAlong

end

end Categorification
