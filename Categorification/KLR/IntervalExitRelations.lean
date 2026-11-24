/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IntervalSpectatorDots

/-!
# Reflection of affine interval relations

For Webster, arXiv:1309.3796v2, §6.1, after (6.21), an affine exit relation
with fixed exterior loading idempotents can be read in the smaller KLR algebra
at each exterior permutation. Local inputs may have arbitrary dots and repeated
colours.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open TypeA Equiv

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
    (hQ : KLRSymm Q) {α β γ : Multiset I}

local notation "μ₀" => α+(β+γ)
local notation "m" => Multiset.card μ₀
local notation "ι" => intervalConcat (β := β) Q
local notation "M" => intervalPBWSpan Q (ν := μ₀) (p := α.card) (n := β.card)

include hQ in
theorem intervalConcat_mem_intervalPBWSpan (l : Seq α) (r : Seq γ) (x : KLRAlgebra k Q β) :
    ι l r x ∈ M := by
  have h : LinearMap.range (ι l r) ≤ M := by
    rw [range_intervalConcat_eq_span Q hQ l r (TypeA.canWord _) (fun v => ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩),
      Submodule.span_le]
    rintro _ ⟨⟨s,v,d⟩,rfl⟩
    exact intervalPBWSpan_polynomial Q (l.append (s.append r)) v _
  exact h ⟨x,rfl⟩

include hQ in
/-- Finite affine right-exit relations on fixed spectator strands reflect exactly
the same relations in the smaller KLR algebra at each sorted exterior. -/
theorem intervalConcat_exit_relation_iff {η : Type*} (l : Seq α) (r : Seq γ)
    (T : Finset (Perm (Fin m))) (hT : ∀ u ∈ T, StrictMono (fun i : Fin β.card =>
      u ⟨α.card+i.val,by simp only [Multiset.card_add]; omega⟩)) (L : Finset η)
    (z : Perm (Fin m) → η → KLRAlgebra k Q β) (leg : η → KLRAlgebra k Q β) :
    (∑ a ∈ L, (∑ u ∈ T, ψw (TypeA.canWord m u) * ι l r (z u a)) * ι l r (leg a)) = 0 ↔
      ∀ u ∈ T, ∑ a ∈ L, z u a * leg a = 0 := by
  classical
  let z' (u : Perm (Fin m)) (a : η) : M := ⟨ι l r (z u a), intervalConcat_mem_intervalPBWSpan Q hQ l r _⟩
  have hw : α.card+(β.card+γ.card)=m := by simp only [Multiset.card_add]
  have mem (u : Perm (Fin m)) (a : η) : (z' u a).val * ι l r (leg a) ∈ M := by
    change ι l r (z u a) * ι l r (leg a) ∈ M
    rw [← intervalConcat_mul]
    exact intervalConcat_mem_intervalPBWSpan Q hQ l r _
  have formula := intervalPBW_exit_relation_iff Q hw hQ T hT L z'
    (fun a => ι l r (leg a)) (fun u _ a _ => mem u a)
  rw [formula]
  apply forall₂_congr
  intro u _
  change (∑ a ∈ L, ι l r (z u a) * ι l r (leg a)) = 0 ↔ _
  simp_rw [← intervalConcat_mul]
  rw [← map_sum]
  exact (intervalConcat_injective Q hQ l r).eq_iff' (map_zero _)

end Categorification.KLR.KLRAlgebra

namespace Categorification.KLR.KLRAlgebra
open TypeA Equiv

variable {I k : Type} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
    (hQ : KLRSymm Q) {α β γ : Multiset I}

local notation "μ" => α+(β+γ)
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k Q μ
local notation "ι" => intervalConcat (β := β) Q

/-- A family of embedded interval exits has zero total product precisely when its
products with the interval coefficients vanish at every exterior. -/
theorem intervalConcat_exit_kernel_iff {η : Type*} (L : Finset η)
    (l : η → Seq α) (r : η → Seq γ) (x : η → R) (leg : η → KLRAlgebra k Q β) :
    let h : α.card+(β.card+γ.card)=m := by simp only [Multiset.card_add]
    (∑ a ∈ L, x a * ι (l a) (r a) (leg a)) = 0 ↔ ∀ u : Perm (Fin m),
      ∑ a ∈ L, (intervalPBWCoefficient Q h hQ u (x a)).val * ι (l a) (r a) (leg a) = 0 := by
  intro h
  exact intervalPBWCoefficient_exit_kernel_iff Q h hQ L x (fun a => ι (l a) (r a) (leg a))
    (fun a _ u => intervalPBWSpan_mul_intervalConcat Q hQ (l a) (r a)
      (intervalPBWCoefficient Q h hQ u (x a)) (leg a))

end Categorification.KLR.KLRAlgebra
