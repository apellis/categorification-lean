/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnBottomGeneration
import Categorification.WeightedKLR.RedStrands.BraidedStandardModule
import Categorification.WeightedKLR.RedStrands.LeftStandardSupport

/-!
# Strict-dominance relations of braid-column standards

Webster, arXiv:1309.3796v3, Definition 5.1 and proof of Lemma 6.12, p. 66.
The shorter cut in the generation induction preserves or raises black
counts. The projected corrections keep the original bottom. The
induction therefore applies above a fixed strict dominance threshold.
Multiplication by a generator of the ordinary higher trace lands in
the span of eligible diagrams with strictly higher bottom labels.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra
open MvPolynomial
variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)

private theorem stendhalLT_sadj_of_black_right (a b : Seq μ) (j : ℕ) (hj : j + 1 < m)
    (hb : (b.lbl ⟨j+1,hj⟩).isLeft) (hab : StendhalLT a b) :
    StendhalLT a (sadj m j • b) := by
  obtain ⟨i,hi⟩ : ∃ i, b.lbl ⟨j+1,hj⟩ = .inl i := by
    cases h : b.lbl ⟨j+1,hj⟩ with
    | inl i => exact ⟨i,rfl⟩
    | inr r => simp [h] at hb
  cases h : b.lbl ⟨j,by omega⟩ with
  | inl i' =>
    have hc (r : Fin ℓ) (q : I) := blackCount_sadj_black_black b hj h hi r q
    exact ⟨fun r q => (hc r q).symm ▸ hab.1 r q, fun hle =>
      hab.2 (fun r q => (hc r q) ▸ hle r q)⟩
  | inr r =>
    have hb' := stendhalLT_sadj hj h hi (fun d hd => lbl_eq_inr_unique hd h)
    exact ⟨fun r q => (hab.1 r q).trans (hb'.1 r q), fun hle =>
      hb'.2 (fun r q => (hle r q).trans (hab.1 r q))⟩

/-- A column element ending at a strictly higher bottom is in the span of
eligible diagrams at strictly higher bottoms. -/
theorem braidColumnBottomBlock_mul_loading_mem_higher_span
    (s a b : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    (hword : redWord b = (List.finRange ℓ).map σ) (higher : StendhalLT a b)
    (x : V) (hx : F (e s) * x = x) :
    x * F (e b) ∈ Submodule.span k (braidColumnBottomProductsWhere
      (Q := Q) (Λ := Λ) s σ ρ (StendhalLT a)) := by
  let f := braidColumnLoadingProjection (Q := Q) (Λ := Λ) s b
  obtain ⟨y,rfl⟩ := (violMk_surjective.comp ofKLR_surjective : Function.Surjective F) x
  change F (e s) * F y = F y at hx
  change F y * F (e b) ∈ _
  have hproj : f y = F y * F (e b) := by
    change F (e s * (y * e b)) = _
    rw [map_mul F,map_mul F,← mul_assoc,hx]
  rw [← hproj]
  have hy : y ∈ Submodule.span k (Set.range (KLRAlgebra.stdElt (Q := stendhalQ Q Λ) (ν := μ) ρ)) := by
    rw [KLRAlgebra.span_stdElt ρ hρ]
    exact Submodule.mem_top
  have hm := Submodule.mem_map_of_mem (f := f) hy
  rw [Submodule.map_span] at hm
  refine (Submodule.span_le.mpr ?_) hm
  rintro _ ⟨_,⟨⟨c,w,u⟩,rfl⟩,rfl⟩
  let p := monomial u (1 : k)
  change F (e s * ((ψw (ρ w) * pol p * e c) * e b)) ∈ _
  rw [gen_mul_e]
  by_cases hc : c = b
  · subst c
    rw [ite_eq_left rfl,e_mul_gen,(hρ w).2]
    by_cases hw : w⁻¹ • s = b
    · rw [ite_eq_left hw]
      have hp : StendhalLT a (w⁻¹ • s) := hw ▸ higher
      have H := braidColumnBottomBlock_pbw_mem_span_where (Q := Q) (Λ := Λ)
        s hs σ ρ hρ (StendhalLT a) (stendhalLT_sadj_of_black_right a)
        w (hw ▸ hword) hp p
      rwa [hw] at H
    · rw [ite_eq_right hw,map_zero]
      exact zero_mem _
  · rw [ite_eq_right hc,mul_zero,map_zero]
    exact zero_mem _

end Categorification.Stendhal

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra MulOpposite
variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "E" => fun κ => violMk k Q Λ ν (redProj k Q Λ ν κ)

/-- Multiplying an element of the higher trace into the column gives a
combination of eligible diagrams whose bottom strictly dominates the
source label. This is the strict-dominance standard relation. -/
theorem braidColumnBottomBlock_mul_violStandardUpper_mem_higher_span
    (s a : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    (y : V) (hy : F (e s) * y = y)
    (z : violCorner k Q Λ ν a ((List.finRange ℓ).map σ))
    (hz : z ∈ violStandardUpper (Q := Q) (Λ := Λ) a ((List.finRange ℓ).map σ)) :
    y * z.val ∈ Submodule.span k (braidColumnBottomProductsWhere
      (Q := Q) (Λ := Λ) s σ ρ (StendhalLT a)) := by
  let κ := (List.finRange ℓ).map σ
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b,x,hb,hab,rfl⟩ := hz
    change y * (F (e a) * (x * F (e b)) * E κ) ∈ _
    have he : F (e b : R) * E κ = F (e b : R) := by
      change (violMk k Q Λ ν) (ofKLR k Q Λ ν (e b)) * _ = _
      rw [← map_mul,e_mul_redProj,ite_eq_left hb]
      rfl
    rw [mul_assoc (F (e a)),mul_assoc x,he]
    have hy' : F (e s) * (y * F (e a) * x) = y * F (e a) * x := by
      rw [← mul_assoc _ (y * F (e a)),← mul_assoc _ y,hy]
    have H := braidColumnBottomBlock_mul_loading_mem_higher_span s a b hs σ ρ hρ
      hb hab (y * F (e a) * x) hy'
    simpa only [mul_assoc] using H
  | zero => change y * (0 : V) ∈ _; rw [mul_zero]; exact zero_mem _
  | add z z' _ _ h h' =>
    change y * (z.val + z'.val) ∈ _
    rw [mul_add]
    exact add_mem h h'
  | smul q z _ h =>
    rw [violCorner_smul_val, ← mul_assoc]
    have he : IsIdempotentElem (E κ) := (isIdempotentElem_redProj κ).map (violMk k Q Λ ν)
    exact braidColumnBottomProductsWhere_mul_mem_span s σ ρ (StendhalLT a)
      h (((Subsemigroup.mem_corner_iff he).1 q.unop.2).2)

end Categorification.Stendhal
