/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingSeam
import Categorification.WeightedKLR.RedStrands.OrderProjection

/-!
# Inserting the uncrossed order at an interior height

Webster, arXiv:1309.3796v2, §6.1, Proposition 6.4 and ordinary comparison of Lemma 6.8.
In the diagonal red corner, forgetting all red crossings is faithful. Thus projection to
the same red order at both ends allows insertion of that order between *arbitrary* factors.
At a juxtaposed boundary the global order cuts out exactly the tensor of the local orders.
-/
noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA BraidedStendhalAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) {ν : Multiset I}
local notation "Braid" => BraidedStendhalAlgebra k Q Λ ν
local notation "P" => redProj k Q Λ ν

private theorem inIdentityOrder (hQ : KLRSymm Q) (x y : Braid) :
    let p := P (List.finRange ℓ)
    p * (x*y) * p = p * (x*p*y) * p := by
  intro p
  let ρ := canWord (stendhalWeight ℓ ν).card
  have hw : IsReducedChoice ρ := fun w => ⟨isReduced_canWord _ w,wordProd_canWord _ w⟩
  apply congrArg Subtype.val (α := (isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.finRange ℓ)).Corner)
    (a₁ := cornerMk (x*y)) (a₂ := cornerMk (x*p*y))
  apply (identityCornerHom_bijective hw hQ).1; apply Subtype.ext
  change toAllOrders k Q Λ ν (p*(x*y)*p) = toAllOrders k Q Λ ν (p*(x*p*y)*p)
  simp only [map_mul, p, redProj, toAllOrders_redIdem]
  let e := StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
  have hc := (redOrderedIdem_commute Q Λ ν (toAllOrders k Q Λ ν x)).eq
  have he : e * e = e := StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem.eq
  have fix : e * toAllOrders k Q Λ ν x * e = e * toAllOrders k Q Λ ν x := by
    rw [mul_assoc, ← hc, ← mul_assoc, he]
  simp only [← mul_assoc]
  exact congrArg (fun t => t * toAllOrders k Q Λ ν y * e) fix.symm

private theorem inRedOrder (hQ : KLRSymm Q) (κ : List (Fin ℓ)) (x y : Braid) :
    let p := P κ
    p * (x*y) * p = p * (x*p*y) * p := by
  by_cases h : ∃ i : Seq (stendhalWeight ℓ ν), redWord i = κ
  · obtain ⟨i, rfl⟩ := h
    have hp : (redWord i).Perm (List.finRange ℓ) := (List.perm_ext_iff_of_nodup (redWord_nodup _) (List.nodup_finRange _)).2
      fun r => by simp [mem_redWord]
    obtain ⟨σ,hs⟩ := exists_perm_eq_map_finRange hp
    let b := redPermAlgEquiv (Q := Q) (Λ' := Λ ∘ σ) (ν := ν) σ (fun _ => rfl)
    obtain ⟨x,rfl⟩ := b.surjective x; obtain ⟨y,rfl⟩ := b.surjective y
    simpa only [hs, map_mul, b, redPermAlgEquiv_redProj] using
      congrArg b (inIdentityOrder Q (Λ ∘ σ) hQ x y)
  · push Not at h
    dsimp only; rw [redProj_eq_zero h]; simp

local notation "ord" => (fun (_ : RedBlock I ℓ) => 1)

private theorem order_at_loading : ∀ row (s : Loadings row),
    orderedIdem Q Λ ord row * loadingIdem Q Λ row s =
      @ite _ (UncrossedLoading row s) (Classical.propDecidable _) (loadingIdem Q Λ row s) 0
  | [], _ => (one_mul _).trans (ite_eq_left (show True from trivial)).symm
  | B :: row, s => by
    classical
    simp only [orderedIdem, loadingIdem, Algebra.TensorProduct.tmul_mul_tmul, Equiv.Perm.coe_one,
      List.map_id_fun, id_eq, redProj_mul_e, order_at_loading row s.2, UncrossedLoading]
    split_ifs <;> simp_all

variable (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "row" => adjacentRow L M f β
local notation "κ" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "G" => affineStackBlocks Q Λ L M f β h
local notation "E" => orderedIdem Q Λ ord row
local notation "p" => redIdem k Q Λ (ν := ν) κ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

/-- The global uncrossed-order projector restricts on the juxtaposed unit to the product of the local order projectors. -/
theorem affineStackBlocks_orderedIdem : p * G 1 = G E ∧ G 1 * p = G E := by
  classical
  let g := LinearMap.ofClass G
  let l := (LinearMap.mulLeft k p).comp g
  let r := (LinearMap.mulRight k p).comp g
  let o := g.comp (LinearMap.mulLeft k E)
  have H : (1 : diagrams Q Λ row) ∈ LinearMap.ker (l-o) ⊓ LinearMap.ker (r-o) := by
    apply (Submodule.span_le.2 ?_) (unit_mem_loadingSpan Q Λ row)
    rintro _ ⟨s,rfl⟩
    have he : G (loadingIdem Q Λ row s) = e (Seq.cast h (place row s)) := by
      change castKLR _ h _ = _; rw [juxtapose_loadingIdem,castKLR_e]
    change _ - G (E * loadingIdem Q Λ row s) = 0 ∧ _ - G (E * loadingIdem Q Λ row s) = 0
    change p * G (loadingIdem Q Λ row s) - _ = 0 ∧ G (loadingIdem Q Λ row s) * p - _ = 0
    have ho := order_at_loading Q Λ row s
    by_cases hs : UncrossedLoading row s
    · rw [ite_eq_left hs] at ho
      have ht := (uncrossedLoading_iff L M f β h s).mp hs
      rw [ho, he, redIdem_mul_e, e_mul_redIdem, ite_eq_left ht, sub_self]; exact ⟨rfl,rfl⟩
    · rw [ite_eq_right hs] at ho
      have ht := hs ∘ (uncrossedLoading_iff L M f β h s).mpr
      rw [ho, map_zero G, he, redIdem_mul_e, e_mul_redIdem, ite_eq_right ht, sub_self]; exact ⟨rfl,rfl⟩
  change p * G 1 - G (E*1) = 0 ∧ G 1 * p - G (E*1) = 0 at H
  simpa only [mul_one,sub_eq_zero] using H

/-- A placed loading in the prescribed local orders factors through the juxtaposed
ordered projector already in the ambient KLR algebra. -/
theorem affineStackBlocks_orderedIdem_mul_placed (u : Loadings row) (hu : UncrossedLoading row u) :
    G E * e (Seq.cast h (place row u)) = e (Seq.cast h (place row u)) := by
  classical
  have load : G (loadingIdem Q Λ row u) = e (Seq.cast h (place row u)) := by
    change castKLR _ h _ = _
    rw [juxtapose_loadingIdem, castKLR_e]
  rw [← load, ← map_mul G, order_at_loading Q Λ row u, ite_eq_left hu]

/-- Cutting the lower column before an arbitrary local coefficient has the same effect as
also projecting its other end to the uncrossed red order (Webster v2, proof of Lemma 6.8).
This is a diagonal-column equality, not commutation of the red projector in the braid algebra. -/
theorem insert_uncrossed_order (hQ : KLRSymm Q) (a : diagrams Q Λ row) (y : R) :
    let π := ofKLR k Q Λ ν
    π (G (E*a) * y * p) = π (G (E*a*E) * y * p) := by
  intro π
  have H := affineStackBlocks_orderedIdem Q Λ L M f β h
  have fix (a : diagrams Q Λ row) : p * G (E*a) = G (E*a) := by
    rw [map_mul, ← H.1]; simp only [← mul_assoc, redIdem_mul_redIdem]
  have right (a : diagrams Q Λ row) : G a * p = G (a*E) := by
    rw [map_mul, ← H.2, ← mul_assoc, ← map_mul, mul_one]
  have he := inRedOrder Q Λ hQ (ν := ν) κ (π (G (E*a))) (π y)
  change π p * (π (G (E*a)) * π y) * π p = π p * ((π (G (E*a)) * π p) * π y) * π p at he
  have he' : π (p * (G (E*a)*y) * p) = π (p * (G (E*a)*p*y) * p) := by simpa only [map_mul] using he
  simp only [← mul_assoc, fix] at he'; rw [right] at he'; exact he'

end Categorification.Stendhal.RedBlock
