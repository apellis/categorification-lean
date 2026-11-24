/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelTensor

/-!
# The projective presentation of partial standardization at a loading

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 at (6.21). Identify the image
of the quotient of the ordered loading projective with the summand of the partial
standardization column cut out by the external loading idempotent. Here top and bottom
have the same red order; the braiding has not yet been applied.
-/
noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR BraidedStendhalAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "row" => adjacentRow L M f β
local notation "κ" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "α" => fun r i => boundaryCount (cut (f 0) (f 1) r) i row
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1) α κ
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)
local notation "mk" => violMk k Q Λ ν
local notation "π" => AlgHom.comp mk (ofKLR k Q Λ ν)
variable (s : Loadings (adjacentRow L M f β))
local notation "t" => Seq.cast h (place row s)
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "S" => loadingSummand Q Λ L M f β h s
variable (ho : redWord (Seq.cast h (place (adjacentRow L M f β) s)) =
  L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)

/-- The cover onto the partial standardization of the external loading projective.
The map sends a diagram to the same diagram modulo the retained higher boundaries. -/
def blockStandardCover : P →ₗ[k] S :=
  ((q).toLinearMap ∘ₗ IsIdempotentElem.cornerVal (R := k) (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t)) ∘ₗ
    (P).subtype.restrictScalars k).codRestrict S fun x => by
      rw [loadingSummand_eq]
      refine ⟨x.1.1, ?_⟩
      change q (π (KLRAlgebra.e t) * (x.1.1 * mk (redProj k Q Λ ν κ))) = q x.1.1
      have hr : x.1.1 * mk (redProj k Q Λ ν κ) = x.1.1 :=
        ho ▸ CornerEndomorphism.corner_mul_right (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t)) x.1
      rw [hr]
      exact congrArg (q) (congrArg Subtype.val x.2)

theorem blockStandardCover_surjective : Function.Surjective (blockStandardCover Q Λ L M f β h s ho) := by
  rintro ⟨z,hz⟩
  rw [loadingSummand_eq] at hz
  obtain ⟨v,rfl⟩ := hz
  refine ⟨blockLoadingRep Q Λ t v, Subtype.ext ?_⟩
  change q (blockLoadingRep Q Λ t v).1.1 = q (π (KLRAlgebra.e t) * (v * mk (redProj k Q Λ ν κ)))
  rw [blockLoadingRep_val, ho, mul_assoc]; rfl

/-- The cover respects the right ordered algebra: on the external loading summand
the action is multiplication at the bottom of the diagram, modulo the retained cuts. -/
theorem blockStandardCover_right (x : P)
    (d : (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t)).Corner) :
    (blockStandardCover Q Λ L M f β h s ho (MulOpposite.op d • x)).1 =
      (blockStandardCover Q Λ L M f β h s ho x).1 * q d.1 :=
  map_mul (q) x.1.1 d.1

/-- **Loading presentation at (6.21)** (Webster v2, proof of Lemma 6.8): the kernel of
the surjection to the external loading summand is precisely the higher right submodule. -/
theorem ker_blockStandardCover (hs : ¬ Violated row s) :
    LinearMap.ker (blockStandardCover Q Λ L M f β h s ho) =
      (blockLoadingKernel Q Λ t (f 0) (f 1)).restrictScalars k := by
  have ha : adjacentBlockRoot (f 0) (f 1) t = α := by
    funext r i
    have hc {u w : Multiset (I ⊕ Fin ℓ)} (he : u = w) (z : Seq u) (C : Finset (Fin ℓ)) :
        blockBlackCount (Seq.cast he z) C i = blockBlackCount z C i := by subst w; rfl
    exact (hc h _ _).trans (count_place_of_not_violated r i s (aligned_adjacent L M f β (ho ▸ redWord_nodup t)) hs)
  ext x
  change blockStandardCover Q Λ L M f β h s ho x = 0 ↔ x.1.1 ∈ blockUpperIdeal k Q Λ ν _ _ _ _
  have hJ : blockUpperIdeal k Q Λ ν (f 0) (f 1) (adjacentBlockRoot (f 0) (f 1) t) (redWord t) = J := by
    rw [ha, ho]
  rw [Subtype.ext_iff, hJ]
  change (J).ringCon.mk' x.1.1 = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

end Categorification.Stendhal.RedBlock
