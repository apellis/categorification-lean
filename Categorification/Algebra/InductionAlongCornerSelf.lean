/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongCornerRes

/-!
# Induction along a nonunital map onto a corner, and induction along the identity

Let `φ : A →ₙ+* B` be an injective nonunital ring map whose image is the corner
`φ(1) B φ(1)`. Then `φ(1) Ind_φ N ≅ N` (`fixSubIndSelfEquiv`): the bimodule `φ(1) B φ(1)` is
`A`, so the piece is the induction of `N` along the identity (`indIdEquiv`). This is used in
the dimension count of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Proposition 5.5, for the map `T^{λ'} → e_ℓ T^λ e_ℓ` of
Proposition 4.18.
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u w

variable {A B : Type u} [Ring A] [Ring B]

/-- The identity of `A` as a nonunital ring map. -/
abbrev idHom (A : Type u) [Ring A] : A →ₙ+* A := NonUnitalRingHom.id A

section IdInduction

variable (M : Type w) [AddCommGroup M] [Module A M]

/-- `A ⊗_A M → M`, `z ⊗ n ↦ z n`. -/
def indIdFwd : Ind M (idHom A) →+ M :=
  Ind.liftAdd (fun z n => z.1 • n) (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_add _ _ _)
    (fun _ _ _ => mul_smul _ _ _)

theorem indIdFwd_smul (a : A) (x : Ind M (idHom A)) : indIdFwd M (a • x) = a • indIdFwd M x := by
  induction x using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul z n =>
    rw [Ind.smul_tmul]
    change (a * z.1) • n = a • (z.1 • n)
    rw [mul_smul]
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

variable (k : Type*) [CommRing k] [Algebra k A] [Module k M] [IsScalarTower k A M]

/-- **Induction along the identity**: `IndK k M id ≅ M`. -/
def indIdEquiv : IndK k M (idHom A) ≃ₗ[k] M where
  toFun := indIdFwd M
  invFun n := IndK.tmul (unitGen (idHom A)) n
  map_add' := map_add _
  map_smul' c x := by
    change indIdFwd M (algebraMap k A c • (x : Ind M (idHom A))) = c • indIdFwd M x
    exact (indIdFwd_smul M _ x).trans (algebraMap_smul _ _ _)
  left_inv x := by
    change Ind.tmul (unitGen (idHom A)) (indIdFwd M x) = x
    induction x using Ind.induction_on with
    | zero => rw [map_zero, Ind.tmul_zero]
    | tmul z n =>
      change Ind.tmul (unitGen (idHom A)) (z.1 • n) = Ind.tmul z n
      rw [← Ind.op_smul_tmul]
      congr 1
      exact Subtype.ext (one_mul z.1)
    | add s t hs ht => rw [map_add, Ind.tmul_add, hs, ht]
  right_inv n := one_smul A n

end IdInduction

section CornerSelf

variable (φ : A →ₙ+* B) (hφ : Function.Injective φ) (hs : ∀ z : B, ∃ a, φ a = φ 1 * z * φ 1)

/-- A preimage of `φ(1) z φ(1)`. -/
def cornerPre (z : B) : A := (hs z).choose

theorem map_cornerPre (z : B) : φ (cornerPre φ hs z) = φ 1 * z * φ 1 := (hs z).choose_spec

include hφ in
theorem cornerPre_eq {z : B} {a : A} (h : φ a = φ 1 * z * φ 1) : cornerPre φ hs z = a :=
  hφ ((map_cornerPre φ hs z).trans h.symm)

/-- `A ≅ φ(1) B φ(1)` as a corner isomorphism with `φ' = id`. -/
def cornerSelfIso : CornerIso φ φ (idHom A) where
  toFun :=
    { toFun := fun g => ⟨φ g.1, by
        change φ g.1 * φ 1 = φ g.1
        rw [← map_mul, mul_one]⟩
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun g g' => Subtype.ext (map_add φ g.1 g'.1) }
  invFun :=
    { toFun := fun z => ⟨cornerPre φ hs z.1, mul_one _⟩
      map_zero' := Subtype.ext (cornerPre_eq φ hφ hs (by
        change φ 0 = φ 1 * 0 * φ 1
        rw [map_zero, mul_zero, zero_mul]))
      map_add' := fun z z' => Subtype.ext (cornerPre_eq φ hφ hs (by
        change φ (cornerPre φ hs z.1 + cornerPre φ hs z'.1) = φ 1 * (z.1 + z'.1) * φ 1
        rw [map_add, map_cornerPre, map_cornerPre, mul_add, add_mul])) }
  fixed g := by
    change φ 1 * φ g.1 = φ g.1
    rw [← map_mul, one_mul]
  inv_toFun g := Subtype.ext (cornerPre_eq φ hφ hs (by
    change φ g.1 = φ 1 * φ g.1 * φ 1
    rw [← map_mul, ← map_mul, one_mul, mul_one]))
  toFun_inv z := by
    change φ (cornerPre φ hs z.1) = φ 1 * z.1
    rw [map_cornerPre, mul_assoc, z.2]
  inv_unit z := Subtype.ext (by
    change cornerPre φ hs z.1 = cornerPre φ hs (φ 1 * z.1)
    refine (cornerPre_eq φ hφ hs ?_).symm
    rw [map_cornerPre, ← mul_assoc, unit_mul_unit])
  map_left a g := by
    change φ (a * g.1) = φ a * φ g.1
    rw [map_mul]
  map_right a g := Subtype.ext (by
    change φ (g.1 * a) = φ g.1 * φ a
    rw [map_mul])
  inv_right a z := Subtype.ext (by
    change cornerPre φ hs (z.1 * φ a) = cornerPre φ hs z.1 * a
    refine cornerPre_eq φ hφ hs ?_
    have h1 : φ 1 * φ a = φ a := by rw [← map_mul, one_mul]
    have h2 : φ a * φ 1 = φ a := by rw [← map_mul, mul_one]
    rw [map_mul, map_cornerPre]
    simp only [mul_assoc, h1, h2])

variable (k : Type*) [CommRing k] [Algebra k A] [Algebra k B]
  (hk : ∀ c : k, φ (algebraMap k A c) = algebraMap k B c * φ 1)
  (N : Type w) [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

include hφ hs hk in
/-- **`φ(1) Ind_φ N ≅ N`** when `φ` maps `A` isomorphically onto `φ(1) B φ(1)`. -/
def fixSubIndSelfEquiv : fixSub k (IndK k N φ) (φ 1) ≃ₗ[k] N :=
  (fixSubIndEquiv k hk (cornerSelfIso φ hφ hs)).trans (indIdEquiv N k)

include hφ hs hk in
theorem finrank_fixSub_indSelf :
    Module.finrank k (fixSub k (IndK k N φ) (φ 1)) = Module.finrank k N :=
  (fixSubIndSelfEquiv φ hφ hs k hk N).finrank_eq

end CornerSelf

end InductionAlong

end

end Categorification
