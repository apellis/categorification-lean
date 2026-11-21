/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicBaseProjective

/-!
# Projectivity of cyclotomic restriction over a commutative ring

Kang–Kashiwara, arXiv:1102.4677v4, Corollaries 4.4 and 4.6, over every commutative ring `k`:
for `Q` with `KLRSymm Q` and unit constant leading coefficients and monic cyclotomic
polynomials, the cyclotomic restriction (restriction along the last-strand embedding) `R^Λ({i} + β)-mod → R^Λ(β)-mod` preserves finitely
generated projective modules (`CycKLR.projective_res_of_ring`, `CycKLR.finite_res_of_ring`).
For `β ≠ 0` this is Theorem 4.5 (`projective_res_regular_of_pos`); for `β = 0` the restriction
of the regular module is a direct summand of the `k`-projective module `R^Λ(i)`
(`projective_base`). Finite generation holds because the restriction of the regular module is
a direct summand of the finitely generated `k`-module `R^Λ({i} + β)`. These are the inputs for
the action of `𝒰` on finitely generated projective `Ř^λ`-modules (B. Webster,
arXiv:1309.3796v2, Corollary 3.27).
-/

noncomputable section

namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour MulOpposite

variable {k I : Type*} [CommRing k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
  (a : I → Polynomial k) (β : Multiset I) (i : I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rl" => CycKLR k Q a β
local notation "Su" => CycKLR k Q a (Si + β)

section Ring

/-- The `k`-linear projection `m ↦ e m` of a module onto its restriction, `e` the idempotent of
the last strand. -/
private def resProj (M : Type*) [AddCommGroup M] [Module k M] [Module Su M]
    [IsScalarTower k Su M] : M →ₗ[k] Res Q i a β M where
  toFun m := ⟨lastIdem Q i a β • m, smul_mem_fixSub (lastIdem_mul Q i a β) m⟩
  map_add' _ _ := Subtype.ext (smul_add _ _ _)
  map_smul' c m := Subtype.ext (smul_comm _ c m)

private theorem resProj_comp_subtype (M : Type*) [AddCommGroup M] [Module k M] [Module Su M]
    [IsScalarTower k Su M] :
    (resProj a β i M).comp (fixSub k M (lastIdem Q i a β)).subtype = LinearMap.id :=
  LinearMap.ext fun z => Subtype.ext z.2

private theorem projective_res_zero (M : Type*) [AddCommGroup M] [Module k M]
    [Module (CycKLR k Q a (Si + 0)) M] [IsScalarTower k (CycKLR k Q a (Si + 0)) M]
    [Module.Projective k (Res Q i a 0 M)] :
    Module.Projective (CycKLR k Q a 0) (Res Q i a 0 M) := by
  let σ := (cyclotomicZeroEquiv Q a).toRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  let e : Res Q i a 0 M ≃ₛₗ[(σ : CycKLR k Q a 0 →+* k)] Res Q i a 0 M :=
    { Equiv.refl _ with
      map_add' := fun _ _ => rfl
      map_smul' := fun r z => Subtype.ext (by
        change cyclotomicLast Q i a 0 r • z.1 = (cyclotomicZeroEquiv Q a r) • z.1
        rw [cyclotomicLast_zero_eq, smul_assoc, one_smul]) }
  exact Module.Projective.of_equiv e.symm

variable (hsym : KLRSymm Q)
  (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)

include hsym hQ ha in
/-- The restriction of the regular module is projective, over every commutative ring
(Kang–Kashiwara, arXiv:1102.4677v4, Theorem 4.5 for `β ≠ 0`; for `β = 0` the algebra
`R^Λ(0)` is the ground ring and the restriction is a direct summand of the projective
`k`-module `R^Λ(i)`). -/
theorem projective_res_regular : Module.Projective Rl (Res Q i a β Su) := by
  rcases eq_or_ne β 0 with rfl | h
  · have : Module.Projective k (CycKLR k Q a (Si + 0)) := projective_base a hsym hQ ha _
    have : Module.Projective k (Res Q i a 0 (CycKLR k Q a (Si + 0))) :=
      Module.Projective.of_split (fixSub k _ (lastIdem Q i a 0)).subtype
        (resProj a 0 i _) (resProj_comp_subtype a 0 i _)
    exact projective_res_zero a i _
  · exact projective_res_regular_of_pos a β i hsym hQ (ha i) (Multiset.card_pos.mpr h)

include hQ ha in
/-- The restriction of the regular module is finitely generated, over every commutative ring:
it is a direct summand of the finitely generated `k`-module `R^Λ({i} + β)`
(Kang–Kashiwara, arXiv:1102.4677v4, Corollary 4.4). -/
theorem finite_res_regular : Module.Finite Rl (Res Q i a β Su) := by
  have : Module.Finite k Su := module_finite (ν := Si + β) (fun s t h => by
    obtain ⟨c, hc, he⟩ := hQ s t h
    rw [he]
    exact hc.map Polynomial.C) ha
  have : Module.Finite k (Res Q i a β Su) :=
    Module.Finite.of_surjective (resProj a β i Su) fun z => ⟨z.1, Subtype.ext z.2⟩
  exact Module.Finite.of_restrictScalars_finite k Rl _

include hsym hQ ha in
/-- **Restriction preserves finitely generated projective modules**, over every commutative ring
(Kang–Kashiwara, arXiv:1102.4677v4, Corollary 4.6). -/
theorem projective_res_of_ring (M : Type*) [AddCommGroup M] [Module Su M] [Module.Finite Su M]
    [Module.Projective Su M] :
    Module.Projective Rl (InductionAlong.Res (cyclotomicLast Q i a β : Rl →ₙ+* Su) M) := by
  let φ : Rl →ₙ+* Su := cyclotomicLast Q i a β
  have : Module.Projective Rl (InductionAlong.Res φ Su) :=
    projective_res_regular a β i hsym hQ ha
  exact InductionAlong.Res.projective_of_regular φ M

include hQ ha in
/-- Restriction preserves finitely generated projective modules: finite generation, over every
commutative ring (Kang–Kashiwara, arXiv:1102.4677v4, Corollary 4.4). -/
theorem finite_res_of_ring (M : Type*) [AddCommGroup M] [Module Su M] [Module.Finite Su M]
    [Module.Projective Su M] :
    Module.Finite Rl (InductionAlong.Res (cyclotomicLast Q i a β : Rl →ₙ+* Su) M) := by
  let φ : Rl →ₙ+* Su := cyclotomicLast Q i a β
  have : Module.Finite Rl (InductionAlong.Res φ Su) := finite_res_regular a β i hQ ha
  exact InductionAlong.Res.finite_of_regular φ M

end Ring

end Categorification.KLR.CycKLR
