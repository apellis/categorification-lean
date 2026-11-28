/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721ResIndCounit
import Categorification.Algebra.InductionAlongDotMate

/-!
# Conjugates along `Res ⊣ Ind` and the symmetry of the trace

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31,
as used in §7.3, proof of Proposition 7.21. Let `φ : A → B` be a ring map and `c ∈ B` commute
with the image of `φ`. Left multiplication by `c` on restriction (`resAct`) has two conjugates
on induction: along the adjunction `Ind ⊣ Res` it is right multiplication `z ⊗ n ↦ z c ⊗ n`
(`InductionAlong.conjugateEquiv_symm_resAct_app`), and along any adjunction `Res ⊣ Ind` it is
determined by the counit, that is, by the trace `τ(z) = ε_A (z ⊗ 1)` of
`CupCap.resIndCounit_app_mk_tmul`. The two conjugates agree as soon as `τ(c z) = τ(z c)` for all
`z` in the corner `φ(1) B φ(1)` (`CupCap.conjugateEquiv_resAct_eq_of_trace`).

For Webster's `𝔈_i ⊣ 𝔉_i` (Theorem 4.31) and `c` the dot on the new strand this reduces the
agreement of the conjugate dot on `𝔉_i` with the dot on `𝔉_i` to the symmetry of the trace of
Theorem 4.31 against the dot; the two-strand version (`CupCap.conjugateEquiv_resAct₂_eq_of_trace`)
does the same for the crossing and the composite trace.

## Main definitions

* `CupCap.resIndTrace adj z`: the trace `ε_A (z ⊗ 1)` of an adjunction `Res ⊣ Ind`.

## Main results

* `CupCap.conjugateEquiv_resAct_eq_of_trace`: the two conjugates of `resAct c` agree when the
  trace is symmetric against `c`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory MulOpposite InductionAlong

section OneStep

variable {A B : Type} [Ring A] [Ring B] {φ : A →ₙ+* B}
  (adj : resFunctor.{0, 0} φ ⊣ InductionAlong.functor.{0, 0} φ)

/-- **The trace of an adjunction `Res_φ ⊣ Ind_φ`**: the counit on the regular module evaluated at
`z ⊗ 1`, for `z` in the corner with `φ(1) z = z` (Webster, arXiv:1309.3796v3, Theorem 4.31; by
`CupCap.resIndCounit_app_mk_tmul` it determines the counit). -/
def resIndTrace (z : Corner φ) (hz : φ 1 * z.1 = z.1) : A :=
  (adj.counit.app (ModuleCat.of A A)).hom (Res.mk (Ind.tmul z (1 : A)) (ind_tmul_fixed z hz 1))

variable {c : B} (hc : ∀ a, c * φ a = φ a * c)

include hc in
theorem smul_corner_fixed (z : Corner φ) (hz : φ 1 * z.1 = z.1) :
    φ 1 * (c • z).1 = (c • z).1 := by
  change φ 1 * (c * z.1) = c * z.1
  rw [← mul_assoc, ← hc 1, mul_assoc, hz]

theorem cornerMul_fixed {x : B} (hx : Intertwines φ φ x) (z : Corner φ)
    (hz : φ 1 * z.1 = z.1) : φ 1 * (cornerMul hx z).1 = (cornerMul hx z).1 := by
  change φ 1 * (z.1 * x) = z.1 * x
  rw [← mul_assoc, hz]

theorem unit_smul_corner_fixed (z : Corner φ) : φ 1 * ((φ 1) • z).1 = ((φ 1) • z).1 := by
  change φ 1 * (φ 1 * z.1) = φ 1 * z.1
  rw [← mul_assoc, unit_mul_unit]

private theorem conjugateEquiv_eq_of_counit' {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (β : R₁ ⟶ R₂)
    (h : ∀ d : D, L₂.map (β.app d) ≫ adj₂.counit.app d = α.app (R₁.obj d) ≫ adj₁.counit.app d) :
    conjugateEquiv adj₁ adj₂ α = β := by
  ext d
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, h d]
  exact conjugateEquiv_counit adj₁ adj₂ α d

/-- Two linear maps out of `Res_φ (Ind_φ N)` agree if they agree on the generators `z ⊗ n` with
`φ(1) z = z`. -/
theorem res_ind_hom_ext {N P : Type} [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    {f g : Res φ (Ind N φ) →ₗ[A] P}
    (h : ∀ (z : Corner φ) (hz : φ 1 * z.1 = z.1) (n : N),
      f (Res.mk (Ind.tmul z n) (ind_tmul_fixed z hz n)) =
        g (Res.mk (Ind.tmul z n) (ind_tmul_fixed z hz n))) : f = g := by
  have hfix : ∀ t : Ind N φ, φ 1 • (φ 1 • t) = φ 1 • t := fun t => by
    rw [smul_smul, unit_mul_unit]
  have key : ∀ t : Ind N φ, f (Res.mk (φ 1 • t) (hfix t)) = g (Res.mk (φ 1 • t) (hfix t)) := by
    intro t
    induction t using Ind.induction_on with
    | zero =>
      have h0 : (Res.mk (φ 1 • (0 : Ind N φ)) (hfix 0) : Res φ (Ind N φ)) = 0 :=
        Res.ext (smul_zero _)
      rw [h0, map_zero, map_zero]
    | add s t hs ht =>
      have hst : (Res.mk (φ 1 • (s + t)) (hfix (s + t)) : Res φ (Ind N φ)) =
          Res.mk (φ 1 • s) (hfix s) + Res.mk (φ 1 • t) (hfix t) := Res.ext (smul_add _ _ _)
      rw [hst, map_add, map_add, hs, ht]
    | tmul z n =>
      have hzt : (Res.mk (φ 1 • Ind.tmul z n) (hfix _) : Res φ (Ind N φ)) =
          Res.mk (Ind.tmul ((φ 1) • z) n) (ind_tmul_fixed _ (unit_smul_corner_fixed z) n) :=
        Res.ext (Ind.smul_tmul _ _ _)
      rw [hzt]
      exact h _ (unit_smul_corner_fixed z) n
  ext r
  have hr : r = Res.mk (φ 1 • r.val) (hfix r.val) := Res.ext r.prop.symm
  rw [hr]
  exact key r.val

variable (τ : resFunctor.{0, 0} φ ⟶ resFunctor φ)
  (hτ : ∀ M, τ.app M = ModuleCat.ofHom (resAct c hc M))

include hτ in
/-- **The conjugate of left multiplication along `Res ⊣ Ind` is right multiplication, when the
trace is symmetric against `c`** (Webster, arXiv:1309.3796v3, Theorem 4.31): if
`τ(c z) = τ(z c)` for every `z` in the corner with `φ(1) z = z`, then the conjugate along `adj`
of `resAct c` is the conjugate along `Ind ⊣ Res`, right multiplication `z ⊗ n ↦ z c ⊗ n`. -/
theorem conjugateEquiv_resAct_eq_of_trace
    (htr : ∀ (z : Corner φ) (hz : φ 1 * z.1 = z.1),
      resIndTrace adj (c • z) (smul_corner_fixed hc z hz) =
        resIndTrace adj (cornerMul (intertwines_of_commute hc) z)
          (cornerMul_fixed (intertwines_of_commute hc) z hz)) :
    conjugateEquiv adj adj τ = (conjugateEquiv (adjunction.{0, 0} φ) (adjunction φ)).symm τ := by
  refine conjugateEquiv_eq_of_counit' adj adj τ _ fun d => ?_
  rw [conjugateEquiv_symm_resAct_app hc τ hτ d, hτ]
  refine ModuleCat.hom_ext (res_ind_hom_ext fun z hz n => ?_)
  change (adj.counit.app d).hom (Res.mk (Ind.tmul (cornerMul (intertwines_of_commute hc) z) n)
      (ind_tmul_fixed _ (cornerMul_fixed (intertwines_of_commute hc) z hz) n)) =
    (adj.counit.app d).hom (Res.mk (Ind.tmul (c • z) n)
      (ind_tmul_fixed _ (smul_corner_fixed hc z hz) n))
  rw [resIndCounit_app_mk_tmul adj d _ (cornerMul_fixed (intertwines_of_commute hc) z hz) n,
    resIndCounit_app_mk_tmul adj d _ (smul_corner_fixed hc z hz) n]
  exact congrArg (· • n) (htr z hz).symm

end OneStep

section Transport

variable {A B A' B' : Type} [Ring A] [Ring B] [Ring A'] [Ring B'] {φ : A →ₙ+* B}
  {φ' : A' →ₙ+* B'} (a : A ≃+* A') (c : B ≃+* B') (hac : ∀ t, φ' (a t) = c (φ t))
  (adj' : resFunctor.{0, 0} φ' ⊣ InductionAlong.functor.{0, 0} φ')

theorem resIndTrace_congr (adj : resFunctor.{0, 0} φ ⊣ InductionAlong.functor.{0, 0} φ)
    {z z' : Corner φ} (e : z = z') (hz : φ 1 * z.1 = z.1) (hz' : φ 1 * z'.1 = z'.1) :
    resIndTrace adj z hz = resIndTrace adj z' hz' := by
  subst e; rfl

/-- **The trace of a transported `Res ⊣ Ind`** (Webster, arXiv:1309.3796v3, Theorem 4.31,
transported along Lemma 4.29): `τ(z) = a⁻¹ (τ' (c z))`. -/
theorem resIndTrace_transport (z : Corner φ) (hz : φ 1 * z.1 = z.1) :
    resIndTrace (resIndAdjunctionTransport.{0, 0} a c hac adj') z hz =
      a.symm (resIndTrace adj' (transportCorner a c hac z) (transportCorner_fixed a c hac z hz)) :=
  (resIndAdjunctionTransport_counit_app_mk_tmul a c hac adj' (ModuleCat.of A A) z hz 1).trans
    (by rw [smul_eq_mul, mul_one]; rfl)

variable {c₀ : B} (hc₀ : ∀ t, c₀ * φ t = φ t * c₀)

include hac hc₀ in
/-- The image of an element commuting with the image of `φ` commutes with the image of `φ'`. -/
theorem transport_commute (t : A') : c c₀ * φ' t = φ' t * c c₀ := by
  rw [← a.apply_symm_apply t, hac, ← map_mul, ← map_mul, hc₀]

include hc₀ in
/-- **Symmetry of the trace transports along ring isomorphisms** (Webster, arXiv:1309.3796v3,
Theorem 4.31, transported along Lemma 4.29): if the trace of `adj'` is symmetric against `c c₀`,
the trace of the transported adjunction is symmetric against `c₀`. -/
theorem resIndTrace_transport_cyclic
    (h' : ∀ (z : Corner φ') (hz : φ' 1 * z.1 = z.1),
      resIndTrace adj' (c c₀ • z) (smul_corner_fixed (transport_commute a c hac hc₀) z hz) =
        resIndTrace adj' (cornerMul (intertwines_of_commute (transport_commute a c hac hc₀)) z)
          (cornerMul_fixed (intertwines_of_commute (transport_commute a c hac hc₀)) z hz))
    (z : Corner φ) (hz : φ 1 * z.1 = z.1) :
    resIndTrace (resIndAdjunctionTransport.{0, 0} a c hac adj') (c₀ • z)
        (smul_corner_fixed hc₀ z hz) =
      resIndTrace (resIndAdjunctionTransport.{0, 0} a c hac adj')
        (cornerMul (intertwines_of_commute hc₀) z)
        (cornerMul_fixed (intertwines_of_commute hc₀) z hz) := by
  rw [resIndTrace_transport, resIndTrace_transport]
  congr 1
  have hzt := transportCorner_fixed a c hac z hz
  refine (resIndTrace_congr adj' (Subtype.ext (map_mul c c₀ z.1)) _
    (smul_corner_fixed (transport_commute a c hac hc₀) _ hzt)).trans
      ((h' _ hzt).trans
        (resIndTrace_congr adj' (Subtype.ext (map_mul c z.1 c₀).symm) _ _))

end Transport

end Categorification.Stendhal.CupCap
