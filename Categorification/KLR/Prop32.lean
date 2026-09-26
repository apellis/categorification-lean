/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BarK0

/-!
# `[Res] [P_s]` in `K₀` (graded Proposition 2.19), towards KL I Proposition 3.2

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Proposition 2.19, and §3.1, Propositions 3.2, 3.3.
The graded Proposition 2.19 (`GradingDatum.resProjGradedEquiv`,
`Categorification.KLR.ResProjGraded`) identifies `Res_{ν,ν'} P_s` with the finite product
`Π_u (P_{i_u} ⊠ P_{j_u}){deg(ψ_{σ(u)} 1_s)}` over the shuffles `u` of `s`. We deduce the
corresponding identity in `K₀(R(ν) ⊗ R(ν'))`:

`[Res] [P_s] = ∑_u q^{deg(ψ_{σ(u)} 1_s)} [P_{i_u}] ⊗ [P_{j_u}]`   (`GradingDatum.resK0_projP`),

which is the decomposition `[Res] y = ∑_α y_α ⊗ y'_α` needed to evaluate Proposition 3.3 (4)
on `y = [P_s]` for the bilinear form (`GradingDatum.pform_indK0_projP_eq_sum`).

## Generic results

* `GProj.pi` : finite products of graded projective modules (with the product grading
  `Graded.piGrading`), and `K0.of_pi` : **`[Π_t M_t] = ∑_t [M_t]`**;
  `K0.of_eq_sum_of_iso_pi` : `[X] = ∑_t [M_t]` whenever `X ≅ Π_t M_t`.

## Not formalized here

KL I, Proposition 3.2 (`[Res]` is an algebra map for the twisted multiplication on
`K₀(R) ⊗ K₀(R)`) requires, beyond `resK0_projP`, the combinatorial identity matching the
shuffles of a concatenation `st` with pairs of shuffles of `s` and `t` together with the
degrees `deg(ψ_{σ(u)} 1_{st}) = deg(ψ_{σ(u₁)} 1_s) + deg(ψ_{σ(u₂)} 1_t) - |j_{u₁}| · |i_{u₂}|`
(equivalently, comparing `resK0_projP` with Lusztig's `r` on words), and a product on
`⨁_{ν,ν'} K₀(R(ν) ⊗ R(ν'))`; neither is formalized here.
-/

noncomputable section

universe u v

namespace Categorification

open DirectSum

namespace Graded

/-! ### Finite products in `A-pmod` -/

namespace GProj

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

/-- The finite product `Π_t M_t` of graded projective modules, graded by `Graded.piGrading`. -/
abbrev pi {ι : Type} [Fintype ι] [DecidableEq ι] (Ms : ι → GProj 𝒜) : GProj 𝒜 :=
  haveI : Module.Projective A (⨁ t, (Ms t).carrier) :=
    inferInstanceAs (Module.Projective A (Π₀ t, (Ms t).carrier))
  { carrier := ∀ t, (Ms t).carrier
    grading := piGrading fun t => (Ms t).grading
    finite := Module.Finite.pi
    projective := Module.Projective.of_equiv
      (DirectSum.linearEquivFunOnFintype A ι fun t => (Ms t).carrier) }

/-- Reindexing a finite product along an equivalence. -/
def piReindex {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (Ms : ι → GProj 𝒜) (e : ι' ≃ ι) : (pi (fun i' => Ms (e i'))).Iso (pi Ms) where
  toLinearEquiv := LinearEquiv.piCongrLeft A (fun t => (Ms t).carrier) e
  map_mem' d f hf i := by
    obtain ⟨i', rfl⟩ := e.surjective i
    change (Equiv.piCongrLeft (fun t => (Ms t).carrier) e) f (e i') ∈ (Ms (e i')).grading d
    rw [Equiv.piCongrLeft_apply_apply]
    exact hf i'
  symm_map_mem' d g hg i' := by
    change (Equiv.piCongrLeft (fun t => (Ms t).carrier) e).symm g i' ∈ (Ms (e i')).grading d
    rw [Equiv.piCongrLeft_symm_apply]
    exact hg (e i')

/-- `Π_{Option α} M ≅ M none × Π_α M (some ·)`. -/
def piOption {α : Type} [Fintype α] [DecidableEq α] (Ms : Option α → GProj 𝒜) :
    (pi Ms).Iso ((Ms none).prod (pi fun a => Ms (some a))) where
  toLinearEquiv := LinearEquiv.piOptionEquivProd A
  map_mem' d f hf := ⟨hf none, fun a => hf (some a)⟩
  symm_map_mem' d g hg o := by
    cases o with
    | none => exact hg.1
    | some a => exact hg.2 a

/-- A product over an empty index type is isomorphic to its square. -/
def piEmptyProdSelf {α : Type} [Fintype α] [DecidableEq α] [IsEmpty α] (Ms : α → GProj 𝒜) :
    (pi Ms).Iso ((pi Ms).prod (pi Ms)) :=
  haveI : Subsingleton (pi Ms).carrier := inferInstanceAs (Subsingleton (∀ t, (Ms t).carrier))
  haveI : Subsingleton ((pi Ms).prod (pi Ms)).carrier :=
    inferInstanceAs (Subsingleton ((pi Ms).carrier × (pi Ms).carrier))
  { toLinearEquiv := LinearEquiv.ofSubsingleton _ _
    map_mem' := fun d x _ => by
      rw [Subsingleton.elim (LinearEquiv.ofSubsingleton _ _ x) 0]; exact zero_mem _
    symm_map_mem' := fun d y _ => by
      rw [Subsingleton.elim ((LinearEquiv.ofSubsingleton _ _).symm y) 0]; exact zero_mem _ }

end GProj

namespace K0

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

open GProj

omit [GradedAlgebra 𝒜] in
/-- **`[Π_t M_t] = ∑_t [M_t]`** for a finite product of graded projective modules. -/
theorem of_pi {ι : Type} [Fintype ι] [DecidableEq ι] (Ms : ι → GProj 𝒜) :
    of (GProj.pi Ms) = ∑ t, of (Ms t) := by
  revert Ms
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ [DecidableEq ι] (Ms : ι → GProj 𝒜), of (GProj.pi Ms) = ∑ t, of (Ms t))
    ?_ ?_ ?_ ι
  · intro α β _ e h _ Ms
    classical
    letI := Fintype.ofEquiv β e.symm
    rw [← of_eq_of_iso (piReindex Ms e), h]
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  · intro _ Ms
    have h := of_eq_of_iso (piEmptyProdSelf Ms)
    rw [of_prod] at h
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    simpa using h
  · intro α _ h _ Ms
    classical
    rw [of_eq_of_iso (piOption Ms), of_prod, h, Fintype.sum_option]

omit [GradedAlgebra 𝒜] in
/-- `[X] = ∑_t [M_t]` whenever `X ≅ Π_t M_t` (graded). -/
theorem of_eq_sum_of_iso_pi {ι : Type} [Fintype ι] [DecidableEq ι] (X : GProj 𝒜)
    (Ms : ι → GProj 𝒜) (e : X.grading ≃ᵍ[A] piGrading fun t => (Ms t).grading) :
    of X = ∑ t, of (Ms t) := by
  rw [← of_pi]
  exact of_eq_of_iso e

end K0

end Graded

namespace KLR

open Graded KLRAlgebra TypeA MvPolynomial LaurentPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν ν' : Multiset I}

namespace GradingDatum

variable (G : GradingDatum Q) {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

/-- **KL I, Proposition 2.19, in `K₀`**:
`[Res_{ν,ν'}] [P_s] = ∑_u q^{deg(ψ_{σ(u)} 1_s)} [P_{i_u}] ⊗ [P_{j_u}]`, the sum over the shuffles
`u` of `s` (`u • s = i_u j_u`). -/
theorem resK0_projP (s : Seq (ν + ν')) :
    G.resK0 ν ν' hPQ hP (K0.of (G.projP s)) =
      ∑ u : ShuffleOf ν ν' s, (T (G.degW (shuffleWord u.1) s) : LaurentPolynomial ℤ) •
        K0.extTensor (G.grade ν) (G.grade ν') (K0.of (G.projP u.split.1))
          (K0.of (G.projP u.split.2)) := by
  classical
  rw [resK0_of, K0.of_eq_sum_of_iso_pi _ (G.resSummand ν ν' s)
    (G.resProjGradedEquiv hPQ hP s).symm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [resSummand, ← K0.T_smul_of, K0.extTensor_of]

variable (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a)
  [HasGdim (G.grade ν)] [HasGdim (G.grade ν')] [HasGdim (G.grade (ν + ν'))]

include hPQ hP in
/-- **KL I, Proposition 3.3 (4), for the bilinear form, evaluated on `P_s`**: for `x`, `x'` in the
spans of idempotent classes,
`(x x', [P_s]) = ∑_u q^{deg(ψ_{σ(u)} 1_s)} (x, [P_{i_u}]) (x', [P_{j_u}])`. -/
theorem pform_indK0_projP_eq_sum {x : K0 (G.grade ν)} {x' : K0 (G.grade ν')}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν)))
    (hx' : x' ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν')))
    (s : Seq (ν + ν')) :
    K0.pform (G.grade (ν + ν')) (G.psi hsymm (ν + ν')) (G.indK0 ν ν' x x') (K0.of (G.projP s)) =
      ∑ u : ShuffleOf ν ν' s, HahnSeries.single (G.degW (shuffleWord u.1) s) 1 *
        (K0.pform (G.grade ν) (G.psi hsymm ν) x (K0.of (G.projP u.split.1)) *
          K0.pform (G.grade ν') (G.psi hsymm ν') x' (K0.of (G.projP u.split.2))) := by
  rw [G.pform_indK0 hsymm hPQ hP hx hx', G.resK0_projP hPQ hP, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [K0.pform_T_smul_right, K0.pform_extTensor_of_mem_span _ _ hx hx']

include hPQ hP in
/-- **KL I, Proposition 3.3 (3), evaluated on `P_s`**: for `y`, `y'` in the spans of idempotent
classes, `([P_s], y y') = ∑_u q^{deg(ψ_{σ(u)} 1_s)} ([P_{i_u}], y) ([P_{j_u}], y')`. -/
theorem pform_projP_indK0_eq_sum {y : K0 (G.grade ν)} {y' : K0 (G.grade ν')}
    (hy : y ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν)))
    (hy' : y' ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν')))
    (s : Seq (ν + ν')) :
    K0.pform (G.grade (ν + ν')) (G.psi hsymm (ν + ν')) (K0.of (G.projP s)) (G.indK0 ν ν' y y') =
      ∑ u : ShuffleOf ν ν' s, HahnSeries.single (G.degW (shuffleWord u.1) s) 1 *
        (K0.pform (G.grade ν) (G.psi hsymm ν) (K0.of (G.projP u.split.1)) y *
          K0.pform (G.grade ν') (G.psi hsymm ν') (K0.of (G.projP u.split.2)) y') := by
  rw [K0.pform_comm, G.pform_indK0_projP_eq_sum hPQ hP hsymm hy hy' s]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [K0.pform_comm _ y, K0.pform_comm _ y']

end GradingDatum

end KLR

end Categorification
