/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyResRight
import Categorification.KLR.ResProjGraded
import Categorification.KLR.GradingFlip

/-!
# Graded Proposition 2.19, second formula (right projective modules)

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Proposition 2.19** (`\label{prop_res_proj}`,
TeX lines 1842–1851), second formula: for `s ∈ Seq(ν + ν')`,

`Res_{ν,ν'} (ₛP) ≅ ⊕_{i * j = s} ᵢP ⊗ ⱼP {deg(i, j, s)}`

as graded right `R(ν) ⊗ R(ν')`-modules, the sum over the ways of writing `s` as a shuffle of
`i ∈ Seq ν` and `j ∈ Seq ν'`, where `deg(i, j, s)` is "the degree of the diagram in `R(ν + ν')`
naturally associated to the shuffle".

The ungraded isomorphism `(t_u)_u ↦ ∑_u 1_s ψ_{σ(u)^{rev}} ι(t_u)` is
`KLRAlgebra.resProjEquivRight` (`Categorification.KLR.MackeyResRight`); it is right
`R(ν) ⊗ R(ν')`-linear (`KLRAlgebra.resProjEquivRight_mul`). Here we record the gradings:

* `ₛP = 1_s R(ν + ν')` and `Res_{ν,ν'} (ₛP) = 1_s R(ν + ν') 1_{ν,ν'}` (`resRightSub`) are graded by
  `R(ν + ν')` (`GradingDatum.resRightGrading`), and `ᵢP ⊗ ⱼP = (1_i ⊗ 1_j)(R(ν) ⊗ R(ν'))`
  (`projPPR`) by the tensor product grading (`GradingDatum.projPPRGrading`); these are gradings
  (`DirectSum.Decomposition`) since the idempotents have degree `0`.
* The diagram attached to the shuffle `u` for right modules is `1_s ψ_{σ(u)^{rev}}`, the
  reflection `ψ = hflip` of the diagram `ψ_{σ(u)} 1_s` used for left modules. It is homogeneous of
  degree `GradingDatum.degR (σ u) s = deg(ψ_{σ(u)^{rev}} 1_{σ(u)⁻¹ s})`
  (`GradingDatum.e_mul_ψw_reverse_mem_grade`), and, when the crossing degrees are symmetric
  (`degΨ a b = degΨ b a`, e.g. for KL I's grading `degΨ a b = -a · b`), also of degree
  `deg(ψ_{σ(u)} 1_s) = G.degW (σ u) s` (`GradingDatum.e_mul_ψw_reverse_mem_grade_of_symm`), the
  same shift `deg(i, j, s)` as in the first formula (`GradingDatum.resProjGradedEquiv`).

## Main results

* `GradingDatum.resProjGradedEquivRightOf` : for any shifts `δ u` with
  `1_s ψ_{σ(u)^{rev}} ∈ R(ν + ν')_{δ u}`, the isomorphism of Proposition 2.19 is a graded
  isomorphism `⊕_u (ᵢ₍ᵤ₎P ⊗ ⱼ₍ᵤ₎P){δ u} ≅ Res_{ν,ν'} (ₛP)` (degree-preserving in both directions).
* `GradingDatum.resProjGradedEquivRight` : the case `δ u = degR (σ u) s`, for every grading
  datum.
* `GradingDatum.resProjGradedEquivRight_of_symm` (**KL I, Proposition 2.19, second formula,
  graded**): for symmetric crossing degrees, `δ u = deg(ψ_{σ(u)} 1_s) = deg(i_u, j_u, s)`, the
  printed shift. `KL1.resProjGradedEquivRight` is the case of KL I's grading.

In both cases the underlying map is `resProjEquivRight`, so it intertwines the right actions
(`GradingDatum.resProjGradedEquivRight_mul`).

## Conventions

As for the first formula, `M{a}` is the grading shifted up by `a` (`Graded.shift`,
`(M{a})_d = M_{d - a}`), the direct sum is modelled as the finite product `Π_u` with the product
grading `Graded.piGrading`, and we use the canonical reduced words `σ(u) = canWord u`
(`KLRAlgebra.shuffleWord`). Right modules are modelled as `k`-subspaces closed under right
multiplication, so the graded isomorphism is a degree-preserving `k`-linear isomorphism together
with the intertwining property for the right action.
-/

noncomputable section

namespace Categorification.KLR

open Graded KLRAlgebra TypeA Equiv MvPolynomial DirectSum
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν ν' : Multiset I}

namespace GradingDatum

variable (G : GradingDatum Q)

/-! ### Gradings of the right modules -/

section Gradings

/-- The grading of the right projective `ᵢP ⊗ ⱼP = (1_i ⊗ 1_j)(R(ν) ⊗ R(ν'))`, induced from the
tensor product grading of `R(ν) ⊗ R(ν')`. -/
def projPPRGrading (i : Seq ν) (j : Seq ν') : ℤ → Submodule k (projPPR Q i j) :=
  comap (tensorGrading (G.grade ν) (G.grade ν')) (projPPR Q i j).subtype

@[simp] theorem mem_projPPRGrading {i : Seq ν} {j : Seq ν'} {d : ℤ} {t : projPPR Q i j} :
    t ∈ G.projPPRGrading i j d ↔
      (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') ∈ tensorGrading (G.grade ν) (G.grade ν') d :=
  Iff.rfl

theorem e_tmul_e_mem_tensorGrading (i : Seq ν) (j : Seq ν') :
    ((e i : KLRAlgebra k Q ν) ⊗ₜ[k] (e j : KLRAlgebra k Q ν')) ∈
      tensorGrading (G.grade ν) (G.grade ν') 0 := by
  simpa using tmul_mem_tensorGrading (G.e_mem_grade i) (G.e_mem_grade j)

theorem isInternal_projPPRGrading (i : Seq ν) (j : Seq ν') :
    IsInternal (G.projPPRGrading i j) :=
  isInternal_comap _ _ Subtype.val_injective fun t d =>
    ⟨⟨_, by
      have h := coe_decompose_mul_of_left_mem_zero (𝒜 := tensorGrading (G.grade ν) (G.grade ν'))
        (j := d) (b := (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν'))
        (G.e_tmul_e_mem_tensorGrading i j)
      rw [mem_projPPR.1 t.2] at h
      exact h.symm⟩, rfl⟩

instance (i : Seq ν) (j : Seq ν') : Decomposition (G.projPPRGrading i j) :=
  (G.isInternal_projPPRGrading i j).chooseDecomposition

variable (ν ν') in
/-- The grading of `Res_{ν,ν'} (ₛP) = 1_s R(ν + ν') 1_{ν,ν'}`, induced from `R(ν + ν')`. -/
def resRightGrading (s : Seq (ν + ν')) : ℤ → Submodule k (resRightSub Q ν ν' s) :=
  comap (G.grade (ν + ν')) (resRightSub Q ν ν' s).subtype

@[simp] theorem mem_resRightGrading {s : Seq (ν + ν')} {d : ℤ} {r : resRightSub Q ν ν' s} :
    r ∈ G.resRightGrading ν ν' s d ↔ (r : KLRAlgebra k Q (ν + ν')) ∈ G.grade (ν + ν') d :=
  Iff.rfl

theorem isInternal_resRightGrading (s : Seq (ν + ν')) :
    IsInternal (G.resRightGrading ν ν' s) :=
  isInternal_comap _ _ Subtype.val_injective fun r d =>
    ⟨⟨_, by
      refine ⟨?_, ?_⟩
      · have h := coe_decompose_mul_of_left_mem_zero (𝒜 := G.grade (ν + ν')) (j := d)
          (b := (r : KLRAlgebra k Q (ν + ν'))) (G.e_mem_grade s)
        rw [r.2.1] at h
        exact h.symm
      · have h := coe_decompose_mul_of_right_mem_zero (𝒜 := G.grade (ν + ν')) (i := d)
          (a := (r : KLRAlgebra k Q (ν + ν'))) (G.oneConcat_mem_grade (ν := ν) (ν' := ν'))
        rw [r.2.2] at h
        exact h.symm⟩, rfl⟩

instance (s : Seq (ν + ν')) : Decomposition (G.resRightGrading ν ν' s) :=
  (G.isInternal_resRightGrading s).chooseDecomposition

end Gradings

/-! ### The degree of the diagram of a shuffle, for right modules -/

section Degree

variable {μ : Multiset I}

/-- The degree of `1_s ψ_{ρ^{rev}} = ψ_{ρ^{rev}} 1_{w⁻¹ s}` (`w = wordProd ρ^{rev}`), the
reflection of the diagram `ψ_ρ 1_s`. -/
def degR (ρ : List ℕ) (s : Seq μ) : ℤ :=
  G.degW ρ.reverse ((wordProd (Multiset.card μ) ρ.reverse)⁻¹ • s)

theorem e_mul_ψw_reverse_mem_grade (ρ : List ℕ) (s : Seq μ) :
    (e s * ψw ρ.reverse : KLRAlgebra k Q μ) ∈ G.grade μ (G.degR ρ s) := by
  rw [e_mul_ψw]
  exact G.ψw_mul_e_mem_grade _ _

/-- For symmetric crossing degrees, `1_s ψ_{ρ^{rev}} = ψ(ψ_ρ 1_s)` has the degree `deg(ψ_ρ 1_s)`
of the diagram used for left modules. -/
theorem e_mul_ψw_reverse_mem_grade_of_symm (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a)
    (ρ : List ℕ) (s : Seq μ) :
    (e s * ψw ρ.reverse : KLRAlgebra k Q μ) ∈ G.grade μ (G.degW ρ s) := by
  have h := G.hflip_mem_grade hsymm (G.ψw_mul_e_mem_grade ρ s)
  rwa [hflip_mul, hflip_e, KLRAlgebra.hflip_ψw] at h

end Degree

/-! ### Proposition 2.19, second formula, graded -/

section Main

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

/-- The ungraded isomorphism of Proposition 2.19 (second formula) for the canonical reduced
words, `(t_u)_u ↦ ∑_u 1_s ψ_{σ(u)^{rev}} ι(t_u)`. -/
abbrev resProjEquivRightCan (s : Seq (ν + ν')) :
    ((u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2) ≃ₗ[k] resRightSub Q ν ν' s :=
  resProjEquivRight shuffleWord hPQ hP shuffleWord_spec (canWord _) (canWord _)
    (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
    (fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩) s

variable (ν ν') in
/-- The summand `ᵢP ⊗ ⱼP {δ u}`: the grading of `projPPR Q i_u j_u` shifted up by `δ u`, and the
grading of `⊕_u ᵢ₍ᵤ₎P ⊗ ⱼ₍ᵤ₎P {δ u}`. -/
def resRightDomGrading (s : Seq (ν + ν')) (δ : ShuffleOf ν ν' s → ℤ) :
    ℤ → Submodule k ((u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2) :=
  piGrading fun u => shift (G.projPPRGrading u.split.1 u.split.2) (δ u)

instance (s : Seq (ν + ν')) (δ : ShuffleOf ν ν' s → ℤ) :
    Decomposition (G.resRightDomGrading ν ν' s δ) := by
  unfold resRightDomGrading; infer_instance

/-- The map of Proposition 2.19 (second formula) is degree-preserving when the summand `u` is
shifted by a degree `δ u` of the diagram `1_s ψ_{σ(u)^{rev}}`. -/
theorem resProjEquivRightCan_mem (s : Seq (ν + ν')) (δ : ShuffleOf ν ν' s → ℤ)
    (hδ : ∀ u, (e s * ψw (shuffleWord u.1).reverse : KLRAlgebra k Q (ν + ν')) ∈
      G.grade (ν + ν') (δ u)) :
    PreservesGrading (G.resRightDomGrading ν ν' s δ) (G.resRightGrading ν ν' s)
      (resProjEquivRightCan hPQ hP s).toLinearMap := by
  intro d t ht
  rw [mem_resRightGrading, LinearEquiv.coe_toLinearMap, resProjEquivRight_apply]
  refine Submodule.sum_mem _ fun u _ => ?_
  have hu : ((t u : projPPR Q u.split.1 u.split.2) : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') ∈
      tensorGrading (G.grade ν) (G.grade ν') (d - δ u) := ht u
  have h2 := SetLike.GradedMul.mul_mem (A := G.grade (ν + ν')) (hδ u) (G.concat_mem_grade hu)
  rwa [add_sub_cancel] at h2

/-- **KL I, Proposition 2.19, second formula, graded, with a given choice of shifts**: if
`1_s ψ_{σ(u)^{rev}}` is homogeneous of degree `δ u` for every shuffle `u`, then
`⊕_u ᵢ₍ᵤ₎P ⊗ ⱼ₍ᵤ₎P {δ u} ≅ Res_{ν,ν'} (ₛP)` as graded vector spaces, by the right
`R(ν) ⊗ R(ν')`-linear isomorphism `resProjEquivRight` (`resProjGradedEquivRight_mul`). -/
def resProjGradedEquivRightOf (s : Seq (ν + ν')) (δ : ShuffleOf ν ν' s → ℤ)
    (hδ : ∀ u, (e s * ψw (shuffleWord u.1).reverse : KLRAlgebra k Q (ν + ν')) ∈
      G.grade (ν + ν') (δ u)) :
    GradedEquiv k (G.resRightDomGrading ν ν' s δ) (G.resRightGrading ν ν' s) :=
  GradedEquiv.ofPreserves (resProjEquivRightCan hPQ hP s)
    (G.resProjEquivRightCan_mem hPQ hP s δ hδ)

@[simp] theorem resProjGradedEquivRightOf_apply (s : Seq (ν + ν')) (δ : ShuffleOf ν ν' s → ℤ)
    (hδ : ∀ u, (e s * ψw (shuffleWord u.1).reverse : KLRAlgebra k Q (ν + ν')) ∈
      G.grade (ν + ν') (δ u))
    (t : (u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2) :
    G.resProjGradedEquivRightOf hPQ hP s δ hδ t = resProjEquivRightCan hPQ hP s t := rfl

/-- The graded isomorphism of Proposition 2.19 (second formula) intertwines the right actions of
`R(ν) ⊗ R(ν')`: `Φ((t_u c)_u) = Φ((t_u)_u) ι(c)`. -/
theorem resProjGradedEquivRight_mul (s : Seq (ν + ν')) (δ : ShuffleOf ν ν' s → ℤ)
    (hδ : ∀ u, (e s * ψw (shuffleWord u.1).reverse : KLRAlgebra k Q (ν + ν')) ∈
      G.grade (ν + ν') (δ u))
    (t : (u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2)
    (c : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    ((G.resProjGradedEquivRightOf hPQ hP s δ hδ (fun u =>
      ⟨(t u : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') * c, mul_mem_projPPR (t u).2 c⟩) :
        resRightSub Q ν ν' s) : KLRAlgebra k Q (ν + ν')) =
      (G.resProjGradedEquivRightOf hPQ hP s δ hδ t : KLRAlgebra k Q (ν + ν')) *
        concat Q ν ν' c :=
  resProjEquivRight_mul shuffleWord hPQ hP shuffleWord_spec (canWord _) (canWord _)
    (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
    (fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩) s t c

/-- **KL I, Proposition 2.19, second formula, graded** (any grading datum):
`Res_{ν,ν'} (ₛP) ≅ ⊕_u ᵢ₍ᵤ₎P ⊗ ⱼ₍ᵤ₎P {deg(1_s ψ_{σ(u)^{rev}})}`. -/
def resProjGradedEquivRight (s : Seq (ν + ν')) :
    GradedEquiv k (G.resRightDomGrading ν ν' s fun u => G.degR (shuffleWord u.1) s)
      (G.resRightGrading ν ν' s) :=
  G.resProjGradedEquivRightOf hPQ hP s _ fun _ => G.e_mul_ψw_reverse_mem_grade _ s

/-- **KL I, Proposition 2.19, second formula, graded**, with the printed shifts: for symmetric
crossing degrees,
`Res_{ν,ν'} (ₛP) ≅ ⊕_u ᵢ₍ᵤ₎P ⊗ ⱼ₍ᵤ₎P {deg(i_u, j_u, s)}`, `deg(i_u, j_u, s) = deg(ψ_{σ(u)} 1_s)`,
the same shifts as in the first formula (`GradingDatum.resProjGradedEquiv`). -/
def resProjGradedEquivRight_of_symm (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a)
    (s : Seq (ν + ν')) :
    GradedEquiv k (G.resRightDomGrading ν ν' s fun u => G.degW (shuffleWord u.1) s)
      (G.resRightGrading ν ν' s) :=
  G.resProjGradedEquivRightOf hPQ hP s _ fun _ =>
    G.e_mul_ψw_reverse_mem_grade_of_symm hsymm _ s

end Main

end GradingDatum

namespace KL1

variable (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

/-- **KL I, Proposition 2.19, second formula, graded, for KL I's grading**: for
`s ∈ Seq(ν + ν')`, `Res_{ν,ν'} (ₛP) ≅ ⊕_u ᵢ₍ᵤ₎P ⊗ ⱼ₍ᵤ₎P {deg(i_u, j_u, s)}` as graded right
`R(ν) ⊗ R(ν')`-modules (right linearity: `GradingDatum.resProjGradedEquivRight_mul`). -/
def resProjGradedEquivRight (s : Seq (ν + ν')) :
    GradedEquiv k ((klGradingDatum k Γ).resRightDomGrading ν ν' s
        fun u => (klGradingDatum k Γ).degW (shuffleWord u.1) s)
      ((klGradingDatum k Γ).resRightGrading ν ν' s) :=
  (klGradingDatum k Γ).resProjGradedEquivRight_of_symm (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b) (fun a b => by
      show -cartan Γ a b = -cartan Γ b a
      rw [cartan_symm]) s

end KL1

end Categorification.KLR
