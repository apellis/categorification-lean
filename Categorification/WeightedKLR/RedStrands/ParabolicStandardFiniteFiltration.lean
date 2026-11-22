/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardProjectiveFiltration
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFinite

/-!
# Filtrations by standardizations with finite-dimensional layers

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 5.20. The filtration of `F_w S(N)` by standardizations
(`hasFiltration_blackWord_stdLayer`) uses injectivity of `δ₁` in Proposition 5.5 for every
layer it meets. Webster's dimension count proves this injectivity for finite-dimensional
input modules. This file checks that only finite-dimensional layers occur: for Rouquier
parameters the inductions `₁Fᵢ N` and `₂Fᵢ N` of a finite-dimensional `N` are
finite-dimensional, and so is the red layer `T^{λ'} e(s)`. The filtrations therefore need the
route hypothesis only for finite-dimensional layers (`AllFiniteDeltaInjective`).

## Main definitions

* `StdLayer.IsFiniteDim`: the input module of a layer is finite-dimensional.
* `AllFiniteDeltaInjective`: injectivity of `δ₁` for every finite-dimensional input module.

## Main results

* `parabolicFactorAlgebra_finite`: `T^{λ'}_θ ⊗ R^{λ_ℓ}_β` is finite-dimensional.
* `StdLayer.isFiniteDim_of_mem_wordLayers`: the layers of `F_w S(N)` are finite-dimensional
  when `N` is.
* `isFiniteDim_redLayer`: the red layer `T^{λ'} e(s)` is finite-dimensional.
* `HasFiltration.blackWord_of_finite`, `hasFiltration_blackWord_stdLayer_of_finite`,
  `hasFiltration_loadingProj_of_finite`: the filtrations of
  `ParabolicStandardFiltration` and `ParabolicStandardProjectiveFiltration` under
  `AllFiniteDeltaInjective`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra InductionAlong MulOpposite ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ}
  {C : QuantumGroup.CartanDatum I}

local notation "Si" j => (Singleton.singleton j : Multiset I)

section Finite

variable (Λ) in
/-- **`T^{λ'}_θ ⊗ R^{λ_ℓ}_β` is finite-dimensional** for Rouquier parameters (Webster,
arXiv:1309.3796v2, Theorem 4.38 for `T^{λ'}`; Kang–Kashiwara, Corollary 4.4 for the
cyclotomic factor). -/
theorem parabolicFactorAlgebra_finite (hR : IsRouquierQ C Q) (θ β : Multiset I) :
    Module.Finite k (parabolicFactorAlgebra Q Λ θ β) :=
  have := tensorProductAlgebra_finite (Q := Q) (Λ ∘ Fin.castSucc) θ hR
  have := CycKLR.module_finite (ν := β) (Q := Q) (fun i j hij => by
    obtain ⟨c, hc, h⟩ := hR.polyInY_leading i j hij
    rw [h]
    exact hc.map Polynomial.C) (fun j => Polynomial.monic_X_pow (Λ (Fin.last ℓ) j))
  inferInstance

variable (i : I) (θ β : Multiset I) (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]

/-- **`₁Fᵢ N` is finite-dimensional when `N` is**, for Rouquier parameters. -/
theorem finiteDimensional_firstIndLeft (hR : IsRouquierQ C Q) [FiniteDimensional k N] :
    FiniteDimensional k (FirstIndLeft Q Λ i θ β N) :=
  have : Module.Finite (parabolicFactorAlgebra Q Λ θ β) N :=
    Module.Finite.of_restrictScalars_finite k _ N
  have := parabolicFactorAlgebra_finite Λ hR ((Si i) + θ) β
  IndK.finite_restrict k N _

/-- **`₂Fᵢ N` is finite-dimensional when `N` is**, for Rouquier parameters. -/
theorem finiteDimensional_lastIndRight (hR : IsRouquierQ C Q) [FiniteDimensional k N] :
    FiniteDimensional k (LastIndRight Q Λ i θ β N) :=
  have : Module.Finite (parabolicFactorAlgebra Q Λ θ β) N :=
    Module.Finite.of_restrictScalars_finite k _ N
  have := parabolicFactorAlgebra_finite Λ hR θ ((Si i) + β)
  IndK.finite_restrict k N _

end Finite

/-! ### Finite-dimensional layers -/

variable (Q Λ) in
/-- The input module of the standard layer `c` is finite-dimensional. -/
def StdLayer.IsFiniteDim {ν : Multiset I} (c : StdLayer Q Λ ν) : Prop :=
  FiniteDimensional k c.M.carrier

variable (Q Λ) in
/-- **The route hypothesis of Proposition 5.5 for finite-dimensional inputs**: injectivity of
`δ₁ : S(₁Fᵢ N) → Fᵢ S(N)` for every finite-dimensional module `N` over
`T^{λ'}_θ ⊗ R^{λ_ℓ}_β`. -/
def AllFiniteDeltaInjective (hQ : KLRSymm Q) : Prop :=
  ∀ (i : I) (θ β : Multiset I) (M : FactorModule Q Λ θ β), FiniteDimensional k M.carrier →
    FirstIndDeltaInjective Q Λ i θ β M.carrier hQ

/-- The unrestricted route hypothesis implies the finite-dimensional one. -/
theorem AllDeltaInjective.allFiniteDeltaInjective {hQ : KLRSymm Q}
    (h : AllDeltaInjective Q Λ hQ) : AllFiniteDeltaInjective Q Λ hQ :=
  fun i θ β M _ => h i θ β M

variable (hR : IsRouquierQ C Q)
include hR

/-- The layer `₁Fᵢ N` is finite-dimensional when `N` is. -/
theorem StdLayer.isFiniteDim_first (i : I) {ν : Multiset I} {c : StdLayer Q Λ ν}
    (hc : c.IsFiniteDim Q Λ) : (c.first Q Λ i).IsFiniteDim Q Λ :=
  have : FiniteDimensional k c.M.carrier := hc
  finiteDimensional_firstIndLeft i c.θ c.β c.M.carrier hR

/-- The layer `₂Fᵢ N` is finite-dimensional when `N` is. -/
theorem StdLayer.isFiniteDim_last (i : I) {ν : Multiset I} {c : StdLayer Q Λ ν}
    (hc : c.IsFiniteDim Q Λ) : (c.last Q Λ i).IsFiniteDim Q Λ :=
  have : FiniteDimensional k c.M.carrier := hc
  finiteDimensional_lastIndRight i c.θ c.β c.M.carrier hR

/-- The two layers `₂Fᵢ N`, `₁Fᵢ N` of `Fᵢ S(N)` are finite-dimensional when `N` is. -/
theorem StdLayer.isFiniteDim_of_mem_blackIndLayers (i : I) {ν : Multiset I}
    {c : StdLayer Q Λ ν} (hc : c.IsFiniteDim Q Λ) {c' : StdLayer Q Λ ((Si i) + ν)}
    (h : c' ∈ c.blackIndLayers Q Λ i) : c'.IsFiniteDim Q Λ := by
  simp only [StdLayer.blackIndLayers, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact StdLayer.isFiniteDim_last hR i hc
  · exact StdLayer.isFiniteDim_first hR i hc

/-- **The layers of `F_w S(N)` are finite-dimensional when `N` is** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.20). -/
theorem StdLayer.isFiniteDim_of_mem_wordLayers (w : List I) {ν : Multiset I}
    {c : StdLayer Q Λ ν} (hc : c.IsFiniteDim Q Λ) {c' : StdLayer Q Λ (wordWt w ν)}
    (h : c' ∈ c.wordLayers Q Λ w) : c'.IsFiniteDim Q Λ := by
  induction w with
  | nil =>
    simp only [StdLayer.wordLayers, List.mem_singleton] at h
    exact h ▸ hc
  | cons j w ih =>
    simp only [StdLayer.wordLayers, List.mem_flatMap] at h
    obtain ⟨d, hd, h⟩ := h
    exact StdLayer.isFiniteDim_of_mem_blackIndLayers hR j (ih hd) h

omit hR in
/-- **The red layer `T^{λ'} e(s)` is finite-dimensional**, for Rouquier parameters. -/
theorem isFiniteDim_redLayer (hR : IsRouquierQ C Q) (θ : Multiset I)
    (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    (redLayer Q Λ θ s hs).IsFiniteDim Q Λ := by
  have := tensorProductAlgebra_finite (Q := Q) (Λ ∘ Fin.castSucc) (θ + 0) hR
  change FiniteDimensional k (lIdeal (oldIdem Q Λ θ s hs))
  exact Module.Finite.of_injective
    ((lIdeal (oldIdem Q Λ θ s hs)).subtype.restrictScalars k) Subtype.val_injective

variable {hQ : KLRSymm Q}

/-- **`F_w` refines filtrations by finite-dimensional standard layers** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.20), given the route hypothesis
`FirstIndDeltaInjective` for finite-dimensional layers only. -/
theorem HasFiltration.blackWord_of_finite (hall : AllFiniteDeltaInjective Q Λ hQ)
    (w : List I) {ν : Multiset I} {m : List (StdLayer Q Λ ν)}
    {X : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)}
    (h : HasFiltration (stdLayerModule Q Λ hQ) m X) (hm : ∀ c ∈ m, c.IsFiniteDim Q Λ) :
    HasFiltration (stdLayerModule Q Λ hQ) (m.flatMap (StdLayer.wordLayers Q Λ w))
      (blackWordModule Q Λ w X) := by
  induction w with
  | nil => simpa [StdLayer.wordLayers, blackWordModule] using h
  | cons j w ih =>
    have := HasFiltration.blackInd j C hR ih (fun c hc => by
      simp only [List.mem_flatMap] at hc
      obtain ⟨d, hd, hc⟩ := hc
      exact hall j c.θ c.β c.M (StdLayer.isFiniteDim_of_mem_wordLayers hR w (hm d hd) hc))
    simpa [StdLayer.wordLayers, blackWordModule, List.flatMap_assoc] using this

/-- **`F_w S(N)` has a filtration by standardizations for finite-dimensional `N`** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.20), given the route hypothesis
`FirstIndDeltaInjective` for finite-dimensional layers only. -/
theorem hasFiltration_blackWord_stdLayer_of_finite (hall : AllFiniteDeltaInjective Q Λ hQ)
    (w : List I) {ν : Multiset I} (c : StdLayer Q Λ ν) (hc : c.IsFiniteDim Q Λ) :
    HasFiltration (stdLayerModule Q Λ hQ) (c.wordLayers Q Λ w)
      (blackWordModule Q Λ w (stdLayerModule Q Λ hQ c)) := by
  simpa using HasFiltration.blackWord_of_finite hR hall w (HasFiltration.single
    (L := stdLayerModule Q Λ hQ) (LinearEquiv.refl _ (stdLayerModule Q Λ hQ c)))
    (by simpa using hc)

/-- **Filtration of `T^λ e(s, λ_ℓ, w)` by standardizations** (Webster, arXiv:1309.3796v2,
proof of Proposition 5.20), given the route hypothesis `FirstIndDeltaInjective` for
finite-dimensional layers only. -/
theorem hasFiltration_loadingProj_of_finite (hall : AllFiniteDeltaInjective Q Λ hQ)
    (w : List I) {θ : Multiset I} (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    HasFiltration (stdLayerModule Q Λ hQ) ((redLayer Q Λ θ s hs).wordLayers Q Λ w)
      (loadingProj Q Λ (blackWordLoading w (appendRedLoading s))
        (blackWordLoading_ordered w _ ((appendRedLoading_ordered_iff s).2 hs))) :=
  HasFiltration.of_equiv (hasFiltration_blackWord_stdLayer_of_finite hR hall w
      (redLayer Q Λ θ s hs) (isFiniteDim_redLayer hR θ s hs))
    ((loadingProjWordEquiv Q Λ w (appendRedLoading s)
      ((appendRedLoading_ordered_iff s).2 hs)).trans
      (blackWordMapEquiv Q Λ w (loadingProjRedEquiv Q Λ θ hQ s hs))).symm

end Categorification.Stendhal
