/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer

/-!
# The braid on partial standards is concentrated in degree zero

B. Webster, *Knot invariants and higher representation theory*,
[arXiv:1309.3796v2](https://arxiv.org/abs/1309.3796v2), §6.1, Lemma 6.8
(v3: Lemma 6.9), the part of the proof that runs through (6.21).

Fix an adjacent red pair `a, b` and a red order `κ`. For every loading `s` with red word `κ`
the braid functor `B_j` applied to the partial standard at `s` has no cohomology outside
degree zero. The proof is Webster's induction on the preorder of loadings: the loading
projective at `s` surjects onto the partial standard, its kernel is filtered by partial
standards at strictly higher loadings, and the long exact sequence (6.21) gives the
vanishing once the degree-zero map `H⁰(B_j(K)) → H⁰(B_j(P))` is injective.

Two inputs of Webster's argument are hypotheses here.

* `hfilt`: the kernel of the loading projective onto the partial standard is filtered by
  partial standards at strictly higher loadings. Webster uses this without proof; §5
  proves the corresponding statement for full standardization (Proposition 5.20).
* `hinj`: the ordinary balanced tensor of the kernel inclusion with the braiding bimodule
  is injective. Webster's cut argument after (6.21) does not handle the dotted
  relations in general.

The roadmap tracks the removal of both hypotheses.

## Main results

* `blockPartialStandardAt_braid_homology_vanish`: one step of the induction, at a loading
  placed in the corner of an equal red word.
* `blockPartialStandardAt_braid_homology_vanish_of_kernel_filtrations`: the vanishing for
  every loading of red word `κ`, from `hfilt` and `hinj`.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w u v

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (a b : Fin ℓ)
    (κ κ' : List (Fin ℓ))
    [HasDerivedCategory.{w, max u v} (isIdempotentElem_violMk_redProj k Q Λ ν κ).Cornerᵐᵒᵖ]
    [HasDerivedCategory.{w, max u v} (isIdempotentElem_violMk_redProj k Q Λ ν κ').Cornerᵐᵒᵖ]

local notation "μ" => stendhalWeight ℓ ν
local notation "C" => (isIdempotentElem_violMk_redProj k Q Λ ν κ).Corner
local notation "D" => (isIdempotentElem_violMk_redProj k Q Λ ν κ').Corner
local notation "F" => braidingFunctor k Q Λ ν κ κ'

set_option backward.isDefEq.respectTransparency false in
/-- One step of the induction through (6.21) in Webster's Lemma 6.8, for a loading `s` placed
in the corner of an equal red word `κ`. -/
theorem blockPartialStandardAt_braid_homology_vanish (s : Seq μ) (hs : redWord s = κ)
    {ι : Type*} {L : ι → ModuleCat Cᵐᵒᵖ} {m : List ι}
    (hK : ModuleFiltration.HasFiltration L m
      (ModuleCat.of Cᵐᵒᵖ (blockLoadingKernelAt Q Λ s a b κ hs)))
    (hL : ∀ c ∈ m, ∀ n : ℤ, n ≠ 0 → IsZero
      ((DG.DerivedCategory.homologyFunctor (A := Dᵐᵒᵖ) ℤ n).obj
        ((F).obj (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Cᵐᵒᵖ).obj (L c))))))
    (hi : Function.Injective (blockKernelTensorInclusion Q Λ s a b κ'))
    (n : ℤ) (hn : n ≠ 0) : IsZero
      ((DG.DerivedCategory.homologyFunctor (A := Dᵐᵒᵖ) ℤ n).obj
        ((F).obj (DG.DerivedCategory.Q.obj
          ((degreeZeroModuleFunctor Cᵐᵒᵖ).obj (blockPartialStandardAt Q Λ s a b κ hs))))) := by
  subst hs
  exact blockPartialStandard_braid_homology_vanish Q Λ s a b κ' hK hL hi n hn

set_option backward.isDefEq.respectTransparency false in
/-- **Webster, arXiv:1309.3796v2, Lemma 6.8, higher cohomology** (v3: Lemma 6.9). For every
loading `s` of red word `κ`, the braid of the partial standard at `s` has no cohomology outside
degree zero.

The hypotheses `hfilt` (the kernel at each loading is filtered by partial standards at strictly
higher loadings) and `hinj` (injectivity of the balanced kernel inclusion in (6.21)) are inputs
of Webster's proof that are not yet formalized; see the module docstring. -/
theorem blockPartialStandardAt_braid_homology_vanish_of_kernel_filtrations
    (hfilt : ∀ (s : Seq μ) (hs : redWord s = κ), ∃ m : List {u : Seq μ // redWord u = κ},
      (∀ u ∈ m, adjacentBlockRoot a b s < adjacentBlockRoot a b u.1) ∧
      ModuleFiltration.HasFiltration (fun u => blockPartialStandardAt Q Λ u.1 a b κ u.2) m
        (ModuleCat.of Cᵐᵒᵖ (blockLoadingKernelAt Q Λ s a b κ hs)))
    (hinj : ∀ s : Seq μ, redWord s = κ →
      Function.Injective (blockKernelTensorInclusion Q Λ s a b κ'))
    (s : Seq μ) (hs : redWord s = κ) (n : ℤ) (hn : n ≠ 0) : IsZero
      ((DG.DerivedCategory.homologyFunctor (A := Dᵐᵒᵖ) ℤ n).obj
        ((F).obj (DG.DerivedCategory.Q.obj
          ((degreeZeroModuleFunctor Cᵐᵒᵖ).obj (blockPartialStandardAt Q Λ s a b κ hs))))) := by
  let r : Seq μ → Seq μ → Prop := fun t s => adjacentBlockRoot a b s < adjacentBlockRoot a b t
  have : IsTrans (Seq μ) r := ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
  have : IsIrrefl (Seq μ) r := ⟨fun _ h => lt_irrefl _ h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  suffices H : ∀ s : Seq μ, ∀ hs : redWord s = κ, ∀ n : ℤ, n ≠ 0 → IsZero
      ((DG.DerivedCategory.homologyFunctor (A := Dᵐᵒᵖ) ℤ n).obj
        ((F).obj (DG.DerivedCategory.Q.obj
          ((degreeZeroModuleFunctor Cᵐᵒᵖ).obj (blockPartialStandardAt Q Λ s a b κ hs))))) from
    H s hs n hn
  intro s
  induction s using hwf.induction with
  | _ s ih =>
    intro hs n hn
    obtain ⟨m, hm, hK⟩ := hfilt s hs
    exact blockPartialStandardAt_braid_homology_vanish Q Λ a b κ κ' s hs hK
      (fun u hu n hn => ih u.1 (hm u hu) u.2 n hn) (hinj s hs) n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
