/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingRowStandard

/-!
# The braid of a partial standard at a Figure 5 row loading

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 (v3: Proposition
6.10), steps 2 and 3 combined. Let `s` be a row loading whose distinguished block carries the
crossed Figure 5 loading, and `s'` the row loading with the uncrossed Figure 5 loading in that
block. The derived braid of the partial standard of Lemma 6.8 at `s` is, in degree zero, the
standard module of Definition 5.1 at `s'` (`rowPartialStandard_braidIso`).

It carries the two hypotheses of Lemma 6.8 and the hypothesis `StackedStandard` (partial
standardization of the local standard is the global standard).
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open CategoryTheory KLR BraidedStendhalAlgebra MulOpposite DG DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe v w
variable {k : Type v} [CommRing k]
variable {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
local notation "m₂" => Multiset.card (stendhalWeight 2 β)

/-- **The braid of a partial standard at a Figure 5 row loading** (Webster,
arXiv:1309.3796v2, §6.1, proof of Proposition 6.9). With `t` the placed crossed loading and `t'`
the placed uncrossed loading, the derived braid from `κ₁ = L ++ f 1 :: f 0 :: M` to
`κ₀ = L ++ f 0 :: f 1 :: M` of the partial standard at `t` is the standard module at `t'` in
degree zero.

The hypotheses `hfilt` and `hinj` are those of Lemma 6.8 (`blockPartialStandard_braidIso`),
and `hstd` is `StackedStandard`; each is an explicit hypothesis tracked for removal. -/
def rowPartialStandard_braidIso {ρ : Equiv.Perm (Fin m₂) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)}
    (h1 : 1 < m₂) (ht₀ : t₂.lbl ⟨0, by omega⟩ = .inr 0) (ht₁ : t₂.lbl ⟨1, h1⟩ = .inr 1)
    (hb : EdgeBraid (show 0 < m₂ by omega) 0 g σ t₂) (hσ : redWord σ = [1, 0])
    (ht₂ : redWord t₂ = [0, 1]) (L : List (Fin ℓ × Multiset I)) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν) (u : Loadings (adjacentRow L M f β))
    (hs : ¬ Violated _ (setPairLoading M f β σ L u))
    (ht : redWord (Seq.cast h (place _ (setPairLoading M f β σ L u))) =
      L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hstd : StackedStandard hQ h (rowRelations Q Λ hQ M f β
      (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e t₂)) (pairRelations Q Λ hQ f β t₂) L u)
      (setPairLoading M f β t₂ L u))
    [HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
      (redWord (Seq.cast h (place _ (setPairLoading M f β σ L u))))))ᵐᵒᵖ]
    [HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
      (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)))ᵐᵒᵖ]
    (hfilt : ∀ (s : Seq (stendhalWeight ℓ ν))
      (hs : redWord s = redWord (Seq.cast h (place _ (setPairLoading M f β σ L u)))),
      ∃ m : List {v : Seq (stendhalWeight ℓ ν) //
        redWord v = redWord (Seq.cast h (place _ (setPairLoading M f β σ L u)))},
      (∀ v ∈ m, adjacentBlockRoot (f 0) (f 1) s < adjacentBlockRoot (f 0) (f 1) v.1) ∧
      ModuleFiltration.HasFiltration
        (fun v => blockPartialStandardAt Q Λ v.1 (f 0) (f 1)
          (redWord (Seq.cast h (place _ (setPairLoading M f β σ L u)))) v.2) m
        (blockLoadingKernelObjAt Q Λ (f 0) (f 1)
          (redWord (Seq.cast h (place _ (setPairLoading M f β σ L u)))) s hs))
    (hinj : ∀ s : Seq (stendhalWeight ℓ ν),
      redWord s = redWord (Seq.cast h (place _ (setPairLoading M f β σ L u))) →
      Function.Injective (blockKernelTensorInclusion Q Λ s (f 0) (f 1)
        (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst))) :
    (braidingFunctor.{w} k Q Λ ν (redWord (Seq.cast h (place _ (setPairLoading M f β σ L u))))
        (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
          (blockLoadingShortComplex Q Λ (Seq.cast h (place _ (setPairLoading M f β σ L u)))
            (f 0) (f 1)).X₃)) ≅
      DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj (ModuleCat.of _
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ)
          (Seq.cast h (place _ (setPairLoading M f β t₂ L u)))
          (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)))) :=
  blockPartialStandard_braidIso ht rfl hfilt hinj ≪≫
    DG.DerivedCategory.Q.mapIso ((degreeZeroModuleFunctor _).mapIso
      (rowBraidCutEquivStandard Q Λ hQ M f β hρ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht
        hstd).symm.toModuleIso)

end Categorification.Stendhal.RedBlock
