/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidRigidStandard
import Categorification.WeightedKLR.RedStrands.RightStandardRelabel
import Categorification.WeightedKLR.RedStrands.BlockCrossingRigid

/-!
# The braid of a standard module at a Figure 5 row loading

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Corollary 6.10, using Proposition 6.9.
Let the red order `(1, …, ℓ) = κ₁ = L ++ f 1 :: f 0 :: M`, and let `π` be a permutation with
`π(1, …, ℓ) = κ₀ = L ++ f 0 :: f 1 :: M`. Let `t` be a row loading whose distinguished block
carries the crossed Figure 5 loading, and `t'` the row loading with the uncrossed loading in that
block, written `t' = π s'` for a loading `s'` of `(1, …, ℓ)` with labels `λ ∘ π`. Then the braid
`B ⊗ (e(t) T^λ / U_t)` is the standard module `e(s') T^{λ ∘ π} / U_{s'}` as right
`T^{λ ∘ π}`-modules (`rowBraidStandardEquiv`). It composes:
relabelling the red strands (`rightStandardRelabel`), the standard module at `t'` as the cut
quotient at `t` (`rowBraidCutEquivStandard`, Proposition 6.9), and the cut quotient as the braid
at a rigid cut (`braidRigidStandardEquiv`).

The hypothesis `hstd` (`StackedStandard`) is that of `rowBraidCutEquivStandard`.
-/

noncomputable section

namespace Categorification.Stendhal.RedBlock

open KLR BraidedStendhalAlgebra MulOpposite Categorification.Graded Equiv

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)

local notation "m₂" => Multiset.card (stendhalWeight 2 β)

local instance rowCornerRing {ν : Multiset I} (κ : List (Fin ℓ)) :
    Ring (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ) := _root_.instRingCorner _ _


/-- The additive isomorphism underlying `rowBraidStandardEquiv`. -/
def rowBraidStandardAddEquiv {ρ₂ : Equiv.Perm (Fin m₂) → List ℕ}
    (hρ₂ : TypeA.IsReducedChoice ρ₂) {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)}
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
    {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) (π : Perm (Fin ℓ))
    (hord : List.finRange ℓ = L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hκ : (List.finRange ℓ).map π = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)
    {s' : Seq (stendhalWeight ℓ ν)} (hs' : redWord s' = List.finRange ℓ)
    (hts : Seq.redPerm π s' = Seq.cast h (place _ (setPairLoading M f β t₂ L u))) :
    RightStandard (Λ ∘ π) hρ hQ s' ≃+
      BalancedTensor k (TensorProductAlgebra k Q (Λ ∘ π) ν)ᵐᵒᵖ (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ
        (braidBimod Q Λ ν hρ hQ π) (RightStandard Λ hρ hQ
        (Seq.cast h (place _ (setPairLoading M f β σ L u)))) :=
  (rightStandardRelabel π hρ hQ hs').trans ((loadingStandardCongr hts hκ).trans
    ((rowBraidCutEquivStandard Q Λ hQ M f β hρ₂ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht
      hstd).toAddEquiv.trans
      (braidRigidStandardEquiv (Λ := Λ) hρ hQ π _ (f 0) (f 1) (ht.trans hord.symm) hord hκ
        (isRigidCut_place_setPairLoading M f β hb L h u hs ht)).symm.toAddEquiv))

theorem rowBraidStandardAddEquiv_apply {ρ₂ : Equiv.Perm (Fin m₂) → List ℕ}
    (hρ₂ : TypeA.IsReducedChoice ρ₂) {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)}
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
    {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) (π : Perm (Fin ℓ))
    (hord : List.finRange ℓ = L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hκ : (List.finRange ℓ).map π = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)
    {s' : Seq (stendhalWeight ℓ ν)} (hs' : redWord s' = List.finRange ℓ)
    (hts : Seq.redPerm π s' = Seq.cast h (place _ (setPairLoading M f β t₂ L u)))
    (z : RightStandard (Λ ∘ π) hρ hQ s') :
    rowBraidStandardAddEquiv Q Λ hQ M f β hρ₂ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd hρ π hord hκ
        hs' hts z =
      braidRigidStandardInv (Λ := Λ) hρ hQ π _ (f 0) (f 1) (ht.trans hord.symm) hord
        (isRigidCut_place_setPairLoading M f β hb L h u hs ht)
        (rowBraidCutEquivStandard Q Λ hQ M f β hρ₂ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd
          (loadingStandardCongr hts hκ (rightStandardRelabel π hρ hQ hs' z))) := rfl

theorem rowBraidStandardAddEquiv_smul {ρ₂ : Equiv.Perm (Fin m₂) → List ℕ}
    (hρ₂ : TypeA.IsReducedChoice ρ₂) {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)}
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
    {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) (π : Perm (Fin ℓ))
    (hord : List.finRange ℓ = L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hκ : (List.finRange ℓ).map π = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)
    {s' : Seq (stendhalWeight ℓ ν)} (hs' : redWord s' = List.finRange ℓ)
    (hts : Seq.redPerm π s' = Seq.cast h (place _ (setPairLoading M f β t₂ L u)))
    (v : (TensorProductAlgebra k Q (Λ ∘ π) ν)ᵐᵒᵖ) (z : RightStandard (Λ ∘ π) hρ hQ s') :
    rowBraidStandardAddEquiv Q Λ hQ M f β hρ₂ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd hρ π hord hκ
        hs' hts (v • z) =
      v • rowBraidStandardAddEquiv Q Λ hQ M f β hρ₂ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd hρ π
        hord hκ hs' hts z := by
  let c₁ : (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ((List.finRange ℓ).map π))ᵐᵒᵖ :=
    op (violCornerRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ π) (Λ := Λ) (ν := ν) π
      (fun _ => rfl) (List.finRange ℓ) ((violCornerEquiv hρ hQ).symm v.unop))
  let c₂ : (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst))ᵐᵒᵖ := op (cornerCast hκ c₁.unop)
  rw [rowBraidStandardAddEquiv_apply, rowBraidStandardAddEquiv_apply,
    rightStandardRelabel_smul π hρ hQ hs' v c₁ rfl,
    loadingStandardCongr_smul hts hκ c₁ c₂ (cornerCast_val _ _), map_smul,
    braidRigidStandardInv_smul hρ hQ π _ _ _ v c₂ (cornerCast_val _ _)]

/-- **The braid of a standard module at a Figure 5 row loading** (Webster, arXiv:1309.3796v2,
§6.1, Proposition 6.9 and proof of Corollary 6.10, ungraded): with `t` the placed crossed loading
of red order `(1, …, ℓ) = L ++ f 1 :: f 0 :: M`, `π(1, …, ℓ) = L ++ f 0 :: f 1 :: M`, and the
placed uncrossed loading equal to `π s'`, the braid `B ⊗ (e(t) T^λ / U_t)` is the standard module
`e(s') T^{λ ∘ π} / U_{s'}` as right `T^{λ ∘ π}`-modules.

The hypothesis `hstd` is `StackedStandard`, an explicit hypothesis of `rowBraidCutEquivStandard`
tracked for removal. -/
def rowBraidStandardEquiv {ρ₂ : Equiv.Perm (Fin m₂) → List ℕ}
    (hρ₂ : TypeA.IsReducedChoice ρ₂) {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)}
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
    {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) (π : Perm (Fin ℓ))
    (hord : List.finRange ℓ = L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hκ : (List.finRange ℓ).map π = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)
    {s' : Seq (stendhalWeight ℓ ν)} (hs' : redWord s' = List.finRange ℓ)
    (hts : Seq.redPerm π s' = Seq.cast h (place _ (setPairLoading M f β t₂ L u))) :
    RightStandard (Λ ∘ π) hρ hQ s' ≃ₗ[(TensorProductAlgebra k Q (Λ ∘ π) ν)ᵐᵒᵖ]
      BalancedTensor k (TensorProductAlgebra k Q (Λ ∘ π) ν)ᵐᵒᵖ (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ
        (braidBimod Q Λ ν hρ hQ π) (RightStandard Λ hρ hQ
        (Seq.cast h (place _ (setPairLoading M f β σ L u)))) :=
  (rowBraidStandardAddEquiv Q Λ hQ M f β hρ₂ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd hρ π hord hκ
    hs' hts).toLinearEquiv
    (rowBraidStandardAddEquiv_smul Q Λ hQ M f β hρ₂ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd hρ π
      hord hκ hs' hts)

end Categorification.Stendhal.RedBlock
