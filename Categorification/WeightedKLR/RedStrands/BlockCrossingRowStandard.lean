/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingStandard
import Categorification.WeightedKLR.RedStrands.BlockPairedCrossingLoading

/-!
# The Figure 5 generator of a row

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 (v3: Proposition
6.10), the reduction to two red strands. In a row whose distinguished block carries the two-red
Figure 5 loadings, the generator of the crossing bimodule (`crossingProduct_generator`) has
as top and bottom idempotents the loading idempotents of the row loadings with the two local
loadings inserted (`rowTop_eq_projection`, `orderedInclusion_rowTau`). Hence the cut quotient
of step 2 at the top loading is the standard module at the bottom loading, under the explicit
hypothesis `StackedStandard` (`rowBraidCutEquivStandard`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Categorification.Stendhal.RedBlock
open KLR BraidedStendhalAlgebra MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe v
variable {k : Type v} [CommRing k]
variable {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)
local notation "topOrd" => (fun (_ : RedBlock I ℓ) => Fin.revPerm)
local notation "B₂" => (RedBlock.mk 2 f β : RedBlock I ℓ)
local notation "q₂" => violMk k Q (Λ ∘ f) β
local notation "ι₂" => ofKLR k Q (Λ ∘ f) β

/-- Replace the loading of the distinguished block of a row. -/
def setPairLoading (σ : Seq (B₂).localWeight) :
    (L : List (Fin ℓ × Multiset I)) → Loadings (adjacentRow L M f β) →
      Loadings (adjacentRow L M f β)
  | [], s => (σ, s.2)
  | _ :: L, s => (s.1, setPairLoading σ L s.2)

omit [DecidableEq I] in
theorem pairLoading_setPairLoading (σ : Seq (B₂).localWeight) :
    ∀ L (s : Loadings (adjacentRow L M f β)),
      pairLoading M f β L (setPairLoading M f β σ L s) = σ
  | [], _ => rfl
  | _ :: L, s => pairLoading_setPairLoading σ L s.2

/-- The top idempotent of the row generator is a loading idempotent of the row. -/
theorem rowTop_eq_projection (σ : Seq (B₂).localWeight) :
    ∀ L (s : Loadings (adjacentRow L M f β)),
      rowTop Q Λ M f β (q₂ (ι₂ (KLRAlgebra.e σ))) L s =
        projection Q Λ _ (loadingIdem Q Λ _ (setPairLoading M f β σ L s))
  | [], s => (Algebra.TensorProduct.map_tmul _ _ _ _).symm
  | x :: L, s => by
    rw [rowTop, rowTop_eq_projection σ L s.2]
    exact (Algebra.TensorProduct.map_tmul _ _ _ _).symm

theorem orderedInclusion_spectatorsIdem :
    ∀ (M : List (Fin ℓ × Multiset I)) (s : Loadings (M.map spectator)),
      orderedInclusion Q Λ hQ botOrd (M.map spectator) (spectatorsIdem Q Λ hQ M s) =
        projection Q Λ _ (loadingIdem Q Λ _ s)
  | [], _ => rfl
  | x :: xs, s => by
    change TensorProduct.map _ _ (_ ⊗ₜ _) = _
    rw [TensorProduct.map_tmul]
    change orderedValue Q Λ hQ botOrd (spectator x) (spectatorIdem Q Λ hQ x s.1) ⊗ₜ
      orderedInclusion Q Λ hQ botOrd (xs.map spectator) (spectatorsIdem Q Λ hQ xs s.2) = _
    rw [orderedValue_spectatorIdem, orderedInclusion_spectatorsIdem xs s.2]
    exact (Algebra.TensorProduct.map_tmul _ _ _ _).symm

/-- The bottom idempotent of the row generator includes as a loading idempotent of the row. -/
theorem orderedInclusion_rowTau (σ : Seq (B₂).localWeight) (hσ : redWord σ = List.finRange 2) :
    ∀ L (s : Loadings (adjacentRow L M f β)),
      orderedInclusion Q Λ hQ botOrd (adjacentRow L M f β)
        (rowTau Q Λ hQ M f β (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e σ)) L s) =
        projection Q Λ _ (loadingIdem Q Λ _ (setPairLoading M f β σ L s))
  | [], s => by
    change TensorProduct.map _ _ (_ ⊗ₜ _) = _
    rw [TensorProduct.map_tmul]
    change orderedValue Q Λ hQ botOrd B₂ (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e σ)) ⊗ₜ
      orderedInclusion Q Λ hQ botOrd (M.map spectator) (spectatorsIdem Q Λ hQ M s.2) = _
    rw [orderedValue_identity_e Q Λ hQ B₂ σ hσ, orderedInclusion_spectatorsIdem]
    exact (Algebra.TensorProduct.map_tmul _ _ _ _).symm
  | x :: L, s => by
    change TensorProduct.map _ _ (_ ⊗ₜ _) = _
    rw [TensorProduct.map_tmul]
    change orderedValue Q Λ hQ botOrd (spectator x) (spectatorIdem Q Λ hQ x s.1) ⊗ₜ
      orderedInclusion Q Λ hQ botOrd (adjacentRow L M f β)
        (rowTau Q Λ hQ M f β (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e σ)) L s.2) = _
    rw [orderedValue_spectatorIdem, orderedInclusion_rowTau σ hσ L s.2]
    exact (Algebra.TensorProduct.map_tmul _ _ _ _).symm

private theorem tmul_isIdempotentElem {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    {a : A} {b : B} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a ⊗ₜ[k] b) := by
  change (a ⊗ₜ[k] b) * (a ⊗ₜ[k] b) = a ⊗ₜ[k] b
  rw [Algebra.TensorProduct.tmul_mul_tmul, ha.eq, hb.eq]

theorem isIdempotentElem_spectatorsIdem :
    ∀ (M : List (Fin ℓ × Multiset I)) (s : Loadings (M.map spectator)),
      IsIdempotentElem (spectatorsIdem Q Λ hQ M s)
  | [], _ => IsIdempotentElem.one
  | x :: xs, s => tmul_isIdempotentElem (isIdempotentElem_spectatorIdem Q Λ hQ x s.1)
      (isIdempotentElem_spectatorsIdem xs s.2)

include hQ in
theorem isIdempotentElem_tensorOfKLR_e (σ : Seq (B₂).localWeight)
    (hσ : redWord σ = List.finRange 2) :
    IsIdempotentElem (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e σ)) := by
  have hi : Function.Injective (orderedValue Q Λ hQ botOrd B₂) := fun a b h => by
    rw [← orderedRetraction_value Q Λ hQ botOrd B₂ a, h, orderedRetraction_value]
  apply hi
  change orderedValue Q Λ hQ botOrd B₂ (_ * _) = _
  rw [map_mul, orderedValue_identity_e Q Λ hQ B₂ σ hσ, ← map_mul, ← map_mul,
    KLRAlgebra.e_mul_self]

theorem isIdempotentElem_rowTau (σ : Seq (B₂).localWeight) (hσ : redWord σ = List.finRange 2) :
    ∀ L (s : Loadings (adjacentRow L M f β)),
      IsIdempotentElem (rowTau Q Λ hQ M f β (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e σ)) L s)
  | [], s => tmul_isIdempotentElem (isIdempotentElem_tensorOfKLR_e Q Λ hQ f β σ hσ)
      (isIdempotentElem_spectatorsIdem Q Λ hQ M s.2)
  | x :: L, s => tmul_isIdempotentElem (isIdempotentElem_spectatorIdem Q Λ hQ x s.1)
      (isIdempotentElem_rowTau σ hσ L s.2)

private theorem finRange_one_rev :
    (List.finRange 1).map (Fin.revPerm : Equiv.Perm (Fin 1)) = [0] := by decide

private theorem finRange_two_rev :
    (List.finRange 2).map (Fin.revPerm : Equiv.Perm (Fin 2)) = [1, 0] := by decide

omit [DecidableEq I] in
private theorem redWord_spectator' (x : Fin ℓ × Multiset I) (σ : Seq (spectator x).localWeight) :
    redWord σ = (List.finRange 1).map (Fin.revPerm : Equiv.Perm (Fin 1)) := by
  have hp : (redWord σ).Perm (List.finRange 1) :=
    (List.perm_ext_iff_of_nodup (redWord_nodup _) (List.nodup_finRange _)).2
      fun r => by simp [mem_redWord]
  exact (List.perm_singleton.1 (hp.trans (List.Perm.of_eq rfl))).trans (by rw [finRange_one_rev]; rfl)

private theorem top_mul_loading_block (B : RedBlock I ℓ) (σ : Seq B.localWeight)
    (hσ : redWord σ = (List.finRange B.size).map (Fin.revPerm : Equiv.Perm (Fin B.size))) :
    redProj k Q (Λ ∘ B.label) B.black ((List.finRange B.size).map
        (Fin.revPerm : Equiv.Perm (Fin B.size))) *
      ofKLR k Q (Λ ∘ B.label) B.black (KLRAlgebra.e σ) =
      ofKLR k Q (Λ ∘ B.label) B.black (KLRAlgebra.e σ) := by
  rw [redProj_mul_e, ite_eq_left hσ]

private theorem orderedIdem_top_spectators :
    ∀ (M : List (Fin ℓ × Multiset I)) (s : Loadings (M.map spectator)),
      orderedIdem Q Λ topOrd (M.map spectator) * loadingIdem Q Λ _ s = loadingIdem Q Λ _ s
  | [], _ => one_mul _
  | x :: xs, s => by
    change (_ ⊗ₜ _) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, orderedIdem_top_spectators xs s.2,
      top_mul_loading_block Q Λ (spectator x) s.1 (redWord_spectator' x s.1)]

private theorem orderedIdem_top_row (σ : Seq (B₂).localWeight) (hσ : redWord σ = [1, 0]) :
    ∀ L (s : Loadings (adjacentRow L M f β)), pairLoading M f β L s = σ →
      orderedIdem Q Λ topOrd (adjacentRow L M f β) * loadingIdem Q Λ _ s = loadingIdem Q Λ _ s
  | [], s, hs => by
    change (_ ⊗ₜ _) * (_ ⊗ₜ _) = _ ⊗ₜ _
    have hσ' : redWord s.1 = (List.finRange 2).map (Fin.revPerm : Equiv.Perm (Fin 2)) := by
      change redWord (pairLoading M f β [] s) = _
      rw [hs, hσ]; exact finRange_two_rev.symm
    rw [Algebra.TensorProduct.tmul_mul_tmul, orderedIdem_top_spectators Q Λ M s.2,
      top_mul_loading_block Q Λ B₂ s.1 hσ']
  | x :: L, s, hs => by
    change (_ ⊗ₜ _) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul,
      top_mul_loading_block Q Λ (spectator x) s.1 (redWord_spectator' x s.1)]
    congr 1
    exact orderedIdem_top_row σ hσ L s.2 hs

/-- The top order projector fixes a loading idempotent whose distinguished block is crossed. -/
theorem orderedInclusion_top_one_mul (σ : Seq (B₂).localWeight) (hσ : redWord σ = [1, 0])
    (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β)) :
    orderedInclusion Q Λ hQ topOrd (adjacentRow L M f β) 1 *
        projection Q Λ _ (loadingIdem Q Λ _ (setPairLoading M f β σ L s)) =
      projection Q Λ _ (loadingIdem Q Λ _ (setPairLoading M f β σ L s)) := by
  rw [orderedInclusion_one, ← map_mul,
    orderedIdem_top_row Q Λ M f β σ hσ L _ (pairLoading_setPairLoading M f β σ L s)]
local notation "m₂" => Multiset.card (stendhalWeight 2 β)

/-- **The cut quotient at a Figure 5 row loading is a standard module** (Webster,
arXiv:1309.3796v2, §6.1, proof of Proposition 6.9, the reduction to two red strands). Let the
distinguished block of a row carry the crossed Figure 5 loading `σ` in the loading `s` and the
uncrossed loading `t₂ = g⁻¹ σ` in the loading `s'`, with the same spectator loadings. Then the
cut quotient of step 2 at `s` is the standard module at `s'`. The hypothesis `hstd` is
`StackedStandard` for the relations of the row generator. -/
def rowBraidCutEquivStandard {ρ : Equiv.Perm (Fin m₂) → List ℕ} (hρ : TypeA.IsReducedChoice ρ)
    {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)} (h1 : 1 < m₂)
    (ht₀ : t₂.lbl ⟨0, by omega⟩ = .inr 0) (ht₁ : t₂.lbl ⟨1, h1⟩ = .inr 1)
    (hb : EdgeBraid (show 0 < m₂ by omega) 0 g σ t₂) (hσ : redWord σ = [1, 0])
    (ht₂ : redWord t₂ = [0, 1]) (L : List (Fin ℓ × Multiset I)) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν) (u : Loadings (adjacentRow L M f β))
    (hs : ¬ Violated _ (setPairLoading M f β σ L u))
    (ht : redWord (Seq.cast h (place _ (setPairLoading M f β σ L u))) =
      L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hstd : StackedStandard hQ h (rowRelations Q Λ hQ M f β
      (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e t₂)) (pairRelations Q Λ hQ f β t₂) L u)
      (setPairLoading M f β t₂ L u)) :
    ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ)
        (Seq.cast h (place _ (setPairLoading M f β t₂ L u)))
        (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst) ≃ₗ[(ViolOrderCorner (k := k) (Q := Q)
          (Λ := Λ) (ν := ν) (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst))ᵐᵒᵖ]
      BraidCutQuotient Q Λ (Seq.cast h (place _ (setPairLoading M f β σ L u))) (f 0) (f 1)
        (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst) :=
  have ht₂' : redWord t₂ = List.finRange 2 := ht₂.trans (by decide)
  braidCutQuotientEquivStandard
    (crossingProduct_generator Q Λ hQ M f β
      (pairCut_generator Q Λ hQ f β hρ h1 ht₀ ht₁ hb hσ ht₂) L u)
    ((rowTop_eq_projection Q Λ M f β σ L u).symm ▸
      orderedInclusion_top_one_mul Q Λ hQ M f β σ hσ L u)
    (isIdempotentElem_rowTau Q Λ hQ M f β t₂ ht₂' L u)
    (rowTop_eq_projection Q Λ M f β σ L u) (orderedInclusion_rowTau Q Λ hQ M f β t₂ ht₂' L u)
    hs ht hstd
end Categorification.Stendhal.RedBlock
