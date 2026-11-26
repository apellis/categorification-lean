/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingBraidStandard
import Categorification.WeightedKLR.RedStrands.GradedBraidResolution
import Categorification.WeightedKLR.RedStrands.GradedRightStandardModule

/-!
# The derived braid of a standard module at a Figure 5 row loading is concentrated

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Corollary 6.10. With the notation of
`RedBlock.rowStandard_braidIso`, the derived braid of the standard module at the crossed row
loading `t` is a module in degree zero, so `e(t) T^λ / U_t` is braid-concentrated
(`braidConcentrated_rowStandard`).

It carries the hypotheses of `rowStandard_braidIso`: `hfilt` and `hinj` of Lemma 6.8 and
`StackedStandard`.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open CategoryTheory CategoryTheory.Limits KLR BraidedStendhalAlgebra MulOpposite DG DG.DegreeZero
open DG.DerivedCategory (cohomologyAddEquiv)
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w

/-- A module placed in degree zero has no derived cohomology outside degree zero. -/
theorem isZero_homology_degreeZero {R : Type} [Ring R] [HasDerivedCategory.{w} R]
    (Y : ModuleCat.{0} R) {n : ℤ} (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := R) ℤ n).obj
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor R).obj Y))) := by
  let Z := (degreeZeroModuleFunctor R).obj Y
  let : Subsingleton (cocycles Z n) := ⟨fun x y => by
    apply Subtype.ext
    have hx := ((InDegreeZero.mem_grading_iff Y).mp (mem_cocycles.mp x.2).1).resolve_left hn
    have hy := ((InDegreeZero.mem_grading_iff Y).mp (mem_cocycles.mp y.2).1).resolve_left hn
    exact hx.trans hy.symm⟩
  let : Subsingleton (cohomology Z n) := (cohomology.mk_surjective Z n).subsingleton
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((cohomologyAddEquiv ℤ Z n).surjective.subsingleton)

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
local notation "m₂" => Multiset.card (stendhalWeight 2 β)

/-- Vanishing of the derived cohomology of the braid of a standard module only depends on the
red orders up to equality. -/
theorem braidStandard_isZero_congr {ν : Multiset I} (t : Seq (stendhalWeight ℓ ν))
    {κ₁ κ₁' κ₀ κ₀' : List (Fin ℓ)} (h₁ : κ₁ = κ₁') (h₀ : κ₀ = κ₀') (n : ℤ)
    [HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
      κ₁'))ᵐᵒᵖ]
    [HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
      κ₀'))ᵐᵒᵖ]
    (H : ∀ [HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q
        Λ ν κ₁))ᵐᵒᵖ] [HasDerivedCategory.{w} (IsIdempotentElem.Corner
        (isIdempotentElem_violMk_redProj k Q Λ ν κ₀))ᵐᵒᵖ],
      IsZero ((DG.DerivedCategory.homologyFunctor (A := (IsIdempotentElem.Corner
        (isIdempotentElem_violMk_redProj k Q Λ ν κ₀))ᵐᵒᵖ) ℤ n).obj
        ((braidingFunctor.{w} k Q Λ ν κ₁ κ₀).obj (DG.DerivedCategory.Q.obj
          ((degreeZeroModuleFunctor _).obj (ModuleCat.of _
            (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ₁))))))) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := (IsIdempotentElem.Corner
        (isIdempotentElem_violMk_redProj k Q Λ ν κ₀'))ᵐᵒᵖ) ℤ n).obj
        ((braidingFunctor.{w} k Q Λ ν κ₁' κ₀').obj (DG.DerivedCategory.Q.obj
          ((degreeZeroModuleFunctor _).obj (ModuleCat.of _
            (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ₁')))))) := by
  subst h₁ h₀
  exact H

/-- The corner restriction of the right standard module `e(t) T^λ / U_t` is the standard
module over the corner `e_λ V e_λ`. -/
def cornerResRightStandardEquiv {ν : Multiset I}
    {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) (G : GradingDatum (stendhalQ Q Λ))
    [Module.Finite k (TensorProductAlgebra k Q Λ ν)]
    {t : Seq (stendhalWeight ℓ ν)} (ht : redWord t = List.finRange ℓ) :
    CornerRes G hρ hQ (rightStandard hρ hQ t G ht) ≃ₗ[(IsIdempotentElem.Corner
      (isIdempotentElem_violMk_redProj k Q Λ ν (List.finRange ℓ)))ᵐᵒᵖ]
      ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t (List.finRange ℓ) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    have hc : rightCornerHom hρ hQ (cornerOpRingHom hρ hQ c) = c :=
      MulOpposite.unop_injective (RingEquiv.symm_apply_apply _ c.unop)
    change rightCornerHom hρ hQ (cornerOpRingHom hρ hQ c) •
      (show ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t (List.finRange ℓ) from x) = c • _
    rw [hc]

/-- **The standard module at a crossed Figure 5 row loading is braid-concentrated** (Webster,
arXiv:1309.3796v2, §6.1, proof of Corollary 6.10). With `t` the placed crossed loading, of red
order `(1, …, ℓ) = L ++ f 1 :: f 0 :: M`, and `π` a permutation with
`π(1, …, ℓ) = L ++ f 0 :: f 1 :: M`, the derived braid `𝔅_π (e(t) T^λ / U_t)` has no cohomology
outside degree zero.

The hypotheses `hfilt` and `hinj` are those of Lemma 6.8 and `hstd` is `StackedStandard`, as in
`rowStandard_braidIso`; each is an explicit hypothesis tracked for removal. -/
theorem braidConcentrated_rowStandard {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q)
    {ρ₂ : Equiv.Perm (Fin m₂) → List ℕ}
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
    {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) (π : Equiv.Perm (Fin ℓ))
    (hord : List.finRange ℓ = L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hκ : (List.finRange ℓ).map π = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)
    [Module.Finite k (TensorProductAlgebra k Q Λ ν)]
    [HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
      (List.finRange ℓ)))ᵐᵒᵖ]
    [HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
      ((List.finRange ℓ).map π)))ᵐᵒᵖ]
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
    BraidConcentrated.{w} Λ ν hρ hQ π hR (rightStandard hρ hQ
      (Seq.cast h (place _ (setPairLoading M f β σ L u))) (rouquierGrading Q hR Λ)
      (ht.trans hord.symm)) := by
  intro n hn
  have key := braidStandard_isZero_congr.{w} Q Λ (Seq.cast h (place _ (setPairLoading M f β σ L u)))
    (ht.trans hord.symm) hκ.symm n (fun {_ _} =>
      (isZero_homology_degreeZero.{w} _ hn).of_iso
        ((DG.DerivedCategory.homologyFunctor ℤ n).mapIso
          (rowStandard_braidIso Q Λ hQ M f β hρ₂ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd hfilt
            hinj)))
  exact key.of_iso ((DG.DerivedCategory.homologyFunctor ℤ n).mapIso
    ((braidingFunctor.{w} k Q Λ ν _ _).mapIso (DG.DerivedCategory.Q.mapIso
      ((degreeZeroModuleFunctor _).mapIso
        (cornerResRightStandardEquiv Q Λ hQ hρ (rouquierGrading Q hR Λ)
          (ht.trans hord.symm)).toModuleIso))))

end Categorification.Stendhal.RedBlock
