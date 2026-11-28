/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistExt
import Categorification.WeightedKLR.RedStrands.HalfTwistEquivalence
import Categorification.WeightedKLR.RedStrands.BraidedStandardTor
import Categorification.WeightedKLR.RedStrands.RedBlackPairsOrder
import Categorification.Algebra.OrderedStandardExt
import Categorification.WeightedKLR.RedStrands.FlipDualExt

set_option backward.isDefEq.respectTransparency false

/-!
# Indecomposable tilting modules are summands of the cuts `𝔅_τ P`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 6.14,
second clause, by Ringel's argument. Over the corner `e_κ V e_κ` of a red order
`κ = w(1, …, ℓ)` reversing every pair of red strands:

* `Ext¹` between loading standards vanishes unless the first is strictly below the second
  (`hom_shift_one_loadingStandard_eq_zero`), from the ordered covers of the standards;
* an indecomposable module `T` of finite length with a standard filtration and no `Ext¹` from
  the standards is a direct summand of a cut `e(b) V e_κ = 𝔅_τ P` for a red-ordered loading `b`
  (`exists_leftInverse_violCorner_halfTwist`). Take a maximal standard `Δ_s` of `T`; it moves to
  the bottom of `T`. The loading `s` is the label of the stay index of the column of some `b`
  (`exists_stay_label`), where it has the fewest red–black pairs, so it is maximal among the
  labels of `e(b) V e_κ` (`redBlackPairs_le_of_stendhalLE`) and moves to the bottom there too.
  The cut has no higher `Ext` from standards (it is self-dual), and Ringel's comparison
  (`exists_leftInverse_of_bottom`) splits `T` off.

Webster's tilting modules are those `T` such that `T` and its dual `T⋆` have filtrations by
standardizations of projectives, that is, by loading standards. The dual condition gives the
vanishing of higher `Ext` from standards into `T` (`hom_shift_eq_zero_of_flipDual`), so Webster's
clause holds as stated (`exists_leftInverse_violCorner_of_tilting`).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite CornerEndomorphism
  ModuleFiltration DG DG.DerivedCategory

open scoped DG.DegreeZero

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

section General

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
local notation "μ" => stendhalWeight ℓ ν

include hρ hQ in
/-- **`Ext¹` between loading standards in the wrong order vanishes** (Webster,
arXiv:1309.3796v3, proof of Theorem 6.14, Ringel's argument): for loadings `s`, `a` of red order
`κ = σ(1, …, ℓ)` with `s` not strictly below `a`, `Ext¹(Δ_s, Δ_a) = 0` for the right loading
standards of the corner `e_κ V e_κ`. -/
theorem hom_shift_one_loadingStandard_eq_zero [HasDerivedCategory.{0, 0} Cᵐᵒᵖ]
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ σ) ν)
        (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {s a : Seq μ} (hs : redWord s = κ) (ha : redWord a = κ) (hsa : ¬ StendhalLT s a)
    (u : moduleObj (ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s κ)) ⟶
      (moduleObj (ModuleCat.of Cᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) a κ)))⟦(1 : ℤ)⟧) : u = 0 := by
  obtain ⟨s₁, hs₁, rfl⟩ := exists_redPerm_of_redWord σ hs
  obtain ⟨a₁, ha₁, rfl⟩ := exists_redPerm_of_redWord σ ha
  rw [stendhalLT_redPerm_iff'] at hsa
  exact (rightLoadingStandardCovers hρ hQ σ D).hom_shift_one_eq_zero (s := ⟨s₁, hs₁⟩)
    (a := ⟨a₁, ha₁⟩)
    (fun d => congrArg op (isIdempotentElem_violLoadingIdem (k := k) (Q := Q) (Λ := Λ)
      (redWord_relabel σ d.2)))
    (fun d hd x => violLoadingIdem_smul_violLoadingStandard_eq_zero_of_not_le hρ hQ σ ha₁ d.2
      (not_stendhalLE_of_lt_of_not_lt hd hsa) x) u

end General

section KhovanovLauda

open QuantumGroup KL3.Diagram
open scoped Classical DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} {k : Type} [Field k] (C : CartanDatum I)
  (hQ : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {ℓ : ℕ}
  (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (w : Perm (Fin (ℓ + 1)))
  {Y : Type*} [AddCommGroup Y] [Finite I]
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I),
    Module.Finite k (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Ω ν)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} ℤ]
  (H : ∀ (n m : ℕ), n + 2 + m = ℓ + 1 → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
    (u : Fin (n + 2 + m) → List I) (hu : u (FirstWeight.rightPos n m) = []),
    FirstWeight.RowFigureFiveHypotheses C hQ Ω u hu)
  (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
  (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (hw : w ≠ 1)

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "κ" => List.map w (List.finRange (ℓ + 1))
local notation "𝒞" => ViolOrderCorner (k := k) (Q := QL) (Λ := Λ) (ν := ν) κ
local notation "Lab" => {s : Seq (stendhalWeight (ℓ + 1) ν) // redWord s = κ ∧ ¬ IsViolated s}
set_option quotPrecheck false in
local notation "𝕃" => fun s : {s : Seq (stendhalWeight (ℓ + 1) ν) // redWord s = κ ∧
  ¬ IsViolated s} => ModuleCat.of 𝒞ᵐᵒᵖ
    (ViolLoadingStandard (k := k) (Q := QL) (Λ := Λ) s.1 κ)

include hQ hR H hwt hw in
/-- **Indecomposable tilting modules are summands of the cuts `𝔅_τ P`** (Webster,
arXiv:1309.3796v3, Theorem 6.14, second clause, by Ringel's argument), at the Khovanov–Lauda
scalars: for a red order `κ = w(1, …, ℓ)` reversing every pair of red strands, an indecomposable
right module `T` of finite length over `e_κ V e_κ` with a filtration by the loading standards and
with `Ext¹(Δ_a, T) = 0` for every loading standard `Δ_a` is a direct summand of a cut
`e(b) V e_κ` at a red-ordered loading `b`. Webster's tilting condition (the dual has a filtration
by standardizations) is replaced by this vanishing of `Ext¹`. Route hypothesis: the injectivity
of Lemma 6.8 (`RowFigureFiveHypotheses`). -/
theorem exists_leftInverse_violCorner_halfTwist
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
    {T : ModuleCat.{0} 𝒞ᵐᵒᵖ} [IsArtinian 𝒞ᵐᵒᵖ T] [IsNoetherian 𝒞ᵐᵒᵖ T]
    (hT : IsIndecomposableModule 𝒞ᵐᵒᵖ T) {m : List Lab} (hm : HasFiltration 𝕃 m T)
    (hext : ∀ a : Lab, ∀ u : moduleObj (𝕃 a) ⟶ (moduleObj T)⟦(1 : ℤ)⟧, u = 0) :
    ∃ b : Seq (stendhalWeight (ℓ + 1) ν), IsRedOrdered b ∧
      ∃ (i : T →ₗ[𝒞ᵐᵒᵖ] violCorner k QL Λ ν b κ) (p : violCorner k QL Λ ν b κ →ₗ[𝒞ᵐᵒᵖ] T),
        p ∘ₗ i = LinearMap.id := by
  let D := orderedStandardCovers QL (Λ ∘ w)
    (fun s => exists_hasFiltration_leftUpper_of_rouquier hQ hQ.klrSymm (Λ ∘ w) ν s.1 s.2)
  have hρ := FirstWeight.isReducedChoice_canChoice (ℓ := ℓ + 1) ν
  -- `Ext¹` between standards, vanishing into a zero standard
  have hstd : ∀ s a : Lab, (¬ StendhalLT s.1 a.1 ∨ Subsingleton (𝕃 a)) →
      ∀ u : moduleObj (𝕃 s) ⟶ (moduleObj (𝕃 a))⟦(1 : ℤ)⟧, u = 0 := by
    rintro s a (h | h) u
    · exact hom_shift_one_loadingStandard_eq_zero hρ hQ.klrSymm w D s.2.1 a.2.1 h u
    · exact ((shiftFunctor _ (1 : ℤ)).map_isZero
        (isZero_moduleObj_of_subsingleton h)).eq_of_tgt _ _
  -- a maximal nontrivial standard of `T`
  let r : Lab → Lab → Prop := fun a b => StendhalLT b.1 a.1
  have : IsTrans Lab r := ⟨fun a b c hab hbc =>
    ⟨fun r i => (hbc.1 r i).trans (hab.1 r i),
      fun hac => hbc.2 (fun r i => (hab.1 r i).trans (hac r i))⟩⟩
  have : Std.Irrefl r := ⟨fun a ha => ha.2 fun _ _ => le_rfl⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨c₀, hc₀, hc₀n⟩ := hm.exists_nontrivial hT.1
  obtain ⟨s, ⟨hsm, hsn⟩, hsmax⟩ := hwf.has_min {a | a ∈ m ∧ Nontrivial (𝕃 a)} ⟨c₀, hc₀, hc₀n⟩
  have hsT : ∀ a ∈ m, ¬ StendhalLT s.1 a.1 ∨ Subsingleton (𝕃 a) := fun a ha => by
    by_cases hna : Nontrivial (𝕃 a)
    · exact .inl (hsmax a ⟨ha, hna⟩)
    · exact .inr (not_nontrivial_iff_subsingleton.1 hna)
  obtain ⟨T', iT, pT, hiT, hipT, hpT, hT'⟩ := hm.exists_bottom hsm
    (fun a ha u => hstd s a (hsT a ha) u)
  -- the stay label `s` of the column at some `b`
  have hσ := strictAnti_of_isRedReversed s.2.1 (hκ s.1 s.2.1)
  obtain ⟨b, hb, W₀, hW₀, hlab, hlt⟩ := exists_stay_label hσ s.1 s.2.1 s.2.2
  obtain ⟨mB, hmv, hB⟩ := exists_hasFiltration_violCorner_halfTwist C hQ Λ ν w hR H wt hwt hw hb
  have hsB : s ∈ mB := by
    have : s.1 ∈ mB.map Subtype.val := by
      rw [hmv]
      exact List.mem_map.2 ⟨W₀, List.mem_reverse.2 hW₀, hlab⟩
    obtain ⟨e, he, hes⟩ := List.mem_map.1 this
    exact (Subtype.ext hes : e = s) ▸ he
  have hsBmax : ∀ a ∈ mB, ¬ StendhalLT s.1 a.1 := fun a ha hsa => by
    have : a.1 ∈ mB.map Subtype.val := List.mem_map_of_mem ha
    rw [hmv] at this
    obtain ⟨W, hW, hWa⟩ := List.mem_map.1 this
    by_cases hWW : W = W₀
    · rw [← hWa, hWW, hlab] at hsa
      exact hsa.2 fun _ _ => le_rfl
    · have h1 := hlt W (List.mem_reverse.1 hW) hWW
      rw [hWa] at h1
      exact absurd (redBlackPairs_le_of_stendhalLE hsa.1) (not_le.2 h1)
  obtain ⟨B', iB, pB, hiB, hipB, hpB, hB'⟩ := hB.exists_bottom hsB
    (fun a ha u => hstd s a (.inl (hsBmax a ha)) u)
  obtain ⟨Φ, hΦ⟩ := exists_halfTwistSelfDual C hQ Λ ν w hR H wt hwt hw hκ b hb
  obtain ⟨i, p, hip⟩ := exists_leftInverse_of_bottom (L := 𝕃) (s := s) hsn hT iT pT hiT hipT hpT hT'
    iB pB hiB hipB hpB hB'
    (fun a _ u => hom_shift_eq_zero_of_isContravariant hρ hQ.klrSymm w D hB Φ hΦ
      (HasFiltration.single (LinearEquiv.refl _ _)) 1 one_ne_zero u)
    (fun a _ u => hext a u)
  exact ⟨b, hb, i, p, hip⟩

include hQ hR H hwt hw in
/-- **Indecomposable tilting modules are summands of the cuts `𝔅_τ P`** (Webster,
arXiv:1309.3796v3, Theorem 6.14, second clause), at the Khovanov–Lauda scalars: for a red order
`κ = w(1, …, ℓ)` reversing every pair of red strands, let `T` be a finite-dimensional
indecomposable right module over `e_κ V e_κ` such that `T` and its flip dual `T⋆` both have
filtrations by loading standards (Webster's tilting condition, standards being the
standardizations of projectives). Then `T` is a direct summand of a cut `e(b) V e_κ` at a
red-ordered loading `b`. Route hypothesis: the injectivity of Lemma 6.8
(`RowFigureFiveHypotheses`). -/
theorem exists_leftInverse_violCorner_of_tilting
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
    {T : ModuleCat.{0} 𝒞ᵐᵒᵖ} [Module k T] [IsScalarTower k 𝒞ᵐᵒᵖ T] [FiniteDimensional k T]
    (hT : IsIndecomposableModule 𝒞ᵐᵒᵖ T) {m : List Lab} (hm : HasFiltration 𝕃 m T)
    {m' : List Lab}
    (hm' : HasFiltration 𝕃 m' (ModuleCat.of 𝒞ᵐᵒᵖ (RightDual k (FlipModule k QL Λ ν κ T)))) :
    ∃ b : Seq (stendhalWeight (ℓ + 1) ν), IsRedOrdered b ∧
      ∃ (i : T →ₗ[𝒞ᵐᵒᵖ] violCorner k QL Λ ν b κ) (p : violCorner k QL Λ ν b κ →ₗ[𝒞ᵐᵒᵖ] T),
        p ∘ₗ i = LinearMap.id := by
  have : IsArtinian 𝒞ᵐᵒᵖ T := isArtinian_of_tower k inferInstance
  have : IsNoetherian 𝒞ᵐᵒᵖ T := isNoetherian_of_tower k inferInstance
  let D := orderedStandardCovers QL (Λ ∘ w)
    (fun s => exists_hasFiltration_leftUpper_of_rouquier hQ hQ.klrSymm (Λ ∘ w) ν s.1 s.2)
  exact exists_leftInverse_violCorner_halfTwist C hQ Λ ν w hR H wt hwt hw hκ hT hm
    fun a u => hom_shift_eq_zero_of_flipDual (FirstWeight.isReducedChoice_canChoice ν)
      hQ.klrSymm w D hm' (HasFiltration.single (LinearEquiv.refl _ _)) 1 one_ne_zero u

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
