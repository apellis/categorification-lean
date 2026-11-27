/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistTilting
import Categorification.WeightedKLR.RedStrands.BraidedStandardConcentrated
import Categorification.Algebra.ExtTorDualityModule
import Categorification.Algebra.DerivedTensorRingEquiv
import Categorification.WeightedKLR.RedStrands.StandardStratificationStd

set_option backward.isDefEq.respectTransparency false

/-!
# The higher Ext between the tilting modules `𝔅_τ P` vanish

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.15: "the higher Ext's between tilting modules always vanish". For right modules `T`,
`T'` over the corner `e_κ V e_κ` with standard filtrations, the higher Tor between `T` and the
flip of `T'` vanish (`isZero_derivedTensorHomology_flipLeft`, the Tor vanishing between standards
and reflected standards of Lemma 6.12). If moreover `T'` is identified with its flip dual by a
contravariant form, Ext–Tor duality gives `Ext^n(T, T') = 0` for `n ≠ 0`
(`hom_shift_eq_zero_of_isContravariant`). For the cuts `𝔅_τ P^κ = e(t) V e_κ` of the half twist
this is `halfTwist_hom_shift_eq_zero`.
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

local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
local notation "μ" => stendhalWeight ℓ ν

variable (k Q Λ) in
/-- A cut `e(t) V e_κ` as a right module over `(e_κ V e_κ)ᵐᵒᵖ` through the flip:
`m · c = m ċ`. -/
def FlipLeft (t : Seq μ) (κ : List (Fin ℓ)) : Type := violCorner k Q Λ ν t κ

instance (t : Seq μ) (κ : List (Fin ℓ)) : AddCommGroup (FlipLeft k Q Λ t κ) :=
  inferInstanceAs (AddCommGroup (violCorner k Q Λ ν t κ))

instance (t : Seq μ) (κ : List (Fin ℓ)) : Module k (FlipLeft k Q Λ t κ) :=
  inferInstanceAs (Module k (violCorner k Q Λ ν t κ))

instance (t : Seq μ) (κ : List (Fin ℓ)) : Module (C κ)ᵐᵒᵖᵐᵒᵖ (FlipLeft k Q Λ t κ) :=
  (Module.compHom (violCorner k Q Λ ν t κ)
    (RingHom.op (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ).toRingHom) :
    Module (C κ)ᵐᵒᵖᵐᵒᵖ (violCorner k Q Λ ν t κ))

theorem flipLeft_smul_val {t : Seq μ} {κ : List (Fin ℓ)} (c : (C κ)ᵐᵒᵖᵐᵒᵖ)
    (m : FlipLeft k Q Λ t κ) :
    (show violCorner k Q Λ ν t κ from c • m).1 =
      (show violCorner k Q Λ ν t κ from m).1 * violFlip c.unop.unop.val := rfl

instance (t : Seq μ) (κ : List (Fin ℓ)) : SMulCommClass k (C κ)ᵐᵒᵖᵐᵒᵖ (FlipLeft k Q Λ t κ) where
  smul_comm r c m := Subtype.ext (by
    change r • ((show violCorner k Q Λ ν t κ from m).1 * _) =
      (r • (show violCorner k Q Λ ν t κ from m).1) * _
    exact (smul_mul_assoc _ _ _).symm)

/-- The flip dual of a cut is the dual of its flip. -/
def flipDualRightDualEquiv (t : Seq μ) (κ : List (Fin ℓ)) :
    FlipDual k Q Λ t κ ≃ₗ[(C κ)ᵐᵒᵖ] RightDual k (FlipLeft k Q Λ t κ) where
  toFun φ := φ
  invFun φ := φ
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restricting the flip of a cut back along the flip gives the cut. -/
def flipLeftCoefficientEquiv (t : Seq μ) (κ : List (Fin ℓ)) :
    ringEquivCoefficient (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ) (FlipLeft k Q Λ t κ) ≃ₗ[(C κ)ᵐᵒᵖ]
      ModuleCat.of (C κ)ᵐᵒᵖ (violCorner k Q Λ ν t κ) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a m := Subtype.ext (by
    change (show violCorner k Q Λ ν t κ from m).1 * violFlip (cornerFlip a.unop).val =
      (show violCorner k Q Λ ν t κ from m).1 * a.unop.val
    rw [← cornerFlip_val, cornerFlip_cornerFlip])

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
set_option quotPrecheck false in
local notation "𝕃" => fun s : {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s} =>
  ModuleCat.of (C κ)ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ)

include hρ hQ in
/-- **Tor between a standardly filtered module and the flip of another vanishes** (Webster,
arXiv:1309.3796v3, proof of Lemma 6.12, step `f_n → s_n`): for right modules `T` and `e(t) V e_κ`
over the corner at `κ = σ(1, …, ℓ)` with standard filtrations, the derived tensor of the flip of
`e(t) V e_κ` with `T` has homology only in degree `0`. -/
theorem isZero_derivedTensorHomology_flipLeft
    [HasDerivedCategory.{0, 0} (C κ)] [HasDerivedCategory.{0, 0} ℤ]
    [HasDerivedCategory.{0, 0} (C κ)ᵐᵒᵖ]
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ σ) ν)
        (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {t : Seq μ} {m : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}}
    (hf : HasFiltration 𝕃 m (ModuleCat.of (C κ)ᵐᵒᵖ (violCorner k Q Λ ν t κ)))
    {m' : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}} {X : ModuleCat.{0} (C κ)ᵐᵒᵖ}
    (hX : HasFiltration 𝕃 m' X) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{0} ℤ (C κ)ᵐᵒᵖ
      (ModuleCat.of (C κ)ᵐᵒᵖᵐᵒᵖ (FlipLeft k Q Λ t κ))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).obj X)))) := by
  let φ := cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ
  refine isZero_derivedTensorHomology_of_ringEquiv φ (FlipLeft k Q Λ t κ) X n ?_
  refine isZero_derivedTensorHomology_of_filtrations
    (hf.of_equiv (flipLeftCoefficientEquiv t κ).symm)
    (hX.restrictScalars φ.symm.toRingHom) n fun c _ d _ => ?_
  obtain ⟨t₁, ht₁, htc⟩ := exists_redPerm_of_redWord σ c.2.1
  obtain ⟨s₁, hs₁, hsd⟩ := exists_redPerm_of_redWord σ d.2.1
  have := isZero_derivedTensorHomology_loadingStandard hρ hQ σ D hs₁ ht₁ n hn
  rw [htc, hsd] at this
  exact this

include hρ hQ in
/-- **The higher Ext into a self-dual standardly filtered cut vanish** (Webster,
arXiv:1309.3796v3, proof of Theorem 6.15): if `T` and `e(t) V e_κ` have standard filtrations and
`e(t) V e_κ` carries a nondegenerate form contravariant for the flip, then every morphism
`T → e(t) V e_κ⟦n⟧` in the derived category of right modules vanishes for `n ≠ 0`. -/
theorem hom_shift_eq_zero_of_isContravariant
    [HasDerivedCategory.{0, 0} (C κ)] [HasDerivedCategory.{0, 0} ℤ]
    [HasDerivedCategory.{0, 0} (C κ)ᵐᵒᵖ]
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ σ) ν)
        (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {t : Seq μ} {m : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}}
    (hf : HasFiltration 𝕃 m (ModuleCat.of (C κ)ᵐᵒᵖ (violCorner k Q Λ ν t κ)))
    (Φ : violCorner k Q Λ ν t κ ≃ₗ[k] Module.Dual k (violCorner k Q Λ ν t κ))
    (hΦ : CornerSelfDual.IsContravariant
      (fun c : ViolQuotient k Q Λ ν =>
        violMk k Q Λ ν (redProj k Q Λ ν κ) * c * violMk k Q Λ ν (redProj k Q Λ ν κ) = c)
      violFlip Φ.toLinearMap)
    {m' : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}} {X : ModuleCat.{0} (C κ)ᵐᵒᵖ}
    (hX : HasFiltration 𝕃 m' X) (n : ℤ) (hn : n ≠ 0)
    (f : DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).obj X) ⟶
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).obj
        (ModuleCat.of (C κ)ᵐᵒᵖ (violCorner k Q Λ ν t κ))))⟦n⟧) : f = 0 := by
  let E : violCorner k Q Λ ν t κ ≃ₗ[(C κ)ᵐᵒᵖ] RightDual k (FlipLeft k Q Λ t κ) :=
    (flipDualEquiv Φ hΦ).trans (flipDualRightDualEquiv t κ)
  let e : (degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).obj (ModuleCat.of (C κ)ᵐᵒᵖ (violCorner k Q Λ ν t κ)) ≅
      (degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).obj
        (ModuleCat.of (C κ)ᵐᵒᵖ (RightDual k (FlipLeft k Q Λ t κ))) :=
    (degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).mapIso E.toModuleIso
  have h0 := hom_rightDual_shift_eq_zero_of_isZero (k := k) (FlipLeft k Q Λ t κ) X n
    (isZero_derivedTensorHomology_flipLeft hρ hQ σ D hf hX (-n) (neg_ne_zero.2 hn))
    (f ≫ (shiftFunctor _ n).map (DG.DerivedCategory.Q.map e.hom))
  have : f = (f ≫ (shiftFunctor _ n).map (DG.DerivedCategory.Q.map e.hom)) ≫ (shiftFunctor _ n).map (DG.DerivedCategory.Q.map e.inv) := by
    rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [this, h0, zero_comp]

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

include hQ hR H hwt hw in
/-- **The higher Ext between the cuts `𝔅_τ P^κ` vanish** (Webster, arXiv:1309.3796v3, proof of
Theorem 6.15), at the Khovanov–Lauda scalars: for red-ordered loadings `t`, `t'` and a red
order `κ = w(1, …, ℓ)` reversing every pair of red strands, every morphism
`e(t) V e_κ → e(t') V e_κ⟦n⟧` in the derived category of right modules over `e_κ V e_κ`
vanishes for `n ≠ 0`. Route hypothesis: the injectivity of Lemma 6.8
(`RowFigureFiveHypotheses`); `AllFiniteDeltaInjective` and `BaseCrossing` are proved at these
scalars. -/
theorem halfTwist_hom_shift_eq_zero
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
    {t t' : Seq (stendhalWeight (ℓ + 1) ν)} (ht : IsRedOrdered t) (ht' : IsRedOrdered t')
    (n : ℤ) (hn : n ≠ 0)
    (f : DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor 𝒞ᵐᵒᵖ).obj
        (ModuleCat.of 𝒞ᵐᵒᵖ (violCorner k QL Λ ν t κ))) ⟶
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor 𝒞ᵐᵒᵖ).obj
        (ModuleCat.of 𝒞ᵐᵒᵖ (violCorner k QL Λ ν t' κ))))⟦n⟧) : f = 0 := by
  obtain ⟨⟨m, hm⟩, -⟩ := halfTwist_hasFiltration C hQ Λ ν w hR H wt hwt hw hκ t ht
  obtain ⟨⟨m', hm'⟩, -⟩ := halfTwist_hasFiltration C hQ Λ ν w hR H wt hwt hw hκ t' ht'
  obtain ⟨Φ, hΦ⟩ := exists_halfTwistSelfDual C hQ Λ ν w hR H wt hwt hw hκ t' ht'
  let D := orderedStandardCovers QL (Λ ∘ w)
    (fun s => exists_hasFiltration_leftUpper_of_rouquier hQ hQ.klrSymm (Λ ∘ w) ν s.1 s.2)
  exact hom_shift_eq_zero_of_isContravariant (FirstWeight.isReducedChoice_canChoice ν)
    hQ.klrSymm w D hm' Φ hΦ hm n hn f

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
