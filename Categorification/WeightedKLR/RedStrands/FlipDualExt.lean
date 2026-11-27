/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistExt

set_option backward.isDefEq.respectTransparency false

/-!
# No higher `Ext` from standards into duals of standardly filtered modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §6, the
tilting condition of Theorem 6.14. A right module `N` over the corner `e_κ V e_κ` becomes a left
module through the flip of diagrams (`FlipModule`), and its `k`-dual `N⋆ = Hom_k(N, k)` is again a
right module, `(φ c)(n) = φ(n ċ)`. If `N` has a filtration by loading standards, the higher Tor
between the flip of `N` and any standardly filtered module vanish
(`isZero_derivedTensorHomology_flipModule`), so by Ext–Tor duality there are no higher `Ext`
from standardly filtered modules into `N⋆` (`hom_shift_eq_zero_rightDual_flipModule`). For `T`
finite-dimensional, `T ≅ T⋆⋆` (`flipDoubleDualEquiv`), so if `T⋆` is standardly filtered there
are no higher `Ext` from standardly filtered modules into `T` (`hom_shift_eq_zero_of_flipDual`).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite CornerEndomorphism
  ModuleFiltration DG DG.DerivedCategory

open scoped DG.DegreeZero

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
local notation "μ" => stendhalWeight ℓ ν

/-- A right module `N` over the corner at `κ`, read as a left module through the flip:
`c · n = n ċ`. -/
def FlipModule (k : Type) [Field k] (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin ℓ → I →₀ ℕ)
    (_ν : Multiset I) (_κ : List (Fin ℓ)) (N : Type) : Type := N

/-- The flip of the corner at `κ`, an isomorphism with its opposite. -/
abbrev flipEquiv (κ : List (Fin ℓ)) : (C κ)ᵐᵒᵖ ≃+* C κ := cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ

section FlipModule

variable {κ : List (Fin ℓ)}

instance {N : Type} [AddCommGroup N] :
    AddCommGroup (FlipModule k Q Λ ν κ N) := inferInstanceAs (AddCommGroup N)

instance {N : Type} [AddCommGroup N] [Module k N] : Module k (FlipModule k Q Λ ν κ N) :=
  inferInstanceAs (Module k N)

instance {N : Type} [AddCommGroup N] [Module (C κ)ᵐᵒᵖ N] :
    Module (C κ)ᵐᵒᵖᵐᵒᵖ (FlipModule k Q Λ ν κ N) :=
  (Module.compHom N (RingHom.op (flipEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ).toRingHom) :
    Module (C κ)ᵐᵒᵖᵐᵒᵖ N)

instance {N : Type} [AddCommGroup N] [Module k N] [Module (C κ)ᵐᵒᵖ N]
    [SMulCommClass k (C κ)ᵐᵒᵖ N] :
    SMulCommClass k (C κ)ᵐᵒᵖᵐᵒᵖ (FlipModule k Q Λ ν κ N) where
  smul_comm r c n := smul_comm (α := N) r
    ((RingHom.op (flipEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ).toRingHom) c) n

/-- Restricting the flip of `N` back along the flip gives `N`. -/
def flipModuleCoefficientEquiv {N : Type} [AddCommGroup N] [Module (C κ)ᵐᵒᵖ N] :
    ringEquivCoefficient (flipEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ) (FlipModule k Q Λ ν κ N)
      ≃ₗ[(C κ)ᵐᵒᵖ] ModuleCat.of (C κ)ᵐᵒᵖ N where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a m := by
    change ((RingHom.op (flipEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ).toRingHom)
      ((RingHom.op (flipEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ).symm.toRingHom) a)) •
        (show N from m) = a • (show N from m)
    congr 1
    exact MulOpposite.unop_injective
      ((flipEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ).apply_symm_apply a.unop)

/-- Flipping twice is the identity. -/
theorem op_cornerFlipEquiv_op_cornerFlipEquiv (r : (C κ)ᵐᵒᵖ) :
    op ((flipEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)
      (op ((flipEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ) r))) = r := by
  change op (cornerFlip (cornerFlip r.unop)) = r
  rw [cornerFlip_cornerFlip]
  rfl

instance {N : Type} [AddCommGroup N] [Module k N] [Module (C κ)ᵐᵒᵖ N]
    [SMulCommClass k (C κ)ᵐᵒᵖ N] :
    SMulCommClass k (C κ)ᵐᵒᵖ (RightDual k (FlipModule k Q Λ ν κ N)) :=
  SMulCommClass.symm _ _ _

/-- **The flip double dual**: a finite-dimensional right module is its flip double dual,
`n ↦ (φ ↦ φ n)`. -/
def flipDoubleDualEquiv (N : Type) [AddCommGroup N] [Module k N] [Module (C κ)ᵐᵒᵖ N]
    [SMulCommClass k (C κ)ᵐᵒᵖ N] [FiniteDimensional k N] :
    N ≃ₗ[(C κ)ᵐᵒᵖ] RightDual k (FlipModule k Q Λ ν κ (RightDual k (FlipModule k Q Λ ν κ N))) :=
  { (Module.evalEquiv k N : N ≃ₗ[k] Module.Dual k (Module.Dual k N)) with
    map_smul' := fun r n => LinearMap.ext fun φ => by
      change φ (r • n) = φ (op ((flipEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)
        (op ((flipEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ) r))) • n)
      rw [op_cornerFlipEquiv_op_cornerFlipEquiv] }

end FlipModule

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
set_option quotPrecheck false in
local notation "𝕃" => fun s : {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s} =>
  ModuleCat.of (C κ)ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ)


include hρ hQ in
/-- **Tor between a standardly filtered module and the flip of another vanishes** (Webster,
arXiv:1309.3796v3, Lemma 6.12, Tor between standards and reflected standards): for right modules
`N` and `X` over the corner at `κ = σ(1, …, ℓ)` with standard filtrations, the derived tensor of
the flip of `N` with `X` has homology only in degree `0`. -/
theorem isZero_derivedTensorHomology_flipModule
    [HasDerivedCategory.{0, 0} (C κ)] [HasDerivedCategory.{0, 0} ℤ]
    [HasDerivedCategory.{0, 0} (C κ)ᵐᵒᵖ]
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ σ) ν)
        (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {N : Type} [AddCommGroup N] [Module k N] [Module (C κ)ᵐᵒᵖ N]
    [SMulCommClass k (C κ)ᵐᵒᵖ N]
    {m : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}}
    (hN : HasFiltration 𝕃 m (ModuleCat.of (C κ)ᵐᵒᵖ N))
    {m' : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}} {X : ModuleCat.{0} (C κ)ᵐᵒᵖ}
    (hX : HasFiltration 𝕃 m' X) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{0} ℤ (C κ)ᵐᵒᵖ
      (ModuleCat.of (C κ)ᵐᵒᵖᵐᵒᵖ (FlipModule k Q Λ ν κ N))).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).obj X)))) := by
  let φ := flipEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
  refine isZero_derivedTensorHomology_of_ringEquiv φ (FlipModule k Q Λ ν κ N) X n ?_
  refine isZero_derivedTensorHomology_of_filtrations
    (hN.of_equiv (flipModuleCoefficientEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (N := N)).symm)
    (hX.restrictScalars φ.symm.toRingHom) n fun c _ d _ => ?_
  obtain ⟨t₁, ht₁, htc⟩ := exists_redPerm_of_redWord σ c.2.1
  obtain ⟨s₁, hs₁, hsd⟩ := exists_redPerm_of_redWord σ d.2.1
  have := isZero_derivedTensorHomology_loadingStandard hρ hQ σ D hs₁ ht₁ n hn
  rw [htc, hsd] at this
  exact this

include hρ hQ in
/-- **No higher `Ext` into the dual of a standardly filtered module** (Webster,
arXiv:1309.3796v3, §6): if `N` and `X` have standard filtrations, every morphism
`X → N⋆⟦n⟧` in the derived category of right modules vanishes for `n ≠ 0`. -/
theorem hom_shift_eq_zero_rightDual_flipModule
    [HasDerivedCategory.{0, 0} (C κ)] [HasDerivedCategory.{0, 0} ℤ]
    [HasDerivedCategory.{0, 0} (C κ)ᵐᵒᵖ]
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ σ) ν)
        (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {N : Type} [AddCommGroup N] [Module k N] [Module (C κ)ᵐᵒᵖ N]
    [SMulCommClass k (C κ)ᵐᵒᵖ N]
    {m : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}}
    (hN : HasFiltration 𝕃 m (ModuleCat.of (C κ)ᵐᵒᵖ N))
    {m' : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}} {X : ModuleCat.{0} (C κ)ᵐᵒᵖ}
    (hX : HasFiltration 𝕃 m' X) (n : ℤ) (hn : n ≠ 0)
    (f : DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).obj X) ⟶
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).obj
        (ModuleCat.of (C κ)ᵐᵒᵖ (RightDual k (FlipModule k Q Λ ν κ N)))))⟦n⟧) : f = 0 :=
  hom_rightDual_shift_eq_zero_of_isZero (k := k) (FlipModule k Q Λ ν κ N) X n
    (isZero_derivedTensorHomology_flipModule hρ hQ σ D hN hX (-n) (neg_ne_zero.2 hn)) f

include hρ hQ in
/-- **No higher `Ext` from standards into a module with standardly filtered dual** (Webster,
arXiv:1309.3796v3, §6, the tilting condition of Theorem 6.14): if `T` is finite-dimensional
and its flip dual `T⋆` has a standard filtration, every morphism `X → T⟦n⟧` from a standardly
filtered `X` vanishes for `n ≠ 0`. -/
theorem hom_shift_eq_zero_of_flipDual
    [HasDerivedCategory.{0, 0} (C κ)] [HasDerivedCategory.{0, 0} ℤ]
    [HasDerivedCategory.{0, 0} (C κ)ᵐᵒᵖ]
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ σ) ν)
        (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {N : Type} [AddCommGroup N] [Module k N] [Module (C κ)ᵐᵒᵖ N]
    [SMulCommClass k (C κ)ᵐᵒᵖ N]
    [FiniteDimensional k N] {m : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}}
    (hN : HasFiltration 𝕃 m (ModuleCat.of (C κ)ᵐᵒᵖ (RightDual k (FlipModule k Q Λ ν κ N))))
    {m' : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}} {X : ModuleCat.{0} (C κ)ᵐᵒᵖ}
    (hX : HasFiltration 𝕃 m' X) (n : ℤ) (hn : n ≠ 0)
    (f : DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).obj X) ⟶
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).obj
        (ModuleCat.of (C κ)ᵐᵒᵖ N)))⟦n⟧) : f = 0 := by
  let e := (degreeZeroModuleFunctor (C κ)ᵐᵒᵖ).mapIso
    (flipDoubleDualEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) N :
      N ≃ₗ[(C κ)ᵐᵒᵖ] _).toModuleIso
  have h0 := hom_shift_eq_zero_rightDual_flipModule hρ hQ σ D hN hX n hn
    (f ≫ (shiftFunctor _ n).map (DG.DerivedCategory.Q.map e.hom))
  have : f = (f ≫ (shiftFunctor _ n).map (DG.DerivedCategory.Q.map e.hom)) ≫
      (shiftFunctor _ n).map (DG.DerivedCategory.Q.map e.inv) := by
    rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [this, h0, zero_comp]

end Categorification.Stendhal.BraidedStendhalAlgebra
