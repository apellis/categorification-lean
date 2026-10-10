/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CLTwoFunctorShift
import Categorification.TwoRep.DotExtension

/-!
# CL Theorem 1.1: a 2-functor from the Karoubi completion of `U_Q(g)`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §1.2, Theorem 1.1: *a `Q`-strong 2-representation of `g` on `K` extends to a
2-representation `U̇_Q(g) → K`*, where a 2-representation of `U̇_Q(g)` is a graded additive
`k`-linear (weak) 2-functor `U̇_Q(g) → K` (the definition preceding Theorem 1.1; §2.1.2), and
`U̇_Q(g)` is the Karoubi completion of `U_Q(g)` (Definition 1.1, §2.1.2).

Here:

* `U_Q(g)` (Definition 1.1: objects the weights, 1-morphisms formal direct sums of shifted words in
  the `E_i` and `F_i`, 2-morphisms the diagrams of degree `0` between them) is the additive envelope
  `MatBicat (UQShift RD S₀)` of the graded presented 2-category `UQShift RD S₀`
  (`Categorification.TwoRep.CLTwoFunctorShift`), and
* `U̇_Q(g)` is its idempotent completion: `UQDot RD S₀ = Kar (UQShift RD S₀)
  = KarBicat (MatBicat (UQShift RD S₀))`, the additive Karoubi envelope of string-diagrams-lean
  (J. Brundan, A. P. Ellis, arXiv:1603.05928v3, §1.5: hom categories `Karoubi (Mat_ (Hom(λ, μ)))`);
* the target `K` is the bicategory `B` of the `Q`-strong 2-representation (its hom categories are
  additive, `k`-linear and idempotent complete, CL Definition 1.2).

`QStrong.twoFunctorDot : UQDot RD S₀ ⥤ᵖ B` is the extension of `QStrong.twoFunctorShift`: first to
formal direct sums (`MatBicat.mapPseudofunctor`), then to idempotents
(`KarBicat.mapPseudofunctor`), and realized in `B`, where formal direct sums are biproducts
(`MatBicat.realize`) and idempotents split (`KarBicat.realize`); this is the general construction
`DotExt.ext` of `Categorification.TwoRep.DotExtension`.

`twoFunctorDot` extends `twoFunctorShift` as a pseudofunctor: the isomorphisms
`twoFunctorDotInclIso x : twoFunctorDot ((x), 1) ≅ twoFunctorShift x` are natural in 2-morphisms
(`twoFunctorDotInclIso_naturality`) and compatible with the composition and identity constraints
(`twoFunctorDotInclIso_mapComp`, `twoFunctorDotInclIso_mapId`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open KrullSchmidtCat (HomFinite)

universe w v u u₁ u₀ u₂ u₃ w₂ v₂

section Model

open GradedHomBicat GradedHomCat ShiftEnv ShiftEnvK PresGrading
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp

section Generic

variable {R : Type w₂} [CommRing R] {S' : Signature.{u₀, u₂, u₃}} [S'.IsEven]

theorem rescale_map₂_add {χ : S'.Gen → Rˣ} {P P' : Presentation.{w₂, v₂} S' R}
    (h : ∀ i, P'.lin (CL.Rescale.scL χ (P.rel i)) = 0) {a b : RevBicat P.Bicat} {x y : a ⟶ b}
    (η θ : x ⟶ y) :
    (CL.Rescale.pseudofunctor h).map₂ (η + θ) =
      (CL.Rescale.pseudofunctor h).map₂ η + (CL.Rescale.pseudofunctor h).map₂ θ :=
  (CL.Rescale.functor χ h).map_add

theorem rescale_map₂_smul {χ : S'.Gen → Rˣ} {P P' : Presentation.{w₂, v₂} S' R}
    (h : ∀ i, P'.lin (CL.Rescale.scL χ (P.rel i)) = 0) {a b : RevBicat P.Bicat} {x y : a ⟶ b}
    (r : R) (η : x ⟶ y) :
    (CL.Rescale.pseudofunctor h).map₂ (r • η) = r • (CL.Rescale.pseudofunctor h).map₂ η :=
  (CL.Rescale.functor χ h).map_smul r η

theorem presPseudo_map₂_add {C' : Type*} [Bicategory C'] [∀ a b : C', Preadditive (a ⟶ b)]
    [∀ a b : C', Linear R (a ⟶ b)] [∀ (a b c : C') (f : a ⟶ b), (precomp c f).Additive]
    [∀ (a b c : C') (g : b ⟶ c), (postcomp a g).Additive]
    [∀ (a b c : C') (f : a ⟶ b), (precomp c f).Linear R]
    [∀ (a b c : C') (g : b ⟶ c), (postcomp a g).Linear R] [∀ a b : C', HasZeroObject (a ⟶ b)]
    {M : Model S' C'} (G : GenImg M) {P : Presentation.{w₂, v₂} S' R}
    (hP : ∀ s₀ t₀ : S'.Region, P.Respects (interp G s₀ t₀).functor) {a b : RevBicat P.Bicat}
    {x y : a ⟶ b} (η θ : x ⟶ y) :
    PresPseudo.map₂ G hP (η + θ) = PresPseudo.map₂ G hP η + PresPseudo.map₂ G hP θ := by
  simp only [PresPseudo.map₂]
  rw [show (P.lift (hP b.as.region a.as.region)).map (η + θ) =
      (P.lift (hP b.as.region a.as.region)).map η + (P.lift (hP b.as.region a.as.region)).map θ
    from Functor.map_add _, Preadditive.add_comp, Preadditive.comp_add]

theorem presPseudo_map₂_smul {C' : Type*} [Bicategory C'] [∀ a b : C', Preadditive (a ⟶ b)]
    [∀ a b : C', Linear R (a ⟶ b)] [∀ (a b c : C') (f : a ⟶ b), (precomp c f).Additive]
    [∀ (a b c : C') (g : b ⟶ c), (postcomp a g).Additive]
    [∀ (a b c : C') (f : a ⟶ b), (precomp c f).Linear R]
    [∀ (a b c : C') (g : b ⟶ c), (postcomp a g).Linear R] [∀ a b : C', HasZeroObject (a ⟶ b)]
    {M : Model S' C'} (G : GenImg M) {P : Presentation.{w₂, v₂} S' R}
    (hP : ∀ s₀ t₀ : S'.Region, P.Respects (interp G s₀ t₀).functor) {a b : RevBicat P.Bicat}
    {x y : a ⟶ b} (r : R) (η : x ⟶ y) :
    PresPseudo.map₂ G hP (r • η) = r • PresPseudo.map₂ G hP η := by
  simp only [PresPseudo.map₂]
  rw [show (P.lift (hP b.as.region a.as.region)).map (r • η) =
      r • (P.lift (hP b.as.region a.as.region)).map η from Functor.map_smul _ _ _,
    Linear.smul_comp, Linear.comp_smul]

end Generic

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} [DecidableEq I] {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X]
  [AddCommGroup Y] {RD : RootDatum C X Y}

variable (RD) in
/-- **The Karoubi completion `U̇_Q(g)`** of CL Definition 1.1 (§2.1.2): the additive Karoubi
envelope of the graded presented 2-category `U_Q(g)`. -/
abbrev UQDot (S₀ : CL.CLScalars C k) : Type _ := Kar (UQShift RD S₀)

/-- Whiskering in a graded bicategory is additive. -/
theorem preadditiveBicategory_of_graded : PreadditiveBicategory B :=
  ⟨fun f _ _ η θ => whiskerLeft_add f η θ, fun η θ h => add_whiskerRight η θ h⟩

attribute [local instance] preadditiveBicategory_of_graded

/-- The hom categories of `B` have finite biproducts. -/
instance hasFiniteBiproducts_hom (a b : B) : HasFiniteBiproducts (a ⟶ b) :=
  have : HasFiniteProducts (a ⟶ b) := hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

namespace QStrong

variable (S₀ : CL.CLScalars C k) (S : QStrong B C RD k (CL.qCL S₀))
  (hrQ : ∀ i, S.rQ i = S₀.r i)

theorem twoFunctorHOM_map₂_add {a b : RevBicat (CL.presCL RD k S₀).Bicat} {x y : a ⟶ b}
    (η θ : x ⟶ y) :
    (twoFunctorHOM S₀ S hrQ).map₂ (η + θ) =
      (twoFunctorHOM S₀ S hrQ).map₂ η + (twoFunctorHOM S₀ S hrQ).map₂ θ := by
  rw [twoFunctorHOM_map₂, twoFunctorHOM_map₂, twoFunctorHOM_map₂, rescale_map₂_add]
  exact presPseudo_map₂_add _ _ _ _

theorem shiftHOM_map₂_add {a b : UQShift RD S₀} {f g : a ⟶ b} (η θ : f ⟶ g) :
    (shiftHOM S₀ S hrQ).map₂ (η + θ) = (shiftHOM S₀ S hrQ).map₂ η + (shiftHOM S₀ S hrQ).map₂ θ :=
  hom₂_ext (twoFunctorHOM_map₂_add S₀ S hrQ (val₂ η) (val₂ θ))

theorem twoFunctorShift_map₂_add {a b : UQShift RD S₀} {f g : a ⟶ b} (η θ : f ⟶ g) :
    (twoFunctorShift S₀ S hrQ).map₂ (η + θ) =
      (twoFunctorShift S₀ S hrQ).map₂ η + (twoFunctorShift S₀ S hrQ).map₂ θ :=
  realize_map₂_add _ (shiftHOM_map₂_add S₀ S hrQ) η θ

theorem twoFunctorHOM_map₂_smul {a b : RevBicat (CL.presCL RD k S₀).Bicat} {x y : a ⟶ b}
    (r : k) (η : x ⟶ y) :
    (twoFunctorHOM S₀ S hrQ).map₂ (r • η) = r • (twoFunctorHOM S₀ S hrQ).map₂ η := by
  rw [twoFunctorHOM_map₂, twoFunctorHOM_map₂, rescale_map₂_smul]
  exact presPseudo_map₂_smul _ _ _ _

theorem shiftHOM_map₂_smul {a b : UQShift RD S₀} {f g : a ⟶ b} (r : k) (η : f ⟶ g) :
    (shiftHOM S₀ S hrQ).map₂ (r • η) = r • (shiftHOM S₀ S hrQ).map₂ η :=
  hom₂_ext (twoFunctorHOM_map₂_smul S₀ S hrQ r (val₂ η))

theorem twoFunctorShift_map₂_smul {a b : UQShift RD S₀} {f g : a ⟶ b} (r : k) (η : f ⟶ g) :
    (twoFunctorShift S₀ S hrQ).map₂ (r • η) = r • (twoFunctorShift S₀ S hrQ).map₂ η :=
  realize_map₂_smul _ (shiftHOM_map₂_smul S₀ S hrQ) r η

theorem twoFunctorShift_addHyp : DotExt.AddHyp (twoFunctorShift S₀ S hrQ) :=
  ⟨fun η θ => twoFunctorShift_map₂_add S₀ S hrQ η θ⟩

/-- The pseudofunctor into the Karoubi envelope of `B` realized by `twoFunctorDot`: the extension
of `twoFunctorShift` to formal direct sums and idempotents, followed by the realization of formal
direct sums in `B`. -/
abbrev kQ : Pseudofunctor (UQDot RD S₀) (StringDiagrams.KarBicat B) :=
  DotExt.kar (twoFunctorShift S₀ S hrQ) (twoFunctorShift_addHyp S₀ S hrQ)

include hrQ in
/-- **CL Theorem 1.1** (arXiv:1111.1431v3, §1.2, for every symmetrizable Cartan datum, under CL's
hypotheses only): a `Q`-strong 2-representation (Definition 1.2) whose KLR action is given by CL's
polynomials `Q = qCL S₀` and scalars `r_i = S₀.r i` extends to a 2-representation of `U̇_{S₀}(g)`:
a pseudofunctor from the Karoubi completion `UQDot RD S₀` of `U_{S₀}(g)` to the target bicategory
`B` (the extension `DotExt.ext` of `twoFunctorShift` to the additive Karoubi envelope). -/
abbrev twoFunctorDot : Pseudofunctor (UQDot RD S₀) B :=
  DotExt.ext (twoFunctorShift S₀ S hrQ) (twoFunctorShift_addHyp S₀ S hrQ)

example : twoFunctorDot S₀ S hrQ = (twoFunctorDot S₀ S hrQ : Pseudofunctor (UQDot RD S₀) B) := rfl

/-- `twoFunctorDot` is additive on 2-morphisms. -/
theorem twoFunctorDot_map₂_add {a b : UQDot RD S₀} {f g : a ⟶ b} (η θ : f ⟶ g) :
    (twoFunctorDot S₀ S hrQ).map₂ (η + θ) =
      (twoFunctorDot S₀ S hrQ).map₂ η + (twoFunctorDot S₀ S hrQ).map₂ θ :=
  DotExt.ext_map₂_add _ _ η θ

/-- `twoFunctorDot` is `k`-linear on 2-morphisms. -/
theorem twoFunctorDot_map₂_smul {a b : UQDot RD S₀} {f g : a ⟶ b} (r : k) (η : f ⟶ g) :
    (twoFunctorDot S₀ S hrQ).map₂ (r • η) = r • (twoFunctorDot S₀ S hrQ).map₂ η :=
  DotExt.ext_map₂_smul _ _ (twoFunctorShift_map₂_smul S₀ S hrQ) r η

/-! ### `twoFunctorDot` extends `twoFunctorShift` -/

variable (RD) in
/-- The inclusion of `U_Q(g)` before direct sums into its Karoubi completion: `x ↦ ((x), 1)`. -/
abbrev inclDot : Pseudofunctor (UQShift RD S₀) (UQDot RD S₀) :=
  DotExt.incl (UQShift RD S₀)

/-- **`twoFunctorDot` extends `twoFunctorShift`** on 1-morphisms: the image of the inclusion of
`x` is isomorphic to `twoFunctorShift x`. -/
abbrev twoFunctorDotInclIso {a b : UQShift RD S₀} (x : a ⟶ b) :
    (twoFunctorDot S₀ S hrQ).map ((inclDot RD S₀).map x) ≅ (twoFunctorShift S₀ S hrQ).map x :=
  DotExt.inclIso _ _ x

/-- **Naturality**: the isomorphisms `twoFunctorDotInclIso` intertwine `twoFunctorDot` on the
image of a 2-morphism and `twoFunctorShift`. -/
theorem twoFunctorDotInclIso_naturality {a b : UQShift RD S₀} {x y : a ⟶ b} (η : x ⟶ y) :
    (twoFunctorDot S₀ S hrQ).map₂ ((inclDot RD S₀).map₂ η) ≫
        (twoFunctorDotInclIso S₀ S hrQ y).hom =
      (twoFunctorDotInclIso S₀ S hrQ x).hom ≫ (twoFunctorShift S₀ S hrQ).map₂ η := by
  -- The two types agree up to the normalization of universe levels (see `kernel_exact`).
  kernel_exact DotExt.inclIso_naturality (twoFunctorShift S₀ S hrQ)
    (twoFunctorShift_addHyp S₀ S hrQ) η

/-- **Compatibility with the composition constraints**: under `twoFunctorDotInclIso`, the
composition constraint of `twoFunctorDot` at the inclusions of `x` and `y` is that of
`twoFunctorShift` at `(x, y)`. -/
theorem twoFunctorDotInclIso_mapComp {a b c : UQShift RD S₀} (x : a ⟶ b) (y : b ⟶ c) :
    ((twoFunctorDot S₀ S hrQ).mapComp ((inclDot RD S₀).map x) ((inclDot RD S₀).map y)).hom ≫
        (twoFunctorDotInclIso S₀ S hrQ x).hom ▷
            (twoFunctorDot S₀ S hrQ).map ((inclDot RD S₀).map y) ≫
          (twoFunctorShift S₀ S hrQ).map x ◁ (twoFunctorDotInclIso S₀ S hrQ y).hom =
      (twoFunctorDot S₀ S hrQ).map₂ ((inclDot RD S₀).mapComp x y).inv ≫
        (twoFunctorDotInclIso S₀ S hrQ (x ≫ y)).hom ≫
          ((twoFunctorShift S₀ S hrQ).mapComp x y).hom := by
  kernel_exact DotExt.inclIso_mapComp (twoFunctorShift S₀ S hrQ)
    (twoFunctorShift_addHyp S₀ S hrQ) x y

/-- **Compatibility with the identity constraints**: under `twoFunctorDotInclIso`, the identity
constraint of `twoFunctorDot` at the inclusion of `a` is that of `twoFunctorShift`. -/
theorem twoFunctorDotInclIso_mapId (a : UQShift RD S₀) :
    (twoFunctorDot S₀ S hrQ).map₂ ((inclDot RD S₀).mapId a).hom ≫
        ((twoFunctorDot S₀ S hrQ).mapId ((inclDot RD S₀).obj a)).hom =
      (twoFunctorDotInclIso S₀ S hrQ (𝟙 a)).hom ≫ ((twoFunctorShift S₀ S hrQ).mapId a).hom := by
  kernel_exact DotExt.inclIso_mapId (twoFunctorShift S₀ S hrQ)
    (twoFunctorShift_addHyp S₀ S hrQ) a

end QStrong

end Model

end Categorification.TwoRep
