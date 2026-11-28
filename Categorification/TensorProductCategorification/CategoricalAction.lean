/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqFullCL
import Categorification.TwoRep.RouqUpKLR
import Categorification.TwoRep.LinearCat

/-!
# Categorical actions on abelian categories (Losev–Webster §3.1)

I. Losev, B. Webster, *On uniqueness of tensor products of irreducible categorifications*,
arXiv:1303.1336v3, §3.1: a categorical `g`-action on an abelian `K`-linear category is an action
of Rouquier's 2-category, that is, exact functors `F_i` such that `F^k` carries an action of the
KLR algebra `R_k`, exact right adjoints `E_i`, and invertibility of Rouquier's map `ρ_{s,μ}`.

Here an action is a `TwoRep.RouqFamily` in `LinearCat k` (Brundan, arXiv:1501.00350v1,
Definition 1.1, which is Rouquier's definition in Brundan's form): the single-colour KLR
relations and the `sl₂` inversion are fields of `RouqFamily`, the mixed KLR relations are
`RouqUpKLR` for the polynomials `Q`, and the mixed inversion is `BrundanMixedInversion`.
Its weight spaces are required to be abelian (`IsAbelianCat`, stated as properties of the given
preadditive structure, so that no second preadditive structure arises), and the functors exact.

**Conventions.** The 1-morphisms of `RouqFamily` that carry the KLR action are called `E` and
raise the weight of the root datum; Losev–Webster call them `F_i` and let them lower weights.
So the weight space `fam.obj x` is Losev–Webster's weight space of weight `-x`, `fam.E` is their
`F_i` and `fam.F` their right adjoint `E_i`. This matches the indexing of Webster's action in the
library (`Stendhal.blackRouqData`: adding a black strand raises the weight).
-/

namespace Categorification.TensorProductCategorification

open CategoryTheory Limits TwoRep QuantumGroup UDot

universe w v u u₁

/-- A preadditive category is **abelian** (for its given preadditive structure): it has finite
products, kernels and cokernels, and every coimage–image comparison is an isomorphism
(Mathlib's `Abelian.ofCoimageImageComparisonIsIso`). -/
class IsAbelianCat (C : Type u) [Category.{v} C] [Preadditive C] : Prop where
  hasFiniteProducts : HasFiniteProducts C
  hasKernels : HasKernels C
  hasCokernels : HasCokernels C
  isIso_coimageImageComparison : ∀ {X Y : C} (f : X ⟶ Y),
    IsIso (Abelian.coimageImageComparison f)

/-- The abelian structure of an `IsAbelianCat`, extending the given preadditive structure. -/
noncomputable abbrev IsAbelianCat.abelian (C : Type u) [Category.{v} C] [Preadditive C]
    [h : IsAbelianCat C] : Abelian C :=
  haveI := h.hasFiniteProducts
  haveI := h.hasKernels
  haveI := h.hasCokernels
  haveI : ∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) :=
    h.isIso_coimageImageComparison
  Abelian.ofCoimageImageComparisonIsIso

variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]

/-- **A categorical `g`-action on abelian `k`-linear categories** (Losev–Webster,
arXiv:1303.1336v3, §3.1), for the KLR polynomials `Q`: a Rouquier family in `LinearCat k`
(Brundan's Definition 1.1) with abelian weight spaces and exact 1-morphisms. See the module
docstring for the weight convention. -/
structure CategoricalAction (k : Type w) [Field k] (RD : WeightDatum C X Y)
    (Q : I → I → MvPolynomial (Fin 2) k) where
  /-- The Rouquier family. -/
  fam : RouqFamily (B := LinearCat.{w, v, u} k) RD
  isAbelian : ∀ x, IsAbelianCat (fam.obj x)
  upKLR : RouqUpKLR fam Q
  mixedInversion : BrundanMixedInversion fam
  /-- The functors carrying the KLR action (Losev–Webster's `F_i`) are exact. -/
  preservesFiniteLimits_E : ∀ (i : I) {x y : X} (h : x + RD.iX i = y),
    PreservesFiniteLimits (fam.E i h).obj
  preservesFiniteColimits_E : ∀ (i : I) {x y : X} (h : x + RD.iX i = y),
    PreservesFiniteColimits (fam.E i h).obj
  /-- Their right adjoints (Losev–Webster's `E_i`) are exact. -/
  preservesFiniteLimits_F : ∀ (i : I) {x y : X} (h : x + RD.iX i = y),
    PreservesFiniteLimits (fam.F i h).obj
  preservesFiniteColimits_F : ∀ (i : I) {x y : X} (h : x + RD.iX i = y),
    PreservesFiniteColimits (fam.F i h).obj

namespace CategoricalAction

variable {k : Type w} [Field k] {RD : WeightDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}
  (A : CategoricalAction.{w, v, u} k RD Q)

/-- The dot `y` acts **locally nilpotently** on `F_i` (Losev–Webster §3.2): on every object it is
nilpotent. -/
def DotLocallyNilpotent : Prop :=
  ∀ (i : I) {x y : X} (h : x + RD.iX i = y) (M : A.fam.obj x),
    IsNilpotent (show CategoryTheory.End ((A.fam.E i h).obj.obj M) from
      (A.fam.dot i h).hom.app M)

end CategoricalAction

end Categorification.TensorProductCategorification
