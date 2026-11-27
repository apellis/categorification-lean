/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidHomInjective
import Categorification.WeightedKLR.RedStrands.HalfTwistDimension
import Categorification.WeightedKLR.RedStrands.BraidedStandardDerived
import Categorification.Algebra.DerivedTensorProjectiveHom

set_option backward.isDefEq.respectTransparency false

/-!
# The half twist is bijective on morphisms between sequence projectives

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.15. On the loading projectives `e(t) T^λ` of the identity red order, the braid
`- ⊗ B(1, κ)` is the cut `e(t) V e_κ` (`loadingProjectiveTensorEquiv`), and on morphisms it is
left multiplication on the cuts (`cutMul`). This map is injective
(`eq_zero_of_identityCornerMap_mul_violCorner`); for the half twist both sides have the same
finite dimension (`finrank_hom_halfTwist_braidF`), so it is bijective
(`bijective_cutMul_halfTwist`), and so is the derived half twist on these morphisms
(`bijective_braidingFunctor_map_halfTwist`).

## Main results

* `homRingEquivCongr`: morphisms along a ring isomorphism, as a linear equivalence over the
  common ground field.
* `cutMul`, `cutMul_injective`, `loadingCutFun_braidTensorFun`.
* `finrank_hom_rIdeal_eq`, `finrank_hom_violCorner_eq_braidF`: the dimension transports.
* `bijective_cutMul_halfTwist`, `bijective_braidingFunctor_map_halfTwist`.
-/

noncomputable section

namespace Categorification

open MulOpposite

section HomCongr

variable {k R S : Type*} [CommSemiring k] [Semiring R] [Semiring S] [Algebra k R] [Algebra k S]
  {M N M' N' : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module k N]
  [IsScalarTower k R N] [AddCommMonoid M'] [Module S M'] [AddCommMonoid N'] [Module S N']
  [Module k N'] [IsScalarTower k S N']

/-- Morphisms along a ring isomorphism `φ : R ≃ S` compatible with the scalars `k`, for
`φ`-semilinear bijections of the sources and of the targets. -/
def homRingEquivCongr (φ : R ≃+* S) (hφ : ∀ c : k, φ (algebraMap k R c) = algebraMap k S c)
    (eM : M ≃+ M') (heM : ∀ (r : R) (m : M), eM (r • m) = φ r • eM m)
    (eN : N ≃+ N') (heN : ∀ (r : R) (n : N), eN (r • n) = φ r • eN n) :
    (M →ₗ[R] N) ≃ₗ[k] (M' →ₗ[S] N') where
  toFun f :=
    { toFun := fun m' => eN (f (eM.symm m'))
      map_add' := fun a b => by rw [map_add, map_add, map_add]
      map_smul' := fun s m' => by
        have : eM.symm (s • m') = φ.symm s • eM.symm m' := by
          apply eM.injective
          rw [heM, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        rw [this, map_smul, heN, RingEquiv.apply_symm_apply, RingHom.id_apply] }
  invFun g :=
    { toFun := fun m => eN.symm (g (eM m))
      map_add' := fun a b => by rw [map_add, map_add, map_add]
      map_smul' := fun r m => by
        apply eN.injective
        rw [heM, map_smul, AddEquiv.apply_symm_apply, RingHom.id_apply, heN,
          AddEquiv.apply_symm_apply] }
  left_inv f := LinearMap.ext fun m => by simp
  right_inv g := LinearMap.ext fun m' => by simp
  map_add' f g := LinearMap.ext fun m' => by simp
  map_smul' c f := LinearMap.ext fun m' => by
    change eN ((c • f) (eM.symm m')) = c • eN (f (eM.symm m'))
    rw [LinearMap.smul_apply, ← algebraMap_smul R c, heN, hφ, algebraMap_smul]

theorem finrank_hom_eq_of_ringEquiv (φ : R ≃+* S)
    (hφ : ∀ c : k, φ (algebraMap k R c) = algebraMap k S c)
    (eM : M ≃+ M') (heM : ∀ (r : R) (m : M), eM (r • m) = φ r • eM m)
    (eN : N ≃+ N') (heN : ∀ (r : R) (n : N), eN (r • n) = φ r • eN n) :
    Module.finrank k (M →ₗ[R] N) = Module.finrank k (M' →ₗ[S] N') :=
  (homRingEquivCongr φ hφ eM heM eN heN).finrank_eq

theorem rIdeal_eq_smul_gen {A : Type*} [Ring A] {f : A} (hf : IsIdempotentElem f)
    (p : rIdeal f) : p = op p.1 • (⟨f, hf⟩ : rIdeal f) :=
  Subtype.ext (by
    change p.1 = f * p.1
    exact (mem_rIdeal.1 p.2).symm)

end HomCongr

namespace Stendhal.BraidedStendhalAlgebra

open KLR Equiv DG
open scoped DG.DegreeZero

section Cut


variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)

variable {t t' : Seq (stendhalWeight ℓ ν)} (ht : redWord t = List.finRange ℓ)
  (ht' : redWord t' = List.finRange ℓ)
  (κ : List (Fin ℓ))

/-- The generator `e(t)` of the loading projective `e(t) (e_ord V e_ord)`. -/
def loadingGen : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht) :=
  ⟨_, isIdempotentElem_violLoadingIdem ht⟩

/-- The value of a morphism of loading projectives on the generator, as an element of `V`. -/
def genVal (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht) →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ]
    rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht')) : ViolQuotient k Q Λ ν :=
  (g (loadingGen ht)).1.val

theorem violLoadingIdem_mul_genVal (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
    →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht')) :
    violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e t')) * genVal ht ht' g = genVal ht ht' g :=
  congrArg Subtype.val ((mem_rIdeal (A := C (List.finRange ℓ))).1 (g (loadingGen ht)).2)

theorem genVal_mul_violLoadingIdem (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
    →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht')) :
    genVal ht ht' g * violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e t)) = genVal ht ht' g := by
  have h := congrArg (fun p => (g p).1.val) (rIdeal_eq_smul_gen (A := C (List.finRange ℓ))
    (isIdempotentElem_violLoadingIdem ht) (loadingGen ht))
  simp only [map_smul] at h
  exact h.symm

theorem val_apply_eq (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
    →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht'))
    (p : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)) :
    (g p).1.val = genVal ht ht' g * p.1.val := by
  conv_lhs => rw [rIdeal_eq_smul_gen (A := C (List.finRange ℓ)) (isIdempotentElem_violLoadingIdem ht) p, map_smul]
  rfl

/-- Left multiplication by the value of a morphism of loading projectives, on the cuts. -/
def cutMulHom (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
    →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht')) :
    violCorner k Q Λ ν t κ →ₗ[(C κ)ᵐᵒᵖ] violCorner k Q Λ ν t' κ where
  toFun y := ⟨genVal ht ht' g * y.1, mem_violCorner_iff.2 ⟨by
    rw [← mul_assoc, violLoadingIdem_mul_genVal], by
    rw [mul_assoc, (mem_violCorner_iff.1 y.2).2]⟩⟩
  map_add' y y' := Subtype.ext (mul_add _ y.1 y'.1)
  map_smul' a y := Subtype.ext (by
    change genVal ht ht' g * (y.1 * a.unop.val) = genVal ht ht' g * y.1 * a.unop.val
    rw [mul_assoc])

local notation "PL" h => ModuleCat.of (C (List.finRange ℓ))ᵐᵒᵖ
  (rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) h))
local notation "BB" κ => OpBimodule (C (List.finRange ℓ)) (braidingBimodule k Q Λ ν (List.finRange ℓ) κ)

/-- `B(1, κ) ⊗ e(t) T ≅ e(t) V e_κ` (`loadingProjectiveTensorEquiv`). -/
def loadingCutEquiv : TensorInDegreeZero (BB κ) (PL ht) ≃ₗ[(C κ)ᵐᵒᵖ] violCorner k Q Λ ν t κ :=
  loadingProjectiveTensorEquiv (κ := κ) ht

/-- `g ↦ id ⊗ g` for the braiding bimodule `B(1, κ)` on loading projectives. -/
def braidTensorMap (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
      →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht')) :
    TensorInDegreeZero (BB κ) (PL ht) →ₗ[(C κ)ᵐᵒᵖ] TensorInDegreeZero (BB κ) (PL ht') :=
  tensorInDegreeZeroMap (A := (C κ)ᵐᵒᵖ) (BB κ) (X := PL ht) (Y := PL ht') g

/-- The cut identification as a function. -/
def loadingCutFun {s : Seq (stendhalWeight ℓ ν)} (hs : redWord s = List.finRange ℓ)
    (z : TensorInDegreeZero (BB κ) (PL hs)) : violCorner k Q Λ ν s κ :=
  loadingCutEquiv hs κ z

/-- The inverse of the cut identification as a function. -/
def loadingCutInv {s : Seq (stendhalWeight ℓ ν)} (hs : redWord s = List.finRange ℓ)
    (y : violCorner k Q Λ ν s κ) : TensorInDegreeZero (BB κ) (PL hs) :=
  (loadingCutEquiv hs κ).symm y

theorem loadingCutFun_inv {s : Seq (stendhalWeight ℓ ν)} (hs : redWord s = List.finRange ℓ)
    (y : violCorner k Q Λ ν s κ) : loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ hs (loadingCutInv (k := k) (Q := Q) (Λ := Λ) κ hs y) = y :=
  (loadingCutEquiv hs κ).apply_symm_apply y

theorem loadingCutInv_fun {s : Seq (stendhalWeight ℓ ν)} (hs : redWord s = List.finRange ℓ)
    (z : TensorInDegreeZero (BB κ) (PL hs)) : loadingCutInv (k := k) (Q := Q) (Λ := Λ) κ hs (loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ hs z) = z :=
  (loadingCutEquiv hs κ).symm_apply_apply z

theorem loadingCutFun_injective {s : Seq (stendhalWeight ℓ ν)}
    (hs : redWord s = List.finRange ℓ) : Function.Injective (loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ hs) :=
  (loadingCutEquiv hs κ).injective

theorem loadingCutFun_zero {s : Seq (stendhalWeight ℓ ν)} (hs : redWord s = List.finRange ℓ) :
    loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ hs 0 = 0 :=
  map_zero (loadingCutEquiv hs κ)

theorem loadingCutFun_add {s : Seq (stendhalWeight ℓ ν)} (hs : redWord s = List.finRange ℓ)
    (z z' : TensorInDegreeZero (BB κ) (PL hs)) :
    loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ hs (z + z') = loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ hs z + loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ hs z' :=
  map_add (loadingCutEquiv hs κ) z z'

theorem loadingCutFun_tmul_val {s : Seq (stendhalWeight ℓ ν)} (hs : redWord s = List.finRange ℓ)
    (b : InDegreeZero (BB κ)) (p : InDegreeZero (PL hs)) :
    (loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ hs (TensorProductOver.tmul (C (List.finRange ℓ))ᵐᵒᵖ b p)).1 = p.1.val * b.1 :=
  rfl

/-- `id ⊗ g` as a function. -/
def braidTensorFun (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
      →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht'))
    (z : TensorInDegreeZero (BB κ) (PL ht)) : TensorInDegreeZero (BB κ) (PL ht') :=
  braidTensorMap ht ht' κ g z

theorem braidTensorFun_zero (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
      →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht')) :
    braidTensorFun ht ht' κ g 0 = 0 :=
  map_zero (braidTensorMap ht ht' κ g)

theorem braidTensorFun_add (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
      →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht'))
    (z z' : TensorInDegreeZero (BB κ) (PL ht)) :
    braidTensorFun ht ht' κ g (z + z') = braidTensorFun ht ht' κ g z + braidTensorFun ht ht' κ g z' :=
  map_add (braidTensorMap ht ht' κ g) z z'

theorem braidTensorFun_tmul (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
      →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht'))
    (b : InDegreeZero (BB κ)) (p : InDegreeZero (PL ht)) :
    braidTensorFun ht ht' κ g (TensorProductOver.tmul (C (List.finRange ℓ))ᵐᵒᵖ b p) =
      TensorProductOver.tmul (C (List.finRange ℓ))ᵐᵒᵖ b (show InDegreeZero (PL ht') from g p) :=
  rfl

/-- **The braid of a morphism of loading projectives is `cutMulHom`**: under the
identifications `B ⊗ e(t) T = e(t) V e_κ`, `id ⊗ g` is left multiplication by `g(e(t))`. -/
theorem loadingCutFun_braidTensorFun (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
      →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht'))
    (z : TensorInDegreeZero (BB κ) (PL ht)) :
    loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ ht' (braidTensorFun ht ht' κ g z) =
      cutMulHom ht ht' κ g (loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ ht z) := by
  induction z using TensorProductOver.induction_on with
  | zero => rw [braidTensorFun_zero, loadingCutFun_zero, loadingCutFun_zero, map_zero]
  | tmul b p =>
    apply Subtype.ext
    rw [braidTensorFun_tmul, loadingCutFun_tmul_val]
    change (g p).1.val * b.1 = genVal ht ht' g * (p.1.val * b.1)
    rw [val_apply_eq, mul_assoc]
  | add x y hx hy =>
    rw [braidTensorFun_add, loadingCutFun_add, hx, hy, loadingCutFun_add, map_add]

end Cut

section CutLinear

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)

variable {t t' : Seq (stendhalWeight ℓ ν)} (ht : redWord t = List.finRange ℓ)
  (ht' : redWord t' = List.finRange ℓ) (κ : List (Fin ℓ))

/-- `cutMulHom` is linear in the morphism. -/
def cutMul : (rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
    →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht')) →ₗ[k]
    (violCorner k Q Λ ν t κ →ₗ[(C κ)ᵐᵒᵖ] violCorner k Q Λ ν t' κ) where
  toFun := cutMulHom ht ht' κ
  map_add' g g' := LinearMap.ext fun y => Subtype.ext (by
    change (g (loadingGen ht) + g' (loadingGen ht)).1.val * y.1 =
      genVal ht ht' g * y.1 + genVal ht ht' g' * y.1
    rw [← add_mul]
    rfl)
  map_smul' c g := LinearMap.ext fun y => Subtype.ext (by
    change (c • g (loadingGen ht)).1.val * y.1 = c • (genVal ht ht' g * y.1)
    rw [← smul_mul_assoc]
    rfl)

theorem cutMul_apply_val (g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
    →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht'))
    (y : violCorner k Q Λ ν t κ) :
    (cutMul ht ht' κ g y).1 = genVal ht ht' g * y.1 := rfl

local notation "PL" h => ModuleCat.of (C (List.finRange ℓ))ᵐᵒᵖ
  (rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) h))
local notation "BB" κ => OpBimodule (C (List.finRange ℓ)) (braidingBimodule k Q Λ ν (List.finRange ℓ) κ)

theorem cutMul_eq_zero {g : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
    →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht')}
    (h : genVal ht ht' g = 0) : g = 0 := by
  refine LinearMap.ext fun p => Subtype.ext (Subtype.ext ?_)
  change (g p).1.val = 0
  rw [val_apply_eq, h, zero_mul]

/-- If the braid is bijective on the cuts, then `g ↦ id ⊗ g` is bijective. -/
theorem bijective_braidTensorMap_of_bijective_cutMul
    (h : Function.Bijective (cutMul (k := k) (Q := Q) (Λ := Λ) ht ht' κ)) :
    Function.Bijective (braidTensorMap (k := k) (Q := Q) (Λ := Λ) ht ht' κ) := by
  constructor
  · intro g g' hg
    have hf : ∀ z, braidTensorFun ht ht' κ g z = braidTensorFun ht ht' κ g' z := fun z => by
      unfold braidTensorFun
      rw [hg]
    refine h.1 (LinearMap.ext fun y => ?_)
    change cutMulHom ht ht' κ g y = cutMulHom ht ht' κ g' y
    rw [← loadingCutFun_inv (k := k) (Q := Q) (Λ := Λ) κ ht y, ← loadingCutFun_braidTensorFun,
      ← loadingCutFun_braidTensorFun, hf]
  · intro F
    let F' : violCorner k Q Λ ν t κ →ₗ[(C κ)ᵐᵒᵖ] violCorner k Q Λ ν t' κ :=
      (loadingCutEquiv ht' κ).toLinearMap ∘ₗ F ∘ₗ (loadingCutEquiv ht κ).symm.toLinearMap
    obtain ⟨g, hg⟩ := h.2 F'
    refine ⟨g, LinearMap.ext fun z => loadingCutFun_injective (k := k) (Q := Q) (Λ := Λ) κ ht' ?_⟩
    have e := LinearMap.congr_fun hg (loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ ht z)
    change cutMulHom ht ht' κ g (loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ ht z) =
      loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ ht'
        (F (loadingCutInv (k := k) (Q := Q) (Λ := Λ) κ ht
          (loadingCutFun (k := k) (Q := Q) (Λ := Λ) κ ht z))) at e
    rw [loadingCutInv_fun, ← loadingCutFun_braidTensorFun] at e
    exact e

variable (hQ : KLRSymm Q)
  (ρ : ∀ ν : Multiset I, Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (hρ : ∀ ν, TypeA.IsReducedChoice (ρ ν))
  {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q) (hbase : BaseCrossing Q)

include hQ hρ hR hbase in
/-- **The braid is faithful on morphisms of loading projectives** (Webster, arXiv:1309.3796v3,
proof of Theorem 6.15), for every red order `κ = σ(1, …, ℓ)`. -/
theorem cutMul_injective (σ : Perm (Fin ℓ)) :
    Function.Injective (cutMul (k := k) (Q := Q) (Λ := Λ) ht ht' ((List.finRange ℓ).map σ)) := by
  intro g g' hg
  have htO : IsRedOrdered t := (redWord_eq_finRange_iff t).1 ht
  let c : C (List.finRange ℓ) := (g (loadingGen ht)).1 - (g' (loadingGen ht)).1
  have hc : c.val = genVal ht ht' g - genVal ht ht' g' := rfl
  let x := violCornerEquiv (hρ ν) hQ c
  have hid : identityCornerMap Q Λ ν (hρ ν) hQ x = genVal ht ht' g - genVal ht ht' g' := by
    rw [identityCornerMap_apply, RingEquiv.symm_apply_apply]
    exact hc
  have he : (violCornerEquiv (hρ ν) hQ).symm (redLoadingIdem Q Λ ν t htO) =
      violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht :=
    Subtype.ext ((identityCornerMap_apply (hρ ν) hQ _).symm.trans
      (identityCornerMap_mk_e (hρ ν) hQ t htO))
  have hx : x * redLoadingIdem Q Λ ν t htO = x := by
    apply (violCornerEquiv (hρ ν) hQ).symm.injective
    rw [map_mul, he, RingEquiv.symm_apply_apply]
    refine Subtype.ext ?_
    change c.val * violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e t)) = c.val
    rw [hc, sub_mul, genVal_mul_violLoadingIdem, genVal_mul_violLoadingIdem]
  have h0 := eq_zero_of_identityCornerMap_mul_violCorner hQ ρ hρ hR hbase htO σ x hx
    fun y hy => by
      have e := congrArg Subtype.val (LinearMap.congr_fun hg ⟨y, hy⟩)
      rw [cutMul_apply_val, cutMul_apply_val] at e
      rw [hid, sub_mul, e, sub_self]
  have hgg : genVal ht ht' g = genVal ht ht' g' := by
    rw [← sub_eq_zero, ← hid, h0, map_zero]
  refine LinearMap.ext fun p => Subtype.ext (Subtype.ext ?_)
  rw [val_apply_eq, val_apply_eq, hgg]

end CutLinear

section Dimension

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)

local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)

theorem violCornerEquiv_symm_redLoadingIdem {t : Seq (stendhalWeight ℓ ν)}
    (ht : redWord t = List.finRange ℓ) :
    (violCornerEquiv hρ hQ).symm (redLoadingIdem Q Λ ν t ((redWord_eq_finRange_iff t).1 ht)) =
      violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht :=
  Subtype.ext ((identityCornerMap_apply hρ hQ _).symm.trans
    (identityCornerMap_mk_e hρ hQ t _))

theorem rightCornerEquiv_algebraMap (c : k) :
    rightCornerEquiv (Λ := Λ) (ν := ν) hρ hQ (algebraMap k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ c) =
      algebraMap k (C (List.finRange ℓ))ᵐᵒᵖ c :=
  congrArg op ((RingEquiv.symm_apply_eq _).2 (violCornerEquiv_algebraMap hρ hQ c).symm)

/-- The right sequence ideal `e(t) T^λ` as the loading ideal `f_t (e_λ V e_λ)` of the corner. -/
def rightSequenceLoadingEquiv (G : GradingDatum (stendhalQ Q Λ)) {t : Seq (stendhalWeight ℓ ν)}
    (ht : redWord t = List.finRange ℓ) :
    (rightSequenceProj G t ((redWord_eq_finRange_iff t).1 ht)).carrier ≃+
      rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht) where
  toFun m := ⟨(violCornerEquiv hρ hQ).symm m.1.unop, by
    rw [mem_rIdeal (A := C (List.finRange ℓ)), ← violCornerEquiv_symm_redLoadingIdem hρ hQ ht,
      ← map_mul]
    exact congrArg _ (congrArg unop (Graded.mem_leftIdeal.1 m.2))⟩
  invFun y := ⟨op (violCornerEquiv hρ hQ y.1), by
    have h1 : violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht * y.1 = y.1 :=
      (mem_rIdeal (A := C (List.finRange ℓ))).1 y.2
    have h2 : violCornerEquiv hρ hQ (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht) =
        redLoadingIdem Q Λ ν t ((redWord_eq_finRange_iff t).1 ht) := by
      rw [← violCornerEquiv_symm_redLoadingIdem hρ hQ ht, RingEquiv.apply_symm_apply]
    have hy : violCornerEquiv hρ hQ y.1 = redLoadingIdem Q Λ ν t ((redWord_eq_finRange_iff t).1 ht) *
        violCornerEquiv hρ hQ y.1 := by
      conv_lhs => rw [← h1]
      rw [map_mul, h2]
    change op (violCornerEquiv hρ hQ y.1) * op (redLoadingIdem Q Λ ν t _) = _
    rw [← op_mul, ← hy]⟩
  left_inv m := Subtype.ext (by
    change op (violCornerEquiv hρ hQ ((violCornerEquiv hρ hQ).symm m.1.unop)) = m.1
    rw [RingEquiv.apply_symm_apply, op_unop])
  right_inv y := Subtype.ext (by
    change (violCornerEquiv hρ hQ).symm (violCornerEquiv hρ hQ y.1) = y.1
    rw [RingEquiv.symm_apply_apply])
  map_add' a b := Subtype.ext (map_add (violCornerEquiv hρ hQ).symm a.1.unop b.1.unop)

theorem rightSequenceLoadingEquiv_smul (G : GradingDatum (stendhalQ Q Λ))
    {t : Seq (stendhalWeight ℓ ν)} (ht : redWord t = List.finRange ℓ)
    (r : (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)
    (m : (rightSequenceProj G t ((redWord_eq_finRange_iff t).1 ht)).carrier) :
    rightSequenceLoadingEquiv hρ hQ G ht (r • m) =
      rightCornerEquiv (Λ := Λ) (ν := ν) hρ hQ r • rightSequenceLoadingEquiv hρ hQ G ht m :=
  Subtype.ext (map_mul (violCornerEquiv hρ hQ).symm m.1.unop r.unop)

include hρ hQ in
/-- `dim Hom(e(t) T^λ, e(t') T^λ) = dim Hom(f_t C, f_{t'} C)` over the corner `C = e_λ V e_λ`. -/
theorem finrank_hom_rIdeal_eq (G : GradingDatum (stendhalQ Q Λ))
    {t t' : Seq (stendhalWeight ℓ ν)} (ht : redWord t = List.finRange ℓ)
    (ht' : redWord t' = List.finRange ℓ) :
    Module.finrank k (rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
        →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht')) =
      Module.finrank k ((rightSequenceProj G t ((redWord_eq_finRange_iff t).1 ht)).carrier
        →ₗ[(TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
        (rightSequenceProj G t' ((redWord_eq_finRange_iff t').1 ht')).carrier) :=
  (finrank_hom_eq_of_ringEquiv (rightCornerEquiv (Λ := Λ) (ν := ν) hρ hQ)
    (rightCornerEquiv_algebraMap hρ hQ) (rightSequenceLoadingEquiv hρ hQ G ht)
    (rightSequenceLoadingEquiv_smul hρ hQ G ht) (rightSequenceLoadingEquiv hρ hQ G ht')
    (rightSequenceLoadingEquiv_smul hρ hQ G ht')).symm

include hρ hQ in
theorem finite_hom_rIdeal (G : GradingDatum (stendhalQ Q Λ))
    {t t' : Seq (stendhalWeight ℓ ν)} (ht : redWord t = List.finRange ℓ)
    (ht' : redWord t' = List.finRange ℓ)
    [Module.Finite k ((rightSequenceProj G t ((redWord_eq_finRange_iff t).1 ht)).carrier
        →ₗ[(TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
        (rightSequenceProj G t' ((redWord_eq_finRange_iff t').1 ht')).carrier)] :
    Module.Finite k (rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht)
        →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht')) :=
  Module.Finite.equiv (homRingEquivCongr (rightCornerEquiv (Λ := Λ) (ν := ν) hρ hQ)
    (rightCornerEquiv_algebraMap hρ hQ) (rightSequenceLoadingEquiv hρ hQ G ht)
    (rightSequenceLoadingEquiv_smul hρ hQ G ht) (rightSequenceLoadingEquiv hρ hQ G ht')
    (rightSequenceLoadingEquiv_smul hρ hQ G ht'))

variable (σ : Perm (Fin ℓ))

theorem cornerRelabelOp_symm_algebraMap (κ : List (Fin ℓ)) (c : k) :
    (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ).symm
      (algebraMap k (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν) κ)ᵐᵒᵖ c) =
      algebraMap k (C (κ.map σ))ᵐᵒᵖ c := by
  rw [RingEquiv.symm_apply_eq]
  apply MulOpposite.unop_injective
  change algebraMap k (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν) κ) c =
    (violCornerRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ) (ν := ν) σ (fun _ => rfl)
      κ).symm (algebraMap k (C (κ.map σ)) c)
  rw [RingEquiv.eq_symm_apply]
  apply Subtype.ext
  change violRedPermEquiv σ (fun _ => rfl)
      (c • violMk k Q (Λ ∘ σ) ν (redProj k Q (Λ ∘ σ) ν κ)) =
    c • violMk k Q Λ ν (redProj k Q Λ ν (κ.map σ))
  rw [map_smul]
  exact congrArg (c • ·) (congrArg (violMk k Q Λ ν) (redPermAlgEquiv_redProj σ (fun _ => rfl) κ))

variable (𝔠 : QuantumGroup.CartanDatum I) (hR : IsRouquierQ 𝔠 Q)

theorem braidCutRingEquiv_algebraMap (c : k) :
    braidCutRingEquiv Λ ν 𝔠 hR σ (algebraMap k _ c) = algebraMap k _ c := by
  change (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ (List.finRange ℓ)).symm
    (rightCornerEquiv (Λ := Λ ∘ σ) (ν := ν) (FirstWeight.isReducedChoice_canChoice ν)
      hR.klrSymm (algebraMap k _ c)) = _
  rw [rightCornerEquiv_algebraMap, cornerRelabelOp_symm_algebraMap]

variable [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I),
  Module.Finite k (TensorProductAlgebra k Q Ω ν)]

local notation "G" => stendhalGradingDatum Λ hR.gradingDatum (fun i => 𝔠.dot i i / 2)
  (dotDegree 𝔠 hR)

/-- `braidCutEquiv` as an additive equivalence on the braid of a sequence projective. -/
def braidCutAddEquiv {t : Seq (stendhalWeight ℓ ν)} (ht : IsRedOrdered t) :
    (FirstWeight.braidF 𝔠 hR Λ σ ν (rightSequenceProj G t ht).toGFin).carrier ≃+
      violCorner k Q Λ ν t (List.map σ (List.finRange ℓ)) :=
  (braidCutEquiv (Λ := Λ) 𝔠 hR σ ht).toAddEquiv

theorem braidCutAddEquiv_smul {t : Seq (stendhalWeight ℓ ν)} (ht : IsRedOrdered t)
    (r : (TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ)
    (m : (FirstWeight.braidF 𝔠 hR Λ σ ν (rightSequenceProj G t ht).toGFin).carrier) :
    braidCutAddEquiv σ 𝔠 hR ht (r • m) =
      braidCutRingEquiv Λ ν 𝔠 hR σ r • braidCutAddEquiv σ 𝔠 hR ht m := by
  change braidCutEquiv (Λ := Λ) 𝔠 hR σ ht (r • m) = braidCutRingEquiv Λ ν 𝔠 hR σ r •
    braidCutEquiv (Λ := Λ) 𝔠 hR σ ht m
  rw [← LinearEquiv.map_smul]
  congr 1
  change r • m = (braidCutRingEquiv Λ ν 𝔠 hR σ).symm (braidCutRingEquiv Λ ν 𝔠 hR σ r) • m
  rw [RingEquiv.symm_apply_apply]

/-- `dim Hom(𝔅_σ P_t, 𝔅_σ P_{t'})` is the dimension of `Hom` between the cuts at `σλ`. -/
theorem finrank_hom_violCorner_eq_braidF {t t' : Seq (stendhalWeight ℓ ν)} (ht : IsRedOrdered t)
    (ht' : IsRedOrdered t') :
    Module.finrank k (violCorner k Q Λ ν t (List.map σ (List.finRange ℓ))
        →ₗ[(C (List.map σ (List.finRange ℓ)))ᵐᵒᵖ] violCorner k Q Λ ν t' (List.map σ (List.finRange ℓ))) =
      Module.finrank k ((FirstWeight.braidF 𝔠 hR Λ σ ν (rightSequenceProj G t ht).toGFin).carrier
        →ₗ[(TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ]
        (FirstWeight.braidF 𝔠 hR Λ σ ν (rightSequenceProj G t' ht').toGFin).carrier) :=
  (finrank_hom_eq_of_ringEquiv (braidCutRingEquiv Λ ν 𝔠 hR σ)
    (braidCutRingEquiv_algebraMap σ 𝔠 hR) (braidCutAddEquiv σ 𝔠 hR ht)
    (braidCutAddEquiv_smul σ 𝔠 hR ht) (braidCutAddEquiv σ 𝔠 hR ht')
    (braidCutAddEquiv_smul σ 𝔠 hR ht')).symm

theorem finite_hom_violCorner {t t' : Seq (stendhalWeight ℓ ν)} (ht : IsRedOrdered t)
    (ht' : IsRedOrdered t')
    [Module.Finite k ((FirstWeight.braidF 𝔠 hR Λ σ ν (rightSequenceProj G t ht).toGFin).carrier
        →ₗ[(TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ]
        (FirstWeight.braidF 𝔠 hR Λ σ ν (rightSequenceProj G t' ht').toGFin).carrier)] :
    Module.Finite k (violCorner k Q Λ ν t (List.map σ (List.finRange ℓ))
        →ₗ[(C (List.map σ (List.finRange ℓ)))ᵐᵒᵖ] violCorner k Q Λ ν t' (List.map σ (List.finRange ℓ))) :=
  Module.Finite.equiv (homRingEquivCongr (braidCutRingEquiv Λ ν 𝔠 hR σ)
    (braidCutRingEquiv_algebraMap σ 𝔠 hR) (braidCutAddEquiv σ 𝔠 hR ht)
    (braidCutAddEquiv_smul σ 𝔠 hR ht) (braidCutAddEquiv σ 𝔠 hR ht')
    (braidCutAddEquiv_smul σ 𝔠 hR ht'))

end Dimension

section KhovanovLauda

open QuantumGroup KL3.Diagram
open scoped Classical

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
local notation "G" Ω => stendhalGradingDatum Ω hQ.gradingDatum (fun i => C.dot i i / 2)
  (dotDegree C hQ)

include hR H hwt hw in
/-- **The half twist is bijective on morphisms of loading projectives** (Webster,
arXiv:1309.3796v3, proof of Theorem 6.15), at the Khovanov–Lauda scalars: for a red order
`κ = w(1, …, ℓ)` reversing every pair of red strands, `g ↦ g ⊗ B(1, κ)` is a bijection
`Hom(e(t) T^λ, e(t') T^λ) → Hom(e(t) V e_κ, e(t') V e_κ)`. Route hypothesis: the injectivity of
Lemma 6.8 (`RowFigureFiveHypotheses`). -/
theorem bijective_cutMul_halfTwist
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
    {t t' : Seq (stendhalWeight (ℓ + 1) ν)} (ht : redWord t = List.finRange (ℓ + 1))
    (ht' : redWord t' = List.finRange (ℓ + 1)) :
    Function.Bijective (cutMul (k := k) (Q := QL) (Λ := Λ) ht ht'
      ((List.finRange (ℓ + 1)).map w)) := by
  have htO := (redWord_eq_finRange_iff t).1 ht
  have htO' := (redWord_eq_finRange_iff t').1 ht'
  have hinj := cutMul_injective (k := k) (Q := QL) (Λ := Λ) ht ht' hQ.klrSymm
    (fun ν => FirstWeight.canChoice (ℓ + 1) ν) (fun ν => FirstWeight.isReducedChoice_canChoice ν)
    hQ (baseCrossing_std hQ hQ.klrSymm) w
  have : Module.Finite k ((rightSequenceProj (G Λ) t htO).carrier
      →ₗ[(TensorProductAlgebra k QL Λ ν)ᵐᵒᵖ] (rightSequenceProj (G Λ) t' htO').carrier) :=
    Graded.finiteDimensional_hom (rightSequenceProj (G Λ) t htO).toGFin
      (rightSequenceProj (G Λ) t' htO').toGFin
  have : Module.Finite k
      ((FirstWeight.braidF C hQ Λ w ν (rightSequenceProj (G Λ) t htO).toGFin).carrier
        →ₗ[(TensorProductAlgebra k QL (Λ ∘ w) ν)ᵐᵒᵖ]
        (FirstWeight.braidF C hQ Λ w ν (rightSequenceProj (G Λ) t' htO').toGFin).carrier) :=
    Graded.finiteDimensional_hom
      (FirstWeight.braidF C hQ Λ w ν (rightSequenceProj (G Λ) t htO).toGFin)
      (FirstWeight.braidF C hQ Λ w ν (rightSequenceProj (G Λ) t' htO').toGFin)
  have := finite_hom_rIdeal (FirstWeight.isReducedChoice_canChoice ν) hQ.klrSymm (G Λ) ht ht'
  have := finite_hom_violCorner (Λ := Λ) w C hQ htO htO'
  have hdim := ((finrank_hom_rIdeal_eq (FirstWeight.isReducedChoice_canChoice ν) hQ.klrSymm
    (G Λ) ht ht').trans (finrank_hom_halfTwist_braidF C hQ Λ ν w hR H wt hwt hw hκ htO htO').symm).trans
    (finrank_hom_violCorner_eq_braidF (Λ := Λ) w C hQ htO htO').symm
  let _ := Module.addCommMonoidToAddCommGroup k (M := rIdeal (violLoadingIdem (k := k) (Q := QL)
    (Λ := Λ) ht) →ₗ[(ViolOrderCorner (k := k) (Q := QL) (Λ := Λ) (ν := ν)
      (List.finRange (ℓ + 1)))ᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := QL) (Λ := Λ) ht'))
  let _ := Module.addCommMonoidToAddCommGroup k (M := violCorner k QL Λ ν t
    (List.map w (List.finRange (ℓ + 1))) →ₗ[(ViolOrderCorner (k := k) (Q := QL) (Λ := Λ) (ν := ν)
      (List.map w (List.finRange (ℓ + 1))))ᵐᵒᵖ] violCorner k QL Λ ν t'
        (List.map w (List.finRange (ℓ + 1))))
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

local notation "CL" κ => ViolOrderCorner (k := k) (Q := QL) (Λ := Λ) (ν := ν) κ
local notation "PL" h => ModuleCat.of (CL (List.finRange (ℓ + 1)))ᵐᵒᵖ
  (rIdeal (violLoadingIdem (k := k) (Q := QL) (Λ := Λ) h))

include hR H hwt hw in
/-- **The derived half twist is bijective on morphisms of loading projectives** (Webster,
arXiv:1309.3796v3, proof of Theorem 6.15): `𝔅_w = - ⊗ᴸ B(1, κ)` induces a bijection
`Hom(e(t) T^λ, e(t') T^λ) → Hom(𝔅_w (e(t) T^λ), 𝔅_w (e(t') T^λ))` in the derived category.
Route hypothesis: the injectivity of Lemma 6.8 (`RowFigureFiveHypotheses`). -/
theorem bijective_braidingFunctor_map_halfTwist
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
    {t t' : Seq (stendhalWeight (ℓ + 1) ν)} (ht : redWord t = List.finRange (ℓ + 1))
    (ht' : redWord t' = List.finRange (ℓ + 1)) :
    Function.Bijective ((braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1))
        ((List.finRange (ℓ + 1)).map w)).map :
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (CL (List.finRange (ℓ + 1)))ᵐᵒᵖ).obj
          (PL ht)) ⟶
        DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (CL (List.finRange (ℓ + 1)))ᵐᵒᵖ).obj
          (PL ht'))) → _) := by
  have := rIdeal_projective (isIdempotentElem_violLoadingIdem (k := k) (Q := QL) (Λ := Λ) ht)
  have := rIdeal_projective (isIdempotentElem_violLoadingIdem (k := k) (Q := QL) (Λ := Λ) ht')
  exact (derivedTensor_map_bijective_iff (A := (CL ((List.finRange (ℓ + 1)).map w))ᵐᵒᵖ)
    (OpBimodule (CL (List.finRange (ℓ + 1)))
      (braidingBimodule k QL Λ ν (List.finRange (ℓ + 1)) ((List.finRange (ℓ + 1)).map w)))
    (PL ht) (PL ht')).2 (bijective_braidTensorMap_of_bijective_cutMul ht ht' _
      (bijective_cutMul_halfTwist C hQ Λ ν w hR H wt hwt hw hκ ht ht'))

end KhovanovLauda

end Stendhal.BraidedStendhalAlgebra

end Categorification
