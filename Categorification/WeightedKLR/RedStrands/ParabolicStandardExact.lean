/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleDescent

/-!
# Exactness of the induced standardization

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5,
Proposition 5.7, for the induced model of standardization. Standardization of a module `N`
over the two factor algebras at the cut (the tensor product algebra of the first `ℓ` red
strands and the cyclotomic quotient of the last one) is modelled by the quotient
`ParabolicStandard N` of affine parabolic induction by the subspace supported on the loadings
whose red strands are out of order (`Stendhal.ParabolicStandard`).

* `KLR.KLRAlgebra.indDecomp_mapRight_apply`: in the decomposition `Ind N ≅ ⊕_u N`, induction
  of a map acts coordinatewise.
* `KLR.KLRAlgebra.indMapRight_exact`: induction `Ind = R(ν + ν') 1_{ν,ν'} ⊗ -` is exact.
* `Stendhal.kerQuotientMap_exact`: passing to the quotient by the kernel of an idempotent
  that commutes with the maps preserves exactness.
* `Stendhal.parabolicStandardMap`: the map of standardizations induced by a map of modules
  over the two factor algebras; it is linear over the tensor product algebra
  (`parabolicStandardMap_action`).
* `Stendhal.parabolicStandardMap_exact`, `parabolicStandardMap_injective`,
  `parabolicStandardMap_surjective`: **Proposition 5.7 for the induced model**:
  standardization is exact.

Webster states Proposition 5.7 for the standardization functor of Definition 5.4. The
identification of that functor with the induced model is a separate step; the statements
here are for the induced model, for all modules and over every commutative ring.
-/

noncomputable section

namespace Categorification

namespace KLR.KLRAlgebra

open TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' : Multiset I} (hsym : KLRSymm Q)
  {N N' N'' : Type*} [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν ν') N]
  [IsScalarTower k (TensorKLR Q ν ν') N]
  [AddCommGroup N'] [Module k N'] [Module (TensorKLR Q ν ν') N']
  [IsScalarTower k (TensorKLR Q ν ν') N']
  [AddCommGroup N''] [Module k N''] [Module (TensorKLR Q ν ν') N'']
  [IsScalarTower k (TensorKLR Q ν ν') N'']

include hsym in
/-- In the decomposition `Ind N ≅ ⊕_u N`, induction of a map acts on each coordinate. -/
theorem indDecomp_mapRight_apply (g : N →ₗ[TensorKLR Q ν ν'] N') (y : Ind Q ν ν' N)
    (u : Shuffle (Seq.card_add' ν ν')) :
    indDecomp hsym N' (BalancedTensor.mapRight (k := k) g y) u = g (indDecomp hsym N y u) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp
  | tmul r n =>
    rw [BalancedTensor.mapRight_tmul, indDecomp_tmul, indDecomp_tmul, g.map_smul]
  | add y z hy hz => simp only [map_add, Pi.add_apply, hy, hz]

include hsym in
/-- **Induction is exact.** -/
theorem indMapRight_exact (f : N →ₗ[TensorKLR Q ν ν'] N') (g : N' →ₗ[TensorKLR Q ν ν'] N'')
    (h : Function.Exact f g) :
    Function.Exact (BalancedTensor.mapRight (k := k) (B := KLRAlgebra k Q (ν + ν'))
        (M := IndBimod Q ν ν') f)
      (BalancedTensor.mapRight (k := k) (B := KLRAlgebra k Q (ν + ν'))
        (M := IndBimod Q ν ν') g) := by
  intro y
  constructor
  · intro hy
    have hc (u : Shuffle (Seq.card_add' ν ν')) : ∃ n, f n = indDecomp hsym N' y u := by
      refine (h _).1 ?_
      rw [← indDecomp_mapRight_apply hsym g y u, hy, map_zero, Pi.zero_apply]
    choose n hn using hc
    refine ⟨(indDecomp hsym N).symm n, (indDecomp hsym N').injective (funext fun u => ?_)⟩
    rw [indDecomp_mapRight_apply, LinearEquiv.apply_symm_apply, hn]
  · rintro ⟨x, rfl⟩
    apply (indDecomp hsym N'').injective
    funext u
    rw [indDecomp_mapRight_apply, indDecomp_mapRight_apply, map_zero, Pi.zero_apply]
    exact (h _).2 ⟨_, rfl⟩

include hsym in
theorem indMapRight_injective (f : N →ₗ[TensorKLR Q ν ν'] N') (hf : Function.Injective f) :
    Function.Injective (BalancedTensor.mapRight (k := k) (B := KLRAlgebra k Q (ν + ν'))
      (M := IndBimod Q ν ν') f) := by
  intro y z he
  apply (indDecomp hsym N).injective
  funext u
  apply hf
  have := congrArg (fun w => indDecomp hsym N' w u) he
  simpa only [indDecomp_mapRight_apply] using this

include hsym in
theorem indMapRight_surjective (f : N →ₗ[TensorKLR Q ν ν'] N') (hf : Function.Surjective f) :
    Function.Surjective (BalancedTensor.mapRight (k := k) (B := KLRAlgebra k Q (ν + ν'))
      (M := IndBimod Q ν ν') f) := by
  intro y
  choose n hn using fun u => hf (indDecomp hsym N' y u)
  refine ⟨(indDecomp hsym N).symm n, (indDecomp hsym N').injective (funext fun u => ?_)⟩
  rw [indDecomp_mapRight_apply, LinearEquiv.apply_symm_apply, hn]

end KLR.KLRAlgebra

namespace Stendhal

section KerQuotient

variable {k : Type*} [CommRing k] {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]
  {P₁ : Module.End k M₁} {P₂ : Module.End k M₂} {P₃ : Module.End k M₃}

/-- The map `M₁ / ker P₁ → M₂ / ker P₂` induced by a map intertwining `P₁` and
`P₂`. -/
def kerQuotientMap (f : M₁ →ₗ[k] M₂) (hf : ∀ x, P₂ (f x) = f (P₁ x)) :
    M₁ ⧸ LinearMap.ker P₁ →ₗ[k] M₂ ⧸ LinearMap.ker P₂ :=
  (LinearMap.ker P₁).mapQ (LinearMap.ker P₂) f fun x hx => by
    change P₂ (f x) = 0
    rw [hf, show P₁ x = 0 from hx, map_zero]

theorem kerQuotientMap_mk (f : M₁ →ₗ[k] M₂) (hf : ∀ x, P₂ (f x) = f (P₁ x))
    (x : M₁) :
    kerQuotientMap f hf (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

/-- Passing to the quotients by the kernels of intertwined idempotents preserves
exactness. -/
theorem kerQuotientMap_exact (hP₂ : IsIdempotentElem P₂) (f : M₁ →ₗ[k] M₂)
    (g : M₂ →ₗ[k] M₃) (hf : ∀ x, P₂ (f x) = f (P₁ x))
    (hg : ∀ x, P₃ (g x) = g (P₂ x))
    (h : Function.Exact f g) : Function.Exact (kerQuotientMap f hf) (kerQuotientMap g hg) := by
  intro z
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  change kerQuotientMap g hg (Submodule.Quotient.mk y) = 0 ↔ _
  rw [kerQuotientMap_mk, Submodule.Quotient.mk_eq_zero]
  change P₃ (g y) = 0 ↔ _
  rw [hg]
  have hy : (Submodule.Quotient.mk y : M₂ ⧸ LinearMap.ker P₂) =
      Submodule.Quotient.mk (P₂ y) := by
    rw [Submodule.Quotient.eq]
    change P₂ (y - P₂ y) = 0
    rw [map_sub, ← Module.End.mul_apply, hP₂.eq, sub_self]
  constructor
  · intro h0
    obtain ⟨x, hx⟩ := (h _).1 h0
    refine ⟨Submodule.Quotient.mk (P₁ x), ?_⟩
    rw [kerQuotientMap_mk, ← hf, hx, ← Module.End.mul_apply, hP₂.eq]
    exact hy.symm
  · rintro ⟨w, hw⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
    change (Submodule.Quotient.mk (f x) : M₂ ⧸ LinearMap.ker P₂) =
      Submodule.Quotient.mk y at hw
    rw [hy, Submodule.Quotient.eq] at hw
    change P₂ (f x - P₂ y) = 0 at hw
    rw [map_sub, ← Module.End.mul_apply P₂ P₂, hP₂.eq, sub_eq_zero] at hw
    rw [← hw, hf]
    exact (h _).2 ⟨_, rfl⟩

theorem kerQuotientMap_injective (f : M₁ →ₗ[k] M₂) (hf : ∀ x, P₂ (f x) = f (P₁ x))
    (hinj : Function.Injective f) : Function.Injective (kerQuotientMap f hf) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  change kerQuotientMap f hf (Submodule.Quotient.mk x) = 0 at hz
  rw [kerQuotientMap_mk, Submodule.Quotient.mk_eq_zero] at hz
  change P₂ (f x) = 0 at hz
  rw [hf, ← map_zero f] at hz
  exact (Submodule.Quotient.mk_eq_zero _).2 (hinj hz)

theorem kerQuotientMap_surjective (f : M₁ →ₗ[k] M₂) (hf : ∀ x, P₂ (f x) = f (P₁ x))
    (hs : Function.Surjective f) : Function.Surjective (kerQuotientMap f hf) := by
  intro z
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

end KerQuotient

open KLR KLRAlgebra TypeA

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) (θ β : Multiset I)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 β)
local notation "S" => stendhalQ Q Λ
local notation "D" => parabolicFactorAlgebra Q Λ θ β
local notation "B" => TensorKLR S α δ
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)
local notation "F" => parabolicOrderedLoadings (ℓ := ℓ) θ β

variable {N N' N'' : Type*}
  [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (parabolicFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N']
  [AddCommGroup N''] [Module k N''] [Module (parabolicFactorAlgebra Q Λ θ β) N'']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N'']

/-- A map of modules over the factor algebras, as a map of their restrictions along the
affine parabolic quotient. -/
def parabolicInputHom (g : N →ₗ[D] N') :
    ParabolicInput Q Λ θ β N →ₗ[B] ParabolicInput Q Λ θ β N' where
  toFun n := (g n : N')
  map_add' := g.map_add
  map_smul' t n := g.map_smul (parabolicInputMap Q Λ θ β t) n

omit [Module k N] [Module k N'] [IsScalarTower k D N] [IsScalarTower k D N'] in
theorem parabolicInputHom_apply (g : N →ₗ[D] N') (n : N) :
    parabolicInputHom Q Λ θ β g n = g n := rfl

/-- The affine induction of a map of modules over the factor algebras. -/
def parabolicShuffleMap (g : N →ₗ[D] N') :
    ParabolicShuffle Q Λ θ β N →ₗ[KLRAlgebra k S (α + δ)] ParabolicShuffle Q Λ θ β N' :=
  BalancedTensor.mapRight (parabolicInputHom Q Λ θ β g)

theorem parabolicShuffleMap_eSum (g : N →ₗ[D] N') (y : ParabolicShuffle Q Λ θ β N) :
    parabolicShuffleAction Q Λ θ β N' (eSum S F) (parabolicShuffleMap Q Λ θ β g y) =
      parabolicShuffleMap Q Λ θ β g (parabolicShuffleAction Q Λ θ β N (eSum S F) y) :=
  ((parabolicShuffleMap Q Λ θ β g).map_smul _ y).symm

/-- **The map of standardizations** induced by a map of modules over the factor
algebras. -/
def parabolicStandardMap (g : N →ₗ[D] N') :
    ParabolicStandard Q Λ θ β N →ₗ[k] ParabolicStandard Q Λ θ β N' :=
  kerQuotientMap ((parabolicShuffleMap Q Λ θ β g).restrictScalars k)
    (parabolicShuffleMap_eSum Q Λ θ β g)

theorem parabolicStandardMap_mk (g : N →ₗ[D] N') (y : ParabolicShuffle Q Λ θ β N) :
    parabolicStandardMap Q Λ θ β g (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (parabolicShuffleMap Q Λ θ β g y) := rfl

variable (hQ : KLRSymm Q)

/-- Every element of the tensor product algebra comes from the affine KLR algebra. -/
theorem parabolicStandardAffine_surjective (t : T) :
    ∃ a : KLRAlgebra k S (α + δ), TensorProductAlgebra.mk Q Λ (θ + β)
      (orderProjection Q Λ (θ + β) (StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + β)
        (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β) a))) = t := by
  obtain ⟨c, rfl⟩ := (show Function.Surjective (TensorProductAlgebra.mk Q Λ (θ + β)) from
    RingCon.mkₐ_surjective _) t
  obtain ⟨b, rfl⟩ := orderProjection_surjective Q Λ (θ + β) c
  obtain ⟨a', rfl⟩ := StendhalAlgebraAllOrders.ofKLR_surjective b
  obtain ⟨a, rfl⟩ := (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β)).surjective a'
  exact ⟨a, rfl⟩

include hQ in
/-- The map of standardizations is linear over the tensor product algebra. -/
theorem parabolicStandardMap_action (g : N →ₗ[D] N') (t : T)
    (z : ParabolicStandard Q Λ θ β N) :
    parabolicStandardMap Q Λ θ β g (parabolicStandardAction Q Λ θ β N hQ t z) =
      parabolicStandardAction Q Λ θ β N' hQ t (parabolicStandardMap Q Λ θ β g z) := by
  obtain ⟨a, rfl⟩ := parabolicStandardAffine_surjective Q Λ θ β t
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  rw [parabolicStandardAction_affine, parabolicStandardAction_affine]
  exact congrArg Submodule.Quotient.mk ((parabolicShuffleMap Q Λ θ β g).map_smul a y)

include hQ in
/-- **Standardization is exact** (Webster, arXiv:1309.3796v3, Proposition 5.7, for the
induced model): a sequence `N → N' → N''` of modules over the factor algebras which is exact
at `N'` gives a sequence of standardizations exact at the middle. -/
theorem parabolicStandardMap_exact (f : N →ₗ[D] N') (g : N' →ₗ[D] N'')
    (h : Function.Exact f g) :
    Function.Exact (parabolicStandardMap Q Λ θ β f) (parabolicStandardMap Q Λ θ β g) :=
  kerQuotientMap_exact ((eSum_idem (Q := S) F).map (parabolicShuffleAction Q Λ θ β N')) _ _ _ _
    (indMapRight_exact (stendhalQ_swap_symm Q Λ hQ) (parabolicInputHom Q Λ θ β f)
      (parabolicInputHom Q Λ θ β g) h)

include hQ in
/-- Standardization preserves injections. -/
theorem parabolicStandardMap_injective (f : N →ₗ[D] N') (hf : Function.Injective f) :
    Function.Injective (parabolicStandardMap Q Λ θ β f) :=
  kerQuotientMap_injective _ _
    (indMapRight_injective (stendhalQ_swap_symm Q Λ hQ) (parabolicInputHom Q Λ θ β f) hf)

include hQ in
/-- Standardization preserves surjections. -/
theorem parabolicStandardMap_surjective (f : N →ₗ[D] N') (hf : Function.Surjective f) :
    Function.Surjective (parabolicStandardMap Q Λ θ β f) :=
  kerQuotientMap_surjective _ _
    (indMapRight_surjective (stendhalQ_swap_symm Q Λ hQ) (parabolicInputHom Q Λ θ β f) hf)

end Stendhal

end Categorification
