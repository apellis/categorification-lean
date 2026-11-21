/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Dimension
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastBlackLinear
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndMap
import Categorification.WeightedKLR.RedStrands.LastStrandPieceDimension

/-!
# Dimensions of standardizations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5 (the dimension count). For the induced model `S N = ParabolicStandard N` of
standardization, over a field `k`:

* `finrank_parabolicStandard_congr`: isomorphic modules over the factor algebras have
  standardizations of the same dimension;
* `finrank_parabolicStandard_of_exact`: dimension of standardization is additive on short exact
  sequences (Proposition 5.7, induced model);
* `finrank_parabolicStandard_prod`, `finrank_parabolicStandard_pi`,
  `finrank_parabolicStandard_of_equiv_prod_pi`: `dim S(X × N^n) = dim S X + n dim S N`, the form
  in which the commutation isomorphisms `₁Eᵢ ₁Fᵢ N ≅ ₁Fᵢ ₁Eᵢ N ⊕ N^{⊕ n}` enter;
* `finrank_lastBlackRes_eq`: the `E`-part, `dim E_i S(N) = dim S(₁E_i N) + dim S(₂E_i N)`, for
  `θ = i + θ₀` and `β = i + β₀` (the colour `i` occurs in both blocks); and
  `finrank_fixSub_lastStrandIdem_parabolicStandardT_eq`, the same count for the piece of
  `S N` over `T(θ + β)` whose last strand is black of colour `i`.

The `E`-part sequence `lastBlackRes_exact` is available only when `i` occurs in both blocks;
the cases where `i` is absent from `θ` or from `β` are not covered here.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section General

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ β : Multiset I)
  (hQ : KLRSymm Q)

local notation "D" => parabolicFactorAlgebra Q Λ θ β

variable {N N' N'' : Type*}
  [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (parabolicFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N']
  [AddCommGroup N''] [Module k N''] [Module (parabolicFactorAlgebra Q Λ θ β) N'']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N'']

include hQ in
/-- **Standardization respects isomorphisms in dimension** (Webster, arXiv:1309.3796v3, proof
of Proposition 5.5): `N ≅ N'` over the factor algebras gives `dim S N = dim S N'`. -/
theorem finrank_parabolicStandard_congr (e : N ≃ₗ[D] N') :
    Module.finrank k (ParabolicStandard Q Λ θ β N) =
      Module.finrank k (ParabolicStandard Q Λ θ β N') :=
  (LinearEquiv.ofBijective (parabolicStandardMap Q Λ θ β e.toLinearMap)
    ⟨parabolicStandardMap_injective Q Λ θ β hQ _ e.injective,
      parabolicStandardMap_surjective Q Λ θ β hQ _ e.surjective⟩).finrank_eq

include hQ in
/-- **Dimension of standardization is additive on short exact sequences** (Webster,
arXiv:1309.3796v3, Proposition 5.7 for the induced model, in the proof of Proposition 5.5). -/
theorem finrank_parabolicStandard_of_exact {f : N →ₗ[D] N'} {g : N' →ₗ[D] N''}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N')] :
    Module.finrank k (ParabolicStandard Q Λ θ β N') =
      Module.finrank k (ParabolicStandard Q Λ θ β N) +
        Module.finrank k (ParabolicStandard Q Λ θ β N'') :=
  Graded.finrank_eq_add_of_exact (parabolicStandardMap_injective Q Λ θ β hQ f hf)
    (parabolicStandardMap_surjective Q Λ θ β hQ g hg)
    (parabolicStandardMap_exact Q Λ θ β hQ f g hfg)

include hQ in
/-- The standardization of the middle term of a short exact sequence is finite-dimensional when
those of the outer terms are. -/
theorem finiteDimensional_parabolicStandard_of_exact {f : N →ₗ[D] N'} {g : N' →ₗ[D] N''}
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N)]
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N'')] :
    FiniteDimensional k (ParabolicStandard Q Λ θ β N') :=
  Module.Finite.of_exact (parabolicStandardMap_exact Q Λ θ β hQ f g hfg)
    (parabolicStandardMap_surjective Q Λ θ β hQ g hg)

include hQ in
/-- The standardization of a zero module is zero. -/
theorem subsingleton_parabolicStandard [Subsingleton N] :
    Subsingleton (ParabolicStandard Q Λ θ β N) := by
  let s := parabolicStandardMap Q Λ θ β (LinearMap.id : N →ₗ[D] N)
  have hinj : Function.Injective s :=
    parabolicStandardMap_injective Q Λ θ β hQ _ Function.injective_id
  have hex : Function.Exact s s := parabolicStandardMap_exact Q Λ θ β hQ _ _
    (fun y => ⟨fun _ => ⟨y, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩)
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : ParabolicStandard Q Λ θ β N, z = 0 := fun z => by
    have h1 : s (s z) = 0 := (hex (s z)).2 ⟨z, rfl⟩
    exact hinj (hinj (h1.trans (by rw [map_zero, map_zero])))
  rw [hx x, hx y]

include hQ in
/-- `S(X × Y)` is finite-dimensional when `S X` and `S Y` are. -/
theorem finiteDimensional_parabolicStandard_prod
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N)]
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N')] :
    FiniteDimensional k (ParabolicStandard Q Λ θ β (N × N')) :=
  finiteDimensional_parabolicStandard_of_exact Q Λ θ β hQ (f := LinearMap.inl D N N')
    (g := LinearMap.snd D N N') LinearMap.snd_surjective Function.Exact.inl_snd

include hQ in
/-- **`dim S(X × Y) = dim S X + dim S Y`** (Webster, arXiv:1309.3796v3, proof of Proposition
5.5). -/
theorem finrank_parabolicStandard_prod
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N)]
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N')] :
    Module.finrank k (ParabolicStandard Q Λ θ β (N × N')) =
      Module.finrank k (ParabolicStandard Q Λ θ β N) +
        Module.finrank k (ParabolicStandard Q Λ θ β N') := by
  have := finiteDimensional_parabolicStandard_prod Q Λ θ β hQ (N := N) (N' := N')
  exact finrank_parabolicStandard_of_exact Q Λ θ β hQ (f := LinearMap.inl D N N')
    (g := LinearMap.snd D N N') LinearMap.inl_injective LinearMap.snd_surjective
    Function.Exact.inl_snd

include hQ in
/-- `S(N^n)` is finite-dimensional when `S N` is. -/
theorem finiteDimensional_parabolicStandard_pi (n : ℕ)
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N)] :
    FiniteDimensional k (ParabolicStandard Q Λ θ β (Fin n → N)) := by
  induction n with
  | zero =>
    have := subsingleton_parabolicStandard Q Λ θ β hQ (N := Fin 0 → N)
    infer_instance
  | succ n ih =>
    have := finiteDimensional_parabolicStandard_prod Q Λ θ β hQ (N := N) (N' := Fin n → N)
    exact LinearEquiv.finiteDimensional (LinearEquiv.ofBijective
      (parabolicStandardMap Q Λ θ β (Fin.consLinearEquiv D (fun _ : Fin (n + 1) => N)).toLinearMap)
      ⟨parabolicStandardMap_injective Q Λ θ β hQ _ (LinearEquiv.injective _),
        parabolicStandardMap_surjective Q Λ θ β hQ _ (LinearEquiv.surjective _)⟩)

include hQ in
/-- **`dim S(N^n) = n dim S N`** (Webster, arXiv:1309.3796v3, proof of Proposition 5.5). -/
theorem finrank_parabolicStandard_pi (n : ℕ)
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N)] :
    Module.finrank k (ParabolicStandard Q Λ θ β (Fin n → N)) =
      n * Module.finrank k (ParabolicStandard Q Λ θ β N) := by
  induction n with
  | zero =>
    have := subsingleton_parabolicStandard Q Λ θ β hQ (N := Fin 0 → N)
    rw [Module.finrank_zero_of_subsingleton, zero_mul]
  | succ n ih =>
    have := finiteDimensional_parabolicStandard_pi Q Λ θ β hQ (N := N) n
    rw [← finrank_parabolicStandard_congr Q Λ θ β hQ
        (Fin.consLinearEquiv D (fun _ : Fin (n + 1) => N)),
      finrank_parabolicStandard_prod Q Λ θ β hQ, ih]
    ring

include hQ in
/-- **Dimension form of an isomorphism `Y ≅ X ⊕ N^{⊕ n}`** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5), the shape of the commutation isomorphisms `factorEFEquiv`,
`secondFactorEFEquiv`: `dim S Y = dim S X + n dim S N`. -/
theorem finrank_parabolicStandard_of_equiv_prod_pi {Y : Type*} [AddCommGroup Y] [Module k Y]
    [Module (parabolicFactorAlgebra Q Λ θ β) Y]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) Y] {n : ℕ}
    (e : Y ≃ₗ[D] N' × (Fin n → N))
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N)]
    [FiniteDimensional k (ParabolicStandard Q Λ θ β N')] :
    Module.finrank k (ParabolicStandard Q Λ θ β Y) =
      Module.finrank k (ParabolicStandard Q Λ θ β N') +
        n * Module.finrank k (ParabolicStandard Q Λ θ β N) := by
  have := finiteDimensional_parabolicStandard_pi Q Λ θ β hQ (N := N) n
  rw [finrank_parabolicStandard_congr Q Λ θ β hQ e, finrank_parabolicStandard_prod Q Λ θ β hQ,
    finrank_parabolicStandard_pi Q Λ θ β hQ]

end General

section LastBlack

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ₀ β₀ : Multiset I)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "θ" => ((Si i) + θ₀)
local notation "β" => ((Si i) + β₀)

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  (hQ : KLRSymm Q)

local notation "Er" => LastResRight Q Λ i θ₀ β₀ N
local notation "El" => LastResLeft Q Λ i θ₀ β₀ N

/-- **Webster, Prop 5.5, `E`-part, in dimension form** (arXiv:1309.3796v3, proof of
Proposition 5.5): for `θ = i + θ₀` and `β = i + β₀`,
`dim E_i S(N) = dim S(₁E_i N) + dim S(₂E_i N)`. -/
theorem finrank_lastBlackRes_eq
    [FiniteDimensional k
      (BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ))] :
    Module.finrank k
        (BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ)) =
      Module.finrank k (ParabolicStandard Q Λ θ₀ β El) +
        Module.finrank k (ParabolicStandard Q Λ θ β₀ Er) := by
  rw [Graded.finrank_eq_add_of_exact (lastBlackResTwo_injective Q Λ i θ₀ β₀ N hQ)
    (lastBlackResOne_surjective Q Λ i θ₀ β₀ N hQ) (lastBlackRes_exact Q Λ i θ₀ β₀ N hQ),
    add_comm]

/-- `E_i S(N)` is finite-dimensional when `S(₁E_i N)` and `S(₂E_i N)` are. -/
theorem finiteDimensional_lastBlackRes
    [FiniteDimensional k (ParabolicStandard Q Λ θ₀ β El)]
    [FiniteDimensional k (ParabolicStandard Q Λ θ β₀ Er)] :
    FiniteDimensional k
      (BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ)) :=
  Module.Finite.of_exact (lastBlackRes_exact Q Λ i θ₀ β₀ N hQ)
    (lastBlackResOne_surjective Q Λ i θ₀ β₀ N hQ)

/-- The scalar tower `k → T(θ + β) → S N` (a local instance). -/
local instance parabolicStandardT_isScalarTower (θ' β' : Multiset I) (M : Type*) [AddCommGroup M]
    [Module k M] [Module (parabolicFactorAlgebra Q Λ θ' β') M]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ' β') M] :
    IsScalarTower k (TensorProductAlgebra k Q Λ (θ' + β')) (ParabolicStandardT Q Λ θ' β' M hQ) :=
  ⟨fun c t y => DFunLike.congr_fun (map_smul (parabolicStandardAction Q Λ θ' β' M hQ) c t) y⟩

/-- **The black-last piece of `S N`** (Webster, arXiv:1309.3796v3, proof of Proposition 5.5):
for `θ = i + θ₀` and `β = i + β₀`, the piece of `S N` over `T(θ + β)` whose last strand is
black of colour `i` has dimension `dim S(₁E_i N) + dim S(₂E_i N)`. -/
theorem finrank_fixSub_lastStrandIdem_parabolicStandardT_eq
    [FiniteDimensional k
      (BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ))] :
    Module.finrank k (fixSub k (ParabolicStandardT Q Λ θ β N hQ)
        (lastStrandIdem Q Λ (θ + β) (some i))) =
      Module.finrank k (ParabolicStandard Q Λ θ₀ β El) +
        Module.finrank k (ParabolicStandard Q Λ θ β₀ Er) := by
  rw [lastStrandIdem_some Q Λ (θ + β) i (θ₀ + β) (lastBlack_weight i θ₀ β₀),
    ← finrank_lastBlackRes_eq Q Λ i θ₀ β₀ N hQ]
  rfl

end LastBlack

end Categorification.Stendhal
