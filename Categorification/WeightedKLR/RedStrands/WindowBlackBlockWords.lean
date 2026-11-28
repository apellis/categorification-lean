/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.WindowBlackBlock

/-!
# The black block beside the window: regrouping the generators

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, input (B3), steps 1–3 of the paper
argument for (B3-L). The end corner `e_L T̃^{λ⁺}` is spanned by the generators
`γ_{(x, j, u)} = x · e(j) · ψ_u e(u⁻¹ (i j))` (`CupCap.genElt`), where `x` is a basis term of
`T̃^λ` with dots on top and bottom `i`, `j` a red-ordered loading of the strands at the maximum
and `u` a shuffle. The term `x` only enters through the juxtaposition: `γ_{(x, j, u)} = x ·
γ_{(e(i), j, u)}`. So the generators regroup as pairs of a base generator
`c = (e(i), j, u)` (`CupCap.BaseGen`) and a basis term `x` with bottom `i`, and

  `ι(x ⊗ y) · γ_c = y · γ_{(x, j, u)}`

is the basis term of `T̃^{λ⁺}` indexed by the pair `((x, j, u), y)`, for every basis term `y` of
`T̃^{(μ,μ*)}` with bottom `j` (`CupCap.blockTensor_topTerm_mul_genElt`); the other products of a
basis term of `T̃^λ ⊗ T̃^{(μ,μ*)}` with `γ_c` vanish. Hence the coordinates of `ι(d) γ_c` in the
basis of `T̃^{λ⁺}` with dots on top are the coordinates of `d` in the tensor product basis
(`CupCap.topBasis_repr_blockGenMul`). No correction terms occur.

For `ℓ = 0` this is the regrouping of step 1 and the basis comparison of step 3 in the paper
argument for (B3-L), with `T̃^λ = R(b)`. Symmetric `Q`, any commutative ring.

## Main definitions

* `CupCap.liftGen`: the generator `(x, j, u)` of a base generator `(e(i), j, u)` and `x`.
* `CupCap.baseOf`: the base generator of a generator.
* `CupCap.blockGenMul`: the `k`-linear map `d ↦ ι(d) γ_c`.

## Main results

* `CupCap.blockTensor_topTerm_mul_genElt`: `ι(x ⊗ y) γ_c` is a basis term of `T̃^{λ⁺}`.
* `CupCap.topBasis_repr_blockGenMul`: the coordinates of `ι(d) γ_c`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

/-! ### Base generators and lifts -/

/-- The generator `(x, j, u)` of a base generator `c = (e(i), j, u)` and a basis term `x` of
`T̃^λ` with bottom `i`. -/
def liftGen (c : BaseGen ν₀ ρ₁) (x : {x // IsTopTerm ρ₁ x}) (hx : x.1.1 = c.1.1.1.1.1) :
    EndGen ν₀ ρ₁ :=
  ⟨(x, c.1.1.2), c.1.2.1, by rw [hx]; exact c.1.2.2⟩

/-- The base generator `(e(i), j, u)` of a generator `(x, j, u)`, `i` the bottom of `x`. -/
def baseOf (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a) (g : EndGen ν₀ ρ₁) :
    BaseGen ν₀ ρ₁ :=
  ⟨baseGen hρ₁ g, rfl⟩

omit [DecidableEq I] in
theorem baseGen_liftGen (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (c : BaseGen ν₀ ρ₁) (x : {x // IsTopTerm ρ₁ x}) (hx : x.1.1 = c.1.1.1.1.1) :
    baseGen hρ₁ (liftGen c x hx) = c.1 := by
  obtain ⟨⟨⟨⟨⟨i, w, d⟩, hx₀⟩, j, u⟩, hg⟩, hc⟩ := c
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  obtain ⟨⟨i', w', d'⟩, hx'⟩ := x
  obtain rfl : i' = i := hx
  rfl

omit [DecidableEq I] in
theorem baseOf_liftGen (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (c : BaseGen ν₀ ρ₁) (x : {x // IsTopTerm ρ₁ x}) (hx : x.1.1 = c.1.1.1.1.1) :
    baseOf hρ₁ (liftGen c x hx) = c :=
  Subtype.ext (baseGen_liftGen hρ₁ c x hx)

omit [DecidableEq I] in
/-- **The pairs over a base generator**: the pair `((x, j, u), y)` built from `c = (e(i), j, u)`
is `p` exactly when `c` is the base generator of `p` and `(x, y)` are the basis terms of `p`. -/
theorem liftPair_eq_iff (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (c : BaseGen ν₀ ρ₁) (x : {x // IsTopTerm ρ₁ x}) (y : {y // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ y})
    (hx : x.1.1 = c.1.1.1.1.1) (hy : y.1.1 = c.1.1.2.1) (p : EndPair ρ₁ ρ₂) :
    (⟨(liftGen c x hx, y), hy⟩ : EndPair ρ₁ ρ₂) = p ↔
      baseOf hρ₁ p.1.1 = c ∧ (x, y) = (p.1.1.1.1, p.1.2) := by
  constructor
  · rintro rfl
    exact ⟨baseOf_liftGen hρ₁ c x hx, rfl⟩
  · rintro ⟨rfl, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl

/-! ### Products with the base generators -/

/-- A base generator `(e(i), j, u)` is fixed by `e(i)` placed on the first strands. -/
theorem prefixStendhal_e_mul_genElt_base (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (c : BaseGen ν₀ ρ₁) (hi : IsRedOrdered c.1.1.1.1.1) :
    prefixStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.e c.1.1.1.1.1 hi) *
        genElt Q Λ Λc ρ₁ ρ₃ c.1 = genElt Q Λ Λc ρ₁ ρ₃ c.1 := by
  obtain ⟨⟨⟨⟨⟨i, w, d⟩, hx₀⟩, j, u⟩, hg⟩, hc⟩ := c
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  have h := prefixStendhal_topTerm_mul_genElt_base (Q := Q) (Λ := Λ) (Λc := Λc) (ρ₃ := ρ₃) hρ₁
    ⟨(⟨(i, 1, 0), hx₀⟩, j, u), hg⟩
  rw [topTerm_base hρ₁ hi] at h
  exact h

/-- **The juxtaposition of basis terms times a base generator is a basis term**: for a base
generator `c = (e(i), j, u)` and basis terms `x` of `T̃^λ` with bottom `i` and `y` of
`T̃^{(μ,μ*)}` with bottom `j`, `ι(x ⊗ y) γ_c` is the basis term of `T̃^{λ⁺}` indexed by the pair
`((x, j, u), y)`. -/
theorem blockTensor_topTerm_mul_genElt (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (c : BaseGen ν₀ ρ₁)
    (x : {x // IsTopTerm ρ₁ x}) (y : {y // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ y})
    (hx : x.1.1 = c.1.1.1.1.1) (hy : y.1.1 = c.1.1.2.1) :
    blockTensor Q Λ Λc ν ν₀ (topTerm Q Λ (fun w => (hρ₁ w).2) x ⊗ₜ
        topTerm Q Λc (fun b => (hρ₂ b).2) y) * genElt Q Λ Λc ρ₁ ρ₃ c.1 =
      topTerm Q (plusLabels Λ Λc ℓ le_rfl) (fun w => (endWord_spec hρ₁ hρ₂ hρ₃ w).2)
        (endPairIdx ρ₁ ρ₂ ρ₃ (endWord_spec hρ₁ hρ₂ hρ₃) ⟨(liftGen c x hx, y), hy⟩) := by
  have h1 : prefixStendhal Q Λ Λc ν ν₀ (topTerm Q Λ (fun w => (hρ₁ w).2) x) *
      genElt Q Λ Λc ρ₁ ρ₃ c.1 = genElt Q Λ Λc ρ₁ ρ₃ (liftGen c x hx) :=
    (congrArg (fun g => prefixStendhal Q Λ Λc ν ν₀ (topTerm Q Λ (fun w => (hρ₁ w).2) x) *
      genElt Q Λ Λc ρ₁ ρ₃ g) (baseGen_liftGen hρ₁ c x hx).symm).trans
      (prefixStendhal_topTerm_mul_genElt_base hρ₁ (liftGen c x hx))
  rw [blockTensor_tmul, (commute_prefixStendhal_endStendhal Q Λ Λc _ _).eq, mul_assoc, h1]
  exact endStendhal_topTerm_mul_genElt ρ₂ hρ₁ hρ₂ hρ₃ ⟨(liftGen c x hx, y), hy⟩

/-- A basis term `y` whose bottom is not the loading `j` of `c` gives `ι(x ⊗ y) γ_c = 0`. -/
theorem blockTensor_topTerm_mul_genElt_of_ne_right
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b) (c : BaseGen ν₀ ρ₁) (x : T)
    (y : {y // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ y}) (hy : y.1.1 ≠ c.1.1.2.1) :
    blockTensor Q Λ Λc ν ν₀ (x ⊗ₜ topTerm Q Λc (fun b => (hρ₂ b).2) y) *
      genElt Q Λ Λc ρ₁ ρ₃ c.1 = 0 := by
  rw [blockTensor_tmul, mul_assoc,
    endStendhal_topTerm_mul_genElt_of_ne (fun b => (hρ₂ b).2) c.1 y hy, mul_zero]

/-- A basis term `x` whose bottom is not the loading `i` of `c` gives `ι(x ⊗ y) γ_c = 0`. -/
theorem blockTensor_topTerm_mul_genElt_of_ne_left
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a) (c : BaseGen ν₀ ρ₁)
    (x : {x // IsTopTerm ρ₁ x}) (y : Tc) (hx : x.1.1 ≠ c.1.1.1.1.1) :
    blockTensor Q Λ Λc ν ν₀ (topTerm Q Λ (fun w => (hρ₁ w).2) x ⊗ₜ y) *
      genElt Q Λ Λc ρ₁ ρ₃ c.1 = 0 := by
  have hi : IsRedOrdered c.1.1.1.1.1 := c.1.1.1.2.1
  have h0 : prefixStendhal Q Λ Λc ν ν₀ (topTerm Q Λ (fun w => (hρ₁ w).2) x) *
      prefixStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.e c.1.1.1.1.1 hi) = 0 := by
    rw [← map_mul, topTerm_mul_e, ite_eq_right_of_eq_false _ _ (eq_false hx), map_zero]
  rw [blockTensor_tmul, (commute_prefixStendhal_endStendhal Q Λ Λc _ _).eq, mul_assoc,
    ← prefixStendhal_e_mul_genElt_base hρ₁ c hi, ← mul_assoc (prefixStendhal Q Λ Λc ν ν₀ _), h0,
    zero_mul, mul_zero]

/-! ### Coordinates of `ι(d) γ_c` -/

variable (Q Λ Λc ρ₃) in
/-- The `k`-linear map `d ↦ ι(d) γ_c` of a base generator `c`. -/
def blockGenMul (c : BaseGen ν₀ ρ₁) : T ⊗[k] Tc →ₗ[k] Tp :=
  (LinearMap.mulRight k (genElt Q Λ Λc ρ₁ ρ₃ c.1)).comp (blockTensorLin Q Λ Λc ν ν₀)

theorem blockGenMul_apply (c : BaseGen ν₀ ρ₁) (d : T ⊗[k] Tc) :
    blockGenMul Q Λ Λc ρ₃ c d = blockTensor Q Λ Λc ν ν₀ d * genElt Q Λ Λc ρ₁ ρ₃ c.1 := rfl

open Classical in
/-- **The coordinates of `ι(d) γ_c`** in the basis of `T̃^{λ⁺}` with dots on top: at the basis
term of a pair `p = ((x, j, u), y)` it is the coordinate of `d` at `x ⊗ y` if `c` is the base
generator of `p`, and `0` otherwise. -/
theorem topBasis_repr_blockGenMul (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (c : BaseGen ν₀ ρ₁)
    (d : T ⊗[k] Tc) (p : EndPair ρ₁ ρ₂) :
    (topBasis Q (plusLabels Λ Λc ℓ le_rfl) hQ (endWord ρ₁ ρ₂ ρ₃) (endWord_spec hρ₁ hρ₂ hρ₃)).repr
        (blockGenMul Q Λ Λc ρ₃ c d) (endPairIdx ρ₁ ρ₂ ρ₃ (endWord_spec hρ₁ hρ₂ hρ₃) p) =
      if baseOf hρ₁ p.1.1 = c then
        ((topBasis Q Λ hQ ρ₁ hρ₁).tensorProduct (topBasis Q Λc hQ ρ₂ hρ₂)).repr d
          (p.1.1.1.1, p.1.2)
      else 0 := by
  classical
  set Bp := topBasis Q (plusLabels Λ Λc ℓ le_rfl) hQ (endWord ρ₁ ρ₂ ρ₃)
    (endWord_spec hρ₁ hρ₂ hρ₃)
  set BD := (topBasis Q Λ hQ ρ₁ hρ₁).tensorProduct (topBasis Q Λc hQ ρ₂ hρ₂)
  set b₀ := endPairIdx ρ₁ ρ₂ ρ₃ (endWord_spec hρ₁ hρ₂ hρ₃) p
  have hb : ∀ xy, Bp.repr (blockGenMul Q Λ Λc ρ₃ c (BD xy)) b₀ =
      if baseOf hρ₁ p.1.1 = c then BD.repr (BD xy) (p.1.1.1.1, p.1.2) else 0 := fun xy => by
    obtain ⟨x, y⟩ := xy
    rw [BD.repr_self, blockGenMul_apply, Module.Basis.tensorProduct_apply, topBasis_apply,
      topBasis_apply]
    by_cases hx : x.1.1 = c.1.1.1.1.1
    · by_cases hy : y.1.1 = c.1.1.2.1
      · rw [blockTensor_topTerm_mul_genElt hρ₁ hρ₂ hρ₃ c x y hx hy,
          ← topBasis_apply hQ _ (endWord_spec hρ₁ hρ₂ hρ₃), Bp.repr_self, Finsupp.single_apply,
          Finsupp.single_apply]
        have hinj := endPairIdx_injective (ρ₃ := ρ₃) (endWord_spec hρ₁ hρ₂ hρ₃)
        have hiff := liftPair_eq_iff hρ₁ c x y hx hy p
        by_cases hp : (⟨(liftGen c x hx, y), hy⟩ : EndPair ρ₁ ρ₂) = p
        · obtain ⟨h1, h2⟩ := hiff.1 hp
          rw [ite_eq_left_of_eq_true _ _ (eq_true (congrArg _ hp)),
            ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hp (hinj h))]
          split_ifs with h1 h2
          · exact (hp (hiff.2 ⟨h1, h2⟩)).elim
          · rfl
          · rfl
      · rw [blockTensor_topTerm_mul_genElt_of_ne_right hρ₂ c _ y hy, map_zero, Finsupp.coe_zero,
          Pi.zero_apply]
        split_ifs with h1
        · refine (Finsupp.single_apply_eq_zero.2 fun hh => (hy ?_).elim).symm
          subst h1
          rw [show y = p.1.2 from (congrArg Prod.snd hh).symm]
          exact p.2
        · rfl
    · rw [blockTensor_topTerm_mul_genElt_of_ne_left hρ₁ c x _ hx, map_zero, Finsupp.coe_zero,
        Pi.zero_apply]
      split_ifs with h1
      · refine (Finsupp.single_apply_eq_zero.2 fun hh => (hx ?_).elim).symm
        subst h1
        rw [show x = p.1.1.1.1 from (congrArg Prod.fst hh).symm]
        rfl
      · rfl
  have hext := BD.ext (f₁ := (Bp.coord b₀).comp (blockGenMul Q Λ Λc ρ₃ c))
    (f₂ := if baseOf hρ₁ p.1.1 = c then BD.coord (p.1.1.1.1, p.1.2) else 0) fun xy => by
      rw [LinearMap.comp_apply, Bp.coord_apply, hb]
      split_ifs <;> rfl
  have := LinearMap.congr_fun hext d
  rw [LinearMap.comp_apply, Bp.coord_apply] at this
  rw [this]
  split_ifs <;> rfl

end Categorification.Stendhal.CupCap
