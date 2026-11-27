/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockWords

/-!
# The black block beside the window: freeness over `T̃^λ ⊗ T̃^{(μ,μ*)}`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, input (B3), the statement (B3-L) and step
4 of its paper argument. Let `D = T̃^λ ⊗_k T̃^{(μ,μ*)}(ν₀)`, acting on the end corner
`e_L T̃^{λ⁺}(ν + ν₀)` through the juxtaposition `ι` (`CupCap.blockTensor`). For a base generator
`c = (e(i), j, u)` (`CupCap.BaseGen`) let `1_c = e(i) ⊗ e(j)` (`CupCap.blockIdem`), and let
`D 1_c = {d | d 1_c = d}` be the cyclic projective left ideal (`CupCap.blockLeft`). Then

  `⨁_c D 1_c → e_L T̃^{λ⁺}`, `(d_c)_c ↦ ∑_c ι(d_c) γ_c`

(`CupCap.blockSum`) is a bijection onto the end corner (`CupCap.blockSum_injective`,
`CupCap.mem_range_blockSum_iff`, `CupCap.blockSumEquiv`), and it is `D`-linear:
`∑_c ι(d d_c) γ_c = ι(d) ∑_c ι(d_c) γ_c` (`CupCap.blockSum_blockLeftMul`). So `e_L T̃^{λ⁺}` is the
direct sum of the cyclic projective `D`-modules `D 1_c`.

The proof maps bases to bases. The tensor product of the bases with dots on top of `T̃^λ` and
`T̃^{(μ,μ*)}`, restricted to `D 1_c`, consists of the `x ⊗ y` with bottoms `(i, j)`
(`CupCap.topBasis_repr_mul_blockIdem`); `ι(x ⊗ y) γ_c` is the basis term of `T̃^{λ⁺}` of the pair
`((x, j, u), y)` (`CupCap.blockTensor_topTerm_mul_genElt`), and these pairs are exactly the basis
terms in the end corner (`CupCap.exists_endPairIdx`).

For `ℓ = 0`, `T̃^λ` is the KLR algebra `R(b)` of the black block (`b = ν`), `T̃^{λ⁺}(ν + ν₀)` is
`A = T̃^{(μ,μ*)}(b + ν₀)`, `D = R(b) ⊗ A′`, and this is (B3-L): `e_L A = ⨁_c ι(D) γ_c`, with the
`b`-block on the left. The generator `γ_c` is `ψ_u e(u⁻¹ (i j))` for the shuffle `u`, a minimal
coset representative. The statement holds for every `ℓ`, for symmetric `Q`, over any commutative
ring `k`.

## Main definitions

* `CupCap.blockIdem`: the idempotent `1_c = e(i) ⊗ e(j)` of `D`.
* `CupCap.blockLeft`: the left ideal `D 1_c`.
* `CupCap.blockSum`: the map `⨁_c D 1_c → T̃^{λ⁺}`.
* `CupCap.blockLeftMul`: the left action of `D` on `⨁_c D 1_c`.
* `CupCap.endCorner`: the end corner `e_L T̃^{λ⁺}`.
* `CupCap.blockSumEquiv`: `⨁_c D 1_c ≃ e_L T̃^{λ⁺}`.

## Main results

* `CupCap.topBasis_repr_blockSum`: the coordinates of `∑_c ι(d_c) γ_c`.
* `CupCap.blockSum_injective`, `CupCap.mem_range_blockSum_iff`: (B3-L).
* `CupCap.blockSum_blockLeftMul`: `D`-linearity.
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

/-! ### The left ideals `D 1_c` -/

variable (Q Λ Λc) in
/-- The idempotent `1_c = e(i) ⊗ e(j)` of `D = T̃^λ ⊗ T̃^{(μ,μ*)}` of a base generator
`c = (e(i), j, u)`. -/
def blockIdem (c : BaseGen ν₀ ρ₁) : T ⊗[k] Tc :=
  StendhalAlgebra.e c.1.1.1.1.1 c.1.1.1.2.1 ⊗ₜ StendhalAlgebra.e c.1.1.2.1 c.1.2.1

variable (Q Λ Λc) in
/-- The cyclic projective left ideal `D 1_c = {d | d 1_c = d}` of `D`. -/
def blockLeft (c : BaseGen ν₀ ρ₁) : Submodule (T ⊗[k] Tc) (T ⊗[k] Tc) where
  carrier := {d | d * blockIdem Q Λ Λc c = d}
  add_mem' {d d'} hd hd' := by
    change (d + d') * _ = d + d'
    rw [add_mul, hd, hd']
  zero_mem' := zero_mul _
  smul_mem' a d hd := by
    change (a * d) * _ = a * d
    rw [mul_assoc, hd]

theorem mem_blockLeft {c : BaseGen ν₀ ρ₁} {d : T ⊗[k] Tc} :
    d ∈ blockLeft Q Λ Λc c ↔ d * blockIdem Q Λ Λc c = d := Iff.rfl

/-- **The coordinates of `d 1_c`** in the tensor product of the bases with dots on top: those
of `d` at the terms `x ⊗ y` with bottoms `(i, j)`, and `0` elsewhere. -/
theorem topBasis_repr_mul_blockIdem (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b) (c : BaseGen ν₀ ρ₁)
    (d : T ⊗[k] Tc) (x : {x // IsTopTerm ρ₁ x}) (y : {y // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ y}) :
    ((topBasis Q Λ hQ ρ₁ hρ₁).tensorProduct (topBasis Q Λc hQ ρ₂ hρ₂)).repr
        (d * blockIdem Q Λ Λc c) (x, y) =
      if x.1.1 = c.1.1.1.1.1 ∧ y.1.1 = c.1.1.2.1 then
        ((topBasis Q Λ hQ ρ₁ hρ₁).tensorProduct (topBasis Q Λc hQ ρ₂ hρ₂)).repr d (x, y)
      else 0 := by
  induction d using TensorProduct.inductionOn with
  | tmul a b =>
    rw [blockIdem, Algebra.TensorProduct.tmul_mul_tmul, Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.tensorProduct_repr_tmul_apply, topBasis_repr_mul_e, topBasis_repr_mul_e]
    by_cases hx : x.1.1 = c.1.1.1.1.1 <;> by_cases hy : y.1.1 = c.1.1.2.1 <;> simp [hx, hy]
  | add a b ha hb =>
    rw [add_mul, map_add, Finsupp.add_apply, ha, hb, map_add, Finsupp.add_apply]
    split_ifs
    · rfl
    · rw [add_zero]

/-! ### The map `⨁_c D 1_c → e_L T̃^{λ⁺}` -/

variable [DecidableEq (EndGen ν₀ ρ₁)]

variable (Q Λ Λc ρ₁ ρ₃) in
/-- **The map** `⨁_c D 1_c → T̃^{λ⁺}`, `(d_c)_c ↦ ∑_c ι(d_c) γ_c`. -/
def blockSum : (Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) →ₗ[k] Tp :=
  DFinsupp.lsum ℕ fun c =>
    (blockGenMul Q Λ Λc ρ₃ c).comp ((blockLeft Q Λ Λc c).subtype.restrictScalars k)

theorem blockSum_single (c : BaseGen ν₀ ρ₁) (a : blockLeft Q Λ Λc c) :
    blockSum Q Λ Λc ρ₁ ρ₃ (DFinsupp.single c a) =
      blockTensor Q Λ Λc ν ν₀ a * genElt Q Λ Λc ρ₁ ρ₃ c.1 := by
  rw [blockSum, DFinsupp.lsum_single]
  rfl

variable (Q Λ Λc) in
/-- Left multiplication by `d ∈ D` on `⨁_c D 1_c`, componentwise. -/
def blockLeftMul (d : T ⊗[k] Tc) :
    (Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) →ₗ[k] Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c :=
  DFinsupp.mapRange.linearMap fun c =>
    { toFun := fun b => ⟨d * b, by rw [mem_blockLeft, mul_assoc, mem_blockLeft.1 b.2]⟩
      map_add' := fun b b' => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r b => Subtype.ext (mul_smul_comm _ _ _) }

omit [DecidableEq (EndGen ν₀ ρ₁)] in
theorem blockLeftMul_apply (d : T ⊗[k] Tc) (a : Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c)
    (c : BaseGen ν₀ ρ₁) : (blockLeftMul Q Λ Λc d a c : T ⊗[k] Tc) = d * a c := by
  simp [blockLeftMul]

/-- **`D`-linearity**: `∑_c ι(d d_c) γ_c = ι(d) ∑_c ι(d_c) γ_c`. -/
theorem blockSum_blockLeftMul (d : T ⊗[k] Tc) (a : Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) :
    blockSum Q Λ Λc ρ₁ ρ₃ (blockLeftMul Q Λ Λc d a) =
      blockTensor Q Λ Λc ν ν₀ d * blockSum Q Λ Λc ρ₁ ρ₃ a := by
  have h : (blockSum Q Λ Λc ρ₁ ρ₃).comp (blockLeftMul Q Λ Λc d) =
      (LinearMap.mulLeft k (blockTensor Q Λ Λc ν ν₀ d)).comp (blockSum Q Λ Λc ρ₁ ρ₃) := by
    refine DFinsupp.lhom_ext' fun c => LinearMap.ext fun b => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, DFinsupp.lsingle_apply, blockLeftMul,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.mulLeft_apply]
    rw [blockSum_single, blockSum_single, blockTensor_mul, mul_assoc]
  exact LinearMap.congr_fun h a

/-- The image of `⨁_c D 1_c` lies in the end corner. -/
theorem endStendhal_one_mul_blockSum (a : Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) :
    endStendhal Q Λ Λc ν ν₀ 1 * blockSum Q Λ Λc ρ₁ ρ₃ a = blockSum Q Λ Λc ρ₁ ρ₃ a := by
  induction a using DFinsupp.induction with
  | h0 => rw [map_zero, mul_zero]
  | ha c b f _ _ ih =>
    rw [map_add, mul_add, ih, blockSum_single, ← mul_assoc, endStendhal_one_mul_blockTensor]

/-- **The coordinates of `∑_c ι(d_c) γ_c`**: at the basis term of a pair `p = ((x, j, u), y)` it
is the coordinate of `d_c` at `x ⊗ y`, `c` the base generator of `p`. -/
theorem topBasis_repr_blockSum (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (a : Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) (p : EndPair ρ₁ ρ₂) :
    (topBasis Q (plusLabels Λ Λc ℓ le_rfl) hQ (endWord ρ₁ ρ₂ ρ₃) (endWord_spec hρ₁ hρ₂ hρ₃)).repr
        (blockSum Q Λ Λc ρ₁ ρ₃ a) (endPairIdx ρ₁ ρ₂ ρ₃ (endWord_spec hρ₁ hρ₂ hρ₃) p) =
      ((topBasis Q Λ hQ ρ₁ hρ₁).tensorProduct (topBasis Q Λc hQ ρ₂ hρ₂)).repr
        (a (baseOf hρ₁ p.1.1) : T ⊗[k] Tc) (p.1.1.1.1, p.1.2) := by
  induction a using DFinsupp.induction with
  | h0 => simp
  | ha c b f _ _ ih =>
    rw [map_add, map_add, Finsupp.add_apply, ih, blockSum_single, ← blockGenMul_apply,
      topBasis_repr_blockGenMul hQ hρ₁ hρ₂ hρ₃, DFinsupp.add_apply, Submodule.coe_add, map_add,
      Finsupp.add_apply]
    congr 1
    by_cases hc : baseOf hρ₁ p.1.1 = c
    · subst hc
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), DFinsupp.single_eq_same]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), DFinsupp.single_eq_of_ne hc]
      simp

/-- **(B3-L), uniqueness**: the map `⨁_c D 1_c → e_L T̃^{λ⁺}` is injective. -/
theorem blockSum_injective (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    Function.Injective (blockSum Q Λ Λc ρ₁ ρ₃) := by
  set BD := (topBasis Q Λ hQ ρ₁ hρ₁).tensorProduct (topBasis Q Λc hQ ρ₂ hρ₂)
  intro a a' ha
  refine DFinsupp.ext fun c => Subtype.ext (BD.ext_elem fun xy => ?_)
  obtain ⟨x, y⟩ := xy
  by_cases h : x.1.1 = c.1.1.1.1.1 ∧ y.1.1 = c.1.1.2.1
  · have hp := topBasis_repr_blockSum hQ hρ₁ hρ₂ hρ₃ a ⟨(liftGen c x h.1, y), h.2⟩
    have hp' := topBasis_repr_blockSum hQ hρ₁ hρ₂ hρ₃ a' ⟨(liftGen c x h.1, y), h.2⟩
    rw [ha] at hp
    have hb : baseOf hρ₁ (liftGen c x h.1) = c := baseOf_liftGen hρ₁ c x h.1
    rw [hb] at hp hp'
    exact hp.symm.trans hp'
  · rw [← (mem_blockLeft.1 (a c).2), ← (mem_blockLeft.1 (a' c).2),
      topBasis_repr_mul_blockIdem hQ hρ₁ hρ₂, topBasis_repr_mul_blockIdem hQ hρ₁ hρ₂,
      ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- A basis term of the end corner is `ι(x ⊗ y) γ_c` for its pair `((x, j, u), y)`. -/
theorem topTerm_endPairIdx_mem_range
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (p : EndPair ρ₁ ρ₂) :
    topTerm Q (plusLabels Λ Λc ℓ le_rfl) (fun w => (endWord_spec hρ₁ hρ₂ hρ₃ w).2)
        (endPairIdx ρ₁ ρ₂ ρ₃ (endWord_spec hρ₁ hρ₂ hρ₃) p) ∈
      LinearMap.range (blockSum Q Λ Λc ρ₁ ρ₃) := by
  set c := baseOf hρ₁ p.1.1
  have hx : p.1.1.1.1.1.1 = c.1.1.1.1.1 := rfl
  have hy : p.1.2.1.1 = c.1.1.2.1 := p.2
  have hmem : topTerm Q Λ (fun w => (hρ₁ w).2) p.1.1.1.1 ⊗ₜ
      topTerm Q Λc (fun b => (hρ₂ b).2) p.1.2 ∈ blockLeft Q Λ Λc c := by
    rw [mem_blockLeft, blockIdem, Algebra.TensorProduct.tmul_mul_tmul, topTerm_mul_e,
      topTerm_mul_e, ite_eq_left_of_eq_true _ _ (eq_true hx),
      ite_eq_left_of_eq_true _ _ (eq_true hy)]
  refine ⟨DFinsupp.single c ⟨_, hmem⟩, ?_⟩
  rw [blockSum_single, blockTensor_topTerm_mul_genElt hρ₁ hρ₂ hρ₃ c _ _ hx hy,
    (liftPair_eq_iff hρ₁ c _ _ hx hy p).2 ⟨rfl, rfl⟩]

/-- **(B3-L), existence**: an element `z` of `T̃^{λ⁺}` is `∑_c ι(d_c) γ_c` for some
`(d_c) ∈ ⨁_c D 1_c` if and only if it lies in the end corner, `e_L z = z`. -/
theorem mem_range_blockSum_iff (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (z : Tp) :
    z ∈ LinearMap.range (blockSum Q Λ Λc ρ₁ ρ₃) ↔ endStendhal Q Λ Λc ν ν₀ 1 * z = z := by
  constructor
  · rintro ⟨a, rfl⟩
    exact endStendhal_one_mul_blockSum a
  · intro hz
    set Bp := topBasis Q (plusLabels Λ Λc ℓ le_rfl) hQ (endWord ρ₁ ρ₂ ρ₃)
      (endWord_spec hρ₁ hρ₂ hρ₃)
    have hexp : z = ∑ b ∈ (Bp.repr z).support,
        Bp.repr z b • (endStendhal Q Λ Λc ν ν₀ 1 * Bp b) := by
      conv_lhs => rw [← hz, ← Bp.linearCombination_repr z]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => mul_smul_comm _ _ _
    rw [hexp]
    refine Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
    classical
    rw [topBasis_apply, endStendhal_one_mul_topTerm]
    split_ifs with hb
    · obtain ⟨p, rfl⟩ := exists_endPairIdx ρ₁ ρ₂ ρ₃ hρ₁ hρ₂ hρ₃ b hb
      exact topTerm_endPairIdx_mem_range hρ₁ hρ₂ hρ₃ p
    · exact Submodule.zero_mem _

variable (Q Λ Λc ν ν₀) in
/-- The end corner `e_L T̃^{λ⁺} = {z | e_L z = z}`, as a `k`-submodule. -/
def endCorner : Submodule k Tp where
  carrier := {z | endStendhal Q Λ Λc ν ν₀ 1 * z = z}
  add_mem' {z z'} hz hz' := by
    change _ * (z + z') = z + z'
    rw [mul_add, hz, hz']
  zero_mem' := mul_zero _
  smul_mem' r z hz := by
    change _ * (r • z) = r • z
    rw [mul_smul_comm, hz]

variable (Q Λ Λc ρ₁ ρ₃) in
/-- **(B3-L)** (arXiv:1309.3796v3, proof of Lemma 7.19, for symmetric `Q`, over any commutative
ring): the end corner `e_L T̃^{λ⁺}` is `⨁_c D 1_c` over the base generators `c = (e(i), j, u)`,
`(d_c)_c ↦ ∑_c ι(d_c) γ_c`, with `D = T̃^λ ⊗ T̃^{(μ,μ*)}` acting through `ι`
(`CupCap.blockSum_blockLeftMul`). -/
def blockSumEquiv (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    (Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) ≃ₗ[k] endCorner Q Λ Λc ν ν₀ :=
  LinearEquiv.ofBijective
    ((blockSum Q Λ Λc ρ₁ ρ₃).codRestrict (endCorner Q Λ Λc ν ν₀)
      fun a => endStendhal_one_mul_blockSum a)
    ⟨fun a a' h => blockSum_injective hQ hρ₁ hρ₂ hρ₃ (congrArg Subtype.val h), fun z => by
      obtain ⟨a, ha⟩ := (mem_range_blockSum_iff hQ hρ₁ hρ₂ hρ₃ z.1).2 z.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem blockSumEquiv_apply (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (a : Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) :
    (blockSumEquiv Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ a : Tp) = blockSum Q Λ Λc ρ₁ ρ₃ a := rfl

end Categorification.Stendhal.CupCap
