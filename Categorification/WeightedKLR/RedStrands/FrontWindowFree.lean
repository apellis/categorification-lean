/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FrontWindowCorner

/-!
# (B3-R): the front corner as a sum of cyclic projective left `D_R`-modules

Webster, arXiv:1309.3796v3, proof of Lemma 7.19, input (B3) with the black block at the right
end, step 4 of the paper argument. Let `D_R = T̃^{(μ,μ*)}(ν₀) ⊗_k T̃^λ`, acting on `T̃^{λ⁺}` through
the juxtaposition `ι` (`CupCap.blockTensorR`), and let `e_R = ι(1)` be the front idempotent. For a
base generator `c = (i, j, u)` (`CupCap.FrontGen`) let `1_c = e(j) ⊗ e(i)` (`CupCap.blockIdemF`)
and `D_R 1_c` the cyclic projective left ideal (`CupCap.blockLeftF`). For symmetric `Q`, over any
commutative ring,

  `⨁_c D_R 1_c → e_R T̃^{λ⁺}`, `(d_c)_c ↦ ∑_c ι(d_c) γ_c`

is bijective (`CupCap.blockSumF_injective`, `CupCap.mem_range_blockSumF_iff`,
`CupCap.blockSumFEquiv`) and `D_R`-linear (`CupCap.blockSumF_blockLeftMulF`): the coordinates of
`∑_c ι(d_c) γ_c` in the basis of `T̃^{λ⁺}` with dots on top are the coordinates of the `d_c` in the
tensor product basis (`CupCap.topBasis_repr_blockSumF`), and every basis term of the front corner
is some `ι(y ⊗ x) γ_c`.

For `ℓ = 0`, `T̃^λ = R(b)` with `b = ν`, `A′ = T̃^{(μ,μ*)}(ν₀)` and `T̃^{λ⁺}(ν + ν₀) = A`,
so this is (B3-R): `e_R A = ⨁_{(i, c)} D_R ψ_c e(i)` with `D_R = A′ ⊗ R(b)`, the `b`-block on
the right. The statements hold for every `ℓ`.

## Main definitions

* `CupCap.blockIdemF`, `CupCap.blockLeftF`: the idempotents `1_c` and the left ideals `D_R 1_c`.
* `CupCap.blockSumF`: the map `⨁_c D_R 1_c → T̃^{λ⁺}`.
* `CupCap.blockLeftMulF`: the left action of `D_R` on `⨁_c D_R 1_c`.
* `CupCap.frontCorner`: the front corner `e_R T̃^{λ⁺}`.
* `CupCap.blockSumFEquiv`: `⨁_c D_R 1_c ≃ e_R T̃^{λ⁺}`.

## Main results

* `CupCap.topBasis_repr_blockSumF`: the coordinates of `∑_c ι(d_c) γ_c`.
* `CupCap.blockSumF_injective`, `CupCap.mem_range_blockSumF_iff`: (B3-R).
* `CupCap.blockSumF_blockLeftMulF`: `D_R`-linearity.
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
local notation "z₀" => Nat.zero_le ℓ
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc 0 (Nat.zero_le ℓ)) (ν + ν₀)

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

/-! ### The left ideals `D_R 1_c` -/

variable (Q Λ Λc) in
/-- The idempotent `1_c = e(j) ⊗ e(i)` of `D_R = T̃^{(μ,μ*)} ⊗ T̃^λ` of a base generator
`c = (i, j, u)`. -/
def blockIdemF (c : FrontGen ℓ ν ν₀) : Tc ⊗[k] T :=
  StendhalAlgebra.e c.1.2.1 c.2.2.1 ⊗ₜ StendhalAlgebra.e c.1.1 c.2.1

variable (Q Λ Λc) in
/-- The cyclic projective left ideal `D_R 1_c = {d | d 1_c = d}` of `D_R`. -/
def blockLeftF (c : FrontGen ℓ ν ν₀) : Submodule (Tc ⊗[k] T) (Tc ⊗[k] T) where
  carrier := {d | d * blockIdemF Q Λ Λc c = d}
  add_mem' {d d'} hd hd' := by
    change (d + d') * _ = d + d'
    rw [add_mul, hd, hd']
  zero_mem' := zero_mul _
  smul_mem' a d hd := by
    change (a * d) * _ = a * d
    rw [mul_assoc, hd]

theorem mem_blockLeftF {c : FrontGen ℓ ν ν₀} {d : Tc ⊗[k] T} :
    d ∈ blockLeftF Q Λ Λc c ↔ d * blockIdemF Q Λ Λc c = d := Iff.rfl

/-- **The coordinates of `d 1_c`** in the tensor product of the bases with dots on top: those
of `d` at the terms `y ⊗ x` with bottoms `(j, i)`, and `0` elsewhere. -/
theorem topBasis_repr_mul_blockIdemF (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b) (c : FrontGen ℓ ν ν₀)
    (d : Tc ⊗[k] T) (y : {y // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ y})
    (x : {x // IsTopTerm (ℓ := ℓ) (ν := ν) ρ₁ x}) :
    ((topBasis Q Λc hQ ρ₂ hρ₂).tensorProduct (topBasis Q Λ hQ ρ₁ hρ₁)).repr
        (d * blockIdemF Q Λ Λc c) (y, x) =
      if y.1.1 = c.1.2.1 ∧ x.1.1 = c.1.1 then
        ((topBasis Q Λc hQ ρ₂ hρ₂).tensorProduct (topBasis Q Λ hQ ρ₁ hρ₁)).repr d (y, x)
      else 0 := by
  induction d using TensorProduct.inductionOn with
  | tmul a b =>
    rw [blockIdemF, Algebra.TensorProduct.tmul_mul_tmul,
      Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
      topBasis_repr_mul_e, topBasis_repr_mul_e]
    by_cases hy : y.1.1 = c.1.2.1 <;> by_cases hx : x.1.1 = c.1.1 <;> simp [hx, hy]
  | add a b ha hb =>
    rw [add_mul, map_add, Finsupp.add_apply, ha, hb, map_add, Finsupp.add_apply]
    split_ifs
    · rfl
    · rw [add_zero]

/-! ### The map `⨁_c D_R 1_c → e_R T̃^{λ⁺}` -/

variable [DecidableEq (FrontGen ℓ ν ν₀)]

variable (Q Λ Λc ρ₃) in
/-- **The map** `⨁_c D_R 1_c → T̃^{λ⁺}`, `(d_c)_c ↦ ∑_c ι(d_c) γ_c`. -/
def blockSumF : (Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c) →ₗ[k] Tp :=
  DFinsupp.lsum ℕ fun c =>
    (blockGenMulF Q Λ Λc ρ₃ c).comp ((blockLeftF Q Λ Λc c).subtype.restrictScalars k)

theorem blockSumF_single (c : FrontGen ℓ ν ν₀) (a : blockLeftF Q Λ Λc c) :
    blockSumF Q Λ Λc ρ₃ (DFinsupp.single c a) =
      blockTensorR Q Λ Λc ν ν₀ a * genEltF Q Λ Λc ρ₃ c := by
  rw [blockSumF, DFinsupp.lsum_single]
  rfl

variable (Q Λ Λc) in
/-- Left multiplication by `d ∈ D_R` on `⨁_c D_R 1_c`, componentwise. -/
def blockLeftMulF (d : Tc ⊗[k] T) :
    (Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c) →ₗ[k]
      Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c :=
  DFinsupp.mapRange.linearMap fun c =>
    { toFun := fun b => ⟨d * b, by rw [mem_blockLeftF, mul_assoc, mem_blockLeftF.1 b.2]⟩
      map_add' := fun b b' => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r b => Subtype.ext (mul_smul_comm _ _ _) }

omit [DecidableEq (FrontGen ℓ ν ν₀)] in
theorem blockLeftMulF_apply (d : Tc ⊗[k] T) (a : Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c)
    (c : FrontGen ℓ ν ν₀) : (blockLeftMulF Q Λ Λc d a c : Tc ⊗[k] T) = d * a c := by
  simp [blockLeftMulF]

/-- **`D_R`-linearity**: `∑_c ι(d d_c) γ_c = ι(d) ∑_c ι(d_c) γ_c`. -/
theorem blockSumF_blockLeftMulF (d : Tc ⊗[k] T)
    (a : Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c) :
    blockSumF Q Λ Λc ρ₃ (blockLeftMulF Q Λ Λc d a) =
      blockTensorR Q Λ Λc ν ν₀ d * blockSumF Q Λ Λc ρ₃ a := by
  have h : (blockSumF Q Λ Λc ρ₃).comp (blockLeftMulF Q Λ Λc d) =
      (LinearMap.mulLeft k (blockTensorR Q Λ Λc ν ν₀ d)).comp (blockSumF Q Λ Λc ρ₃) := by
    refine DFinsupp.lhom_ext' fun c => LinearMap.ext fun b => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, DFinsupp.lsingle_apply, blockLeftMulF,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.mulLeft_apply]
    rw [blockSumF_single, blockSumF_single, blockTensorR_mul, mul_assoc]
  exact LinearMap.congr_fun h a

/-- The image of `⨁_c D_R 1_c` lies in the front corner. -/
theorem frontStendhal_one_mul_blockSumF (a : Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c) :
    frontStendhal Q Λ Λc ν ν₀ 1 * blockSumF Q Λ Λc ρ₃ a = blockSumF Q Λ Λc ρ₃ a := by
  induction a using DFinsupp.induction with
  | h0 => rw [map_zero, mul_zero]
  | ha c b f _ _ ih =>
    rw [map_add, mul_add, ih, blockSumF_single, ← mul_assoc, frontStendhal_one_mul_blockTensorR]

/-- **The coordinates of `∑_c ι(d_c) γ_c`**: at the basis term of a triple `p = (c, y, x)` it is
the coordinate of `d_c` at `y ⊗ x`. -/
theorem topBasis_repr_blockSumF (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (a : Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c) (p : FrontTriple ρ₁ ρ₂) :
    (topBasis Q (plusLabels Λ Λc 0 z₀) hQ (frontWord ρ₁ ρ₂ ρ₃)
        (frontWord_spec hρ₁ hρ₂ hρ₃)).repr
        (blockSumF Q Λ Λc ρ₃ a) (frontIdx ρ₁ ρ₂ ρ₃ (frontWord_spec hρ₁ hρ₂ hρ₃) p) =
      ((topBasis Q Λc hQ ρ₂ hρ₂).tensorProduct (topBasis Q Λ hQ ρ₁ hρ₁)).repr
        (a p.1.1 : Tc ⊗[k] T) (p.1.2.1, p.1.2.2) := by
  induction a using DFinsupp.induction with
  | h0 => simp
  | ha c b f _ _ ih =>
    rw [map_add, map_add, Finsupp.add_apply, ih, blockSumF_single, ← blockGenMulF_apply,
      topBasis_repr_blockGenMulF hQ hρ₁ hρ₂ hρ₃, DFinsupp.add_apply, Submodule.coe_add, map_add,
      Finsupp.add_apply]
    congr 1
    by_cases hc : p.1.1 = c
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      subst hc
      rw [DFinsupp.single_eq_same]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), DFinsupp.single_eq_of_ne hc]
      simp

/-- **(B3-R), uniqueness**: the map `⨁_c D_R 1_c → e_R T̃^{λ⁺}` is injective. -/
theorem blockSumF_injective (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    Function.Injective (blockSumF Q Λ Λc ρ₃) := by
  set BD := (topBasis Q Λc hQ ρ₂ hρ₂).tensorProduct (topBasis Q Λ hQ ρ₁ hρ₁)
  intro a a' ha
  refine DFinsupp.ext fun c => Subtype.ext (BD.ext_elem fun yx => ?_)
  obtain ⟨y, x⟩ := yx
  by_cases h : y.1.1 = c.1.2.1 ∧ x.1.1 = c.1.1
  · have hp := topBasis_repr_blockSumF hQ hρ₁ hρ₂ hρ₃ a ⟨(c, y, x), h.1, h.2⟩
    have hp' := topBasis_repr_blockSumF hQ hρ₁ hρ₂ hρ₃ a' ⟨(c, y, x), h.1, h.2⟩
    rw [ha] at hp
    exact hp.symm.trans hp'
  · rw [← (mem_blockLeftF.1 (a c).2), ← (mem_blockLeftF.1 (a' c).2),
      topBasis_repr_mul_blockIdemF hQ hρ₁ hρ₂, topBasis_repr_mul_blockIdemF hQ hρ₁ hρ₂,
      ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- A basis term of the front corner is `ι(y ⊗ x) γ_c` for its triple `(c, y, x)`. -/
theorem topTerm_frontIdx_mem_range
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (p : FrontTriple ρ₁ ρ₂) :
    topTerm Q (plusLabels Λ Λc 0 z₀) (fun w => (frontWord_spec hρ₁ hρ₂ hρ₃ w).2)
        (frontIdx ρ₁ ρ₂ ρ₃ (frontWord_spec hρ₁ hρ₂ hρ₃) p) ∈
      LinearMap.range (blockSumF Q Λ Λc ρ₃) := by
  have hmem : topTerm Q Λc (fun b => (hρ₂ b).2) p.1.2.1 ⊗ₜ
      topTerm Q Λ (fun a => (hρ₁ a).2) p.1.2.2 ∈ blockLeftF Q Λ Λc p.1.1 := by
    rw [mem_blockLeftF, blockIdemF, Algebra.TensorProduct.tmul_mul_tmul, topTerm_mul_e,
      topTerm_mul_e, ite_eq_left_of_eq_true _ _ (eq_true p.2.1),
      ite_eq_left_of_eq_true _ _ (eq_true p.2.2)]
  refine ⟨DFinsupp.single p.1.1 ⟨_, hmem⟩, ?_⟩
  rw [blockSumF_single]
  exact blockTensorR_topTerm_mul_genEltF hρ₁ hρ₂ hρ₃ p

/-- **(B3-R), existence**: an element `z` of `T̃^{λ⁺}` is `∑_c ι(d_c) γ_c` for some
`(d_c) ∈ ⨁_c D_R 1_c` if and only if it lies in the front corner, `e_R z = z`. -/
theorem mem_range_blockSumF_iff (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (z : Tp) :
    z ∈ LinearMap.range (blockSumF Q Λ Λc ρ₃) ↔ frontStendhal Q Λ Λc ν ν₀ 1 * z = z := by
  constructor
  · rintro ⟨a, rfl⟩
    exact frontStendhal_one_mul_blockSumF a
  · intro hz
    set Bp := topBasis Q (plusLabels Λ Λc 0 z₀) hQ (frontWord ρ₁ ρ₂ ρ₃)
      (frontWord_spec hρ₁ hρ₂ hρ₃)
    have hexp : z = ∑ b ∈ (Bp.repr z).support,
        Bp.repr z b • (frontStendhal Q Λ Λc ν ν₀ 1 * Bp b) := by
      conv_lhs => rw [← hz, ← Bp.linearCombination_repr z]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => mul_smul_comm _ _ _
    rw [hexp]
    refine Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
    classical
    rw [topBasis_apply, frontStendhal_one_mul_topTerm]
    split_ifs with hb
    · obtain ⟨p, rfl⟩ := exists_frontIdx ρ₁ ρ₂ ρ₃ hρ₁ hρ₂ hρ₃ b hb
      exact topTerm_frontIdx_mem_range hρ₁ hρ₂ hρ₃ p
    · exact Submodule.zero_mem _

variable (Q Λ Λc ν ν₀) in
/-- The front corner `e_R T̃^{λ⁺} = {z | e_R z = z}`, as a `k`-submodule. -/
def frontCorner : Submodule k Tp where
  carrier := {z | frontStendhal Q Λ Λc ν ν₀ 1 * z = z}
  add_mem' {z z'} hz hz' := by
    change _ * (z + z') = z + z'
    rw [mul_add, hz, hz']
  zero_mem' := mul_zero _
  smul_mem' r z hz := by
    change _ * (r • z) = r • z
    rw [mul_smul_comm, hz]

variable (Q Λ Λc ρ₁ ρ₃) in
/-- **(B3-R)** (arXiv:1309.3796v3, proof of Lemma 7.19, for symmetric `Q`, over any commutative
ring): the front corner `e_R T̃^{λ⁺}` is `⨁_c D_R 1_c` over the base generators `c = (i, j, u)`,
`(d_c)_c ↦ ∑_c ι(d_c) γ_c`, with `D_R = T̃^{(μ,μ*)} ⊗ T̃^λ` acting through `ι`
(`CupCap.blockSumF_blockLeftMulF`). -/
def blockSumFEquiv (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    (Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c) ≃ₗ[k] frontCorner Q Λ Λc ν ν₀ :=
  LinearEquiv.ofBijective
    ((blockSumF Q Λ Λc ρ₃).codRestrict (frontCorner Q Λ Λc ν ν₀)
      fun a => frontStendhal_one_mul_blockSumF a)
    ⟨fun a a' h => blockSumF_injective (ρ₁ := ρ₁) (ρ₂ := ρ₂) hQ hρ₁ hρ₂ hρ₃
      (congrArg Subtype.val h), fun z => by
      obtain ⟨a, ha⟩ := (mem_range_blockSumF_iff (ρ₁ := ρ₁) hQ hρ₁ hρ₂ hρ₃ z.1).2 z.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem blockSumFEquiv_apply (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (a : Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c) :
    (blockSumFEquiv Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ a : Tp) = blockSumF Q Λ Λc ρ₃ a := rfl

end Categorification.Stendhal.CupCap
