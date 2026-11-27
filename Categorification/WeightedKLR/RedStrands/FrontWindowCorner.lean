/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FrontWindowIndex
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockRight
import Categorification.WeightedKLR.Rigidity.CupCapEndFree

/-!
# The generators of the front corner and the coordinates of `ι(d) γ_c`

Webster, arXiv:1309.3796v3, proof of Lemma 7.19, the block decomposition (B3) with the black
block at the right end, step 3 of the paper argument. For a base generator `c = (i, j, u)`
(`CupCap.FrontGen`) let `γ_c = e(j i) ψ_{ρ₃(u)} e(u⁻¹ (j i))` (`CupCap.genEltF`). For basis
terms `y` of `T̃^{(μ,μ*)}` with bottom `j` and `x` of `T̃^λ` with bottom `i`,

  `ι(y ⊗ x) · γ_c`

is the basis term of `T̃^{λ⁺}` indexed by the triple `(c, y, x)`
(`CupCap.blockTensorR_topTerm_mul_genEltF`), with no correction terms; the products with the
other basis terms of `T̃^{(μ,μ*)} ⊗ T̃^λ` vanish. Hence the coordinates of `ι(d) γ_c` in the basis
of `T̃^{λ⁺}` with dots on top are the coordinates of `d` in the tensor product basis
(`CupCap.topBasis_repr_blockGenMulF`). The front idempotent `e_R` keeps exactly the basis terms
whose top lies in `frontSet` (`CupCap.frontStendhal_one_mul_topTerm`).

## Main definitions

* `CupCap.genEltF`: the generators.
* `CupCap.blockGenMulF`: the `k`-linear map `d ↦ ι(d) γ_c`.

## Main results

* `CupCap.blockTensorR_topTerm_mul_genEltF`, `CupCap.topBasis_repr_blockGenMulF`,
  `CupCap.frontStendhal_one_mul_topTerm`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders
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
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc 0 (Nat.zero_le ℓ))) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "β" => botMap k Q Λ Λc 0 (Nat.zero_le ℓ) ν ν₀

/-! ### Images of elements -/

theorem frontStendhal_of_val (z : Tc) (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀))
    (hx : z.val = StendhalAlgebraAllOrders.ofKLR k Q Λc ν₀ x) :
    frontStendhal Q Λ Λc ν ν₀ z = β (frontMapKLR Q Λ Λc ν ν₀ x) := by
  rw [frontStendhal, stendhalLift_apply, hx, allOrdersLift_ofKLR]
  rfl

theorem suffixStendhal_of_val (z : T) (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
    (ha : z.val = StendhalAlgebraAllOrders.ofKLR k Q Λ ν a) :
    suffixStendhal Q Λ Λc ν ν₀ z = β (suffixMapKLR Q Λ Λc ν ν₀ a) := by
  rw [suffixStendhal, stendhalLift_apply, ha, allOrdersLift_ofKLR]
  rfl

/-- The order projection on a basis term with dots on top is the basis term. -/
theorem botMap_topElt_front
    {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}
    (hρ : ∀ w, wordProd M (ρ w) = w) (b : {b // IsTopTerm ρ b}) :
    β (topElt (Q := Q) (Λ := plusLabels Λ Λc 0 z₀) ρ b.1) =
      topTerm Q (plusLabels Λ Λc 0 z₀) hρ b := by
  apply Subtype.ext
  change ofKLR k Q _ (ν + ν₀) _ * redOrderedIdem k Q _ (ν + ν₀) = _
  rw [topTerm_val]
  have h := ro_mul_ofKLR_topElt_mul_ro (Q := Q) (Λ := plusLabels Λ Λc 0 z₀) hρ b.1
  rw [ite_eq_left_of_eq_true _ _ (eq_true b.2)] at h
  have hE := isIdempotentElem_redOrderedIdem (k := k) (Q := Q) (Λ := plusLabels Λ Λc 0 z₀)
    (ν := ν + ν₀)
  conv_lhs => rw [← h]
  rw [mul_assoc, hE.eq, h]

/-! ### The generators -/

variable (ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ)
  (ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ)

variable (Q Λ Λc) in
/-- The KLR diagram `e(j i) ψ_{ρ₃(u)} e(u⁻¹ (j i))` of a base generator `c = (i, j, u)`. -/
def genKLRF (c : FrontGen ℓ ν ν₀) : Rp :=
  KLRAlgebra.e (frontSeq c.1.1 c.1.2.1) * ψw (ρ₃ c.1.2.2.1) * KLRAlgebra.e c.bot

variable (Q Λ Λc) in
/-- **The generator** `γ_c` of the front corner of `T̃^{λ⁺}`. -/
def genEltF (c : FrontGen ℓ ν ν₀) : Tp := β (genKLRF Q Λ Λc ρ₃ c)

variable {ρ₁ ρ₂ ρ₃}

/-- `γ_c` lies in the corner `e(j) T̃^{λ⁺}`, for `e(j)` on the first `N` strands. -/
theorem frontStendhal_e_mul_genEltF (c : FrontGen ℓ ν ν₀) :
    frontStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.e c.1.2.1 c.2.2.1) * genEltF Q Λ Λc ρ₃ c =
      genEltF Q Λ Λc ρ₃ c := by
  rw [frontStendhal_of_val _ _ rfl, genEltF, ← map_mul]
  congr 1
  rw [genKLRF, ← frontMapKLR_e_mul_suffixMapKLR_e]
  simp only [← mul_assoc]
  rw [← frontMapKLR_mul, e_mul_self]

/-- `γ_c` lies in the corner `e(i) T̃^{λ⁺}`, for `e(i)` on the last `m` strands. -/
theorem suffixStendhal_e_mul_genEltF (c : FrontGen ℓ ν ν₀) :
    suffixStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.e c.1.1 c.2.1) * genEltF Q Λ Λc ρ₃ c =
      genEltF Q Λ Λc ρ₃ c := by
  rw [suffixStendhal_of_val _ _ rfl, genEltF, ← map_mul]
  congr 1
  rw [genKLRF, ← frontMapKLR_e_mul_suffixMapKLR_e]
  simp only [← mul_assoc]
  rw [(commute_suffixMapKLR_frontMapKLR Q Λ Λc ν ν₀ _ _).eq, mul_assoc (frontMapKLR _ _ _ _ _ _),
    ← suffixMapKLR_mul, e_mul_self]

/-- **The juxtaposition of basis terms times a base generator is a basis term**: for a triple
`(c, y, x)`, `ι(y ⊗ x) γ_c` is the basis term of `T̃^{λ⁺}` indexed by it. -/
theorem blockTensorR_topTerm_mul_genEltF (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (p : FrontTriple ρ₁ ρ₂) :
    blockTensorR Q Λ Λc ν ν₀ (topTerm Q Λc (fun b => (hρ₂ b).2) p.1.2.1 ⊗ₜ
        topTerm Q Λ (fun a => (hρ₁ a).2) p.1.2.2) * genEltF Q Λ Λc ρ₃ p.1.1 =
      topTerm Q (plusLabels Λ Λc 0 z₀) (fun w => (frontWord_spec hρ₁ hρ₂ hρ₃ w).2)
        (frontIdx ρ₁ ρ₂ ρ₃ (frontWord_spec hρ₁ hρ₂ hρ₃) p) := by
  obtain ⟨⟨c, y, x⟩, hy, hx⟩ := p
  obtain ⟨⟨i, j, u⟩, hi, hj, hbot⟩ := c
  obtain ⟨⟨j', b, d⟩, hy'⟩ := y
  obtain ⟨⟨i', a, d'⟩, hx'⟩ := x
  simp only at hy hx
  subst j' i'
  rw [blockTensorR_tmul, frontStendhal_of_val _ _ (topTerm_val _ _),
    suffixStendhal_of_val _ _ (topTerm_val _ _), genEltF, ← map_mul, ← map_mul,
    ← botMap_topElt_front (fun w => (frontWord_spec hρ₁ hρ₂ hρ₃ w).2)]
  congr 1
  simp only [topElt, genKLRF]
  rw [frontMapKLR_mul_suffixMapKLR _ _ (hρ₂ b).1.1 (hρ₁ a).1.1]
  have key : (KLRAlgebra.e (frontSeq i j) * (KLRAlgebra.e (frontSeq i j) * ψw (ρ₃ u.1) *
      KLRAlgebra.e (u.1⁻¹ • frontSeq i j)) : Rp) =
      ψw (ρ₃ u.1) * KLRAlgebra.e (u.1⁻¹ • frontSeq i j) := by
    rw [← mul_assoc, ← mul_assoc, e_mul_self, e_mul_ψw, (hρ₃ u.1).2, mul_assoc, e_mul_self]
  change _ * (KLRAlgebra.e (frontSeq i j) * ψw (ρ₃ u.1) * KLRAlgebra.e (u.1⁻¹ • frontSeq i j)) =
    pol (monomial (frontExp ν ν₀ (d, d')) 1) *
      ψw (frontWord ρ₁ ρ₂ ρ₃ (blockPerm _ b a * u.1)) * KLRAlgebra.e (u.1⁻¹ • frontSeq i j)
  rw [mul_assoc _ (KLRAlgebra.e _), key, frontWord_blockPerm_mul, monomial_frontExp]
  simp only [ψw_append, mul_assoc]

/-- A basis term `y` whose bottom is not the loading `j` of `c` gives `ι(y ⊗ x) γ_c = 0`. -/
theorem blockTensorR_topTerm_mul_genEltF_of_ne_left
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b) (c : FrontGen ℓ ν ν₀)
    (y : {y // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ y}) (x : T) (hy : y.1.1 ≠ c.1.2.1) :
    blockTensorR Q Λ Λc ν ν₀ (topTerm Q Λc (fun b => (hρ₂ b).2) y ⊗ₜ x) *
      genEltF Q Λ Λc ρ₃ c = 0 := by
  have h0 : frontStendhal Q Λ Λc ν ν₀ (topTerm Q Λc (fun b => (hρ₂ b).2) y) *
      frontStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.e c.1.2.1 c.2.2.1) = 0 := by
    rw [← map_mul, topTerm_mul_e, ite_eq_right_of_eq_false _ _ (eq_false hy), map_zero]
  rw [blockTensorR_tmul, (commute_suffixStendhal_frontStendhal Q Λ Λc _ _).eq.symm, mul_assoc,
    ← frontStendhal_e_mul_genEltF c, ← mul_assoc (frontStendhal Q Λ Λc ν ν₀ _), h0, zero_mul,
    mul_zero]

/-- A basis term `x` whose bottom is not the loading `i` of `c` gives `ι(y ⊗ x) γ_c = 0`. -/
theorem blockTensorR_topTerm_mul_genEltF_of_ne_right
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a) (c : FrontGen ℓ ν ν₀) (y : Tc)
    (x : {x // IsTopTerm (ℓ := ℓ) (ν := ν) ρ₁ x}) (hx : x.1.1 ≠ c.1.1) :
    blockTensorR Q Λ Λc ν ν₀ (y ⊗ₜ topTerm Q Λ (fun a => (hρ₁ a).2) x) *
      genEltF Q Λ Λc ρ₃ c = 0 := by
  have h0 : suffixStendhal Q Λ Λc ν ν₀ (topTerm Q Λ (fun a => (hρ₁ a).2) x) *
      suffixStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.e c.1.1 c.2.1) = 0 := by
    rw [← map_mul, topTerm_mul_e, ite_eq_right_of_eq_false _ _ (eq_false hx), map_zero]
  rw [blockTensorR_tmul, mul_assoc, ← suffixStendhal_e_mul_genEltF c,
    ← mul_assoc (suffixStendhal Q Λ Λc ν ν₀ _), h0, zero_mul, mul_zero]

/-! ### Coordinates of `ι(d) γ_c` -/

variable (Q Λ Λc ρ₃) in
/-- The `k`-linear map `d ↦ ι(d) γ_c` of a base generator `c`. -/
def blockGenMulF (c : FrontGen ℓ ν ν₀) : Tc ⊗[k] T →ₗ[k] Tp :=
  (LinearMap.mulRight k (genEltF Q Λ Λc ρ₃ c)).comp (blockTensorRLin Q Λ Λc ν ν₀)

theorem blockGenMulF_apply (c : FrontGen ℓ ν ν₀) (d : Tc ⊗[k] T) :
    blockGenMulF Q Λ Λc ρ₃ c d = blockTensorR Q Λ Λc ν ν₀ d * genEltF Q Λ Λc ρ₃ c := rfl

omit [DecidableEq I] in
theorem frontTriple_eq_iff (c : FrontGen ℓ ν ν₀) (y : {y // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ y})
    (x : {x // IsTopTerm (ℓ := ℓ) (ν := ν) ρ₁ x}) (hy : y.1.1 = c.1.2.1) (hx : x.1.1 = c.1.1)
    (p : FrontTriple ρ₁ ρ₂) :
    (⟨(c, y, x), hy, hx⟩ : FrontTriple ρ₁ ρ₂) = p ↔ p.1.1 = c ∧ (y, x) = (p.1.2.1, p.1.2.2) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · obtain ⟨⟨c', y', x'⟩, hp⟩ := p
    rintro ⟨rfl, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl

open Classical in
/-- **The coordinates of `ι(d) γ_c`** in the basis of `T̃^{λ⁺}` with dots on top: at the basis
term of a triple `p = (c', y, x)` it is the coordinate of `d` at `y ⊗ x` if `c' = c`, and `0`
otherwise. -/
theorem topBasis_repr_blockGenMulF (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (c : FrontGen ℓ ν ν₀)
    (d : Tc ⊗[k] T) (p : FrontTriple ρ₁ ρ₂) :
    (topBasis Q (plusLabels Λ Λc 0 z₀) hQ (frontWord ρ₁ ρ₂ ρ₃)
        (frontWord_spec hρ₁ hρ₂ hρ₃)).repr
        (blockGenMulF Q Λ Λc ρ₃ c d) (frontIdx ρ₁ ρ₂ ρ₃ (frontWord_spec hρ₁ hρ₂ hρ₃) p) =
      if p.1.1 = c then
        ((topBasis Q Λc hQ ρ₂ hρ₂).tensorProduct (topBasis Q Λ hQ ρ₁ hρ₁)).repr d
          (p.1.2.1, p.1.2.2)
      else 0 := by
  classical
  set Bp := topBasis Q (plusLabels Λ Λc 0 z₀) hQ (frontWord ρ₁ ρ₂ ρ₃)
    (frontWord_spec hρ₁ hρ₂ hρ₃)
  set BD := (topBasis Q Λc hQ ρ₂ hρ₂).tensorProduct (topBasis Q Λ hQ ρ₁ hρ₁)
  set b₀ := frontIdx ρ₁ ρ₂ ρ₃ (frontWord_spec hρ₁ hρ₂ hρ₃) p
  have hb : ∀ yx, Bp.repr (blockGenMulF Q Λ Λc ρ₃ c (BD yx)) b₀ =
      if p.1.1 = c then BD.repr (BD yx) (p.1.2.1, p.1.2.2) else 0 := fun yx => by
    obtain ⟨y, x⟩ := yx
    rw [BD.repr_self, blockGenMulF_apply, Module.Basis.tensorProduct_apply, topBasis_apply,
      topBasis_apply]
    by_cases hy : y.1.1 = c.1.2.1
    · by_cases hx : x.1.1 = c.1.1
      · have h := blockTensorR_topTerm_mul_genEltF (Q := Q) (Λ := Λ) (Λc := Λc) hρ₁ hρ₂ hρ₃
          ⟨(c, y, x), hy, hx⟩
        rw [h, ← topBasis_apply hQ _ (frontWord_spec hρ₁ hρ₂ hρ₃), Bp.repr_self,
          Finsupp.single_apply, Finsupp.single_apply]
        have hinj := frontIdx_injective (ρ₃ := ρ₃) (frontWord_spec hρ₁ hρ₂ hρ₃)
        have hiff := frontTriple_eq_iff c y x hy hx p
        by_cases hp : (⟨(c, y, x), hy, hx⟩ : FrontTriple ρ₁ ρ₂) = p
        · obtain ⟨h1, h2⟩ := hiff.1 hp
          rw [ite_eq_left_of_eq_true _ _ (eq_true (congrArg _ hp)),
            ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hp (hinj h))]
          split_ifs with h1 h2
          · exact (hp (hiff.2 ⟨h1, h2⟩)).elim
          · rfl
          · rfl
      · rw [blockTensorR_topTerm_mul_genEltF_of_ne_right hρ₁ c _ x hx, map_zero, Finsupp.coe_zero,
          Pi.zero_apply]
        split_ifs with h1
        · refine (Finsupp.single_apply_eq_zero.2 fun hh => (hx ?_).elim).symm
          subst h1
          rw [show x = p.1.2.2 from (congrArg Prod.snd hh).symm]
          exact p.2.2
        · rfl
    · rw [blockTensorR_topTerm_mul_genEltF_of_ne_left hρ₂ c y _ hy, map_zero, Finsupp.coe_zero,
        Pi.zero_apply]
      split_ifs with h1
      · refine (Finsupp.single_apply_eq_zero.2 fun hh => (hy ?_).elim).symm
        subst h1
        rw [show y = p.1.2.1 from (congrArg Prod.fst hh).symm]
        exact p.2.1
      · rfl
  have hext := BD.ext (f₁ := (Bp.coord b₀).comp (blockGenMulF Q Λ Λc ρ₃ c))
    (f₂ := if p.1.1 = c then BD.coord (p.1.2.1, p.1.2.2) else 0) fun yx => by
      rw [LinearMap.comp_apply, Bp.coord_apply, hb]
      split_ifs <;> rfl
  have := LinearMap.congr_fun hext d
  rw [LinearMap.comp_apply, Bp.coord_apply] at this
  rw [this]
  split_ifs <;> rfl

/-! ### The front idempotent on the basis of `T̃^{λ⁺}` -/

theorem frontStendhal_one_eq :
    frontStendhal Q Λ Λc ν ν₀ 1 = frontBot Q Λ Λc ν ν₀ (redOrderedKLR k Q Λc ν₀) := by
  change allOrdersLift (redRelations_frontBot Q Λ Λc)
    (StendhalAlgebraAllOrders.redOrderedIdem k Q Λc ν₀) = _
  have h := allOrdersLift_ofKLR (redRelations_frontBot Q Λ Λc (ν := ν) (ν₀ := ν₀))
    (redOrderedKLR k Q Λc ν₀)
  rw [ofKLR_redOrderedKLR] at h
  exact h

theorem frontMapKLR_sum {ι : Type*} (S : Finset ι)
    (f : ι → KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    frontMapKLR Q Λ Λc ν ν₀ (∑ x ∈ S, f x) = ∑ x ∈ S, frontMapKLR Q Λ Λc ν ν₀ (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, frontMapKLR_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frontMapKLR_add, ih]

theorem frontMapKLR_e_eq_sum (t : Seq (stendhalWeight 2 ν₀)) :
    frontMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e t) =
      ∑ s : Seq (stendhalWeight ℓ ν), KLRAlgebra.e (frontSeq s t) := by
  rw [frontMapKLR_eq_sum]
  exact Finset.sum_congr rfl fun s _ => insertMap_e s _ t

/-- **The front idempotent keeps exactly the basis terms whose top lies in `frontSet`.** -/
theorem frontStendhal_one_mul_topTerm
    {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}
    (hρ : ∀ w, wordProd M (ρ w) = w) (b : {b // IsTopTerm ρ b}) :
    frontStendhal Q Λ Λc ν ν₀ 1 * topTerm Q (plusLabels Λ Λc 0 z₀) hρ b =
      if b.1.2.1 • b.1.1 ∈ frontSet ν ν₀ then topTerm Q (plusLabels Λ Λc 0 z₀) hρ b
      else 0 := by
  classical
  rw [frontStendhal_one_eq, frontBot_apply, ← botMap_topElt_front hρ, ← map_mul,
    ← e_mul_topElt hρ b.1, ← mul_assoc, redOrderedKLR]
  rw [frontMapKLR_sum, Finset.sum_mul, Finset.sum_mul]
  simp_rw [frontMapKLR_e_eq_sum, Finset.sum_mul, KLRAlgebra.e_mul_e]
  split_ifs with hm
  · obtain ⟨s, t, hst⟩ := exists_frontSeq_of_mem hm
    have ht : IsRedOrdered t := ((isRedOrdered_frontSeq s t).1 (hst ▸ b.2.2.1)).2
    rw [Finset.sum_eq_single_of_mem t (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩),
      Finset.sum_eq_single s, ite_eq_left_of_eq_true _ _ (eq_true hst), hst, e_mul_topElt hρ b.1]
    · intro s' _ hs'
      rw [ite_eq_right_of_eq_false _ _
        (eq_false fun h => hs' (frontSeq_injective (h.trans hst.symm)).1), zero_mul]
    · simp
    · intro t' _ ht'
      refine Finset.sum_eq_zero fun s' _ => ?_
      rw [ite_eq_right_of_eq_false _ _
        (eq_false fun h => ht' (frontSeq_injective (h.trans hst.symm)).2), zero_mul]
  · rw [Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun s _ => ?_, map_zero]
    split_ifs with h
    · exact absurd (h ▸ frontSeq_mem_frontSet s t) hm
    · exact zero_mul _

end Categorification.Stendhal.CupCap
