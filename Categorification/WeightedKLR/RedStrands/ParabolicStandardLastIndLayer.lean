/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndMap
import Categorification.WeightedKLR.RedStrands.BlackAffineProjection
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleLayer
import Categorification.KLR.Crystal.IndDecomp

/-!
# Late red idempotents kill the first-slide induction

Webster, arXiv:1309.3796v3, proof of Proposition 5.5. In the induction `F_i N` of a parabolic
standard module along adding a black strand at the far right of the black block, every
idempotent of the affine cover whose last red strand stands after position `|α| + 1` acts by
zero (`e_smul_lastIndF_eq_zero`). This is the vanishing needed to let the next last-red layer
quotient act on the induced module.
-/

noncomputable section

namespace Categorification.TypeA
open Equiv
variable {n n' m : ℕ} (h : n + n' = m)

/-- A shuffle sends the `q`-th position of the first block, under `u⁻¹`, to a position at most
`q + n'`: only the earlier positions of the first block and the second block can precede it. -/
theorem shuffle_inl_le (u : Shuffle h) (q : Fin n) :
    (u.1⁻¹ (blockEquiv h (Sum.inl q))).val ≤ q.val + n' := by
  set f := u.1⁻¹ (blockEquiv h (Sum.inl q))
  let φ : Fin m → Fin n ⊕ Fin n' := fun x => (blockEquiv h).symm (u.1 x)
  have hφ : Function.Injective φ := fun x y hxy =>
    u.1.injective ((blockEquiv h).symm.injective hxy)
  have hsub : (Finset.univ.filter (fun x : Fin m => x < f)).image φ ⊆
      (Finset.univ.filter (fun q' : Fin n => q' < q)).map Function.Embedding.inl ∪
        Finset.univ.map Function.Embedding.inr := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    have hx : x < f := (Finset.mem_filter.1 hx).2
    rcases hφx : φ x with q' | y
    · refine Finset.mem_union_left _ (Finset.mem_map.2 ⟨q', ?_, rfl⟩)
      have hxq : x = u.1⁻¹ (blockEquiv h (Sum.inl q')) := by
        rw [← hφx]; simp [φ, Perm.inv_def]
      rw [hxq] at hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, u.2.1.lt_iff_lt.1 hx⟩
    · exact Finset.mem_union_right _ (Finset.mem_map.2 ⟨y, Finset.mem_univ _, rfl⟩)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hφ] at h1
  have h2 := Finset.card_union_le
    ((Finset.univ.filter (fun q' : Fin n => q' < q)).map Function.Embedding.inl)
    (Finset.univ.map (Function.Embedding.inr : Fin n' ↪ Fin n ⊕ Fin n'))
  have h3 : (Finset.univ.filter (fun x : Fin m => x < f)).card = f.val := by
    rw [Finset.filter_gt_eq_Iio]; exact Fin.card_Iio f
  have h4 : (Finset.univ.filter (fun q' : Fin n => q' < q)).card = q.val := by
    rw [Finset.filter_gt_eq_Iio]; exact Fin.card_Iio q
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin] at h2
  omega

end Categorification.TypeA


namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ β : Multiset I)

local notation "Si" j => (Singleton.singleton j : Multiset I)

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "πA" => affineTensorProjection (Q := Q) Λ (θ + β)

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- The affine projection of `1_s` is `1_s` when `s` is red-ordered and `0` otherwise. -/
theorem affineTensorProjection_e_of_ordered (ν : Multiset I) (s : Seq (stendhalWeight (ℓ+1) ν))
    (hs : IsRedOrdered s) :
    affineTensorProjection (Q := Q) Λ ν (KLRAlgebra.e s) =
      TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) := by
  change TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (affineCover Q Λ ν _)) = _
  rw [affineCover_e]
  exact congrArg _ (Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans
    (ite_eq_left hs)))

theorem affineTensorProjection_e_of_not_ordered (ν : Multiset I)
    (s : Seq (stendhalWeight (ℓ+1) ν)) (hs : ¬ IsRedOrdered s) :
    affineTensorProjection (Q := Q) Λ ν (KLRAlgebra.e s) = 0 := by
  change TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (affineCover Q Λ ν _)) = _
  rw [affineCover_e]
  have : orderProjection Q Λ ν (StendhalAlgebraAllOrders.e s) = 0 :=
    Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_right hs))
  rw [this, map_zero]

/-- An idempotent whose last red strand lies after position `|α|` kills `S N`. -/
theorem affineTensorProjection_e_smul_standard (a : Seq (stendhalWeight (ℓ+1) (θ + β)))
    (q : Fin (stendhalWeight (ℓ+1) (θ + β)).card) (hq : a.lbl q = .inr (Fin.last ℓ))
    (hlt : (Aₚ).card < q.val) (m : ParabolicStandardT Q Λ θ β N hQ) :
    πA (KLRAlgebra.e a) • m = 0 := by
  by_cases ha : IsRedOrdered a
  · rw [affineTensorProjection_e_of_ordered Q Λ _ a ha]
    have hp : (Aₚ).card < (stendhalWeight (ℓ+1) (θ + β)).card := hlt.trans q.isLt
    set p : Fin (stendhalWeight (ℓ+1) (θ + β)).card := ⟨(Aₚ).card, hp⟩
    have hmem : TensorProductAlgebra.mk Q Λ (θ + β) (StendhalAlgebra.e a ha) ∈
        smallerSuffixIdeal (ν := θ + β) Q Λ p :=
      TwoSidedIdeal.subset_span ⟨a, ha, q, hlt, hq, rfl⟩
    have h0 : (smallerSuffixIdeal (ν := θ + β) Q Λ p).ringCon.mkₐ k
        (TensorProductAlgebra.mk Q Λ (θ + β) (StendhalAlgebra.e a ha)) = 0 := by
      rw [← map_zero ((smallerSuffixIdeal (ν := θ + β) Q Λ p).ringCon.mkₐ k)]
      exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 (by simpa using hmem))
    change parabolicStandardAction Q Λ θ β N hQ _ m = 0
    rw [← parabolicStandardLayerAction_comp Q Λ θ β N hQ p rfl, AlgHom.comp_apply, h0,
      map_zero]
    rfl
  · rw [affineTensorProjection_e_of_not_ordered Q Λ _ a ha, zero_smul]

local notation "μ₀" => stendhalWeight (ℓ+1) (θ + β)
local notation "μ₁" => stendhalWeight (ℓ+1) ((Si i) + (θ + β))
local notation "σ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin (ℓ+1)))
local notation "S" => affineCoverQ Q Λ
local notation "π'" => affineTensorProjection (Q := Q) Λ ((Si i) + (θ + β))
local notation "aB" => appendBlackHom Q Λ i θ β

omit [DecidableEq I] in
theorem blackCast : μ₀ + σ = μ₁ :=
  (add_comm _ _).trans (stendhalWeight_black_cons (ℓ := ℓ+1) i (θ + β))

local notation "C" => castKLR S (blackCast (ℓ := ℓ) i θ β)

omit [DecidableEq I] in
private theorem castKLR_castKLR' {J : Type*} [DecidableEq J] {Q' : J → J → MvPolynomial (Fin 2) k}
    {a b c : Multiset J} (h : a = b) (h' : b = c) (z : KLRAlgebra k Q' a) :
    castKLR Q' h' (castKLR Q' h z) = castKLR Q' (h.trans h') z := by
  subst c; subst b; rfl

theorem appendBlack_affine (x : KLRAlgebra k S μ₀) :
    aB (πA x) = π' (C (concat S μ₀ σ (x ⊗ₜ 1))) := by
  show appendBlack Q Λ i (θ + β) (πA x) = _
  rw [appendBlack_affineTensorProjection, cL, castKLR_castKLR']

theorem appendBlack_one_affine : aB 1 = π' (C (oneConcat S μ₀ σ)) := by
  rw [← map_one πA, appendBlack_affine, ← concat_one]; rfl

/-- The element `π'(X 1_{μ,i})` of the corner `T(i + (θ + β)) · appendBlack(1)`. -/
def blackCorner (X : KLRAlgebra k S (μ₀ + σ)) : Corner aB :=
  ⟨π' (C (X * oneConcat S μ₀ σ)), by
    rw [mem_lIdeal, appendBlack_one_affine, ← map_mul, ← map_mul, mul_assoc,
      oneConcat_idem.eq]⟩

theorem tmul_blackCorner_mul_concat (H : KLRAlgebra k S (μ₀ + σ)) (X : KLRAlgebra k S μ₀)
    (n : ParabolicStandardT Q Λ θ β N hQ) :
    Ind.tmul (blackCorner Q Λ i θ β (H * concat S μ₀ σ (X ⊗ₜ 1))) n =
      Ind.tmul (blackCorner Q Λ i θ β H) (πA X • n) := by
  rw [← Ind.op_smul_tmul]
  congr 1
  apply Subtype.ext
  rw [op_smul_val]
  change π' (C (H * concat S μ₀ σ (X ⊗ₜ 1) * oneConcat S μ₀ σ)) =
    π' (C (H * oneConcat S μ₀ σ)) * aB (πA X)
  rw [appendBlack_affine, ← map_mul, ← map_mul, mul_assoc, mul_assoc, concat_mul_oneConcat,
    oneConcat_mul_concat]


theorem blackCorner_add (X Y : KLRAlgebra k S (μ₀ + σ)) :
    blackCorner Q Λ i θ β (X + Y) = blackCorner Q Λ i θ β X + blackCorner Q Λ i θ β Y :=
  Subtype.ext (by
    change π' (C ((X + Y) * oneConcat S μ₀ σ)) =
      π' (C (X * oneConcat S μ₀ σ)) + π' (C (Y * oneConcat S μ₀ σ))
    rw [add_mul, map_add, map_add])

theorem blackCorner_zero : blackCorner Q Λ i θ β 0 = 0 :=
  Subtype.ext (by
    change π' (C (0 * oneConcat S μ₀ σ)) = 0
    rw [zero_mul, map_zero, map_zero])

theorem blackCorner_mul_oneConcat (X : KLRAlgebra k S (μ₀ + σ)) :
    blackCorner Q Λ i θ β (X * oneConcat S μ₀ σ) = blackCorner Q Λ i θ β X :=
  Subtype.ext (by
    change π' (C (X * oneConcat S μ₀ σ * oneConcat S μ₀ σ)) = π' (C (X * oneConcat S μ₀ σ))
    rw [mul_assoc, oneConcat_idem.eq])

omit [DecidableEq I] in
/-- If the last red strand of `s'` sits after position `|α| + 1` and `u • s' = a b`, then the
last red strand of `a` sits after position `|α|`. -/
theorem exists_late_red_of_append (s' : Seq (μ₀ + σ)) (a0 : Fin (Multiset.card (μ₀ + σ)))
    (hred : s'.lbl a0 = .inr (Fin.last ℓ)) (hlt : (Aₚ).card + 1 < a0.val)
    (u : TypeA.Shuffle (Seq.card_add' μ₀ σ)) (a : Seq μ₀) (b : Seq σ)
    (hab : a.append b = u.1 • s') :
    ∃ q : Fin (Multiset.card (μ₀)), a.lbl q = .inr (Fin.last ℓ) ∧ (Aₚ).card < q.val := by
  have hP : (u.1 • s').1 (u.1 a0) = .inr (Fin.last ℓ) := by
    rw [Seq.smul_apply, Equiv.symm_apply_apply]; exact hred
  rw [← hab] at hP
  rcases hb : (TypeA.blockEquiv (Seq.card_add' μ₀ σ)).symm (u.1 a0) with q | r
  · have hPq : u.1 a0 = Seq.posL σ q := by
      rw [Seq.posL, ← hb, Equiv.apply_symm_apply]
    rw [hPq, Seq.append_posL] at hP
    refine ⟨q, hP, ?_⟩
    have hle := TypeA.shuffle_inl_le (Seq.card_add' μ₀ σ) u q
    have h1 : u.1⁻¹ (TypeA.blockEquiv (Seq.card_add' μ₀ σ) (Sum.inl q)) = a0 := by
      rw [← Seq.posL, ← hPq, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [h1, Multiset.card_singleton] at hle
    omega
  · have hPr : u.1 a0 = Seq.posR μ₀ r := by
      rw [Seq.posR, ← hb, Equiv.apply_symm_apply]
    rw [hPr, Seq.append_posR] at hP
    have hm := b.mem r
    rw [hP, Multiset.mem_singleton] at hm
    exact absurd hm (by simp)

theorem tmul_blackCorner_concatIdem (s' : Seq (μ₀ + σ)) (a0 : Fin (Multiset.card (μ₀ + σ)))
    (hred : s'.lbl a0 = .inr (Fin.last ℓ)) (hlt : (Aₚ).card + 1 < a0.val)
    (u : TypeA.Shuffle (Seq.card_add' μ₀ σ)) (H : KLRAlgebra k S (μ₀ + σ))
    (t : TensorKLR S μ₀ σ) (n : ParabolicStandardT Q Λ θ β N hQ) :
    Ind.tmul (blackCorner Q Λ i θ β (H * concat S μ₀ σ (concatIdem (u.1 • s') * t))) n = 0 := by
  by_cases hm : u.1 • s' ∈ concatSet μ₀ σ
  · obtain ⟨a, b, hab⟩ := mem_concatSet.1 hm
    obtain ⟨q, hq, hqlt⟩ := exists_late_red_of_append i θ β s' a0 hred hlt u a b hab
    rw [← hab, concatIdem_append]
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      have : (KLRAlgebra.e a * x) ⊗ₜ[k] (KLRAlgebra.e b * y) =
          ((1 : KLRAlgebra k S μ₀) ⊗ₜ[k] (KLRAlgebra.e b * y)) *
            ((KLRAlgebra.e a * x) ⊗ₜ[k] (1 : KLRAlgebra k S σ)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [this, concat_mul, ← mul_assoc, tmul_blackCorner_mul_concat, map_mul, mul_smul,
        affineTensorProjection_e_smul_standard Q Λ θ β N hQ a q hq hqlt, Ind.tmul_zero]
    | add t t' ht ht' =>
      rw [mul_add, map_add, mul_add, blackCorner_add, Ind.add_tmul, ht, ht', add_zero]
  · rw [concatIdem_of_not_mem hm, zero_mul, map_zero, mul_zero, blackCorner_zero,
      Ind.zero_tmul]


/-- `X ↦ π'(X 1_{μ,i}) ⊗ n` as an additive map. -/
def blackTmul (n : ParabolicStandardT Q Λ θ β N hQ) :
    KLRAlgebra k S (μ₀ + σ) →+ LastIndF Q Λ i θ β N hQ where
  toFun X := Ind.tmul (blackCorner Q Λ i θ β X) n
  map_zero' := by rw [blackCorner_zero, Ind.zero_tmul]
  map_add' X Y := by rw [blackCorner_add, Ind.add_tmul]

/-- Every element of the corner of `appendBlack` is `π'(X 1_{μ,i})` for some `X`. -/
theorem exists_blackCorner_eq (z : Corner aB) :
    ∃ X : KLRAlgebra k S (μ₀ + σ), blackCorner Q Λ i θ β X = z := by
  obtain ⟨Z, hZ⟩ := affineTensorProjection_surjective (Q := Q) Λ ((Si i) + (θ + β)) z.1
  refine ⟨(C).symm Z, Subtype.ext ?_⟩
  change π' (C ((C).symm Z * oneConcat S μ₀ σ)) = z.1
  rw [map_mul, AlgEquiv.apply_symm_apply, map_mul, hZ, ← appendBlack_one_affine]
  exact mem_lIdeal.1 z.2

/-- **The next layer ideal kills `F_i(S N)`**: an idempotent of the affine cover whose last
red strand lies after position `|α| + 1` acts by zero on the induced module. -/
theorem e_smul_lastIndF_eq_zero (s' : Seq (μ₀ + σ)) (a0 : Fin (Multiset.card (μ₀ + σ)))
    (hred : s'.lbl a0 = .inr (Fin.last ℓ)) (hlt : (Aₚ).card + 1 < a0.val)
    (x : LastIndF Q Λ i θ β N hQ) : π' (C (KLRAlgebra.e s')) • x = 0 := by
  induction x using Ind.induction_on with
  | zero => rw [smul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  | tmul z n =>
    obtain ⟨X, rfl⟩ := exists_blackCorner_eq Q Λ i θ β z
    rw [Ind.smul_tmul]
    have hz : π' (C (KLRAlgebra.e s')) • blackCorner Q Λ i θ β X =
        blackCorner Q Λ i θ β (KLRAlgebra.e s' * X) := Subtype.ext (by
      change π' (C (KLRAlgebra.e s')) * π' (C (X * oneConcat S μ₀ σ)) =
        π' (C (KLRAlgebra.e s' * X * oneConcat S μ₀ σ))
      rw [← map_mul, ← map_mul, mul_assoc])
    rw [hz, ← blackCorner_mul_oneConcat, mul_assoc]
    obtain ⟨g, hg⟩ := exists_rightFreeMapOf_eq (affineCoverQ_symm Λ hQ)
      shufWord_spec (r := X * oneConcat S μ₀ σ) (by rw [mul_assoc, oneConcat_idem.eq])
    rw [← hg, rightFreeMapOf_apply, Finsupp.mul_sum]
    change blackTmul Q Λ i θ β N hQ n _ = 0
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_eq_zero fun u _ => ?_
    change Ind.tmul (blackCorner Q Λ i θ β _) n = 0
    rw [← mul_assoc, e_mul_hatWRevOf shufWord shufWord_spec, mul_assoc, ← concat_mul]
    exact tmul_blackCorner_concatIdem Q Λ i θ β N hQ s' a0 hred hlt u _ _ n

end Categorification.Stendhal
