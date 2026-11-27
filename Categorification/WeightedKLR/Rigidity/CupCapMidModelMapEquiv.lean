/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidModelMapInverse

/-!
# `K̃^{λ⁺}_λ` is isomorphic to the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, for a cap inserted after the red strand
`λ_j` (any `j ≤ ℓ`). The map `CupCap.midCapToModel` and its inverse `CupCap.midModelToCap`
compose to the identity in both orders. After the inverse, the map to the model sends `Z ⊗ v` to
`∑_s e E_s Z ⊗ v = e μ(1) Z ⊗ v = Z ⊗ v`. In the other order the cap generator `cap s n v` goes to
`c(s, n) · cap(s, c, v) · U E_{s,n}`, where `U` passes the strands of `s` at `n, …, c - 1` under
the maximum; by (max1) along the passage this is `cap s n v`, the scalars cancelling against
`c(s, n)`. When `n > c`, or a red strand lies in `[n, c)`, the generator vanishes in both
`K̃^{λ⁺}_λ` and the model, by the order of the red strands.

## Main results

* `CupCap.midCapElt_passU`: (max1) along a passage of black strands under the maximum.
* `CupCap.midCapToModel_midModelToCapAdd`, `CupCap.midModelToCap_midCapToModel`: the two
  composites are the identity.
* `CupCap.midCapModelEquiv`: **Lemma 7.17** for a cap after `λ_j`: under the support hypothesis
  on `L`, the two pull-off identities, invertible scalars of (max1) and the KLR relations of `λ`
  on the model, `K̃^{λ⁺}_λ` is isomorphic as a bimodule to the model `L ⊗ e T̃^{λ⁺}`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}
  {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀
local notation "μ" => midMapKLR j hj Q Λ Λc ν ν₀
local notation "Ev" => Env k Q Λ Λc j hj ν ν₀
local notation "K" => CapTilde k Q Λ Λc j hj ν ν₀ L
local notation "cpos" s:max => midCPos j s
local notation "gC" => midGenCap j hj Q Λ Λc ν₀
local notation "F" => midModelToCapAdd j hj Q Λ Λc ν ν₀ L
local notation "img" =>
  midCapImage (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) L

/-! ### Generators and sums -/

theorem envMk_one_one_mid : (Env.mk (1 : T) (1 : Tp) : Ev) = 1 := by
  unfold Env.mk
  rw [op_one]
  rfl

theorem capElt_one_one_mid (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) :
    (capElt 1 s n v 1 : K) = Submodule.Quotient.mk (gen (s, n) v) := by
  rw [capElt, act, map_one, envMk_one_one_mid, one_smul]

theorem midGen_add (X Y : Tp) :
    midGen j hj Q Λ Λc ν ν₀ (X + Y) = midGen j hj Q Λ Λc ν ν₀ X + midGen j hj Q Λ Λc ν ν₀ Y :=
  Subtype.ext (by rw [Submodule.coe_add, midGen_val, midGen_val, midGen_val, mul_add, op_add])

theorem sum_tmul_midGen (f : Seq (stendhalWeight ℓ ν) → Tp) (v : L) :
    ∑ s, (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (f s)) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (∑ s, f s)) v := by
  let φ : Tp →+ MidModel j hj Q Λ Λc ν ν₀ L :=
    AddMonoidHom.mk' (fun Z => Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) v)
      (fun X Y => by rw [midGen_add, Ind.add_tmul])
  exact (map_sum φ f Finset.univ).symm

theorem midGen_botMap_midMapKLR_one (z : Corner (midOp j hj Q Λ Λc ν ν₀)) :
    midGen j hj Q Λ Λc ν ν₀ (bot (μ 1) * z.1.unop) = z := by
  apply Subtype.ext
  rw [midGen_val]
  have h : σ 1 * bot (μ 1) = σ 1 := by
    rw [midStendhal_one_eq_bot, ← map_mul, ← midMapKLR_mul, mul_one]
  rw [← mul_assoc, h]
  exact (z.2 : op (σ 1 * z.1.unop) = z.1)

/-! ### The map to the model after its inverse -/

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- **The map to the model after its inverse is the identity.** -/
theorem midCapToModel_midModelToCapAdd (hP : PullOff k Q Λc ν₀ L)
    (hPL : PullOffLeft k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midCapToModel L hL hP hPL hκ hR (F y) = toMidBimod L hL hR y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']; rfl
  | tmul z v =>
    rw [midModelToCapAdd_tmul, midInvFun, map_sum]
    have h1 : ∀ s : Seq (stendhalWeight ℓ ν), midCapToModel L hL hP hPL hκ hR
        ((Env.mk 1 z.1.unop : Ev) • gC s v) = toMidBimod L hL hR
          (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (E s) * z.1.unop)) v) := by
      intro s
      rw [map_smul, midGenCap, capElt_one_one_mid, midCapToModel_mk]
      change midEnvAlg L hL hR (Env.mk 1 z.1.unop) (img (s, cpos s) v) = _
      rw [midEnvAlg_mk, map_one, Module.End.one_apply]
      rw [midCapImage_of_le s (cpos s) v le_rfl, midCapScalar_self, one_smul, op_smul_tmul_midGen,
        midCapBot, Nat.sub_self, passU_zero, mul_one, (KLRAlgebra.eSum_idem _).eq]
      rfl
    rw [Finset.sum_congr rfl fun s _ => h1 s]
    change (∑ s, (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (E s) * z.1.unop)) v :
      MidModel j hj Q Λ Λc ν ν₀ L)) = Ind.tmul z v
    rw [sum_tmul_midGen, ← Finset.sum_mul, ← map_sum, ← midMapKLR_one,
      midGen_botMap_midMapKLR_one]

/-! ### The inverse after the map to the model -/

/-- **(max1) along a passage**: a cap generator whose black strands left of the maximum pass
under it moves left, picking up the scalars of (max1). -/
theorem midCapElt_passU (a : T) (s : Seq (stendhalWeight ℓ ν)) (v : L) (b : Rp) :
    ∀ (d n : ℕ) (hnd : n + d ≤ m), (∀ (r : ℕ) (h : r < m), n ≤ r → r < n + d →
      ∃ i, s.lbl ⟨r, h⟩ = .inl i) →
    (capElt a s ⟨n + d, by omega⟩ v (passU Q Λ Λc j hj ν ν₀ n d * b) : K) =
      capElt (a * algebraMap k T (∏ r ∈ Finset.Ico n (n + d),
        if h : r < m then labelScalar Q ν₀ (s.lbl ⟨r, h⟩) else 1)) s ⟨n, by omega⟩ v b
  | 0, n, _, _ => by
    simp only [passU_zero, one_mul, add_zero, Finset.Ico_self, Finset.prod_empty, map_one,
      mul_one]
  | d + 1, n, hnd, hb => by
    obtain ⟨i, hi⟩ := hb n (by omega) le_rfl (by omega)
    have hfin : (⟨n + (d + 1), by omega⟩ : Fin (m + 1)) = ⟨n + 1 + d, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hfin, passU_succ_left, mul_assoc,
      midCapElt_passU a s v (underRight _ n * b) d (n + 1) (by omega)
        (fun r h h1 h2 => hb r h (by omega) (by omega))]
    refine (capElt_over _ s ⟨n + 1, by omega⟩ v i (Nat.succ_pos n) hi b).trans ?_
    have hP : (∏ r ∈ Finset.Ico n (n + (d + 1)),
        if h : r < m then labelScalar Q ν₀ (s.lbl ⟨r, h⟩) else 1) =
        cupScalar Q ν₀ i * ∏ r ∈ Finset.Ico (n + 1) (n + 1 + d),
          if h : r < m then labelScalar Q ν₀ (s.lbl ⟨r, h⟩) else 1 := by
      rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : n < n + (d + 1))]
      simp only [show n + (d + 1) = n + 1 + d by omega, show n < m by omega, ↓reduceDIte, hi,
        labelScalar, Sum.elim_inl]
    rw [hP, map_mul, mul_assoc, ← map_mul, ← map_mul, mul_comm (cupScalar Q ν₀ i)]
    rfl

theorem midCapScalar_mul_prod (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) :
    midCapScalar j Q ν₀ s n * ∏ r ∈ Finset.Ico n (midPos j s),
      (if h : r < m then labelScalar Q ν₀ (s.lbl ⟨r, h⟩) else 1) = 1 := by
  rw [midCapScalar, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun r _ => ?_
  by_cases h : r < m
  · simp only [midFac, h, ↓reduceDIte]
    exact Ring.inverse_mul_cancel _ (isUnit_labelScalar Q ν₀ hκ _)
  · simp [midFac, h]

theorem botMap_eSum_insertSet_eq_zero (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (h : ∀ w, ¬ IsRedOrdered (insertSeq (j := j) (hj := hj) (ν₀ := ν₀) s n hn w)) :
    bot (Eat s n hn) = 0 := by
  rw [KLRAlgebra.eSum, map_sum]
  refine Finset.sum_eq_zero fun t ht => ?_
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 ht
  rw [botMap, AlgHom.comp_apply, orderProjection_e_of_not (h w)]

/-- The inverse of the model of a cap generator below the maximum. -/
theorem midModelToCapAdd_midCapImage (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (h : n.val ≤ midPos j s) :
    F (img (s, n) v) = capElt (midCapScalar j Q ν₀ s n • (1 : T)) s (cpos s) v
      (midCapBot j hj Q Λ Λc ν₀ s n h) := by
  rw [midCapImage_of_le s n v h, ← tmul_midGen_smul, midModelToCapAdd_tmul_midGen, midInvFun,
    Finset.sum_eq_single s (fun t _ ht => ?_) (by simp)]
  · rw [← map_smul, smul_midGenCap, capElt_smul_right]
  · rw [← map_smul, smul_midGenCap, capElt_smul_right, capElt_mid_eSum,
      ← eSum_mul_midCapBot s h, ← mul_assoc, eSum_mid_mul_eSum_mid]
    simp [ht, capElt_zero_right]

/-- **The inverse after the map to the model is the identity on the generators**. -/
theorem midModelToCapAdd_midCapToModel_gen (hP : PullOff k Q Λc ν₀ L)
    (hPL : PullOffLeft k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1))
    (v : L) :
    F (ofMidBimod L hL hR (midCapToModel L hL hP hPL hκ hR
      (Submodule.Quotient.mk (gen (s, n) v)))) = Submodule.Quotient.mk (gen (s, n) v) := by
  rw [midCapToModel_mk]
  change F (img (s, n) v) = _
  rw [← capElt_one_one_mid]
  have hn : n.val ≤ m := Nat.lt_succ_iff.1 n.2
  by_cases hlt : midPos j s < n.val
  · rw [midCapImage_of_lt s n v hlt, map_zero]
    have hjl : j < ℓ := lt_of_midPos_lt j (by omega : midPos j s < m) le_rfl
    obtain ⟨a, ha, hla⟩ := midPos_of_lt j s hjl
    exact (capElt_eq_zero_of_bottom _ _ _ _ _ fun t =>
      not_isRedOrdered_of_red_left s hn t a (by omega) hla le_rfl).symm
  have h : n.val ≤ midPos j s := by omega
  rw [midModelToCapAdd_midCapImage s n v h]
  by_cases hs : IsRedOrdered s
  swap
  · rw [capElt_eq_zero_of_top _ hs, capElt_eq_zero_of_top _ hs]
  by_cases hred : ∃ (a : Fin m) (r : Fin ℓ), n.val ≤ a.val ∧ a.val < midPos j s ∧
      s.lbl a = .inr r
  · obtain ⟨a, r, ha, hac, hr⟩ := hred
    have hrj : r.val < j := by
      by_cases hjl : j < ℓ
      · obtain ⟨b, hb, hlb⟩ := midPos_of_lt j s hjl
        exact hs a b r ⟨j, hjl⟩ (by rw [Fin.lt_def, hb]; exact hac) hr hlb
      · have := r.2
        omega
    have hbot : bot (midCapBot j hj Q Λ Λc ν₀ s n h) = 0 := by
      rw [midCapBot, map_mul, botMap_eSum_insertSet_eq_zero s _ fun w =>
        not_isRedOrdered_of_red_right s _ w a ha hr hrj, mul_zero]
    rw [capElt_eq_zero_of_botMap _ _ _ _ hbot, capElt_eq_zero_of_bottom _ _ _ _ _ fun t =>
      not_isRedOrdered_of_red_right s hn t a ha hr hrj]
  · have hcm := midPos_le j s
    have hb : ∀ (r : ℕ) (hr : r < m), n.val ≤ r → r < n.val + (midPos j s - n.val) →
        ∃ i, s.lbl ⟨r, hr⟩ = .inl i := by
      intro r hr h1 h2
      cases hl : s.lbl ⟨r, hr⟩ with
      | inl i => exact ⟨i, rfl⟩
      | inr r' => exact absurd ⟨⟨r, hr⟩, r', h1, by simp only; omega, hl⟩ hred
    rw [midCapBot_eq s h,
      capElt_fin_congr _ s (cpos s) ⟨n.val + (midPos j s - n.val), by omega⟩ v _
        (by simp only; omega),
      midCapElt_passU _ s v _ (midPos j s - n.val) n.val (by omega) hb,
      capElt_fin_congr _ s ⟨n.val, by omega⟩ n v _ rfl]
    have he := capElt_eq_eSum_mul (L := L) (Q := Q) (Λc := Λc) (ν₀ := ν₀) (j := j) (hj := hj)
      (midCapScalar j Q ν₀ s n • (1 : T) * algebraMap k T (∏ r ∈ Finset.Ico n.val
        (n.val + (midPos j s - n.val)),
          if h : r < m then labelScalar Q ν₀ (s.lbl ⟨r, h⟩) else 1)) s n v 1
    rw [mul_one] at he
    rw [← he, Nat.add_sub_cancel' h, smul_mul_assoc, one_mul, Algebra.smul_def, ← map_mul,
      midCapScalar_mul_prod hκ s n, map_one]

/-- **The inverse after the map to the model is the identity.** -/
theorem midModelToCap_midCapToModel (hP : PullOff k Q Λc ν₀ L)
    (hPL : PullOffLeft k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    (midModelToCap L hL hκ hR).comp (midCapToModel L hL hP hPL hκ hR) =
      (LinearMap.id : K →ₗ[Ev] K) := by
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext fun p r => ?_)
  rw [← Finsupp.smul_single_one, LinearMap.comp_apply, LinearMap.comp_apply, map_smul, map_smul,
    map_smul, LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply]
  exact congrArg (r • ·) (midModelToCapAdd_midCapToModel_gen hP hPL hκ hR p.1.1 p.1.2 p.2)

/-- **Lemma 7.17 for a cap after `λ_j`** (Webster, arXiv:1309.3796v3, proof of Lemma 7.17): when
`L` is supported on the loadings with `μ` and `μ*` at the ends, both pull-off identities hold,
the scalars of (max1) are units and the KLR relations of `λ` hold on the model, `K̃^{λ⁺}_λ` is
isomorphic as a bimodule to the model `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}` with the maximum just before
the red strand `λ_{j+1}`. -/
def midCapModelEquiv (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    K ≃ₗ[Ev] MidBimod L hL hR :=
  LinearEquiv.ofLinearMap (midCapToModel L hL hP hPL hκ hR) (midModelToCap L hL hκ hR)
    (LinearMap.ext fun y => midCapToModel_midModelToCapAdd hP hPL hκ hR (ofMidBimod L hL hR y))
    (midModelToCap_midCapToModel hP hPL hκ hR)

theorem midCapModelEquiv_mk (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (q : CapIdx ℓ ν) (v : L) :
    midCapModelEquiv hP hPL hκ hR (Submodule.Quotient.mk (gen q v)) =
      toMidBimod L hL hR (img q v) :=
  midCapToModel_mk L hL hP hPL hκ hR q v

end Categorification.Stendhal.CupCap
