/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapModelMap
import Categorification.WeightedKLR.Rigidity.CupCapSpanning

/-!
# The inverse of the map from `K̃^{λ⁺}_λ` to the model of a cap at the right end

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ`.

## Main results

* `CupCap.sum_capElt_prefixMapKLR`: diagrams of `λ` placed left of the maximum at the right end
  pass through the cap generators at the right end.
* `CupCap.modelToCap`: the bimodule map from the model `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}` to
  `K̃^{λ⁺}_λ`, `Z ⊗ v ↦ ∑_s c(s, m)⁻¹ · cap(s, m, v) · Z`.
* `CupCap.capElt_passU`: (max1) along a passage of black strands under the maximum.
* `CupCap.capModelEquiv`: when the scalars of (max1) are units, `L` is supported on the
  loadings `μ ⋯ μ*` and the left pull-off identity holds, `K̃^{λ⁺}_λ` is isomorphic to the
  model.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section PrefixKLR

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

theorem prefixMapKLR_algebraMap (c : k) :
    prefixMapKLR Q Λ Λc ν ν₀ (algebraMap k (KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) c) =
      c • KLRAlgebra.eSum _ (endSet ν ν₀) := by
  unfold prefixMapKLR
  rw [AlgHom.commutes, AlgHom.commutes, Corner.val_algebraMap, Algebra.smul_def]

end PrefixKLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Prefix

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}
  {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
    (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl)
local notation "K" => CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L

/-- A generator at the right end only sees its bottom through the window idempotent. -/
theorem capElt_last_congr (a : T) (s : Seq (stendhalWeight ℓ ν)) (v : L) {y y' : Rp}
    (h : E s * y = E s * y') (b : Rp) :
    (capElt a s (Fin.last m) v (y * b) : K) = capElt a s (Fin.last m) v (y' * b) := by
  rw [capElt_eq_eSum_mul, ← mul_assoc]
  change capElt a s (Fin.last m) v (E s * y * b) = _
  rw [h, mul_assoc]
  exact (capElt_eq_eSum_mul a s (Fin.last m) v _).symm

theorem eSum_end_mul_eSum_end {s s' : Seq (stendhalWeight ℓ ν)} (h : s ≠ s') :
    (E s * E s' : Rp) = 0 := by
  rw [KLRAlgebra.eSum_mul_eSum, Finset.disjoint_iff_inter_eq_empty.1, KLRAlgebra.eSum,
    Finset.sum_empty]
  refine Finset.disjoint_left.2 fun u hu hu' => h ?_
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
  exact ((insertSeq_mem_insertSet (s := s) (s' := s') (t := t)).1 hu').symm

theorem capElt_last_eSum_ne (a : T) {s s' : Seq (stendhalWeight ℓ ν)} (h : s ≠ s') (v : L)
    (b : Rp) : (capElt a s (Fin.last m) v (E s' * b) : K) = 0 := by
  rw [capElt_eq_eSum_mul, ← mul_assoc]
  change capElt a s (Fin.last m) v (E s * E s' * b) = 0
  rw [eSum_end_mul_eSum_end h, zero_mul, capElt_zero_right]

theorem prefixMapKLR_add (u u' : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    prefixMapKLR Q Λ Λc ν ν₀ (u + u') =
      prefixMapKLR Q Λ Λc ν ν₀ u + prefixMapKLR Q Λ Λc ν ν₀ u' := by
  unfold prefixMapKLR; rw [map_add, map_add]; rfl

theorem prefixMapKLR_zero : prefixMapKLR Q Λ Λc ν ν₀ (0 : KLRAlgebra k (stendhalQ Q Λ)
    (stendhalWeight ℓ ν)) = 0 := by
  unfold prefixMapKLR; rw [map_zero, map_zero]; rfl

theorem eSum_end_mul_eSum_endSet (s : Seq (stendhalWeight ℓ ν)) :
    (E s * KLRAlgebra.eSum _ (endSet ν ν₀) : Rp) = E s := by
  rw [KLRAlgebra.eSum_mul_eSum, Finset.inter_eq_left.2 (insertSet_subset_endSet s)]

omit [DecidableEq I] in
theorem sadj_smul_sadj_smul (p : ℕ) (s : Seq (stendhalWeight ℓ ν)) :
    sadj m p • sadj m p • s = s := by
  have h := inv_smul_smul (sadj m p) s
  rwa [sadj_inv] at h

variable (r : Seq (stendhalWeight ℓ ν) → k) (v : L)

local notation "Σc" a:max w:max b:max =>
  ∑ s, (capElt (algebraMap k T (r s) * a) s (Fin.last m) v
    (prefixMapKLR Q Λ Λc ν ν₀ w * b) : K)
local notation "Σt" a:max w:max b:max =>
  ∑ s, (capElt (algebraMap k T (r s) * a * topMap k Q Λ ν w) s (Fin.last m) v b : K)

theorem sum_capElt_prefix_algebraMap (c : k) (a : T) (b : Rp) :
    Σc a (algebraMap k _ c) b = Σt a (algebraMap k _ c) b := by
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [prefixMapKLR_algebraMap, smul_mul_assoc, capElt_smul_right, AlgHom.commutes,
    ((Algebra.commutes c _).symm).trans (Algebra.smul_def c _).symm]
  have h := capElt_last_congr (c • (algebraMap k T (r s) * a)) s v
    (y := KLRAlgebra.eSum _ (endSet ν ν₀)) (y' := 1) (by rw [eSum_end_mul_eSum_endSet, mul_one]) b
  rwa [one_mul] at h

theorem sum_capElt_prefix_e (t : Seq (stendhalWeight ℓ ν)) (a : T) (b : Rp) :
    Σc a (KLRAlgebra.e t) b = Σt a (KLRAlgebra.e t) b := by
  rw [prefixMapKLR_e, Finset.sum_eq_single t (fun s _ hs => capElt_last_eSum_ne _ hs v b)
    (by simp), Finset.sum_eq_single t (fun s _ hs => ?_) (by simp), capElt_idem]
  · exact (capElt_eq_eSum_mul _ t (Fin.last m) v b).symm
  · rw [← capElt_idem _ s, mul_assoc, ← map_mul, KLRAlgebra.e_mul_e]
    simp only [Ne.symm hs, ↓reduceIte, map_zero, mul_zero, capElt_zero_left]

theorem sum_capElt_prefix_x (b' : Fin m) (a : T) (b : Rp) :
    Σc a (KLRAlgebra.x b') b = Σt a (KLRAlgebra.x b') b := by
  refine Finset.sum_congr rfl fun s _ => ?_
  have hd : dotPos (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) (Fin.last m) b' =
      ⟨b'.val, lt_M_of_lt b'.2⟩ := Fin.ext (by rw [dotPos_val]; simp [b'.2])
  rw [prefixMapKLR_x, capElt_dot, hd]
  refine capElt_last_congr _ s v ?_ b
  have hc1 := (commute_x_eSum (Q' := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
    ⟨b'.val, lt_M_of_lt b'.2⟩ (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl)).eq
  rw [← mul_assoc, ← hc1, mul_assoc, eSum_end_mul_eSum_endSet, hc1]

theorem eSum_end_mul_ψ (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m) :
    (E s * KLRAlgebra.ψ p : Rp) = KLRAlgebra.ψ p * E (sadj m p • s) := by
  have h := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := ℓ) (hj := le_rfl) (ν₀ := ν₀)
    (sadj m p • s) (le_refl m) (p := p) (Or.inl hp)
  rw [crossPos_end hp, sadj_smul_sadj_smul] at h
  exact h.symm

theorem sum_capElt_prefix_ψ
    (hr : ∀ (p : ℕ) (s : Seq (stendhalWeight ℓ ν)), p + 1 < m → r (sadj m p • s) = r s)
    (p : ℕ) (a : T) (b : Rp) :
    Σc a (KLRAlgebra.ψ p) b = Σt a (KLRAlgebra.ψ p) b := by
  by_cases hp : p + 1 < m
  · have hL : ∀ s : Seq (stendhalWeight ℓ ν),
        (capElt (algebraMap k T (r s) * a) s (Fin.last m) v
          (prefixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.ψ p) * b) : K) =
        capElt (algebraMap k T (r s) * a) s (Fin.last m) v (KLRAlgebra.ψ p * b) := by
      intro s
      rw [prefixMapKLR_ψ _ _ _ hp]
      refine capElt_last_congr _ s v ?_ b
      rw [← mul_assoc, eSum_end_mul_ψ s hp, mul_assoc, eSum_end_mul_eSum_endSet]
    have hR : ∀ s : Seq (stendhalWeight ℓ ν),
        (capElt (algebraMap k T (r s) * a * topMap k Q Λ ν (KLRAlgebra.ψ p)) s (Fin.last m) v b :
          K) = capElt (algebraMap k T (r (sadj m p • s)) * a) (sadj m p • s) (Fin.last m) v
            (KLRAlgebra.ψ p * b) := by
      intro s
      have h := capElt_cross (algebraMap k T (r s) * a) s (Fin.last m) v p (Or.inl hp) b
      have hc : crossPos (Fin.last m).val N p = p := crossPos_end hp
      rw [hc] at h
      rw [h, hr p s hp]
    rw [Finset.sum_congr rfl fun s _ => hL s, Finset.sum_congr rfl fun s _ => hR s]
    exact (Equiv.sum_comp (MulAction.toPerm (sadj m p)) (fun s =>
      (capElt (algebraMap k T (r s) * a) s (Fin.last m) v (KLRAlgebra.ψ p * b) : K))).symm
  · have h0 : (KLRAlgebra.ψ p : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) = 0 :=
      KLRAlgebra.ψ_eq_zero p (by omega)
    simp only [h0, prefixMapKLR_zero, zero_mul, capElt_zero_right, map_zero, mul_zero,
      capElt_zero_left]

/-- **Diagrams of `λ` placed left of the maximum at the right end pass through the cap
generators**, summed over the top loadings with weights invariant under the symmetric group. -/
theorem sum_capElt_prefixMapKLR
    (hr : ∀ (p : ℕ) (s : Seq (stendhalWeight ℓ ν)), p + 1 < m → r (sadj m p • s) = r s)
    (w : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    ∀ (a : T) (b : Rp), Σc a w b = Σt a w b := by
  induction w using KLRAlgebra.klr_induction with
  | hadd u u' hu hu' =>
    intro a b
    simp only [prefixMapKLR_add, add_mul, capElt_add_right, Finset.sum_add_distrib, hu a b,
      hu' a b, map_add, mul_add, capElt_add_left]
  | hmul u u' hu hu' =>
    intro a b
    rw [prefixMapKLR_mul, mul_assoc, hu a]
    have h := hu' (a * topMap k Q Λ ν u) b
    simp only [mul_assoc] at h ⊢
    rw [h, map_mul]
  | hr c => exact sum_capElt_prefix_algebraMap r v c
  | he t => exact sum_capElt_prefix_e r v t
  | hx b' => exact sum_capElt_prefix_x r v b'
  | hψ p => exact sum_capElt_prefix_ψ r v hr p

end Prefix


section Inverse

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {ν : Multiset I} (ν₀ : Multiset I)
  (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
    (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl)
local notation "bot" => botMap k Q Λ Λc ℓ le_rfl ν ν₀
local notation "K" => CapTilde k Q Λ Λc ℓ le_rfl ν ν₀ L
local notation "Ev" => Env k Q Λ Λc ℓ le_rfl ν ν₀

/-- The cap generator with the maximum at the right end. -/
def lastGen (s : Seq (stendhalWeight ℓ ν)) (v : L) : K := capElt 1 s (Fin.last m) v 1

theorem smul_lastGen_eq_capElt (a : T) (s : Seq (stendhalWeight ℓ ν)) (v : L) (b : Rp) :
    Env.mk a (bot b) • lastGen Q Λ Λc ν₀ L s v = capElt a s (Fin.last m) v b := by
  rw [lastGen, smul_capElt, mul_one, one_mul]

theorem lastGen_eq (s : Seq (stendhalWeight ℓ ν)) (v : L) :
    lastGen Q Λ Λc ν₀ L s v = Env.mk 1 (bot (E s)) • lastGen Q Λ Λc ν₀ L s v := by
  rw [smul_lastGen_eq_capElt, lastGen, capElt_eq_eSum_mul, mul_one]
  rfl

theorem smul_lastGen_eSum (a : T) (Y : Tp) (s : Seq (stendhalWeight ℓ ν)) (v : L) :
    Env.mk a Y • lastGen Q Λ Λc ν₀ L s v = Env.mk a (bot (E s) * Y) • lastGen Q Λ Λc ν₀ L s v := by
  conv_lhs => rw [lastGen_eq]
  rw [smul_smul, Env.mk_mul_mk, mul_one]

theorem smul_lastGen_congr (a : T) {Y Y' : Tp} (s : Seq (stendhalWeight ℓ ν)) (v : L)
    (h : bot (E s) * Y = bot (E s) * Y') :
    Env.mk a Y • lastGen Q Λ Λc ν₀ L s v = Env.mk a Y' • lastGen Q Λ Λc ν₀ L s v := by
  rw [smul_lastGen_eSum, h, ← smul_lastGen_eSum]

theorem lastGen_add (s : Seq (stendhalWeight ℓ ν)) (v w : L) :
    lastGen Q Λ Λc ν₀ L s (v + w) = lastGen Q Λ Λc ν₀ L s v + lastGen Q Λ Λc ν₀ L s w :=
  capElt_add_mid _ _ _ _ _ _

theorem lastGen_box (s : Seq (stendhalWeight ℓ ν)) (v : L) (x : Rc) :
    lastGen Q Λ Λc ν₀ L s (op (cupMap k Q Λc ν₀ x) • v) =
      Env.mk 1 (bot (ι s m le_rfl x)) • lastGen Q Λ Λc ν₀ L s v := by
  rw [smul_lastGen_eq_capElt, lastGen, capElt_box, mul_one]
  rfl

theorem lastGen_eq_zero_of_top {s : Seq (stendhalWeight ℓ ν)} (hs : ¬ IsRedOrdered s) (v : L) :
    lastGen Q Λ Λc ν₀ L s v = 0 :=
  capElt_eq_zero_of_top _ hs _ _ _

/-! ### Diagrams at the maximum, seen from the right end -/

theorem endStendhal_one_eq_endBot :
    endStendhal Q Λ Λc ν ν₀ 1 = endBot Q Λ Λc ν ν₀ (redOrderedKLR k Q Λc ν₀) := by
  have h1 : endStendhal Q Λ Λc ν ν₀ 1 = allOrdersLift (redRelations_endBot Q Λ Λc)
      (StendhalAlgebraAllOrders.redOrderedIdem k Q Λc ν₀) := rfl
  rw [h1, endBot_eq_allOrdersLift, ofKLR_redOrderedKLR]

theorem eSum_end_mul_endBot (s : Seq (stendhalWeight ℓ ν)) (x : Rc) :
    bot (E s) * endBot Q Λ Λc ν ν₀ x = bot (ι s m le_rfl x) := by
  rw [endBot_apply, ← map_mul, insertMap_eq_prefix_mul_end, prefixMapKLR_e]

theorem eSum_end_mul_endStendhal_one (s : Seq (stendhalWeight ℓ ν)) :
    bot (E s) * endStendhal Q Λ Λc ν ν₀ 1 = bot (E s) := by
  rw [endStendhal_one_eq_endBot, eSum_end_mul_endBot, botMap_insertMap_redOrderedKLR]

theorem eSum_end_mul_prefixStendhal_one {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) :
    bot (E s) * prefixStendhal Q Λ Λc ν ν₀ 1 = bot (E s) := by
  classical
  rw [prefixStendhal_one, Finset.mul_sum, Finset.sum_eq_single s]
  · rw [← map_mul, (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) _).eq]
  · intro s' _ hs'
    rw [← map_mul, eSum_end_mul_eSum_end (Ne.symm hs'), map_zero]
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩) h

/-! ### The inverse map -/

variable {L} in
/-- The summand of the inverse map at the loading `s`. -/
def invTerm (Z : Tp) (s : Seq (stendhalWeight ℓ ν)) (v : L) : K :=
  Env.mk (algebraMap k T (Ring.inverse (capScalar Q ν₀ s m))) Z • lastGen Q Λ Λc ν₀ L s v

variable {L} in
/-- The inverse map on pure tensors: `Z ⊗ v ↦ ∑_s κ_s⁻¹ · cap(s, m, v) · Z`. -/
def invFun (Z : Tp) (v : L) : K := ∑ s, invTerm Q Λ Λc ν₀ Z s v

theorem invFun_add_left (Z Z' : Tp) (v : L) :
    invFun Q Λ Λc ν₀ (Z + Z') v = invFun Q Λ Λc ν₀ Z v + invFun Q Λ Λc ν₀ Z' v := by
  simp only [invFun, invTerm, Env.mk_add_right, add_smul, Finset.sum_add_distrib]

theorem invFun_add_right (Z : Tp) (v w : L) :
    invFun Q Λ Λc ν₀ Z (v + w) = invFun Q Λ Λc ν₀ Z v + invFun Q Λ Λc ν₀ Z w := by
  simp only [invFun, invTerm, lastGen_add, smul_add, Finset.sum_add_distrib]

theorem invFun_balanced (Z : Tp) (x : Rc) (v : L) :
    invFun Q Λ Λc ν₀ (endStendhal Q Λ Λc ν ν₀ (cupMap k Q Λc ν₀ x) * Z) v =
      invFun Q Λ Λc ν₀ Z (op (cupMap k Q Λc ν₀ x) • v) := by
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [invTerm, invTerm, lastGen_box, smul_smul, Env.mk_mul_mk, mul_one]
  refine smul_lastGen_congr Q Λ Λc ν₀ L _ s v ?_
  rw [endStendhal_cupMap', ← mul_assoc, ← mul_assoc, eSum_end_mul_endStendhal_one,
    eSum_end_mul_endBot, ← mul_assoc, ← map_mul, eSum_mul_insertMap]

theorem invFun_smul (B Z : Tp) (v : L) :
    invFun Q Λ Λc ν₀ (Z * B) v = (Env.mk (1 : T) B : Ev) • invFun Q Λ Λc ν₀ Z v := by
  rw [invFun, invFun, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [invTerm, invTerm, smul_smul, Env.mk_mul_mk, one_mul]

/-- **Diagrams of `λ` placed left of the maximum pass through the inverse map**. -/
theorem sum_invTerm_prefix (w : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) (v : L) :
    ∑ s : Seq (stendhalWeight ℓ ν), (Env.mk (algebraMap k T (Ring.inverse (capScalar Q ν₀ s m)))
        (endStendhal Q Λ Λc ν ν₀ 1 * prefixStendhal Q Λ Λc ν ν₀ (topMap k Q Λ ν w)) : Ev) •
        lastGen Q Λ Λc ν₀ L s v =
      ∑ s : Seq (stendhalWeight ℓ ν),
        (Env.mk (topMap k Q Λ ν w * algebraMap k T (Ring.inverse (capScalar Q ν₀ s m))) 1 : Ev) •
        lastGen Q Λ Λc ν₀ L s v := by
  have hr : ∀ (p : ℕ) (s : Seq (stendhalWeight ℓ ν)), p + 1 < m →
      Ring.inverse (capScalar Q ν₀ (sadj m p • s) m) = Ring.inverse (capScalar Q ν₀ s m) :=
    fun p s hp => by rw [capScalar_sadj Q s le_rfl (Or.inl hp)]
  have key := sum_capElt_prefixMapKLR (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀)
    (fun s => Ring.inverse (capScalar Q ν₀ s m)) v hr w 1 1
  simp only [mul_one] at key
  have h1 : ∀ s : Seq (stendhalWeight ℓ ν),
      (Env.mk (algebraMap k T (Ring.inverse (capScalar Q ν₀ s m)))
        (endStendhal Q Λ Λc ν ν₀ 1 * prefixStendhal Q Λ Λc ν ν₀ (topMap k Q Λ ν w)) : Ev) •
        lastGen Q Λ Λc ν₀ L s v =
      (Env.mk (1 : T) (prefixStendhal Q Λ Λc ν ν₀ 1) : Ev) •
        capElt (algebraMap k T (Ring.inverse (capScalar Q ν₀ s m))) s (Fin.last m) v
          (prefixMapKLR Q Λ Λc ν ν₀ w) := by
    intro s
    have hm : (Env.mk (algebraMap k T (Ring.inverse (capScalar Q ν₀ s m)))
        (endStendhal Q Λ Λc ν ν₀ 1 * prefixStendhal Q Λ Λc ν ν₀ (topMap k Q Λ ν w)) : Ev) =
        Env.mk 1 (prefixStendhal Q Λ Λc ν ν₀ 1) *
          Env.mk (algebraMap k T (Ring.inverse (capScalar Q ν₀ s m)))
            (endStendhal Q Λ Λc ν ν₀ 1 * prefixBot Q Λ Λc ν ν₀ w) := by
      rw [Env.mk_mul_mk, one_mul, prefixStendhal_topMap, mul_assoc]
    rw [hm, mul_smul, ← smul_lastGen_eq_capElt]
    congr 1
    refine smul_lastGen_congr Q Λ Λc ν₀ L _ s v ?_
    rw [← mul_assoc, eSum_end_mul_endStendhal_one, prefixBot_apply]
  have h2 : ∀ s : Seq (stendhalWeight ℓ ν),
      (Env.mk (1 : T) (prefixStendhal Q Λ Λc ν ν₀ 1) : Ev) •
        capElt (algebraMap k T (Ring.inverse (capScalar Q ν₀ s m)) * topMap k Q Λ ν w) s
          (Fin.last m) v 1 =
      (Env.mk (topMap k Q Λ ν w * algebraMap k T (Ring.inverse (capScalar Q ν₀ s m))) 1 : Ev) •
        lastGen Q Λ Λc ν₀ L s v := by
    intro s
    rw [← smul_lastGen_eq_capElt, smul_smul, Env.mk_mul_mk, one_mul,
      map_one (botMap k Q Λ Λc ℓ le_rfl ν ν₀), one_mul, ← Algebra.commutes]
    by_cases hs : IsRedOrdered s
    · refine smul_lastGen_congr Q Λ Λc ν₀ L _ s v ?_
      rw [eSum_end_mul_prefixStendhal_one Q Λ Λc ν₀ hs, mul_one]
    · rw [lastGen_eq_zero_of_top Q Λ Λc ν₀ L hs, smul_zero, smul_zero]
  rw [Finset.sum_congr rfl fun s _ => h1 s, ← Finset.smul_sum, key, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => h2 s

theorem topMap_surjective' : Function.Surjective (topMap k Q Λ ν) :=
  (orderProjection_surjective (Q := Q) (Λ := Λ) (ν := ν)).comp
    (StendhalAlgebraAllOrders.ofKLR_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν))

theorem invFun_left (a : T) (Z : Tp) (v : L) :
    invFun Q Λ Λc ν₀ ((endStendhal Q Λ Λc ν ν₀ 1 * prefixStendhal Q Λ Λc ν ν₀ a) * Z) v =
      (Env.mk a 1 : Ev) • invFun Q Λ Λc ν₀ Z v := by
  obtain ⟨w, rfl⟩ := topMap_surjective' Q Λ a
  have h1 : ∀ s : Seq (stendhalWeight ℓ ν), invTerm Q Λ Λc ν₀
      ((endStendhal Q Λ Λc ν ν₀ 1 * prefixStendhal Q Λ Λc ν ν₀ (topMap k Q Λ ν w)) * Z) s v =
      (Env.mk 1 Z : Ev) • ((Env.mk (algebraMap k T (Ring.inverse (capScalar Q ν₀ s m)))
        (endStendhal Q Λ Λc ν ν₀ 1 * prefixStendhal Q Λ Λc ν ν₀ (topMap k Q Λ ν w)) : Ev) •
        lastGen Q Λ Λc ν₀ L s v) := by
    intro s
    rw [invTerm, smul_smul, Env.mk_mul_mk, one_mul]
  rw [invFun, Finset.sum_congr rfl fun s _ => h1 s, ← Finset.smul_sum, sum_invTerm_prefix,
    invFun, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [invTerm, smul_smul, smul_smul, Env.mk_mul_mk, Env.mk_mul_mk, one_mul, one_mul, mul_one]

/-- **The inverse of the map to the model**, as an additive map: `Z ⊗ v ↦ ∑_s κ_s⁻¹ ·
cap(s, m, v) · Z`. -/
def modelToCapAdd : EndModel Q Λ Λc ν ν₀ L →+ K :=
  Ind.liftAdd (fun z v => invFun Q Λ Λc ν₀ z.1.unop v)
    (fun z z' v => invFun_add_left Q Λ Λc ν₀ L _ _ v)
    (fun z v v' => invFun_add_right Q Λ Λc ν₀ L _ v v')
    (fun z a v => by
      obtain ⟨x, hx⟩ := cupMap_surjective (Q := Q) (Λc := Λc) (ν₀ := ν₀) a.unop
      change invFun Q Λ Λc ν₀ (endStendhal Q Λ Λc ν ν₀ a.unop * z.1.unop) v = _
      rw [← hx, invFun_balanced, hx, op_unop])

theorem modelToCapAdd_tmul (z : Corner (endOp Q Λ Λc ν ν₀)) (v : L) :
    modelToCapAdd Q Λ Λc ν₀ L (Ind.tmul z v) = invFun Q Λ Λc ν₀ z.1.unop v := rfl

theorem modelToCapAdd_op_smul (b : Tp) (y : EndModel Q Λ Λc ν ν₀ L) :
    modelToCapAdd Q Λ Λc ν₀ L ((op b : Tpᵐᵒᵖ) • y) =
      (Env.mk 1 b : Ev) • modelToCapAdd Q Λ Λc ν₀ L y := by
  induction y using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', smul_add]
  | tmul z v =>
    rw [Ind.smul_tmul, modelToCapAdd_tmul, modelToCapAdd_tmul]
    exact invFun_smul Q Λ Λc ν₀ L b z.1.unop v

theorem modelToCapAdd_leftAct (a : T) (y : EndModel Q Λ Λc ν ν₀ L) :
    modelToCapAdd Q Λ Λc ν₀ L (leftAct Q Λ Λc ν ν₀ L a y) =
      (Env.mk a 1 : Ev) • modelToCapAdd Q Λ Λc ν₀ L y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy', smul_add]
  | tmul z v =>
    rw [leftAct_tmul, modelToCapAdd_tmul, modelToCapAdd_tmul]
    exact invFun_left Q Λ Λc ν₀ L a z.1.unop v

theorem modelToCapAdd_envMk (a : T) (b : Tp) (y : EndModel Q Λ Λc ν ν₀ L) :
    modelToCapAdd Q Λ Λc ν₀ L ((Env.mk a b : Ev) • y) =
      (Env.mk a b : Ev) • modelToCapAdd Q Λ Λc ν₀ L y := by
  rw [envMk_smul, modelToCapAdd_leftAct, modelToCapAdd_op_smul, smul_smul, Env.mk_mul_mk,
    mul_one, mul_one]

theorem modelToCapAdd_smul (r : Ev) (y : EndModel Q Λ Λc ν ν₀ L) :
    modelToCapAdd Q Λ Λc ν₀ L (r • y) = r • modelToCapAdd Q Λ Λc ν₀ L y := by
  induction r using TensorProduct.inductionOn with
  | tmul a b => exact modelToCapAdd_envMk Q Λ Λc ν₀ L a b.unop y
  | add r r' hr hr' =>
    have h := add_smul (show Ev from r) (show Ev from r') y
    have h' := add_smul (show Ev from r) (show Ev from r') (modelToCapAdd Q Λ Λc ν₀ L y)
    exact (congrArg _ h).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) hr hr').trans h'.symm))

/-- **The inverse of the map to the model** (Webster, arXiv:1309.3796v3, proof of Lemma 7.17,
`j = ℓ`), as a map of bimodules. -/
def modelToCap : EndModel Q Λ Λc ν ν₀ L →ₗ[Ev] K where
  toFun := modelToCapAdd Q Λ Λc ν₀ L
  map_add' := map_add _
  map_smul' := modelToCapAdd_smul Q Λ Λc ν₀ L

theorem modelToCap_apply (y : EndModel Q Λ Λc ν ν₀ L) :
    modelToCap Q Λ Λc ν₀ L y = modelToCapAdd Q Λ Λc ν₀ L y := rfl

/-! ### The scalars -/

theorem isUnit_labelScalar (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (c : I ⊕ Fin ℓ) :
    IsUnit (labelScalar Q ν₀ c) := by
  cases c with
  | inl i => exact hκ i
  | inr _ => exact isUnit_one

theorem isUnit_capScalar (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (s : Seq (stendhalWeight ℓ ν))
    (n : ℕ) : IsUnit (capScalar Q ν₀ s n) := by
  refine IsUnit.prod_iff.2 fun r _ => ?_
  by_cases h : r < m
  · simp only [h, ↓reduceDIte]
    exact isUnit_labelScalar Q ν₀ hκ _
  · simp only [h, ↓reduceDIte, isUnit_one]

/-- **(max1) along a passage**: a cap generator whose black strands right of the maximum pass
under it moves left, picking up the scalars of (max1). -/
theorem capElt_passU (a : T) (s : Seq (stendhalWeight ℓ ν)) (v : L) (b : Rp) :
    ∀ (d n : ℕ) (hnd : n + d ≤ m), (∀ (r : ℕ) (h : r < m), n ≤ r → r < n + d →
      ∃ i, s.lbl ⟨r, h⟩ = .inl i) →
    (capElt a s ⟨n + d, by omega⟩ v (passU Q Λ Λc ℓ le_rfl ν ν₀ n d * b) : K) =
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
      capElt_passU a s v (underRight N n * b) d (n + 1) (by omega)
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

/-! ### The two composites -/

theorem envMk_one_one : (Env.mk (1 : T) (1 : Tp) : Ev) = 1 := by
  unfold Env.mk
  rw [op_one]
  rfl

theorem capElt_one_one (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) :
    (capElt 1 s n v 1 : K) = Submodule.Quotient.mk (gen (s, n) v) := by
  rw [capElt, act, map_one, envMk_one_one, one_smul]

variable {Q Λ Λc ν₀ L} in
theorem capToModel_capElt
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) (a : T) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1))
    (v : L) (b : Rp) :
    capToModel Q Λ Λc L hL hP (capElt a s n v b) =
      (Env.mk a (bot b) : Ev) • capImage Q Λ Λc ν₀ L (s, n) v := by
  rw [capElt, act, Submodule.Quotient.mk_smul, map_smul, capToModel_mk]

theorem capBot_last (s : Seq (stendhalWeight ℓ ν)) (h : (Fin.last m).val ≤ m) :
    capBot Q Λ Λc ν₀ s (Fin.last m).val h = E s := by
  rw [capBot_congr Q Λ Λc s h le_rfl (Fin.val_last m), capBot, Nat.sub_self, passU_zero, mul_one]
  exact (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) _).eq

theorem sum_tmul_endGen (f : Seq (stendhalWeight ℓ ν) → Tp) (v : L) :
    ∑ s, (Ind.tmul (endGen Q Λ Λc ν ν₀ (f s)) v : EndModel Q Λ Λc ν ν₀ L) =
      Ind.tmul (endGen Q Λ Λc ν ν₀ (∑ s, f s)) v := by
  let φ : Tp →+ EndModel Q Λ Λc ν ν₀ L :=
    AddMonoidHom.mk' (fun Z => Ind.tmul (endGen Q Λ Λc ν ν₀ Z) v)
      (fun X Y => by rw [endGen_add, Ind.add_tmul])
  exact (map_sum φ f Finset.univ).symm

theorem endGen_unop (z : Corner (endOp Q Λ Λc ν ν₀)) : endGen Q Λ Λc ν ν₀ z.1.unop = z := by
  apply Subtype.ext
  rw [endGen_val]
  exact (z.2 : op (endStendhal Q Λ Λc ν ν₀ 1 * z.1.unop) = z.1)

theorem endIdem_mul_corner (z : Corner (endOp Q Λ Λc ν ν₀)) :
    endIdem Q Λ Λc ν ν₀ * z.1.unop = z.1.unop := by
  have hz' : endStendhal Q Λ Λc ν ν₀ 1 * z.1.unop = z.1.unop :=
    congrArg unop (z.2 : op (endStendhal Q Λ Λc ν ν₀ 1 * z.1.unop) = z.1)
  rw [← hz', ← mul_assoc, endStendhal_one_eq_endBot, endIdem_mul_endBot]

/-- **The map to the model after its inverse is the identity**, when the scalars of (max1) are
units. -/
theorem capToModel_modelToCap (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) (y : EndModel Q Λ Λc ν ν₀ L) :
    capToModel Q Λ Λc L hL hP (modelToCap Q Λ Λc ν₀ L y) = y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']
  | tmul z v =>
    rw [modelToCap_apply, modelToCapAdd_tmul, invFun, map_sum]
    have h1 : ∀ (Z : Tp) (s : Seq (stendhalWeight ℓ ν)),
        capToModel Q Λ Λc L hL hP (invTerm Q Λ Λc ν₀ Z s v) =
          Ind.tmul (endGen Q Λ Λc ν ν₀ (bot (E s) * Z)) v := by
      intro Z s
      have hc : Ring.inverse (capScalar Q ν₀ s m) * capScalar Q ν₀ s (Fin.last m) = 1 :=
        Ring.inverse_mul_cancel _ (isUnit_capScalar Q ν₀ hκ s m)
      rw [invTerm, map_smul, lastGen, capToModel_capElt, map_one (botMap k Q Λ Λc ℓ le_rfl ν ν₀),
        envMk_one_one, one_smul,
        envMk_smul, op_smul_capImage, leftAct_algebraMap, smul_smul, hc, one_smul, capBot_last]
    rw [Finset.sum_congr rfl fun s _ => h1 z.1.unop s, sum_tmul_endGen, ← Finset.sum_mul, ← map_sum,
      ← eSum_endSet, endIdem_mul_corner, endGen_unop]

theorem capScalar_mul_prod_Ico (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) :
    capScalar Q ν₀ s n * (∏ r ∈ Finset.Ico n (n + (m - n)),
      if h : r < m then labelScalar Q ν₀ (s.lbl ⟨r, h⟩) else 1) = capScalar Q ν₀ s m := by
  rw [Nat.add_sub_cancel' hn, capScalar, capScalar, Finset.prod_range_mul_prod_Ico _ hn]

theorem capElt_last_eSum (a : T) (s : Seq (stendhalWeight ℓ ν)) (v : L) (b : Rp) :
    (capElt a s (Fin.last m) v (E s * b) : K) = capElt a s (Fin.last m) v b :=
  (capElt_eq_eSum_mul a s _ v b).symm

/-- **The inverse after the map to the model is the identity on the generators**, when the
scalars of (max1) are units. -/
theorem modelToCap_capToModel_gen (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) :
    modelToCap Q Λ Λc ν₀ L (capToModel Q Λ Λc L hL hP (Submodule.Quotient.mk (gen (s, n) v))) =
      Submodule.Quotient.mk (gen (s, n) v) := by
  have hn : n.val ≤ m := Nat.lt_succ_iff.1 n.2
  by_cases hred : ∃ (a : Fin m) (r : Fin ℓ), n.val ≤ a.val ∧ s.lbl a = .inr r
  · obtain ⟨a, r, ha, hr⟩ := hred
    have h0 : (Submodule.Quotient.mk (gen (s, n) v) : K) = 0 := by
      rw [← capElt_one_one]
      exact capElt_eq_zero_of_bottom _ _ _ _ _ fun t =>
        not_isRedOrdered_of_red_right s hn t a ha hr r.2
    rw [h0, map_zero, map_zero]
  have hb : ∀ (r : ℕ) (h : r < m), n.val ≤ r → r < n.val + (m - n.val) →
      ∃ i, s.lbl ⟨r, h⟩ = .inl i := by
    intro r h h1 _
    cases hl : s.lbl ⟨r, h⟩ with
    | inl i => exact ⟨i, rfl⟩
    | inr r' => exact absurd ⟨⟨r, h⟩, r', h1, hl⟩ hred
  rw [capToModel_mk, capImage_mk, algebraMap_smul, MulOpposite.algebraMap_apply, modelToCap_apply,
    modelToCapAdd_op_smul, modelToCapAdd_tmul, endGen_val, unop_op, invFun,
    Finset.sum_eq_single s]
  · rw [invTerm]
    rw [smul_lastGen_congr Q Λ Λc ν₀ L _ s v (Y' := bot (capBot Q Λ Λc ν₀ s n hn))
      (by rw [← mul_assoc, eSum_end_mul_endStendhal_one]),
      smul_lastGen_eq_capElt, capBot, mul_assoc, capElt_last_eSum]
    have hf : Fin.last m = ⟨n.val + (m - n.val), by omega⟩ :=
      Fin.ext (by simp only [Fin.val_last]; omega)
    rw [hf, capElt_passU Q Λ Λc ν₀ L _ s v _ (m - n.val) n.val (by omega) hb]
    have he := capElt_eq_eSum_mul (L := L) (Q := Q) (Λc := Λc) (ν₀ := ν₀) (j := ℓ) (hj := le_rfl)
      (algebraMap k T (Ring.inverse (capScalar Q ν₀ s m)) *
      algebraMap k T (∏ r ∈ Finset.Ico n.val (n.val + (m - n.val)),
        if h : r < m then labelScalar Q ν₀ (s.lbl ⟨r, h⟩) else 1)) s n v 1
    rw [mul_one] at he
    rw [← he, ← AlgHom.commutes (botMap k Q Λ Λc ℓ le_rfl ν ν₀), smul_capElt, one_mul, one_mul,
      Algebra.algebraMap_eq_smul_one (A := Rp) (capScalar Q ν₀ s n), capElt_smul_right]
    have hA : capScalar Q ν₀ s n • (algebraMap k T (Ring.inverse (capScalar Q ν₀ s m)) *
        algebraMap k T (∏ r ∈ Finset.Ico n.val (n.val + (m - n.val)),
          if h : r < m then labelScalar Q ν₀ (s.lbl ⟨r, h⟩) else 1)) = 1 := by
      rw [Algebra.smul_def, ← map_mul, ← map_mul, mul_left_comm, capScalar_mul_prod_Ico Q ν₀ s hn,
        Ring.inverse_mul_cancel _ (isUnit_capScalar Q ν₀ hκ s m), map_one]
    rw [hA, capElt_one_one]
  · intro s' _ hs'
    rw [invTerm, smul_lastGen_congr Q Λ Λc ν₀ L _ s' v (Y' := 0), Env.mk_zero_right, zero_smul]
    rw [← mul_assoc, eSum_end_mul_endStendhal_one, mul_zero, capBot, ← map_mul, ← mul_assoc,
      ← mul_assoc, eSum_end_mul_eSum_end hs', zero_mul, zero_mul, map_zero]
  · intro h
    exact absurd (Finset.mem_univ s) h

theorem modelToCap_capToModel (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) :
    (modelToCap Q Λ Λc ν₀ L).comp (capToModel Q Λ Λc L hL hP) = (LinearMap.id : K →ₗ[Ev] K) := by
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext fun p r => ?_)
  rw [← Finsupp.smul_single_one, LinearMap.comp_apply, LinearMap.comp_apply, map_smul, map_smul,
    map_smul, LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply]
  exact congrArg (r • ·) (modelToCap_capToModel_gen Q Λ Λc ν₀ L hκ hL hP p.1.1 p.1.2 p.2)

/-- **Lemma 7.17, the right end** (Webster, arXiv:1309.3796v3, proof of Lemma 7.17, `j = ℓ`):
when the scalars of (max1) are units, `L` is supported on loadings with `μ` and `μ*` at the ends,
and the left pull-off identity holds, `K̃^{λ⁺}_λ` is isomorphic as a bimodule to the model
`L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}`. -/
def capModelEquiv (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) : K ≃ₗ[Ev] EndModel Q Λ Λc ν ν₀ L :=
  LinearEquiv.ofLinearMap (capToModel Q Λ Λc L hL hP) (modelToCap Q Λ Λc ν₀ L)
    (LinearMap.ext fun y => capToModel_modelToCap Q Λ Λc ν₀ L hκ hL hP y)
    (modelToCap_capToModel Q Λ Λc ν₀ L hκ hL hP)

end Inverse

end Categorification.Stendhal.CupCap
