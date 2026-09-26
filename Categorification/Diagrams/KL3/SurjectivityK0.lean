/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SurjectivityTop
import Categorification.Diagrams.KL3.KaroubiK0
import Categorification.KLR.KL2.Prop320KL2
import Categorification.KLR.BarK0

/-!
# The Grothendieck group hypothesis: idempotents of `R(ν) ⊗ R(ν')` give classes in `γ(_𝒜 U̇)`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.8.4, end
of the proof of Theorem 1.1:

> It now suffices to show that `[E_{ν,-ν'} 1_λ, e_{r,r'}]` belongs to image of `γ`. But the
> idempotent `e_{r,r'}` is the image of `e_r ⊗ e_{r'}` in `R(ν) ⊗ R(ν') ⊗ Π_λ`, and the
> Grothendieck group of the latter is isomorphic to `_𝒜f(ν) ⊗ _𝒜f(ν')`. Therefore
> `[E_{ν,-ν'}, e_{r,r'}]` is in the image of `_𝒜f(ν) ⊗ _𝒜f(ν')` under the composition map
> `x ⊗ y ↦ x⁺ y⁻ 1_λ` […]

We prove `TobjHyp` (`tobjHyp`): for every degree-zero idempotent `g` of `R(ν) ⊗ R(ν')` in the
corner of `(i, j)`, the class of `(E_{+i} E_{-j} 1_λ {t}, α(g))` lies in the image of `γ`.

* By `Categorification.Diagrams.KL3.KaroubiK0`, `[(E_{+i} E_{-j} 1_λ, α(g))] = Φ[(R(ν) ⊗ R(ν')) g]`
  for the (bar-semilinear) additive map `Φ = transferK0 (alphaDataR …)`.
* `K₀(R(ν) ⊗ R(ν'))` is spanned by the classes `[P_d ⊠ P_{d'}]` of external tensor products of
  divided-power projectives, by KL II Theorem 8 (`k0B2_mem_span_projDiv2`) and
  `K₀(R(ν) ⊗ R(ν')) ≅ K₀(R(ν)) ⊗ K₀(R(ν'))` (`k0TensorEquiv`, KL I §3.1); hence
  `Φ(K₀(R(ν) ⊗ R(ν'))) ⊆ γ(_𝒜 U̇)` (`transferK0_mem_gammaImg`).
* `Φ[P_d ⊠ P_{d'}] = [E_{+d} E_{-d'} 1_λ]` (`transferK0_extTensor_projDiv2`): both sides become
  the class of `E_{+i} E_{-j} 1_λ` (`i`, `j` the expanded sequences) after multiplication by the
  bar-invariant quantum factorial `∏ [a_r]_{i_r}!`, and `K₀(U̇)` has no torsion.

## Main results

* `tobjHyp`: the hypothesis `TobjHyp` of `Categorification.Diagrams.KL3.SurjectivityTop` holds
  (simply-laced Cartan data, `I` finite, `k` a field).
* `gammaUA'_surjective_of_sortedSpan'`: **KL III Theorem 1.1** (`γ` is surjective) conditional
  only on the spanning hypothesis `SortedSpan`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation
  GradedBicat KrullSchmidtCat KLR Graded LaurentPolynomial
open scoped TensorProduct

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

open KLR.Diagram (word)

/-! ## Quantum factorials -/

section QFac

theorem qfact_tUnit_eq_qfac (h : ℤ) (n : ℕ) :
    QuantumGroup.qfact (KLR.KL2.tUnit h) n = qfac h n := by
  unfold QuantumGroup.qfact qfac
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [QuantumGroup.qint_eq_sum]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [KLR.KL2.val_tUnit_zpow]
  congr 1
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

/-- The dpss `(+d)(-d')` of a pair of divided-power expressions. -/
def dpPair (d d' : List (I × ℕ)) : List (Bool × I × ℕ) :=
  d.map (fun q => (true, q.1, q.2)) ++ d'.map (fun q => (false, q.1, q.2))

theorem dpWord_map (b : Bool) (d : List (I × ℕ)) :
    dpWord (d.map fun q => (b, q.1, q.2)) = (KLR.KLRAlgebra.expandDiv d).map fun i => (b, i) := by
  induction d with
  | nil => rfl
  | cons q d ih =>
    rw [List.map_cons, dpWord_cons, ih]
    simp [dpLetters, KLR.KLRAlgebra.expandDiv, List.map_replicate]

theorem dpWord_dpPair (d d' : List (I × ℕ)) :
    dpWord (dpPair d d') = ups (KLR.KLRAlgebra.expandDiv d) ++ dns (KLR.KLRAlgebra.expandDiv d') := by
  rw [dpPair, dpWord_append, dpWord_map, dpWord_map]

theorem dpFac_dpPair (d d' : List (I × ℕ)) :
    dpFac (C := C) (dpPair d d') = KLR.KL2.divQFact2 C d * KLR.KL2.divQFact2 C d' := by
  simp only [dpPair, dpFac, List.map_append, List.prod_append, List.map_map, KLR.KL2.divQFact2]
  congr 1 <;> {
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp_apply]
    rw [qfact_tUnit_eq_qfac]
    rfl }

theorem dpFac_ne_zero (dd : List (Bool × I × ℕ)) : dpFac (C := C) dd ≠ 0 := by
  intro h
  have := lpToQ_dpFac_ne_zero (C := C) dd
  rw [h, map_zero] at this
  exact this rfl

end QFac

theorem word_seqOfList' {ν : Multiset I} (l : List I) (h : (l : Multiset I) = ν) :
    word (KLR.KLRAlgebra.Seq.ofList l h) = l := by
  show List.ofFn _ = l
  rw [List.ofFn_congr (by rw [← h, Multiset.coe_card] : Multiset.card ν = l.length)]
  exact List.ofFn_get l

/-! ## The corner idempotent `e_i ⊗ e_j` -/

section Corner

variable [DecidableEq I] (lam ρ : X) {ν ν' : Multiset I} (hρ : rhoS RD lam ν ν' = ρ)

variable (k) in
/-- The corner idempotent `e_i ⊗ e_j`, as a degree-zero idempotent of its own corner. -/
def cornerE (p : KLR.Seq ν × KLR.Seq ν') : TCorner (TG C k ν ν') (fun p : KLR.Seq ν × KLR.Seq ν' =>
      (KLRAlgebra.e p.1 ⊗ₜ KLRAlgebra.e p.2 : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν')) p where
  f := KLRAlgebra.e p.1 ⊗ₜ KLRAlgebra.e p.2
  deg0 := e₀_mem p.1 p.2
  idem := by rw [Algebra.TensorProduct.tmul_mul_tmul, KLRAlgebra.e_mul_self, KLRAlgebra.e_mul_self]
  left := by rw [Algebra.TensorProduct.tmul_mul_tmul, KLRAlgebra.e_mul_self, KLRAlgebra.e_mul_self]

/-- `(E_{+i} E_{-j} 1_λ, α(e_i ⊗ e_j)) = E_{+i} E_{-j} 1_λ`. -/
theorem cl_tobj_cornerE (p : KLR.Seq ν × KLR.Seq ν') :
    K0U.cl (tobj (alphaDataR RD k lam ν ν' ρ hρ) (cornerE k p) 0) =
      eC RD k ρ lam (ups (word p.1) ++ dns (word p.2)) ((wt_ZS RD lam ν ν' p).trans hρ) := by
  have h : (alphaDataR RD k lam ν ν' ρ hρ).α (cornerE k p).f p p = 𝟙 _ := by
    show alpha RD k lam ν ν' (KLRAlgebra.e p.1 ⊗ₜ KLRAlgebra.e p.2) p p = _
    rw [alpha_e]
    exact KLR.Diagram.MatEnd.single_apply_self _ _ _
  show K0U.cl (idemObj _ _ _ _ _) = K0U.cl (objOf _ 0)
  rw [idemObj_congr h _ (h ▸ (alphaDataR RD k lam ν ν' ρ hρ).α_mem (cornerE k p).deg0 p p) _
    (by rw [Category.comp_id]), idemObj_id]

end Corner

/-! ## The transfer of `[P_d ⊠ P_{d'}]` -/

section Transfer

variable [DecidableEq I] [Finite I] (hSL : SimplyLaced C) (lam ρ : X) {ν ν' : Multiset I}
  (hρ : rhoS RD lam ν ν' = ρ)

include hSL in
/-- **`Φ[P_d ⊠ P_{d'}] = [E_{+d} E_{-d'} 1_λ]`**: the transfer of the external tensor product of
the divided-power projectives `P_d = R(ν) ψ(1_{d̂}) {-⟨d⟩}` is the class of the product of
divided powers `E^{(a_1)}_{+i_1} ⋯ E^{(b_1)}_{-j_1} ⋯ 1_λ`. -/
theorem transferK0_extTensor_projDiv2 (d d' : List (I × ℕ))
    (h : (KLR.KLRAlgebra.expandDiv d : Multiset I) = ν)
    (h' : (KLR.KLRAlgebra.expandDiv d' : Multiset I) = ν')
    (hw : wt RD lam (dpWord (dpPair d d')) = ρ) :
    transferK0 (alphaDataR RD k lam ν ν' ρ hρ)
      (K0.extTensor _ _ (K0.of (KLR.KL2.projDiv2 k C d h)) (K0.of (KLR.KL2.projDiv2 k C d' h'))) =
      dpC RD k (dpPair d d') lam ρ hw := by
  set t := KLR.KLRAlgebra.Seq.ofList (KLR.KLRAlgebra.expandDiv d) h
  set t' := KLR.KLRAlgebra.Seq.ofList (KLR.KLRAlgebra.expandDiv d') h'
  set D := alphaDataR RD k lam ν ν' ρ hρ
  set c := dpFac (C := C) (dpPair d d')
  -- the transfer of `[P_t ⊠ P_{t'}]`
  have h1 : transferK0 D (K0.extTensor _ _ (K0.of (KLR.KL2.projSeq2 k C t))
      (K0.of (KLR.KL2.projSeq2 k C t'))) = c • dpC RD k (dpPair d d') lam ρ hw := by
    rw [KLR.KL2.projSeq2, KLR.KL2.projSeq2, K0.extTensor_ofIdempotent]
    have e1 := transferK0_ofIdempotent D (cornerE k (t, t'))
    refine (congrArg (transferK0 D) (ofIdempotent_congr rfl _ _ _ _)).trans (e1.trans ?_)
    rw [cl_tobj_cornerE, show c • dpC RD k (dpPair d d') lam ρ hw =
      eC RD k ρ lam (dpWord (dpPair d d')) hw from (eC_dpWord _ _ _ hw).symm]
    exact congrArg K0U.cl (nfObj_congr_list (RD := RD) (k := k)
      (l := ups (word t) ++ dns (word t')) (l' := dpWord (dpPair d d')) (by
      rw [dpWord_dpPair, word_seqOfList', word_seqOfList']) _ hw 0)
  rw [KLR.KL2.K0_projSeq2_expandDiv, KLR.KL2.K0_projSeq2_expandDiv, LinearMap.map_smul₂,
    LinearMap.map_smul, smul_smul, transferK0_smul, ← dpFac_dpPair (C := C), invert_dpFac] at h1
  refine sub_eq_zero.1 (K0Kar_torsionFree hSL ρ lam c
    (mem_nonZeroDivisors_of_ne_zero (dpFac_ne_zero _)) _ ?_)
  rw [smul_sub, sub_eq_zero]
  exact h1

include hSL in
/-- **Every class in `K₀(R(ν) ⊗ R(ν'))` is transferred into the image of `γ`**: `K₀(R(ν) ⊗ R(ν'))`
is spanned by the classes `[P_d ⊠ P_{d'}]` (KL II Theorem 8 and KL I §3.1). -/
theorem transferK0_mem_gammaImg (y : K0 (TG C k ν ν')) :
    transferK0 (alphaDataR RD k lam ν ν' ρ hρ) y ∈ gammaImg RD k lam ρ := by
  set D := alphaDataR RD k lam ν ν' ρ hρ
  let S : Submodule (LaurentPolynomial ℤ) (K0 (TG C k ν ν')) :=
    { carrier := {y | transferK0 D y ∈ gammaImg RD k lam ρ}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *; exact add_mem ha hb
      zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact zero_mem _
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, transferK0_smul] at *; exact Submodule.smul_mem _ _ ha }
  have hS : ∀ y, y ∈ S ↔ transferK0 D y ∈ gammaImg RD k lam ρ := fun y => Iff.rfl
  have hspan : ∀ μ : Multiset I, Submodule.span (LaurentPolynomial ℤ)
      {z | ∃ (d : List (I × ℕ)) (h : (KLR.KLRAlgebra.expandDiv d : Multiset I) = μ),
        z = K0.of (KLR.KL2.projDiv2 k C d h)} = ⊤ := by
    intro μ
    refine eq_top_iff.2 ?_
    rw [← (KLR.KL2Gamma.k0B2 k C μ).span_eq, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact KLR.KL2Gamma.k0B2_mem_span_projDiv2 k C μ b
  have hext : ∀ x x', K0.extTensor _ _ x x' ∈ S := by
    intro x x'
    have hx : x ∈ Submodule.span (LaurentPolynomial ℤ) _ := (hspan ν).symm ▸ Submodule.mem_top
    have hx' : x' ∈ Submodule.span (LaurentPolynomial ℤ) _ := (hspan ν').symm ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, h, rfl⟩ := hx
      induction hx' using Submodule.span_induction with
      | mem x' hx' =>
        obtain ⟨d', h', rfl⟩ := hx'
        have hw := (wt_ZS RD lam ν ν' (KLR.KLRAlgebra.Seq.ofList _ h,
          KLR.KLRAlgebra.Seq.ofList _ h')).trans hρ
        rw [word_seqOfList', word_seqOfList', ← dpWord_dpPair] at hw
        rw [hS, transferK0_extTensor_projDiv2 hSL lam ρ hρ d d' h h' hw]
        exact dpC_mem_gammaImg _ hw
      | zero => rw [map_zero]; exact S.zero_mem
      | add a b _ _ ha hb => rw [map_add]; exact S.add_mem ha hb
      | smul c a _ ha => rw [LinearMap.map_smul]; exact S.smul_mem c ha
    | zero => rw [map_zero, LinearMap.zero_apply]; exact S.zero_mem
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact S.add_mem ha hb
    | smul c a _ ha => rw [LinearMap.map_smul₂]; exact S.smul_mem c ha
  obtain ⟨z, rfl⟩ := ((klGradingDatum2 k C).k0TensorEquiv
    (klQ2_eq_klP2 (o := KL1.stdOrient) KL2.stdOrient_spec) (fun a b hab => klP2_ne_zero a b hab)
    (KLR.KL2Gamma.klGradingDatum2_degX_pos k C) ν ν').surjective y
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact S.zero_mem
  | tmul x x' => rw [GradingDatum.k0TensorEquiv_tmul]; exact hext x x'
  | add a b ha hb => rw [map_add]; exact S.add_mem ha hb

end Transfer

/-! ## The Grothendieck group hypothesis and surjectivity -/

section Main

variable [DecidableEq I] [Finite I] (hSL : SimplyLaced C)

include hSL in
/-- **The Grothendieck group hypothesis `TobjHyp` holds** (KL III, end of the proof of
Theorem 1.1): the class of `(E_{+i} E_{-j} 1_λ {t}, α(g))` lies in the image of `γ` for every
degree-zero idempotent `g` of `R(ν) ⊗ R(ν')` in the corner of `(i, j)`. -/
theorem tobjHyp : TobjHyp RD k := by
  intro lam ρ ν ν' hρ p F t
  have h1 := transferK0_mem_gammaImg hSL lam ρ hρ
    (K0.of (GProj.ofIdempotent F.f (show IsIdempotentElem F.f from F.idem) F.deg0))
  rw [transferK0_ofIdempotent] at h1
  show K0U.cl (idemObj _ t _ _ _) ∈ _
  rw [K0U.idemObj_shift]
  exact Submodule.smul_mem _ _ h1

/-- **KL III Theorem 1.1 (surjectivity of `γ : _𝒜 U̇ → K₀(U̇)`), conditional only on the spanning
hypothesis `SortedSpan`** (simply-laced Cartan data, `I` finite, `k` a field). -/
theorem gammaUA'_surjective_of_sortedSpan' (hspan : SortedSpan RD k) (lam ρ : X) :
    Function.Surjective (gammaUA' (RD := RD) (k := k) hSL lam ρ) :=
  gammaUA'_surjective_of_sortedSpan hSL hspan (tobjHyp hSL) lam ρ

end Main

end Categorification.KL3.Diagram
