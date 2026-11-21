/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumSpanning
import Categorification.KLR.CyclotomicAction.VacuumCurl

/-!
# The quotient by `I` at the vacuum (Webster, Prop. 3.25)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25. The comparison map `vacTheta` from the KLR algebra over `Ř^λ_λ` to the upward
2-endomorphisms of the words of `ν` at the region of `P_∅` sends the cyclotomic ideal, after the
flips `hflip` and `σ`, into the ideal `I` of 2-morphisms factoring through a downward strand next
to the vacuum (`vacThetaM_sigma_hflip_mem`): the universal cyclotomic polynomial in the dot on
the strand next to the vacuum is the cyclotomic relation coming from the right curl
(`vacThetaM_cycPoly_mem`, via `vacCurl_mem`). With upward spanning
(`exists_vacThetaM_sub_mem`), the kernel of the vacuum-entry homomorphism `vacRingHom` is exactly
the matrices with entries in `I` (`vacRingHom_eq_zero_iff`), and it is surjective
(`vacRingHom_surjective`), so the quotient by `I` is the opposite of the cyclotomic quotient
`Ř^λ(ν)` (`vacQuotientEquiv`).
-/

namespace Categorification.KLR.Diagram.DiagR
open CategoryTheory MatEnd
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν : Multiset I}

/-- Powers of a dot times an idempotent, as a single matrix entry. -/
theorem X_pow_mul_E (j : Seq ν) (a : Fin (Multiset.card ν)) (n : ℕ) :
    (X a : DiagR k Q ν) ^ n * E j = single j j (dotE k Q j a ^ n) := by
  induction n with
  | zero => rw [pow_zero, one_mul, pow_zero]; rfl
  | succ n ih => rw [pow_succ', mul_assoc, ih, X_mul_single, pow_succ', End.mul_def]
end Categorification.KLR.Diagram.DiagR

namespace Categorification.KLR.KLRAlgebra
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν : Multiset I}

/-- The horizontal flip fixes polynomials in a dot. -/
theorem hflip_aeval_x (a : Fin (Multiset.card ν)) (p : Polynomial k) :
    hflip (Polynomial.aeval (x a : KLRAlgebra k Q ν) p) = Polynomial.aeval (x a) p := by
  rw [hflip, ← Polynomial.aeval_algHom_apply]
  have : flipAlgHom k Q ν (x a) = MulOpposite.op (x a) := by
    apply MulOpposite.unop_injective; exact hflip_x (Q := Q) a
  rw [this]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, MulOpposite.unop_add, hp, hq]
  | monomial n c => simp [Polynomial.aeval_monomial, Algebra.commutes]

/-- Idempotents commute with polynomials in a dot. -/
theorem commute_e_aeval_x (i : Seq ν) (a : Fin (Multiset.card ν)) (p : Polynomial k) :
    Commute (e i : KLRAlgebra k Q ν) (Polynomial.aeval (x a) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    exact (Algebra.commute_algebraMap_right c _).mul_right (Commute.pow_right (x_mul_e a i).symm n)
end Categorification.KLR.KLRAlgebra

namespace Categorification.KLR.CyclotomicAction
open CategoryTheory TwoRep QuantumGroup KLRAlgebra StringDiagrams Diagrams.BicatInterp
open KL3.Diagram KLR.Diagram.MatEnd
universe u v w u₁
noncomputable section
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)
attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

/-- A power of the dot on the strand next to the vacuum, as an upward diagram. -/
theorem vacUpHom_x_pow_e {ν : Multiset I} (j : KLR.Seq ν) (a : Fin (Multiset.card ν))
    (ha : a.val + 1 = Multiset.card ν) (n : ℕ) :
    vacUpHom hQ RD Λ ν (x a ^ n * e j) = single j j
      (CL.dgC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (ups (KLR.Diagram.word j))
        (ups (KLR.Diagram.word j))
        (List.replicate n (ups ((KLR.Diagram.word j).take a), .dot (up (j.1 a)), []))) := by
  have hd : (KLR.Diagram.word j).drop (a + 1) = [] :=
    List.drop_eq_nil_of_le (by simp [ha])
  have hx : SChain (ups (KLR.Diagram.word j))
      [(ups ((KLR.Diagram.word j).take a), .dot (up (j.1 a)), [])] (ups (KLR.Diagram.word j)) := by
    have := sChain_upLD (StringDiagrams.Diagram.chain (KLR.Diagram.dotD j a))
    rw [KLR.Diagram.layers_dotD] at this
    simpa [upLD, upShape, hd] using this
  change matEndMap k (CL.upFunctorC (CL.presCL RD k (univScalars hQ RD))
    (CL.qCL (univScalars hQ RD)) (univScalars_klr hQ RD) (vacWt RD Λ)) _
    (KLR.Diagram.diagREquiv k (CL.qCL (univScalars hQ RD)) ν (x a ^ n * e j)) = _
  rw [map_mul, map_pow, KLR.Diagram.diagREquiv_x, KLR.Diagram.diagREquiv_e,
    KLR.Diagram.DiagR.X_pow_mul_E, matEndMap_single]
  congr 1
  refine Eq.trans ?_ (CL.dgEC_pow_single _ _ _ _ hx n)
  refine (map_pow (Functor.mapEnd (X := (KLR.Diagram.pres k (CL.qCL (univScalars hQ RD))).obj
    (KLR.Diagram.ob (KLR.Diagram.word j))) (CL.upFunctorC (CL.presCL RD k (univScalars hQ RD))
    (CL.qCL (univScalars hQ RD)) (univScalars_klr hQ RD) (vacWt RD Λ))) _ n).trans ?_
  congr 1
  change (CL.upFunctorC (CL.presCL RD k (univScalars hQ RD))
    (CL.qCL (univScalars hQ RD)) (univScalars_klr hQ RD) (vacWt RD Λ)).map
      ((KLR.Diagram.pres k (CL.qCL (univScalars hQ RD))).diag (KLR.Diagram.dotD j a)) = _
  rw [CL.upFunctorC_diag, CL.upDiag_eq_dgC, KLR.Diagram.layers_dotD]
  simp only [List.map_cons, List.map_nil, upLD, hd]
  rfl

/-- The comparison map on a power of the dot on the strand next to the vacuum. -/
theorem vacThetaM_x_pow_e {ν : Multiset I} (j : KLR.Seq ν) (a : Fin (Multiset.card ν))
    (ha : a.val + 1 = Multiset.card ν) (n : ℕ) :
    vacThetaM (lam := lam) hQ RD Λ ν (x a ^ n * e j) = single j j
      (CL.dgC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (ups (KLR.Diagram.word j))
        (ups (KLR.Diagram.word j))
        (List.replicate n (ups ((KLR.Diagram.word j).take a), .dot (up (j.1 a)), []))) := by
  rw [← vacUpHom_x_pow_e hQ RD Λ j a ha n, map_mul (vacUpHom hQ RD Λ ν), map_pow]
  change vacTheta (lam := lam) hQ RD Λ ν (x a ^ n * e j) = _
  rw [map_mul, map_pow, vacTheta_x, vacTheta_e]
  rfl

include hΛ in
/-- **The cyclotomic relations go to `I`**: the universal cyclotomic polynomial of the label of
the last strand, in the dot on that strand, maps into the matrices with entries in `I`. -/
theorem vacThetaM_cycPoly_mem {ν : Multiset I} (j : KLR.Seq ν) (a : Fin (Multiset.card ν))
    (ha : a.val + 1 = Multiset.card ν) :
    vacThetaM (lam := lam) hQ RD Λ ν
      (Polynomial.aeval (x a) (univCycPoly k lam (j.1 a)) * e j) ∈ vacMatIdeal hQ RD Λ ν := by
  have hd : (KLR.Diagram.word j).drop (a + 1) = [] :=
    List.drop_eq_nil_of_le (by simp [ha])
  have hS : ups (KLR.Diagram.word j) = ups ((KLR.Diagram.word j).take a) ++ [up (j.1 a)] ++ [] := by
    conv_lhs => rw [← KLR.Diagram.word_split j a]
    simp [hd, ups]
  have e1 : Polynomial.aeval (x a) (univCycPoly k lam (j.1 a)) * e j =
      x a ^ lam (j.1 a) * e j + ∑ n : Fin (lam (j.1 a)),
        algebraMap (UnivCycRing k lam) (KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν)
          ((-1) ^ (n.val + 1) * MvPolynomial.X ⟨j.1 a, n⟩) *
          (x a ^ (lam (j.1 a) - (n.val + 1)) * e j) := by
    rw [univCycPoly, univCycTail, map_add, map_sum, Polynomial.aeval_X_pow, add_mul,
      Finset.sum_mul]
    simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, mul_assoc]
  have e2 : ∀ n : Fin (lam (j.1 a)), vacThetaM (lam := lam) hQ RD Λ ν
      (algebraMap (UnivCycRing k lam) (KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν)
          ((-1) ^ (n.val + 1) * MvPolynomial.X ⟨j.1 a, n⟩) *
          (x a ^ (lam (j.1 a) - (n.val + 1)) * e j)) = single j j
        (CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (ups (KLR.Diagram.word j))
            (vacScal hQ RD Λ ((-1) ^ (n.val + 1) * MvPolynomial.X ⟨j.1 a, n⟩)).val ≫
          CL.dgC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (ups (KLR.Diagram.word j))
            (ups (KLR.Diagram.word j)) (List.replicate (lam (j.1 a) - (n.val + 1))
              (ups ((KLR.Diagram.word j).take a), .dot (up (j.1 a)), []))) := by
    intro n
    rw [map_mul, vacThetaM_algebraMap, vacThetaM_x_pow_e hQ RD Λ j a ha]
    change CLQ.bubDiag RD k (univScalars hQ RD) (vacWt RD Λ) ν _ * _ = _
    refine (CLQ.bubDiag_central RD k (univScalars hQ RD) (vacWt RD Λ) ν _ _).trans ?_
    exact CLQ.single_mul_bubDiag RD k (univScalars hQ RD) (vacWt RD Λ) ν _ j j _
  rw [e1, map_add, map_sum, vacThetaM_x_pow_e hQ RD Λ j a ha, Finset.sum_congr rfl fun n _ => e2 n,
    ← KLR.Diagram.MatEnd.single_sum, ← KLR.Diagram.MatEnd.single_add]
  refine single_mem_vacMatIdeal j j _ ?_
  have h1 := mem_vacFactor_of_mem_vacIdeal hQ RD Λ rfl rfl
    (vacCurl_mem hQ RD Λ hΛ _ (j.1 a) _ hS)
  exact mem_vacIdeal_of_mem_vacFactor hQ RD Λ (RouqFamily.cond_word (vacWt RD Λ) j).2.2
    (RouqFamily.cond_word (vacWt RD Λ) j).2.2 h1

include hΛ in
/-- **The cyclotomic ideal maps into `I`** after the flips: for `z` in the cyclotomic ideal,
`Θ(σ(hflip z))` has all entries in `I`. -/
theorem vacThetaM_sigma_hflip_mem {ν : Multiset I}
    {z : KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν}
    (hz : z ∈ cycIdeal (cycQ k lam Q) (univCycPoly k lam) ν) :
    vacThetaM (lam := lam) hQ RD Λ ν (sigma hQ.cycQ.klrSymm (hflip z)) ∈
      vacMatIdeal hQ RD Λ ν := by
  set g : KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν → VacMat hQ RD Λ ν :=
    fun z => vacThetaM (lam := lam) hQ RD Λ ν (sigma hQ.cycQ.klrSymm (hflip z)) with hg
  have gmul : ∀ a b, g (a * b) = g b * g a := fun a b => by
    simp only [hg, hflip_mul, map_mul]
  let J : TwoSidedIdeal (KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν) :=
    TwoSidedIdeal.mk' {z | g z ∈ vacMatIdeal hQ RD Λ ν}
      (by
        have h0 : hflip (0 : KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν) = 0 := by
          have := hflip_sub (0 : KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν) 0
          rwa [sub_zero, sub_self] at this
        show g 0 ∈ vacMatIdeal hQ RD Λ ν
        simp only [hg, h0, map_zero]; exact zero_mem _)
      (fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, hg, hflip_add, map_add] at ha hb ⊢; exact add_mem ha hb)
      (fun {a} ha => by
        simp only [Set.mem_ofPred_eq, hg] at ha ⊢
        rw [show hflip (-a) = -hflip a by simpa using hflip_sub 0 a, map_neg, map_neg]
        exact neg_mem ha)
      (fun {a b} hb => by
        simp only [Set.mem_ofPred_eq] at hb ⊢
        rw [gmul]; exact TwoSidedIdeal.mul_mem_right _ _ _ hb)
      (fun {a b} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [gmul]; exact TwoSidedIdeal.mul_mem_left _ _ _ ha)
  have hJ : ∀ z, z ∈ J ↔ g z ∈ vacMatIdeal hQ RD Λ ν := fun z =>
    TwoSidedIdeal.mem_mk' {z | g z ∈ vacMatIdeal hQ RD Λ ν} _ _ _ _ _ z
  have hle : cycIdeal (cycQ k lam Q) (univCycPoly k lam) ν ≤ J := by
    rw [cycIdeal, TwoSidedIdeal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, hJ]
    by_cases h : 0 < Multiset.card ν
    · rw [cycElt_of_pos _ _ i h]
      have ha : (Fin.rev ⟨0, h⟩ : Fin (Multiset.card ν)).val + 1 = Multiset.card ν := by
        simp only [Fin.val_rev]; omega
      have := vacThetaM_cycPoly_mem hQ RD Λ hΛ i.rev (Fin.rev ⟨0, h⟩) ha
      rw [Seq.rev_apply, Fin.rev_rev] at this
      convert this using 2
      rw [hflip_mul, hflip_e, hflip_aeval_x, map_mul, sigma_e,
        ← (commute_e_aeval_x i.rev _ _).eq]
      congr 1
      exact (Polynomial.aeval_algHom_apply (sigma hQ.cycQ.klrSymm).toAlgHom _ _).symm.trans
        (by erw [sigma_x])
    · have h0 : cycElt (cycQ k lam Q) (univCycPoly k lam) i = 0 := by simp [cycElt, h]
      rw [h0, ← hJ]
      exact zero_mem J
  exact (hJ z).1 (hle hz)

/-- **The kernel of the comparison map is `I`** (Webster, arXiv:1309.3796v2, proof of
Prop. 3.25): a matrix of upward 2-morphisms has vanishing vacuum entries exactly when all its
entries lie in `I`. -/
theorem vacRingHom_eq_zero_iff {ν : Multiset I} (φ : VacMat hQ RD Λ ν) :
    vacRingHom.{u, v, w} hQ RD Λ hΛ ν φ = 0 ↔ φ ∈ vacMatIdeal hQ RD Λ ν := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := exists_vacThetaM_sub_mem (hQ := hQ) (RD := RD) (Λ := Λ) hΛ φ
    have h1 : vacRingHom.{u, v, w} hQ RD Λ hΛ ν (vacThetaM (lam := lam) hQ RD Λ ν y) = 0 := by
      have h2 := congrArg MulOpposite.op (vacSum_eq_zero_of_mem_vacMatIdeal hQ RD Λ hΛ hy)
      rw [← vacRingHom_apply, map_sub, h, zero_sub, MulOpposite.op_zero, neg_eq_zero] at h2
      exact h2
    rw [vacRingHom_apply, MulOpposite.op_eq_zero_iff] at h1
    change vacSum.{u, v, w} hQ RD Λ hΛ ν (vacTheta (lam := lam) hQ RD Λ ν y) = 0 at h1
    rw [vacSum_vacTheta, CycKLR.mk_eq_zero_iff] at h1
    have h3 := vacThetaM_sigma_hflip_mem hQ RD Λ hΛ h1
    rw [hflip_hflip, sigma_sigma] at h3
    simpa using add_mem hy h3
  · intro h
    rw [vacRingHom_apply, vacSum_eq_zero_of_mem_vacMatIdeal hQ RD Λ hΛ h, MulOpposite.op_zero]

/-- The comparison map is surjective. -/
theorem vacRingHom_surjective (ν : Multiset I) :
    Function.Surjective (vacRingHom.{u, v, w} hQ RD Λ hΛ ν) := by
  intro c
  obtain ⟨u', hu⟩ := CycKLR.mk_surjective (k := UnivCycRing k lam) (Q := cycQ k lam Q)
    (a := univCycPoly k lam) (ν := ν) c.unop
  refine ⟨vacThetaM (lam := lam) hQ RD Λ ν (sigma hQ.cycQ.klrSymm (hflip u')), ?_⟩
  rw [vacRingHom_apply]
  change MulOpposite.op (vacSum.{u, v, w} hQ RD Λ hΛ ν (vacTheta (lam := lam) hQ RD Λ ν _)) = c
  rw [vacSum_vacTheta, sigma_sigma, hflip_hflip, hu, MulOpposite.op_unop]

/-- **Webster, arXiv:1309.3796v2, Prop. 3.25 (vacuum form)**: modulo `I`, the upward
2-endomorphisms of the words of `ν` at the region of `P_∅` form the opposite of the cyclotomic
quotient `Ř^λ(ν)` of the universal KLR algebra. -/
noncomputable def vacQuotientEquiv (ν : Multiset I) :
    (vacMatIdeal hQ RD Λ ν).ringCon.Quotient ≃+*
      (CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν)ᵐᵒᵖ :=
  (RingCon.congr (RingEquiv.refl _) (RingCon.ext fun x y => by
      change _ ↔ vacRingHom.{u, v, w} hQ RD Λ hΛ ν x = vacRingHom.{u, v, w} hQ RD Λ hΛ ν y
      rw [TwoSidedIdeal.rel_iff, ← sub_eq_zero, ← map_sub, vacRingHom_eq_zero_iff])).trans
    (RingCon.quotientKerEquivOfSurjective _ (vacRingHom_surjective hQ RD Λ hΛ ν))

end
end Categorification.KLR.CyclotomicAction
