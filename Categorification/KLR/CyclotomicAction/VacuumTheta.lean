/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumFakeBubbles
import Categorification.KLR.CyclotomicAction.VacuumBubbleScaling
import Categorification.Diagrams.CLQ.SpanningPhi
import Categorification.KLR.CyclotomicAction.VacuumEvalIdeal
import Categorification.KLR.CyclotomicAction.VacuumCoeffMul
import Categorification.KLR.ExtendScalars

/-!
# The comparison map from the cyclotomic KLR algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25. At the region `λ` of `P_∅`, the endomorphisms of `⊕_𝐢 E_𝐢 λ` (upward words)
form a matrix ring, an algebra over `Ř^λ_λ` through the fake bubbles. The KLR algebra over
`Ř^λ_λ` maps to it by upward diagrams (`vacTheta`), and composing with the vacuum entries gives
the cyclotomic quotient (`vacSum_vacTheta`).

* `VacMat`, `vacMatIdeal`: the matrix ring and the matrices with all entries in `I`;
* `vacMatIdeal_le_ker`: the vacuum entries vanish on `vacMatIdeal`;
* `vacScal`, `vacScalMat`: `Ř^λ_λ` as fake bubbles and as diagonal matrices;
* `vacTheta`: the comparison map;
* `vacSum_vacTheta`: the comparison map on vacuum entries.
-/

namespace Categorification.KLR.CyclotomicAction
open CategoryTheory TwoRep QuantumGroup KLRAlgebra StringDiagrams Diagrams.BicatInterp
open KL3.Diagram
universe u v w u₁
noncomputable section
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)
attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

/-- The endomorphisms of `⊕_t E_t 1_λ` (upward words of weight `ν`), `λ` the region of
`P_∅`, as a matrix ring. -/
abbrev VacMat (ν : Multiset I) := KLR.Diagram.MatEnd (fun t : KLR.Seq ν =>
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t))))

/-- All entries of `φ` lie in the ideal `I`. -/
def VacMem {ν : Multiset I} (φ : VacMat hQ RD Λ ν) : Prop :=
  ∀ t s, (show vacUpHom₁ hQ RD Λ t ⟶ vacUpHom₁ hQ RD Λ s from φ t s) ∈ vacIdeal hQ RD Λ _ _

variable {hQ RD Λ} in
theorem vacMem_comp {ν : Multiset I} {t s r : KLR.Seq ν}
    (f : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t))) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word s))))
    (g : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word s))) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word r))))
    (h : (show vacUpHom₁ hQ RD Λ t ⟶ vacUpHom₁ hQ RD Λ s from f) ∈ vacIdeal hQ RD Λ _ _ ∨
      (show vacUpHom₁ hQ RD Λ s ⟶ vacUpHom₁ hQ RD Λ r from g) ∈ vacIdeal hQ RD Λ _ _) :
    (show vacUpHom₁ hQ RD Λ t ⟶ vacUpHom₁ hQ RD Λ r from
      (f ≫ g : (CL.presCL RD k (univScalars hQ RD)).obj _ ⟶ _)) ∈ vacIdeal hQ RD Λ _ _ := by
  rcases h with h | h
  · exact mem_factorIdeal_comp h (show vacUpHom₁ hQ RD Λ s ⟶ vacUpHom₁ hQ RD Λ r from g)
  · exact comp_mem_factorIdeal (show vacUpHom₁ hQ RD Λ t ⟶ vacUpHom₁ hQ RD Λ s from f) h

/-- The matrices of upward 2-morphisms all of whose entries lie in `I`. -/
def vacMatIdeal (ν : Multiset I) : TwoSidedIdeal (VacMat hQ RD Λ ν) :=
  TwoSidedIdeal.mk' {φ | VacMem hQ RD Λ φ}
    (fun t s => Submodule.zero_mem _)
    (fun hx hy t s => Submodule.add_mem _ (hx t s) (hy t s))
    (fun hx t s => Submodule.neg_mem _ (hx t s))
    (fun {x y} hy t s => by
      exact Submodule.sum_mem _ fun j _ => vacMem_comp _ _ (Or.inl (hy t j)))
    (fun {x y} hx t s => by
      exact Submodule.sum_mem _ fun j _ => vacMem_comp _ _ (Or.inr (hx j s)))

theorem mem_vacMatIdeal {ν : Multiset I} (φ : VacMat hQ RD Λ ν) :
    φ ∈ vacMatIdeal hQ RD Λ ν ↔ VacMem hQ RD Λ φ := TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _

theorem vacSum_eq_zero_of_mem_vacMatIdeal {ν : Multiset I} {φ : VacMat hQ RD Λ ν}
    (hφ : φ ∈ vacMatIdeal hQ RD Λ ν) : vacSum.{u, v, w} (lam := lam) hQ RD Λ hΛ ν φ = 0 := by
  rw [mem_vacMatIdeal] at hφ
  exact Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun s _ =>
    vacCoeff_eq_zero_of_mem_vacIdeal hQ RD Λ hΛ φ t s (hφ t s)

theorem vacMatIdeal_le_ker (ν : Multiset I) :
    vacMatIdeal hQ RD Λ ν ≤ TwoSidedIdeal.ker (vacRingHom.{u, v, w} (lam := lam) hQ RD Λ hΛ ν) :=
  fun φ hφ => by
    rw [TwoSidedIdeal.mem_ker, vacRingHom_apply, vacSum_eq_zero_of_mem_vacMatIdeal hQ RD Λ hΛ hφ]
    rfl

/-- The fake clockwise bubble at the vacuum whose action is the coordinate `e_{r+1}(p_j)`, up to
the sign `(-1)^{r+1}`. -/
def vacScalGen (p : Σ j : I, Fin (lam j)) :
    CLQ.EndOne RD k (univScalars hQ RD) (vacWt RD Λ) :=
  ((-1 : ℤ) ^ (p.2.val + 1)) • (show CLQ.EndOne RD k (univScalars hQ RD) (vacWt RD Λ) from
    (CL.presCL RD k (univScalars hQ RD)).lin
      (cwL RD k (vacWt RD Λ) p.1 (((p.2.val + 1 : ℕ) : ℤ) - lam p.1 - 1)))

/-- The scalars `Ř^λ_λ` as fake bubbles at the region of `P_∅`. -/
def vacScal : UnivCycRing k lam →ₐ[k] CLQ.EndOne RD k (univScalars hQ RD) (vacWt RD Λ) :=
  MvPolynomial.aeval (vacScalGen (lam := lam) hQ RD Λ)

include hΛ in
theorem vacEval_vacScal (c : UnivCycRing k lam) :
    vacEval.{u, v, w} hQ RD Λ hΛ (vacScal hQ RD Λ c).val = vacScalarHom.{u, v, w} hQ RD Λ hΛ c := by
  have h : ((vacEval.{u, v, w} hQ RD Λ hΛ).comp
      (show CLQ.EndOne RD k (univScalars hQ RD) (vacWt RD Λ) →+*
        End ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) [])) from
        RingHom.id _)).comp (vacScal hQ RD Λ).toRingHom = vacScalarHom.{u, v, w} hQ RD Λ hΛ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
    · change vacEval.{u, v, w} hQ RD Λ hΛ (MvPolynomial.aeval (vacScalGen (lam := lam) hQ RD Λ)
        (MvPolynomial.C a)) = (MvPolynomial.C a : UnivCycRing k lam) • 𝟙 _
      rw [MvPolynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
      change ((univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).map₂
        (show vacHom (k := k) hQ RD Λ [] rfl ⟶ vacHom hQ RD Λ [] rfl from a • 𝟙 _)).hom.app _ = _
      erw [Diagrams.BicatInterp.admissiblePseudofunctor_map₂_smul]
      change (MvPolynomial.C a : UnivCycRing k lam) • vacEval.{u, v, w} hQ RD Λ hΛ 1 = _
      rw [map_one]
      rfl
    · obtain ⟨j, r⟩ := p
      have hE : vacEval.{u, v, w} hQ RD Λ hΛ (vacScalGen hQ RD Λ ⟨j, r⟩) =
          ((-1 : ℤ) ^ (r.val + 1)) • vacEvalLin.{u, v, w} hQ RD Λ hΛ
            (cwL RD k (vacWt RD Λ) j (((r.val + 1 : ℕ) : ℤ) - lam j - 1)) :=
        map_zsmul (vacEval.{u, v, w} hQ RD Λ hΛ) _ _
      change vacEval.{u, v, w} hQ RD Λ hΛ (MvPolynomial.aeval (vacScalGen (lam := lam) hQ RD Λ)
        (MvPolynomial.X ⟨j, r⟩)) = _
      rw [MvPolynomial.aeval_X, hE, vacEvalLin_cwL hQ RD Λ hΛ j (r.val + 1) r.isLt, ← map_zsmul]
      congr 1
      simp only [vacFakeVal, Nat.add_one_ne_zero, ↓reduceDIte, Nat.succ_le_of_lt r.isLt,
        Nat.add_sub_cancel, Fin.eta, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        ← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, one_pow]
  exact congrArg (fun f => f c) h

/-- The scalars `Ř^λ_λ` acting diagonally on `⊕_t E_t 1_λ` by fake bubbles at the right. -/
def vacScalMat (ν : Multiset I) : UnivCycRing k lam →ₐ[k] KLR.Diagram.MatEnd (fun t : KLR.Seq ν =>
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t)))) :=
  (CLQ.bubDiag RD k (univScalars hQ RD) (vacWt RD Λ) ν).comp (vacScal hQ RD Λ)

theorem vacScalMat_eq (ν : Multiset I) (c : UnivCycRing k lam) :
    vacScalMat hQ RD Λ ν c = vacBubMat hQ RD Λ ν (vacScal hQ RD Λ c).val := by
  ext t s
  change (∑ i, KLR.Diagram.MatEnd.single i i (CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ)
    (ups (KLR.Diagram.word i)) (vacScal hQ RD Λ c).val)) t s = _
  rw [KLR.Diagram.MatEnd.sum_apply]
  by_cases h : t = s
  · subst h
    rw [Finset.sum_eq_single t (fun i _ hi => KLR.Diagram.MatEnd.single_apply_of_ne _
      (fun h' => hi h'.1.symm)) (by simp), KLR.Diagram.MatEnd.single_apply_self]
    simp only [vacBubMat, KLR.Diagram.MatEnd.one_apply_self, Category.id_comp]
    rfl
  · rw [Finset.sum_eq_zero (fun i _ => KLR.Diagram.MatEnd.single_apply_of_ne _
      (fun h' => h (h'.1.trans h'.2.symm)))]
    simp only [vacBubMat, KLR.Diagram.MatEnd.one_apply_of_ne h, Limits.zero_comp]
    rfl

theorem vacCoeff_vacScalMat_mul {ν : Multiset I} (c : UnivCycRing k lam)
    (φ : KLR.Diagram.MatEnd (fun t : KLR.Seq ν =>
      (CL.presCL RD k (univScalars hQ RD)).obj
        (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t))))) (t s : KLR.Seq ν) :
    vacCoeff.{u, v, w} hQ RD Λ hΛ ν (vacScalMat hQ RD Λ ν c * φ) t s =
      algebraMap _ (CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν) c *
        vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t s := by
  rw [vacScalMat_eq]
  exact vacCoeff_vacBubMat_mul hQ RD Λ hΛ _ c (vacEval_vacScal hQ RD Λ hΛ c) φ t s

theorem vacSum_vacScalMat_mul {ν : Multiset I} (c : UnivCycRing k lam) (φ : VacMat hQ RD Λ ν) :
    vacSum.{u, v, w} hQ RD Λ hΛ ν (vacScalMat hQ RD Λ ν c * φ) =
      algebraMap _ (CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν) c *
        vacSum.{u, v, w} hQ RD Λ hΛ ν φ := by
  simp only [vacSum, vacCoeff_vacScalMat_mul hQ RD Λ hΛ, Finset.mul_sum]

/-- The matrix ring `End(⊕_t E_t 1_λ)`, viewed as an algebra over `Ř^λ_λ` acting by fake
bubbles at the region of `P_∅`. -/
def VacMatR (ν : Multiset I) : Type _ := VacMat hQ RD Λ ν

instance (ν : Multiset I) : Ring (VacMatR hQ RD Λ ν) := inferInstanceAs (Ring (VacMat hQ RD Λ ν))

instance (ν : Multiset I) : Algebra (UnivCycRing k lam) (VacMatR hQ RD Λ ν) :=
  RingHom.toAlgebra' (vacScalMat hQ RD Λ ν).toRingHom (fun c φ =>
    CLQ.bubDiag_central RD k (univScalars hQ RD) (vacWt RD Λ) ν (vacScal hQ RD Λ c) φ)

/-- **The comparison map** (Webster, arXiv:1309.3796v2, proof of Prop. 3.25): the KLR algebra over
`Ř^λ_λ` acting on `⊕_t E_t 1_λ` by upward diagrams, with the scalars acting by fake bubbles. -/
def vacTheta (ν : Multiset I) :
    KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν →ₐ[UnivCycRing k lam] VacMatR hQ RD Λ ν :=
  KLRAlgebra.extendScalars (algebraMap k (UnivCycRing k lam)) (map_qCL_univScalars hQ RD)
    (B := VacMatR hQ RD Λ ν) (vacUpHom hQ RD Λ ν).toRingHom (fun c => by
      change vacUpHom hQ RD Λ ν (algebraMap k _ c) =
        vacScalMat hQ RD Λ ν (algebraMap k _ c)
      rw [AlgHom.commutes, AlgHom.commutes])

theorem vacTheta_e (ν : Multiset I) (i : KLR.Seq ν) :
    vacTheta (lam := lam) hQ RD Λ ν (e i) = vacUpHom hQ RD Λ ν (e i) :=
  KLRAlgebra.extendScalars_e _ _ _ _ i

theorem vacTheta_x (ν : Multiset I) (a : Fin (Multiset.card ν)) :
    vacTheta (lam := lam) hQ RD Λ ν (x a) = vacUpHom hQ RD Λ ν (x a) :=
  KLRAlgebra.extendScalars_x _ _ _ _ a

theorem vacTheta_ψ (ν : Multiset I) (j : ℕ) :
    vacTheta (lam := lam) hQ RD Λ ν (ψ j) = vacUpHom hQ RD Λ ν (ψ j) :=
  KLRAlgebra.extendScalars_ψ _ _ _ _ j

theorem vacTheta_algebraMap (ν : Multiset I) (c : UnivCycRing k lam) :
    vacTheta (lam := lam) hQ RD Λ ν (algebraMap _ _ c) = vacScalMat hQ RD Λ ν c :=
  (vacTheta (lam := lam) hQ RD Λ ν).commutes c

/-- The cyclotomic quotient composed with `hflip ∘ σ`, as an algebra homomorphism into the
opposite ring. -/
def vacTarget (ν : Multiset I) :
    KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν →ₐ[UnivCycRing k lam]
      (CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν)ᵐᵒᵖ :=
  (AlgHom.op (CycKLR.mk _ (cycQ k lam Q) (univCycPoly k lam) ν)).comp
    ((flipAlgHom _ (cycQ k lam Q) ν).comp (sigma hQ.cycQ.klrSymm).toAlgHom)

omit [Nontrivial k] in
theorem vacTarget_apply (ν : Multiset I) (y : KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν) :
    vacTarget hQ ν y = MulOpposite.op (CycKLR.mk _ (cycQ k lam Q) (univCycPoly k lam) ν
      (hflip (sigma hQ.cycQ.klrSymm y))) := rfl

/-- The comparison map followed by the vacuum entries, as an algebra homomorphism. -/
def vacThetaSum (ν : Multiset I) :
    KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν →ₐ[UnivCycRing k lam]
      (CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν)ᵐᵒᵖ :=
  { (vacRingHom.{u, v, w} hQ RD Λ hΛ ν).comp
      (show KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν →+* VacMat hQ RD Λ ν from
        (vacTheta (lam := lam) hQ RD Λ ν).toRingHom) with
    commutes' := fun c => by
      change MulOpposite.op (vacSum.{u, v, w} hQ RD Λ hΛ ν
        (vacTheta (lam := lam) hQ RD Λ ν (algebraMap _ _ c))) = _
      rw [vacTheta_algebraMap, ← mul_one (vacScalMat hQ RD Λ ν c), vacSum_vacScalMat_mul,
        vacSum_one, mul_one]
      rfl }

theorem vacThetaSum_apply (ν : Multiset I) (y : KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν) :
    vacThetaSum.{u, v, w} hQ RD Λ hΛ ν y = MulOpposite.op (vacSum.{u, v, w} hQ RD Λ hΛ ν
      (vacTheta (lam := lam) hQ RD Λ ν y)) := rfl

theorem vacThetaSum_eq (ν : Multiset I) : vacThetaSum.{u, v, w} hQ RD Λ hΛ ν = vacTarget hQ ν := by
  refine KLRAlgebra.extendScalars_ext (fun i => ?_) (fun a => ?_) (fun j => ?_)
  · rw [vacThetaSum_apply, vacTheta_e, vacSum_vacUpHom, vacTarget_apply, mapRingHom_e]
  · rw [vacThetaSum_apply, vacTheta_x, vacSum_vacUpHom, vacTarget_apply, mapRingHom_x]
  · rw [vacThetaSum_apply, vacTheta_ψ, vacSum_vacUpHom, vacTarget_apply, mapRingHom_ψ]

/-- **The comparison map on vacuum entries** (Webster, arXiv:1309.3796v2, proof of Prop. 3.25). -/
theorem vacSum_vacTheta (ν : Multiset I) (y : KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν) :
    vacSum.{u, v, w} hQ RD Λ hΛ ν (vacTheta (lam := lam) hQ RD Λ ν y) =
      CycKLR.mk _ (cycQ k lam Q) (univCycPoly k lam) ν (hflip (sigma hQ.cycQ.klrSymm y)) :=
  congrArg MulOpposite.unop (AlgHom.congr_fun (vacThetaSum_eq hQ RD Λ hΛ ν) y)

end
end Categorification.KLR.CyclotomicAction
