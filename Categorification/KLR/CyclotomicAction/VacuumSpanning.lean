/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumTheta
import Categorification.KLR.CyclotomicAction.VacuumFactor

/-!
# Upward spanning at the vacuum

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25. At the region `λ` of `P_∅`, every endomorphism of `⊕_𝐢 E_𝐢 λ` is congruent
modulo the ideal `I` to the image of the comparison map from the KLR algebra over `Ř^λ_λ`
(`exists_vacThetaM_sub_mem`). The proof writes each matrix entry in the spanning set of
Prop. 3.10 (upward diagrams with bubbles on the right) and reduces the bubbles to fake bubbles
modulo `I`.

* `exists_vacScal_eq`: the fake bubbles at the vacuum are the scalars `Ř^λ_λ`;
* `vacThetaM`: the comparison map as a ring homomorphism;
* `single_mem_vacMatIdeal`: a single entry in `I` gives a matrix in `vacMatIdeal`;
* `exists_vacThetaM_sub_mem`: upward spanning modulo `I`.
-/
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

include hΛ in
/-- The fake bubbles at the vacuum are the scalars `Ř^λ_λ`. -/
theorem exists_vacScal_eq {a} (ha : a ∈ vacFakeAlg hQ RD Λ) :
    ∃ c : UnivCycRing k lam, (vacScal hQ RD Λ c).val = a := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, m, hm, rfl⟩ := hx
    have hi := ip_vacWt RD Λ hΛ i
    rcases lt_trichotomy (m + lam i + 1) 0 with hn | hn | hn
    · refine ⟨0, ?_⟩
      rw [map_zero, CLQ.EndOne.val_zero, cwL, ite_eq_right (by omega : ¬ (0 : ℤ) ≤ m),
        ite_eq_right (by omega : ¬ (0 : ℤ) ≤ m + 1 - ip RD i (vacWt RD Λ))]
      exact (Presentation.lin_zero _).symm
    · refine ⟨1, ?_⟩
      rw [map_one, CLQ.EndOne.val_one, show m = ip RD i (vacWt RD Λ) - 1 by omega,
        cwL_vacWt_ip_sub_one hQ RD Λ hΛ i]; rfl
    · obtain ⟨n, hn'⟩ : ∃ n : ℕ, m + lam i + 1 = (n + 1 : ℕ) := ⟨(m + lam i).toNat, by omega⟩
      have hnl : n < lam i := by omega
      refine ⟨((-1 : ℤ) ^ (n + 1)) • MvPolynomial.X ⟨i, ⟨n, hnl⟩⟩, ?_⟩
      rw [map_zsmul, vacScal, MvPolynomial.aeval_X, vacScalGen, smul_smul, ← pow_add,
        Even.neg_one_pow ⟨n + 1, rfl⟩, one_smul, show m = ((n + 1 : ℕ) : ℤ) - lam i - 1 by omega]
      rfl
  | algebraMap r => exact ⟨algebraMap k _ r, by rw [AlgHom.commutes]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, rfl⟩ := hx; obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, by rw [map_add]; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, rfl⟩ := hx; obtain ⟨d, rfl⟩ := hy
    exact ⟨c * d, by rw [map_mul]; rfl⟩


/-- `vacTheta` as a ring homomorphism into the matrix ring `VacMat`. -/
def vacThetaM (ν : Multiset I) :
    KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν →+* VacMat hQ RD Λ ν :=
  (vacTheta (lam := lam) hQ RD Λ ν).toRingHom

theorem vacThetaM_vacKLRMap (ν : Multiset I) (r : KLRAlgebra k (CL.qCL (univScalars hQ RD)) ν) :
    vacThetaM (lam := lam) hQ RD Λ ν (vacKLRMap hQ RD ν r) = vacUpHom hQ RD Λ ν r :=
  KLRAlgebra.extendScalars_mapRingHom (B := VacMatR hQ RD Λ ν) _ _ _ _ r

theorem vacThetaM_algebraMap (ν : Multiset I) (c : UnivCycRing k lam) :
    vacThetaM (lam := lam) hQ RD Λ ν (algebraMap _ _ c) = vacScalMat hQ RD Λ ν c :=
  vacTheta_algebraMap hQ RD Λ ν c

/-- `φ` is congruent modulo the ideal `I` to the image of the comparison map. -/
def VacApprox {ν : Multiset I} (φ : VacMat hQ RD Λ ν) : Prop :=
  ∃ y, φ - vacThetaM (lam := lam) hQ RD Λ ν y ∈ vacMatIdeal hQ RD Λ ν

variable {hQ RD Λ}

theorem VacApprox.of_mem {ν : Multiset I} {φ : VacMat hQ RD Λ ν}
    (h : φ ∈ vacMatIdeal hQ RD Λ ν) : VacApprox (lam := lam) hQ RD Λ φ :=
  ⟨0, by rwa [map_zero, sub_zero]⟩

theorem VacApprox.add {ν : Multiset I} {φ ψ : VacMat hQ RD Λ ν}
    (hφ : VacApprox (lam := lam) hQ RD Λ φ) (hψ : VacApprox (lam := lam) hQ RD Λ ψ) :
    VacApprox (lam := lam) hQ RD Λ (φ + ψ) := by
  obtain ⟨y, hy⟩ := hφ; obtain ⟨z, hz⟩ := hψ
  refine ⟨y + z, ?_⟩
  rw [map_add, show φ + ψ - (vacThetaM hQ RD Λ ν y + vacThetaM hQ RD Λ ν z) =
    (φ - vacThetaM hQ RD Λ ν y) + (ψ - vacThetaM hQ RD Λ ν z) by abel]
  exact add_mem hy hz

theorem VacApprox.mul {ν : Multiset I} {φ ψ : VacMat hQ RD Λ ν}
    (hφ : VacApprox (lam := lam) hQ RD Λ φ) (hψ : VacApprox (lam := lam) hQ RD Λ ψ) :
    VacApprox (lam := lam) hQ RD Λ (φ * ψ) := by
  obtain ⟨y, hy⟩ := hφ; obtain ⟨z, hz⟩ := hψ
  refine ⟨y * z, ?_⟩
  rw [map_mul, show φ * ψ - vacThetaM hQ RD Λ ν y * vacThetaM hQ RD Λ ν z =
    (φ - vacThetaM hQ RD Λ ν y) * ψ + vacThetaM hQ RD Λ ν y * (ψ - vacThetaM hQ RD Λ ν z) by
      noncomm_ring]
  exact add_mem (TwoSidedIdeal.mul_mem_right _ _ _ hy) (TwoSidedIdeal.mul_mem_left _ _ _ hz)

theorem VacApprox.vacUpHom {ν : Multiset I} (r : KLRAlgebra k (CL.qCL (univScalars hQ RD)) ν) :
    VacApprox (lam := lam) hQ RD Λ (vacUpHom hQ RD Λ ν r) :=
  ⟨vacKLRMap hQ RD ν r, by rw [vacThetaM_vacKLRMap, sub_self]; exact zero_mem _⟩

theorem VacApprox.vacScalMat {ν : Multiset I} (c : UnivCycRing k lam) :
    VacApprox (lam := lam) hQ RD Λ (vacScalMat hQ RD Λ ν c) :=
  ⟨algebraMap _ _ c, by rw [vacThetaM_algebraMap, sub_self]; exact zero_mem _⟩

theorem VacApprox.smul {ν : Multiset I} (a : k) {φ : VacMat hQ RD Λ ν}
    (hφ : VacApprox (lam := lam) hQ RD Λ φ) : VacApprox (lam := lam) hQ RD Λ (a • φ) := by
  rw [Algebra.smul_def, ← (CyclotomicAction.vacUpHom hQ RD Λ ν).commutes a]
  exact (VacApprox.vacUpHom _).mul hφ

theorem single_mem_vacMatIdeal {ν : Multiset I} (t s : KLR.Seq ν)
    (g : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t))) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word s))))
    (hg : (show vacUpHom₁ hQ RD Λ t ⟶ vacUpHom₁ hQ RD Λ s from g) ∈ vacIdeal hQ RD Λ _ _) :
    single t s g ∈ vacMatIdeal hQ RD Λ ν := by
  rw [mem_vacMatIdeal]
  intro t' s'
  by_cases h : t' = t ∧ s' = s
  · obtain ⟨rfl, rfl⟩ := h
    rw [single_apply_self]; exact hg
  · rw [single_apply_of_ne _ h]; exact zero_mem _

/-- Upward KLR diagrams in a single entry. -/
theorem VacApprox.single_up {ν : Multiset I} (t s : KLR.Seq ν)
    (F : (KLR.Diagram.pres k (CL.qCL (univScalars hQ RD))).obj (KLR.Diagram.ob (KLR.Diagram.word t))
      ⟶ (KLR.Diagram.pres k (CL.qCL (univScalars hQ RD))).obj
        (KLR.Diagram.ob (KLR.Diagram.word s))) :
    VacApprox (lam := lam) hQ RD Λ (single t s ((CL.upFunctorC (CL.presCL RD k (univScalars hQ RD))
      (CL.qCL (univScalars hQ RD)) (univScalars_klr hQ RD) (vacWt RD Λ)).map F)) := by
  have e : CyclotomicAction.vacUpHom hQ RD Λ ν
      ((KLR.Diagram.diagREquiv k (CL.qCL (univScalars hQ RD)) ν).symm (single t s F)) =
      single t s ((CL.upFunctorC (CL.presCL RD k (univScalars hQ RD))
        (CL.qCL (univScalars hQ RD)) (univScalars_klr hQ RD) (vacWt RD Λ)).map F) := by
    change matEndMap k (CL.upFunctorC (CL.presCL RD k (univScalars hQ RD))
        (CL.qCL (univScalars hQ RD)) (univScalars_klr hQ RD) (vacWt RD Λ)) _
        ((KLR.Diagram.diagREquiv k (CL.qCL (univScalars hQ RD)) ν)
      ((KLR.Diagram.diagREquiv k (CL.qCL (univScalars hQ RD)) ν).symm (single t s F))) = _
    rw [AlgEquiv.apply_symm_apply, matEndMap_single]
    rfl
  rw [← e]
  exact VacApprox.vacUpHom _

/-- Upward normal-form diagrams in a single entry. -/
theorem VacApprox.single_dgC {ν : Multiset I} (t s : KLR.Seq ν) {A : List (LayerData I)}
    (hA : Upward A) (h : SChain (ups (KLR.Diagram.word t)) A (ups (KLR.Diagram.word s))) :
    VacApprox (lam := lam) hQ RD Λ (single t s (CL.dgC (CL.presCL RD k (univScalars hQ RD))
      (vacWt RD Λ) (ups (KLR.Diagram.word t)) (ups (KLR.Diagram.word s)) A)) := by
  have hpos : Positive (ups (KLR.Diagram.word t)) := by simp [Positive, ups]
  obtain ⟨hc, hm⟩ := chain_toKLR h hA hpos
  have e₁ : (ups (KLR.Diagram.word t)).map Prod.snd = KLR.Diagram.word t := by
    simp [ups, Function.comp_def]
  have e₂ : (ups (KLR.Diagram.word s)).map Prod.snd = KLR.Diagram.word s := by
    simp [ups, Function.comp_def]
  rw [e₁, e₂] at hc
  have := VacApprox.single_up (lam := lam) (hQ := hQ) (Λ := Λ) t s
    ((KLR.Diagram.pres k (CL.qCL (univScalars hQ RD))).diag ⟨A.map toKLRLayer, hc⟩)
  rwa [CL.upFunctorC_diag, CL.upDiag_eq_dgC,
    show Diagram.layers ⟨A.map toKLRLayer, hc⟩ = A.map toKLRLayer from rfl, hm] at this

include hΛ in
/-- Bubbles at the right of the upward strands, in a diagonal entry. -/
theorem VacApprox.single_bubAtC {ν : Multiset I} (s : KLR.Seq ν)
    {γ : End ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) []))}
    (hγ : CL.IsBubC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) γ) :
    VacApprox (lam := lam) hQ RD Λ (single s s (CL.bubAtC (CL.presCL RD k (univScalars hQ RD))
      (vacWt RD Λ) (ups (KLR.Diagram.word s)) γ)) := by
  obtain ⟨a, ha, hγa⟩ := mem_vacReduced_of_isBubC hQ RD Λ hΛ hγ
  obtain ⟨c, rfl⟩ := exists_vacScal_eq hQ RD Λ hΛ ha
  have e : CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (ups (KLR.Diagram.word s)) γ
      = CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (ups (KLR.Diagram.word s))
          (γ - (show End ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) [])) from
            (vacScal hQ RD Λ c).val)) +
        CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (ups (KLR.Diagram.word s))
          (show End ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) [])) from
            (vacScal hQ RD Λ c).val) := by
    rw [← map_add, sub_add_cancel]
  rw [e, single_add]
  refine (VacApprox.of_mem (single_mem_vacMatIdeal s s _ ?_)).add ?_
  · exact mem_vacIdeal_of_mem_vacFactor hQ RD Λ (RouqFamily.cond_word (vacWt RD Λ) s).2.2
      (RouqFamily.cond_word (vacWt RD Λ) s).2.2 (bubAtC_mem_vacFactor hQ RD Λ _
        (mem_vacFactor_of_mem_vacIdeal hQ RD Λ rfl rfl hγa))
  · have e' : single s s (CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ)
        (ups (KLR.Diagram.word s))
          (show End ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) [])) from
            (vacScal hQ RD Λ c).val)) =
        CyclotomicAction.vacScalMat hQ RD Λ ν c * single s s (𝟙 _) := by
      change _ = CLQ.bubDiag RD k (univScalars hQ RD) (vacWt RD Λ) ν (vacScal hQ RD Λ c) * _
      refine Eq.symm ((CLQ.bubDiag_mul_single RD k (univScalars hQ RD) (vacWt RD Λ) ν
        (vacScal hQ RD Λ c) s s (𝟙 _)).trans ?_)
      erw [Category.id_comp]
      rfl
    rw [e']
    refine (VacApprox.vacScalMat c).mul ?_
    have := VacApprox.single_up (lam := lam) (hQ := hQ) (RD := RD) (Λ := Λ) s s (𝟙 _)
    rwa [CategoryTheory.Functor.map_id] at this

include hΛ in
theorem VacApprox.single {ν : Multiset I} (t s : KLR.Seq ν)
    (f : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t))) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word s)))) :
    VacApprox (lam := lam) hQ RD Λ (single t s f) := by
  have hf : f ∈ CL.upSpanC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) _ _ :=
    CL.prop310UpC (RD := RD) (univScalars hQ RD) (vacWt RD Λ) ν t s f
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨A, γ, hA, hS, hγ, rfl⟩ := hg
    rw [← single_mul_single t s s]
    exact (VacApprox.single_bubAtC hΛ s hγ).mul (VacApprox.single_dgC t s hA hS)
  | zero => rw [single_zero]; exact .of_mem (zero_mem _)
  | add x y _ _ hx hy => rw [single_add]; exact hx.add hy
  | smul a x _ hx => rw [single_smul]; exact hx.smul a

include hΛ in
/-- **Upward spanning at the vacuum** (Webster, arXiv:1309.3796v2, proof of Prop. 3.25): every
endomorphism of `⊕_t E_t 1_λ` is congruent modulo `I` to the image of the comparison map. -/
theorem exists_vacThetaM_sub_mem {ν : Multiset I} (φ : VacMat hQ RD Λ ν) :
    ∃ y, φ - vacThetaM (lam := lam) hQ RD Λ ν y ∈ vacMatIdeal hQ RD Λ ν := by
  rw [eq_sum_single φ]
  refine Finset.sum_induction _ (VacApprox (lam := lam) hQ RD Λ) (fun _ _ => VacApprox.add)
    (.of_mem (zero_mem _)) fun t _ => ?_
  exact Finset.sum_induction _ (VacApprox (lam := lam) hQ RD Λ) (fun _ _ => VacApprox.add)
    (.of_mem (zero_mem _)) fun s _ => VacApprox.single hΛ t s _

end
end Categorification.KLR.CyclotomicAction
