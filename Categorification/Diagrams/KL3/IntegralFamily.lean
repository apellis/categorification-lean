/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.IntegralSpanning

/-!
# Scalar compatibility and integral KL nondegeneracy descent

Khovanov–Lauda, *A categorification of quantum sl(n)*, arXiv:0807.3250v1,
§6.4, “Simple nondegeneracy observations”, using the spanning family of
Proposition 3.11. Rational nondegeneracy supplies an integral canonical basis;
base change then supplies that basis over every commutative ring.
-/
noncomputable section
namespace Categorification.KL3.Diagram.IntegralScalars
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Module
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (k : Type w) [CommRing k] (RD : WeightDatum C X Y)

@[simp] theorem homMap_comp {a b c : Obj (psig RD)}
    (f : (pres RD ℤ).obj a ⟶ (pres RD ℤ).obj b)
    (g : (pres RD ℤ).obj b ⟶ (pres RD ℤ).obj c) :
    homMap k RD a c (f ≫ g) = homMap k RD a b f ≫ homMap k RD b c g := by
  obtain ⟨f, rfl⟩ := (pres RD ℤ).lin_surjective f
  obtain ⟨g, rfl⟩ := (pres RD ℤ).lin_surjective g
  rw [← lin_comp, homMap_lin, coeff_comp, lin_comp, homMap_lin, homMap_lin]

@[simp] theorem homMap_id (a : Obj (psig RD)) :
    homMap k RD a a (𝟙 _) = 𝟙 _ := by
  rw [← diag_id, homMap_diag, diag_id]

@[simp] theorem homMap_dg (μ : X) (s t : List (Letter I)) (A : List (LayerData I)) :
    homMap k RD _ _ (dg RD ℤ μ s t A) = dg RD k μ s t A := by
  classical
  unfold dg
  split_ifs <;> simp

/-- Integer-linear extensionality with the canonical integer module structure. -/
theorem int_hom_ext_dg (μ : X) (s t : List (Letter I))
    {M : Type*} [AddCommGroup M]
    (F G : ((pres RD ℤ).obj (ob RD μ s) ⟶ (pres RD ℤ).obj (ob RD μ t)) →ₗ[ℤ] M)
    (h : ∀ A, SChain s A t → F (dg RD ℤ μ s t A) = G (dg RD ℤ μ s t A)) : F = G := by
  apply LinearMap.ext
  intro f
  have hf := mem_span_dg (RD := RD) (k := ℤ) μ f
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨A, hA, rfl⟩ := hx; exact h A hA
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul n x _ hx =>
    let : Linear ℤ (pres RD ℤ).Presented := (pres RD ℤ).instLinear
    have hn := int_smul_eq_zsmul
      (Linear.homModule ((pres RD ℤ).obj (ob RD μ s)) ((pres RD ℤ).obj (ob RD μ t)) : Module ℤ _) n x
    exact (congrArg F hn).trans ((map_zsmul F n x).trans
      ((congrArg (fun y : M => n • y) hx).trans ((map_zsmul G n x).symm.trans (congrArg G hn).symm)))

/-- Scalar change commutes with the valid empty-right contexts used in the KL family. -/
theorem homMap_ctxL_nil (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ [])) (hpost : SChain (u ++ t ++ []) post t₀)
    (f : (pres RD ℤ).obj (ob RD μ s) ⟶ (pres RD ℤ).obj (ob RD μ t)) :
    homMap k RD _ _ (ctxL RD ℤ μ s₀ t₀ pre u [] post s t f) =
      ctxL RD k μ s₀ t₀ pre u [] post s t (homMap k RD _ _ f) := by
  let F := (homMap k RD _ _).comp
    (ctxL RD ℤ μ s₀ t₀ pre u [] post s t).toAddMonoidHom.toIntLinearMap
  let G := (ctxL RD k μ s₀ t₀ pre u [] post s t).toAddMonoidHom.toIntLinearMap.comp
    (homMap k RD _ _)
  have he : F = G := by
    apply int_hom_ext_dg RD μ s t
    intro A _
    change homMap k RD _ _ (ctxL RD ℤ μ s₀ t₀ pre u [] post s t (dg RD ℤ μ s t A)) =
      ctxL RD k μ s₀ t₀ pre u [] post s t (homMap k RD _ _ (dg RD ℤ μ s t A))
    rw [ctxL_dg_nil RD ℤ μ hpre hpost, homMap_dg]
    exact ((congrArg (ctxL RD k μ s₀ t₀ pre u [] post s t) (homMap_dg k RD μ s t A)).trans
      (ctxL_dg_nil RD k μ hpre hpost A)).symm
  exact LinearMap.congr_fun he f

@[simp] theorem homMap_bubAt (μ : X) (s : List (Letter I))
    (f : End ((pres RD ℤ).obj (ob RD μ []))) :
    homMap k RD _ _ (bubAt RD ℤ μ s f) = bubAt RD k μ s (homMap k RD _ _ f) :=
  homMap_ctxL_nil k RD μ (by simp) (by simp) f

/-- Integer coefficient change on the commutative identity endomorphism ring. -/
def endOneMap (μ : X) : EndOne RD ℤ μ →+* EndOne RD k μ where
  toFun := homMap k RD _ _
  map_zero' := map_zero _
  map_one' := homMap_id k RD _
  map_add' := map_add _
  map_mul' f g := homMap_comp k RD g f

@[simp] theorem homMap_cwU (μ : X) (i : I) (n : ℤ) :
    homMap k RD _ _ (cwU RD ℤ μ i n) = cwU RD k μ i n := by
  simp only [cwU, homMap_lin, coeff_cwL]

@[simp] theorem homMap_ccwU (μ : X) (i : I) (n : ℤ) :
    homMap k RD _ _ (ccwU RD ℤ μ i n) = ccwU RD k μ i n := by
  simp only [ccwU, homMap_lin, coeff_ccwL]

@[simp] theorem homMap_bubGen (μ : X) (i : I) (n : ℕ) :
    homMap k RD _ _ (bubGen RD ℤ μ i n) = bubGen RD k μ i n := by
  unfold bubGen
  split_ifs <;> simp

/-- Product formula for the bubble monomial, over a variable base ring. -/
theorem bubMon_product (μ : X) (m : (I × ℕ) →₀ ℕ) :
    bubMon RD k μ m =
      (m.prod fun p n => (EndOne.of (bubGen RD k μ p.1 (p.2 + 1))) ^ n).val := by
  unfold bubMon bubMap
  rw [MvPolynomial.aeval_monomial, map_one, one_mul]

@[simp] theorem homMap_bubMon (μ : X) (m : (I × ℕ) →₀ ℕ) :
    homMap k RD _ _ (bubMon RD ℤ μ m) = bubMon RD k μ m := by
  rw [bubMon_product ℤ RD, bubMon_product k RD]
  change (endOneMap k RD μ) (m.prod fun p n => (EndOne.of (bubGen RD ℤ μ p.1 (p.2 + 1))) ^ n) =
    m.prod fun p n => (EndOne.of (bubGen RD k μ p.1 (p.2 + 1))) ^ n
  simp only [Finsupp.prod, map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro p _
  congr 1
  exact homMap_bubGen k RD μ p.1 (p.2 + 1)

@[simp] theorem homMap_oneB (μ : X) (v : List (Letter I)) (x : SpanIdx [] v) :
    homMap k RD _ _ (IntegralSpanning.oneB RD ℤ μ v x) = IntegralSpanning.oneB RD k μ v x := by
  simp only [IntegralSpanning.oneB, homMap_comp, homMap_dg, homMap_bubAt, homMap_bubMon]

@[simp] theorem homMap_twoB (μ : X) (s t : List (Letter I)) (x : SpanIdx s t) :
    homMap k RD _ _ (IntegralSpanning.twoB RD ℤ μ s t x) = IntegralSpanning.twoB RD k μ s t x := by
  have hp : SChain s [] (s ++ [] ++ []) := by simp
  have hq : SChain (s ++ (rd s ++ t) ++ []) ((capA (rd s)).map (whL [] t)) t := by
    simpa using (sChain_capA (rd s)).whisk [] t
  exact (homMap_ctxL_nil k RD μ hp hq _).trans
    (congrArg (IntegralSpanning.bendG RD k μ s t) (homMap_oneB k RD μ (rd s ++ t) (oneIdx x)))

end Categorification.KL3.Diagram.IntegralScalars

namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Module
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} [Finite I]

omit [Finite I] in
/-- Integral spanning expressed with the canonical integer module instance. -/
theorem integralTwoB_span (μ : X) (s t : List (Letter I)) :
    Submodule.span ℤ (Set.range (IntegralSpanning.twoB RD ℤ μ s t)) = ⊤ := by
  classical
  have h := IntegralSpanning.span_twoB (RD := RD) (k := ℤ) μ s t
  let : Linear ℤ (pres RD ℤ).Presented := (pres RD ℤ).instLinear
  have hm : (Linear.homModule ((pres RD ℤ).obj (ob RD μ s)) ((pres RD ℤ).obj (ob RD μ t)) :
      Module ℤ _) = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  rw [hm] at h
  exact h

/-- The integral canonical basis, using the canonical integer module structure. -/
def integralCanonicalBasis (hnd : CalculusNondeg RD ℚ) (μ : X) (s t : List (Letter I)) :
    Basis (SpanIdx s t) ℤ ((pres RD ℤ).obj (ob RD μ s) ⟶ (pres RD ℤ).obj (ob RD μ t)) := by
  classical
  have he : ⇑(basisOfCalculusNondeg hnd μ s t (twoB RD ℚ μ s t) (isSpanFamily_twoB μ s t)) =
      twoB RD ℚ μ s t := funext fun x => basisOfCalculusNondeg_apply hnd μ s t _ _ x
  have hli : LinearIndependent ℚ (twoB RD ℚ μ s t) := by
    rw [← he]
    exact (basisOfCalculusNondeg hnd μ s t _ _).linearIndependent
  exact IntegralDescent.integralBasis (IntegralSpanning.twoB RD ℤ μ s t) (twoB RD ℚ μ s t)
    (IntegralScalars.homMap ℚ RD _ _) (IntegralScalars.homMap_twoB ℚ RD μ s t)
    (integralTwoB_span μ s t) hli

@[simp] theorem integralCanonicalBasis_apply (hnd : CalculusNondeg RD ℚ) (μ : X)
    (s t : List (Letter I)) (x : SpanIdx s t) :
    integralCanonicalBasis hnd μ s t x = IntegralSpanning.twoB RD ℤ μ s t x := by
  unfold integralCanonicalBasis
  exact IntegralDescent.integralBasis_apply _ _ _ _ _ _ _

/-- **KL III §6.4: rational nondegeneracy gives the canonical basis over every
commutative ring.** Integral spanning and actual presentation base change are
proved above; no flatness or torsion-freeness of the target Hom is assumed. -/
def integralNondegBasis (k : Type w) [CommRing k] (hnd : CalculusNondeg RD ℚ)
    (μ : X) (s t : List (Letter I)) :
    Basis (SpanIdx s t) k ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) := by
  classical
  exact basisOfIntegralSpanning k hnd μ s t (IntegralSpanning.twoB RD ℤ μ s t)
    (integralTwoB_span μ s t) (twoB RD ℚ μ s t) (isSpanFamily_twoB μ s t)
    (IntegralScalars.homMap_twoB ℚ RD μ s t)

@[simp] theorem integralNondegBasis_apply (k : Type w) [CommRing k] (hnd : CalculusNondeg RD ℚ)
    (μ : X) (s t : List (Letter I)) (x : SpanIdx s t) :
    integralNondegBasis k hnd μ s t x = IntegralSpanning.twoB RD k μ s t x := by
  classical
  exact (basisOfIntegralSpanning_apply k hnd μ s t (IntegralSpanning.twoB RD ℤ μ s t)
    (integralTwoB_span μ s t) (twoB RD ℚ μ s t) (isSpanFamily_twoB μ s t)
    (IntegralScalars.homMap_twoB ℚ RD μ s t) x).trans (IntegralScalars.homMap_twoB k RD μ s t x)

/-- The characteristic-zero worker can supply only `CalculusNondeg RD ℚ`;
this yields `CalculusNondeg` in every characteristic. -/
theorem calculusNondeg_of_rational (k : Type w) [Field k] (hnd : CalculusNondeg RD ℚ) :
    CalculusNondeg RD k := by
  classical
  intro μ s t d
  apply (finrank_eq_iff_linearIndependent μ s t (isSpanFamily_twoB μ s t) d).mpr
  have he : ⇑(integralNondegBasis k hnd μ s t) = twoB RD k μ s t :=
    funext fun x => integralNondegBasis_apply k hnd μ s t x
  have hli : LinearIndependent k (twoB RD k μ s t) := by
    rw [← he]
    exact (integralNondegBasis k hnd μ s t).linearIndependent
  exact hli.comp _ Subtype.val_injective

end Categorification.KL3.Diagram
