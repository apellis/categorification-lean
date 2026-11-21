/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumTheta
import Categorification.KLR.CyclotomicAction.VacuumFactor

/-!
# The cyclotomic relation next to the vacuum

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25. At the region `λ` of `P_∅`, the right curl relation shows that the universal
cyclotomic polynomial in the dot on an upward strand `E_c` next to the vacuum, with its
coefficients acting by fake bubbles, factors through a downward strand next to the vacuum.
Placed to the right of any word, it lies in the ideal `I` (`vacCurl_mem`).

* `CL.plcLC_bubRC`: a bubble right of a strand, placed right of a word;
* `plcLC_mem_vacFactor`: placing a factorization through the vacuum right of a word;
* `vacCurl_mem`: the cyclotomic relation in context lies in `I`.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram.CL
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (psig RD) k)

/-- Whiskering along equal objects, up to the transport isomorphisms. -/
theorem whisk_congr_obj {a b : Obj (psig RD)} (f : P.obj a ⟶ P.obj b) {U U' : Obj (psig RD)}
    {V V' : List (Col I X)} (hU : U = U') (hV : V = V') :
    P.whisk f U V = eqToHom (by rw [hU, hV]) ≫ P.whisk f U' V' ≫ eqToHom (by rw [hU, hV]) := by
  subst hU hV; simp

/-- A bubble to the right of the strand `l`, placed to the right of `s`. -/
theorem plcLC_bubRC (μ : X) (s : List (Letter I)) (l : Letter I) (β : End (P.obj (ob RD μ []))) :
    plcLC P μ s [] [l] [l] (bubRC P μ l β) = bubAtC P μ (s ++ [l] ++ []) β := by
  rw [TwoRep.RouqFamily.bubAtC_eq_whisk]
  simp only [bubRC, plcLC, dite_eq_left, plcC, LinearMap.coe_mk, AddHom.coe_mk]
  rw [whisk_comp, whisk_comp, whisk_eqToHom,
    whisk_whisk _ _ _ _ _ _ (whiskerOK_ob RD μ [l] [] []) ?_,
    whisk_congr_obj P β (U' := ob RD μ (s ++ [l] ++ [])) (V' := []) ?_ ?_]
  · simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  · refine Obj.ext ?_ ?_ <;> simp [ob_start, ob_word, wd_append, wt_append]
  · simp [wd_nil]
  · rw [ob_whisker RD μ [l] [] [] [] rfl]; exact whiskerOK_ob RD μ s [] [l]
  · exact (ob_whisker RD μ [l] [] [] [] rfl).symm
  · exact whiskerOK_ob RD μ s [] [l]
end Categorification.KL3.Diagram.CL

namespace Categorification.KLR.CyclotomicAction
open CategoryTheory TwoRep QuantumGroup KLRAlgebra StringDiagrams Diagrams.BicatInterp
open KL3.Diagram KLR.Diagram.MatEnd
universe u v w u₁
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)
attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

/-- Placing a factorization through a downward strand next to the vacuum to the right of `s`. -/
theorem plcLC_mem_vacFactor (s : List (Letter I)) {t t' : List (Letter I)} {f}
    (hf : f ∈ vacFactor hQ RD Λ t t') :
    CL.plcLC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) s [] t t' f ∈
      vacFactor hQ RD Λ (s ++ t ++ []) (s ++ t' ++ []) := by
  set P := CL.presCL RD k (univScalars hQ RD)
  set μ := vacWt RD Λ
  induction hf using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨t₀, i, hw, α, β, rfl⟩ := h
    have hw' : KL3.Diagram.wt RD (KL3.Diagram.wt RD μ []) (t₀ ++ [dn i]) =
        KL3.Diagram.wt RD (KL3.Diagram.wt RD μ []) t := hw
    by_cases ht : KL3.Diagram.wt RD (KL3.Diagram.wt RD μ []) t' =
        KL3.Diagram.wt RD (KL3.Diagram.wt RD μ []) t
    · erw [← CL.plcLC_comp P μ s [] hw' (ht.trans hw'.symm) α β]
      have hE : P.obj (ob RD μ (s ++ (t₀ ++ [dn i]) ++ [])) =
          P.obj (ob RD μ (s ++ t₀ ++ [dn i])) := by
        simp only [List.append_nil, List.append_assoc]
      refine Submodule.subset_span ⟨s ++ t₀, i, ?_,
        CL.plcLC P μ s [] _ _ α ≫ eqToHom hE,
        eqToHom hE.symm ≫ CL.plcLC P μ s [] _ _ β, ?_⟩
      · rw [List.append_nil, List.append_assoc, wt_append, hw, ← wt_append]
      · simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    · rw [CL.plcLC, dite_eq_right ht]; exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- `lin` commutes with finite sums. -/
theorem lin_sum' {a b : StringDiagrams.Obj (psig RD)} {ι : Type*} (T : Finset ι)
    (f : ι → StringDiagrams.LinDiagram k a b) :
    (CL.presCL RD k (univScalars hQ RD)).lin (∑ x ∈ T, f x) =
      ∑ x ∈ T, (CL.presCL RD k (univScalars hQ RD)).lin (f x) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Presentation.lin_add, ih]

/-- One term of the right curl relation placed to the right of `s`. -/
theorem plcLC_curlTerm (s : List (Letter I)) (c : I) (b : LEnd RD k (ob RD (vacWt RD Λ) []))
    (n : ℕ) :
    CL.plcLC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) s [] [up c] [up c]
      ((CL.presCL RD k (univScalars hQ RD)).lin (bubR RD k (vacWt RD Λ) [up c] b) ≫
        (CL.presCL RD k (univScalars hQ RD)).diag (dots RD (vacWt RD Λ) [] (up c) [] n)) =
      CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (s ++ [up c] ++ [])
          ((CL.presCL RD k (univScalars hQ RD)).lin b) ≫
        CL.dgC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (s ++ [up c] ++ [])
          (s ++ [up c] ++ []) (List.replicate n (s, .dot (up c), [])) := by
  set P := CL.presCL RD k (univScalars hQ RD)
  rw [← CL.plcLC_comp P _ s [] rfl rfl, CL.linC_bubR]
  erw [CL.plcLC_bubRC]
  congr 1
  rw [dots, ← CL.dgC_of]
  erw [CL.plcLC_dg]
  simp [List.map_replicate, whL]

/-- The coefficients of the universal cyclotomic polynomial act by fake bubbles. -/
theorem vacScal_coeff (c : I) (n : Fin (lam c)) :
    (vacScal hQ RD Λ ((-1) ^ (n.val + 1) * MvPolynomial.X ⟨c, n⟩)).val =
      (CL.presCL RD k (univScalars hQ RD)).lin
        (cwL RD k (vacWt RD Λ) c (((n.val + 1 : ℕ) : ℤ) - lam c - 1)) := by
  rw [map_mul, map_pow, map_neg, map_one, vacScal, MvPolynomial.aeval_X, vacScalGen]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, ← mul_assoc, ← mul_pow,
    neg_mul_neg, one_mul, one_pow]
  rfl

include hΛ in
/-- **The cyclotomic relation next to the vacuum, in context**: the universal cyclotomic
polynomial of colour `c` in the dot on the strand `E_c` next to the region of `P_∅`, with the
scalars acting by fake bubbles, lies in `I`. -/
theorem vacCurl_mem (s : List (Letter I)) (c : I) (S : List (Letter I))
    (hS : S = s ++ [up c] ++ []) :
    (show vacHom (k := k) hQ RD Λ S rfl ⟶ vacHom hQ RD Λ S rfl from
      CL.dgC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) S S
          (List.replicate (lam c) (s, .dot (up c), [])) +
        ∑ n : Fin (lam c), CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) S
            (vacScal hQ RD Λ ((-1) ^ (n.val + 1) * MvPolynomial.X ⟨c, n⟩)).val ≫
          CL.dgC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) S S
            (List.replicate (lam c - (n.val + 1)) (s, .dot (up c), []))) ∈
      vacIdeal hQ RD Λ _ _ := by
  subst hS
  have hip := ip_vacWt RD Λ hΛ c
  have hL : (-ip RD c (vacWt RD Λ) + 1).toNat = lam c + 1 := by omega
  have key :
      CL.dgC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (s ++ [up c] ++ [])
          (s ++ [up c] ++ []) (List.replicate (lam c) (s, .dot (up c), [])) +
        ∑ n : Fin (lam c), CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ)
            (s ++ [up c] ++ [])
            (vacScal hQ RD Λ ((-1) ^ (n.val + 1) * MvPolynomial.X ⟨c, n⟩)).val ≫
          CL.dgC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (s ++ [up c] ++ [])
            (s ++ [up c] ++ []) (List.replicate (lam c - (n.val + 1)) (s, .dot (up c), [])) =
      -CL.plcLC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) s [] [up c] [up c]
        ((CL.presCL RD k (univScalars hQ RD)).lin (curlRHS RD k c (vacWt RD Λ))) := by
    rw [curlRHS, Presentation.lin_neg, lin_sum', map_neg, map_sum, neg_neg, hL,
      Finset.sum_range_succ', add_comm (∑ _ ∈ _, _)]
    simp only [Presentation.lin_comp, Presentation.lin_of]
    congr 1
    · have h1 := cwL_vacWt_ip_sub_one hQ RD Λ hΛ c
      have h2 : CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ)
          (s ++ [up c] ++ []) (𝟙 _) = 𝟙 _ :=
        CLQ.bubAt_id RD k (univScalars hQ RD) (vacWt RD Λ) _
      rw [plcLC_curlTerm, Nat.cast_zero, add_zero,
        show (-ip RD c (vacWt RD Λ) - 0).toNat = lam c by omega, h1, h2, Category.id_comp]
    · rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [plcLC_curlTerm, vacScal_coeff, show ip RD c (vacWt RD Λ) - 1 + ((n.val + 1 : ℕ) : ℤ) =
          ((n.val + 1 : ℕ) : ℤ) - lam c - 1 by omega,
        show (-ip RD c (vacWt RD Λ) - ((n.val + 1 : ℕ) : ℤ)).toNat = lam c - (n.val + 1) by omega]
  change _ + _ ∈ _
  rw [key]
  refine neg_mem (mem_vacIdeal_of_mem_vacFactor hQ RD Λ rfl rfl ?_)
  exact plcLC_mem_vacFactor hQ RD Λ s
    (mem_vacFactor_of_mem_vacIdeal hQ RD Λ rfl rfl (curlRHS_mem_vacIdeal hQ RD Λ c))

end Categorification.KLR.CyclotomicAction
