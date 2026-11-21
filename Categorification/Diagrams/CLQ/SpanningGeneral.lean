/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.Lemma39
import Categorification.Diagrams.CL.SpanningDefs
import Categorification.Diagrams.CL.RescaleBicat

/-!
# KL III Proposition 3.10 for `U_Q(g)` with arbitrary scalars

M. Khovanov, A. D. Lauda, *A categorification of quantum sl(n)* (KL III), arXiv:0807.3250v1,
Proposition 3.10, for `U_Q(g)` of S. Cautis, A. D. Lauda, arXiv:1111.1431v3, Definition 1.1,
with arbitrary scalars `S` (`t`, `r` and the bubble-slide scalars `s`): every 2-morphism
`E_s 1_μ ⟶ E_t 1_μ` between upward sequences is a linear combination of upward diagrams followed
by bubble monomials on the far right (`CL.Prop310UpC`).

For `S.withRone` (`r = 1`) this is `CLQ.prop310`, the argument of KL III Lemma 3.9 carried out
in `Categorification.Diagrams.CLQ`. A general `S` reduces to `S.withRone` by the isomorphism
`CL.equivWithRone` (CL, Remark after `eq_r3_hard-gen`, item 1), which rescales every diagram by
a unit; such rescalings preserve the spans of upward diagrams with bubbles on the far right.

## Main results

* `CLQ.upSpans_pres`: `UpSpans (pres RD k S) μ ν`, i.e. `CL.Prop310UpC RD k S.withRone μ ν`.
* `CL.Rescale.functor_mem_upSpanC`, `CL.Rescale.functor_mem_dnSpanC`: rescaling functors
  preserve `upSpanC` and `dnSpanC`.
* `CL.prop310UpC`: **KL III Proposition 3.10** (upward strands) for `U_Q(g)` with arbitrary
  scalars `S`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section


universe w u v

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] {sc : CL.CLScalars C k}

theorem dg_eq_dgC (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    dg RD k sc μ s t ls = CL.dgC (pres RD k sc) μ s t ls := rfl

theorem bubAt_eq_bubAtC (μ : X) (s : List (Letter I)) :
    bubAt RD k sc μ s = CL.bubAtC (pres RD k sc) μ s := rfl

theorem bubGenC_pres (lam : X) (i : I) (n : ℕ) :
    CL.bubGenC (pres RD k sc) lam i n = bubGen RD k sc lam i (n + 1) := by
  unfold CL.bubGenC bubGen
  split_ifs with h
  · rw [← dg_eq_dgC, show ip RD i lam - 1 + ((n + 1 : ℕ) : ℤ) =
      (((ip RD i lam).toNat + n : ℕ) : ℤ) by push_cast; omega, cwU_of_nonneg]
  · rw [← dg_eq_dgC, show -ip RD i lam - 1 + ((n + 1 : ℕ) : ℤ) =
      (((-ip RD i lam).toNat + n : ℕ) : ℤ) by push_cast; omega, ccwU_of_nonneg]

theorem isBubC_pres {lam : X} {x : End ((pres RD k sc).obj (ob RD lam []))}
    (hx : IsBub RD k sc lam x) : CL.IsBubC (pres RD k sc) lam x := by
  obtain ⟨p, hp⟩ := hx
  have key : ∀ q : PiLam I k, CL.IsBubC (pres RD k sc) lam (bubMap RD k sc lam q).val := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [show bubMap RD k sc lam (MvPolynomial.C a) = algebraMap k (EndOne RD k sc lam) a from
        MvPolynomial.aeval_C _ _, EndOne.val_algebraMap]
      exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) a
    | add p q hp hq => rw [map_add, EndOne.val_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p n hp =>
      rw [map_mul, EndOne.val_mul]
      refine Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨n, ?_⟩)
      rw [show bubMap RD k sc lam (MvPolynomial.X n) =
        EndOne.of (bubGen RD k sc lam n.1 (n.2 + 1)) from MvPolynomial.aeval_X _ _, EndOne.val_of]
      exact bubGenC_pres _ _ _
  have := key p
  rwa [show bubMap RD k sc lam p = EndOne.of x from hp, EndOne.val_of] at this

theorem upSpan_le_upSpanC (μ : X) (S T : List (Letter I)) :
    upSpan RD k sc μ S T ≤ CL.upSpanC (pres RD k sc) μ S T := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨A, γ, hA, hc, hγ, rfl⟩
  exact Submodule.subset_span ⟨A, γ, hA, hc, isBubC_pres hγ, rfl⟩

/-- **KL III Proposition 3.10** (upward strands) for `U_Q(g)` with the scalars `S.withRone`. -/
theorem upSpans_pres [DecidableEq I] (μ : X) (ν : Multiset I) :
    CL.UpSpans (pres RD k sc) μ ν :=
  fun s t f => upSpan_le_upSpanC μ _ _
    ((prop310_iff_upSpan RD k sc μ ν).1 (prop310 (RD := RD) (k := k) (sc := sc) μ ν) s t f)

end Categorification.KL3.Diagram.CLQ

namespace Categorification.KL3.Diagram.CL.Rescale

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]
  {P P' : Presentation.{w, max u v} (psig RD) k} {χ : (psig RD).Gen → kˣ}
  (h : ∀ i, P'.lin (scL χ (P.rel i)) = 0)

include h

theorem functor_dgC (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    ∃ c : k, (functor χ h).map (dgC P μ s t ls) = c • dgC P' μ s t ls := by
  by_cases hc : SChain s ls t
  · rw [dgC_of hc, functor_diag, dgC_of hc]
    exact ⟨_, rfl⟩
  · refine ⟨1, ?_⟩
    rw [dgC_of_not hc, Functor.map_zero, dgC_of_not hc, smul_zero]

theorem functor_dgC_nil (μ : X) (s t : List (Letter I)) :
    (functor χ h).map (dgC P μ s t []) = dgC P' μ s t [] := by
  by_cases hc : SChain s [] t
  · rw [dgC_of hc, functor_diag, dgC_of hc]
    simp [layers_mkD, layList]
  · rw [dgC_of_not hc, Functor.map_zero, dgC_of_not hc]

theorem functor_plcLC (μ : X) (u v s t : List (Letter I))
    (f : P.obj (ob RD (wt RD μ v) s) ⟶ P.obj (ob RD (wt RD μ v) t)) :
    (functor χ h).map (plcLC P μ u v s t f) = plcLC P' μ u v s t ((functor χ h).map f) := by
  unfold plcLC
  split_ifs with hst
  · simp only [plcC, LinearMap.coe_mk, AddHom.coe_mk, Functor.map_comp]
    rw [functor_eqToHom h, functor_eqToHom h, functor_whisk]
    · exact ob_whisker RD μ u v s t hst
    · exact (ob_whisker RD μ u v s s rfl).symm
  · simp

theorem functor_bubAtC (μ : X) (T : List (Letter I)) (γ : End (P.obj (ob RD μ []))) :
    (functor χ h).map (bubAtC P μ T γ) = bubAtC P' μ T ((functor χ h).map γ) := by
  show (functor χ h).map (dgC P μ T (T ++ [] ++ []) [] ≫ plcLC P μ T [] [] [] γ ≫
      dgC P μ (T ++ [] ++ []) T []) =
    dgC P' μ T (T ++ [] ++ []) [] ≫ plcLC P' μ T [] [] [] ((functor χ h).map γ) ≫
      dgC P' μ (T ++ [] ++ []) T []
  rw [Functor.map_comp, Functor.map_comp, functor_dgC_nil h, functor_dgC_nil h, functor_plcLC h]

/-- The rescaling functor on the endomorphism algebra of an object. -/
def endAlgHom (a : Obj (psig RD)) : End (P.obj a) →ₐ[k] End (P'.obj a) where
  toFun x := (functor χ h).map x
  map_one' := (functor χ h).map_id _
  map_mul' x y := (functor χ h).map_comp y x
  map_zero' := Functor.map_zero _ _ _
  map_add' x y := (functor χ h).map_add
  commutes' r := by
    show (functor χ h).map (algebraMap k (End (P.obj a)) r) = algebraMap k (End (P'.obj a)) r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Functor.map_smul]
    exact congrArg (r • ·) ((functor χ h).map_id _)

theorem endAlgHom_apply (a : Obj (psig RD)) (x : End (P.obj a)) :
    endAlgHom h a x = (functor χ h).map x := rfl

theorem functor_isBubC {lam : X} {γ : End (P.obj (ob RD lam []))} (hγ : IsBubC P lam γ) :
    IsBubC P' lam ((functor χ h).map γ) := by
  unfold IsBubC at hγ ⊢
  rw [← endAlgHom_apply h]
  have hmem : endAlgHom h (ob RD lam []) γ ∈ (Algebra.adjoin k _).map (endAlgHom h (ob RD lam [])) :=
    Subalgebra.mem_map.mpr ⟨γ, hγ, rfl⟩
  rw [AlgHom.map_adjoin] at hmem
  refine Algebra.adjoin_le ?_ hmem
  rintro _ ⟨_, ⟨⟨i, n⟩, rfl⟩, rfl⟩
  show endAlgHom h (ob RD lam []) (bubGenC P lam i n) ∈
    Algebra.adjoin k (Set.range fun p : I × ℕ => bubGenC P' lam p.1 p.2)
  rw [endAlgHom_apply]
  by_cases hi : 0 ≤ ip RD i lam
  · rw [bubGenC, ite_eq_left hi]
    obtain ⟨c, hc⟩ := functor_dgC h lam [] [] (cwLs i ((ip RD i lam).toNat + n))
    rw [hc, show dgC P' lam [] [] (cwLs i ((ip RD i lam).toNat + n)) = bubGenC P' lam i n by
      rw [bubGenC, ite_eq_left hi]]
    exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range.mpr ⟨(i, n), rfl⟩)) c
  · rw [bubGenC, ite_eq_right hi]
    obtain ⟨c, hc⟩ := functor_dgC h lam [] [] (ccwLs i ((-ip RD i lam).toNat + n))
    rw [hc, show dgC P' lam [] [] (ccwLs i ((-ip RD i lam).toNat + n)) = bubGenC P' lam i n by
      rw [bubGenC, ite_eq_right hi]]
    exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range.mpr ⟨(i, n), rfl⟩)) c

/-- Rescaling functors preserve the span of upward diagrams followed by bubble monomials on the
far right. -/
theorem functor_mem_upSpanC {μ : X} {S T : List (Letter I)} {f : P.obj (ob RD μ S) ⟶ P.obj (ob RD μ T)}
    (hf : f ∈ upSpanC P μ S T) : (functor χ h).map f ∈ upSpanC P' μ S T := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, γ, hA, hc, hγ, rfl⟩ := hf
    obtain ⟨c, hc'⟩ := functor_dgC h μ S T A
    rw [Functor.map_comp, hc', functor_bubAtC h, Linear.smul_comp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨A, _, hA, hc, functor_isBubC h hγ, rfl⟩)
  | zero => rw [Functor.map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Functor.map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Functor.map_smul]; exact Submodule.smul_mem _ _ hx

/-- Rescaling functors preserve the span of downward diagrams followed by bubble monomials on the
far right. -/
theorem functor_mem_dnSpanC {μ : X} {S T : List (Letter I)} {f : P.obj (ob RD μ S) ⟶ P.obj (ob RD μ T)}
    (hf : f ∈ dnSpanC P μ S T) : (functor χ h).map f ∈ dnSpanC P' μ S T := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, γ, hA, hc, hγ, rfl⟩ := hf
    obtain ⟨c, hc'⟩ := functor_dgC h μ S T A
    rw [Functor.map_comp, hc', functor_bubAtC h, Linear.smul_comp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨A, _, hA, hc, functor_isBubC h hγ, rfl⟩)
  | zero => rw [Functor.map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Functor.map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Functor.map_smul]; exact Submodule.smul_mem _ _ hx

end Categorification.KL3.Diagram.CL.Rescale

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

/-- `UpSpans` is invariant under the isomorphism `U_S(g) ≅ U_{S.withRone}(g)` of
`equivWithRone`. -/
theorem upSpans_of_withRone [DecidableEq I] (S : CLScalars C k) {μ : X} {ν : Multiset I}
    (H : UpSpans (presCL RD k S.withRone) μ ν) : UpSpans (presCL RD k S) μ ν := by
  intro s t f
  have h := (RescaleDatum.rDatum (RD := RD) S).lin_scL_rel' S (RescaleDatum.rDatum_mapScalars S)
  have h' := (RescaleDatum.rDatum (RD := RD) S).lin_scL_rel_inv S
    (RescaleDatum.rDatum_mapScalars S)
  have key := Rescale.functor_mem_upSpanC h' (H s t ((Rescale.functor _ h).map f))
  rwa [Rescale.functor_inv_functor h h' (RescaleDatum.rDatum S).chi_inv] at key

/-- `DnSpans` is invariant under the isomorphism `U_S(g) ≅ U_{S.withRone}(g)` of
`equivWithRone`. -/
theorem dnSpans_of_withRone [DecidableEq I] (S : CLScalars C k) {μ : X} {ν : Multiset I}
    (H : DnSpans (presCL RD k S.withRone) μ ν) : DnSpans (presCL RD k S) μ ν := by
  intro s t f
  have h := (RescaleDatum.rDatum (RD := RD) S).lin_scL_rel' S (RescaleDatum.rDatum_mapScalars S)
  have h' := (RescaleDatum.rDatum (RD := RD) S).lin_scL_rel_inv S
    (RescaleDatum.rDatum_mapScalars S)
  have key := Rescale.functor_mem_dnSpanC h' (H s t ((Rescale.functor _ h).map f))
  rwa [Rescale.functor_inv_functor h h' (RescaleDatum.rDatum S).chi_inv] at key

/-- **KL III Proposition 3.10** (arXiv:0807.3250v1; upward strands) for `U_Q(g)` of
CL arXiv:1111.1431v3, Definition 1.1, with arbitrary scalars `S`: every 2-morphism
`E_s 1_μ ⟶ E_t 1_μ` (`s, t ∈ Seq ν`) is a linear combination of upward diagrams followed by
bubble monomials on the far right, so `R(ν) ⊗ Π_μ → END_{U_Q(g)}(E_ν 1_μ)` is surjective. -/
theorem prop310UpC [DecidableEq I] (S : CLScalars C k) (μ : X) (ν : Multiset I) :
    Prop310UpC RD k S μ ν :=
  upSpans_of_withRone S (CLQ.upSpans_pres (sc := S) μ ν)

end Categorification.KL3.Diagram.CL
