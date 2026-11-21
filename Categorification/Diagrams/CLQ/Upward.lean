/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.Presentation
import Categorification.Diagrams.KLR.Comparison
import Categorification.Diagrams.KL3.Upward

/-!
# The KLR algebras act on upward strands of `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1:
the `R(ν)`-relations of Definition 3.1 are the relations of the KLR algebra `R(ν)` of KL II
(with `Q_ij = u^{d_ij} + v^{d_ji}`), imposed on upward strands. Hence for every weight `λ` there
is a homomorphism `R(ν) → END_U(E_ν 1_λ)` (KL III uses it, e.g. in §3.2 and §3.3).

## Main definitions and results

* `upFunctor RD k sc μ : (KLR pres).Presented ⥤ (pres RD k sc).Presented` — the linear functor that
  places a KLR diagram on upward strands with rightmost region `μ`; it is well defined because
  it kills every whiskered KLR relation (these are the relations `klr` of `U`) and every
  whiskered instance of the interchange law (by the interchange law of `U`).
* `upFunctor_obj`, `upFunctor_diag`: it sends the sequence `i` to `E_i 1_μ` and a KLR diagram to
  the same diagram on upward strands.
* `toUEnd RD k sc μ ν : R(ν) →ₐ[k] MatEnd (fun i => E_i 1_μ)` — the algebra homomorphism
  `R(ν) → ⨁_{i, j ∈ Seq ν} Hom_U(E_i 1_μ, E_j 1_μ) = END_U(E_ν 1_μ)` (the endomorphism algebra of
  `⨁_i E_i 1_μ`, as a matrix algebra), with `toUEnd_e`, `toUEnd_x`, `toUEnd_ψ`: it sends the
  idempotent `e(i)`, the dot `x_a` and the crossing `ψ_j` to the identity of `E_i 1_μ`, the dots
  and the crossings on upward strands.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-! ## Weights of upward sequences -/







/-! ## Whiskering -/

section Whisker

variable {RD}






end Whisker

/-! ## The functor -/

/-- The functor from the free 2-category of KLR diagrams placing them on upward strands with
rightmost region `μ`. -/
def upFree (μ : X) : Obj (KLR.Diagram.sig I) ⥤ (pres RD k sc).Presented where
  obj a := (pres RD k sc).obj (ob RD μ (ups a.word))
  map d := (pres RD k sc).diag (upDiag RD μ d)
  map_id a := by
    rw [← (pres RD k sc).diag_id]
    exact (pres RD k sc).diag_eq_of_layers_eq rfl
  map_comp f g := by
    rw [← (pres RD k sc).diag_comp]
    exact (pres RD k sc).diag_eq_of_layers_eq (by simp)

theorem freeLift_upFree (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) :
    (freeLift k (upFree RD k sc μ)).map f = (pres RD k sc).lin (upLin RD k μ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [upLin]
  | add f g hf hg => rw [Functor.map_add, hf, hg, upLin, upLin, upLin, Finsupp.mapDomain_add,
      lin_add]
  | single d r =>
    rw [freeLift_map_single, upLin, Finsupp.mapDomain_single, lin_single]
    rfl


variable {RD k sc}

/-- The KLR interchange law holds on upward strands: moving a generator on the right past a
generator on the left. -/
theorem upDiag_interchange (ν : X) (x : InterchangeData (KLR.Diagram.sig I)) (hx : x.Valid) :
    (pres RD k sc).diag (upDiag RD ν (InterchangeData.ghDiagram hx)) =
      (pres RD k sc).diag (upDiag RD ν (InterchangeData.hgDiagram hx)) := by
  set g' := upShape x.g
  set h' := upShape x.h
  set ν' := wt RD ν (ups x.mid ++ h'.dom)
  let L := lay RD ν' [] g' []
  let M := lay RD ν (ups x.mid) h' []
  have hLv := lay_valid RD ν' [] g' []
  have hMv := lay_valid RD ν (ups x.mid) h' []
  have hLd : L.dom = ob RD ν' g'.dom := by simpa using lay_dom RD ν' [] g' []
  have hLc : L.cod = ob RD ν' g'.cod := by simpa using lay_cod RD ν' [] g' []
  have hMd : M.dom = ob RD ν (ups x.mid ++ h'.dom) := by simpa using lay_dom RD ν (ups x.mid) h' []
  have hMc : M.cod = ob RD ν (ups x.mid ++ h'.cod) := by simpa using lay_cod RD ν (ups x.mid) h' []
  have hcomp : ∀ s t : List (Letter I), wt RD ν (ups x.mid ++ h'.dom) = wt RD ν t →
      (ob RD ν' s).Composable (ob RD ν t) := fun s t e =>
    ⟨ob_wf RD _ _, by rw [ob_endR, ob_start]; exact e, ob_wf RD _ _⟩
  have hwt : wt RD ν (ups x.mid ++ h'.dom) = wt RD ν (ups x.mid ++ h'.cod) := by
    rw [wt_append, wt_append, Shape.wt_dom_eq_wt_cod]
  have h : L.dom.Composable M.dom := by rw [hLd, hMd]; exact hcomp _ _ rfl
  have h₁ : L.cod.Composable M.dom := by rw [hLc, hMd]; exact hcomp _ _ rfl
  have h₂ : L.dom.Composable M.cod := by rw [hLd, hMc]; exact hcomp _ _ hwt
  have key := (pres RD k sc).diag_swap_layers_of_composable L M hLv hMv h h₁ h₂
  simp only [Diagram.oddCountList, Signature.IsEven.odd_eq_false, List.filter_cons,
    List.filter_nil, Bool.false_eq_true, ↓reduceIte, List.length_nil, mul_zero, pow_zero,
    one_smul] at key
  have hν' : ν' = wt RD (wt RD ν (ups (KLR.Diagram.Gen.dom x.h))) (ups x.mid) := by
    simp only [ν', h', upShape_dom, wt_append]
  have ha : ob RD ν (ups x.dom.word) = L.dom.tensor M.dom := by
    rw [hLd, hMd]
    refine Obj.ext ?_ ?_
    · simp only [InterchangeData.dom, ob_start, Obj.tensor_start, g', h', upShape_dom, ν',
        ups_append, List.append_assoc, wt_append]
    · simp only [InterchangeData.dom, ob_word, Obj.tensor_word, g', h', upShape_dom, ν',
        ups_append, List.append_assoc, wt_append, wd_append]
  have hb : ob RD ν (ups x.cod.word) = L.cod.tensor M.cod := by
    rw [hLc, hMc]
    have e : ν' = wt RD ν (ups x.mid ++ h'.cod) := hwt
    refine Obj.ext ?_ ?_
    · simp only [InterchangeData.cod, ob_start, Obj.tensor_start, e, g', h', upShape_cod,
        ups_append, List.append_assoc, wt_append]
    · simp only [InterchangeData.cod, ob_word, Obj.tensor_word, e, g', h', upShape_cod,
        ups_append, List.append_assoc, wt_append, wd_append]
  rw [(pres RD k sc).diag_eq_of_layers_eq' (upDiag RD ν (InterchangeData.ghDiagram hx))
      (Diagram.rwhisker (Diagram.ofLayer L hLv) M.dom h ≫
        Diagram.lwhisker L.cod (Diagram.ofLayer M hMv) h₁) ha hb ?e1,
    (pres RD k sc).diag_eq_of_layers_eq' (upDiag RD ν (InterchangeData.hgDiagram hx))
      (Diagram.lwhisker L.dom (Diagram.ofLayer M hMv) h ≫
        Diagram.rwhisker (Diagram.ofLayer L hLv) M.cod h₂) ha hb ?e2, key]
  case e1 =>
    simp only [layers_upDiag, InterchangeData.ghDiagram, Diagram.layers_mk, List.map_cons,
      List.map_nil, Diagram.layers_comp, Diagram.layers_rwhisker, Diagram.layers_lwhisker,
      Diagram.layers_ofLayer, List.cons_append, List.nil_append]
    rw [hMd, hLc]
    refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, rfl⟩⟩
    · refine Layer.ext ?_ ?_ ?_ ?_ <;>
        simp only [upLay, InterchangeData.gh₁, lay, Layer.wr, L, ν', g', h', ups_append,
          upShape_dom, List.nil_append, List.append_nil,
          List.map_nil, wt_append, wd_append, wd_nil, wt_nil, ob_word]
    · refine Layer.ext ?_ ?_ ?_ ?_ <;>
        simp only [upLay, InterchangeData.gh₂, lay, Layer.wl, M, ν', g', h', ups_append,
          upShape_dom, upShape_cod,List.append_assoc,
          List.append_nil, List.map_nil, wt_append, wd_append, wd_nil, wt_nil,
          ob_word, ob_start]
  case e2 =>
    simp only [layers_upDiag, InterchangeData.hgDiagram, Diagram.layers_mk, List.map_cons,
      List.map_nil, Diagram.layers_comp, Diagram.layers_rwhisker, Diagram.layers_lwhisker,
      Diagram.layers_ofLayer, List.cons_append, List.nil_append]
    rw [hMc, hLd]
    have ehc : wt RD ν (ups (KLR.Diagram.Gen.dom x.h)) = wt RD ν (ups (KLR.Diagram.Gen.cod x.h)) := by
      rw [← upShape_dom, ← upShape_cod]; exact Shape.wt_dom_eq_wt_cod _ _
    refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, rfl⟩⟩
    · refine Layer.ext ?_ ?_ ?_ ?_ <;>
        simp only [upLay, InterchangeData.hg₁, lay, Layer.wl, M, ν', g', h', ehc, ups_append,
          upShape_dom, List.append_assoc,
          List.append_nil, List.map_nil, wt_append, wd_append, wd_nil, wt_nil,
          ob_word, ob_start]
    · refine Layer.ext ?_ ?_ ?_ ?_ <;>
        simp only [upLay, InterchangeData.hg₂, lay, Layer.wr, L, ν', g', h', ehc, ups_append,
          upShape_dom, upShape_cod,
          List.nil_append, List.append_nil, List.map_nil, wt_append, wd_append, wd_nil, wt_nil,
          ob_word]

/-! ## The functor on the presented category -/

variable (RD k sc)





/-- The placement of KLR diagrams on upward strands kills the whiskered KLR relations (they are
relations of `U`) and the whiskered interchange law. -/
theorem upFree_respects (μ : X) :
    (KLR.Diagram.pres k (CL.qCL sc)).Respects (upFree RD k sc μ) where
  rel r u v hw := by
    rw [freeLift_upFree, upLin_whisker RD k μ _ u v hw (wsum_relation_cod RD r)]
    erw [← rel_klr]
    exact (pres RD k sc).lin_rel_cast (.inr (.klr (wt RD μ (ups v)) r)) _ _ _ _ _
  interchange x hx u v hw := by
    have hab : wsum RD x.cod.word = wsum RD x.dom.word := by
      simp only [InterchangeData.cod, InterchangeData.dom,
        wsum_append, wsum_gen_cod]
    rw [freeLift_upFree, upLin_whisker RD k μ _ u v hw hab, lin_cast, ← LinDiagram.whisk_of_ok,
      ← whisk_lin, InterchangeData.rel, upLin_sub, upLin_smul, upLin_of, upLin_of, lin_sub,
      lin_smul, lin_of, lin_of, upDiag_interchange]
    have hs : x.sign = 1 := by simp [InterchangeData.sign]
    simp [hs, whisk_zero]

/-- **The KLR 2-morphisms on upward strands.** The linear functor from the diagrammatic KLR
category (KL II relations, `Q = klQ2 k C`) to `U`, placing diagrams on upward strands with
rightmost region `μ`: the sequence `i` goes to `E_i 1_μ`. -/
def upFunctor (μ : X) : (KLR.Diagram.pres k (CL.qCL sc)).Presented ⥤ (pres RD k sc).Presented :=
  (KLR.Diagram.pres k (CL.qCL sc)).lift (upFree_respects RD k sc μ)

instance (μ : X) : (upFunctor RD k sc μ).Additive := by unfold upFunctor; infer_instance

instance (μ : X) : (upFunctor RD k sc μ).Linear k := by unfold upFunctor; infer_instance

@[simp] theorem upFunctor_obj (μ : X) (a : Obj (KLR.Diagram.sig I)) :
    (upFunctor RD k sc μ).obj ((KLR.Diagram.pres k (CL.qCL sc)).obj a) =
      (pres RD k sc).obj (ob RD μ (ups a.word)) := rfl

@[simp] theorem upFunctor_diag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    (upFunctor RD k sc μ).map ((KLR.Diagram.pres k (CL.qCL sc)).diag d) =
      (pres RD k sc).diag (upDiag RD μ d) :=
  (KLR.Diagram.pres k (CL.qCL sc)).lift_diag _ d

/-! ## `R(ν) → END_U(E_ν 1_λ)` -/

section MatEnd

open KLR.Diagram MatEnd

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] [Category 𝒟] [Preadditive 𝒟]
  [Linear k 𝒟] {ι : Type*} [Fintype ι] [DecidableEq ι]



end MatEnd

variable [DecidableEq I]

open KLR.Diagram in
/-- **`R(ν) → END_U(E_ν 1_μ)`**: the algebra homomorphism from the KLR algebra `R(ν)` of KL II
(`R2 k C ν`) to `⨁_{i, j ∈ Seq ν} Hom_U(E_i 1_μ, E_j 1_μ)` (the endomorphism algebra of
`⨁_i E_i 1_μ`, written as matrices of 2-morphisms), given by placing diagrams on upward strands.
It is the composite of the identification `R(ν) ≅ DiagR` (`diagREquiv`) with `upFunctor`. -/
def toUEnd (μ : X) (ν : Multiset I) :
    KLR.KLRAlgebra k (CL.qCL sc) ν →ₐ[k] MatEnd (fun i : KLR.Seq ν => (pres RD k sc).obj (ob RD μ (ups (word i)))) :=
  (matEndMap k (upFunctor RD k sc μ) _).comp (diagREquiv k (CL.qCL sc) ν).toAlgHom

open KLR.Diagram in
theorem toUEnd_e (μ : X) (ν : Multiset I) (i : KLR.Seq ν) :
    toUEnd RD k sc μ ν (KLR.KLRAlgebra.e i) = MatEnd.single i i (𝟙 _) := by
  rw [toUEnd]
  show matEndMap k (upFunctor RD k sc μ) _ (diagREquiv k _ ν (KLR.KLRAlgebra.e i)) = _
  rw [diagREquiv_e, DiagR.E, matEndMap_single, CategoryTheory.Functor.map_id]
  rfl

open KLR.Diagram in
theorem toUEnd_x (μ : X) (ν : Multiset I) (a : Fin (Multiset.card ν)) :
    toUEnd RD k sc μ ν (KLR.KLRAlgebra.x a) =
      ∑ i, MatEnd.single i i ((upFunctor RD k sc μ).map (dotE k (CL.qCL sc) i a)) := by
  rw [toUEnd]
  show matEndMap k (upFunctor RD k sc μ) _ (diagREquiv k _ ν (KLR.KLRAlgebra.x a)) = _
  rw [diagREquiv_x, DiagR.X, map_sum]
  exact Finset.sum_congr rfl fun i _ => matEndMap_single k (upFunctor RD k sc μ) _ i i _

open KLR.Diagram in
theorem toUEnd_ψ (μ : X) (ν : Multiset I) (j : ℕ) :
    toUEnd RD k sc μ ν (KLR.KLRAlgebra.ψ j) =
      ∑ i, MatEnd.single i (TypeA.sadj (Multiset.card ν) j • i)
        ((upFunctor RD k sc μ).map (crossE k (CL.qCL sc) i j)) := by
  rw [toUEnd]
  show matEndMap k (upFunctor RD k sc μ) _ (diagREquiv k _ ν (KLR.KLRAlgebra.ψ j)) = _
  rw [diagREquiv_ψ, DiagR.Ψ, map_sum]
  exact Finset.sum_congr rfl fun i _ => matEndMap_single k (upFunctor RD k sc μ) _ i _ _

end Categorification.KL3.Diagram.CLQ
