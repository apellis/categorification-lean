/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.SlideCalculusC
import Categorification.Diagrams.CL.Presentation

/-!
# `U_Q(g)` without the mixed relations

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.1 and §2. The presentation `presNM RD k S` has the generators of
`U_Q(g)` (`presCL`) and all its relations except the *mixed* ones: the left rotation of a crossing
with distinct labels (`cycCrossL j i`, `j ≠ i`, `eq_almost_cyclic`) and the relations
`downupEF`, `downupFE` (`sec:mixedrels`). These are the relations that follow from the invertibility
of the sideways crossings for distinct labels (R. Rouquier, arXiv:0812.5023v1, §4.1.3;
J. Brundan, arXiv:1501.00350v1, §5), and `presNM` is the setting in which the diagrammatic part of
that argument is carried out.

## Main definitions and results

* `nonMixed`, `presNM`, `presNM_zigzags`, `presNM_lin_rel`;
* the KLR relations on upward strands, for any presentation `P` on `psig RD` in which the KLR
  relations for polynomials `Q` hold (`KLRHolds`): the functor `upFunctorC` from the KLR
  category, and the normal forms `dgC_slideRNe`, `dgC_slideLNe`, `dgC_sqEq`, `dgC_slideREq`,
  `dgC_slideLEq`, `dgC_braid`, `dgC_braidQ`, `dgC_sqNe`;
* for `presNM` (with `r_i = 1`): `presNM_klr`, and the normal forms of the dot cyclicity
  (`dgN_cycDotL`, `dgN_cycDotR`), the bubbles (`dgN_ccwNeg`, `dgN_cwNeg`, `dgN_ccwOne`,
  `dgN_cwOne`), the curls (`dgN_curlL`, `dgN_curlR`) and the decompositions (`dgN_decompEF`,
  `dgN_decompFE`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## The KLR relations on upward strands of a presentation -/

section Upward

variable (P : Presentation.{w, max u v} (psig RD) k) (Q : I → I → MvPolynomial (Fin 2) k)

/-- The KLR relations for the polynomials `Q` (`KLR.Diagram.relation k Q`) hold on upward strands
of `P`, for every rightmost region. -/
def KLRHolds : Prop :=
  ∀ (μ : X) (r : KLR.Diagram.Rel I), P.lin (upLin RD k μ (KLR.Diagram.relation k Q r)) = 0

/-- Placing KLR diagrams on upward strands of `P` with rightmost region `μ`. -/
def upFreeC (μ : X) : Obj (KLR.Diagram.sig I) ⥤ P.Presented where
  obj a := P.obj (ob RD μ (ups a.word))
  map d := P.diag (upDiag RD μ d)
  map_id a := by
    rw [← P.diag_id]
    exact P.diag_eq_of_layers_eq rfl
  map_comp f g := by
    rw [← P.diag_comp]
    exact P.diag_eq_of_layers_eq (by simp)

theorem freeLift_upFreeC (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) :
    (freeLift k (upFreeC P μ)).map f = P.lin (upLin RD k μ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [upLin]
  | add f g hf hg => rw [Functor.map_add, hf, hg, upLin, upLin, upLin, Finsupp.mapDomain_add,
      lin_add]
  | single d r =>
    rw [freeLift_map_single, upLin, Finsupp.mapDomain_single, lin_single]
    rfl

variable {P} in
/-- The KLR interchange law holds on upward strands of any presentation (by its interchange
law). -/
theorem upDiag_interchangeC (ν : X) (x : InterchangeData (KLR.Diagram.sig I)) (hx : x.Valid) :
    P.diag (upDiag RD ν (InterchangeData.ghDiagram hx)) =
      P.diag (upDiag RD ν (InterchangeData.hgDiagram hx)) := by
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
  have key := P.diag_swap_layers_of_composable L M hLv hMv h h₁ h₂
  simp only [Diagram.oddCountList, Signature.IsEven.odd_eq_false, List.filter_cons,
    List.filter_nil, Bool.false_eq_true, ↓reduceIte, List.length_nil, mul_zero, pow_zero,
    one_smul] at key
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
  rw [P.diag_eq_of_layers_eq' (upDiag RD ν (InterchangeData.ghDiagram hx))
      (Diagram.rwhisker (Diagram.ofLayer L hLv) M.dom h ≫
        Diagram.lwhisker L.cod (Diagram.ofLayer M hMv) h₁) ha hb ?e1,
    P.diag_eq_of_layers_eq' (upDiag RD ν (InterchangeData.hgDiagram hx))
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

variable {P Q}

theorem lin_castC {a b a' b' : Obj (psig RD)} (f : LinDiagram k a b) (ha : a = a') (hb : b = b') :
    P.lin (LinDiagram.cast f ha hb) =
      eqToHom (congrArg P.obj ha).symm ≫ P.lin f ≫ eqToHom (congrArg P.obj hb) := by
  subst ha hb; simp

/-- Placing KLR diagrams on upward strands kills the whiskered KLR relations and the whiskered
interchange law. -/
theorem upFreeC_respects (hK : KLRHolds P Q) (μ : X) :
    (KLR.Diagram.pres k Q).Respects (upFreeC P μ) where
  rel r u v hw := by
    rw [freeLift_upFreeC, upLin_whisker RD k μ _ u v hw (wsum_relation_cod RD r), lin_castC,
      ← LinDiagram.whisk_of_ok _ (wU_ok μ _ u v), ← whisk_lin]
    change _ ≫ P.whisk (P.lin (upLin RD k (wt RD μ (ups v)) (KLR.Diagram.relation k Q r))) _ _ ≫
      _ = 0
    rw [hK, whisk_zero, Limits.zero_comp, Limits.comp_zero]
  interchange x hx u v hw := by
    have hab : wsum RD x.cod.word = wsum RD x.dom.word := by
      simp only [InterchangeData.cod, InterchangeData.dom,
        wsum_append, wsum_gen_cod]
    rw [freeLift_upFreeC, upLin_whisker RD k μ _ u v hw hab, lin_castC, ← LinDiagram.whisk_of_ok,
      ← whisk_lin, InterchangeData.rel, upLin_sub, upLin_smul, upLin_of, upLin_of, lin_sub,
      lin_smul, lin_of, lin_of, upDiag_interchangeC]
    have hs : x.sign = 1 := by simp [InterchangeData.sign]
    simp [hs, whisk_zero]

variable (P Q) in
/-- **The KLR 2-morphisms on upward strands** of `P`: the linear functor from the diagrammatic
KLR category for `Q` to `P`, placing diagrams on upward strands with rightmost region `μ`. -/
def upFunctorC (hK : KLRHolds P Q) (μ : X) : (KLR.Diagram.pres k Q).Presented ⥤ P.Presented :=
  (KLR.Diagram.pres k Q).lift (upFreeC_respects hK μ)

instance (hK : KLRHolds P Q) (μ : X) : (upFunctorC P Q hK μ).Additive := by
  unfold upFunctorC; infer_instance

instance (hK : KLRHolds P Q) (μ : X) : (upFunctorC P Q hK μ).Linear k := by
  unfold upFunctorC; infer_instance

@[simp] theorem upFunctorC_diag (hK : KLRHolds P Q) (μ : X) {a b : Obj (KLR.Diagram.sig I)}
    (d : a ⟶ b) :
    (upFunctorC P Q hK μ).map ((KLR.Diagram.pres k Q).diag d) = P.diag (upDiag RD μ d) :=
  (KLR.Diagram.pres k Q).lift_diag _ d

variable (P) in
theorem upDiag_eq_dgC (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    P.diag (upDiag RD μ d) =
      dgC P μ (ups a.word) (ups b.word) ((Diagram.layers d).map upLD) := by
  rw [dgC_of (sChain_upLD (Diagram.chain d))]
  exact P.diag_eq_of_layers_eq (by simp [layList, upLay, upLD, List.map_map])

variable (hK : KLRHolds P Q)
include hK

/-- The upward dot slide `ψ x₀ = x₁ ψ` for `c ≠ d`: a dot on the left strand of `E_c E_d` moves
up through the crossing to the right strand. -/
theorem dgC_slideRNe (μ : X) (c d : I) (h : c ≠ d) :
    dgC P μ [up c, up d] [up d, up c] [([], .dot (up c), [up d]), ([], .cross true c d, [])] =
      dgC P μ [up c, up d] [up d, up c] [([], .cross true c d, []), ([up d], .dot (up c), [])] := by
  have key := (KLR.Diagram.pres k Q).diag_eq_of_rel (.slideRNe c d h) rfl
  have key' := congrArg (upFunctorC P Q hK μ).map key
  rw [upFunctorC_diag, upFunctorC_diag, upDiag_eq_dgC, upDiag_eq_dgC] at key'
  exact key'

/-- The upward dot slide `x₀ ψ = ψ x₁` for `c ≠ d`: a dot on the right strand of `E_c E_d` moves
up through the crossing to the left strand. -/
theorem dgC_slideLNe (μ : X) (c d : I) (h : c ≠ d) :
    dgC P μ [up c, up d] [up d, up c] [([], .cross true c d, []), ([], .dot (up d), [up c])] =
      dgC P μ [up c, up d] [up d, up c] [([up c], .dot (up d), []), ([], .cross true c d, [])] := by
  have key := (KLR.Diagram.pres k Q).diag_eq_of_rel (.slideLNe c d h) rfl
  have key' := congrArg (upFunctorC P Q hK μ).map key
  rw [upFunctorC_diag, upFunctorC_diag, upDiag_eq_dgC, upDiag_eq_dgC] at key'
  exact key'

/-- `ψ² = 0` on `E_c E_c`. -/
theorem dgC_sqEq (μ : X) (c : I) :
    dgC P μ [up c, up c] [up c, up c] [([], .cross true c c, []), ([], .cross true c c, [])] = 0 := by
  have key := KLR.Diagram.sqEq_at Q (u := []) (v := [])
    (KLR.Diagram.X2 c c ≫ KLR.Diagram.X2 c c) rfl
  have key' := congrArg (upFunctorC P Q hK μ).map key
  rw [upFunctorC_diag, Functor.map_zero, upDiag_eq_dgC] at key'
  exact key'

/-- The nilHecke dot slide `x₁ ψ = ψ x₂ + 1` on `E_c E_c`. -/
theorem dgC_slideREq (μ : X) (c : I) :
    dgC P μ [up c, up c] [up c, up c] [([], .dot (up c), [up c]), ([], .cross true c c, [])] =
      dgC P μ [up c, up c] [up c, up c] [([], .cross true c c, []), ([up c], .dot (up c), [])] +
        dgC P μ [up c, up c] [up c, up c] [] := by
  have key := KLR.Diagram.slideREq_at Q (u := []) (v := [])
    (KLR.Diagram.D0 c c ≫ KLR.Diagram.X2 c c) (KLR.Diagram.X2 c c ≫ KLR.Diagram.D1 c c) rfl rfl
  have key' := congrArg (upFunctorC P Q hK μ).map key
  rw [Functor.map_sub, upFunctorC_diag, upFunctorC_diag, CategoryTheory.Functor.map_id,
    upDiag_eq_dgC, upDiag_eq_dgC] at key'
  rw [dgC_nil]
  exact sub_eq_iff_eq_add'.mp key'

/-- The nilHecke dot slide `ψ x₁ = x₂ ψ + 1` on `E_c E_c`. -/
theorem dgC_slideLEq (μ : X) (c : I) :
    dgC P μ [up c, up c] [up c, up c] [([], .cross true c c, []), ([], .dot (up c), [up c])] =
      dgC P μ [up c, up c] [up c, up c] [([up c], .dot (up c), []), ([], .cross true c c, [])] +
        dgC P μ [up c, up c] [up c, up c] [] := by
  have key := KLR.Diagram.slideLEq_at Q (u := []) (v := [])
    (KLR.Diagram.X2 c c ≫ KLR.Diagram.D0 c c) (KLR.Diagram.D1 c c ≫ KLR.Diagram.X2 c c) rfl rfl
  have key' := congrArg (upFunctorC P Q hK μ).map key
  rw [Functor.map_sub, upFunctorC_diag, upFunctorC_diag, CategoryTheory.Functor.map_id,
    upDiag_eq_dgC, upDiag_eq_dgC] at key'
  rw [dgC_nil]
  exact sub_eq_iff_eq_add'.mp key'

/-- The braid relation `ψ₀ψ₁ψ₀ = ψ₁ψ₀ψ₁` on upward strands `E_c E_d E_e`, unless `c = e ≠ d`. -/
theorem dgC_braid (μ : X) (c d e : I) (h : ¬ (c = e ∧ c ≠ d)) :
    dgC P μ [up c, up d, up e] [up e, up d, up c]
        [([], .cross true c d, [up e]), ([up d], .cross true c e, []),
          ([], .cross true d e, [up c])] =
      dgC P μ [up c, up d, up e] [up e, up d, up c]
        [([up c], .cross true d e, []), ([], .cross true c e, [up d]),
          ([up e], .cross true c d, [])] := by
  have key := (KLR.Diagram.pres k Q).diag_eq_of_rel (.braid c d e h) rfl
  have key' := congrArg (upFunctorC P Q hK μ).map key
  rw [upFunctorC_diag, upFunctorC_diag, upDiag_eq_dgC, upDiag_eq_dgC] at key'
  exact key'

/-- The quadratic relation on `E_c E_d`, `c ≠ d`: the double crossing is `Q_{cd}(x₀, x₁)`, the
dot `x₀` on the left strand, `x₁` on the right one. -/
theorem dgC_sqNe (μ : X) (c d : I) (h : c ≠ d) :
    dgC P μ [up c, up d] [up c, up d] [([], .cross true c d, []), ([], .cross true d c, [])] =
      KLR.ncEval (A := End (P.obj (ob RD μ [up c, up d])))
        ![dgC P μ [up c, up d] [up c, up d] [([], .dot (up c), [up d])],
          dgC P μ [up c, up d] [up c, up d] [([up c], .dot (up d), [])]] (Q c d) := by
  have key := KLR.Diagram.sqNe_at Q (u := []) (v := []) h
    (KLR.Diagram.X2 c d ≫ KLR.Diagram.X2 d c) (KLR.Diagram.D0 c d) (KLR.Diagram.D1 c d) rfl rfl rfl
  have key' := congrArg (functorEndAlg k (upFunctorC P Q hK μ) _) key
  rw [AlgHom.map_ncEval] at key'
  simp only [functorEndAlg, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    upFunctorC_diag] at key'
  rw [upDiag_eq_dgC] at key'
  refine key'.trans ?_
  congr 1
  funext a; fin_cases a
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, upFunctorC_diag, upDiag_eq_dgC]; rfl
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      upFunctorC_diag, upDiag_eq_dgC]
    rfl

/-- The deformed braid relation on `E_c E_d E_c`, `c ≠ d`:
`ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁ = Q̄_{cd}(x₀, x₁, x₂)`. -/
theorem dgC_braidQ (μ : X) (c d : I) (h : c ≠ d) :
    dgC P μ [up c, up d, up c] [up c, up d, up c]
        [([], .cross true c d, [up c]), ([up d], .cross true c c, []),
          ([], .cross true d c, [up c])] -
      dgC P μ [up c, up d, up c] [up c, up d, up c]
        [([up c], .cross true d c, []), ([], .cross true c c, [up d]),
          ([up c], .cross true c d, [])] =
      KLR.ncEval (A := End (P.obj (ob RD μ [up c, up d, up c])))
        ![dgC P μ [up c, up d, up c] [up c, up d, up c] [([], .dot (up c), [up d, up c])],
          dgC P μ [up c, up d, up c] [up c, up d, up c] [([up c], .dot (up d), [up c])],
          dgC P μ [up c, up d, up c] [up c, up d, up c] [([up c, up d], .dot (up c), [])]]
        (KLR.qbar (Q c d)) := by
  have key := KLR.Diagram.braidQ_at Q (u := []) (v := []) h
    (KLR.Diagram.braidL c d c) (KLR.Diagram.braidR c d c)
    (KLR.Diagram.E0 c d c) (KLR.Diagram.E1 c d c) (KLR.Diagram.E2 c d c) rfl rfl rfl rfl rfl
  have key' := congrArg (functorEndAlg k (upFunctorC P Q hK μ) _) key
  rw [map_sub, AlgHom.map_ncEval] at key'
  simp only [functorEndAlg, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    upFunctorC_diag] at key'
  rw [upDiag_eq_dgC, upDiag_eq_dgC] at key'
  refine key'.trans ?_
  congr 1
  funext a; fin_cases a <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      upFunctorC_diag, upDiag_eq_dgC] <;> rfl

end Upward

/-! ## The presentation without the mixed relations -/

section NoMix

variable (RD k)

/-- The relations of `presCL` other than the mixed ones: all except `cycCrossL j i` with
`j ≠ i`, `downupEF` and `downupFE`. -/
def nonMixed : Rel RD → Prop
  | .cycCrossL j i _ => j = i
  | .downupEF _ _ _ _ => False
  | .downupFE _ _ _ _ => False
  | _ => True

/-- **`U_Q(g)` without the mixed relations**: the pivotal base of `U` with the relations of
`presCL` other than the mixed ones (`nonMixed`). -/
def presNM (S : CLScalars C k) : Presentation.{w, max u v} (psig RD) k :=
  ((pres0 RD k).pivotal (inv RD).toColourDuality).addRels {r : Rel RD // nonMixed RD r}
    (fun r => r.1.dom) (fun r => r.1.cod) (fun r => relationCL RD k S r.1)

variable (S : CLScalars C k)

/-- Biadjointness (the zigzag relations) holds in `presNM`. -/
theorem presNM_zigzags : (presNM RD k S).PivotalZigzags (inv RD).toColourDuality :=
  Presentation.pivotal_addRels_zigzags (inv RD).toColourDuality (pres0 RD k) _ _ _ _

variable {RD k}

theorem presNM_lin_rel (r : Rel RD) (h : nonMixed RD r) :
    (presNM RD k S).lin (relationCL RD k S r) = 0 :=
  (presNM RD k S).lin_rel_self (.inr ⟨r, h⟩)

variable {S} (hr : ∀ c, S.r c = 1)
include hr

/-- With `r_i = 1`, the KLR relations for `Q = qCL S` hold on upward strands of `presNM`. -/
theorem presNM_klr : KLRHolds (presNM RD k S) (qCL S) := by
  intro μ r
  have hr' : (fun c => (S.r c : k)) = fun _ => 1 := by funext c; rw [hr c, Units.val_one]
  have h := presNM_lin_rel (RD := RD) S (.klr μ r) trivial
  change (presNM RD k S).lin (upLin RD k μ (relationR k (qCL S) (fun c => (S.r c : k)) r)) = 0 at h
  rwa [hr', relationR_one] at h

end NoMix

section NoMixRel

variable (S : CLScalars C k)

/-- The sideways crossing `crossl` in normal form. -/
theorem dgN_crossl (i j : I) (μ : X) :
    dgC (presNM RD k S) μ [up i, dn j] [dn j, up i] (crosslL i j) =
      (presNM RD k S).diag (crossl RD i j μ) := by
  rw [dgC_of (by schain)]; rfl

/-- The sideways crossing `crossr` in normal form. -/
theorem dgN_crossr (i j : I) (μ : X) :
    dgC (presNM RD k S) μ [dn j, up i] [up i, dn j] (crossrL i j) =
      (presNM RD k S).diag (crossr RD i j μ) := by
  rw [dgC_of (by schain)]; rfl

/-- **Dot cyclicity** (`eq_cyclic_dot`), rotation with the cup on the left. -/
theorem dgN_cycDotL (i : I) (μ : X) :
    dgC (presNM RD k S) μ [dn i] [dn i] [([], .dot (dn i), [])] =
      dgC (presNM RD k S) μ [dn i] [dn i]
        [([], .cup (dn i), [dn i]), ([dn i], .dot (up i), [dn i]), ([dn i], .cap (dn i), [])] := by
  rw [dgC_of (by schain), dgC_of (by schain)]
  exact ((presNM RD k S).diag_eq_of_rel (.inr ⟨.cycDotL i μ, trivial⟩) rfl).symm

/-- **Dot cyclicity** (`eq_cyclic_dot`), rotation with the cup on the right. -/
theorem dgN_cycDotR (i : I) (μ : X) :
    dgC (presNM RD k S) μ [dn i] [dn i] [([], .dot (dn i), [])] =
      dgC (presNM RD k S) μ [dn i] [dn i]
        [([dn i], .cup (up i), []), ([dn i], .dot (up i), [dn i]), ([], .cap (up i), [dn i])] := by
  rw [dgC_of (by schain), dgC_of (by schain)]
  exact ((presNM RD k S).diag_eq_of_rel (.inr ⟨.cycDotR i μ, trivial⟩) rfl).symm

theorem linN_ccwReal (ν : X) (i : I) (m : ℕ) :
    (presNM RD k S).lin (LinDiagram.of (ccwReal RD ν i m)) =
      dgC (presNM RD k S) ν [] [] (ccwLs i m) := by
  rw [ccwReal, linC_of_mkD]; rfl

theorem linN_cwReal (ν : X) (i : I) (m : ℕ) :
    (presNM RD k S).lin (LinDiagram.of (cwReal RD ν i m)) =
      dgC (presNM RD k S) ν [] [] (cwLs i m) := by
  rw [cwReal, linC_of_mkD]; rfl

/-- Negative-degree counterclockwise bubbles vanish (`eq_positivity_bubbles`). -/
theorem dgN_ccwNeg (ν : X) (i : I) (α : ℕ) (h : (α : ℤ) < -ip RD i ν - 1) :
    dgC (presNM RD k S) ν [] [] (ccwLs i α) = 0 := by
  rw [← linN_ccwReal]; exact presNM_lin_rel S (.ccwNeg i ν α h) trivial

/-- Negative-degree clockwise bubbles vanish (`eq_positivity_bubbles`). -/
theorem dgN_cwNeg (ν : X) (i : I) (α : ℕ) (h : (α : ℤ) < ip RD i ν - 1) :
    dgC (presNM RD k S) ν [] [] (cwLs i α) = 0 := by
  rw [← linN_cwReal]; exact presNM_lin_rel S (.cwNeg i ν α h) trivial

/-- The degree-zero counterclockwise bubble is `1` (`⟨i, ν⟩ ≤ -1`). -/
theorem dgN_ccwOne (ν : X) (i : I) (h : ip RD i ν ≤ -1) :
    dgC (presNM RD k S) ν [] [] (ccwLs i (-ip RD i ν - 1).toNat) =
      dgC (presNM RD k S) ν [] [] [] := by
  rw [← linN_ccwReal, dgC_nil]
  exact ((presNM RD k S).diag_eq_of_rel (.inr ⟨.ccwOne i ν h, trivial⟩) rfl).trans
    ((presNM RD k S).diag_id _)

/-- The degree-zero clockwise bubble is `1` (`⟨i, ν⟩ ≥ 1`). -/
theorem dgN_cwOne (ν : X) (i : I) (h : 1 ≤ ip RD i ν) :
    dgC (presNM RD k S) ν [] [] (cwLs i (ip RD i ν - 1).toNat) =
      dgC (presNM RD k S) ν [] [] [] := by
  rw [← linN_cwReal, dgC_nil]
  exact ((presNM RD k S).diag_eq_of_rel (.inr ⟨.cwOne i ν h, trivial⟩) rfl).trans
    ((presNM RD k S).diag_id _)

/-- The counterclockwise bubble with label `m ∈ ℤ` (`ccwL`) in `presNM`. -/
abbrev ccwN (ν : X) (i : I) (m : ℤ) : End ((presNM RD k S).obj (ob RD ν [])) :=
  (presNM RD k S).lin (ccwL RD k ν i m)

/-- The clockwise bubble with label `m ∈ ℤ` (`cwL`) in `presNM`. -/
abbrev cwN (ν : X) (i : I) (m : ℤ) : End ((presNM RD k S).obj (ob RD ν [])) :=
  (presNM RD k S).lin (cwL RD k ν i m)

/-- `n` dots on the strand `l` in `presNM`. -/
abbrev dotsN (lam : X) (l : Letter I) (n : ℕ) : End ((presNM RD k S).obj (ob RD lam [l])) :=
  dgC (presNM RD k S) lam [l] [l] (List.replicate n ([], .dot l, []))

theorem dotsN_eq (lam : X) (l : Letter I) (n : ℕ) :
    (presNM RD k S).diag (dots RD lam [] l [] n) = dotsN S lam l n :=
  (dgC_of _).symm

theorem ccwN_of_nonneg (ν : X) (i : I) (m : ℕ) :
    ccwN S ν i m = dgC (presNM RD k S) ν [] [] (ccwLs i m) := by
  rw [ccwN, ccwL, ite_eq_left (Int.natCast_nonneg m), Int.toNat_natCast, linN_ccwReal]

theorem cwN_of_nonneg (ν : X) (i : I) (m : ℕ) :
    cwN S ν i m = dgC (presNM RD k S) ν [] [] (cwLs i m) := by
  rw [cwN, cwL, ite_eq_left (Int.natCast_nonneg m), Int.toNat_natCast, linN_cwReal]

theorem linN_finsum {a b : Obj (psig RD)} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    (presNM RD k S).lin (∑ x ∈ s, f x) = ∑ x ∈ s, (presNM RD k S).lin (f x) :=
  map_sum (Presentation.linFunctor (presNM RD k S)).mapAddHom f s

variable {S} (hr : ∀ c, S.r c = 1)
include hr

/-- **The left curl** (`eq_reduction-ngeqz`, `r_i = 1`), in normal form (outer region
`λ = μ + i_X`, `n = ⟨i, λ⟩`): `∑_{g=0}^{n} ccw_{-n-1+g} x^{n-g}`, the bubbles on the left. -/
theorem dgN_curlL (i : I) (μ : X) :
    dgC (presNM RD k S) μ [up i] [up i]
        [([], .cup (dn i), [up i]), ([dn i], .cross true i i, []), ([], .cap (up i), [up i])] =
      ∑ g ∈ Finset.range (ip RD i (wt RD μ [up i]) + 1).toNat,
        bubLC (presNM RD k S) μ (up i) (ccwN S (wt RD μ [up i]) i (-ip RD i (wt RD μ [up i]) - 1 + g)) ≫
          dotsN S μ (up i) (ip RD i (wt RD μ [up i]) - g).toNat := by
  have key := presNM_lin_rel (RD := RD) S (.curlL i μ) trivial
  change (presNM RD k S).lin (LinDiagram.of (curlL RD i μ) - (S.r i : k) • curlLHS RD k i μ) = 0
    at key
  rw [hr i, Units.val_one, one_smul, Presentation.lin_sub, Presentation.lin_of, sub_eq_zero] at key
  rw [dgC_of (by schain)]
  refine key.trans ?_
  rw [curlLHS, linN_finsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Presentation.lin_comp, linC_bubL, Presentation.lin_of, dotsN_eq]

/-- **The right curl** (`eq_reduction-nleqz`, `r_i = 1`), in normal form (outer region `λ`,
`n = ⟨i, λ⟩`): `-∑_{f=0}^{-n} x^{-n-f} cw_{n-1+f}`, the bubbles on the right. -/
theorem dgN_curlR (i : I) (lam : X) :
    dgC (presNM RD k S) lam [up i] [up i]
        [([up i], .cup (up i), []), ([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])] =
      -∑ f ∈ Finset.range (-ip RD i lam + 1).toNat,
        bubRC (presNM RD k S) lam (up i) (cwN S lam i (ip RD i lam - 1 + f)) ≫
          dotsN S lam (up i) (-ip RD i lam - f).toNat := by
  have key := presNM_lin_rel (RD := RD) S (.curlR i lam) trivial
  change (presNM RD k S).lin (LinDiagram.of (curlR RD i lam) - (S.r i : k) • curlRHS RD k i lam) = 0
    at key
  rw [hr i, Units.val_one, one_smul, Presentation.lin_sub, Presentation.lin_of, sub_eq_zero] at key
  rw [dgC_of (by schain)]
  refine key.trans ?_
  rw [curlRHS, Presentation.lin_neg, linN_finsum]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Presentation.lin_comp, linC_bubR, Presentation.lin_of, dotsN_eq]

/-- **The decomposition of `1_{E F 1_λ}`** (`eq_ident_decomp`, `r_i = 1`), in normal form
(`n = ⟨i, λ⟩`). -/
theorem dgN_decompEF (i : I) (lam : X) :
    dgC (presNM RD k S) lam [up i, dn i] [up i, dn i] [] =
      -dgC (presNM RD k S) lam [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i) +
        ∑ f ∈ Finset.range (ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
          dgC (presNM RD k S) lam [up i, dn i] [] (dotCapEFLs i (f - g)) ≫
            ccwN S lam i (-ip RD i lam - 1 + g) ≫
              dgC (presNM RD k S) lam [] [up i, dn i] (cupDotEFLs i ((ip RD i lam).toNat - 1 - f)) := by
  have key := presNM_lin_rel (RD := RD) S (.decompEF i lam) trivial
  change (presNM RD k S).lin (LinDiagram.of (𝟙 _) + (((S.r i)⁻¹ : kˣ) : k) ^ 2 •
      LinDiagram.of (crossl RD i i lam ≫ crossr RD i i lam) - decompEFSum RD k i lam) = 0 at key
  rw [hr i, inv_one, Units.val_one, one_pow, one_smul] at key
  simp only [Presentation.lin_sub, Presentation.lin_add, Presentation.lin_of, sub_eq_zero] at key
  rw [dgC_nil, ← dgC_comp (t := [dn i, up i]) (by schain) (by schain), dgN_crossl, dgN_crossr,
    ← Presentation.diag_comp, eq_neg_add_iff_add_eq, ← Presentation.diag_id, add_comm, key,
    decompEFSum, linN_finsum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [linN_finsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Presentation.lin_comp, Presentation.lin_comp, Presentation.lin_of, Presentation.lin_of,
    dotCapEF, cupDotEF, ← linC_of_mkD, ← linC_of_mkD]
  rfl

/-- **The decomposition of `1_{F E 1_λ}`** (`eq_ident_decomp`, `r_i = 1`), in normal form
(`n = ⟨i, λ⟩`). -/
theorem dgN_decompFE (i : I) (lam : X) :
    dgC (presNM RD k S) lam [dn i, up i] [dn i, up i] [] =
      -dgC (presNM RD k S) lam [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i) +
        ∑ f ∈ Finset.range (-ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
          dgC (presNM RD k S) lam [dn i, up i] [] (dotCapFELs i (f - g)) ≫
            cwN S lam i (ip RD i lam - 1 + g) ≫
              dgC (presNM RD k S) lam [] [dn i, up i] (cupDotFELs i ((-ip RD i lam).toNat - 1 - f)) := by
  have key := presNM_lin_rel (RD := RD) S (.decompFE i lam) trivial
  change (presNM RD k S).lin (LinDiagram.of (𝟙 _) + (((S.r i)⁻¹ : kˣ) : k) ^ 2 •
      LinDiagram.of (crossr RD i i lam ≫ crossl RD i i lam) - decompFESum RD k i lam) = 0 at key
  rw [hr i, inv_one, Units.val_one, one_pow, one_smul] at key
  simp only [Presentation.lin_sub, Presentation.lin_add, Presentation.lin_of, sub_eq_zero] at key
  rw [dgC_nil, ← dgC_comp (t := [up i, dn i]) (by schain) (by schain), dgN_crossl, dgN_crossr,
    ← Presentation.diag_comp, eq_neg_add_iff_add_eq, ← Presentation.diag_id, add_comm, key,
    decompFESum, linN_finsum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [linN_finsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Presentation.lin_comp, Presentation.lin_comp, Presentation.lin_of, Presentation.lin_of,
    dotCapFE, cupDotFE, ← linC_of_mkD, ← linC_of_mkD]
  rfl

end NoMixRel

end Categorification.KL3.Diagram.CL
