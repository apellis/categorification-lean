/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.Upward
import Categorification.Diagrams.KL3.SlideCalculus

/-!
# The relations of `U_Q(g)` in normal form

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1, for the
Cautis–Lauda scalars (S. Cautis, A. D. Lauda, arXiv:1111.1431v3, Definition 1.1, `r = 1`).

The calculus of normal-form diagrams (placement, rewriting in context, the interchange law and
the zigzag relations, the tactic `dstepQ`) is `Categorification.Diagrams.KL3.NormalForm`, for any
presentation on the signature of `U`; here `P = pres RD k sc` (`HasZigzags` from `zigzags`).
This file gives the remaining relations of `U_Q(g)` in normal form: `dg_downupEF`,
`dg_downupFE` (`eq_downup_ij-gen`, with `t_{ij}`), `dg_cycDotL`, `dg_cycDotR` (KL III (3.3)),
`dg_slideLNe`, `dg_slideRNe`, `dg_sqNe` (`eq_dot_slide_ij-gen`, `eq_r2_ij-gen` with `Q_{ij}`),
`dg_slideLEq`, `dg_slideREq`, `dg_sqEq` (`eq_nil_rels`, `eq_nil_dotslide`), `dg_ccwNeg`,
`dg_cwNeg`, `dg_ccwOne`, `dg_cwOne` (`eq_positivity_bubbles` and the degree-zero bubbles),
`dg_curlL`, `dg_curlR` (curl relations), `dg_decompEF`, `dg_decompFE` (`eq_ident_decomp`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

instance : NF.HasZigzags (pres RD k sc) := ⟨zigzags RD k sc⟩

/-- The class of a normal-form diagram of `U_Q(g)`. -/
@[deprecated NF.dg (since := "2026-11-22")]
abbrev dg (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    (pres RD k sc).obj (ob RD μ s) ⟶ (pres RD k sc).obj (ob RD μ t) :=
  NF.dg (pres RD k sc) μ s t ls

/-! ## The relations of `U` in normal form -/

theorem dg_crossl (i j : I) (μ : X) :
    NF.dg (pres RD k sc) μ [up i, dn j] [dn j, up i] (crosslL i j) = (pres RD k sc).diag (crossl RD i j μ) := by
  rw [NF.dg_of (by schain)]; rfl

theorem dg_crossr (i j : I) (μ : X) :
    NF.dg (pres RD k sc) μ [dn j, up i] [up i, dn j] (crossrL i j) = (pres RD k sc).diag (crossr RD i j μ) := by
  rw [NF.dg_of (by schain)]; rfl

/-- **CL `sec:mixedrels`, first relation** (`i ≠ j`): `crossr ∘ crossl = t_{ji} · 1` on
`E_i F_j 1_μ`. -/
theorem dg_downupEF (i j : I) (h : i ≠ j) (μ : X) :
    NF.dg (pres RD k sc) μ [up i, dn j] [up i, dn j] (crosslL i j ++ crossrL i j) =
      (sc.t j i : k) • NF.dg (pres RD k sc) μ [up i, dn j] [up i, dn j] [] := by
  rw [← NF.dg_comp (t := [dn j, up i]) (by schain) (by schain), dg_crossl, dg_crossr, NF.dg_nil,
    ← Presentation.diag_comp]
  have key : (pres RD k sc).lin (LinDiagram.of (crossl RD i j μ ≫ crossr RD i j μ) -
      (sc.t j i : k) • LinDiagram.of (𝟙 _)) = 0 := lin_relationCL RD k sc (.downupEF i j h μ)
  rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, Presentation.lin_of,
    sub_eq_zero] at key
  rw [key, Presentation.diag_id]

/-- **CL `sec:mixedrels`, second relation** (`i ≠ j`): `crossl ∘ crossr = t_{ij} · 1` on
`F_i E_j 1_μ`. -/
theorem dg_downupFE (i j : I) (h : i ≠ j) (μ : X) :
    NF.dg (pres RD k sc) μ [dn i, up j] [dn i, up j] (crossrL j i ++ crosslL j i) =
      (sc.t i j : k) • NF.dg (pres RD k sc) μ [dn i, up j] [dn i, up j] [] := by
  rw [← NF.dg_comp (t := [up j, dn i]) (by schain) (by schain), dg_crossl, dg_crossr, NF.dg_nil,
    ← Presentation.diag_comp]
  have key : (pres RD k sc).lin (LinDiagram.of (crossr RD j i μ ≫ crossl RD j i μ) -
      (sc.t i j : k) • LinDiagram.of (𝟙 _)) = 0 := lin_relationCL RD k sc (.downupFE i j h μ)
  rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, Presentation.lin_of,
    sub_eq_zero] at key
  rw [key, Presentation.diag_id]

/-- **KL III (3.3)**, rotation with the cup on the left: the downward dot on `F_i 1_μ` is the
upward dot rotated by the cup `1 ⟶ F E` and the cap `E F ⟶ 1`. -/
theorem dg_cycDotL (i : I) (μ : X) :
    NF.dg (pres RD k sc) μ [dn i] [dn i] [([], .dot (dn i), [])] =
      NF.dg (pres RD k sc) μ [dn i] [dn i]
        [([], .cup (dn i), [dn i]), ([dn i], .dot (up i), [dn i]), ([dn i], .cap (dn i), [])] := by
  rw [NF.dg_of (by schain), NF.dg_of (by schain)]
  exact ((pres RD k sc).diag_eq_of_rel (.inr (.cycDotL i μ)) rfl).symm

/-- **KL III (3.3)**, rotation with the cup on the right. -/
theorem dg_cycDotR (i : I) (μ : X) :
    NF.dg (pres RD k sc) μ [dn i] [dn i] [([], .dot (dn i), [])] =
      NF.dg (pres RD k sc) μ [dn i] [dn i]
        [([dn i], .cup (up i), []), ([dn i], .dot (up i), [dn i]), ([], .cap (up i), [dn i])] := by
  rw [NF.dg_of (by schain), NF.dg_of (by schain)]
  exact ((pres RD k sc).diag_eq_of_rel (.inr (.cycDotR i μ)) rfl).symm

/-! ### The KLR relations on upward strands -/

theorem upDiag_eq_dg (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    (pres RD k sc).diag (upDiag RD μ d) =
      NF.dg (pres RD k sc) μ (ups a.word) (ups b.word) ((Diagram.layers d).map upLD) := by
  rw [NF.dg_of (sChain_upLD (Diagram.chain d))]
  exact (pres RD k sc).diag_eq_of_layers_eq (by simp [layList, upLay, upLD, List.map_map])

/-- The upward dot slide `ψ x₀ = x₁ ψ` for `c ≠ d` (KL III `eq_dot_slide_ij-gen`), in the form
"a dot on the left strand of `E_c E_d` moves up through the crossing to the right strand". -/
theorem dg_slideRNe (μ : X) (c d : I) (h : c ≠ d) :
    NF.dg (pres RD k sc) μ [up c, up d] [up d, up c] [([], .dot (up c), [up d]), ([], .cross true c d, [])] =
      NF.dg (pres RD k sc) μ [up c, up d] [up d, up c] [([], .cross true c d, []), ([up d], .dot (up c), [])] := by
  have key := (KLR.Diagram.pres k (CL.qCL sc)).diag_eq_of_rel (.slideRNe c d h) rfl
  have key' := congrArg (upFunctor RD k sc μ).map key
  rw [upFunctor_diag, upFunctor_diag, upDiag_eq_dg, upDiag_eq_dg] at key'
  exact key'

/-- The upward dot slide `x₀ ψ = ψ x₁` for `c ≠ d` (KL III `eq_dot_slide_ij-gen`): a dot on the
right strand of `E_c E_d` moves up through the crossing to the left strand. -/
theorem dg_slideLNe (μ : X) (c d : I) (h : c ≠ d) :
    NF.dg (pres RD k sc) μ [up c, up d] [up d, up c] [([], .cross true c d, []), ([], .dot (up d), [up c])] =
      NF.dg (pres RD k sc) μ [up c, up d] [up d, up c] [([up c], .dot (up d), []), ([], .cross true c d, [])] := by
  have key := (KLR.Diagram.pres k (CL.qCL sc)).diag_eq_of_rel (.slideLNe c d h) rfl
  have key' := congrArg (upFunctor RD k sc μ).map key
  rw [upFunctor_diag, upFunctor_diag, upDiag_eq_dg, upDiag_eq_dg] at key'
  exact key'

/-- **KL III `eq_r2_ij-gen`** (`c ≠ d`): the double crossing of upward strands `E_c E_d` is
`1` if `c · d = 0`, and `x_c^{d_cd} + x_d^{d_dc}` otherwise (the KL II polynomial
`Q_cd = u^{d_cd} + v^{d_dc}`). -/
theorem dg_sqNe (μ : X) (c d : I) (h : c ≠ d) :
    NF.dg (pres RD k sc) μ [up c, up d] [up c, up d] [([], .cross true c d, []), ([], .cross true d c, [])] =
      KLR.ncEval ![NF.dgE (pres RD k sc) μ [up c, up d] [([], .dot (up c), [up d])],
        NF.dgE (pres RD k sc) μ [up c, up d] [([up c], .dot (up d), [])]] (CL.qCL sc c d) := by
  have key := KLR.Diagram.sqNe_at (CL.qCL sc) (u := []) (v := []) h
    (KLR.Diagram.X2 c d ≫ KLR.Diagram.X2 d c) (KLR.Diagram.D0 c d) (KLR.Diagram.D1 c d) rfl rfl rfl
  have key' := congrArg (functorEndAlg k (upFunctor RD k sc μ) _) key
  rw [AlgHom.map_ncEval] at key'
  simp only [functorEndAlg, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    upFunctor_diag] at key'
  rw [upDiag_eq_dg] at key'
  refine key'.trans ?_
  have e₀ : (fun a => ((upFunctor RD k sc μ).map ((![(KLR.Diagram.pres k (CL.qCL sc)).diag
      (KLR.Diagram.D0 c d), (KLR.Diagram.pres k (CL.qCL sc)).diag (KLR.Diagram.D1 c d)] :
        Fin 2 → _) a) : End ((pres RD k sc).obj (ob RD μ [up c, up d])))) =
      ![NF.dg (pres RD k sc) μ [up c, up d] [up c, up d] [([], .dot (up c), [up d])],
        NF.dg (pres RD k sc) μ [up c, up d] [up c, up d] [([up c], .dot (up d), [])]] := by
    funext a; fin_cases a
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, upFunctor_diag, upDiag_eq_dg]; rfl
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        upFunctor_diag, upDiag_eq_dg]
      rfl
  rw [e₀]

/-! ### The nilHecke relations on upward strands of one colour -/

/-- **KL III `eq_nil_rels`**: `ψ² = 0` on `E_c E_c`. -/
theorem dg_sqEq (μ : X) (c : I) :
    NF.dg (pres RD k sc) μ [up c, up c] [up c, up c] [([], .cross true c c, []), ([], .cross true c c, [])] = 0 := by
  have key := KLR.Diagram.sqEq_at (CL.qCL sc) (u := []) (v := [])
    (KLR.Diagram.X2 c c ≫ KLR.Diagram.X2 c c) rfl
  have key' := congrArg (upFunctor RD k sc μ).map key
  rw [upFunctor_diag, Functor.map_zero, upDiag_eq_dg] at key'
  exact key'

/-- **KL III `eq_nil_dotslide`**, first form: `x₁ ψ = ψ x₂ + 1` on `E_c E_c` (bottom to top: a dot
on the left strand below the crossing equals a dot on the right strand above it, plus the
identity). -/
theorem dg_slideREq (μ : X) (c : I) :
    NF.dg (pres RD k sc) μ [up c, up c] [up c, up c] [([], .dot (up c), [up c]), ([], .cross true c c, [])] =
      NF.dg (pres RD k sc) μ [up c, up c] [up c, up c] [([], .cross true c c, []), ([up c], .dot (up c), [])] +
        NF.dg (pres RD k sc) μ [up c, up c] [up c, up c] [] := by
  have key := KLR.Diagram.slideREq_at (CL.qCL sc) (u := []) (v := [])
    (KLR.Diagram.D0 c c ≫ KLR.Diagram.X2 c c) (KLR.Diagram.X2 c c ≫ KLR.Diagram.D1 c c) rfl rfl
  have key' := congrArg (upFunctor RD k sc μ).map key
  rw [Functor.map_sub, upFunctor_diag, upFunctor_diag, CategoryTheory.Functor.map_id, upDiag_eq_dg,
    upDiag_eq_dg] at key'
  rw [NF.dg_nil]
  exact sub_eq_iff_eq_add'.mp key'

/-- **KL III `eq_nil_dotslide`**, second form: `ψ x₁ = x₂ ψ + 1` on `E_c E_c` (a dot on the
left strand above the crossing equals a dot on the right strand below it, plus the identity). -/
theorem dg_slideLEq (μ : X) (c : I) :
    NF.dg (pres RD k sc) μ [up c, up c] [up c, up c] [([], .cross true c c, []), ([], .dot (up c), [up c])] =
      NF.dg (pres RD k sc) μ [up c, up c] [up c, up c] [([up c], .dot (up c), []), ([], .cross true c c, [])] +
        NF.dg (pres RD k sc) μ [up c, up c] [up c, up c] [] := by
  have key := KLR.Diagram.slideLEq_at (CL.qCL sc) (u := []) (v := [])
    (KLR.Diagram.X2 c c ≫ KLR.Diagram.D0 c c) (KLR.Diagram.D1 c c ≫ KLR.Diagram.X2 c c) rfl rfl
  have key' := congrArg (upFunctor RD k sc μ).map key
  rw [Functor.map_sub, upFunctor_diag, upFunctor_diag, CategoryTheory.Functor.map_id, upDiag_eq_dg,
    upDiag_eq_dg] at key'
  rw [NF.dg_nil]
  exact sub_eq_iff_eq_add'.mp key'

/-! ### Bubbles -/

/-- **KL III (3.4)**, counterclockwise. -/
theorem dg_ccwNeg (ν : X) (i : I) (α : ℕ) (h : (α : ℤ) < -ip RD i ν - 1) :
    NF.dg (pres RD k sc) ν [] [] (ccwLs i α) = 0 := by
  rw [← NF.lin_ccwReal]; exact (pres RD k sc).lin_rel_self (.inr (.ccwNeg i ν α h))

/-- **KL III (3.4)**, clockwise. -/
theorem dg_cwNeg (ν : X) (i : I) (α : ℕ) (h : (α : ℤ) < ip RD i ν - 1) :
    NF.dg (pres RD k sc) ν [] [] (cwLs i α) = 0 := by
  rw [← NF.lin_cwReal]; exact (pres RD k sc).lin_rel_self (.inr (.cwNeg i ν α h))

/-- The degree-zero counterclockwise bubble is `1` (`⟨i,ν⟩ ≤ -1`). -/
theorem dg_ccwOne (ν : X) (i : I) (h : ip RD i ν ≤ -1) :
    NF.dg (pres RD k sc) ν [] [] (ccwLs i (-ip RD i ν - 1).toNat) = NF.dg (pres RD k sc) ν [] [] [] := by
  rw [← NF.lin_ccwReal, NF.dg_nil]
  exact ((pres RD k sc).diag_eq_of_rel (.inr (.ccwOne i ν h)) rfl).trans ((pres RD k sc).diag_id _)

/-- The degree-zero clockwise bubble is `1` (`⟨i,ν⟩ ≥ 1`). -/
theorem dg_cwOne (ν : X) (i : I) (h : 1 ≤ ip RD i ν) :
    NF.dg (pres RD k sc) ν [] [] (cwLs i (ip RD i ν - 1).toNat) = NF.dg (pres RD k sc) ν [] [] [] := by
  rw [← NF.lin_cwReal, NF.dg_nil]
  exact ((pres RD k sc).diag_eq_of_rel (.inr (.cwOne i ν h)) rfl).trans ((pres RD k sc).diag_id _)

/-! ### Dots, fake bubbles, curls and the decompositions -/

/-- **KL III, curl relation (item iv), left curl)**, in normal form: an upward strand `E_i` with
a curl on its left (outer region `λ = μ + i_X`, `n = ⟨i, λ⟩`) equals
`∑_{g=0}^{n} ccw_{-n-1+g} x^{n-g}`, the bubbles to the left of the strand. -/
theorem dg_curlL (i : I) (μ : X) :
    NF.dg (pres RD k sc) μ [up i] [up i]
        [([], .cup (dn i), [up i]), ([dn i], .cross true i i, []), ([], .cap (up i), [up i])] =
      ∑ g ∈ Finset.range (ip RD i (wt RD μ [up i]) + 1).toNat,
        NF.bubLU (pres RD k sc) μ (up i) (NF.ccwU (pres RD k sc) (wt RD μ [up i]) i (-ip RD i (wt RD μ [up i]) - 1 + g)) ≫
          NF.dotsU (pres RD k sc) μ (up i) (ip RD i (wt RD μ [up i]) - g).toNat := by
  have key : (pres RD k sc).lin (relation (RD := RD) k (.curlL i μ)) = 0 :=
    lin_relation_of RD k sc _ (relationCL_curlL RD k sc i μ)
  simp only [relation, Presentation.lin_sub, Presentation.lin_of,
    sub_eq_zero] at key
  rw [NF.dg_of (by schain)]
  refine key.trans ?_
  rw [curlLHS, NF.lin_finsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Presentation.lin_comp, NF.lin_bubL, Presentation.lin_of, NF.dotsU_eq]

/-- **KL III, curl relation (item iv), right curl)**, in normal form: an upward strand `E_i`
with a curl on its right (outer region `λ`, `n = ⟨i, λ⟩`) equals
`-∑_{f=0}^{-n} x^{-n-f} cw_{n-1+f}`, the bubbles to the right of the strand. -/
theorem dg_curlR (i : I) (lam : X) :
    NF.dg (pres RD k sc) lam [up i] [up i]
        [([up i], .cup (up i), []), ([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])] =
      -∑ f ∈ Finset.range (-ip RD i lam + 1).toNat,
        NF.bubRU (pres RD k sc) lam (up i) (NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + f)) ≫
          NF.dotsU (pres RD k sc) lam (up i) (-ip RD i lam - f).toNat := by
  have key : (pres RD k sc).lin (relation (RD := RD) k (.curlR i lam)) = 0 :=
    lin_relation_of RD k sc _ (relationCL_curlR RD k sc i lam)
  simp only [relation, Presentation.lin_sub, Presentation.lin_of,
    sub_eq_zero] at key
  rw [NF.dg_of (by schain)]
  refine key.trans ?_
  rw [curlRHS, Presentation.lin_neg, NF.lin_finsum]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Presentation.lin_comp, NF.lin_bubR, Presentation.lin_of, NF.dotsU_eq]

/-- **KL III `eq_ident_decomp`, first identity**, in normal form (`n = ⟨i, λ⟩`):
`1_{E F 1_λ} = -crossr ∘ crossl + ∑_{f=0}^{n-1} ∑_{g=0}^{f}` (cap with `f-g` dots)
`ccw_{-n-1+g}` (cup with `n-1-f` dots). -/
theorem dg_decompEF (i : I) (lam : X) :
    NF.dg (pres RD k sc) lam [up i, dn i] [up i, dn i] [] =
      -NF.dg (pres RD k sc) lam [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i) +
        ∑ f ∈ Finset.range (ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
          NF.dg (pres RD k sc) lam [up i, dn i] [] (dotCapEFLs i (f - g)) ≫ NF.ccwU (pres RD k sc) lam i (-ip RD i lam - 1 + g) ≫
            NF.dg (pres RD k sc) lam [] [up i, dn i] (cupDotEFLs i ((ip RD i lam).toNat - 1 - f)) := by
  have key : (pres RD k sc).lin (relation (RD := RD) k (.decompEF i lam)) = 0 :=
    lin_relation_of RD k sc _ (relationCL_decompEF RD k sc i lam)
  simp only [relation, Presentation.lin_sub, Presentation.lin_add,
    Presentation.lin_of, sub_eq_zero] at key
  rw [NF.dg_nil, ← NF.dg_comp (t := [dn i, up i]) (by schain) (by schain), dg_crossl, dg_crossr,
    ← Presentation.diag_comp, eq_neg_add_iff_add_eq, ← Presentation.diag_id, add_comm, key,
    decompEFSum,
    NF.lin_finsum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [NF.lin_finsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Presentation.lin_comp, Presentation.lin_comp, Presentation.lin_of, Presentation.lin_of,
    dotCapEF, cupDotEF, ← NF.lin_of_mkD, ← NF.lin_of_mkD]
  rfl

/-- **KL III `eq_ident_decomp`, second identity**, in normal form (`n = ⟨i, λ⟩`):
`1_{F E 1_λ} = -crossl ∘ crossr + ∑_{f=0}^{-n-1} ∑_{g=0}^{f}` (cap with `f-g` dots)
`cw_{n-1+g}` (cup with `-n-1-f` dots). -/
theorem dg_decompFE (i : I) (lam : X) :
    NF.dg (pres RD k sc) lam [dn i, up i] [dn i, up i] [] =
      -NF.dg (pres RD k sc) lam [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i) +
        ∑ f ∈ Finset.range (-ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
          NF.dg (pres RD k sc) lam [dn i, up i] [] (dotCapFELs i (f - g)) ≫ NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + g) ≫
            NF.dg (pres RD k sc) lam [] [dn i, up i] (cupDotFELs i ((-ip RD i lam).toNat - 1 - f)) := by
  have key : (pres RD k sc).lin (relation (RD := RD) k (.decompFE i lam)) = 0 :=
    lin_relation_of RD k sc _ (relationCL_decompFE RD k sc i lam)
  simp only [relation, Presentation.lin_sub, Presentation.lin_add,
    Presentation.lin_of, sub_eq_zero] at key
  rw [NF.dg_nil, ← NF.dg_comp (t := [up i, dn i]) (by schain) (by schain), dg_crossl, dg_crossr,
    ← Presentation.diag_comp, eq_neg_add_iff_add_eq, ← Presentation.diag_id, add_comm, key,
    decompFESum,
    NF.lin_finsum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [NF.lin_finsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Presentation.lin_comp, Presentation.lin_comp, Presentation.lin_of, Presentation.lin_of,
    dotCapFE, cupDotFE, ← NF.lin_of_mkD, ← NF.lin_of_mkD]
  rfl

-- `schain` also unfolds the named lists of layers of this file.

end Categorification.KL3.Diagram.CLQ
