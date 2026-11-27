/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetryPsi
import Categorification.Diagrams.CLQ.BubbleSlidesEq
import Categorification.Diagrams.CLQ.Pitchfork
import Categorification.Diagrams.CLQ.Upward
import Categorification.Diagrams.CLQ.Grassmannian

/-!
# The symmetry `ψ̃` of `U_Q(g)`: reflection in a horizontal axis

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3.2
(TeX label `sec_symm`), paragraph "Reflect across the x-axis and invert orientation",
eq. (3.44), for the 2-category `U_Q(g)` of S. Cautis, A. D. Lauda, arXiv:1111.1431v3,
Definition 1.1, with arbitrary scalars `t`, `s` and `r = 1` (`CLQ.pres`).

The reflection of diagrams across the `x`-axis with inverted orientations
(`Categorification.Diagrams.KL3.SymmetryPsi`, `Psi.reflD`) fixes the regions and the
1-morphisms and is contravariant on 2-morphisms. It maps every relation of `U_Q(g)` to a relation
of `U_Q(g)` **with the same scalars**:

* the cyclicity relations `eq_almost_cyclic` are exchanged (`cycCrossR j i ↔ cycCrossL i j`),
  and both carry the scalar `t_{ij}^{-1}`;
* the mixed relations `sec:mixedrels` (`downupEF`, `downupFE`) are fixed, with their scalars;
* the KLR relations on upward strands for `Q = qCL S` are exchanged among themselves
  (`KPsi.lin_kreflLin_relation`, valid for every `Q`);
* the dot cyclicity, the bubble relations, the curl relations and the identity decompositions
  are those of KL III, and are reflected as there.

So `ψ̃` is a `k`-linear functor `psiUQ : U_Q(g) ⥤ U_Q(g)ᵒᵖ`, the identity on objects
(`psiUQ_diag`, `psiUQ_whisk`).

## Main results

* `psiUQ RD k sc : (pres RD k sc).Presented ⥤ (pres RD k sc).Presentedᵒᵖ`, `k`-linear;
* `psiUQ_lin`, `psiUQ_diag`, `psiUQ_dg`: on linear combinations of diagrams, on diagrams and on
  normal forms it is the reflection;
* `psiUQ_whisk`: it commutes with whiskering.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Opposite Psi

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-! ## The reflection on the free 2-category -/

/-- The reflection on the free 2-category, with values in the opposite of `U_Q(g)`. -/
def psiFreeQ : Obj (psig RD) ⥤ (pres RD k sc).Presentedᵒᵖ where
  obj a := op ((pres RD k sc).obj a)
  map d := ((pres RD k sc).diag (reflD d)).op
  map_id a := by rw [reflD_id, Presentation.diag_id]; rfl
  map_comp f g := by rw [reflD_comp, Presentation.diag_comp]; rfl

/-- The reflection of a linear combination of diagrams, in `U_Q(g)`. -/
def psiLQ {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (pres RD k sc).obj b ⟶ (pres RD k sc).obj a :=
  (pres RD k sc).lin (reflLin k f)

variable {RD k sc}

theorem psiLQ_of {a b : Obj (psig RD)} (d : a ⟶ b) :
    psiLQ RD k sc (LinDiagram.of d) = (pres RD k sc).diag (reflD d) := by
  rw [psiLQ, reflLin, Finsupp.mapDomain_single]; rfl

theorem psiLQ_single {a b : Obj (psig RD)} (d : a ⟶ b) (r : k) :
    psiLQ RD k sc (Finsupp.single d r) = r • (pres RD k sc).diag (reflD d) := by
  rw [psiLQ, reflLin, Finsupp.mapDomain_single, Presentation.lin_single]

theorem psiLQ_add {a b : Obj (psig RD)} (f g : LinDiagram k a b) :
    psiLQ RD k sc (f + g) = psiLQ RD k sc f + psiLQ RD k sc g := by
  rw [psiLQ, reflLin, Finsupp.mapDomain_add, Presentation.lin_add]; rfl

theorem psiLQ_smul {a b : Obj (psig RD)} (r : k) (f : LinDiagram k a b) :
    psiLQ RD k sc (r • f) = r • psiLQ RD k sc f := by
  rw [psiLQ, reflLin, Finsupp.mapDomain_smul, Presentation.lin_smul]; rfl

theorem psiLQ_zero {a b : Obj (psig RD)} : psiLQ RD k sc (0 : LinDiagram k a b) = 0 := by
  rw [psiLQ, reflLin, Finsupp.mapDomain_zero, Presentation.lin_zero]

/-- `psiLQ` as a `k`-linear map. -/
def psiLQM (a b : Obj (psig RD)) :
    LinDiagram k a b →ₗ[k] ((pres RD k sc).obj b ⟶ (pres RD k sc).obj a) where
  toFun := psiLQ RD k sc
  map_add' := psiLQ_add
  map_smul' := psiLQ_smul

theorem psiLQ_neg {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    psiLQ RD k sc (-f) = -psiLQ RD k sc f :=
  (psiLQM a b).map_neg f

theorem psiLQ_sub {a b : Obj (psig RD)} (f g : LinDiagram k a b) :
    psiLQ RD k sc (f - g) = psiLQ RD k sc f - psiLQ RD k sc g :=
  (psiLQM a b).map_sub f g

theorem psiLQ_sum {a b : Obj (psig RD)} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    psiLQ RD k sc (∑ x ∈ s, f x) = ∑ x ∈ s, psiLQ RD k sc (f x) :=
  map_sum (psiLQM a b) f s

theorem psiLQ_id (a : Obj (psig RD)) : psiLQ RD k sc (𝟙 (Free.of k a)) = 𝟙 _ := by
  rw [show (𝟙 (Free.of k a) : LinDiagram k a a) = LinDiagram.of (𝟙 a) from rfl, psiLQ_of,
    reflD_id, Presentation.diag_id]

theorem psiLQ_comp {a b c : Obj (psig RD)} (f : LinDiagram k a b) (g : LinDiagram k b c) :
    psiLQ RD k sc (f ≫ g) = psiLQ RD k sc g ≫ psiLQ RD k sc f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, psiLQ_zero, psiLQ_zero, Limits.comp_zero]
  | add f₁ f₂ h₁ h₂ =>
    rw [Preadditive.add_comp, psiLQ_add, psiLQ_add, h₁, h₂, Preadditive.comp_add]
  | single d r =>
    induction g using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, psiLQ_zero, psiLQ_zero, Limits.zero_comp]
    | add g₁ g₂ h₁ h₂ =>
      rw [Preadditive.comp_add, psiLQ_add, psiLQ_add, h₁, h₂, Preadditive.add_comp]
    | single e s =>
      erw [Free.single_comp_single]
      rw [psiLQ_single, psiLQ_single, psiLQ_single, reflD_comp, Presentation.diag_comp,
        Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]

theorem freeLift_psiFreeQ {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (freeLift k (psiFreeQ RD k sc)).map f = (psiLQ RD k sc f).op := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Functor.map_zero, psiLQ_zero]; rfl
  | add f₁ f₂ h₁ h₂ => rw [Functor.map_add, h₁, h₂, psiLQ_add, op_add]
  | single d r =>
    rw [freeLift_map_single, psiLQ_single]
    rfl

theorem psiLQ_whisker {a b : Obj (psig RD)} (f : LinDiagram k a b) (u : Obj (psig RD))
    (v : List (psig RD).Colour) (hw : a.WhiskerOK u v) :
    psiLQ RD k sc (LinDiagram.whisker f u v hw) =
      (pres RD k sc).whisk (psiLQ RD k sc f) u v := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [psiLQ_zero, show LinDiagram.whisker (0 : LinDiagram k a b) u v hw = 0 from
      Finsupp.mapDomain_zero, psiLQ_zero, Presentation.whisk_zero]
  | add f₁ f₂ h₁ h₂ =>
    rw [LinDiagram.whisker_add, psiLQ_add, psiLQ_add, h₁, h₂, Presentation.whisk_add]
  | single d r =>
    rw [LinDiagram.whisker_single, psiLQ_single, psiLQ_single, Presentation.whisk_smul,
      Presentation.whisk_diag _ _ _ _ ((Diagram.chain d).whiskerOK hw), reflD_whisker]

theorem psiLQ_of_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) :
    psiLQ RD k sc (LinDiagram.of (mkD RD μ ls h)) = NF.dg (pres RD k sc) μ t s (rls ls) := by
  rw [psiLQ_of, reflD_mkD, NF.dg_of]

/-! ## Bubbles -/

section Bubbles

theorem psiLQ_bubR (lam : X) (l : Letter I) (b : LEnd RD k (ob RD lam [])) :
    psiLQ RD k sc (bubR RD k lam [l] b) = NF.bubRU (pres RD k sc) lam l (psiLQ RD k sc b) := by
  rw [psiLQ, reflLin_bubR, NF.lin_bubR]; rfl

theorem psiLQ_bubL (μ : X) (l : Letter I) (b : LEnd RD k (ob RD (wt RD μ [l]) [])) :
    psiLQ RD k sc (bubL RD k μ [l] b) = NF.bubLU (pres RD k sc) μ l (psiLQ RD k sc b) := by
  rw [psiLQ, reflLin_bubL, NF.lin_bubL]; rfl

variable (RD k sc) in
/-- The reflection on `END(1_λ)`: an antihomomorphism to a commutative ring, hence a ring
homomorphism. -/
def psiEndQ (lam : X) : LEnd RD k (ob RD lam []) →+* End ((pres RD k sc).obj (ob RD lam [])) where
  toFun := psiLQ RD k sc
  map_one' := psiLQ_id _
  map_mul' f g := by
    show psiLQ RD k sc (g ≫ f) = psiLQ RD k sc g ≫ psiLQ RD k sc f
    rw [psiLQ_comp]; exact endEmpty_comm RD k sc lam _ _
  map_zero' := psiLQ_zero
  map_add' := psiLQ_add

variable (RD k sc) in
/-- The class map on `END(1_λ)`, as a ring homomorphism. -/
def linEndQ (lam : X) : LEnd RD k (ob RD lam []) →+* End ((pres RD k sc).obj (ob RD lam [])) :=
  (KLR.Diagram.linAlg (pres RD k sc) (ob RD lam [])).toRingHom

theorem psiLQ_ccwR (lam : X) (i : I) (m : ℤ) :
    psiLQ RD k sc (ccwR RD k lam i m) = (pres RD k sc).lin (ccwR RD k lam i m) := by
  unfold ccwR
  split_ifs
  · rw [psiLQ_of, reflD_ccwReal]; rfl
  · rw [psiLQ_zero, Presentation.lin_zero]

theorem psiLQ_cwR (lam : X) (i : I) (m : ℤ) :
    psiLQ RD k sc (cwR RD k lam i m) = (pres RD k sc).lin (cwR RD k lam i m) := by
  unfold cwR
  split_ifs
  · rw [psiLQ_of, reflD_cwReal]; rfl
  · rw [psiLQ_zero, Presentation.lin_zero]

/-- **`ψ̃` fixes all clockwise bubbles** (real and fake). -/
theorem psiLQ_cwL (lam : X) (i : I) (m : ℤ) :
    psiLQ RD k sc (cwL RD k lam i m) = NF.cwU (pres RD k sc) lam i m := by
  unfold NF.cwU cwL
  split_ifs
  · rw [psiLQ_of, reflD_cwReal]; rfl
  · show psiEndQ RD k sc lam _ = linEndQ RD k sc lam _
    rw [map_grassInv, map_grassInv]
    congr 1
    funext a
    exact psiLQ_ccwR lam i _
  · rw [psiLQ_zero, Presentation.lin_zero]

/-- **`ψ̃` fixes all counterclockwise bubbles** (real and fake). -/
theorem psiLQ_ccwL (lam : X) (i : I) (m : ℤ) :
    psiLQ RD k sc (ccwL RD k lam i m) = NF.ccwU (pres RD k sc) lam i m := by
  unfold NF.ccwU ccwL
  split_ifs
  · rw [psiLQ_of, reflD_ccwReal]; rfl
  · show psiEndQ RD k sc lam _ = linEndQ RD k sc lam _
    rw [map_grassInv, map_grassInv]
    congr 1
    funext a
    exact psiLQ_cwR lam i _
  · rw [psiLQ_zero, Presentation.lin_zero]

end Bubbles

/-! ## The upward KLR relations -/

theorem psiLQ_upLin (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) :
    psiLQ RD k sc (upLin RD k μ f) =
      (upFunctor RD k sc μ).map
        ((KLR.Diagram.pres k (CL.qCL sc)).lin (KPsi.kreflLin k f)) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [upLin, Finsupp.mapDomain_zero, psiLQ_zero, KPsi.kreflLin_zero, Presentation.lin_zero,
      Functor.map_zero]
  | add f g hf hg =>
    rw [upLin, Finsupp.mapDomain_add, ← upLin, ← upLin, psiLQ_add, hf, hg, KPsi.kreflLin_add,
      Presentation.lin_add, Functor.map_add]
  | single d r =>
    rw [upLin, Finsupp.mapDomain_single, psiLQ_single, reflD_upDiag, KPsi.kreflLin_single,
      Presentation.lin_single, Functor.map_smul, upFunctor_diag]

/-! ## The reflected relations hold -/

section Relations

variable (i : I) (lam : X)

theorem psiLQ_of_cupDotEF (m : ℕ) :
    psiLQ RD k sc (LinDiagram.of (cupDotEF RD lam i m)) =
      NF.dg (pres RD k sc) lam [up i, dn i] [] (dotCapEFLs i m) := by
  rw [cupDotEF, psiLQ_of_mkD, rls_append, rls_replicate]
  exact dg_dots_cap_dn RD k sc lam i m

theorem psiLQ_of_dotCapEF (m : ℕ) :
    psiLQ RD k sc (LinDiagram.of (dotCapEF RD lam i m)) =
      NF.dg (pres RD k sc) lam [] [up i, dn i] (cupDotEFLs i m) := by
  rw [dotCapEF, psiLQ_of_mkD, rls_append, rls_replicate]
  exact (dg_dots_cupUp RD k sc i lam m).symm

theorem psiLQ_of_cupDotFE (m : ℕ) :
    psiLQ RD k sc (LinDiagram.of (cupDotFE RD lam i m)) =
      NF.dg (pres RD k sc) lam [dn i, up i] [] (dotCapFELs i m) := by
  rw [cupDotFE, psiLQ_of_mkD, rls_append, rls_replicate]
  exact (dg_dots_cap_up RD k sc lam i m).symm

theorem psiLQ_of_dotCapFE (m : ℕ) :
    psiLQ RD k sc (LinDiagram.of (dotCapFE RD lam i m)) =
      NF.dg (pres RD k sc) lam [] [dn i, up i] (cupDotFELs i m) := by
  rw [dotCapFE, psiLQ_of_mkD, rls_append, rls_replicate]
  exact (dg_dots_cupDn RD k sc i lam m).symm

theorem psiLQ_decompEFSum :
    psiLQ RD k sc (decompEFSum RD k i lam) = (pres RD k sc).lin (decompEFSum RD k i lam) := by
  unfold decompEFSum
  rw [psiLQ_sum, NF.lin_finsum]
  simp only [psiLQ_sum, NF.lin_finsum, psiLQ_comp, Presentation.lin_comp,
    psiLQ_of_cupDotEF, psiLQ_of_dotCapEF, psiLQ_ccwL, Category.assoc]
  simp only [dotCapEF, cupDotEF, NF.lin_of_mkD]
  exact sum_triangle_swap (ip RD i lam).toNat (fun a g b =>
    NF.dg (pres RD k sc) lam [up i, dn i] [] (dotCapEFLs i a) ≫
      NF.ccwU (pres RD k sc) lam i (-ip RD i lam - 1 + g) ≫
      NF.dg (pres RD k sc) lam [] [up i, dn i] (cupDotEFLs i b))

theorem psiLQ_decompFESum :
    psiLQ RD k sc (decompFESum RD k i lam) = (pres RD k sc).lin (decompFESum RD k i lam) := by
  unfold decompFESum
  rw [psiLQ_sum, NF.lin_finsum]
  simp only [psiLQ_sum, NF.lin_finsum, psiLQ_comp, Presentation.lin_comp,
    psiLQ_of_cupDotFE, psiLQ_of_dotCapFE, psiLQ_cwL, Category.assoc]
  simp only [dotCapFE, cupDotFE, NF.lin_of_mkD]
  exact sum_triangle_swap (-ip RD i lam).toNat (fun a g b =>
    NF.dg (pres RD k sc) lam [dn i, up i] [] (dotCapFELs i a) ≫
      NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + g) ≫
      NF.dg (pres RD k sc) lam [] [dn i, up i] (cupDotFELs i b))

theorem psiLQ_curlRHS :
    psiLQ RD k sc (curlRHS RD k i lam) = (pres RD k sc).lin (curlRHS RD k i lam) := by
  unfold curlRHS
  rw [psiLQ_neg, psiLQ_sum, Presentation.lin_neg, NF.lin_finsum]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [psiLQ_comp, psiLQ_of, reflD_dots, psiLQ_bubR, psiLQ_cwL, Presentation.lin_comp,
    NF.lin_bubR, Presentation.lin_of]
  exact (NF.bubRU_comm (pres RD k sc) lam (up i) _ _).symm

theorem psiLQ_curlLHS (μ : X) :
    psiLQ RD k sc (curlLHS RD k i μ) = (pres RD k sc).lin (curlLHS RD k i μ) := by
  unfold curlLHS
  rw [psiLQ_sum, NF.lin_finsum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [psiLQ_comp, psiLQ_of, reflD_dots, psiLQ_bubL, psiLQ_ccwL, Presentation.lin_comp,
    NF.lin_bubL, Presentation.lin_of]
  exact (NF.bubLU_comm (pres RD k sc) μ (up i) _ _).symm

end Relations

/-- A KL III relation of `U_Q(g)`, reflected, holds if its reflection is a KL III relation of
`U_Q(g)`. -/
theorem lin_relation_self_of (r : Rel RD) (h : CL.relationCL RD k sc.withRone r = relation k r) :
    (pres RD k sc).lin (relation k r) = 0 :=
  lin_relation_of RD k sc r h

/-- **Every relation of `U_Q(g)`, reflected across the `x`-axis (with orientations inverted),
holds in `U_Q(g)`**, with the same scalars. -/
theorem psiLQ_relation (r : Rel RD) :
    psiLQ RD k sc (CL.relationCL RD k sc.withRone r) = 0 := by
  cases r with
  | cycDotR i μ =>
    show psiLQ RD k sc (relation k (.cycDotR i μ)) = 0
    rw [relation, psiLQ_sub, psiLQ_of, psiLQ_of, reflD_rotDotR, reflD_downDot, sub_eq_zero]
    exact (pres RD k sc).diag_eq_of_rel (.inr (.cycDotL i μ)) rfl
  | cycDotL i μ =>
    show psiLQ RD k sc (relation k (.cycDotL i μ)) = 0
    rw [relation, psiLQ_sub, psiLQ_of, psiLQ_of, reflD_rotDotL, reflD_downDot, sub_eq_zero]
    exact (pres RD k sc).diag_eq_of_rel (.inr (.cycDotR i μ)) rfl
  | cwNeg i lam α h =>
    show psiLQ RD k sc (relation k (.cwNeg i lam α h)) = 0
    rw [relation, psiLQ_of, reflD_cwReal]
    exact (pres RD k sc).lin_rel_self (.inr (.cwNeg i lam α h))
  | ccwNeg i lam α h =>
    show psiLQ RD k sc (relation k (.ccwNeg i lam α h)) = 0
    rw [relation, psiLQ_of, reflD_ccwReal]
    exact (pres RD k sc).lin_rel_self (.inr (.ccwNeg i lam α h))
  | cwOne i lam h =>
    have H : (pres RD k sc).lin (relation (RD := RD) k (.cwOne i lam h)) = 0 :=
      (pres RD k sc).lin_rel_self (.inr (.cwOne i lam h))
    show psiLQ RD k sc (relation k (.cwOne i lam h)) = 0
    rw [relation, Presentation.lin_sub] at H
    rw [relation, psiLQ_sub, psiLQ_of, psiLQ_of, reflD_cwReal]
    exact H
  | ccwOne i lam h =>
    have H : (pres RD k sc).lin (relation (RD := RD) k (.ccwOne i lam h)) = 0 :=
      (pres RD k sc).lin_rel_self (.inr (.ccwOne i lam h))
    show psiLQ RD k sc (relation k (.ccwOne i lam h)) = 0
    rw [relation, Presentation.lin_sub] at H
    rw [relation, psiLQ_sub, psiLQ_of, psiLQ_of, reflD_ccwReal]
    exact H
  | curlR i lam =>
    have H := lin_relation_of RD k sc (.curlR i lam) (relationCL_curlR RD k sc i lam)
    rw [relationCL_curlR]
    rw [relation, Presentation.lin_sub] at H
    rw [relation, psiLQ_sub, psiLQ_of, reflD_curlR, psiLQ_curlRHS]
    exact H
  | curlL i μ =>
    have H := lin_relation_of RD k sc (.curlL i μ) (relationCL_curlL RD k sc i μ)
    rw [relationCL_curlL]
    rw [relation, Presentation.lin_sub] at H
    rw [relation, psiLQ_sub, psiLQ_of, reflD_curlL, psiLQ_curlLHS]
    exact H
  | decompEF i lam =>
    have H := lin_relation_of RD k sc (.decompEF i lam) (relationCL_decompEF RD k sc i lam)
    rw [relationCL_decompEF]
    rw [relation, Presentation.lin_sub, Presentation.lin_add] at H
    rw [relation, psiLQ_sub, psiLQ_add, psiLQ_of, psiLQ_of, reflD_comp, reflD_crossl,
      reflD_crossr, psiLQ_decompEFSum]
    exact H
  | decompFE i lam =>
    have H := lin_relation_of RD k sc (.decompFE i lam) (relationCL_decompFE RD k sc i lam)
    rw [relationCL_decompFE]
    rw [relation, Presentation.lin_sub, Presentation.lin_add] at H
    rw [relation, psiLQ_sub, psiLQ_add, psiLQ_of, psiLQ_of, reflD_comp, reflD_crossl,
      reflD_crossr, psiLQ_decompFESum]
    exact H
  | cycCrossR j i μ =>
    have H : (pres RD k sc).lin ((((sc.withRone.t i j)⁻¹ : kˣ) : k) •
        LinDiagram.of (rotCrossL RD i j μ) - LinDiagram.of (downCross RD i j μ)) = 0 :=
      lin_relationCL RD k sc (.cycCrossL i j μ)
    show psiLQ RD k sc ((((sc.withRone.t i j)⁻¹ : kˣ) : k) •
      LinDiagram.of (rotCrossR RD j i μ) - LinDiagram.of (downCross RD j i μ)) = 0
    rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of,
      Presentation.lin_of] at H
    rw [psiLQ_sub, psiLQ_smul, psiLQ_of, psiLQ_of, reflD_rotCrossR, reflD_downCross]
    exact H
  | cycCrossL j i μ =>
    have H : (pres RD k sc).lin ((((sc.withRone.t j i)⁻¹ : kˣ) : k) •
        LinDiagram.of (rotCrossR RD i j μ) - LinDiagram.of (downCross RD i j μ)) = 0 :=
      lin_relationCL RD k sc (.cycCrossR i j μ)
    show psiLQ RD k sc ((((sc.withRone.t j i)⁻¹ : kˣ) : k) •
      LinDiagram.of (rotCrossL RD j i μ) - LinDiagram.of (downCross RD j i μ)) = 0
    rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of,
      Presentation.lin_of] at H
    rw [psiLQ_sub, psiLQ_smul, psiLQ_of, psiLQ_of, reflD_rotCrossL, reflD_downCross]
    exact H
  | downupEF i j h μ =>
    have H : (pres RD k sc).lin (LinDiagram.of (crossl RD i j μ ≫ crossr RD i j μ) -
        (sc.withRone.t j i : k) • LinDiagram.of (𝟙 _)) = 0 :=
      lin_relationCL RD k sc (.downupEF i j h μ)
    show psiLQ RD k sc (LinDiagram.of (crossl RD i j μ ≫ crossr RD i j μ) -
      (sc.withRone.t j i : k) • LinDiagram.of (𝟙 _)) = 0
    rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of,
      Presentation.lin_of] at H
    rw [psiLQ_sub, psiLQ_smul, psiLQ_of, psiLQ_of, reflD_comp, reflD_crossl, reflD_crossr]
    exact H
  | downupFE i j h μ =>
    have H : (pres RD k sc).lin (LinDiagram.of (crossr RD j i μ ≫ crossl RD j i μ) -
        (sc.withRone.t i j : k) • LinDiagram.of (𝟙 _)) = 0 :=
      lin_relationCL RD k sc (.downupFE i j h μ)
    show psiLQ RD k sc (LinDiagram.of (crossr RD j i μ ≫ crossl RD j i μ) -
      (sc.withRone.t i j : k) • LinDiagram.of (𝟙 _)) = 0
    rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of,
      Presentation.lin_of] at H
    rw [psiLQ_sub, psiLQ_smul, psiLQ_of, psiLQ_of, reflD_comp, reflD_crossl, reflD_crossr]
    exact H
  | klr μ r =>
    rw [show CL.relationCL RD k sc.withRone (.klr μ r) =
      upLin RD k μ (KLR.Diagram.relation k (CL.qCL sc) r) from rel_klr RD k sc μ r]
    rw [psiLQ_upLin, KPsi.lin_kreflLin_relation, Functor.map_zero]

/-! ## The zigzag relations and the interchange law -/

/-- The reflection of the left zigzag of `c` is the right zigzag of `c*`. -/
theorem diag_reflD_zigLQ (c : Col I X) :
    (pres RD k sc).diag (reflD (Pivotal.zigL (inv RD).toColourDuality c)) = 𝟙 _ := by
  refine (pres RD k sc).diag_eq_id_of_layers _
    (Pivotal.zigR (inv RD).toColourDuality ((inv RD).dual c))
    (Obj.ext rfl (by show [c] = [(inv RD).dual ((inv RD).dual c)]; rw [inv_dual_dual])) ?_
    ((zigzags RD k sc) ((inv RD).dual c)).2
  simp only [layers_reflD, rrev, Pivotal.zigL, Pivotal.zigR, Diagram.layers_leftZigzag,
    Diagram.layers_rightZigzag, Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil,
    Layer.wl, Layer.wr, rlay, Psi.gen, inv_dual_dual]
  rfl

/-- The reflection of the right zigzag of `c` is the left zigzag of `c*`. -/
theorem diag_reflD_zigRQ (c : Col I X) :
    (pres RD k sc).diag (reflD (Pivotal.zigR (inv RD).toColourDuality c)) = 𝟙 _ := by
  refine (pres RD k sc).diag_eq_id_of_layers _
    (Pivotal.zigL (inv RD).toColourDuality ((inv RD).dual c))
    (Obj.ext ((inv RD).src_dual c).symm rfl) ?_ ((zigzags RD k sc) ((inv RD).dual c)).1
  simp only [layers_reflD, rrev, Pivotal.zigL, Pivotal.zigR, Diagram.layers_leftZigzag,
    Diagram.layers_rightZigzag, Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil,
    Layer.wl, Layer.wr, rlay, Psi.gen]
  rw [(inv RD).src_dual c]

/-- The reflection of the interchange law is the interchange law. -/
theorem psiLQ_interchange (x : InterchangeData (psig RD)) (hx : x.Valid) :
    psiLQ RD k sc (InterchangeData.rel k hx) = 0 := by
  let x' : InterchangeData (psig RD) := ⟨x.start, gen x.g, x.mid, gen x.h⟩
  have e₁ : x'.gh₁ = rlay x.hg₂ := by
    simp [x', InterchangeData.gh₁, InterchangeData.hg₂, rlay, gen_dom]
  have e₂ : x'.gh₂ = rlay x.hg₁ := by
    simp [x', InterchangeData.gh₂, InterchangeData.hg₁, rlay, gen_cod]
  have e₃ : x'.hg₁ = rlay x.gh₂ := by
    simp [x', InterchangeData.hg₁, InterchangeData.gh₂, rlay, gen_dom]
  have e₄ : x'.hg₂ = rlay x.gh₁ := by
    simp [x', InterchangeData.hg₂, InterchangeData.gh₁, rlay, gen_cod]
  have hx' : x'.Valid :=
    ⟨e₁ ▸ rlay_valid hx.hg₂, e₂ ▸ rlay_valid hx.hg₁, e₃ ▸ rlay_valid hx.gh₂,
      e₄ ▸ rlay_valid hx.gh₁⟩
  have hw : x'.dom.WhiskerOK (Obj.nil x.start) [] := ⟨trivial, rfl, trivial⟩
  have ha : x'.dom.whisker (Obj.nil x.start) [] = x.cod :=
    Obj.ext rfl (by simp [x', InterchangeData.dom, InterchangeData.cod, Obj.whisker, Obj.nil,
      gen_dom])
  have hb : x'.cod.whisker (Obj.nil x.start) [] = x.dom :=
    Obj.ext rfl (by simp [x', InterchangeData.dom, InterchangeData.cod, Obj.whisker, Obj.nil,
      gen_cod])
  have key := (pres RD k sc).diag_interchange x' hx' (Obj.nil x.start) [] hw ha hb
  have hs : ∀ y : InterchangeData (psig RD), ((y.sign : ℤ) : k) = 1 := by
    intro y; simp [InterchangeData.sign, Signature.IsEven.odd_eq_false]
  rw [hs, one_smul] at key
  rw [InterchangeData.rel, psiLQ_sub, psiLQ_smul, psiLQ_of, psiLQ_of, hs, one_smul, sub_eq_zero]
  refine ((pres RD k sc).diag_eq_of_layers_eq ?_).trans (key.symm.trans
    ((pres RD k sc).diag_eq_of_layers_eq ?_))
  · simp only [layers_reflD, rrev, InterchangeData.ghDiagram, InterchangeData.hgDiagram,
      Diagram.layers_mk, Diagram.layers_cast, Diagram.layers_whisker, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, ← e₃, ← e₄]
    simp [Layer.whisker, Obj.nil]; exact ⟨rfl, rfl⟩
  · simp only [layers_reflD, rrev, InterchangeData.ghDiagram, InterchangeData.hgDiagram,
      Diagram.layers_mk, Diagram.layers_cast, Diagram.layers_whisker, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, ← e₁, ← e₂]
    simp [Layer.whisker, Obj.nil]; exact ⟨rfl, rfl⟩

/-- Every defining relation of `U_Q(g)` is reflected to a relation of `U_Q(g)`. -/
theorem psiLQ_rel (r : (pres RD k sc).Rel) : psiLQ RD k sc ((pres RD k sc).rel r) = 0 := by
  rcases r with ((e | c | c) | r)
  · exact e.elim
  · show psiLQ RD k sc (LinDiagram.of (Pivotal.zigL _ c) - LinDiagram.of (𝟙 _)) = 0
    rw [psiLQ_sub, psiLQ_of, psiLQ_of, diag_reflD_zigLQ]
    exact sub_self _
  · show psiLQ RD k sc (LinDiagram.of (Pivotal.zigR _ c) - LinDiagram.of (𝟙 _)) = 0
    rw [psiLQ_sub, psiLQ_of, psiLQ_of, diag_reflD_zigRQ]
    exact sub_self _
  · exact psiLQ_relation r

variable (RD k sc)

/-- The reflection functor on the free 2-category respects all the relations of `U_Q(g)`. -/
theorem psiFreeQ_respects : (pres RD k sc).Respects (psiFreeQ RD k sc) where
  rel r u v hw := by
    rw [freeLift_psiFreeQ, psiLQ_whisker, psiLQ_rel, Presentation.whisk_zero]; rfl
  interchange x hx u v hw := by
    rw [freeLift_psiFreeQ, psiLQ_whisker, psiLQ_interchange, Presentation.whisk_zero]; rfl

/-! ## The 2-functor `ψ̃ : U_Q(g) → U_Q(g)^co` -/

/-- **The symmetry `ψ̃ : U_Q(g) → U_Q(g)^co`** (KL III (3.44) for Cautis–Lauda's `U_Q(g)`):
reflection of diagrams across the `x`-axis, with the orientations of the strands inverted. It is
the identity on objects and 1-morphisms and contravariant on 2-morphisms. -/
def psiUQ : (pres RD k sc).Presented ⥤ (pres RD k sc).Presentedᵒᵖ :=
  (pres RD k sc).lift (psiFreeQ_respects RD k sc)

instance : (psiUQ RD k sc).Additive := by unfold psiUQ; infer_instance

instance : (psiUQ RD k sc).Linear k := by unfold psiUQ; infer_instance

variable {RD k sc}

@[simp] theorem psiUQ_obj (a : Obj (psig RD)) :
    (psiUQ RD k sc).obj ((pres RD k sc).obj a) = op ((pres RD k sc).obj a) :=
  rfl

theorem psiUQ_lin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (psiUQ RD k sc).map ((pres RD k sc).lin f) = (psiLQ RD k sc f).op := by
  unfold psiUQ; rw [Presentation.lift_lin, freeLift_psiFreeQ]

/-- `ψ̃` on a diagram: the reflected diagram. -/
@[simp] theorem psiUQ_diag {a b : Obj (psig RD)} (d : a ⟶ b) :
    (psiUQ RD k sc).map ((pres RD k sc).diag d) = ((pres RD k sc).diag (reflD d)).op := by
  unfold psiUQ; rw [Presentation.lift_diag]; rfl

/-- `ψ̃` on normal-form diagrams: reverse the layers and reflect each generator. -/
theorem psiUQ_dg (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    (psiUQ RD k sc).map (NF.dg (pres RD k sc) μ s t ls) =
      (NF.dg (pres RD k sc) μ t s (rls ls)).op := by
  by_cases h : SChain s ls t
  · rw [NF.dg_of h, psiUQ_diag, reflD_mkD, NF.dg_of]
  · have h₂ : ¬ SChain t (rls ls) s := by
      intro h'
      have := sChain_rls h'
      rw [rls_rls] at this
      exact h this
    rw [NF.dg_of_not h, Functor.map_zero, NF.dg_of_not h₂]
    rfl

/-- **`ψ̃` is a strict 2-functor**: it commutes with whiskering. -/
theorem psiUQ_whisk {a b : Obj (psig RD)} (f : (pres RD k sc).obj a ⟶ (pres RD k sc).obj b)
    (u : Obj (psig RD)) (v : List (psig RD).Colour) :
    (psiUQ RD k sc).map ((pres RD k sc).whisk f u v) =
      ((pres RD k sc).whisk ((psiUQ RD k sc).map f).unop u v).op := by
  obtain ⟨g, rfl⟩ := (pres RD k sc).lin_surjective f
  rw [Presentation.whisk_lin, psiUQ_lin, psiUQ_lin, Quiver.Hom.unop_op]
  congr 1
  by_cases h : a.WhiskerOK u v
  · rw [LinDiagram.whisk_of_ok _ h, psiLQ_whisker]
  · rw [LinDiagram.whisk_of_not_ok _ h, psiLQ_zero]
    by_cases hg : reflLin k g = 0
    · rw [psiLQ, hg, Presentation.lin_zero, Presentation.whisk_zero]
    · have hb : ¬ b.WhiskerOK u v := fun hb => h (LinDiagram.whiskerOK_of_ne_zero hg hb)
      rw [psiLQ, Presentation.whisk_lin, LinDiagram.whisk_of_not_ok _ hb, Presentation.lin_zero]

/-- The reflection of a linear combination of diagrams that vanishes in `U_Q(g)` vanishes in
`U_Q(g)`. -/
theorem lin_reflLin_eq_zero {a b : Obj (psig RD)} {f : LinDiagram k a b}
    (hf : (pres RD k sc).lin f = 0) : (pres RD k sc).lin (reflLin k f) = 0 := by
  have h := psiUQ_lin (sc := sc) f
  rw [hf, Functor.map_zero] at h
  exact (congrArg Quiver.Hom.unop h).symm

end Categorification.KL3.Diagram.CLQ
