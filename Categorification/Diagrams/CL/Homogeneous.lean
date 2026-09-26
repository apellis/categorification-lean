/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.Presentation
import Categorification.Diagrams.KL3.SignedSlnErratum

/-!
# `U_Q(g)` is graded

S. Cautis, A. D. Lauda, arXiv:1111.1431v3, Definition 1.1: `U_Q(g)` is a graded 2-category, with
the degrees of the generators listed in the display of Definition 1.1 (the same as KL III
Definition 3.1: `(α_i, α_i)` for dots, `-(α_i, α_j)` for crossings, `d_i ± (λ, α_i)` for cups and
caps; `deg RD` of `Categorification.Diagrams.KL3.Basic`).

We check that every relation of `presCL RD k S` (and of `presCLDown RD k S`) is homogeneous for
`deg RD`, for every choice of scalars `S`: the scalars only rescale individual terms of the
relations of KL III, and the polynomials `Q_{ij}` are weighted homogeneous of the required degree
by the condition `eq_pq` (`qCL_isWeightedHomogeneous`, `qbar_qCL_isWeightedHomogeneous`).
Hence the library's grading theory applies (`Presentation.isInternal_homDeg`).

## Main results

* `relationR_mem`: the KLR relations with scalars `r` are homogeneous for the KLR degree
  whenever `Q`, `Q̄` are weighted homogeneous of the KL degrees.
* `presCL_isHomogeneous`, `presCLDown_isHomogeneous`.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation MvPolynomial

universe w u v

/-! ## The KLR relations with scalars -/

section KLR

open KLR.Diagram

variable {I : Type u} {C : CartanDatum I} {k : Type w} [CommRing k]

local notation "HK" => LinDiagram.homDeg k (degK (I := I) (C := C))

/-- The KLR relations with scalars `r` are homogeneous for the KLR degree, provided `Q_{cd}` and
`Q̄_{cd}` are weighted homogeneous of the degrees required by KL I/II. -/
theorem relationR_mem (Q : I → I → MvPolynomial (Fin 2) k)
    (hQ : ∀ c d, c ≠ d →
      (Q c d).IsWeightedHomogeneous ![C.dot c c, C.dot d d] (-2 * C.dot c d))
    (hQbar : ∀ c d, c ≠ d → (KLR.qbar (Q c d)).IsWeightedHomogeneous
      ![C.dot c c, C.dot d d, C.dot c c] (-2 * C.dot c d - C.dot c c))
    (r : I → k) (x : KLR.Diagram.Rel I) :
    ∃ d, relationR k Q r x ∈ HK x.dom x.cod d := by
  cases x with
  | slideLEq c =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (degK_mem _ ?_) (degK_mem _ ?_))
      (Submodule.smul_mem _ _ (degK_mem _ rfl))⟩ <;> (degK_tac; try ring)
  | slideREq c =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (degK_mem _ ?_) (degK_mem _ ?_))
      (Submodule.smul_mem _ _ (degK_mem _ rfl))⟩ <;> (degK_tac; try ring)
  | braidQ c d h =>
    refine ⟨-2 * C.dot c d - C.dot c c, Submodule.sub_mem _ (Submodule.sub_mem _ (degK_mem _ ?_)
      (degK_mem _ ?_)) (Submodule.smul_mem _ _
      (ncEval_mem_homDeg _ _ ![C.dot c c, C.dot d d, C.dot c c] ?_ _ _ (hQbar c d h)))⟩
    · degK_tac; try (rw [C.symm d c]; ring)
    · degK_tac; try (rw [C.symm d c]; ring)
    · intro t; fin_cases t <;> exact degK_mem _ (by degK_tac)
  | sqEq c => exact klrQ_relation_mem Q hQ hQbar (.sqEq c)
  | sqNe c d h => exact klrQ_relation_mem Q hQ hQbar (.sqNe c d h)
  | slideLNe c d h => exact klrQ_relation_mem Q hQ hQbar (.slideLNe c d h)
  | slideRNe c d h => exact klrQ_relation_mem Q hQ hQbar (.slideRNe c d h)
  | braid c d e h => exact klrQ_relation_mem Q hQ hQbar (.braid c d e h)

end KLR

/-! ## Downward strands -/

section Downward

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

local notation "HD" => LinDiagram.homDeg k (deg RD)

theorem degree_dnDiag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (g : a ⟶ b) :
    Diagram.degree (deg RD) (dnDiag RD μ g) = Diagram.degree (degK (I := I) (C := C)) g := by
  simp only [Diagram.degree, layers_dnDiag, List.map_map]
  congr 1
  refine List.map_congr_left fun L _ => ?_
  show deg RD ((dnShape L.gen).gen RD _) = degK L.gen
  rw [deg_gen]
  cases h : L.gen <;> rfl

theorem dnLin_mem (μ : X) {a b : Obj (KLR.Diagram.sig I)} {f : LinDiagram k a b} {d : ℤ}
    (hf : f ∈ LinDiagram.homDeg k (degK (I := I) (C := C)) a b d) :
    dnLin RD k μ f ∈ HD _ _ d := by
  classical
  rw [LinDiagram.homDeg, Finsupp.mem_supported] at hf ⊢
  intro g hg
  obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
  show Diagram.degree (deg RD) (dnDiag RD μ g') = d
  rw [degree_dnDiag]; exact hf hg'

end Downward

/-! ## All relations -/

section All

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) {k : Type w} [CommRing k]

local notation "HD" => LinDiagram.homDeg k (deg RD)

/-- Every relation of `presCL` is homogeneous. -/
theorem relationCL_mem (S : CLScalars C k) (r : Rel RD) :
    ∃ d, relationCL RD k S r ∈ HD r.dom r.cod d := by
  cases r with
  | klr μ r =>
    obtain ⟨d, hd⟩ := relationR_mem (qCL S) (fun _ _ h => qCL_isWeightedHomogeneous S h)
      (fun _ _ h => qbar_qCL_isWeightedHomogeneous S h) (fun c => (S.r c : k)) r
    exact ⟨d, upLin_mem (RD := RD) μ hd⟩
  | curlR i lam => exact ⟨_, Submodule.sub_mem _
      (LinDiagram.of_mem_homDeg' (degree_curlR i lam)) (Submodule.smul_mem _ _ (curlRHS_mem i lam))⟩
  | curlL i μ => exact ⟨_, Submodule.sub_mem _
      (LinDiagram.of_mem_homDeg' (degree_curlL i μ)) (Submodule.smul_mem _ _ (curlLHS_mem i μ))⟩
  | decompEF i lam =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (LinDiagram.id_mem_homDeg _)
      (Submodule.smul_mem _ _ (LinDiagram.of_mem_homDeg' ?_))) (decompEFSum_mem i lam)⟩
    rw [Diagram.degree_comp, degree_crossl, degree_crossr, add_zero]
  | decompFE i lam =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (LinDiagram.id_mem_homDeg _)
      (Submodule.smul_mem _ _ (LinDiagram.of_mem_homDeg' ?_))) (decompFESum_mem i lam)⟩
    rw [Diagram.degree_comp, degree_crossl, degree_crossr, add_zero]
  | cycCrossR j i μ => exact ⟨_, Submodule.sub_mem _
      (Submodule.smul_mem _ _ (LinDiagram.of_mem_homDeg' (degree_rotCrossR j i μ)))
      (LinDiagram.of_mem_homDeg' (degree_downCross j i μ))⟩
  | cycCrossL j i μ => exact ⟨_, Submodule.sub_mem _
      (Submodule.smul_mem _ _ (LinDiagram.of_mem_homDeg' (degree_rotCrossL j i μ)))
      (LinDiagram.of_mem_homDeg' (degree_downCross j i μ))⟩
  | downupEF i j h μ =>
    refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_)
      (Submodule.smul_mem _ _ (LinDiagram.id_mem_homDeg _))⟩
    rw [Diagram.degree_comp, degree_crossl, degree_crossr, add_zero]
  | downupFE i j h μ =>
    refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_)
      (Submodule.smul_mem _ _ (LinDiagram.id_mem_homDeg _))⟩
    rw [Diagram.degree_comp, degree_crossl, degree_crossr, add_zero]
  | cycDotR i μ => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.cycDotR i μ))
  | cycDotL i μ => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.cycDotL i μ))
  | cwNeg i lam α h => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.cwNeg i lam α h))
  | ccwNeg i lam α h => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.ccwNeg i lam α h))
  | cwOne i lam h => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.cwOne i lam h))
  | ccwOne i lam h => exact pres_isHomogeneous (RD := RD) (k := k) (.inr (.ccwOne i lam h))

/-- **`U_Q(g)` is graded**: `presCL RD k S` is homogeneous for the degrees of Definition 1.1, for
every choice of scalars `S`. -/
theorem presCL_isHomogeneous (S : CLScalars C k) : (presCL RD k S).IsHomogeneous (deg RD) :=
  addRels_isHomogeneous RD _ (relationCL_mem RD S)

/-- `presCLDown RD k S` (with the KLR relations for `Q'` on downward strands) is homogeneous. -/
theorem presCLDown_isHomogeneous (S : CLScalars C k) :
    (presCLDown RD k S).IsHomogeneous (deg RD) := by
  rintro (r | ⟨μ, x⟩)
  · exact presCL_isHomogeneous RD S r
  · obtain ⟨d, hd⟩ := relationR_mem (qCL S.dual)
      (fun _ _ h => qCL_isWeightedHomogeneous S.dual h)
      (fun _ _ h => qbar_qCL_isWeightedHomogeneous S.dual h) (fun c => (S.dual.r c : k)) x
    exact ⟨d, dnLin_mem μ hd⟩

/-- Every Hom-space of `U_Q(g)` is the direct sum of its homogeneous components. -/
theorem isInternal_homDeg (S : CLScalars C k) (a b : Obj (psig RD)) :
    DirectSum.IsInternal ((presCL RD k S).homDeg (deg RD) a b) :=
  Presentation.isInternal_homDeg (presCL_isHomogeneous RD S) a b

end All

end Categorification.KL3.Diagram.CL
