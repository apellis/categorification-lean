/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUpWordsPresentation
import Categorification.Diagrams.KL3.SymmetrySigmaMatrix

/-!
# The signed reflection of upward words and the vertical flip

Through an arbitrary presentation `P` of the Cautis–Lauda calculus in which the upward KLR
relations hold for some symmetric `Q'`, the signed reflection of a KLR diagram, placed on
upward strands, acts on the words of a Rouquier family as the vertical flip `σ` of the KLR
algebra followed by the KLR action of the family (`RouqFamily.upActP_ksMat_toDiagFree`). The
KLR algebra of the family may have different parameters `Q`: on the free algebra on the KLR
generators both flips are given by the same formulas (`KLRAlgebra.comp_sigmaFree_eq`). This is
used in the proof of Webster, arXiv:1309.3796v3, Lemma 4.29, to read off the vacuum
evaluation of a reflected diagram from the projected matrix entries of the KLR action.
-/

noncomputable section

namespace Categorification

open CategoryTheory

namespace KLR.KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ν : Multiset I}
  {Q Q' : I → I → MvPolynomial (Fin 2) k} {W : Type*} [Semiring W] [Algebra k W]

/-- **The vertical flip does not depend on the parameters**: two algebra homomorphisms out of
KLR algebras with possibly different parameters which agree on the free algebra on the
generators also agree after the vertical flip on the free algebra. -/
theorem comp_sigmaFree_eq (F : KLRAlgebra k Q ν →ₐ[k] W) (F' : KLRAlgebra k Q' ν →ₐ[k] W)
    (h : F.comp (mk k Q ν) = F'.comp (mk k Q' ν)) :
    F.comp (sigmaFree k Q ν) = F'.comp (sigmaFree k Q' ν) := by
  have hg (g : Gen ν) : F (mk k Q ν (FreeAlgebra.ι k g)) = F' (mk k Q' ν (FreeAlgebra.ι k g)) :=
    DFunLike.congr_fun h _
  refine FreeAlgebra.hom_ext (funext fun g => ?_)
  cases g with
  | idem i =>
    change F (sigmaFree k Q ν (fe k ν i)) = F' (sigmaFree k Q' ν (fe k ν i))
    rw [sigmaFree_fe, sigmaFree_fe]
    exact hg (.idem i.rev)
  | dot a =>
    change F (sigmaFree k Q ν (fx k ν a)) = F' (sigmaFree k Q' ν (fx k ν a))
    rw [sigmaFree_fx, sigmaFree_fx]
    exact hg (.dot a.rev)
  | cross j =>
    change F (sigmaFree k Q ν (fψ k ν j)) = F' (sigmaFree k Q' ν (fψ k ν j))
    rw [sigmaFree_fψ, sigmaFree_fψ, sigmaψ, sigmaψ]
    split_ifs
    · simp only [map_mul, sgnE, map_sum, map_smul]
      congr 1
      · exact hg (.cross _)
      · exact Finset.sum_congr rfl fun i _ => congrArg _ (hg (.idem i.rev))
    · simp

end KLR.KLRAlgebra

namespace TwoRep

open CategoryTheory.Bicategory QuantumGroup UDot KL3.Diagram StringDiagrams
  Diagrams.BicatInterp

universe w v u

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)]
  {I : Type u} [DecidableEq I] {C : CartanDatum I} {X Y : Type v} [AddCommGroup X]
  [AddCommGroup Y] {RD : WeightDatum C X Y}

namespace RouqFamily

variable (S : RouqFamily (B := B) RD) {ν : Multiset I}
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  (Sc : CL.CLScalars C k) (P : Presentation.{w, max u v} (psig RD) k)
  (hrel : ∀ (r : P.Rel) {s t : X} (ha : Cond (S := psig RD) s t (P.dom r))
    (hb : Cond (S := psig RD) s t (P.cod r)),
    admissibleMap (S.genImg Sc) ha hb (P.rel r) = 0)

/-- **The signed reflection of upward words is the vertical flip.** For a presentation `P` in
which the upward KLR relations hold for a symmetric `Q'`, and a Rouquier family satisfying the
mixed upward equations for `Q`, evaluating the signed reflection (`ksMat`) of the diagram of
`a`, placed on upward strands by `upFunctorC`, is the KLR action of the vertical flip of `a`. -/
theorem upActP_ksMat_toDiagFree {Q Q' : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
    (hQ : KLR.KLRSymm Q) (hQ' : KLR.KLRSymm Q') (hK : CL.KLRHolds P Q') (μ : X)
    (a : FreeAlgebra k (KLR.Gen ν)) :
    S.upActP Sc P hrel μ ν (matEndMap k (CL.upFunctorC P Q' hK μ) _
      (KSig.ksMat k Q' ν hQ' (KLR.Diagram.toDiagFree k Q' ν a))) =
      klrAct H μ (KLR.KLRAlgebra.sigma hQ (KLR.KLRAlgebra.mk k Q ν a)) := by
  have h₁ := DFunLike.congr_fun (KSig.ksMat_comp_toDiagFree (k := k) (ν := ν) hQ') a
  simp only [AlgHom.comp_apply] at h₁
  rw [h₁, KLR.KLRAlgebra.sigma_apply, KLR.KLRAlgebra.sigmaHom_mk]
  let F : KLR.KLRAlgebra k Q' ν →ₐ[k] S.WordEnd μ ν :=
    (S.upActP Sc P hrel μ ν).comp ((matEndMap k (CL.upFunctorC P Q' hK μ) _).comp
      (KLR.Diagram.diagREquiv k Q' ν).toAlgHom)
  have hF : F.comp (KLR.KLRAlgebra.mk k Q' ν) = (klrAct H μ).comp (KLR.KLRAlgebra.mk k Q ν) := by
    refine FreeAlgebra.hom_ext (funext fun g => ?_)
    have h₂ := DFunLike.congr_fun (S.upActP_comp_upFunctorC Sc P hrel Q' hK μ ν)
      (FreeAlgebra.ι k g)
    change F (KLR.KLRAlgebra.mk k Q' ν (FreeAlgebra.ι k g)) =
      klrAct H μ (KLR.KLRAlgebra.mk k Q ν (FreeAlgebra.ι k g))
    rw [klrAct_mk, ← h₂]
    change S.upActP Sc P hrel μ ν (matEndMap k (CL.upFunctorC P Q' hK μ) _
        (KLR.Diagram.toDiagR k Q' ν (KLR.KLRAlgebra.mk k Q' ν (FreeAlgebra.ι k g)))) =
      S.upActP Sc P hrel μ ν (matEndMap k (CL.upFunctorC P Q' hK μ) _
        (KLR.Diagram.toDiagFree k Q' ν (FreeAlgebra.ι k g)))
    rw [KLR.Diagram.toDiagR_mk]
  exact DFunLike.congr_fun (KLR.KLRAlgebra.comp_sigmaFree_eq F (klrAct H μ) hF) a

end RouqFamily

end TwoRep

end Categorification
