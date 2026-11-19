/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUpWords
import Categorification.Diagrams.CL.NoMix

/-!
# Upward words through an arbitrary presentation of the Cautis–Lauda calculus

`RouqUpWords` compares the action of KL III's `U` on upward words of a Rouquier family with the
direct action of the KLR algebra (`RouqFamily.upAct_comp_toUEnd`), for the KL scalars. The same
comparison holds for any presentation `P` on the signature of `U` whose relations hold under
the admissible interpretation `S.genImg Sc` and in which the upward KLR relations hold for some
`Q` (`CL.KLRHolds P Q`). This is used for the cyclotomic Cautis–Lauda presentations of the
proof of Webster, arXiv:1309.3796v3, Lemma 4.29, whose scalars are not the KL scalars.

## Main definitions and results

* `RouqFamily.upEvalP`, `RouqFamily.upActP`: the evaluation of 2-morphisms of `P` between
  upward words, and the algebra homomorphism it induces on matrices.
* `RouqFamily.upActP_comp_upFunctorC`: on the free algebra on the KLR generators, the composite
  of the diagrammatic map `toDiagFree`, the upward functor `upFunctorC` and `upActP` is the
  action `klrActFree` of the Rouquier family.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp

universe w v u

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)]
  {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}

namespace RouqFamily

open RouqData

variable (S : RouqFamily (B := B) RD) {ν : Multiset I}
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  (Sc : CL.CLScalars C k) (P : Presentation.{w, max u v} (psig RD) k)
  (hrel : ∀ (r : P.Rel) {s t : X} (ha : Cond (S := psig RD) s t (P.dom r))
    (hb : Cond (S := psig RD) s t (P.cod r)),
    admissibleMap (S.genImg Sc) ha hb (P.rel r) = 0)

/-- **The evaluation of a 2-morphism of `P` between upward words** `E_t 1_μ → E_{t'} 1_μ`, as a
2-morphism between the words of `t` and `t'` in the Rouquier family. -/
def upEvalP (μ : X) {t t' : KLR.Seq ν}
    (f : P.obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      P.obj (ob RD μ (ups (KLR.Diagram.word t')))) :
    S.wordCell μ t ⟶ S.wordCell μ t' :=
  (S.upIso μ t (cond_word μ t)).inv ≫
    admissibleQuotientMap (S.genImg Sc) P hrel
      Signature.IsEven.odd_eq_false (cond_word μ t) (cond_word μ t') f ≫
    (S.upIso μ t' (cond_word μ t')).hom

theorem upEvalP_add (μ : X) {t t' : KLR.Seq ν}
    (f g : P.obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      P.obj (ob RD μ (ups (KLR.Diagram.word t')))) :
    S.upEvalP Sc P hrel μ (f + g) = S.upEvalP Sc P hrel μ f + S.upEvalP Sc P hrel μ g :=
  (congrArg (fun φ => (S.upIso μ t (cond_word μ t)).inv ≫ φ ≫
    (S.upIso μ t' (cond_word μ t')).hom) (admissibleQuotientMap_add _ _ _ _ _ _ f g)).trans
    (conj_add _ _ _ _)

theorem upEvalP_smul (μ : X) {t t' : KLR.Seq ν} (r : k)
    (f : P.obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      P.obj (ob RD μ (ups (KLR.Diagram.word t')))) :
    S.upEvalP Sc P hrel μ (r • f) = r • S.upEvalP Sc P hrel μ f :=
  (congrArg (fun φ => (S.upIso μ t (cond_word μ t)).inv ≫ φ ≫
    (S.upIso μ t' (cond_word μ t')).hom) (admissibleQuotientMap_smul _ _ _ _ _ _ r f)).trans
    (conj_smul _ _ _ _)

theorem upEvalP_zero (μ : X) {t t' : KLR.Seq ν} :
    S.upEvalP Sc P hrel μ (0 : P.obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      P.obj (ob RD μ (ups (KLR.Diagram.word t')))) = 0 := by
  have h := S.upEvalP_smul Sc P hrel μ (t := t) (t' := t') (0 : k) 0
  rwa [zero_smul, zero_smul] at h

theorem upEvalP_id (μ : X) (t : KLR.Seq ν) :
    S.upEvalP Sc P hrel μ (𝟙 (P.obj (ob RD μ (ups (KLR.Diagram.word t))))) = 𝟙 _ :=
  (congrArg (fun φ => (S.upIso μ t (cond_word μ t)).inv ≫ φ ≫
    (S.upIso μ t (cond_word μ t)).hom) (admissibleQuotientMap_id _ _ _ _ _)).trans
    (conj_id _)

theorem upEvalP_comp (μ : X) {t t' t'' : KLR.Seq ν}
    (f : P.obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      P.obj (ob RD μ (ups (KLR.Diagram.word t'))))
    (g : P.obj (ob RD μ (ups (KLR.Diagram.word t'))) ⟶
      P.obj (ob RD μ (ups (KLR.Diagram.word t'')))) :
    S.upEvalP Sc P hrel μ (f ≫ g) = S.upEvalP Sc P hrel μ f ≫ S.upEvalP Sc P hrel μ g :=
  (congrArg (fun φ => (S.upIso μ t (cond_word μ t)).inv ≫ φ ≫
    (S.upIso μ t'' (cond_word μ t'')).hom)
      (admissibleQuotientMap_comp _ _ _ _ _ (cond_word μ t') _ f g)).trans
    (conj_comp _ (S.upIso μ t' (cond_word μ t')) _ _ _)

variable [DecidableEq I]

/-- **The action of `P` on the Rouquier family, on upward words of weight `ν`**: the algebra
homomorphism `END_P(⊕_t E_t 1_μ) → END(⊕_t E_t)` evaluating each entry by `upEvalP`. -/
def upActP (μ : X) (ν : Multiset I) :
    KLR.Diagram.MatEnd (fun t : KLR.Seq ν => P.obj (ob RD μ (ups (KLR.Diagram.word t))))
    →ₐ[k] S.WordEnd μ ν where
  toFun f i j := S.upEvalP Sc P hrel μ (f i j)
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [KLR.Diagram.MatEnd.one_apply_self]
      exact S.upEvalP_id Sc P hrel μ i
    · simp only [KLR.Diagram.MatEnd.one_apply_of_ne h]
      exact S.upEvalP_zero Sc P hrel μ
  map_mul' f g := by
    ext i l
    change S.upEvalP Sc P hrel μ (∑ j, g i j ≫ f j l) =
      ∑ j, S.upEvalP Sc P hrel μ (g i j) ≫ S.upEvalP Sc P hrel μ (f j l)
    exact (map_sum (AddMonoidHom.mk' (fun φ => S.upEvalP Sc P hrel μ (t := i) (t' := l) φ)
      (S.upEvalP_add Sc P hrel μ)) (fun j => g i j ≫ f j l) Finset.univ).trans
      (Finset.sum_congr rfl fun j _ => S.upEvalP_comp Sc P hrel μ _ _)
  map_zero' := by ext; exact S.upEvalP_zero Sc P hrel μ
  map_add' f g := by ext; exact S.upEvalP_add Sc P hrel μ _ _
  commutes' r := by
    ext i j
    simp only [Algebra.algebraMap_eq_smul_one, KLR.Diagram.MatEnd.smul_apply]
    rw [upEvalP_smul]
    by_cases h : i = j
    · subst h
      simp only [KLR.Diagram.MatEnd.one_apply_self]
      rw [upEvalP_id]
    · simp only [KLR.Diagram.MatEnd.one_apply_of_ne h, smul_zero]
      rw [upEvalP_zero, smul_zero]

theorem upActP_single (μ : X) (i j : KLR.Seq ν)
    (f : P.obj (ob RD μ (ups (KLR.Diagram.word i))) ⟶
      P.obj (ob RD μ (ups (KLR.Diagram.word j)))) :
    S.upActP Sc P hrel μ ν (KLR.Diagram.MatEnd.single i j f) =
      KLR.Diagram.MatEnd.single i j (S.upEvalP Sc P hrel μ f) := by
  ext i' j'
  change S.upEvalP Sc P hrel μ (KLR.Diagram.MatEnd.single (X := fun t : KLR.Seq ν =>
    P.obj (ob RD μ (ups (KLR.Diagram.word t)))) i j f i' j') = _
  by_cases h : i' = i ∧ j' = j
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [KLR.Diagram.MatEnd.single_apply_of_ne _ h, KLR.Diagram.MatEnd.single_apply_of_ne _ h,
      upEvalP_zero]

/-- **`P` acts on upward words through the KLR action of the Rouquier family**: on the free
algebra on the KLR generators, the composite of `toDiagFree`, the upward functor `upFunctorC`
of `P` and the evaluation `upActP` is the action `klrActFree` of the family. -/
theorem upActP_comp_upFunctorC (Q : I → I → MvPolynomial (Fin 2) k) (hK : CL.KLRHolds P Q)
    (μ : X) (ν : Multiset I) :
    ((S.upActP Sc P hrel μ ν).comp ((KL3.Diagram.matEndMap k
      (CL.upFunctorC P Q hK μ) _).comp (KLR.Diagram.toDiagFree k Q ν))) =
      S.klrActFree k μ ν := by
  refine FreeAlgebra.hom_ext (funext fun g => ?_)
  cases g with
  | idem i =>
    change S.upActP Sc P hrel μ ν (KL3.Diagram.matEndMap k (CL.upFunctorC P Q hK μ) _
      (KLR.Diagram.toDiagFree k Q ν (KLR.fe k ν i))) = S.klrActFree k μ ν (KLR.fe k ν i)
    rw [KLR.Diagram.toDiagFree_fe, klrActFree_fe, KLR.Diagram.DiagR.E,
      KL3.Diagram.matEndMap_single, CategoryTheory.Functor.map_id]
    erw [upActP_single, upEvalP_id]
    rfl
  | dot a =>
    change S.upActP Sc P hrel μ ν (KL3.Diagram.matEndMap k (CL.upFunctorC P Q hK μ) _
      (KLR.Diagram.toDiagFree k Q ν (KLR.fx k ν a))) = S.klrActFree k μ ν (KLR.fx k ν a)
    rw [KLR.Diagram.toDiagFree_fx, klrActFree_fx, KLR.Diagram.DiagR.X, map_sum, map_sum, wordX]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [KL3.Diagram.matEndMap_single, upActP_single, KLR.Diagram.dotE,
      CL.upFunctorC_diag]
    exact congrArg _ (S.upIso_dot Sc μ i a (cond_word μ i))
  | cross j =>
    change S.upActP Sc P hrel μ ν (KL3.Diagram.matEndMap k (CL.upFunctorC P Q hK μ) _
      (KLR.Diagram.toDiagFree k Q ν (KLR.fψ k ν j))) = S.klrActFree k μ ν (KLR.fψ k ν j)
    rw [KLR.Diagram.toDiagFree_fψ, klrActFree_fψ, KLR.Diagram.DiagR.Ψ, map_sum, map_sum, wordΨ]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [KL3.Diagram.matEndMap_single, upActP_single]
    by_cases hj : j + 1 < Multiset.card ν
    · erw [KLR.Diagram.crossE_def _ hj, CL.upFunctorC_diag]
      exact congrArg _ (S.upIso_cross Sc μ i hj (cond_word μ i) (cond_word μ _))
    · erw [KLR.Diagram.crossE_of_le _ (by omega), Functor.map_zero, upEvalP_zero,
        wordCross_of_le _ _ _ (by omega)]

end RouqFamily

end Categorification.TwoRep
