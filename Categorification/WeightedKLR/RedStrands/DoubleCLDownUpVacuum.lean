/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLDownKLRUp
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverUnorderedVacuum

/-!
# Downward and upward KLR diagrams agree on the projected vacuum

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. On the projected cyclotomic vacuum, the
downward translation of a KLR diagram of the extended datum, followed by the cover functor, acts
as the reflected diagram on upward strands (`vacuumNegligible_downCover_sub_upCover`), for any
number of red strands. The layers of the two images differ only by dots on red strands, which
are red-negligible, and by crossings of two red strands. A crossing of two red strands has an
upward word with unordered reds at its bottom or at its top, and such words vanish on the
projected vacuum (`isZero_vacuumWord_of_not_isRedOrdered`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits QuantumGroup QuantumGroup.UDot StringDiagrams KLR
  TwoRep CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram InductionAlong
  KLRAlgebra

universe u v w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  (hc : CoverDotCentral Λ C Q) (ν : Multiset I)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "monic" => cyclotomicCoverPolynomial_monic (k := k)
local notation "topDeg" => cyclotomicCoverPolynomial_natDegree (k := k) Λ C
local notation "wt₀" => (blockWeight Wgt L 0 : I ⊕ Fin ℓ → ℤ)
local notation "π" => cyclotomicCoverToTensor (Q := Q) Λ ν C
set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => cyclotomicFamily.{u, v, w} sym lead monic Wgt L topDeg deg

/-- **Upward words of a list with unordered reds vanish on the projected vacuum**, whatever the
rightmost region of the word: an admissible word ends in the vacuum region. -/
theorem isZero_vacuumWord_list (l : List (I ⊕ Fin ℓ))
    (hl : ¬ IsRedOrdered (Seq.ofList l rfl).rev) {s e : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s)
    {w : List (Col (I ⊕ Fin ℓ) (I ⊕ Fin ℓ → ℤ))} (h : (psig Wgt).ok s w)
    (he : (psig Wgt).endR s w = wt₀) (hw : w = wd Wgt e (ups l)) :
    IsZero ((functor (RingHom.toNonUnitalRingHom (AlgHom.toRingHom π))).obj
      ((((Fam).model.word s w wt₀ h he).obj.obj (coverVacuum.{u, v, w} Λ C hQ))
        ⟨stendhalWeight ℓ ν, hν⟩)) := by
  have hw' : w = wd Wgt wt₀ (ups l) := by
    subst hw
    cases hl' : ups l with
    | nil => rfl
    | cons x t =>
      rw [hl'] at h he
      have hs : s = wt Wgt e (x :: t) := h.1.symm
      rw [hs, endR_wd] at he
      rw [he]
  exact isZero_vacuumWord_of_not_isRedOrdered Λ ν C hQ (Seq.ofList l rfl) hl hν h he
    (by rw [hw', word_ofList]; rfl)

/-- **Projected vacuum negligibility.** Every admissible component of the action of the
morphism on the cyclotomic vacuum, at the Stendhal block of `ν`, vanishes after extension of
scalars to the tensor-product algebra. -/
def VacuumNegligible {c d : Obj (psig Wgt)} (φ : (PCL).obj c ⟶ (PCL).obj d) : Prop :=
  ∀ {s : I ⊕ Fin ℓ → ℤ} (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s)
    (ha : Cond s wt₀ c) (hb : Cond s wt₀ d), vacuumEval.{u, v, w} Λ C hQ ν hν ha hb φ = 0

variable {Λ C hQ ν}

theorem vacuumEval_zero {s : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) {c d : Obj (psig Wgt)}
    (ha : Cond s wt₀ c) (hb : Cond s wt₀ d) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha hb (0 : (PCL).obj c ⟶ (PCL).obj d) = 0 := by
  simpa using vacuumEval_smul hν ha hb (0 : k) (0 : (PCL).obj c ⟶ (PCL).obj d)

/-- A morphism out of an upward word with unordered reds evaluates to zero. -/
theorem vacuumEval_eq_zero_of_dom {s e : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) {c d : Obj (psig Wgt)}
    (ha : Cond s wt₀ c) (hb : Cond s wt₀ d) (φ : (PCL).obj c ⟶ (PCL).obj d)
    (l : List (I ⊕ Fin ℓ)) (hl : ¬ IsRedOrdered (Seq.ofList l rfl).rev)
    (hw : c.word = wd Wgt e (ups l)) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha hb φ = 0 :=
  (isZero_vacuumWord_list Λ C hQ ν l hl hν ha.1 ha.2.1 hw).eq_of_src _ _

/-- A morphism into an upward word with unordered reds evaluates to zero. -/
theorem vacuumEval_eq_zero_of_cod {s e : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) {c d : Obj (psig Wgt)}
    (ha : Cond s wt₀ c) (hb : Cond s wt₀ d) (φ : (PCL).obj c ⟶ (PCL).obj d)
    (l : List (I ⊕ Fin ℓ)) (hl : ¬ IsRedOrdered (Seq.ofList l rfl).rev)
    (hw : d.word = wd Wgt e (ups l)) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha hb φ = 0 :=
  (isZero_vacuumWord_list Λ C hQ ν l hl hν hb.1 hb.2.1 hw).eq_of_tgt _ _

namespace VacuumNegligible

theorem zero {c d : Obj (psig Wgt)} :
    VacuumNegligible.{u, v, w} Λ C hQ ν (0 : (PCL).obj c ⟶ (PCL).obj d) :=
  fun hν ha hb => vacuumEval_zero hν ha hb

theorem add {c d : Obj (psig Wgt)} {f g : (PCL).obj c ⟶ (PCL).obj d}
    (hf : VacuumNegligible.{u, v, w} Λ C hQ ν f)
    (hg : VacuumNegligible.{u, v, w} Λ C hQ ν g) :
    VacuumNegligible.{u, v, w} Λ C hQ ν (f + g) :=
  fun hν ha hb => by rw [vacuumEval_add, hf hν ha hb, hg hν ha hb, add_zero]

theorem smul {c d : Obj (psig Wgt)} (r : k) {f : (PCL).obj c ⟶ (PCL).obj d}
    (hf : VacuumNegligible.{u, v, w} Λ C hQ ν f) :
    VacuumNegligible.{u, v, w} Λ C hQ ν (r • f) :=
  fun hν ha hb => by rw [vacuumEval_smul, hf hν ha hb, smul_zero]

theorem comp_left {c d e : Obj (psig Wgt)} (g : (PCL).obj c ⟶ (PCL).obj d)
    {f : (PCL).obj d ⟶ (PCL).obj e}
    (hf : VacuumNegligible.{u, v, w} Λ C hQ ν f) :
    VacuumNegligible.{u, v, w} Λ C hQ ν (g ≫ f) := by
  intro s hν ha he
  by_cases hb : Cond s wt₀ d
  · rw [vacuumEval_comp hν ha hb he, hf hν hb he, Limits.comp_zero]
  · rw [presented_eq_zero_of_not_cond (PCL) ha hb g, Limits.zero_comp]
    exact vacuumEval_zero hν ha he

theorem comp_right {c d e : Obj (psig Wgt)} {f : (PCL).obj c ⟶ (PCL).obj d}
    (g : (PCL).obj d ⟶ (PCL).obj e)
    (hf : VacuumNegligible.{u, v, w} Λ C hQ ν f) :
    VacuumNegligible.{u, v, w} Λ C hQ ν (f ≫ g) := by
  intro s hν ha he
  by_cases hb : Cond s wt₀ d
  · rw [vacuumEval_comp hν ha hb he, hf hν ha hb, Limits.zero_comp]
  · rw [presented_eq_zero_of_not_cond (PCL) ha hb f, Limits.zero_comp]
    exact vacuumEval_zero hν ha he

theorem of_coverRedNegligible {c d : Obj (psig Wgt)} {f : (PCL).obj c ⟶ (PCL).obj d}
    (hf : CoverRedNegligible.{u, v, w} Λ C hQ hc f) :
    VacuumNegligible.{u, v, w} Λ C hQ ν f :=
  fun hν ha hb => vacuumEval_eq_zero hc hν ha hb hf

end VacuumNegligible

variable (Λ C hQ ν) (o : I ⊕ Fin ℓ → ℤ)

omit [Field k] [DecidableEq I] in
/-- Two red letters next to each other are in the wrong order in one of the two words of
their crossing. -/
theorem not_isRedOrdered_crossing (lf rt : List (I ⊕ Fin ℓ)) (r r' : Fin ℓ) :
    ¬ IsRedOrdered (Seq.ofList (lf ++ [Sum.inr r, Sum.inr r'] ++ rt).reverse rfl).rev ∨
      ¬ IsRedOrdered (Seq.ofList (lf ++ [Sum.inr r', Sum.inr r] ++ rt).reverse rfl).rev := by
  by_cases h : r < r'
  · refine Or.inr (not_isRedOrdered_ofList_reverse _ (a := lf.length) (b := lf.length + 1)
      (r := r') (r' := r) (by omega) (by simp) (by simp) (by simp) ?_)
    exact fun h' => lt_asymm h h'
  · exact Or.inl (not_isRedOrdered_ofList_reverse _ (a := lf.length) (b := lf.length + 1)
      (by omega) (by simp) (by simp) (by simp) h)

include hc in
/-- **The downward translation agrees with the reflected upward image on the projected
vacuum.** For any KLR diagram of the extended datum, the downward translation in the empty
context followed by the cover functor and the signed reflection on upward strands differ by a
morphism that vanishes on the projected cyclotomic vacuum. -/
theorem vacuumNegligible_downCover_sub_upCover (μ : I ⊕ Fin ℓ → ℤ)
    {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (f : LinDiagram k a b) (ha : a.WF) (hb : b.WF) :
    VacuumNegligible.{u, v, w} Λ C hQ ν
      ((freeLift k (downCover Λ C hQ o μ)).map f -
        eqToHom (freeLift_obj_eq_on (R := k) _ _ (fun _ => True)
          (fun x _ _ => downCover_obj_eq Λ C hQ o μ x) a ha trivial) ≫
          (freeLift k (upCover Λ C hQ o μ)).map f ≫
          eqToHom (freeLift_obj_eq_on (R := k) _ _ (fun _ => True)
            (fun x _ _ => downCover_obj_eq Λ C hQ o μ x) b hb trivial).symm) := by
  let N : ∀ {x y : (PCL).Presented}, (x ⟶ y) → Prop := fun {x y} φ =>
    VacuumNegligible.{u, v, w} Λ C hQ ν (c := (PCL).toObj x) (d := (PCL).toObj y) φ ∧ True
  have key : N ((freeLift k (downCover Λ C hQ o μ)).map f -
      eqToHom (freeLift_obj_eq_on (R := k) _ _ (fun _ => True)
        (fun x _ _ => downCover_obj_eq Λ C hQ o μ x) a ha trivial) ≫
        (freeLift k (upCover Λ C hQ o μ)).map f ≫
        eqToHom (freeLift_obj_eq_on (R := k) _ _ (fun _ => True)
          (fun x _ _ => downCover_obj_eq Λ C hQ o μ x) b hb trivial).symm) := by
    refine freeLift_map_sub_mem_of_layer_on (R := k) (downCover Λ C hQ o μ)
      (upCover Λ C hQ o μ) (fun _ => True) (fun _ _ _ => trivial)
      (fun x _ _ => downCover_obj_eq Λ C hQ o μ x) N
      ⟨VacuumNegligible.zero, trivial⟩
      (fun hf hg => ⟨VacuumNegligible.add hf.1 hg.1, trivial⟩)
      (fun {_ _} r {_} hf => ⟨VacuumNegligible.smul r hf.1, trivial⟩)
      (fun {_ _ _} h {_} hf => ⟨VacuumNegligible.comp_left h hf.1, trivial⟩)
      (fun {_ _ _} {_} h hf => ⟨VacuumNegligible.comp_right h hf.1, trivial⟩) ?_ f ha hb
      trivial trivial
    intro Ly hLv _
    refine ⟨?_, trivial⟩
    cases hg : downMove Ly.gen with
    | some g =>
      rw [downCover_map_ofLayer Λ C hQ o μ Ly hLv hg, sub_self]
      exact VacuumNegligible.zero
    | none =>
      obtain ⟨st, lf, gen, rt⟩ := Ly
      rcases gen with ⟨i | r⟩ | ⟨i | r, j | r'⟩
      · simp [downMove] at hg
      · rw [downCover_map_ofLayer_of_none Λ C hQ o μ _ hLv hg, zero_sub, ← neg_one_smul k]
        refine VacuumNegligible.smul _ ?_
        apply VacuumNegligible.comp_left
        apply VacuumNegligible.comp_right
        exact VacuumNegligible.of_coverRedNegligible hc
          (coverRedNegligible_upCover_redDot.{u, v, w} Λ C hQ hc o μ _ hLv r rfl)
      · simp [downMove] at hg
      · simp [downMove] at hg
      · simp [downMove] at hg
      · intro s hν hda hdb
        have hdom := congrArg (fun x => ((PCL).toObj x).word)
          (downCover_obj Λ C hQ o μ ⟨st, lf ++ [Sum.inr r, Sum.inr r'] ++ rt⟩)
        have hcod := congrArg (fun x => ((PCL).toObj x).word)
          (downCover_obj Λ C hQ o μ ⟨st, lf ++ [Sum.inr r', Sum.inr r] ++ rt⟩)
        rcases not_isRedOrdered_crossing lf rt r r' with h | h
        · exact vacuumEval_eq_zero_of_dom hν hda hdb _ _ h hdom
        · exact vacuumEval_eq_zero_of_cod hν hda hdb _ _ h hcod
  intro s hν hs ht
  exact key.1 hν hs ht

end Categorification.Stendhal
