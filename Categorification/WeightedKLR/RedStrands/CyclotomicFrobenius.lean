/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicBlackAction
import Categorification.WeightedKLR.RedStrands.DoubleProjective
import Categorification.WeightedKLR.RedStrands.DoubleDownBlackMatrix
import Categorification.Diagrams.KLR.MatEndTrace
import Categorification.KLR.CyclotomicAbsentColour
import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat

/-!
# Nondegenerate traces on cyclotomic KLR algebras

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 3.18:
for one red strand the cyclotomic quotient `R^λ_ν` carries a trace whose pairing
`(a, b) ↦ tr (a b)` is nondegenerate. The trace closes the black strands of an all-down
boundary to the right, with the cups and caps of the biadjunction of the Khovanov–Lauda
2-category (Theorem 3.17); its value lies in the endomorphisms of the red strand alone, which
form the ground field.

* `DoubleBoundary.word_eq_of_blackContent_eq_zero`, `DoubleBoundary.word_eq_of_not_isViolated`:
  the words of one red strand used in the proof.
* `downwardMatrix_trace_nondegenerate`: the diagonal closing trace on the all-down matrix ring
  is `k`-linear and nondegenerate on both sides, for every presentation of the form used in
  Theorem 4.29.
* `clCyclotomic_trace_nondegenerate`: Theorem 3.18 at the standard Khovanov–Lauda parameters
  over a field: a `k`-linear trace `R^λ_ν → k` whose pairing is nondegenerate, that is, a
  linear map killing no nonzero left (or right) ideal.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams KLR
  KLR.Diagram AmbidextrousTrace

open scoped Classical

namespace DoubleBoundary

variable {I : Type*}

theorem word_eq_map_inr {ℓ : ℕ} (w : List (DoubleStrand I ℓ))
    (h : w.filterMap DoubleStrand.blackLabel = []) :
    w = (w.filterMap DoubleStrand.redLabel).map Sum.inr := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    cases x with
    | inl s => simp [DoubleStrand.blackLabel, DoubleStrand.erase] at h
    | inr r =>
      simp only [List.filterMap_cons, DoubleStrand.blackLabel, Function.comp_apply,
        DoubleStrand.erase, Sum.getLeft?_inr] at h
      simp only [List.filterMap_cons, Sum.getRight?_inr, List.map_cons]
      exact congrArg _ (ih h)

theorem word_eq_map_inl {ℓ : ℕ} (w : List (DoubleStrand I ℓ))
    (h : w.filterMap DoubleStrand.redLabel = []) :
    w = (w.filterMap Sum.getLeft?).map Sum.inl := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    cases x with
    | inr r => simp at h
    | inl s =>
      simp only [List.filterMap_cons, Sum.getRight?_inl] at h
      simp only [List.filterMap_cons, Sum.getLeft?_inl, List.map_cons]
      exact congrArg _ (ih h)

/-- With one red strand, a boundary of black content zero is the red strand alone. -/
theorem word_eq_of_blackContent_eq_zero (b : DoubleBoundary I 1) (h : b.blackContent = 0) :
    b.word = [Sum.inr 0] := by
  have h' : b.word.filterMap DoubleStrand.blackLabel = [] := by
    simpa [blackContent] using h
  rw [word_eq_map_inr b.word h', b.redOrder]
  rfl

/-- With one red strand, a non-violated boundary is the red strand followed by black
strands. -/
theorem word_eq_of_not_isViolated (b : DoubleBoundary I 1) (h : ¬ b.IsViolated) :
    b.word = Sum.inr 0 :: (b.word.tail.filterMap Sum.getLeft?).map Sum.inl := by
  have hr := b.redOrder
  obtain ⟨w, hw⟩ := b
  dsimp only at hr h ⊢
  cases w with
  | nil => simp at hr
  | cons x w =>
    cases x with
    | inl s => exact (h ⟨s, rfl⟩).elim
    | inr r =>
      have hr2 : r :: w.filterMap DoubleStrand.redLabel = [0] := hr
      have hr' : w.filterMap DoubleStrand.redLabel = [] := (List.cons_eq_cons.mp hr2).2
      rw [Subsingleton.elim r 0, List.tail_cons, ← word_eq_map_inl w hr']

end DoubleBoundary

namespace DoubleDiagram

universe u v w

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {Λ : Fin 1 → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k]

/-- The 1-morphism of the Khovanov–Lauda bicategory given by a word of letters, with a chosen
name for its source weight. -/
def wordHomOf (μ ν : X) (t : List (Letter I)) (h : KL3.Diagram.wt RD μ t = ν) :
    wtObj RD k ν ⟶ wtObj RD k μ :=
  ⟨KL3.Diagram.ob RD μ t, h, KL3.Diagram.ob_wf RD μ t, KL3.Diagram.ob_endR RD μ t⟩

theorem homLetters_wordHomOf (μ ν : X) (t : List (Letter I))
    (h : KL3.Diagram.wt RD μ t = ν) : homLetters (wordHomOf (k := k) μ ν t h) = t :=
  map_l_wd RD μ t

theorem map_reverse_map_comm {α β : Type*} (f : α → α) (g : α → β) (h : β → β)
    (hfg : ∀ a, g (f a) = h (g a)) (w : List α) :
    List.map g (List.map f w).reverse = (List.map h (List.map g w)).reverse := by
  rw [List.map_reverse, List.map_map, List.map_map]
  exact congrArg List.reverse (List.map_congr_left fun a _ => hfg a)

/-- The letters of the dual word are the reversed dual letters. -/
theorem homLetters_dualHom {l m : (pres RD k).Bicat} (x : l ⟶ m) :
    homLetters ((pres RD k).dualHom (inv RD).toColourDuality.pivotal x) =
      ((homLetters x).map Letter.dual).reverse := by
  simp only [homLetters, Presentation.dualHom_obj, Signature.ColourDuality.dualWord_eq]
  exact map_reverse_map_comm _ Col.l Letter.dual (fun _ => rfl) x.obj.word

theorem wordContent_blackWord_dual (t : List (Letter I)) :
    wordContent (blackWord (ℓ := 1) ((t.map Letter.dual).reverse)) =
      -wordContent (blackWord (ℓ := 1) t) := by
  simp only [blackWord, List.reverse_reverse]
  rw [wordContent_map_dual, List.map_reverse, wordContent_reverse]

/-- The boundary consisting of the red strand alone. -/
def redBoundary : DoubleBoundary I 1 := ⟨[Sum.inr 0], rfl⟩

/-- The red strand alone, as an all-down triple of black content zero. -/
def redTriple : DoubleStendhalTriple RD Λ 0 (downRightWeight RD Λ 0) :=
  ⟨redBoundary, by
    simp [DoubleBoundary.rightWeight, downRightWeight, redBoundary, DoubleStrand.weight]⟩

/-- The black letters to the right of the red strand, read so that their mirror word is the
black part of the boundary. -/
def blackLetters (b : DoubleBoundary I 1) : List (Letter I) :=
  (b.word.tail.filterMap Sum.getLeft?).reverse

theorem word_eq_red_append (b : DoubleBoundary I 1) (h : ¬ b.IsViolated) :
    b.word = redBoundary.word ++ blackWord (blackLetters b) := by
  rw [DoubleBoundary.word_eq_of_not_isViolated b h]
  simp [redBoundary, blackLetters, blackWord]

theorem wt_blackLetters {μ : X} (b : DoubleStendhalTriple RD Λ 0 μ) (h : ¬ b.val.IsViolated) :
    KL3.Diagram.wt RD (downRightWeight RD Λ 0) (blackLetters b.val) = μ := by
  rw [← endWeight_blackWord RD (fun r => (Λ r).val),
    ← endWeight_word (redTriple (RD := RD) (Λ := Λ)), ← endWeight_append]
  change endWeight RD _ 0 (redBoundary.word ++ _) = μ
  rw [← word_eq_red_append _ h]
  exact endWeight_word b

theorem appendRight_redTriple {μ : X} (b : DoubleStendhalTriple RD Λ 0 μ)
    (h : ¬ b.val.IsViolated) (hv : RedFree (blackWord (blackLetters b.val)))
    (hν : endWeight RD (fun r => (Λ r).val) (downRightWeight RD Λ 0)
      (blackWord (blackLetters b.val)) = μ) :
    appendRight (blackWord (blackLetters b.val)) hv hν (redTriple (RD := RD) (Λ := Λ)) = b :=
  Subtype.ext (DoubleBoundary.ext (word_eq_red_append b.val h).symm)

theorem wordContent_redBoundary : wordContent (redBoundary (I := I)).word = 0 :=
  wordContent_red 0


variable (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k) (t : I → I → kˣ)
local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

theorem blackAct_obj_violatingFunctor (P' : Presentation (signature RD (Subtype.val ∘ Λ)) k)
    {μ ν : X} (s : List (Letter I))
    (hs : KL3.Diagram.wt RD μ s = ν) (b : DoubleStendhalTriple RD Λ 0 μ) :
    (blackAct P' s hs).obj ((violatingFunctor P' μ).obj b) =
      (violatingFunctor P' ν).obj (appendRight (blackWord s) (blackWord_redFree s)
        ((endWeight_blackWord RD _ μ s).trans hs) b) := rfl

/-- The red strand alone, in the violating quotient of a presentation. -/
abbrev redObj (P' : Presentation (signature RD (Subtype.val ∘ Λ)) k) :
    ViolatingCategory P' (downRightWeight RD Λ 0) :=
  (violatingFunctor P' (downRightWeight RD Λ 0)).obj redTriple

section Zero

variable (P' : Presentation (signature RD (Subtype.val ∘ Λ)) k)

theorem downTriple_eq_redTriple
    (s : {s : Seq (stendhalWeight 1 (0 : Multiset I)) // IsRedOrdered s}) :
    downTriple RD Λ s = redTriple :=
  Subtype.ext (DoubleBoundary.ext (DoubleBoundary.word_eq_of_blackContent_eq_zero _
    (DoubleBoundary.blackContent_ofDown s.val s.property)))

omit [AddCommGroup X] [AddCommGroup Y] in
theorem eq_of_seq_zero (s s' : {s : Seq (stendhalWeight 1 (0 : Multiset I)) // IsRedOrdered s}) :
    s = s' :=
  (DoubleBoundary.allDownEquiv (ℓ := 1) 0).injective <| Subtype.ext <| DoubleBoundary.ext <|
    (DoubleBoundary.word_eq_of_blackContent_eq_zero _
      (DoubleBoundary.blackContent_ofDown s.val s.property)).trans
    (DoubleBoundary.word_eq_of_blackContent_eq_zero _
      (DoubleBoundary.blackContent_ofDown s'.val s'.property)).symm

omit [AddCommGroup X] [AddCommGroup Y] in
theorem exists_seq_zero :
    Nonempty {s : Seq (stendhalWeight 1 (0 : Multiset I)) // IsRedOrdered s} :=
  ⟨(DoubleBoundary.allDownEquiv (ℓ := 1) 0).symm ⟨redBoundary,
    fun i => by simp [redBoundary], by simp [DoubleBoundary.blackContent, redBoundary,
      DoubleStrand.blackLabel, DoubleStrand.erase]⟩⟩

theorem downObj_zero (s : {s : Seq (stendhalWeight 1 (0 : Multiset I)) // IsRedOrdered s}) :
    downObj P' s = redObj P' :=
  congrArg (violatingFunctor P' _).obj (downTriple_eq_redTriple s)

/-- At black content zero the all-down matrix ring is the endomorphism ring of the red strand
alone. -/
def zeroMatrixEquiv : downwardMatrix P' (0 : Multiset I) ≃+ (redObj P' ⟶ redObj P') :=
  let s₀ := (exists_seq_zero (I := I)).some
  { toFun := fun M =>
      eqToHom (downObj_zero P' s₀).symm ≫ M s₀ s₀ ≫ eqToHom (downObj_zero P' s₀)
    invFun := fun f i j => eqToHom (downObj_zero P' i) ≫ f ≫ eqToHom (downObj_zero P' j).symm
    left_inv := fun M => by
      refine KLR.Diagram.MatEnd.ext fun i j => ?_
      obtain rfl := eq_of_seq_zero i s₀
      obtain rfl := eq_of_seq_zero j s₀
      simp
    right_inv := fun f => by simp
    map_add' := fun M N => by
      simp [Preadditive.add_comp, Preadditive.comp_add] }

theorem zeroMatrixEquiv_symm_smul (c : k) (f : redObj P' ⟶ redObj P') :
    (zeroMatrixEquiv P').symm (c • f) = c • (zeroMatrixEquiv P').symm f := by
  refine KLR.Diagram.MatEnd.ext fun i j => ?_
  change eqToHom _ ≫ (c • f) ≫ eqToHom _ = c • (eqToHom _ ≫ f ≫ eqToHom _)
  rw [Linear.smul_comp, Linear.comp_smul]

end Zero

/-- Every boundary of signed content zero is a retract of finitely many copies of the red
strand alone (Webster, arXiv:1309.3796v3, proof of Theorem 3.18). -/
theorem exists_retract_redObj (b : DoubleStendhalTriple RD Λ 0 (downRightWeight RD Λ 0))
    (hb : b.val.signedContent = 0) :
    ∃ (n : ℕ) (π : Fin n → ((violatingFunctor Q _).obj b ⟶ redObj Q))
      (ι : Fin n → (redObj Q ⟶ (violatingFunctor Q _).obj b)),
      ∑ i, π i ≫ ι i = 𝟙 ((violatingFunctor Q _).obj b) := by
  have hb' : b.val.signedContent = contentVector 0 := by simpa [contentVector] using hb
  let π := violatingFunctor Q (downRightWeight RD Λ 0)
  let S : ObjectProperty (ViolatingCategory Q (downRightWeight RD Λ 0)) := fun d =>
    d.as.val.AllDown ∧ d.as.val.blackContent = 0
  have hle : factorSpan k π.obj (fun d => d.val.AllDown ∧ d.val.blackContent = 0) b b ≤
      factorSpan k id S (π.obj b) (π.obj b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, a, c, rfl⟩
    exact Submodule.subset_span ⟨π.obj d, hd, a, c, rfl⟩
  obtain ⟨n, c, u, v, huv⟩ :=
    finiteFactorization S (hle (id_mem_allDownContentFactorSpan P t b 0 hb'))
  have hc : ∀ i, (c i).obj = π.obj redTriple := fun i => by
    have hw := DoubleBoundary.word_eq_of_blackContent_eq_zero _ (c i).property.2
    have he : (c i).obj.as = redTriple := Subtype.ext (DoubleBoundary.ext hw)
    calc (c i).obj = ⟨(c i).obj.as⟩ := rfl
      _ = π.obj redTriple := by rw [he]; rfl
  refine ⟨n, fun i => u i ≫ eqToHom (hc i), fun i => eqToHom (hc i).symm ≫ v i, ?_⟩
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using huv

/-- On every all-down summand the closing trace into the endomorphisms of the red strand is
nondegenerate against the other summands (Webster, arXiv:1309.3796v3, proof of
Theorem 3.18): violated summands are zero, and a non-violated summand is the image of the red
strand under the black action of its word, whose biadjoint generates the red strand. -/
theorem exists_summand_trace
    (hQ : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0) {ν : Multiset I}
    (s : {s : Seq (stendhalWeight 1 ν) // IsRedOrdered s}) :
    ∃ τ : (downObj Q s ⟶ downObj Q s) →+ (redObj Q ⟶ redObj Q),
      IsNondegTrace (redObj Q) (downObj Q s) τ (fun Y => ∃ j, downObj Q j = Y) ∧
        ∀ (c : k) a, τ (c • a) = c • τ a := by
  by_cases hs : Stendhal.IsViolated s.val
  · exact ⟨0, isNondegTrace_zero_of_id_eq_zero _ (downObj_id_eq_zero Q s hs) _,
      fun c a => by simp⟩
  have hnv : ¬ (downTriple RD Λ s).val.IsViolated := fun h =>
    hs ((DoubleBoundary.isViolated_ofDown_iff s.val s.property).mp h)
  let b := downTriple RD Λ s
  let x := wordHomOf (k := k) (RD := RD) (downRightWeight RD Λ 0) (downRightWeight RD Λ ν)
    (blackLetters b.val) (wt_blackLetters b hnv)
  let 𝔽 := blackActionPseudofunctor Q hQ
  let _ : Preadditive (𝔽.obj ⟨wtObj RD k (downRightWeight RD Λ ν)⟩) :=
    inferInstanceAs (Preadditive (ViolatingCategory Q (downRightWeight RD Λ ν)))
  let _ : Preadditive (𝔽.obj ⟨wtObj RD k (downRightWeight RD Λ 0)⟩) :=
    inferInstanceAs (Preadditive (ViolatingCategory Q (downRightWeight RD Λ 0)))
  let _ : Linear k (𝔽.obj ⟨wtObj RD k (downRightWeight RD Λ ν)⟩) :=
    inferInstanceAs (Linear k (ViolatingCategory Q (downRightWeight RD Λ ν)))
  let _ : Linear k (𝔽.obj ⟨wtObj RD k (downRightWeight RD Λ 0)⟩) :=
    inferInstanceAs (Linear k (ViolatingCategory Q (downRightWeight RD Λ 0)))
  let adj₁ := Adjunction.ofCat (𝔽.mapAdjunction (RevBicat.adjunction (biadjWord RD k x).right))
  let adj₂ := Adjunction.ofCat (𝔽.mapAdjunction (RevBicat.adjunction (biadjWord RD k x).left))
  have : (𝔽.map (RevBicat.of
      ((pres RD k).dualHom (inv RD).toColourDuality.pivotal x))).toFunctor.Additive :=
    blackAct_additive Q _ (homWt _)
  have : (𝔽.map (RevBicat.of
      ((pres RD k).dualHom (inv RD).toColourDuality.pivotal x))).toFunctor.Linear k :=
    blackAct_linear Q _ (homWt _)
  have hF : (𝔽.map (RevBicat.of x)).toFunctor.obj (redObj Q) = downObj Q s := by
    refine (blackAct_obj_violatingFunctor Q _ (homWt (RevBicat.of x)) redTriple).trans ?_
    congr 1
    refine Subtype.ext (DoubleBoundary.ext ?_)
    change redBoundary.word ++ blackWord (homLetters x) = b.val.word
    rw [homLetters_wordHomOf]
    exact (word_eq_red_append b.val hnv).symm
  refine ⟨closeTraceIso adj₁ adj₂ (redObj Q) (eqToIso hF),
    isNondegTrace_closeTraceIso adj₁ adj₂ (redObj Q) (eqToIso hF) _ ?_,
    fun c a => closeTraceIso_smul adj₁ adj₂ (redObj Q) (eqToIso hF) c a⟩
  rintro _ ⟨j, rfl⟩
  have hbc : wordContent (blackWord (ℓ := 1) (blackLetters b.val)) = contentVector ν := by
    have hcb : b.val.blackContent = ν := DoubleBoundary.blackContent_ofDown s.val s.property
    have h1 := (DoubleBoundary.signedContent_of_allDown b.val
      (DoubleBoundary.allDown_ofDown s.val s.property)).symm
    rw [DoubleBoundary.signedContent_eq_wordContent, word_eq_red_append b.val hnv,
      wordContent_append, wordContent_redBoundary, zero_add, hcb] at h1
    exact h1.symm
  have hjc : wordContent (downTriple RD Λ j).val.word = contentVector ν := by
    have hcj : (downTriple RD Λ j).val.blackContent = ν :=
      DoubleBoundary.blackContent_ofDown j.val j.property
    rw [← DoubleBoundary.signedContent_eq_wordContent, DoubleBoundary.signedContent_of_allDown
      (downTriple RD Λ j).val (DoubleBoundary.allDown_ofDown j.val j.property), hcj]
  let y := (pres RD k).dualHom (inv RD).toColourDuality.pivotal x
  refine exists_retract_redObj P t (appendRight (blackWord (homLetters (RevBicat.of y)))
    (blackWord_redFree _) ((endWeight_blackWord RD _ _ _).trans (homWt (RevBicat.of y)))
    (downTriple RD Λ j)) ?_
  change wordContent ((downTriple RD Λ j).val.word ++ blackWord (homLetters
    ((pres RD k).dualHom (inv RD).toColourDuality.pivotal x))) = 0
  rw [wordContent_append, homLetters_dualHom, homLetters_wordHomOf, wordContent_blackWord_dual,
    hbc, hjc, add_neg_cancel]

/-- **Webster, arXiv:1309.3796v3, Theorem 3.18, matrix form.** For one red strand, the
diagonal closing trace on the all-down matrix ring, with values in the endomorphisms of the
red strand alone, is `k`-linear and has a pairing `(M, N) ↦ τ (M * N)` that is nondegenerate
on both sides. -/
theorem downwardMatrix_trace_nondegenerate
    (hQ : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
    (ν : Multiset I) :
    ∃ τ : downwardMatrix Q ν →+ (redObj Q ⟶ redObj Q),
      (∀ M : downwardMatrix Q ν, M ≠ 0 → ∃ N : downwardMatrix Q ν, τ (M * N) ≠ 0) ∧
        (∀ N : downwardMatrix Q ν, N ≠ 0 → ∃ M : downwardMatrix Q ν, τ (M * N) ≠ 0) ∧
        ∀ (c : k) M, τ (c • M) = c • τ M := by
  classical
  choose τ hτ hlin using fun s => exists_summand_trace P t hQ (ν := ν) s
  obtain ⟨h₁, h₂⟩ := KLR.Diagram.MatEnd.trace_nondegenerate τ hτ
  exact ⟨KLR.Diagram.MatEnd.trace τ, h₁, h₂, KLR.Diagram.MatEnd.trace_smul τ hlin⟩

end DoubleDiagram

section CL

open DoubleDiagram TwoRep CyclotomicAction KLR.KLRAlgebra

variable {I : Type u} {C : CartanDatum I} {k : Type v} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {hQ : IsRouquierQ C Q}

local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)

/-- **Webster, arXiv:1309.3796v3, Theorem 3.18**, at the standard Khovanov–Lauda parameters
over a field. For one red strand of label `λ`, the cyclotomic KLR algebra `R^λ_ν` carries a
`k`-linear trace `tr : R^λ_ν → k` whose pairing `(a, b) ↦ tr (a b)` is nondegenerate on both
sides; that is, `tr` is a Frobenius trace: it kills no nonzero left ideal (and no nonzero right
ideal). The trace closes the black strands of each all-down boundary to the right with the
biadjunction of Theorem 3.17, landing in the endomorphisms of the red strand alone, that is in
`R^λ_0 = k`. -/
theorem clCyclotomic_trace_nondegenerate (Λ : Fin 1 → I →₀ ℕ) (ν : Multiset I)
    (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL KL i j)
    {P : Presentation.{v, u} (signature (coordinateDatum Λ C)
      (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ (coverDotCentral Λ C hQ)
      (blockWeight (cyclotomicCoverWeightDatum Λ C)
        (cyclotomicCoverHighest (I := I) (ℓ := 1)) 0) P)
    (hwf : P.WFDom) :
    ∃ tr : CycKLR k (CL.qCL KL) (fun i => Polynomial.X ^ Λ 0 i) ν →ₗ[k] k,
      (∀ a, a ≠ 0 → ∃ b, tr (a * b) ≠ 0) ∧
        ∀ b, b ≠ 0 → ∃ a, tr (a * b) ≠ 0 := by
  let B := clDownwardBlock Λ C P
  let f := (SingleRed.cyclotomicEquiv (CL.qCL KL) Λ ν).trans
    (clToDownwardMatrixKLEquiv (ν := ν) hstd hP hwf)
  let f₀ := (SingleRed.cyclotomicEquiv (CL.qCL KL) Λ 0).trans
    (clToDownwardMatrixKLEquiv (ν := 0) hstd hP hwf)
  obtain ⟨τ, h₁, h₂, hlin⟩ := downwardMatrix_trace_nondegenerate _ (KL).t
    (clDownwardBlock_reflectedBlack P) ν
  let cZ := cyclotomicZeroEquiv (CL.qCL KL) (fun i => Polynomial.X ^ Λ 0 i)
  have hψ : ∀ g : redObj B ⟶ redObj B, g ≠ 0 → cZ (f₀.symm ((zeroMatrixEquiv B).symm g)) ≠ 0 :=
    fun g hg h => hg <| by
      have h1 := cZ.injective (h.trans (map_zero cZ).symm)
      have h2 := f₀.symm.injective (h1.trans (map_zero f₀.symm).symm)
      exact (zeroMatrixEquiv B).symm.injective (h2.trans (map_zero _).symm)
  refine ⟨{ toFun := fun a => cZ (f₀.symm ((zeroMatrixEquiv B).symm (τ (f a))))
            map_add' := fun a b => by simp only [map_add]
            map_smul' := fun c a => by
              simp only [map_smul, hlin, zeroMatrixEquiv_symm_smul, RingHom.id_apply] },
    fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨N, hN⟩ := h₁ (f a) (fun h => ha (f.injective (h.trans (map_zero f).symm)))
    refine ⟨f.symm N, hψ _ ?_⟩
    simpa [map_mul] using hN
  · obtain ⟨M, hM⟩ := h₂ (f b) (fun h => hb (f.injective (h.trans (map_zero f).symm)))
    refine ⟨f.symm M, hψ _ ?_⟩
    simpa [map_mul] using hM

end CL

end Categorification.Stendhal
