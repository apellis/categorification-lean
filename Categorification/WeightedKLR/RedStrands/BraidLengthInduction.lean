/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidSequenceStandardFiltration
import Categorification.WeightedKLR.RedStrands.BraidAdjacentClassCongr
import Categorification.WeightedKLR.RedStrands.GradedBraidComposeClass
import Categorification.WeightedKLR.RedStrands.BraidRightSequenceCut

set_option backward.isDefEq.respectTransparency false

/-!
# The class map of a braid functor along a reduced word

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11. By induction on the length of `w`: write `w = τ s` with `s` an adjacent
transposition and `ℓ(w) = ℓ(τ) + 1` (a descent of `w`, `exists_descent`). By the induction
hypothesis and the step `p_n → f_n` (`hasCornerStandardFiltration_braidF_rightSequence`),
`𝔅_τ` sends sequence projectives to modules with standard filtrations; these have finite
projective resolutions and are braid-concentrated for `s` (step `f_n → s_n`), since `B(s, 1)` is
standardly filtered by the length-one case. So `𝔅_w ≅ 𝔅_s ∘ 𝔅_τ` on classes (`p_{n+1}`,
`braidClass_mul`), and the class map of `𝔅_w` is `x ↦ B(f x, -)` with `f` the composite of the
adjacent braidings, congruent at `v = 1` to the permutation of the tensor factors by `w`
(`hasCongruentBraidClass`).

Route hypotheses: those of Corollary 6.10 (`AllFiniteDeltaInjective`,
`RowFigureFiveHypotheses`) and the diagram filtration of the step `p_n → f_n`
(`BraidDiagramFiltration`).
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF Equiv
open BraidedStendhalAlgebra ModuleFiltration
open scoped List RatFunc
open DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra
local notation "𝕂" => RatFunc ℚ

/-! ### Descents -/

section Descent

variable {ℓ : ℕ}


theorem pair_sublist_map_finRange {f : Fin ℓ → Fin ℓ} {x y : Fin ℓ}
    (h : [x, y] <+ (List.finRange ℓ).map f) : ∃ i j, i < j ∧ f i = x ∧ f j = y := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq] at h
  obtain ⟨g, hg⟩ := h
  have hl : ((List.finRange ℓ).map f).length = ℓ := by simp
  refine ⟨Fin.cast hl (g 0), Fin.cast hl (g 1), ?_, ?_, ?_⟩
  · exact g.strictMono (show (0 : Fin 2) < 1 by decide)
  · have := (hg 0).symm
    simp at this
    exact this
  · have := (hg 1).symm
    simp at this
    exact this

theorem pair_sublist_finRange {x y : Fin ℓ} (h : x < y) : [x, y] <+ List.finRange ℓ := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  have hl : (List.finRange ℓ).length = ℓ := by simp
  let g : Fin 2 → Fin (List.finRange ℓ).length := fun c =>
    Fin.cast hl.symm (if c = 0 then x else y)
  have hg : StrictMono g := by
    intro c d hcd
    fin_cases c <;> fin_cases d <;> first | exact absurd hcd (by decide) | exact h
  refine ⟨OrderEmbedding.ofStrictMono g hg, fun c => ?_⟩
  fin_cases c <;> simp [g]

/-- The number of inversions of a permutation. -/
def invCount (w : Perm (Fin ℓ)) : ℕ :=
  (Finset.univ.filter fun p : Fin ℓ × Fin ℓ => p.1 < p.2 ∧ w p.2 < w p.1).card

theorem swap_lt_swap {a b i j : Fin ℓ} (hab : a.val + 1 = b.val) (hij : i < j)
    (hne : ¬ (i = a ∧ j = b)) : swap a b i < swap a b j := by
  rw [swap_apply_def, swap_apply_def]
  simp only [Fin.lt_def, Fin.ext_iff] at hij hne ⊢
  split_ifs <;> omega

theorem invCount_mul_swap_lt (w : Perm (Fin ℓ)) {a b : Fin ℓ} (hab : a.val + 1 = b.val)
    (hw : w b < w a) : invCount (w * swap a b) < invCount w := by
  classical
  set s := swap a b
  have hinj : Function.Injective (Prod.map s s) := fun p q h => by
    simp only [Prod.map, Prod.mk.injEq] at h
    exact Prod.ext (s.injective h.1) (s.injective h.2)
  rw [invCount, ← Finset.card_image_of_injective _ hinj, invCount]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(a, b), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [Fin.lt_def]; omega, hw⟩
    · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
        not_and, Prod.map, Prod.mk.injEq]
      rintro ⟨i, j⟩ ⟨hij, -⟩ hi hj
      have hi' : i = b := by
        have := congrArg s hi
        simpa [s, swap_apply_self] using this
      have hj' : j = a := by
        have := congrArg s hj
        simpa [s, swap_apply_self] using this
      subst hi' hj'
      simp only [Fin.lt_def] at hij
      omega
  · rintro _ hp
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.map] at hp
    obtain ⟨⟨i, j⟩, ⟨hij, hwij⟩, rfl⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hne : ¬ (i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      simp only [Perm.mul_apply, s, swap_apply_left, swap_apply_right] at hwij
      exact lt_asymm hw hwij
    exact ⟨swap_lt_swap hab hij hne, hwij⟩

/-- A permutation other than the identity has a descent at an adjacent pair. -/
theorem exists_descent {w : Perm (Fin ℓ)} (hw : w ≠ 1) :
    ∃ (n m : ℕ) (h : n + 2 + m = ℓ), w (Fin.cast h (Fin.castAdd m (Fin.natAdd n 1))) <
      w (Fin.cast h (Fin.castAdd m (Fin.natAdd n 0))) := by
  by_contra hc
  simp only [not_exists, not_lt] at hc
  apply hw
  obtain _ | k := ℓ
  · exact Subsingleton.elim _ _
  have hmono : StrictMono w := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have hk : i.val + 2 + (k - 1 - i.val) = k + 1 := by omega
    have := hc i.val (k - 1 - i.val) hk
    have h1 : (Fin.cast hk (Fin.castAdd (k - 1 - i.val) (Fin.natAdd i.val (1 : Fin 2)))) =
        i.succ := Fin.ext (by simp)
    have h0 : (Fin.cast hk (Fin.castAdd (k - 1 - i.val) (Fin.natAdd i.val (0 : Fin 2)))) =
        i.castSucc := Fin.ext (by simp)
    rw [h0, h1] at this
    exact lt_of_le_of_ne this (fun h => by
      have := w.injective h
      exact absurd (congrArg Fin.val this) (by simp))
  have : (StrictMono.orderIsoOfSurjective w hmono w.surjective) = OrderIso.refl _ :=
    Subsingleton.elim _ _
  ext x
  exact congrArg Fin.val (DFunLike.congr_fun this x)


theorem swapAt_eq_swap (n m : ℕ) (h : n + 2 + m = ℓ) :
    swapAt n m h = swap (Fin.cast h (Fin.castAdd m (Fin.natAdd n 0)))
      (Fin.cast h (Fin.castAdd m (Fin.natAdd n 1))) := rfl

theorem swapAt_inv (n m : ℕ) (h : n + 2 + m = ℓ) : (swapAt n m h)⁻¹ = swapAt n m h :=
  swap_inv _ _

theorem swapAt_mul_self (n m : ℕ) (h : n + 2 + m = ℓ) : swapAt n m h * swapAt n m h = 1 :=
  swap_mul_self _ _

/-- **The length condition at a descent** (Webster, arXiv:1309.3796v2, Lemma 6.5, in the form
of `braidClass_mul`): if `w` has a descent at the adjacent pair `s`, then every pair of strands
crossed by `τ = w s` is still crossed by `τ s = w`. -/
theorem lengthAdditive_mul_swapAt (w : Perm (Fin ℓ)) (n m : ℕ) (h : n + 2 + m = ℓ)
    (hw : w (Fin.cast h (Fin.castAdd m (Fin.natAdd n 1))) <
      w (Fin.cast h (Fin.castAdd m (Fin.natAdd n 0)))) :
    ∀ x y, [x, y] <+ (List.finRange ℓ).map ⇑(w * swapAt n m h * swapAt n m h) →
      [y, x] <+ (List.finRange ℓ).map ⇑(w * swapAt n m h) → [y, x] <+ List.finRange ℓ := by
  intro x y hxy hyx
  set a := Fin.cast h (Fin.castAdd m (Fin.natAdd n 0))
  set b := Fin.cast h (Fin.castAdd m (Fin.natAdd n 1))
  have hab : a.val + 1 = b.val := by simp [a, b]
  rw [mul_assoc, swapAt_mul_self, mul_one] at hxy
  obtain ⟨i, j, hij, rfl, rfl⟩ := pair_sublist_map_finRange hxy
  obtain ⟨i', j', hij', hi', hj'⟩ := pair_sublist_map_finRange hyx
  rw [swapAt_eq_swap, Perm.mul_apply] at hi' hj'
  have h1 := w.injective hi'
  have h2 := w.injective hj'
  by_cases hne : i' = a ∧ j' = b
  · obtain ⟨rfl, rfl⟩ := hne
    rw [swap_apply_left] at h1
    rw [swap_apply_right] at h2
    subst h1 h2
    exact pair_sublist_finRange hw
  · have := swap_lt_swap hab hij' hne
    rw [h1, h2] at this
    exact absurd hij (lt_asymm this)

end Descent

/-! ### The induction -/

universe w

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}

/-- The class map of `𝔅_w` is `x ↦ B(f x, -)` for a map `f` congruent at `v = 1` to the
permutation of the tensor factors by `w`, for all labels `λ`. -/
def HasCongruentBraidClass [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I),
    Module.Finite k (TensorProductAlgebra k Q Ω ν)] (w : Perm (Fin ℓ)) : Prop :=
  ∀ (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)),
    ∃ f : TensorSpace wt →ₗ[𝕂] TensorSpace (wt ∘ w),
      VOneCongr f (tensorPermute wt w).toLinearMap ∧
        braidClass C hQ hR Λ wt hwt w = (formDual hR (wt ∘ w)).comp f

variable [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (κ : List (Fin ℓ)),
    DG.HasDerivedCategory.{w, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Ω) (ν := ν) κ)]
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (κ : List (Fin ℓ)),
    DG.HasDerivedCategory.{w, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Ω) (ν := ν) κ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w, 0} ℤ]

/-- **The class map along a reduced word** (Webster, arXiv:1309.3796v2, proof of Lemma 6.11,
induction around `p_n → f_n → s_n → p_{n+1}`): for every `w ≠ 1`, the class map of `𝔅_w` is
`x ↦ B(f x, -)` with `f` congruent at `v = 1` to the permutation of the tensor factors by `w`.
Route hypotheses: `AllFiniteDeltaInjective` and `RowFigureFiveHypotheses` (Corollary 6.10), and
`BraidDiagramFiltration` (the diagram filtration of the step `p_n → f_n`). -/
theorem hasCongruentBraidClass
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (H : ∀ (n m : ℕ), n + 2 + m = ℓ → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
      (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []),
      RowFigureFiveHypotheses C hQ Ω u hu)
    (hD : ∀ (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (w : Perm (Fin ℓ)),
      BraidDiagramFiltration C hQ Λ wt w) :
    ∀ w : Perm (Fin ℓ), w ≠ 1 → HasCongruentBraidClass C hQ hR w := by
  have hadj : ∀ (n m : ℕ) (h : n + 2 + m = ℓ), HasCongruentBraidClass C hQ hR (swapAt n m h) :=
    fun n m h Λ wt hwt => exists_braidClass_swapAt.{w} C hQ hR n m h Λ wt hwt hall (H n m h)
  intro w
  induction hn : invCount w using Nat.strong_induction_on generalizing w with
  | _ N ih =>
  intro hw1
  obtain ⟨n, m, h, hdesc⟩ := exists_descent hw1
  set s := swapAt n m h with hs
  set τ := w * s with hτ
  have hwτ : τ * s = w := by rw [hτ, mul_assoc, hs, swapAt_mul_self, mul_one]
  by_cases hτ1 : τ = 1
  · rw [← hwτ, hτ1, one_mul]
    exact hadj n m h
  have hlt : invCount τ < N := hn ▸ invCount_mul_swap_lt w (by simp) hdesc
  have hτc := ih _ hlt τ rfl hτ1
  rw [← hwτ]
  intro Λ wt hwt
  obtain ⟨fτ, hfτ, hτcls⟩ := hτc Λ wt hwt
  obtain ⟨fσ, hfσ, hσcls⟩ := hadj n m h (Λ ∘ τ) (wt ∘ τ) (fun r i => hwt (τ r) i)
  -- `B(s, 1)` for the labels `λ ∘ τ` is standardly filtered (length one, reflected)
  have hB : ∀ ν : Multiset I, ∃ l : List {t : Seq (stendhalWeight ℓ ν) //
      redWord t = List.finRange ℓ ∧ ¬ IsViolated t},
      HasFiltration (fun t => ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ τ)
        (ν := ν) (List.finRange ℓ))ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ τ) t.1
          (List.finRange ℓ))) l
        (ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ τ) (ν := ν)
          (List.finRange ℓ))ᵐᵒᵖ (braidingBimodule k Q (Λ ∘ τ) ν ((List.finRange ℓ).map s)
            (List.finRange ℓ))) := fun ν => by
    refine exists_hasFiltration_braidingBimodule_of_braidFunctor (Λ := Λ ∘ τ)
      (isReducedChoice_canChoice ν) hQ.klrSymm hQ s fun t ht => ?_
    obtain ⟨f₁, hf₁, hcls₁⟩ := hadj n m h ((Λ ∘ τ) ∘ s) ((wt ∘ τ) ∘ s) (fun r i => hwt (τ (s r)) i)
    rw [hs, swapAt_inv]
    exact hasCornerStandardFiltration_braidF_rightSequence C hQ hR ((Λ ∘ τ) ∘ s) ((wt ∘ τ) ∘ s)
      (fun r i => hwt (τ (s r)) i) s f₁ hf₁ hcls₁ (hD _ _ s) t ht
  have hN : ∀ (ν : Multiset I) (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t),
      BraidConcentrated.{w} (Λ ∘ τ) ν (isReducedChoice_canChoice ν) hQ.klrSymm s hQ
        (braidF C hQ Λ τ ν (rightSequenceProj (stendhalGradingDatum Λ hQ.gradingDatum
          (fun i => C.dot i i / 2) (dotDegree C hQ)) t ht).toGFin) ∧
      ∃ Ps : List (GProj (oppositeGrade (tensorProductGrade (stendhalGradingDatum (Λ ∘ τ)
          hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)) ν))),
        Nonempty (GFin.Resolution (braidF C hQ Λ τ ν (rightSequenceProj
          (stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ))
            t ht).toGFin) (Ps.map GProj.toGFin)) := by
    intro ν t ht
    have hF := hasCornerStandardFiltration_braidF_rightSequence C hQ hR Λ wt hwt τ fτ hfτ hτcls
      (hD Λ wt τ) t ht
    obtain ⟨l, hl⟩ := hB ν
    exact ⟨braidConcentrated_of_hasCornerStandardFiltration (Λ := Λ ∘ τ)
        (isReducedChoice_canChoice ν) hQ.klrSymm hQ s hall hl hF,
      exists_resolution_of_hasCornerStandardFiltration (isReducedChoice_canChoice ν)
        hQ.klrSymm hQ hall hF⟩
  have hcls := braidClass_mul.{w} C hQ hR Λ wt hwt τ s
    (lengthAdditive_mul_swapAt w n m h hdesc) fτ fσ hτcls hσcls hN
  refine ⟨fσ ∘ₗ fτ, ?_, hcls⟩
  have hp : (tensorPermute (wt ∘ τ) s).toLinearMap ∘ₗ (tensorPermute wt τ).toLinearMap =
      (tensorPermute wt (τ * s)).toLinearMap :=
    LinearMap.ext fun x => tensorPermute_trans τ s x
  exact hp ▸ hfσ.comp hfτ

include hR in
/-- **Lemma 6.11, standard filtrations** (Webster, arXiv:1309.3796v2, §6.1): for every `w ≠ 1`,
the graded braid functor `𝔅_w` sends each sequence projective `e(t) T^λ` to a module with a
standard filtration. The case `w = 1` is the standard filtration of the projective itself
(Proposition 5.20). Route hypotheses: `AllFiniteDeltaInjective` and `RowFigureFiveHypotheses`
(Corollary 6.10), and `BraidDiagramFiltration` (the diagram filtration of the step `p_n → f_n`),
tracked for removal. -/
theorem hasCornerStandardFiltration_braidF
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (H : ∀ (n m : ℕ), n + 2 + m = ℓ → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
      (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []),
      RowFigureFiveHypotheses C hQ Ω u hu)
    (hD : ∀ (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (w : Perm (Fin ℓ)),
      BraidDiagramFiltration C hQ Λ wt w)
    (w : Perm (Fin ℓ)) (hw : w ≠ 1) (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    {ν : Multiset I} (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t) :
    HasCornerStandardFiltration (Λ ∘ w) ν (isReducedChoice_canChoice ν) hQ.klrSymm hQ
      (braidF C hQ Λ w ν (rightSequenceProj (stendhalGradingDatum Λ hQ.gradingDatum
        (fun i => C.dot i i / 2) (dotDegree C hQ)) t ht).toGFin) := by
  obtain ⟨f, hf, hcls⟩ := hasCongruentBraidClass.{w} C hQ hR hall H hD w hw Λ wt hwt
  exact hasCornerStandardFiltration_braidF_rightSequence C hQ hR Λ wt hwt w f hf hcls
    (hD Λ wt w) t ht

end Categorification.Stendhal.FirstWeight
