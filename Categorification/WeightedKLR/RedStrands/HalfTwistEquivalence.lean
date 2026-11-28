/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistFullyFaithful
import Categorification.WeightedKLR.RedStrands.BraidColumnStayIndex
import Categorification.WeightedKLR.RedStrands.RightProjectiveStandardFiltration
import Categorification.WeightedKLR.RedStrands.StandardStratificationStd
import Categorification.Algebra.LocalizingFiltration

set_option backward.isDefEq.respectTransparency false

/-!
# The half twist is an equivalence

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Theorem 6.15, for the half twist: the derived braiding functor `𝔅_w = - ⊗ᴸ B(1, κ)` for a red
order `κ = w(1, …, ℓ)` reversing every pair of red strands is an equivalence
(`isEquivalence_braidingFunctor_halfTwist`). It is fully faithful
(`fullyFaithfulBraidingFunctorHalfTwist`), so its essential image is localizing; it contains
the cuts `e(t) V e_κ`, the images of the loading projectives. Each cut is filtered by the
loading standards at the bottoms of the eligible indices of its column, and the stay index has
the fewest pairs of a red strand left of a black strand, every other index strictly more
(`exists_stay_label`). By induction on that number every loading standard at `κ` lies in the
essential image (`mem_essImage_loadingStandard_halfTwist`), hence so does every loading
projective at `κ` (Proposition 5.21, right form), and these generate.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR Equiv MulOpposite DG ModuleFiltration BraidColumn
open scoped DG.DegreeZero

theorem count_map_eq_one {α β : Type*} [DecidableEq α] [DecidableEq β] {L : List α} (g : α → β)
    {a : α} {b : β} (hL : L.Nodup) (ha : a ∈ L) (hg : ∀ x ∈ L, g x = b ↔ x = a) :
    (L.map g).count b = 1 := by
  rw [List.count_eq_countP, List.countP_map]
  rw [List.countP_congr (q := fun x => x == a) (fun x hx => by simpa using hg x hx)]
  rw [← List.count_eq_countP]
  exact List.count_eq_one_of_mem hL ha

/-- The loading standard of a violated loading is zero. -/
theorem subsingleton_loadingStandard_of_isViolated {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
    {u : Seq (stendhalWeight ℓ ν)}
    (hv : IsViolated u) (κ : List (Fin ℓ)) :
    Subsingleton (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) u κ) := by
  have h0 : ∀ x : violCorner k Q Λ ν u κ, x = 0 := fun x => Subtype.ext (by
    rw [← (mem_violCorner_iff.1 x.2).1, violMk_e hv, zero_mul]; rfl)
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [h0 a, h0 b]

theorem count_subtype_eq_one {α : Type*} [DecidableEq α] {p : α → Prop}
    [DecidableEq (Subtype p)] {m : List (Subtype p)} {c : Subtype p}
    (h : @List.count _ instBEqOfDecidableEq c.1 (m.map Subtype.val) = 1) :
    @List.count _ instBEqOfDecidableEq c m = 1 := by
  have h' := (List.count_map_of_injective m Subtype.val Subtype.val_injective c).symm.trans h
  rw [List.count_eq_countP] at h'
  rw [@List.count_eq_countP _ instBEqOfDecidableEq, ← h']
  exact List.countP_congr fun x _ => by simp only [beq_iff_eq]

section Relabel

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

/-- A red order `w(1, …, ℓ)` reversing every pair of red strands is decreasing. -/
theorem strictAnti_of_isRedReversed {ℓ : ℕ} {ν : Multiset I} {w : Perm (Fin ℓ)}
    {u : Seq (stendhalWeight ℓ ν)} (hu : redWord u = List.map w (List.finRange ℓ))
    (hrev : IsRedReversed u) : StrictAnti w := by
  have hord : IsRedOrdered (Seq.redPerm w⁻¹ u) := by
    rw [← redWord_eq_finRange_iff, redWord_redPerm, hu, List.map_map]
    simp
  intro c c' h
  have hp : ∀ c, redPos (Seq.redPerm w⁻¹ u) c = redPos u (w c) := fun c =>
    (eq_redPos (by rw [Seq.redPerm_lbl, lbl_redPos]; simp)).symm
  have hlt : redPos u (w c) < redPos u (w c') := by
    rw [← hp, ← hp]
    exact (redPos_lt_iff hord).2 h
  exact hrev _ _ _ _ hlt (lbl_redPos u (w c)) (lbl_redPos u (w c'))

/-- A labelled form of `exists_hasFiltration_of_cornerRelabel`: relabelling the corners
relabels the labels of the filtration by `σ`. -/
theorem exists_labelled_hasFiltration_of_cornerRelabel (σ : Perm (Fin ℓ)) {κ : List (Fin ℓ)}
    {X : ModuleCat.{0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν) κ)ᵐᵒᵖ}
    {Y : ModuleCat.{0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (κ.map σ))ᵐᵒᵖ}
    (e : (ModuleCat.restrictScalars (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ :
        (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (κ.map σ))ᵐᵒᵖ →+*
          (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν) κ)ᵐᵒᵖ)).obj X
        ≃ₗ[(ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (κ.map σ))ᵐᵒᵖ] Y)
    {labels : List (Seq (stendhalWeight ℓ ν))}
    (h : ∃ m : List {s : Seq (stendhalWeight ℓ ν) // redWord s = κ ∧ ¬ IsViolated s},
      m.map Subtype.val = labels ∧
      HasFiltration (fun s => ModuleCat.of
        (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν) κ)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ σ) s.1 κ)) m X) :
    ∃ m : List {s : Seq (stendhalWeight ℓ ν) // redWord s = κ.map σ ∧ ¬ IsViolated s},
      m.map Subtype.val = labels.map (Seq.redPerm σ) ∧
      HasFiltration (fun s => ModuleCat.of
        (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (κ.map σ))ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.1 (κ.map σ))) m Y := by
  obtain ⟨m, hmv, hm⟩ := h
  let g : {s : Seq (stendhalWeight ℓ ν) // redWord s = κ ∧ ¬ IsViolated s} →
      {s : Seq (stendhalWeight ℓ ν) // redWord s = κ.map σ ∧ ¬ IsViolated s} := fun s =>
    ⟨Seq.redPerm σ s.1, by rw [redWord_redPerm, s.2.1], by
      rw [isViolated_redPerm]; exact s.2.2⟩
  have h1 := (hm.restrictScalars (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ :
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (κ.map σ))ᵐᵒᵖ →+*
      (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν) κ)ᵐᵒᵖ)).of_equiv e
  refine ⟨m.flatMap fun s => [g s], ?_, h1.bind fun s => HasFiltration.single ?_⟩
  · rw [← List.map_eq_flatMap, ← hmv, List.map_map, List.map_map]
    rfl
  · exact loadingStandardRelabelEquiv σ s.2.1

/-- A property of the right ideal of a loading idempotent depends only on the loading. -/
theorem rIdealObj_violLoadingIdem_congr {κ : List (Fin ℓ)}
    [DG.HasDerivedCategory.{0, 0}
      (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ]
    {s₁ s₂ : Seq (stendhalWeight ℓ ν)}
    (h : s₁ = s₂) (h₁ : redWord s₁ = κ) (h₂ : redWord s₂ = κ)
    {P : ObjectProperty (DG.DerivedCategory.{0}
      (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ)}
    (hP : P (rIdealObj (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) h₁))) :
    P (rIdealObj (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) h₂)) := by
  subst h
  exact hP

end Relabel

section KhovanovLauda

open QuantumGroup KL3.Diagram
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} {k : Type} [Field k] (C : CartanDatum I)
  (hQ : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {ℓ : ℕ}
  (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (w : Perm (Fin (ℓ + 1)))
  {Y : Type*} [AddCommGroup Y] [Finite I]
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I),
    Module.Finite k (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Ω ν)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} ℤ]
  (H : ∀ (n m : ℕ), n + 2 + m = ℓ + 1 → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
    (u : Fin (n + 2 + m) → List I) (hu : u (FirstWeight.rightPos n m) = []),
    FirstWeight.RowFigureFiveHypotheses C hQ Ω u hu)
  (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
  (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (hw : w ≠ 1)

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "CL" κ => ViolOrderCorner (k := k) (Q := QL) (Λ := Λ) (ν := ν) κ
local notation "PL" h => ModuleCat.of (CL (List.finRange (ℓ + 1)))ᵐᵒᵖ
  (rIdeal (violLoadingIdem (k := k) (Q := QL) (Λ := Λ) h))

local notation "κw" => List.map w (List.finRange (ℓ + 1))

include hR H hwt hw in
/-- **The cut of a loading projective under the half twist, with the labels of its column**
(Webster, arXiv:1309.3796v2, proof of Lemma 6.11): `e(t) V e_κ` is filtered by the loading
standards at the bottoms `W⁻¹ t` of the eligible indices `W`. Route hypothesis: the injectivity
of Lemma 6.8 (`RowFigureFiveHypotheses`). -/
theorem exists_hasFiltration_violCorner_halfTwist {t : Seq (stendhalWeight (ℓ + 1) ν)}
    (ht : IsRedOrdered t) :
    ∃ m : List {s : Seq (stendhalWeight (ℓ + 1) ν) // redWord s = κw ∧ ¬ IsViolated s},
      m.map Subtype.val = (braidColumnIndexList t w).reverse.map (fun W => W⁻¹ • t) ∧
      HasFiltration (fun s => ModuleCat.of (CL κw)ᵐᵒᵖ
          (ViolLoadingStandard (k := k) (Q := QL) (Λ := Λ) s.1 κw)) m
        (ModuleCat.of (CL κw)ᵐᵒᵖ (violCorner k QL Λ ν t κw)) := by
  have hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective QL Λ' hQ.klrSymm :=
    fun _ _ => allFiniteDeltaInjective_of_rouquier hQ hQ.klrSymm
  obtain ⟨f, hf, hcls⟩ := FirstWeight.hasCongruentBraidClass.{0} C hQ hR hall H w hw Λ wt hwt
  have h := exists_labelled_hasFiltration_of_cornerRelabel w
    (braidRightSequenceCutEquiv (Λ := Λ) (FirstWeight.isReducedChoice_canChoice ν)
      hQ.klrSymm hQ w t ht)
    (FirstWeight.exists_hasFiltration_braidRightSequenceCut C hQ hR Λ wt hwt w f hf hcls t ht)
  rwa [List.map_map, show (Seq.redPerm w ∘
      fun W : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) =>
      Seq.redPerm w⁻¹ (W⁻¹ • t)) = fun W => W⁻¹ • t from funext fun W => by
    simp only [Function.comp_apply]
    rw [Seq.redPerm_redPerm, mul_inv_cancel, Seq.redPerm_one]] at h

omit [Finite I] [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I),
    Module.Finite k (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Ω ν)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)]
  [DG.HasDerivedCategory.{0, 0} ℤ] in
/-- The cut `e(t) V e_κ` is in the essential image of the half twist. -/
theorem mem_essImage_violCorner_halfTwist {t : Seq (stendhalWeight (ℓ + 1) ν)}
    (ht : IsRedOrdered t) :
    (braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1)) κw).essImage
      (moduleObj (ModuleCat.of (CL κw)ᵐᵒᵖ (violCorner k QL Λ ν t κw))) :=
  ⟨loadingProjectiveObj k C Λ ν ((redWord_eq_finRange_iff t).2 ht),
    ⟨braidingFunctorObjLoadingProjectiveIso (κ := κw) ((redWord_eq_finRange_iff t).2 ht)⟩⟩

include hR H hwt hw in
/-- The essential image of the half twist is localizing, as it is fully faithful. -/
theorem isLocalizing_essImage_halfTwist
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t') :
    IsLocalizing.{0} (braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1)) κw).essImage := by
  have := (fullyFaithfulBraidingFunctorHalfTwist C hQ Λ ν w hR H wt hwt hw hκ).full
  refine isLocalizing_essImage (braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1)) κw)
    fun J => ?_
  unfold braidingFunctor
  exact derivedRightTensor_preservesCoproducts _ _ _ J

include hR H hwt hw in
/-- **Every loading standard at `κ` is in the essential image of the half twist** (Webster,
arXiv:1309.3796v3, proof of Theorem 6.15), by induction on the number of pairs of a red strand
left of a black strand. Route hypothesis: `RowFigureFiveHypotheses`. -/
theorem mem_essImage_loadingStandard_halfTwist
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
    (u : Seq (stendhalWeight (ℓ + 1) ν)) (hu : redWord u = κw) :
    (braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1)) κw).essImage
      (moduleObj (ModuleCat.of (CL κw)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := QL) (Λ := Λ) u κw))) := by
  have hP := isLocalizing_essImage_halfTwist C hQ Λ ν w hR H wt hwt hw hκ
  let B := Multiset.card (stendhalWeight (ℓ + 1) ν) * (ℓ + 1)
  suffices key : ∀ d, ∀ u : Seq (stendhalWeight (ℓ + 1) ν), redWord u = κw →
      B - redBlackPairs u = d → (braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1)) κw).essImage
        (moduleObj (ModuleCat.of (CL κw)ᵐᵒᵖ
          (ViolLoadingStandard (k := k) (Q := QL) (Λ := Λ) u κw))) from key _ u hu rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro u hu hd
  by_cases hv : IsViolated u
  · have := subsingleton_loadingStandard_of_isViolated (k := k) (Q := QL) (Λ := Λ) hv κw
    exact mem_moduleObj_of_subsingleton hP this
  have hσ := strictAnti_of_isRedReversed hu (hκ u hu)
  obtain ⟨b, hb, W₀, hW₀, hlab, hlt⟩ := exists_stay_label hσ u hu hv
  obtain ⟨m, hmv, hm⟩ := exists_hasFiltration_violCorner_halfTwist C hQ Λ ν w hR H wt hwt hw hb
  let c : {s : Seq (stendhalWeight (ℓ + 1) ν) // redWord s = κw ∧ ¬ IsViolated s} :=
    ⟨u, hu, hv⟩
  have hgW : ∀ W ∈ (braidColumnIndexList b w).reverse, W⁻¹ • b = u ↔ W = W₀ := fun W hW => by
    refine ⟨fun h => ?_, fun h => h ▸ hlab⟩
    by_contra hne
    have := hlt W (List.mem_reverse.1 hW) hne
    rw [h] at this
    exact lt_irrefl _ this
  have hY : (braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1)) κw).essImage
      (moduleObj (ModuleCat.of (CL κw)ᵐᵒᵖ (violCorner k QL Λ ν b κw))) :=
    mem_essImage_violCorner_halfTwist (k := k) (C := C) (Λ := Λ) (ν := ν) (w := w) (ht := hb) ..
  have hc0 : @List.count _ instBEqOfDecidableEq c.1 (m.map Subtype.val) = 1 := by
    rw [hmv]
    exact count_map_eq_one _ (List.nodup_reverse.2 (nodup_braidColumnIndexList b w))
      (List.mem_reverse.2 hW₀) hgW
  have hothers : ∀ e ∈ m, e ≠ c →
      (braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1)) κw).essImage
        (moduleObj (ModuleCat.of (CL κw)ᵐᵒᵖ
          (ViolLoadingStandard (k := k) (Q := QL) (Λ := Λ) e.1 κw))) := fun e he hne => by
    have he' : e.1 ∈ m.map Subtype.val := List.mem_map_of_mem he
    rw [hmv] at he'
    obtain ⟨W, hW, hWe⟩ := List.mem_map.1 he'
    have hWne : W ≠ W₀ := fun h => hne (Subtype.ext (by rw [← hWe, h, hlab]))
    have hlt' := hlt W (List.mem_reverse.1 hW) hWne
    rw [hWe] at hlt'
    have hle := redBlackPairs_le e.1
    exact ih _ (by omega) e.1 e.2.1 rfl
  exact HasFiltration.mem_of_mem (L := fun s : {s : Seq (stendhalWeight (ℓ + 1) ν) //
      redWord s = κw ∧ ¬ IsViolated s} => ModuleCat.of (CL κw)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := QL) (Λ := Λ) s.1 κw)) (c := c) hP hm hY
    (count_subtype_eq_one hc0) hothers

include hR H hwt hw in
/-- **The derived half twist is an equivalence** (Webster, arXiv:1309.3796v3, Theorem 6.15, for
the half twist), at the Khovanov–Lauda scalars, for a red order `κ = w(1, …, ℓ)` reversing every
pair of red strands. Route hypothesis: the injectivity of Lemma 6.8
(`RowFigureFiveHypotheses`). -/
theorem isEquivalence_braidingFunctor_halfTwist
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t') :
    (braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1)) κw).IsEquivalence := by
  let ff := fullyFaithfulBraidingFunctorHalfTwist C hQ Λ ν w hR H wt hwt hw hκ
  have := ff.full
  have := ff.faithful
  have hP := isLocalizing_essImage_halfTwist C hQ Λ ν w hR H wt hwt hw hκ
  have hproj : ∀ t : {t : Seq (stendhalWeight (ℓ + 1) ν) // redWord t = κw},
      (braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1)) κw).essImage
        (rIdealObj (violLoadingIdem (k := k) (Q := QL) (Λ := Λ) t.2)) := by
    rintro ⟨t, ht⟩
    have hs : IsRedOrdered (Seq.redPerm w⁻¹ t) := by
      rw [← redWord_eq_finRange_iff, redWord_redPerm, ht, List.map_map]
      simp
    obtain ⟨m, hm⟩ := exists_hasFiltration_loadingProjective (Λ := Λ)
      (FirstWeight.isReducedChoice_canChoice ν) hQ.klrSymm w
      (hasStandardFiltrations_of_rouquier hQ hQ.klrSymm (Λ ∘ w)) hs
    have hmem := hm.mem_of_forall hP fun c _ =>
      mem_essImage_loadingStandard_halfTwist C hQ Λ ν w hR H wt hwt hw hκ _
        (redWord_relabel w c.2)
    refine rIdealObj_violLoadingIdem_congr (k := k) (Q := QL) ?_ (redWord_relabel w hs) ht hmem
    rw [Seq.redPerm_redPerm, mul_inv_cancel, Seq.redPerm_one]
  have : (braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1)) κw).EssSurj := ⟨fun Y =>
    (compactlyGenerates_loadingProjective (k := k) (Q := QL) (Λ := Λ) (ν := ν)
      κw).forall_of_isLocalizing hP hproj Y⟩
  exact { }

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
