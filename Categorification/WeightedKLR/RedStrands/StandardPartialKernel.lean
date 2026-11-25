/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CommonUpperLoading
import Categorification.WeightedKLR.RedStrands.AdjacentBlockSlide
import Categorification.WeightedKLR.RedStrands.BraidedStandardModule

/-!
# Standard and partial standard relations at a loading

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 (v3: Proposition
6.10). Lemma 6.8 treats the partial standard of a loading `t` for an adjacent pair of red
strands `a, b`: the loading projective modulo the loadings whose retained root
(`adjacentBlockRoot a b`, all cuts except the one between `a` and `b`) is strictly higher.
The standard module of Definition 5.1 instead divides by the loadings strictly higher in
Webster's order, which also sees the cut at `b`.

* Every retained-higher relation is a standard relation, for any loading of the red order
  `… a b …`: a diagram `e(t) x e(u)` factors through loadings above `t` and `u`
  (`e_mul_mul_e_mem_commonUpperSpan`), and these are strictly above `t`
  (`mul_mem_stendhalUpperIdeal_of_mem_blockUpperIdeal`).
* Conversely, every standard relation is retained-higher when the cut at `b` is rigid at `t`
  (`IsRigidCut`), as at the loading of Figure 5, where no black strand lies between `b` and the
  next red strand (`stendhalUpperIdeal_le_blockUpperIdeal`).

So at such a loading the two kernels agree (`mem_violStandardUpper_iff_mem_blockUpperIdeal`).
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

section Root

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

variable {a b : Fin ℓ} {L M : List (Fin ℓ)}

theorem adjacentBlockRoot_eq_blackCount_of_pair {s : Seq μ} (hs : redWord s = L ++ a :: b :: M)
    {r : Fin ℓ} (hr : r = a ∨ r = b) : adjacentBlockRoot a b s r = blackCount s a := by
  have h := adjacentBlockRoot_pair hs
  simp only [adjacentBlockRoot, or_true, ↓reduceIte] at h
  simp only [adjacentBlockRoot, hr, ↓reduceIte]
  exact h

theorem adjacentBlockRoot_eq_blackCount_of_not_pair (s : Seq μ) {r : Fin ℓ}
    (hr : ¬ (r = a ∨ r = b)) : adjacentBlockRoot a b s r = blackCount s r := by
  funext i
  simp only [adjacentBlockRoot, hr, ↓reduceIte, blockBlackCount_singleton]

/-- The retained root is monotone in Webster's order, within one red order. -/
theorem adjacentBlockRoot_mono {s v : Seq μ} (hs : redWord s = L ++ a :: b :: M)
    (hv : redWord v = L ++ a :: b :: M) (hle : StendhalLE s v) :
    adjacentBlockRoot a b s ≤ adjacentBlockRoot a b v := by
  intro r i
  by_cases hr : r = a ∨ r = b
  · rw [adjacentBlockRoot_eq_blackCount_of_pair hs hr,
      adjacentBlockRoot_eq_blackCount_of_pair hv hr]
    exact hle a i
  · rw [adjacentBlockRoot_eq_blackCount_of_not_pair s hr,
      adjacentBlockRoot_eq_blackCount_of_not_pair v hr]
    exact hle r i

/-- A loading above `t` and above a retained-higher loading is strictly above `t`. -/
theorem stendhalLT_of_adjacentBlockRoot_lt {t u v : Seq μ} (ht : redWord t = L ++ a :: b :: M)
    (hu : redWord u = L ++ a :: b :: M) (hv : redWord v = L ++ a :: b :: M)
    (hlt : adjacentBlockRoot a b t < adjacentBlockRoot a b u) (huv : StendhalLE u v)
    (htv : StendhalLE t v) : StendhalLT t v :=
  ⟨htv, fun hvt => not_le_of_gt (lt_of_lt_of_le hlt (adjacentBlockRoot_mono hu hv huv))
    (adjacentBlockRoot_mono hv ht hvt)⟩

/-- The cut at the red strand `b` is rigid at `t`: a loading of the same red order above `t`
with the same black counts at every other red strand has the same black counts at `b`. This
holds when no black strand of `t` lies between `b` and the next red strand. -/
def IsRigidCut (t : Seq μ) (b : Fin ℓ) : Prop :=
  ∀ u : Seq μ, redWord u = redWord t → StendhalLE t u →
    (∀ r, r ≠ b → blackCount u r = blackCount t r) → blackCount u b = blackCount t b

/-- At a loading whose cut at `b` is rigid, a loading strictly above in Webster's order is
retained-higher. -/
theorem adjacentBlockRoot_lt_of_stendhalLT {t u : Seq μ} (ht : redWord t = L ++ a :: b :: M)
    (hu : redWord u = L ++ a :: b :: M) (hrig : IsRigidCut t b) (hlt : StendhalLT t u) :
    adjacentBlockRoot a b t < adjacentBlockRoot a b u := by
  refine lt_of_le_not_ge (adjacentBlockRoot_mono ht hu hlt.1) fun hle => hlt.2 ?_
  have hoff : ∀ r, r ≠ b → blackCount u r = blackCount t r := by
    intro r hrb
    by_cases hra : r = a
    · have h := hle r
      rw [adjacentBlockRoot_eq_blackCount_of_pair hu (Or.inl hra),
        adjacentBlockRoot_eq_blackCount_of_pair ht (Or.inl hra)] at h
      subst hra
      funext i
      exact le_antisymm (h i) (hlt.1 r i)
    · have hr : ¬ (r = a ∨ r = b) := fun h => h.elim hra hrb
      have h := hle r
      rw [adjacentBlockRoot_eq_blackCount_of_not_pair u hr,
        adjacentBlockRoot_eq_blackCount_of_not_pair t hr] at h
      funext i
      exact le_antisymm (h i) (hlt.1 r i)
  have hb := hrig u (hu.trans ht.symm) hlt.1 hoff
  intro r i
  by_cases hrb : r = b
  · subst hrb
    rw [hb]
  · rw [hoff r hrb]

private theorem card_filter_lbl_eq' (s : Seq μ) (x : I ⊕ Fin ℓ) :
    (Finset.univ.filter fun a => s.lbl a = x).card = Multiset.count x (stendhalWeight ℓ ν) := by
  have h := congrArg (Multiset.count x) s.2
  rw [← h, count_map_univ, Finset.card_filter]

omit [DecidableEq I] in
/-- Loadings of one red order place the red strands in the same order. -/
theorem redPos_lt_redPos_of_redWord_eq {s u : Seq μ} (h : redWord u = redWord s) {r r' : Fin ℓ}
    (hlt : redPos s r < redPos s r') : redPos u r < redPos u r' := by
  have hne : r ≠ r' := by
    rintro rfl
    exact lt_irrefl _ hlt
  rcases (redWord_pairwise_one s).both (h ▸ redWord_pairwise_one u) (mem_redWord s r)
      (mem_redWord s r') hne with ⟨_, h₂⟩ | ⟨h₁, _⟩
  · exact h₂ _ _ (lbl_redPos u r) (lbl_redPos u r')
  · exact absurd (h₁ _ _ (lbl_redPos s r') (lbl_redPos s r)) (lt_asymm hlt)

theorem blackCount_le_of_redPos_lt (s : Seq μ) {r r' : Fin ℓ} (h : redPos s r < redPos s r')
    (i : I) : blackCount s r i ≤ blackCount s r' i := by
  rw [blackCount_eq_card_lt_redPos, blackCount_eq_card_lt_redPos]
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

/-- A loading in which every black strand right of the red strand `b` is separated from `b` by
another red strand has a rigid cut at `b`. This is the loading of Figure 5 in
arXiv:1309.3796v2, §6.1, where the slot after `b` is empty. -/
theorem isRigidCut_of_black_right (t : Seq μ) (b : Fin ℓ)
    (hnext : ∀ x : Fin m, (t.lbl x).isLeft → redPos t b < x →
      ∃ c : Fin ℓ, redPos t b < redPos t c ∧ redPos t c < x) : IsRigidCut t b := by
  classical
  intro u hu hle hoff
  funext i
  refine le_antisymm ?_ (hle b i)
  by_cases hc : ∃ c : Fin ℓ, redPos t b < redPos t c
  · obtain ⟨c, hc, hmin⟩ := (Finset.univ.filter fun c => redPos t b < redPos t c).exists_min_image
      (redPos t) (by
        obtain ⟨c, hc⟩ := hc
        exact ⟨c, by simpa using hc⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hmin
    have hcb : c ≠ b := by
      rintro rfl
      exact lt_irrefl _ hc
    have h₁ : blackCount t c i ≤ blackCount t b i := by
      rw [blackCount_eq_card_lt_redPos, blackCount_eq_card_lt_redPos]
      refine Finset.card_le_card fun x hx => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨hx.1, lt_of_not_ge fun hge => ?_⟩
      have hne : redPos t b ≠ x := fun he => by
        have h' := hx.1
        rw [← he, lbl_redPos] at h'
        cases h'
      obtain ⟨c', hc', hc'x⟩ := hnext x (by simp [hx.1]) (lt_of_le_of_ne hge hne)
      exact absurd (hmin c' hc') (not_le_of_gt (hc'x.trans hx.2))
    calc blackCount u b i ≤ blackCount u c i :=
          blackCount_le_of_redPos_lt u (redPos_lt_redPos_of_redWord_eq hu hc) i
      _ = blackCount t c i := by rw [hoff c hcb]
      _ ≤ blackCount t b i := h₁
  · simp only [not_exists, not_lt] at hc
    have hall : ∀ x : Fin m, (t.lbl x).isLeft → x < redPos t b := by
      intro x hx
      refine lt_of_not_ge fun hge => ?_
      have hne : redPos t b ≠ x := fun he => by
        rw [← he, lbl_redPos] at hx
        simp at hx
      obtain ⟨c, hc', _⟩ := hnext x hx (lt_of_le_of_ne hge hne)
      exact absurd hc' (not_lt_of_ge (hc c))
    have ht : blackCount t b i = Multiset.count (.inl i) (stendhalWeight ℓ ν) := by
      rw [blackCount_eq_card_lt_redPos, ← card_filter_lbl_eq' t]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.1, fun h => ⟨h, hall x (by simp [h])⟩⟩
    rw [ht, blackCount_eq_card_lt_redPos, ← card_filter_lbl_eq' u]
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1

end Root

namespace BraidedStendhalAlgebra

open MvPolynomial MulOpposite

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "q" => violMk k Q Λ ν
local notation:max "E" j:arg => π (KLRAlgebra.e j)
local notation:max "P" κ:arg => violMk k Q Λ ν (redProj k Q Λ ν κ)

variable (k Q Λ ν) in
/-- The ideal generated by the loading idempotents of red order `κ` strictly above `t` in
Webster's order (arXiv:1309.3796v2, §5.1). -/
noncomputable def stendhalUpperIdeal (t : Seq μ) (κ : List (Fin ℓ)) : TwoSidedIdeal V :=
  TwoSidedIdeal.span {z | ∃ v : Seq μ, redWord v = κ ∧ StendhalLT t v ∧ z = E v}

variable {a b : Fin ℓ} {L M : List (Fin ℓ)}

private theorem π_surjective : Function.Surjective (π) :=
  (violMk_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν)).comp ofKLR_surjective

/-- **Retained-higher relations are standard relations.** At a loading `t` of red order
`L ++ a :: b :: M`, the left multiple by `e(t)` of any element of the ideal of retained-higher
loadings lies in the ideal of loadings strictly above `t`. -/
theorem mul_mem_stendhalUpperIdeal_of_mem_blockUpperIdeal {t : Seq μ}
    (ht : redWord t = L ++ a :: b :: M) {y : V}
    (hy : y ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t)) (c : V) :
    E t * c * y ∈ stendhalUpperIdeal k Q Λ ν t (redWord t) := by
  induction hy using TwoSidedIdeal.span_induction generalizing c with
  | mem x hx =>
    obtain ⟨s, hs, hlt, rfl⟩ := hx
    obtain ⟨z, rfl⟩ := π_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) c
    rw [← map_mul, ← map_mul]
    suffices H : ∀ y ∈ commonUpperSpan Q Λ s t, π y ∈ stendhalUpperIdeal k Q Λ ν t (redWord t) from
      H _ (e_mul_mul_e_mem_commonUpperSpan Q Λ s t hs.symm z)
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, a', b', hsv, htv, hv, rfl⟩ := hx
      have hlt' : StendhalLT t v := stendhalLT_of_adjacentBlockRoot_lt ht (hs.trans ht)
        (hv.trans (hs.trans ht)) hlt hsv htv
      have hgen : E v ∈ stendhalUpperIdeal k Q Λ ν t (redWord t) :=
        TwoSidedIdeal.subset_span ⟨v, hv.trans hs, hlt', rfl⟩
      rw [map_mul, map_mul]
      exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hgen)
    | zero => rw [map_zero]; exact TwoSidedIdeal.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact TwoSidedIdeal.add_mem _ hx hy
    | smul r x _ hx =>
      rw [map_smul, Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  | zero => rw [mul_zero]; exact TwoSidedIdeal.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact TwoSidedIdeal.add_mem _ (hx c) (hy c)
  | neg x _ hx => rw [mul_neg]; exact TwoSidedIdeal.neg_mem _ (hx c)
  | left_absorb a' x _ hx =>
    rw [← mul_assoc]
    have h := hx (c * a')
    rwa [← mul_assoc] at h
  | right_absorb b' x _ hx =>
    rw [← mul_assoc]
    exact TwoSidedIdeal.mul_mem_right _ _ _ (hx c)

/-- **Standard relations are retained-higher at a rigid cut.** -/
theorem stendhalUpperIdeal_le_blockUpperIdeal {t : Seq μ} (ht : redWord t = L ++ a :: b :: M)
    (hrig : IsRigidCut t b) :
    stendhalUpperIdeal k Q Λ ν t (redWord t) ≤
      blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t) := by
  refine TwoSidedIdeal.span_le.2 ?_
  rintro _ ⟨v, hv, hlt, rfl⟩
  exact TwoSidedIdeal.subset_span
    ⟨v, hv, adjacentBlockRoot_lt_of_stendhalLT ht (hv.trans ht) hrig hlt, rfl⟩

/-- At a loading with rigid cut at `b`, the standard and the partial standard relations of
`e(t)` agree. -/
theorem mul_mem_blockUpperIdeal_iff {t : Seq μ} (ht : redWord t = L ++ a :: b :: M)
    (hrig : IsRigidCut t b) (y : V) :
    E t * y ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t) ↔
      E t * y ∈ stendhalUpperIdeal k Q Λ ν t (redWord t) := by
  refine ⟨fun h => ?_, fun h => stendhalUpperIdeal_le_blockUpperIdeal ht hrig h⟩
  have h' := mul_mem_stendhalUpperIdeal_of_mem_blockUpperIdeal ht h 1
  rwa [mul_one, ← mul_assoc, ← map_mul, KLRAlgebra.e_mul_self] at h'

private theorem sandwich_mem (t : Seq μ) (κ : List (Fin ℓ)) (z : V) :
    E t * z * P κ ∈ violCorner k Q Λ ν t κ := by
  obtain ⟨a, rfl⟩ := violMk_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) z
  simpa only [AlgHom.comp_apply, map_mul] using mem_violCorner (s := t) (κ := κ) a

/-- **The standard relations as an ideal.** An element of the corner `e(t) T e_κ` lies in the
submodule of Definition 5.1 exactly when it lies in the ideal of loadings strictly above `t`. -/
theorem mem_violStandardUpper_iff {t : Seq μ} (x : violCorner k Q Λ ν t (redWord t)) :
    x ∈ violStandardUpper t (redWord t) ↔ x.1 ∈ stendhalUpperIdeal k Q Λ ν t (redWord t) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, a', hj, hlt, rfl⟩ := hy
      change E t * (a' * q (ofKLR k Q Λ ν (KLRAlgebra.e j))) * P (redWord t) ∈ _
      exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _
        (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span ⟨j, hj, hlt, rfl⟩)))
    | zero => exact TwoSidedIdeal.zero_mem _
    | add x y _ _ hx hy => exact TwoSidedIdeal.add_mem _ hx hy
    | smul r x _ hx =>
      rw [violCorner_smul_val]
      exact TwoSidedIdeal.mul_mem_right _ _ _ hx
  · intro hx
    suffices H : ∀ y ∈ stendhalUpperIdeal k Q Λ ν t (redWord t), ∀ c d : V,
        (⟨E t * c * y * d * P (redWord t), by
          simpa only [mul_assoc] using sandwich_mem t (redWord t) (c * y * d)⟩ :
          violCorner k Q Λ ν t (redWord t)) ∈ violStandardUpper t (redWord t) by
      have hc := mem_violCorner_iff.1 x.2
      have hx' := H x.1 hx 1 1
      convert hx' using 1
      apply Subtype.ext
      change x.1 = E t * 1 * x.1 * 1 * P (redWord t)
      simp only [mul_one]
      exact ((congrArg (· * P (redWord t)) hc.1).trans hc.2).symm
    intro y hy
    induction hy using TwoSidedIdeal.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, hlt, rfl⟩ := hz
      intro c d
      let g : (C (redWord t))ᵐᵒᵖ := op ⟨P (redWord t) * d * P (redWord t), d, rfl⟩
      have hgen : (⟨E t * c * E v * P (redWord t), by
          simpa only [mul_assoc] using sandwich_mem t (redWord t) (c * E v)⟩ :
          violCorner k Q Λ ν t (redWord t)) ∈ violStandardUpper t (redWord t) :=
        Submodule.subset_span ⟨v, c, hv, hlt, Subtype.ext (by
          change _ = E t * (c * E v) * P (redWord t)
          simp only [mul_assoc])⟩
      have hEv : E v * P (redWord t) = E v := by
        change q (ofKLR k Q Λ ν (KLRAlgebra.e v)) * q (redProj k Q Λ ν (redWord t)) = _
        rw [← map_mul, e_mul_redProj, ite_eq_left hv]
        rfl
      have heq : g • (⟨E t * c * E v * P (redWord t), by
          simpa only [mul_assoc] using sandwich_mem t (redWord t) (c * E v)⟩ :
          violCorner k Q Λ ν t (redWord t)) =
          ⟨E t * c * E v * d * P (redWord t), by
            simpa only [mul_assoc] using sandwich_mem t (redWord t) (c * E v * d)⟩ := by
        apply Subtype.ext
        rw [violCorner_smul_val]
        change E t * c * E v * P (redWord t) * (P (redWord t) * d * P (redWord t)) =
          E t * c * E v * d * P (redWord t)
        rw [mul_assoc (E t * c), hEv, ← mul_assoc, ← mul_assoc, mul_assoc (E t * c), hEv]
      convert Submodule.smul_mem _ g hgen using 1
      exact heq.symm
    | zero =>
      intro c d
      convert zero_mem (violStandardUpper t (redWord t)) using 1
      exact Subtype.ext (by simp)
    | add y₁ y₂ _ _ h₁ h₂ =>
      intro c d
      convert add_mem (h₁ c d) (h₂ c d) using 1
      exact Subtype.ext (by simp only [Submodule.coe_add, mul_add, add_mul])
    | neg y _ h =>
      intro c d
      convert neg_mem (h c d) using 1
      exact Subtype.ext (by simp only [Submodule.coe_neg, mul_neg, neg_mul])
    | left_absorb a' y _ h =>
      intro c d
      convert h (c * a') d using 1
      exact Subtype.ext (by simp only [mul_assoc])
    | right_absorb b' y _ h =>
      intro c d
      convert h c (b' * d) using 1
      exact Subtype.ext (by simp only [mul_assoc])

/-- **Webster, arXiv:1309.3796v2, §6.1, proof of Proposition 6.9 (v3: Proposition 6.10), the
standard module at a rigid cut.** For a loading `t` of red order `L ++ a :: b :: M` whose cut
at `b` is rigid (as at the loading of Figure 5), an element of `e(t) T e_κ` is a relation of
the standard module of Definition 5.1 exactly when it lies in the ideal of retained-higher
loadings that defines the partial standard of Lemma 6.8. -/
theorem mem_violStandardUpper_iff_mem_blockUpperIdeal {t : Seq μ}
    (ht : redWord t = L ++ a :: b :: M) (hrig : IsRigidCut t b)
    (x : violCorner k Q Λ ν t (redWord t)) :
    x ∈ violStandardUpper t (redWord t) ↔
      x.1 ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t) := by
  have hc : E t * x.1 = x.1 := (mem_violCorner_iff.1 x.2).1
  rw [mem_violStandardUpper_iff, ← hc, mul_mem_blockUpperIdeal_iff ht hrig]

end BraidedStendhalAlgebra

end Categorification.Stendhal
