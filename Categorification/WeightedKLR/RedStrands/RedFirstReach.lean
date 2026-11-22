/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedBlackCrossingChain
import Categorification.WeightedKLR.RedStrands.RedFirstCorner
import Categorification.WeightedKLR.RedStrands.TensorHomInduction

set_option backward.isDefEq.respectTransparency false

/-!
# Reaching the red-first idempotent by injective crossings

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, Lemma 5.23,
in the form used in the proof of Theorem 5.27, (3) ⇒ (1). For every red-ordered loading `s`
there is a chain of single red-black crossings `c₁ ⋯ cₙ` from `e(s)` to an idempotent `e(t)`
with `t` red-first, and right multiplication by the product is injective on `T^λ e(s)`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- The image in `T^λ` of the idempotent of a red-ordered loading. -/
abbrev redLoadingIdem {m : ℕ} (Λ : Fin m → I →₀ ℕ) (ν : Multiset I)
    (s : Seq (stendhalWeight m ν)) (hs : IsRedOrdered s) : TensorProductAlgebra k Q Λ ν :=
  TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs)

theorem isIdempotentElem_redLoadingIdem {m : ℕ} (Λ : Fin m → I →₀ ℕ) (ν : Multiset I)
    (s : Seq (stendhalWeight m ν)) (hs : IsRedOrdered s) :
    IsIdempotentElem (redLoadingIdem Q Λ ν s hs) := by
  unfold IsIdempotentElem redLoadingIdem
  rw [← map_mul, StendhalAlgebra.e_mul_e, ite_eq_left rfl]

/-- `s ⟶ t`: an element `c` with `c e(t) = c` such that `x ↦ x c` is injective on
`T^λ e(s)`. -/
def CrossPair {m : ℕ} (Λ : Fin m → I →₀ ℕ) (ν : Multiset I)
    (s t : Seq (stendhalWeight m ν)) : Prop :=
  ∃ (hs : IsRedOrdered s) (ht : IsRedOrdered t) (c : TensorProductAlgebra k Q Λ ν),
    (∀ x, x * redLoadingIdem Q Λ ν s hs = x → x * c = 0 → x = 0) ∧
      c * redLoadingIdem Q Λ ν t ht = c

/-- A chain of crossings from `s` to a red-first loading. -/
def Reach {m : ℕ} (Λ : Fin m → I →₀ ℕ) (ν : Multiset I) (s : Seq (stendhalWeight m ν)) :
    Prop :=
  ∃ t, IsRedOrdered t ∧ IsRedFirst t ∧ Relation.ReflTransGen (CrossPair Q Λ ν) s t

theorem crossPair_cast {m : ℕ} (Λ : Fin m → I →₀ ℕ) {ν ν' : Multiset I} (h : ν = ν')
    {s t : Seq (stendhalWeight m ν)} (hst : CrossPair Q Λ ν s t) :
    CrossPair Q Λ ν' (Seq.cast (congrArg _ h) s) (Seq.cast (congrArg _ h) t) := by
  subst h; exact hst

theorem reach_cast {m : ℕ} (Λ : Fin m → I →₀ ℕ) {ν ν' : Multiset I} (h : ν = ν')
    {s : Seq (stendhalWeight m ν)} (hs : Reach Q Λ ν s) :
    Reach Q Λ ν' (Seq.cast (congrArg _ h) s) := by
  subst h; exact hs

section Transport

variable {C : QuantumGroup.CartanDatum I}

/-- Adding a black strand on the right transports a crossing pair. -/
theorem crossPair_appendBlack (hQ : IsRouquierQ C Q) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (i : I) (ν : Multiset I) {s t : Seq (stendhalWeight ℓ ν)} (hst : CrossPair Q Λ ν s t) :
    CrossPair Q Λ ({i} + ν) (appendBlackLoading i ν s) (appendBlackLoading i ν t) := by
  obtain ⟨hs, ht, c, hinj, hc⟩ := hst
  refine ⟨appendBlackLoading_ordered i ν s hs, appendBlackLoading_ordered i ν t ht,
    appendBlackNU (Q := Q) (Λ := Λ) i ν c, fun x hx h0 => ?_, ?_⟩
  · refine eq_zero_of_mul_map (appendBlackNU (Q := Q) (Λ := Λ) i ν)
      (isIdempotentElem_redLoadingIdem Q Λ ν s hs) c
      (appendBlack_ind_map_injective C hQ (rmulLIdeal_injective hinj)) x ?_ h0
    change x * appendBlack Q Λ i ν (redLoadingIdem Q Λ ν s hs) = x
    rw [appendBlack_mk_e]; exact hx
  · change appendBlack Q Λ i ν c * _ = _
    rw [show redLoadingIdem Q Λ ({i} + ν) (appendBlackLoading i ν t) _ =
      appendBlack Q Λ i ν (redLoadingIdem Q Λ ν t ht) from (appendBlack_mk_e Q Λ i ν t ht).symm,
      ← map_mul, hc]
    rfl

/-- Adding a red strand on the right transports a crossing pair. -/
theorem crossPair_appendRed (hQs : KLRSymm Q) {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (θ : Multiset I) {s t : Seq (stendhalWeight ℓ (θ + 0))}
    (hst : CrossPair Q (Λ ∘ Fin.castSucc) (θ + 0) s t) :
    CrossPair Q Λ (θ + 0) (appendRedLoading s) (appendRedLoading t) := by
  obtain ⟨hs, ht, c, hinj, hc⟩ := hst
  refine ⟨(appendRedLoading_ordered_iff s).2 hs, (appendRedLoading_ordered_iff t).2 ht,
    emptyRedHom Q Λ θ c, fun x hx h0 => ?_, ?_⟩
  · refine eq_zero_of_mul_map (emptyRedHom Q Λ θ)
      (isIdempotentElem_redLoadingIdem Q _ _ s hs) c
      (emptyRed_lIdeal_ind_map_injective Q Λ θ hQs (rmulLIdeal_injective hinj)) x ?_ h0
    rw [emptyRedHom_apply, appendRed_mk_e]; exact hx
  · rw [emptyRedHom_apply, show redLoadingIdem Q Λ (θ + 0) (appendRedLoading t) _ =
      (appendRed Q Λ (θ + 0) (redLoadingIdem Q _ _ t ht)).val from (appendRed_mk_e Q Λ _ t ht).symm]
    change (appendRed Q Λ (θ + 0) c * appendRed Q Λ (θ + 0) _).val = _
    rw [← map_mul, hc]

/-- Adding a red strand on the right transports a crossing pair, at any black weight. -/
theorem crossPair_appendRed' (hQs : KLRSymm Q) {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I) {s t : Seq (stendhalWeight ℓ ν)}
    (hst : CrossPair Q (Λ ∘ Fin.castSucc) ν s t) :
    CrossPair Q Λ ν (appendRedLoading s) (appendRedLoading t) := by
  have key : ∀ s t : Seq (stendhalWeight ℓ (ν + 0)),
      CrossPair Q (Λ ∘ Fin.castSucc) (ν + 0) s t →
        CrossPair Q Λ (ν + 0) (appendRedLoading s) (appendRedLoading t) :=
    fun _ _ => crossPair_appendRed Q hQs Λ ν
  rw [add_zero] at key
  exact key s t hst

end Transport

section RedFirst

open FirstWeight

omit [DecidableEq I] in
theorem card_stendhalWeight_addBlack_reach {ℓ : ℕ} (i : I) (ν : Multiset I) :
    Multiset.card (stendhalWeight ℓ ({i} + ν)) = Multiset.card (stendhalWeight ℓ ν) + 1 := by
  rw [← stendhalWeight_addBlack, Multiset.card_add, Multiset.card_singleton]

omit [DecidableEq I] in
/-- Adding a black strand on the right preserves and reflects red-firstness. -/
theorem isRedFirst_appendBlackLoading_iff {ℓ : ℕ} (i : I) (ν : Multiset I)
    (s : Seq (stendhalWeight ℓ ν)) :
    IsRedFirst (appendBlackLoading i ν s) ↔ IsRedFirst s := by
  have hc := card_stendhalWeight_addBlack_reach (ℓ := ℓ) i ν
  constructor
  · intro h a b ha hb
    exact h ⟨a.val, by omega⟩ ⟨b.val, by omega⟩
      (by rwa [appendBlackLoading_lbl_of_lt i ν s _ a.isLt])
      (by rwa [appendBlackLoading_lbl_of_lt i ν s _ b.isLt])
  · intro h a b ha hb
    rcases (show b.val < Multiset.card (stendhalWeight ℓ ν) ∨
        b.val = Multiset.card (stendhalWeight ℓ ν) by omega) with hb' | hb'
    · rcases (show a.val < Multiset.card (stendhalWeight ℓ ν) ∨
          a.val = Multiset.card (stendhalWeight ℓ ν) by omega) with ha' | ha'
      · exact h ⟨a.val, ha'⟩ ⟨b.val, hb'⟩
          (by rwa [appendBlackLoading_lbl_of_lt i ν s _ ha'] at ha)
          (by rwa [appendBlackLoading_lbl_of_lt i ν s _ hb'] at hb)
      · exact Fin.lt_def.mpr (by omega)
    · rw [appendBlackLoading_lbl_of_eq i ν s b hb'] at hb
      simp at hb

omit [DecidableEq I] in
/-- Without black strands every loading is red-first. -/
theorem isRedFirst_of_card_eq_zero {ℓ : ℕ} {ν : Multiset I} (hν : Multiset.card ν = 0)
    (s : Seq (stendhalWeight ℓ ν)) : IsRedFirst s := by
  intro a b ha _
  obtain ⟨j, hj⟩ : ∃ j, s.lbl a = .inl j := by
    cases h : s.lbl a with
    | inl j => exact ⟨j, rfl⟩
    | inr r => rw [h] at ha; simp at ha
  have hm := s.mem a
  change s.lbl a ∈ _ at hm
  rw [hj, Multiset.card_eq_zero.mp hν] at hm
  simp [stendhalWeight] at hm

omit [DecidableEq I] in
/-- A red-first loading with a black strand ends with a black strand. -/
theorem exists_terminal_inl_of_isRedFirst {ℓ : ℕ} {ν : Multiset I} (hν : 0 < Multiset.card ν)
    (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedFirst s) :
    ∃ j, s.lbl (terminalPos (ν := ν) (ℓ := ℓ) (by omega)) = .inl j := by
  cases h : s.lbl (terminalPos (ν := ν) (ℓ := ℓ) (by omega)) with
  | inl j => exact ⟨j, rfl⟩
  | inr r =>
    exfalso
    obtain ⟨j, hj⟩ := Multiset.card_pos_iff_exists_mem.mp hν
    have hm : (Sum.inl j : I ⊕ Fin ℓ) ∈ stendhalWeight ℓ ν :=
      Multiset.mem_add.mpr (Or.inl (Multiset.mem_map_of_mem _ hj))
    rw [← s.2] at hm
    obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp hm
    have hlt := hs a (terminalPos (ν := ν) (ℓ := ℓ) (by omega))
      (by change (s.1 a).isLeft; rw [ha]; rfl) (by rw [h]; rfl)
    have := a.isLt
    rw [Fin.lt_def] at hlt
    change _ - 1 < _ at hlt
    omega

omit [DecidableEq I] in
/-- The black colour of a labelled position lies in the black weight. -/
theorem mem_of_lbl_eq_inl {ℓ : ℕ} {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν))
    (a : Fin (Multiset.card (stendhalWeight ℓ ν))) {j : I} (h : s.lbl a = .inl j) :
    j ∈ ν := by
  have hm := s.mem a
  change s.lbl a ∈ _ at hm
  rw [h] at hm
  simpa [stendhalWeight] using hm

open Classical in
theorem redLoadingIdem_mul_redFirstIdem {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
    (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t) (htf : IsRedFirst t) :
    redLoadingIdem Q Λ ν t ht * redFirstIdem Q Λ ν = redLoadingIdem Q Λ ν t ht := by
  unfold redLoadingIdem redFirstIdem redFirstStendhalIdem
  rw [← map_mul, Finset.mul_sum, Finset.sum_eq_single_of_mem
    (⟨t, ht, htf⟩ : RedFirstLoading (ℓ := ℓ) ν) (Finset.mem_univ _)]
  · rw [StendhalAlgebra.e_mul_e, ite_eq_left rfl]
  · intro u _ hne
    rw [StendhalAlgebra.e_mul_e,
      ite_eq_right_iff.mpr (fun h => absurd (Subtype.ext h.symm) hne)]

end RedFirst

/-- The base crossing: moving the last red strand left past the last black strand. -/
def BaseCrossing : Prop :=
  ∀ {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (β : Multiset I)
    (u : Seq (stendhalWeight ℓ β)),
    IsRedOrdered u → CrossPair Q Λ ({i} + β) (appendRedLoading (appendBlackLoading i β u))
      (appendBlackLoading i β (appendRedLoading u))

section Reach

open FirstWeight

variable {Q} {C : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ C Q) (hQs : KLRSymm Q)
  (hbase : BaseCrossing Q)

include hQ hbase in
/-- After adding a red strand on the right of a red-first loading, a chain of crossings reaches a
red-first loading. -/
theorem reach_appendRed_of_isRedFirst : ∀ (n : ℕ) {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I), Multiset.card ν = n → ∀ t : Seq (stendhalWeight ℓ ν),
      IsRedOrdered t → IsRedFirst t → Reach Q Λ ν (appendRedLoading t)
  | 0, ℓ, Λ, ν, hn, t, ht, _ =>
    ⟨_, (appendRedLoading_ordered_iff t).2 ht, isRedFirst_of_card_eq_zero hn _,
      Relation.ReflTransGen.refl⟩
  | n + 1, ℓ, Λ, ν, hn, t, ht, htf => by
    obtain ⟨j, hj⟩ := exists_terminal_inl_of_isRedFirst (by omega) t htf
    obtain ⟨β, rfl⟩ : ∃ β, ν = {j} + β :=
      ⟨_, by rw [Multiset.singleton_add, Multiset.cons_erase (mem_of_lbl_eq_inl t _ hj)]⟩
    obtain ⟨t₁, ht₁, rfl⟩ := exists_appendBlack_terminal t hj ht
    have hrf := (isRedFirst_appendBlackLoading_iff j β t₁).1 htf
    obtain ⟨r, hr, hrf', hch⟩ := reach_appendRed_of_isRedFirst n Λ β
      (by simp at hn; omega) t₁ ht₁ hrf
    refine ⟨appendBlackLoading j β r, appendBlackLoading_ordered j β r hr,
      (isRedFirst_appendBlackLoading_iff j β r).2 hrf', Relation.ReflTransGen.head
        (hbase Λ j β t₁ ht₁) (hch.lift _ fun a b h => crossPair_appendBlack Q hQ Λ j β h)⟩

include hQ hQs hbase in
/-- **Every red-ordered loading reaches a red-first loading** by a chain of crossings. -/
theorem reach_of_isRedOrdered : ∀ (n : ℕ) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I),
    ℓ + Multiset.card ν = n → ∀ s : Seq (stendhalWeight ℓ ν), IsRedOrdered s →
      Reach Q Λ ν s
  | 0, ℓ, Λ, ν, hn, s, hs =>
    ⟨s, hs, isRedFirst_of_card_eq_zero (by omega) s, Relation.ReflTransGen.refl⟩
  | n + 1, ℓ, Λ, ν, hn, s, hs => by
    cases h : s.lbl (terminalPos (ν := ν) (ℓ := ℓ) (by omega)) with
    | inl j =>
      obtain ⟨β, rfl⟩ : ∃ β, ν = {j} + β :=
        ⟨_, by rw [Multiset.singleton_add, Multiset.cons_erase (mem_of_lbl_eq_inl s _ h)]⟩
      obtain ⟨u, hu, rfl⟩ := exists_appendBlack_terminal s h hs
      obtain ⟨r, hr, hrf, hch⟩ := reach_of_isRedOrdered n Λ β
        (by simp at hn; omega) u hu
      exact ⟨appendBlackLoading j β r, appendBlackLoading_ordered j β r hr,
        (isRedFirst_appendBlackLoading_iff j β r).2 hrf,
        hch.lift _ fun a b h => crossPair_appendBlack Q hQ Λ j β h⟩
    | inr r =>
      cases ℓ with
      | zero => exact r.elim0
      | succ ℓ =>
        have hpos :
            terminalPos (ν := ν) (ℓ := ℓ + 1) (by omega) = lastRedPosition ℓ ν := by
          apply Fin.ext
          change Multiset.card (stendhalWeight (ℓ + 1) ν) - 1 = ν.card + ℓ
          rw [cardinal_weight]; omega
        have hlast := terminal_red_last s hs r (hpos ▸ h)
        obtain ⟨⟨u, hu⟩, hus⟩ :=
          (appendRedOrderedEquiv (ℓ := ℓ) (ν := ν)).surjective ⟨s, hs, hlast⟩
        obtain rfl : appendRedLoading u = s := congrArg Subtype.val hus
        obtain ⟨r₁, hr₁, hrf₁, hch₁⟩ := reach_of_isRedOrdered n (Λ ∘ Fin.castSucc) ν
          (by omega) u hu
        obtain ⟨r₂, hr₂, hrf₂, hch₂⟩ :=
          reach_appendRed_of_isRedFirst hQ hbase _ Λ ν rfl r₁ hr₁ hrf₁
        exact ⟨r₂, hr₂, hrf₂,
          (hch₁.lift _ fun a b h => crossPair_appendRed' Q hQs Λ ν h).trans hch₂⟩

include hQ hQs hbase in
/-- **Lemma 5.23 for the red-first idempotent** (Webster, arXiv:1309.3796v2, Lemma 5.23, as used
in the proof of Theorem 5.27): if `x e(s) = x` and `x ≠ 0` for a red-ordered `s`, there is `c`
with `c e⁰ = c` and `x c ≠ 0`. -/
theorem exists_mul_redFirstIdem_ne_zero {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
    (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) (x : TensorProductAlgebra k Q Λ ν)
    (hx : x * redLoadingIdem Q Λ ν s hs = x) (h0 : x ≠ 0) :
    ∃ c, c * redFirstIdem Q Λ ν = c ∧ x * c ≠ 0 := by
  obtain ⟨t, ht, htf, hch⟩ := reach_of_isRedOrdered hQ hQs hbase _ Λ ν rfl s hs
  induction hch using Relation.ReflTransGen.head_induction_on generalizing x with
  | refl =>
    refine ⟨redLoadingIdem Q Λ ν t ht, redLoadingIdem_mul_redFirstIdem Q Λ ν t ht htf, ?_⟩
    rwa [hx]
  | head hst _ ih =>
    obtain ⟨hs₁, hs', c₁, hinj, hc⟩ := hst
    have hy : x * c₁ ≠ 0 := fun h => h0 (hinj x hx h)
    obtain ⟨c₂, hc₂, hxc⟩ := ih hs' (x * c₁) (by rw [mul_assoc, hc]) hy
    exact ⟨c₁ * c₂, by rw [mul_assoc, hc₂], by rwa [← mul_assoc]⟩

end Reach

end Categorification.Stendhal
