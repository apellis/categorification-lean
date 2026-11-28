/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedFirstBaseCrossing
import Categorification.WeightedKLR.RedStrands.RedBlackCrossingFrame
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastBlackLinear

/-!
# Right multiplication by a red–black crossing in a two-red coefficient

Webster, arXiv:1309.3796v2, Lemma 5.23, applied to the internal coefficient in
Lemma 6.8. The two-red crossing moves the black strand from left of the second red
at the top to right of it at the bottom. The base crossing is at the right edge,
and right black strands preserve its injectivity.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA InductionAlong QuantumGroup KL3.Diagram
open scoped TensorProduct

variable {I k : Type} [decI : DecidableEq I] [Field k]
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k}

local notation "QL" => Q
local notation "Si" i:max => (Singleton.singleton i : Multiset I)

section Last

variable (Λ : Fin 2 → I →₀ ℕ) (i : I) (θ : Multiset I)
  (u : Seq (stendhalWeight 1 (θ + 0)))

local notation "ν" => (Si i + (θ + 0))
local notation "s" => appendRedLoading (appendBlackLoading i (θ + 0) u)
local notation "t" => appendBlackLoading i (θ + 0) (appendRedLoading u)
local notation "a" => Multiset.map (addRedColor 1) (stendhalWeight 1 θ)
local notation "b" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last 1))
  (stendhalWeight 1 (0 : Multiset I))
local notation "j" => (Sum.inl i : I ⊕ Fin 2)
local notation "w" => firstInd_klrWeight (ℓ := 1) i θ 0
local notation "s'" => Seq.cast (Eq.symm w) s
local notation "t'" => Seq.cast (Eq.symm w) t

omit [DecidableEq I] in
private theorem firstFactorCrossingIndex : (a).card = (stendhalWeight 1 (θ + 0)).card := by
  simp [stendhalWeight]

omit [DecidableEq I] in
private theorem firstFactorSwap : sadj (a + b + {j}).card (a).card • s' = t' := by
  have hb : (b).card = 1 := by simp [stendhalWeight]
  rw [← quadPerm_firstQuad_eq_sadj a b j hb]
  have h := congrArg (Seq.cast (Eq.symm w)) (cast_quadPerm_smul_base i θ u)
  rwa [Seq.cast_symm_cast] at h

end Last

/-- Right multiplication by the oriented crossing at the last two positions is injective on
its source loading projective for Rouquier parameters. -/
theorem eq_zero_of_mul_secondRedCrossing_at_right
    (hR : IsRouquierQ C QL) (hQs : KLRSymm QL)
    (Λ : Fin 2 → I →₀ ℕ) (i : I) (θ : Multiset I)
    (u : Seq (stendhalWeight 1 (θ + 0))) (hu : IsRedOrdered u)
    (x : TensorProductAlgebra k QL Λ (Si i + (θ + 0)))
    (hx : x * tensorOfKLR QL Λ _ (e (appendRedLoading (appendBlackLoading i (θ + 0) u))) = x)
    (h0 : x * tensorOfKLR QL Λ _ (ψ (stendhalWeight 1 (θ + 0)).card *
      e (appendBlackLoading i (θ + 0) (appendRedLoading u))) = 0) : x = 0 := by
  let d : DecidableEq I := fun a b => Classical.propDecidable (a = b)
  have hd : decI = d := Subsingleton.elim _ _
  subst decI
  let _ : DecidableEq I := d
  let A := Multiset.map (addRedColor 1) (stendhalWeight 1 θ)
  let B := Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last 1))
    (stendhalWeight 1 (0 : Multiset I))
  let j : I ⊕ Fin 2 := .inl i
  let G := firstG (stendhalQ QL Λ) A B j
  let s := appendRedLoading (appendBlackLoading i (θ + 0) u)
  let t := appendBlackLoading i (θ + 0) (appendRedLoading u)
  have hs : IsRedOrdered s := (appendRedLoading_ordered_iff _).2
    (appendBlackLoading_ordered i (θ + 0) u hu)
  have hsrc : redCrossIdem QL Λ i θ u hu = tensorOfKLR QL Λ _ (e s) := by
    rw [redCrossIdem_eq]
    exact (tensorOfKLR_e_of_ordered _ _ hs).symm
  have hb : B.card = 1 := by simp [B, stendhalWeight]
  have hframe := e_mul_firstG_eq_ψ_mul_e_of_singleton (stendhalQ QL Λ) A B j hb
    (Seq.cast (firstInd_klrWeight (ℓ := 1) i θ 0).symm s)
    (Seq.cast (firstInd_klrWeight (ℓ := 1) i θ 0).symm t)
    (cast_blackRedLoading_mem_botSet i θ u (firstInd_klrWeight (ℓ := 1) i θ 0) hb
      (by simp [stendhalWeight]))
    (cast_redBlackLoading_mem_concatSet i θ u (firstInd_klrWeight (ℓ := 1) i θ 0)) (firstFactorSwap i θ u)
  have hclip : redCrossIdem QL Λ i θ u hu * firstIndAffine QL Λ i θ 0 G =
      tensorOfKLR QL Λ _ (ψ (stendhalWeight 1 (θ + 0)).card * e t) := by
    have he : redCrossIdem QL Λ i θ u hu = redLoadingIdem QL Λ _ s hs :=
      redCrossIdem_eq QL Λ i θ u hu
    rw [he, ← firstIndAffine_e_cast QL Λ i θ 0 s hs, ← map_mul]
    change firstIndAffine QL Λ i θ 0 (_ * firstG _ A B j) = _
    rw [hframe, firstIndAffine_apply, map_mul, castKLR_ψ, castKLR_e, Seq.cast_cast_symm,
      show A.card = (stendhalWeight 1 (θ + 0)).card from firstFactorCrossingIndex (I := I) θ]
  have hcross := IsRedBlackCrossing.crossing (Q := QL) Λ i θ u hu
  refine (IsRedBlackCrossing.eq_zero hR hQs hcross).2 x (by rw [hsrc]; exact hx) ?_
  change x * firstIndAffine QL Λ i θ 0 G = 0
  calc
    x * firstIndAffine QL Λ i θ 0 G =
        x * (redCrossIdem QL Λ i θ u hu * firstIndAffine QL Λ i θ 0 G) := by
      rw [← mul_assoc, hsrc, hx]
    _ = 0 := by rw [hclip]; exact h0

section Suffix

variable {ℓ : ℕ} (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

private theorem appendBlack_tensorOfKLR_crossing (j : I) (ν : Multiset I)
    (a : ℕ) (ha : a + 1 < (stendhalWeight (ℓ + 1) ν).card) (t : Seq (stendhalWeight (ℓ + 1) ν)) :
    appendBlack Q Λ j ν (tensorOfKLR Q Λ ν (ψ a * e t)) =
      tensorOfKLR Q Λ (Si j + ν) (ψ a * e (appendBlackLoading j ν t)) := by
  have h := appendBlack_tensorOfKLR_castKLR Q Λ j ν rfl
    (stendhalWeight_addBlack j ν) (ψ a * e t)
  rwa [castKLR_rfl, cast_appendR_ψ_mul_e Q Λ j ν a ha t] at h

end Suffix

/-- Right black strand addition preserves injectivity of a specified crossing on its loading
projective. The generator keeps its original index and gains the new terminal black colour. -/
theorem eq_zero_of_mul_crossing_appendBlack {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (hR : IsRouquierQ C Q)
    (Λ : Fin (ℓ + 1) → I →₀ ℕ) (j : I) (ν : Multiset I) (a : ℕ)
    (ha : a + 1 < (stendhalWeight (ℓ + 1) ν).card) (s t : Seq (stendhalWeight (ℓ + 1) ν))
    (hs : IsRedOrdered s)
    (hinj : ∀ x : TensorProductAlgebra k Q Λ ν,
      x * tensorOfKLR Q Λ ν (e s) = x → x * tensorOfKLR Q Λ ν (ψ a * e t) = 0 → x = 0)
    (x : TensorProductAlgebra k Q Λ (Si j + ν))
    (hx : x * tensorOfKLR Q Λ _ (e (appendBlackLoading j ν s)) = x)
    (h0 : x * tensorOfKLR Q Λ _ (ψ a * e (appendBlackLoading j ν t)) = 0) : x = 0 := by
  let f := tensorOfKLR Q Λ ν (e s)
  let c := tensorOfKLR Q Λ ν (ψ a * e t)
  have hsource : f = redLoadingIdem Q Λ ν s hs :=
    tensorOfKLR_e_of_ordered (Q := Q) (Λ := Λ) ν s hs
  have hf : IsIdempotentElem f := hsource.symm ▸ isIdempotentElem_redLoadingIdem Q Λ ν s hs
  have hmul : Function.Injective (rmulLIdeal f c) := rmulLIdeal_injective hinj
  have hind : Function.Injective (Ind.map (φ := appendBlackNU (Q := Q) (Λ := Λ) j ν)
      (rmulLIdeal f c)) :=
    appendBlack_ind_map_injective (Q := Q) (Λ := Λ) (i := j) (ν := ν) C hR hmul
  refine eq_zero_of_mul_map (appendBlackNU (Q := Q) (Λ := Λ) j ν) hf c hind x ?_ ?_
  · change x * appendBlack Q Λ j ν f = x
    rw [hsource, appendBlack_mk_e,
      ← tensorOfKLR_e_of_ordered (Q := Q) (Λ := Λ) (Si j + ν) (appendBlackLoading j ν s)
        (appendBlackLoading_ordered j ν s hs)]
    exact hx
  · change x * appendBlack Q Λ j ν (tensorOfKLR Q Λ ν (ψ a * e t)) = 0
    rw [appendBlack_tensorOfKLR_crossing Q Λ j ν a ha t]
    exact h0

/-- In a two-red coefficient, the second red crossing at the right edge stays injective after
any sequence of right black strand additions and identification of equal black weights. -/
inductive IsSecondRedCrossing : (ν : Multiset I) → ℕ →
    Seq (stendhalWeight 2 ν) → Seq (stendhalWeight 2 ν) → Prop
  | atRight (i : I) (θ : Multiset I) (u : Seq (stendhalWeight 1 (θ + 0)))
      (hu : IsRedOrdered u) :
      IsSecondRedCrossing (Si i + (θ + 0)) (stendhalWeight 1 (θ + 0)).card
        (appendRedLoading (appendBlackLoading i (θ + 0) u))
        (appendBlackLoading i (θ + 0) (appendRedLoading u))
  | appendBlack {ν : Multiset I} {a : ℕ} {s t : Seq (stendhalWeight 2 ν)} (j : I) :
      IsSecondRedCrossing ν a s t → IsSecondRedCrossing (Si j + ν) a
        (appendBlackLoading j ν s) (appendBlackLoading j ν t)
  | cast {ν ν' : Multiset I} {a : ℕ} {s t : Seq (stendhalWeight 2 ν)} (h : ν = ν') :
      IsSecondRedCrossing ν a s t → IsSecondRedCrossing ν' a
        (Seq.cast (congrArg (stendhalWeight 2) h) s) (Seq.cast (congrArg (stendhalWeight 2) h) t)

/-- Right multiplication by the specified oriented crossing is injective on the source loading
projective for Rouquier parameters. -/
theorem IsSecondRedCrossing.eq_zero_of_mul
    (hR : IsRouquierQ C QL) (hQs : KLRSymm QL) (Λ : Fin 2 → I →₀ ℕ)
    {ν : Multiset I} {a : ℕ} {s t : Seq (stendhalWeight 2 ν)} (h : IsSecondRedCrossing ν a s t) :
    IsRedOrdered s ∧ a + 1 < (stendhalWeight 2 ν).card ∧
      ∀ x : TensorProductAlgebra k QL Λ ν,
        x * tensorOfKLR QL Λ ν (e s) = x →
        x * tensorOfKLR QL Λ ν (ψ a * e t) = 0 → x = 0 := by
  induction h with
  | atRight i θ u hu =>
    refine ⟨(appendRedLoading_ordered_iff _).2 (appendBlackLoading_ordered i _ u hu), ?_,
      eq_zero_of_mul_secondRedCrossing_at_right hR hQs Λ i θ u hu⟩
    simp [stendhalWeight]
  | @appendBlack ν a s t j h ih =>
    refine ⟨appendBlackLoading_ordered j ν s ih.1, ?_,
      eq_zero_of_mul_crossing_appendBlack QL hR Λ j ν a ih.2.1 s t ih.1 ih.2.2⟩
    rw [← stendhalWeight_addBlack, Multiset.card_add, Multiset.card_singleton]
    omega
  | cast h _ ih =>
    subst h
    exact ih

section Recognition

open FirstWeight

private theorem cast_sadj_smul {J : Type*} {m n : Multiset J} (h : m = n)
    (a : ℕ) (s : Seq m) :
    Seq.cast h (sadj m.card a • s) = sadj n.card a • Seq.cast h s := by
  subst h
  rfl

omit [DecidableEq I] in
private theorem sadj_appendBlackLoading (j : I) (ν : Multiset I) (a : ℕ)
    (ha : a + 1 < (stendhalWeight 2 ν).card) (s : Seq (stendhalWeight 2 ν)) :
    sadj (stendhalWeight 2 (Si j + ν)).card a • appendBlackLoading j ν s =
      appendBlackLoading j ν (sadj (stendhalWeight 2 ν).card a • s) := by
  unfold appendBlackLoading
  rw [← cast_sadj_smul, Seq.sadj_smul_append_left ha]

omit [DecidableEq I] in
private theorem secondRedCrossing_atRight (i : I) (β : Multiset I)
    (s : Seq (stendhalWeight 1 β)) (hs : IsRedOrdered s) :
    IsSecondRedCrossing (Si i + β) (stendhalWeight 1 β).card
      (appendRedLoading (appendBlackLoading i β s))
      (appendBlackLoading i β (appendRedLoading s)) := by
  have key (β' : Multiset I) (h : β' = β + 0) (s' : Seq (stendhalWeight 1 β'))
      (hs' : IsRedOrdered s') :
      IsSecondRedCrossing (Si i + β') (stendhalWeight 1 β').card
        (appendRedLoading (appendBlackLoading i β' s'))
        (appendBlackLoading i β' (appendRedLoading s')) := by
    subst β'
    exact .atRight i β s' hs'
  exact key β (add_zero β).symm s hs

/-- An adjacent black strand and the second red strand in an ordered two-red loading give the
oriented elementary crossing of Lemma 5.23. Its bottom loading is the adjacent swap. -/
theorem isSecondRedCrossing_of_labels {ν : Multiset I} {a : ℕ}
    (s : Seq (stendhalWeight 2 ν)) (hs : IsRedOrdered s) (i : I)
    (ha : a + 1 < (stendhalWeight 2 ν).card)
    (hb : s.lbl ⟨a, by omega⟩ = .inl i)
    (hr : s.lbl ⟨a + 1, ha⟩ = .inr (1 : Fin 2)) :
    IsSecondRedCrossing ν a s (sadj (stendhalWeight 2 ν).card a • s) := by
  generalize hν : ν.card = n
  induction n using Nat.strong_induction_on generalizing ν with
  | _ n ih =>
    let q := terminalPos (ν := ν) (ℓ := 2) (by omega)
    have hq : q.val = (stendhalWeight 2 ν).card - 1 := rfl
    have hcard₂ := cardinal_weight (ℓ := 2) (ν := ν)
    by_cases hlast : a + 1 = q.val
    · have hred : HasLastRed s := by
        change s.lbl (lastRedPosition 1 ν) = .inr (Fin.last 1)
        have he : lastRedPosition 1 ν = (⟨a + 1, ha⟩ : Fin (stendhalWeight 2 ν).card) := by
          apply Fin.ext
          change ν.card + 1 = a + 1
          omega
        rw [he]
        exact hr
      obtain ⟨⟨u, hu⟩, he⟩ := (appendRedOrderedEquiv (ℓ := 1) (ν := ν)).surjective ⟨s, hs, hred⟩
      obtain rfl : appendRedLoading u = s := congrArg Subtype.val he
      have hcard₁ := cardinal_weight (ℓ := 1) (ν := ν)
      have hl : a < (stendhalWeight 1 ν).card := by omega
      have hpos : terminalPos (ℓ := 1) (ν := ν) (by omega) =
          (⟨a, hl⟩ : Fin (stendhalWeight 1 ν).card) := by
        apply Fin.ext
        change (stendhalWeight 1 ν).card - 1 = a
        omega
      rw [appendRedLoading_lbl_of_lt u _ hl] at hb
      have hblack : u.lbl (terminalPos (ℓ := 1) (ν := ν) (by omega)) = .inl i := by
        rw [hpos]
        cases h : u.lbl ⟨a, hl⟩ with
        | inl j => simpa [h, addRedColor] using hb
        | inr r => simp [h, addRedColor] at hb
      obtain ⟨β, rfl⟩ := exists_eq_singleton_add_of_mem (mem_of_lbl_eq_inl u _ hblack)
      obtain ⟨v, hv, rfl⟩ := exists_appendBlack_terminal u hblack hu
      have ha' : a = (stendhalWeight 1 β).card := by
        have h := cardinal_weight (ℓ := 1) (ν := β)
        have hsum : (Si i + β).card = β.card + 1 := by simp
        omega
      subst a
      change IsSecondRedCrossing _ _ (blackRedLoading i β v)
        (sadj (stendhalWeight 2 (Si i + β)).card _ • blackRedLoading i β v)
      rw [swap_blackRedLoading]
      exact secondRedCrossing_atRight i β v hv
    · cases hqcolour : s.lbl q with
      | inr r =>
        have he : q = lastRedPosition 1 ν := by
          apply Fin.ext
          change q.val = ν.card + 1
          omega
        have ht := terminal_red_last s hs r (he ▸ hqcolour)
        change s.lbl (lastRedPosition 1 ν) = .inr (Fin.last 1) at ht
        rw [← he] at ht
        have heq := lbl_eq_inr_unique hr ht
        exact (hlast (congrArg Fin.val heq)).elim
      | inl j =>
        obtain ⟨β, rfl⟩ := exists_eq_singleton_add_of_mem (mem_of_lbl_eq_inl s q hqcolour)
        obtain ⟨u, hu, rfl⟩ := exists_appendBlack_terminal s hqcolour hs
        have ha' : a + 1 < (stendhalWeight 2 β).card := by
          have h := cardinal_weight (ℓ := 2) (ν := β)
          have hsum : (Si j + β).card = β.card + 1 := by simp
          omega
        have hlt : a < (stendhalWeight 2 β).card := by omega
        have hb' : u.lbl ⟨a, by omega⟩ = .inl i :=
          (appendBlackLoading_lbl_of_lt j β u ⟨a, by omega⟩ hlt).symm.trans hb
        have hr' : u.lbl ⟨a + 1, ha'⟩ = .inr (1 : Fin 2) :=
          (appendBlackLoading_lbl_of_lt j β u ⟨a + 1, ha⟩ ha').symm.trans hr
        rw [sadj_appendBlackLoading j β a ha']
        have hdec : β.card < n := by
          rw [← hν]
          simp
        exact .appendBlack j (ih β.card hdec (ν := β) u hu ha' hb' hr' rfl)

end Recognition

end Categorification.Stendhal
