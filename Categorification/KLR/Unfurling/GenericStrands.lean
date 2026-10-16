/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericWeights
import Categorification.KLR.Unfurling.CycFlip

/-!
# Distinct negative generic strand lifts in the full cover

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of the theorem labelled `nondegenerate`, construction of representations and
triviality of a relation. For any sequence and at least as many strand slots as
positions, assign a distinct negative generic slot to every strand. The resulting
weight is multiplicity-free, projects to the original weight, and has no arrows
between its labels in the full `coverDatum`. The datum is not replaced by an
arrow-free restriction. Its polynomials must descend to the ground field: arbitrary
coefficients in `K`, which already contains the negative variables, are insufficient.

The concrete `GenericWeights` multiplicities are `M` on this support, so its
cyclotomic generators coincide with those of `UnfCyc`. The strand hypotheses of
`cycGamma` and `cycFlip` are thus constructed; the evaluation and its comparison
with the diagram basis are separate. Empty sequences and arbitrary colour types
are included, without additional finiteness hypotheses.
-/

noncomputable section
namespace Categorification.KLR.Unfurling.GenericFields

variable (k : Type*) [Field k] {I : Type*} (s b : ℕ)

/-- A negative generic strand label in the full spectral cover. -/
def strandLabel (c : I) (q : Fin s) :
    LabelNeg I (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b)) ⊕
      LabelPos I (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b)) :=
  .inl ⟨c, zm k I (Slots s b) c (.inl q)⟩

theorem strandLabel_injective :
    Function.Injective (fun p : I × Fin s => strandLabel k s b p.1 p.2) := by
  intro p p' he
  have hz := congrArg (fun a => (coverLabel I (K k (I × Slots s b))
    (L k (I × Slots s b) (I × Slots s b)) a).2.1) he
  have hp := (independent_neg k (I × Slots s b) (I × Slots s b)).injective hz
  obtain ⟨hc, hq⟩ := Prod.mk.inj hp
  exact Prod.ext hc (Sum.inl_injective hq)

variable {s} {ν : Multiset I} (i : Seq ν) (hs : ν.card ≤ s)

/-- Assign different negative strand slots to the positions of a sequence. -/
def strandWeight := Finset.univ.val.map (fun q : Fin ν.card =>
  strandLabel k s b (i.lbl q) (Fin.castLE hs q))

@[simp] theorem card_strandWeight : (strandWeight k b i hs).card = ν.card := by
  simp [strandWeight]

theorem strandWeight_nodup : (strandWeight k b i hs).Nodup := by
  apply Multiset.Nodup.map _ Finset.univ.nodup
  intro q q' he
  have hp := strandLabel_injective k s b (a₁ := (i.lbl q, Fin.castLE hs q))
    (a₂ := (i.lbl q', Fin.castLE hs q')) he
  exact Fin.ext (congrArg (fun p => p.2.val) hp)

/-- The sequence in the full cover with the assigned distinct negative labels. -/
def strandSeq : Seq (strandWeight k b i hs) :=
  ⟨fun q => strandLabel k s b (i.lbl (Fin.cast (card_strandWeight k b i hs) q))
    (Fin.castLE hs (Fin.cast (card_strandWeight k b i hs) q)), by
    change Finset.univ.val.map ((fun q : Fin ν.card =>
      strandLabel k s b (i.lbl q) (Fin.castLE hs q)) ∘
        finCongr (card_strandWeight k b i hs)) = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
    rfl⟩

variable (P₀ : I → I → MvPolynomial (Fin 2) (K k (I × Slots s b)))
  (d : I → ℕ) (hdpos : ∀ c, 0 < d c)
  (hd : ∀ c, (d c : L k (I × Slots s b) (I × Slots s b)) ≠ 0)
  (hP : ∀ c c', c ≠ c' → MvPolynomial.map
    (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b))) (P₀ c c') ≠ 0)
  (hhom : ∀ c c', c ≠ c' → ∃ D, (MvPolynomial.map
    (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b)))
      (P₀ c c')).IsWeightedHomogeneous ![d c', d c] D)

theorem strandWeight_map :
    (strandWeight k b i hs).map (coverDatum P₀ d hdpos hd hP hhom).π = ν := by
  rw [strandWeight, Multiset.map_map]
  exact i.2

theorem down_strandSeq :
    down (coverDatum P₀ d hdpos hd hP hhom).π
      (strandWeight_map k b i hs P₀ d hdpos hd hP hhom) (strandSeq k b i hs) = i := by
  apply Subtype.ext
  funext q
  rfl

variable (hground : ∀ c c', c ≠ c' → ∃ p : MvPolynomial (Fin 2) k,
  MvPolynomial.map (algebraMap k (K k (I × Slots s b))) p = P₀ c c')

include hground in
/-- Negative generic strand labels have no arrows between them in the full cover.
The crossing polynomials must descend to the ground field, not merely to `K`. -/
theorem strandLabel_arrows (c c' : I) (q q' : Fin s) :
    (coverDatum P₀ d hdpos hd hP hhom).arrows
      (strandLabel k s b c q) (strandLabel k s b c' q') = 0 := by
  by_cases he : c = c'
  · exact UnfurlingDatum.arrows_of_eq _ _ _ he
  apply UnfurlingDatum.arrows_eq_zero_of_aeval_ne_zero
  obtain ⟨p, hp⟩ := hground c' c (Ne.symm he)
  have hp0 : p ≠ 0 := by
    intro hz
    apply hP c' c (Ne.symm he)
    rw [← hp, hz, map_zero, map_zero]
  rw [coverDatum_pw_coeff_zero, coverDatum_pw_coeff_zero]
  change MvPolynomial.aeval ![zNeg k (I × Slots s b) (I × Slots s b) (c, .inl q),
    zNeg k (I × Slots s b) (I × Slots s b) (c', .inl q')]
      (MvPolynomial.map _ (P₀ c' c)) ≠ 0
  rw [← hp, MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_map_algebraMap]
  exact aeval_ne_zero_of_algebraicIndependent
    (independent_neg k (I × Slots s b) (I × Slots s b))
    (fun e => he (congrArg Prod.fst e)) hp0

include hground in
theorem strandWeight_arrows :
    ∀ a ∈ strandWeight k b i hs, ∀ a' ∈ strandWeight k b i hs,
      (coverDatum P₀ d hdpos hd hP hhom).arrows a a' = 0 := by
  intro a ha a' ha'
  obtain ⟨q, -, rfl⟩ := Multiset.mem_map.mp ha
  obtain ⟨q', -, rfl⟩ := Multiset.mem_map.mp ha'
  exact strandLabel_arrows k b P₀ d hdpos hd hP hhom hground _ _ _ _

/-- The negative cyclotomic multiplicity is `M` at every chosen strand label. -/
theorem strandWeight_level (M : ℕ) (h : I → ℤ) :
    ∀ a ∈ strandWeight k b i hs,
      Sum.elim (vacuumWeightNeg k s b M h) (vacuumWeightPos k s b M h) a = M := by
  intro a ha
  obtain ⟨q, -, rfl⟩ := Multiset.mem_map.mp ha
  exact vacuumWeightNeg_strand k s b M h _ _

/-- Every selected label is a negative strand label; this also identifies its slot. -/
theorem mem_strandWeight {a} : a ∈ strandWeight k b i hs ↔
    ∃ q : Fin ν.card, strandLabel k s b (i.lbl q) (Fin.castLE hs q) = a := by
  simp [strandWeight]

/-- On the selected support the concrete cyclotomic generators are precisely those
with constant level `M`. This applies to every ordering of that support. -/
theorem strandWeight_cycElt (M : ℕ) (h : I → ℤ)
    (Q : _ → _ → MvPolynomial (Fin 2) (L k (I × Slots s b) (I × Slots s b)))
    (t : Seq (strandWeight k b i hs)) :
    KLRAlgebra.cycElt Q (fun a => Polynomial.X ^
      Sum.elim (vacuumWeightNeg k s b M h) (vacuumWeightPos k s b M h) a) t =
        KLRAlgebra.cycElt Q (fun _ => Polynomial.X ^ M) t := by
  unfold KLRAlgebra.cycElt
  split_ifs with ht
  · dsimp only
    rw [strandWeight_level k b i hs M h _ (t.mem ⟨0, ht⟩)]
  · rfl

end Categorification.KLR.Unfurling.GenericFields
