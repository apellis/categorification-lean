/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalGrading
import Categorification.WeightedKLR.RedStrands.EmptyTensor
import Categorification.WeightedKLR.RedStrands.StendhalBasis
import Categorification.TypeA.DoubleCoset
import Categorification.KLR.Reindex
import Categorification.KLR.CyclotomicEF
import Categorification.KLR.ConcatAssoc
import Mathlib.RingTheory.Idempotents

/-!
# The corner for a terminal red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.3, Proposition 4.18, p. 36. The idempotent `e_ℓ` is the sum over the
red-ordered loadings with the last red strand at the rightmost position.
Appending the final red strand induces a surjection onto this corner in
every black weight. It is an equivalence for the zero black weight and,
when appending the first red strand, for every black weight. The image of the
old violating ideal equals the part of the new violating ideal in this corner.
Thus injectivity before quotienting suffices for injectivity after quotienting.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR

variable {I : Type*} {ℓ : ℕ} {ν : Multiset I}

/-- The rightmost position of a loading with at least one red strand. -/
def lastRedPosition (ℓ : ℕ) (ν : Multiset I) :
    Fin (Multiset.card (stendhalWeight (ℓ + 1) ν)) :=
  ⟨ν.card + ℓ, by simp [stendhalWeight]⟩

/-- The final strand of the loading is the red strand with the greatest label. -/
def HasLastRed (s : Seq (stendhalWeight (ℓ + 1) ν)) : Prop :=
  s.lbl (lastRedPosition ℓ ν) = .inr (Fin.last ℓ)

section Idempotent

variable [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

local notation "μ" => stendhalWeight (ℓ + 1) ν
local notation "Ordered" => { s : Seq μ // IsRedOrdered s }

local instance : Fintype Ordered := Fintype.ofFinite _

private def orderedIdem (s : Ordered) : StendhalAlgebra k Q Λ ν :=
  StendhalAlgebra.e s.1 s.2

private theorem orthogonal_orderedIdem : OrthogonalIdempotents (orderedIdem Q Λ ν) := by
  classical
  rw [OrthogonalIdempotents.iff_mul_eq]
  intro s t
  by_cases h : s = t
  · subst t
    simp only [↓reduceIte]
    apply Subtype.ext
    change (StendhalAlgebraAllOrders.e (Λ := Λ) s.1 :
      StendhalAlgebraAllOrders k Q Λ ν) * StendhalAlgebraAllOrders.e s.1 =
      StendhalAlgebraAllOrders.e s.1
    simpa using (StendhalAlgebraAllOrders.e_mul_e (k := k) (Q := Q) (Λ := Λ) s.1 s.1)
  · have h' : s.1 ≠ t.1 := fun h' => h (Subtype.ext h')
    simp only [h, ↓reduceIte]
    apply Subtype.ext
    change (StendhalAlgebraAllOrders.e (Λ := Λ) s.1 :
      StendhalAlgebraAllOrders k Q Λ ν) * StendhalAlgebraAllOrders.e t.1 = 0
    simpa [h'] using (StendhalAlgebraAllOrders.e_mul_e (k := k) (Q := Q) (Λ := Λ) s.1 t.1)

/-- The sum of the loading idempotents with the last red strand at the far right in `T̃^λ`. -/
def StendhalAlgebra.lastRedIdem : StendhalAlgebra k Q Λ ν :=
  open Classical in
  ∑ s ∈ Finset.univ.filter (fun s : Ordered => HasLastRed s.1), orderedIdem Q Λ ν s

theorem StendhalAlgebra.isIdempotentElem_lastRedIdem :
    IsIdempotentElem (StendhalAlgebra.lastRedIdem Q Λ ν) :=
  (orthogonal_orderedIdem Q Λ ν).isIdempotentElem_sum

open Classical in
theorem StendhalAlgebra.lastRedIdem_mul_e (s : Seq μ) (hs : IsRedOrdered s) :
    StendhalAlgebra.lastRedIdem Q Λ ν * StendhalAlgebra.e (Q := Q) (Λ := Λ) s hs =
      if HasLastRed s then StendhalAlgebra.e s hs else 0 := by
  change StendhalAlgebra.lastRedIdem Q Λ ν * orderedIdem Q Λ ν ⟨s, hs⟩ = _
  rw [StendhalAlgebra.lastRedIdem, Finset.sum_mul]
  simp_rw [(orthogonal_orderedIdem Q Λ ν).mul_eq]
  rw [Finset.sum_ite_eq']
  simp [orderedIdem]

open Classical in
theorem StendhalAlgebra.e_mul_lastRedIdem (s : Seq μ) (hs : IsRedOrdered s) :
    StendhalAlgebra.e (Q := Q) (Λ := Λ) s hs * StendhalAlgebra.lastRedIdem Q Λ ν =
      if HasLastRed s then StendhalAlgebra.e s hs else 0 := by
  change orderedIdem Q Λ ν ⟨s, hs⟩ * StendhalAlgebra.lastRedIdem Q Λ ν = _
  rw [StendhalAlgebra.lastRedIdem, Finset.mul_sum]
  simp_rw [(orthogonal_orderedIdem Q Λ ν).mul_eq]
  rw [Finset.sum_ite_eq]
  simp [orderedIdem]

/-- Webster's idempotent `e_ℓ` in the violating quotient of Proposition 4.18. -/
def TensorProductAlgebra.lastRedIdem : TensorProductAlgebra k Q Λ ν :=
  TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.lastRedIdem Q Λ ν)

theorem TensorProductAlgebra.isIdempotentElem_lastRedIdem :
    IsIdempotentElem (TensorProductAlgebra.lastRedIdem Q Λ ν) := by
  rw [TensorProductAlgebra.lastRedIdem, IsIdempotentElem, ← map_mul,
    (StendhalAlgebra.isIdempotentElem_lastRedIdem Q Λ ν).eq]

/-- The terminal red idempotent is homogeneous of degree zero. -/
theorem TensorProductAlgebra.lastRedIdem_mem_grade (G : KLR.GradingDatum (stendhalQ Q Λ)) :
    TensorProductAlgebra.lastRedIdem Q Λ ν ∈ tensorProductGrade G ν 0 := by
  unfold TensorProductAlgebra.lastRedIdem StendhalAlgebra.lastRedIdem
  rw [map_sum]
  exact Submodule.sum_mem _ fun s _ => mk_e_mem_tensorProductGrade G ν s.1 s.2

/-- The corner `e_ℓ T^λ e_ℓ` in the fixed black weight. -/
abbrev TensorProductAlgebra.lastRedCorner : Type _ :=
  (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν).Corner

end Idempotent

section Loadings

/-- Embed the old labels into the labels after a new terminal red strand is added. -/
abbrev addRedColor (ℓ : ℕ) : I ⊕ Fin ℓ → I ⊕ Fin (ℓ + 1) :=
  Sum.map id Fin.castSucc

theorem addRedColor_injective (ℓ : ℕ) : Function.Injective (addRedColor (I := I) ℓ) :=
  Sum.map_injective.mpr ⟨fun _ _ h => h, Fin.castSucc_injective ℓ⟩

local notation "ν₀" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ ν)
local notation "νᵣ" => ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ + 1)))

private theorem stendhalWeight_addRed : ν₀ + νᵣ = stendhalWeight (ℓ + 1) ν := by
  simp only [stendhalWeight, Multiset.map_add, Multiset.map_map, Function.comp_def,
    addRedColor, Sum.map_inl, Sum.map_inr, id_eq]
  rw [Fin.univ_castSuccEmb ℓ, Finset.cons_val, Multiset.map_cons, Finset.map_val, Multiset.map_map]
  rw [add_assoc, add_comm _ νᵣ]
  rfl

private def singletonRedSeq (ℓ : ℕ) :
    Seq ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ + 1))) :=
  ⟨fun _ => .inr (Fin.last ℓ), by simp⟩

private theorem singletonRedSeq_lbl (a : Fin (Multiset.card νᵣ)) :
    (singletonRedSeq (I := I) ℓ).lbl a = .inr (Fin.last ℓ) :=
  Multiset.mem_singleton.mp (Seq.mem _ a)

/-- Append the new red strand after all existing strands. -/
def appendRedLoading (s : Seq (stendhalWeight ℓ ν)) : Seq (stendhalWeight (ℓ + 1) ν) :=
  Seq.cast stendhalWeight_addRed ((Seq.map (addRedColor ℓ) s).append (singletonRedSeq ℓ))

/-- The position of an old strand after appending the final red strand. -/
def appendRedPosition (a : Fin (Multiset.card (stendhalWeight ℓ ν))) :
    Fin (Multiset.card (stendhalWeight (ℓ + 1) ν)) :=
  Fin.cast (congrArg Multiset.card stendhalWeight_addRed)
    (Seq.posL νᵣ (Fin.cast (Multiset.card_map (addRedColor ℓ) (stendhalWeight ℓ ν)).symm a))

@[simp] theorem appendRedPosition_val (a : Fin (Multiset.card (stendhalWeight ℓ ν))) :
    (appendRedPosition a).val = a.val := rfl

theorem appendRedLoading_lbl (s : Seq (stendhalWeight ℓ ν))
    (a : Fin (Multiset.card (stendhalWeight ℓ ν))) :
    (appendRedLoading s).lbl (appendRedPosition a) = addRedColor ℓ (s.lbl a) := by
  simp only [appendRedLoading, appendRedPosition, Seq.cast_apply, Fin.cast_cast, Fin.cast_eq_self,
    Seq.append_posL, Seq.map_lbl]

theorem hasLastRed_appendRedLoading (s : Seq (stendhalWeight ℓ ν)) :
    HasLastRed (appendRedLoading s) := by
  have hpos :
      lastRedPosition ℓ ν =
        Fin.cast (congrArg Multiset.card stendhalWeight_addRed)
          (Seq.posR ν₀ (⟨0, by simp⟩ : Fin (Multiset.card νᵣ))) := by
    apply Fin.ext
    change ν.card + ℓ = Multiset.card ν₀ + 0
    simp [stendhalWeight]
  unfold HasLastRed
  rw [hpos]
  simp only [appendRedLoading, Seq.cast_apply, Fin.cast_cast, Fin.cast_eq_self, Seq.append_posR,
    singletonRedSeq_lbl]

private theorem lastRedPosition_ge (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) :
    a ≤ lastRedPosition ℓ ν := by
  change a.val ≤ ν.card + ℓ
  have ha := a.isLt
  simp [stendhalWeight] at ha
  omega

theorem eq_lastRedPosition_or (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) :
    a = lastRedPosition ℓ ν ∨ ∃ b, a = appendRedPosition b := by
  by_cases h : a.val < Multiset.card (stendhalWeight ℓ ν)
  · exact Or.inr ⟨⟨_, h⟩, Fin.ext rfl⟩
  · refine Or.inl (Fin.ext ?_)
    have ha := lastRedPosition_ge a
    change a.val ≤ ν.card + ℓ at ha
    change a.val = ν.card + ℓ
    simp [stendhalWeight] at h
    omega

private theorem addRedColor_eq_inr {c : I ⊕ Fin ℓ} {r : Fin (ℓ + 1)}
    (h : addRedColor ℓ c = .inr r) : ∃ q, c = .inr q ∧ Fin.castSucc q = r := by
  cases c with
  | inl i => cases h
  | inr q => exact ⟨q, rfl, Sum.inr.inj h⟩

/-- The embedding appends the largest red label and preserves the order of the earlier labels. -/
theorem appendRedLoading_ordered_iff (s : Seq (stendhalWeight ℓ ν)) :
    IsRedOrdered (appendRedLoading s) ↔ IsRedOrdered s := by
  constructor
  · intro h a b r r' hab ha hb
    have h₁ : (appendRedLoading s).lbl (appendRedPosition a) = .inr (Fin.castSucc r) := by
      rw [appendRedLoading_lbl, ha]
      rfl
    have h₂ : (appendRedLoading s).lbl (appendRedPosition b) = .inr (Fin.castSucc r') := by
      rw [appendRedLoading_lbl, hb]
      rfl
    exact h (appendRedPosition a) (appendRedPosition b) _ _ hab h₁ h₂
  · intro h a b r r' hab ha hb
    rcases eq_lastRedPosition_or a with rfl | ⟨a, rfl⟩
    · exact (not_lt_of_ge (lastRedPosition_ge b) hab).elim
    rw [appendRedLoading_lbl] at ha
    obtain ⟨q, hq, rfl⟩ := addRedColor_eq_inr ha
    rcases eq_lastRedPosition_or b with rfl | ⟨b, rfl⟩
    · have hlast := hasLastRed_appendRedLoading s
      change (appendRedLoading s).lbl (lastRedPosition ℓ ν) = .inr (Fin.last ℓ) at hlast
      have hr : r' = Fin.last ℓ := Sum.inr.inj (hb.symm.trans hlast)
      subst r'
      exact q.isLt
    rw [appendRedLoading_lbl] at hb
    obtain ⟨q', hq', rfl⟩ := addRedColor_eq_inr hb
    exact h a b q q' hab hq hq'

theorem addRedColor_isLeft (c : I ⊕ Fin ℓ) :
    (addRedColor ℓ c).isLeft = c.isLeft := by
  cases c <;> rfl

/-- Appending a terminal red strand preserves the violated boundary loadings. -/
theorem appendRedLoading_violated_iff (s : Seq (stendhalWeight ℓ ν)) :
    IsViolated (appendRedLoading s) ↔ IsViolated s := by
  constructor
  · rintro ⟨h, ha⟩
    by_cases h₀ : 0 < Multiset.card (stendhalWeight ℓ ν)
    · refine ⟨h₀, ?_⟩
      rwa [show (⟨0, h⟩ : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) =
        appendRedPosition ⟨0, h₀⟩ from Fin.ext rfl, appendRedLoading_lbl, addRedColor_isLeft] at ha
    have hlast : (⟨0, h⟩ : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) =
        lastRedPosition ℓ ν := by
      apply Fin.ext
      change 0 = ν.card + ℓ
      simpa [stendhalWeight] using (Nat.eq_zero_of_not_pos h₀).symm
    have hr := hasLastRed_appendRedLoading s
    change (appendRedLoading s).lbl (lastRedPosition ℓ ν) = .inr (Fin.last ℓ) at hr
    rw [hlast, hr] at ha
    cases ha
  · rintro ⟨h, ha⟩
    have h₁ : 0 < Multiset.card (stendhalWeight (ℓ + 1) ν) := by simp [stendhalWeight]
    refine ⟨h₁, ?_⟩
    rwa [show (⟨0, h₁⟩ : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) =
      appendRedPosition ⟨0, h⟩ from Fin.ext rfl, appendRedLoading_lbl, addRedColor_isLeft]

theorem appendRedLoading_injective :
    Function.Injective (appendRedLoading (ℓ := ℓ) (ν := ν)) := by
  intro s t h
  apply Subtype.ext
  funext a
  apply addRedColor_injective ℓ
  exact (appendRedLoading_lbl s a).symm.trans
    ((congrArg (fun u => u.lbl (appendRedPosition a)) h).trans (appendRedLoading_lbl t a))

private theorem appendRedLoading_surjOn
    (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : HasLastRed s) :
    ∃ t, appendRedLoading t = s := by
  let h := stendhalWeight_addRed (ℓ := ℓ) (ν := ν)
  let s' := Seq.cast h.symm s
  have hr (a : Fin (Multiset.card νᵣ)) : s'.lbl (Seq.posR ν₀ a) = .inr (Fin.last ℓ) := by
    change s.lbl (Fin.cast (congrArg Multiset.card h) (Seq.posR ν₀ a)) = _
    have hpos : Fin.cast (congrArg Multiset.card h) (Seq.posR ν₀ a) =
        lastRedPosition ℓ ν := by
      apply Fin.ext
      change Multiset.card ν₀ + a.val = ν.card + ℓ
      have ha := a.isLt
      simp [stendhalWeight] at ha ⊢
      omega
    rw [hpos]
    exact hs
  let lbl : Fin (Multiset.card (ν₀ + νᵣ)) → I ⊕ Fin (ℓ + 1) := s'.lbl
  have hright : Finset.univ.val.map (lbl ∘ Seq.posR ν₀) = νᵣ := by
    rw [show lbl ∘ Seq.posR ν₀ = fun _ => Sum.inr (Fin.last ℓ) from funext hr]
    simp
  have hsplit : Finset.univ.val.map lbl =
      Finset.univ.val.map (lbl ∘ Seq.posL νᵣ) + Finset.univ.val.map (lbl ∘ Seq.posR ν₀) := by
    conv_lhs => rw [← Multiset.map_univ_val_equiv (TypeA.blockEquiv (Seq.card_add' ν₀ νᵣ))]
    rw [Multiset.map_map, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum,
      Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rfl
  have hs' : Finset.univ.val.map lbl = ν₀ + νᵣ := s'.2
  rw [hs', hright] at hsplit
  let t' : Seq ν₀ := ⟨_, (add_right_cancel hsplit).symm⟩
  obtain ⟨t, ht⟩ := (Seq.map_bijective (addRedColor_injective ℓ) (stendhalWeight ℓ ν)).2 t'
  have hst : t'.append (singletonRedSeq ℓ) = s' := by
    apply Subtype.ext
    funext a
    obtain ⟨a, rfl⟩ := (TypeA.blockEquiv (Seq.card_add' ν₀ νᵣ)).surjective a
    cases a with
    | inl a => exact Seq.append_posL _ _ a
    | inr a =>
      exact (Seq.append_posR _ _ a).trans ((singletonRedSeq_lbl a).trans (hr a).symm)
  refine ⟨t, ?_⟩
  rw [appendRedLoading, ht, hst]
  apply Subtype.ext
  funext a
  simp [s']

/-- Appending the rightmost red strand identifies the old loadings with
the red-ordered loadings indexing Webster's idempotent (e_\ell). -/
def appendRedOrderedEquiv :
    { s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s } ≃
      { s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s ∧ HasLastRed s } :=
  Equiv.ofBijective
    (fun s => ⟨appendRedLoading s.1,
      (appendRedLoading_ordered_iff s.1).2 s.2, hasLastRed_appendRedLoading s.1⟩)
    ⟨fun _ _ h => Subtype.ext (appendRedLoading_injective (congrArg Subtype.val h)), by
      intro s
      obtain ⟨t, ht⟩ := appendRedLoading_surjOn s.1 s.2.2
      have ho : IsRedOrdered (appendRedLoading t) := ht.symm ▸ s.2.1
      exact ⟨⟨t, (appendRedLoading_ordered_iff t).1 ho⟩, Subtype.ext ht⟩⟩

end Loadings

section AppendDiagrams

open KLRAlgebra

variable [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "μ" => stendhalWeight ℓ ν
local notation "ν₀" => Multiset.map (addRedColor ℓ) μ
local notation "νᵣ" => ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ + 1)))
local notation "S" => stendhalQ Q Λ
local notation "A" => StendhalAlgebraAllOrders k Q Λ ν

private def appendRedRelabel :
    SeqRelabel k (stendhalQ Q Λ₀) S μ ν₀ :=
  let R := SeqRelabel.ofInjective (addRedColor_injective (I := I) ℓ) S μ
  { card_eq := R.card_eq
    equiv := R.equiv
    equiv_smul := R.equiv_smul
    lbl_eq_iff := R.lbl_eq_iff
    Q_eq := fun i a b hab =>
      (R.Q_eq i a b hab).trans (by
        cases i.lbl a <;> cases i.lbl b <;> rfl) }

private def appendRedAmbient : KLRAlgebra k S (ν₀ + νᵣ) →ₐ[k] A :=
  (StendhalAlgebraAllOrders.ofKLR k Q Λ ν).comp
    (castKLR S (stendhalWeight_addRed (ℓ := ℓ) (ν := ν))).toAlgHom

private def terminalIdem : A :=
  appendRedAmbient Q Λ ν (oneConcat S ν₀ νᵣ)

private theorem isIdempotentElem_terminalIdem : IsIdempotentElem (terminalIdem Q Λ ν) :=
  (oneConcat_idem (Q := S) (ν := ν₀) (ν' := νᵣ)).map (appendRedAmbient Q Λ ν)

local instance : Algebra k (isIdempotentElem_terminalIdem Q Λ ν).Corner :=
  KLR.cornerAlgebra _

private def appendRedConcatCorner :
    ConcatCorner S ν₀ νᵣ →ₐ[k] (isIdempotentElem_terminalIdem Q Λ ν).Corner where
  toFun z := KLR.Corner.mk (appendRedAmbient Q Λ ν z.val) (by
    have hz : oneConcat S ν₀ νᵣ * z.val * oneConcat S ν₀ νᵣ = z.val :=
      (congrArg (· * oneConcat S ν₀ νᵣ) (KLR.Corner.E_mul_val z)).trans
        (KLR.Corner.val_mul_E z)
    simpa only [map_mul, terminalIdem] using congrArg (appendRedAmbient Q Λ ν) hz)
  map_one' := rfl
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)
  commutes' c := Subtype.ext (by
    change appendRedAmbient Q Λ ν (algebraMap k _ c * oneConcat S ν₀ νᵣ) =
      algebraMap k A c * terminalIdem Q Λ ν
    rw [map_mul, AlgHom.commutes]
    rfl)

private def appendRedKLR :
    KLRAlgebra k (stendhalQ Q Λ₀) μ →ₐ[k] (isIdempotentElem_terminalIdem Q Λ ν).Corner :=
  (appendRedConcatCorner Q Λ ν).comp (((blockL ν₀ νᵣ).hom S).comp
    (relabelHom (appendRedRelabel Q Λ ν)))

omit [DecidableEq I] in
private theorem singletonRedSeq_unique (s : Seq νᵣ) : s = singletonRedSeq ℓ := by
  apply Subtype.ext
  funext a
  exact (Multiset.mem_singleton.mp (Seq.mem s a)).trans (singletonRedSeq_lbl a).symm

private theorem blockL_appendRed_fibre (s : Seq ν₀) :
    (blockL ν₀ νᵣ).F s = {s.append (singletonRedSeq ℓ)} := by
  classical
  ext t
  change t ∈ Finset.univ.image (fun a : Seq νᵣ => s.append a) ↔ _
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [singletonRedSeq_unique a]
  · intro h
    exact ⟨singletonRedSeq ℓ, h.symm⟩

private theorem appendRedKLR_val (z : KLRAlgebra k (stendhalQ Q Λ₀) μ) :
    (appendRedKLR Q Λ ν z).val =
      appendRedAmbient Q Λ ν (((blockL ν₀ νᵣ).hom S)
        (relabelHom (appendRedRelabel Q Λ ν) z)).val := rfl

private theorem appendRedKLR_e (s : Seq μ) :
    (appendRedKLR Q Λ ν (KLRAlgebra.e s)).val =
      StendhalAlgebraAllOrders.e (appendRedLoading s) := by
  rw [appendRedKLR_val, relabelHom_e, BlockEmb.hom_e, BlockEmb.val_gE]
  change appendRedAmbient Q Λ ν (eSum S ((blockL ν₀ νᵣ).F (Seq.map (addRedColor ℓ) s))) = _
  rw [blockL_appendRed_fibre, eSum, Finset.sum_singleton]
  simp [appendRedAmbient, appendRedLoading, castKLR_e, StendhalAlgebraAllOrders.e]

private theorem appendRedKLR_x (a : Fin (Multiset.card μ)) :
    (appendRedKLR Q Λ ν (KLRAlgebra.x a)).val =
      StendhalAlgebraAllOrders.x (appendRedPosition a) * terminalIdem Q Λ ν := by
  rw [appendRedKLR_val, relabelHom_x, BlockEmb.hom_x, val_polCorner, pol_X, map_mul]
  congr 1
  simp [appendRedAmbient, appendRedPosition, castKLR_x,
    StendhalAlgebraAllOrders.x, blockL]

private theorem appendRedKLR_ψ {j : ℕ} (hj : j + 1 < Multiset.card μ) :
    (appendRedKLR Q Λ ν (KLRAlgebra.ψ j)).val =
      StendhalAlgebraAllOrders.ψ j * terminalIdem Q Λ ν := by
  have hj' : j + 1 < Multiset.card ν₀ := by simpa using hj
  rw [appendRedKLR_val, relabelHom_ψ, BlockEmb.hom_ψ, BlockEmb.val_gψ _ hj', map_mul]
  congr 1
  simp [appendRedAmbient, castKLR_ψ, StendhalAlgebraAllOrders.ψ, blockL]

omit [DecidableEq I] in
private theorem addRedColor_isRight (c : I ⊕ Fin ℓ) :
    (addRedColor ℓ c).isRight = c.isRight := by
  cases c <;> rfl

/-- Append the new red strand on the right of a diagram, before imposing the
violating ideal. The corner includes all orders of the earlier red strands. -/
def appendRedAllOrders :
    StendhalAlgebraAllOrders k Q Λ₀ ν →ₐ[k] (isIdempotentElem_terminalIdem Q Λ ν).Corner :=
  RingQuot.liftAlgHom k
    ⟨(appendRedKLR Q Λ ν).comp (KLRAlgebra.mk k (stendhalQ Q Λ₀) μ), fun x y h => by
      cases h with
      | klr h =>
        exact congrArg (appendRedKLR Q Λ ν) (RingQuot.mkAlgHom_rel k h)
      | red_dot a s ha =>
        apply KLR.Corner.ext
        simp only [AlgHom.comp_apply, map_mul, map_zero, KLR.Corner.val_mul, KLR.Corner.val_zero]
        change (appendRedKLR Q Λ ν (KLRAlgebra.x a)).val *
          (appendRedKLR Q Λ ν (KLRAlgebra.e s)).val = 0
        have hs := KLR.Corner.E_mul_val (appendRedKLR Q Λ ν (KLRAlgebra.e s))
        rw [appendRedKLR_e] at hs
        rw [appendRedKLR_x, appendRedKLR_e, mul_assoc]
        change StendhalAlgebraAllOrders.x (appendRedPosition a) *
          (terminalIdem Q Λ ν * StendhalAlgebraAllOrders.e (appendRedLoading s)) = _
        rw [hs]
        have ha' : ((appendRedLoading s).lbl (appendRedPosition a)).isRight := by
          simpa only [appendRedLoading_lbl, addRedColor_isRight] using ha
        exact StendhalAlgebraAllOrders.x_mul_e_of_red (appendRedPosition a) (appendRedLoading s) ha'
      | red_cross j hj s ha hb =>
        apply KLR.Corner.ext
        simp only [AlgHom.comp_apply, map_mul, map_zero, KLR.Corner.val_mul, KLR.Corner.val_zero]
        change (appendRedKLR Q Λ ν (KLRAlgebra.ψ j)).val *
          (appendRedKLR Q Λ ν (KLRAlgebra.e s)).val = 0
        have hs := KLR.Corner.E_mul_val (appendRedKLR Q Λ ν (KLRAlgebra.e s))
        rw [appendRedKLR_e] at hs
        rw [appendRedKLR_ψ Q Λ ν hj, appendRedKLR_e, mul_assoc]
        change StendhalAlgebraAllOrders.ψ j *
          (terminalIdem Q Λ ν * StendhalAlgebraAllOrders.e (appendRedLoading s)) = _
        rw [hs]
        have hj' : j + 1 < Multiset.card (stendhalWeight (ℓ + 1) ν) := by
          simp [stendhalWeight] at hj ⊢
          omega
        have ha' : ((appendRedLoading s).lbl ⟨j, by omega⟩).isRight := by
          rw [show (⟨j, by omega⟩ : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) =
            appendRedPosition ⟨j, by omega⟩ from Fin.ext rfl, appendRedLoading_lbl, addRedColor_isRight]
          exact ha
        have hb' : ((appendRedLoading s).lbl ⟨j + 1, hj'⟩).isRight := by
          rw [show (⟨j + 1, hj'⟩ : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) =
            appendRedPosition ⟨j + 1, hj⟩ from Fin.ext rfl, appendRedLoading_lbl, addRedColor_isRight]
          exact hb
        exact StendhalAlgebraAllOrders.ψ_mul_e_of_red j hj' (appendRedLoading s) ha' hb'⟩

private theorem appendRedAllOrders_ofKLR (z : KLRAlgebra k (stendhalQ Q Λ₀) μ) :
    appendRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.ofKLR k Q Λ₀ ν z) =
      appendRedKLR Q Λ ν z := by
  obtain ⟨w, rfl⟩ := KLRAlgebra.mk_surjective z
  rw [StendhalAlgebraAllOrders.ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem appendRedAllOrders_e (s : Seq μ) :
    (appendRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.e s)).val =
      StendhalAlgebraAllOrders.e (appendRedLoading s) := by
  rw [StendhalAlgebraAllOrders.e, appendRedAllOrders_ofKLR, appendRedKLR_e]

private def appendRedValue : StendhalAlgebraAllOrders k Q Λ₀ ν →ₙ+* A :=
  (KLR.cornerVal (isIdempotentElem_terminalIdem Q Λ ν)).comp
    (appendRedAllOrders Q Λ ν).toRingHom.toNonUnitalRingHom

private theorem appendRedValue_e (s : Seq μ) :
    appendRedValue Q Λ ν (StendhalAlgebraAllOrders.e s) =
      StendhalAlgebraAllOrders.e (appendRedLoading s) :=
  appendRedAllOrders_e Q Λ ν s

private theorem appendRedValue_smul (c : k) (z : StendhalAlgebraAllOrders k Q Λ₀ ν) :
    appendRedValue Q Λ ν (c • z) = c • appendRedValue Q Λ ν z := by
  change (appendRedAllOrders Q Λ ν (c • z)).val =
    c • (appendRedAllOrders Q Λ ν z).val
  rw [AlgHom.map_smul_of_tower, KLR.Corner.val_smul]

local instance : Fintype { s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s ∧ HasLastRed s } :=
  Fintype.ofFinite _

private theorem lastRedIdem_val_eq_sum :
    (StendhalAlgebra.lastRedIdem Q Λ ν).val =
      ∑ s : { s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s ∧ HasLastRed s },
        StendhalAlgebraAllOrders.e s.1 := by
  classical
  let R := { s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s }
  let L := { s : R // HasLastRed s.1 }
  let F := { s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s ∧ HasLastRed s }
  let : Fintype R := Fintype.ofFinite _
  let : Fintype L := Fintype.ofFinite _
  let : Fintype F := Fintype.ofFinite _
  let e : L ≃ F :=
    ⟨fun s => ⟨s.1.1, s.1.2, s.2⟩,
      fun s => ⟨⟨s.1, s.2.1⟩, s.2.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [StendhalAlgebra.lastRedIdem, KLR.Corner.val_sum]
  have hsum :
      (∑ s ∈ Finset.univ.filter (fun s : R => HasLastRed s.1),
        (StendhalAlgebraAllOrders.e (Q := Q) (Λ := Λ) s.1 : A)) =
        ∑ s : L, StendhalAlgebraAllOrders.e s.1.1 :=
    Finset.sum_subtype _ (fun s => by simp) _
  calc
    _ = ∑ s : L, StendhalAlgebraAllOrders.e s.1.1 := hsum
    _ = ∑ s : F, StendhalAlgebraAllOrders.e s.1 :=
      Equiv.sum_comp e (fun s : F => (StendhalAlgebraAllOrders.e s.1 : A))

private theorem appendRedValue_redOrderedIdem :
    appendRedValue Q Λ ν (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν) =
      (StendhalAlgebra.lastRedIdem Q Λ ν).val := by
  classical
  let R := { s : Seq μ // IsRedOrdered s }
  let F := { s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s ∧ HasLastRed s }
  let : Fintype R := Fintype.ofFinite _
  let : Fintype F := Fintype.ofFinite _
  have hsum : StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν =
      ∑ s : R, StendhalAlgebraAllOrders.e s.1 :=
    Finset.sum_subtype _ (fun s => by simp) _
  rw [hsum, map_sum, lastRedIdem_val_eq_sum]
  simp only [appendRedValue_e]
  exact Equiv.sum_comp appendRedOrderedEquiv
    (fun s : F => (StendhalAlgebraAllOrders.e s.1 : A))

private theorem appendRedValue_corner (z : StendhalAlgebra k Q Λ₀ ν) :
    appendRedValue Q Λ ν z.val ∈
      Subsemigroup.corner (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) := by
  let φ := appendRedValue Q Λ ν
  let P := StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν
  let E := StendhalAlgebra.lastRedIdem Q Λ ν
  have hu : φ P = E.val := appendRedValue_redOrderedIdem Q Λ ν
  have hl : E.val * φ z.val = φ z.val := by
    rw [← hu, ← map_mul]
    exact congrArg φ (KLR.Corner.E_mul_val z)
  have hr : φ z.val * E.val = φ z.val := by
    rw [← hu, ← map_mul]
    exact congrArg φ (KLR.Corner.val_mul_E z)
  apply (Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).2
  constructor
  · rw [← hl, ← mul_assoc]
    exact congrArg (· * φ z.val) (KLR.Corner.E_mul_val E)
  · rw [← hr, mul_assoc]
    exact congrArg (φ z.val * ·) (KLR.Corner.val_mul_E E)

/-- Appending a terminal red strand on red-ordered diagrams before quotienting.
Its value on the unit is Webster's terminal red idempotent. -/
def appendRedStendhalValue : StendhalAlgebra k Q Λ₀ ν →ₙ+* StendhalAlgebra k Q Λ ν where
  toFun z := ⟨appendRedValue Q Λ ν z.val, appendRedValue_corner Q Λ ν z⟩
  map_zero' := Subtype.ext (map_zero (appendRedValue Q Λ ν))
  map_add' x y := Subtype.ext (map_add (appendRedValue Q Λ ν) x.val y.val)
  map_mul' x y := Subtype.ext (map_mul (appendRedValue Q Λ ν) x.val y.val)

theorem appendRedStendhalValue_one :
    appendRedStendhalValue Q Λ ν 1 = StendhalAlgebra.lastRedIdem Q Λ ν :=
  Subtype.ext (appendRedValue_redOrderedIdem Q Λ ν)

theorem appendRedStendhalValue_e (s : Seq μ) (hs : IsRedOrdered s) :
    appendRedStendhalValue Q Λ ν (StendhalAlgebra.e s hs) =
      StendhalAlgebra.e (appendRedLoading s) ((appendRedLoading_ordered_iff s).2 hs) :=
  Subtype.ext (appendRedValue_e Q Λ ν s)

open TypeA MvPolynomial

local notation "μ'" => stendhalWeight (ℓ + 1) ν
local notation "B₀" => KLRAlgebra k (stendhalQ Q Λ₀) μ
local notation "π₁" => StendhalAlgebraAllOrders.ofKLR k Q Λ ν

private theorem appendRedKLR_pol_mul (p : MvPolynomial (Fin (Multiset.card μ)) k) (z : B₀) :
    (appendRedKLR Q Λ ν (pol p * z)).val =
      π₁ (pol (rename appendRedPosition p)) * (appendRedKLR Q Λ ν z).val := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [algHom_C, rename_C, algHom_C, AlgHom.commutes, ← Algebra.smul_def,
      AlgHom.map_smul_of_tower, KLR.Corner.val_smul, Algebra.smul_def]
  | add p q hp hq =>
    simp only [map_add, add_mul, KLR.Corner.val_add, hp, hq]
  | mul_X p a hp =>
    rw [mul_comm p, map_mul pol, mul_assoc, map_mul (appendRedKLR Q Λ ν),
      KLR.Corner.val_mul, pol_X, appendRedKLR_x, mul_assoc, KLR.Corner.E_mul_val,
      hp, map_mul (rename _), map_mul pol, map_mul π₁, rename_X, pol_X, mul_assoc]
    rfl

private theorem appendRedKLR_word_mul (ρ : List ℕ) (hr : ValidWord (Multiset.card μ) ρ) (z : B₀) :
    (appendRedKLR Q Λ ν (ψw ρ * z)).val = π₁ (ψw ρ) * (appendRedKLR Q Λ ν z).val := by
  induction ρ with
  | nil => simp [ψw]
  | cons j ρ ih =>
    obtain ⟨hj, hρ⟩ := validWord_cons.1 hr
    rw [ψw_cons, ψw_cons, mul_assoc, map_mul, KLR.Corner.val_mul, appendRedKLR_ψ Q Λ ν hj,
      mul_assoc, KLR.Corner.E_mul_val, ih hρ, map_mul, mul_assoc]
    rfl

omit [DecidableEq I] in
private theorem lastRedPosition_unique (s : Seq μ') (hs : HasLastRed s)
    (a : Fin (Multiset.card μ')) (ha : s.lbl a = .inr (Fin.last ℓ)) :
    a = lastRedPosition ℓ ν := by
  obtain ⟨t, rfl⟩ := appendRedLoading_surjOn s hs
  rcases eq_lastRedPosition_or a with h | ⟨b, rfl⟩
  · exact h
  rw [appendRedLoading_lbl] at ha
  obtain ⟨q, _, he⟩ := addRedColor_eq_inr ha
  exact (Fin.castSucc_ne_last q he).elim

private theorem validWord_of_fix_last {n m : ℕ} (hn : n + 1 = m) {ρ : List ℕ} (hr : IsReduced m ρ)
    (hfix : wordProd m ρ (⟨n, by omega⟩ : Fin m) = ⟨n, by omega⟩) : ValidWord n ρ := by
  classical
  intro j hj
  have hj' := hr.1 j hj
  by_contra h
  have he : j + 1 = n := by omega
  have hz : rk (wordProd m ρ) n n = 0 := by
    rw [rk, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p _ ⟨hp, hw⟩
    have hpos : (wordProd m ρ) p = ⟨n, by omega⟩ :=
      Fin.ext (by change ((wordProd m ρ) p).val = n; have := ((wordProd m ρ) p).isLt; omega)
    have hx := (wordProd m ρ).injective (hpos.trans hfix.symm)
    exact (Nat.ne_of_lt hp) (congrArg Fin.val hx)
  have hle := rk_wordProd_sublist_le hr (List.singleton_sublist.2 hj) n n
  have hpos : 0 < rk (wordProd m [j]) n n := by
    apply Finset.card_pos.2
    refine ⟨⟨j, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · change j < n
      omega
    · simp [wordProd, sadj_val_of_lt hj', swapNat, ← he]
  omega

omit [DecidableEq I] in
private theorem reducedWord_of_lastRed {s : Seq μ'} {w : Equiv.Perm (Fin (Multiset.card μ'))}
    (hs : HasLastRed s) (ht : HasLastRed (w • s)) {ρ : List ℕ}
    (hr : IsReduced (Multiset.card μ') ρ) (hw : wordProd (Multiset.card μ') ρ = w) :
    ValidWord (Multiset.card μ) ρ := by
  have hn : Multiset.card μ + 1 = Multiset.card μ' := by simp [stendhalWeight]; omega
  apply validWord_of_fix_last hn hr
  rw [hw]
  have hpos : (⟨Multiset.card μ, by omega⟩ : Fin (Multiset.card μ')) = lastRedPosition ℓ ν :=
    Fin.ext (by simp [lastRedPosition, stendhalWeight])
  rw [hpos]
  have hl := lastRedPosition_unique ν s hs (w.symm (lastRedPosition ℓ ν)) ht
  exact (congrArg w hl.symm).trans (w.apply_symm_apply _)

omit [DecidableEq I] in
private theorem polynomial_of_lastRed (s : Seq μ') (hs : HasLastRed s)
    (d : Fin (Multiset.card μ') →₀ ℕ) (hd : ∀ a ∈ d.support, (s.lbl a).isLeft) :
    ∃ p : MvPolynomial (Fin (Multiset.card μ)) k,
      rename appendRedPosition p = monomial d 1 := by
  apply exists_rename_eq_of_vars_subset_range
  · exact fun a b h => Fin.ext (congrArg (fun x : Fin (Multiset.card μ') => x.val) h)
  · intro a ha
    rcases eq_lastRedPosition_or a with rfl | ⟨b, rfl⟩
    · have ha' : lastRedPosition ℓ ν ∈ d.support := by
        by_cases h : (1 : k) = 0
        · simp [h] at ha
        · rwa [vars_monomial h] at ha
      have hx := hd _ ha'
      change s.lbl (lastRedPosition ℓ ν) = .inr (Fin.last ℓ) at hs
      rw [hs] at hx
      cases hx
    · exact ⟨b, rfl⟩

section Quotient

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

theorem appendRedStendhalValue_smul (c : k) (z : StendhalAlgebra k Q Λ₀ ν) :
    appendRedStendhalValue Q Λ ν (c • z) = c • appendRedStendhalValue Q Λ ν z :=
  Subtype.ext (appendRedValue_smul Q Λ ν c z.val)

instance (priority := 1200) TensorProductAlgebra.lastRedCornerAlgebra :
    Algebra k (TensorProductAlgebra.lastRedCorner Q Λ ν) :=
  KLR.cornerAlgebra _

private def appendRedBeforeQuotient :
    StendhalAlgebra k Q Λ₀ ν →ₐ[k] TensorProductAlgebra.lastRedCorner Q Λ ν where
  toFun z :=
    let f := appendRedStendhalValue Q Λ ν
    let π := TensorProductAlgebra.mk Q Λ ν
    ⟨π (f z), (Subsemigroup.mem_corner_iff
      (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν)).2
      ⟨by
        change π (StendhalAlgebra.lastRedIdem Q Λ ν) * π (f z) = π (f z)
        rw [← appendRedStendhalValue_one, ← map_mul, ← map_mul, one_mul],
       by
        change π (f z) * π (StendhalAlgebra.lastRedIdem Q Λ ν) = π (f z)
        rw [← appendRedStendhalValue_one, ← map_mul, ← map_mul, mul_one]⟩⟩
  map_one' := Subtype.ext (congrArg (TensorProductAlgebra.mk Q Λ ν)
    (appendRedStendhalValue_one Q Λ ν))
  map_zero' := by
    apply Subtype.ext
    exact (congrArg (TensorProductAlgebra.mk Q Λ ν) (map_zero (appendRedStendhalValue Q Λ ν))).trans
      (map_zero _)
  map_add' x y := by
    apply Subtype.ext
    exact (congrArg (TensorProductAlgebra.mk Q Λ ν)
      (map_add (appendRedStendhalValue Q Λ ν) x y)).trans (map_add _ _ _)
  map_mul' x y := by
    apply Subtype.ext
    exact (congrArg (TensorProductAlgebra.mk Q Λ ν)
      (map_mul (appendRedStendhalValue Q Λ ν) x y)).trans (map_mul _ _ _)
  commutes' c := by
    apply Subtype.ext
    change TensorProductAlgebra.mk Q Λ ν
      (appendRedStendhalValue Q Λ ν (algebraMap k _ c)) =
      algebraMap k _ c * TensorProductAlgebra.lastRedIdem Q Λ ν
    rw [show algebraMap k (StendhalAlgebra k Q Λ₀ ν) c = c • (1 : StendhalAlgebra k Q Λ₀ ν) from
      Algebra.algebraMap_eq_smul_one c, appendRedStendhalValue_smul, appendRedStendhalValue_one]
    exact (map_smul (TensorProductAlgebra.mk Q Λ ν).toLinearMap c _).trans (Algebra.smul_def _ _)

private theorem appendRedBeforeQuotient_e (s : Seq μ) (hs : IsRedOrdered s) :
    (appendRedBeforeQuotient Q Λ ν (StendhalAlgebra.e s hs)).val =
      TensorProductAlgebra.mk Q Λ ν
        (StendhalAlgebra.e (appendRedLoading s) ((appendRedLoading_ordered_iff s).2 hs)) :=
  congrArg (TensorProductAlgebra.mk Q Λ ν) (appendRedStendhalValue_e Q Λ ν s hs)

/-- Appending a red strand induces the map to the corner in the violating quotient
(Webster, arXiv:1309.3796v2, §4.3, proof of Proposition 4.18). -/
def appendRed : TensorProductAlgebra k Q Λ₀ ν →ₐ[k] TensorProductAlgebra.lastRedCorner Q Λ ν := by
  let J := StendhalAlgebra.violatedIdeal k Q Λ₀ ν
  let φ := appendRedBeforeQuotient Q Λ ν
  refine J.ringCon.liftₐ φ ?_
  change J.ringCon ≤ (TwoSidedIdeal.ker φ).ringCon
  rw [← TwoSidedIdeal.ringCon_le_iff]
  apply TwoSidedIdeal.span_le.2
  rintro _ ⟨s, hs, hV, rfl⟩
  change StendhalAlgebra.e s hs ∈ TwoSidedIdeal.ker φ
  apply (TwoSidedIdeal.mem_ker φ).2
  apply Subtype.ext
  change (appendRedBeforeQuotient Q Λ ν (StendhalAlgebra.e s hs)).val = 0
  rw [appendRedBeforeQuotient_e]
  change (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk' _ = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  exact TwoSidedIdeal.subset_span
    ⟨_, _, (appendRedLoading_violated_iff s).2 hV, rfl⟩

/-- The appending map on a boundary idempotent of the violating quotient. -/
theorem appendRed_mk_e (s : Seq μ) (hs : IsRedOrdered s) :
    (appendRed Q Λ ν (TensorProductAlgebra.mk Q Λ₀ ν (StendhalAlgebra.e s hs))).val =
      TensorProductAlgebra.mk Q Λ ν
        (StendhalAlgebra.e (appendRedLoading s) ((appendRedLoading_ordered_iff s).2 hs)) :=
  appendRedBeforeQuotient_e Q Λ ν s hs

private def appendRedOrderedLinear :
    StendhalAlgebra k Q Λ₀ ν →ₗ[k] StendhalAlgebra k Q Λ ν where
  toFun := appendRedStendhalValue Q Λ ν
  map_add' := map_add _
  map_smul' := appendRedStendhalValue_smul Q Λ ν

private theorem sandwich_mem_appendRedOrderedRange (t : StendhalAlgebra k Q Λ ν)
    {z : StendhalAlgebraAllOrders k Q Λ₀ ν} (hz : appendRedValue Q Λ ν z = t.val) :
    StendhalAlgebra.lastRedIdem Q Λ ν * t * StendhalAlgebra.lastRedIdem Q Λ ν ∈
      LinearMap.range (appendRedOrderedLinear Q Λ ν) := by
  let P := StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν
  have hP : P * P = P := StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem.eq
  refine ⟨⟨P * z * P, (Subsemigroup.mem_corner_iff
    StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).2 ⟨?_, ?_⟩⟩, ?_⟩
  · change P * (P * z * P) = _
    rw [← mul_assoc, ← mul_assoc, hP]
  · change P * z * P * P = _
    rw [mul_assoc, hP]
  · apply Subtype.ext
    change appendRedValue Q Λ ν (P * z * P) = _ * _ * _
    rw [map_mul, map_mul, hz, show appendRedValue Q Λ ν P = _ from
      appendRedValue_redOrderedIdem Q Λ ν]

section Span

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

local notation "M" => stendhalWeight (ℓ + 1) ν
local notation "ρ₁" => canWord (Multiset.card M)
local notation "H" => wordProd_canWord (Multiset.card M)
local notation "T" => stendhalTerm Q Λ H
local notation "E" => StendhalAlgebra.lastRedIdem Q Λ ν
local notation "φ" => appendRedOrderedLinear Q Λ ν
local notation "J" => {b // IsStendhalTerm (ℓ := ℓ + 1) (ν := ν) ρ₁ b}

/-- Appending to an old standard Stendhal term leaves its crossing word intact
and renames each of its dot positions into the larger loading
(Webster, arXiv:1309.3796v2, Proposition 4.18, proof using Proposition 4.16). -/
theorem appendRedStendhalValue_stendhalTerm
    {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : ∀ w, IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
      wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)
    (b : {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) ρ b}) :
    (appendRedStendhalValue Q Λ ν
      (stendhalTerm Q (Λ ∘ Fin.castSucc) (fun w => (hρ w).2) b)).val =
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν
        (ψw (ρ b.1.2.1) * (pol (rename appendRedPosition (monomial b.1.2.2 1)) *
          KLRAlgebra.e (appendRedLoading b.1.1))) := by
  change (appendRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.ofKLR _ _ _ _ (stdElt ρ b.1))).val = _
  rw [appendRedAllOrders_ofKLR, stdElt, mul_assoc, appendRedKLR_word_mul Q Λ ν _ (hρ _).1.1,
    appendRedKLR_pol_mul, appendRedKLR_e, map_mul, map_mul]
  rfl

private theorem sandwich_stendhalTerm_mem_range (b : J) : E * T b * E ∈ LinearMap.range φ := by
  classical
  let s := b.1.1
  let w := b.1.2.1
  let d := b.1.2.2
  have ho : IsRedOrdered s := b.2.1
  have ht : IsRedOrdered (w • s) := b.2.2.1
  by_cases hs : HasLastRed s
  · by_cases hw : HasLastRed (w • s)
    · obtain ⟨u, hu⟩ := appendRedLoading_surjOn s hs
      obtain ⟨p, hp⟩ := polynomial_of_lastRed (k := k) ν s hs d b.2.2.2.1
      have hv := reducedWord_of_lastRed ν hs hw (isReduced_canWord _ w) (H w)
      let z : KLRAlgebra k (stendhalQ Q (Λ ∘ Fin.castSucc)) (stendhalWeight ℓ ν) := ψw (ρ₁ w) * (pol p * KLRAlgebra.e u)
      apply sandwich_mem_appendRedOrderedRange Q Λ ν (T b) (z := StendhalAlgebraAllOrders.ofKLR
        k Q (Λ ∘ Fin.castSucc) ν z)
      change (appendRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.ofKLR _ _ _ _ z)).val = _
      rw [appendRedAllOrders_ofKLR, show z = ψw (ρ₁ w) * (pol p * KLRAlgebra.e u) from rfl, appendRedKLR_word_mul Q Λ ν _ hv,
        appendRedKLR_pol_mul, appendRedKLR_e, hu, hp]
      rw [stendhalTerm_val, stdElt, map_mul, map_mul, mul_assoc]
      rfl
    · have hh : StendhalAlgebra.e (Q := Q) (Λ := Λ) (w • s) ht * T b = T b := by
        rw [e_mul_stendhalTerm]
        simp [w, s]
      rw [← hh, ← mul_assoc E, StendhalAlgebra.lastRedIdem_mul_e]
      simp [hw]
  · have hh : T b * StendhalAlgebra.e (Q := Q) (Λ := Λ) s ho = T b := by
      rw [stendhalTerm_mul_e]
      simp [s]
    rw [← hh, mul_assoc E, mul_assoc, StendhalAlgebra.e_mul_lastRedIdem]
    simp [hs]

/-- Before taking the violating quotient, every diagram in the terminal-red corner
is obtained by appending a strand (Webster, arXiv:1309.3796v2, Proposition 4.18,
first paragraph of the proof). -/
theorem exists_appendRedStendhalValue (x : StendhalAlgebra k Q Λ ν) :
    ∃ v, appendRedStendhalValue Q Λ ν v = E * x * E := by
  have hspan := span_stendhalTerm (Q := Q) (Λ := Λ) (ν := ν)
    (fun w => ⟨isReduced_canWord _ w, H w⟩)
  change E * x * E ∈ LinearMap.range φ
  have h : x ∈ Submodule.span k (Set.range T) := hspan Submodule.mem_top
  induction h using Submodule.span_induction with
  | mem _ hb =>
    obtain ⟨b, rfl⟩ := hb
    exact sandwich_stendhalTerm_mem_range Q Λ ν b
  | zero => simp
  | add x y _ _ h₁ h₂ => simpa only [mul_add, add_mul] using add_mem h₁ h₂
  | smul c x _ h => simpa only [mul_smul_comm, smul_mul_assoc] using Submodule.smul_mem _ c h

/-- The add-red map is onto in every black weight (Webster, arXiv:1309.3796v2,
Proposition 4.18, spanning argument from Proposition 4.16). -/
theorem appendRed_surjective : Function.Surjective (appendRed Q Λ ν) := by
  intro y
  let π := TensorProductAlgebra.mk Q Λ ν
  obtain ⟨x, hx⟩ := (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk'_surjective y.val
  obtain ⟨v, hv⟩ := exists_appendRedStendhalValue Q Λ ν x
  refine ⟨TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) ν v, Subtype.ext ?_⟩
  change π (appendRedStendhalValue Q Λ ν v) = y.val
  change π x = y.val at hx
  rw [hv, map_mul, map_mul, hx]
  change TensorProductAlgebra.lastRedIdem Q Λ ν * y.val *
    TensorProductAlgebra.lastRedIdem Q Λ ν = y.val
  rw [KLR.Corner.E_mul_val, KLR.Corner.val_mul_E]

end Span

omit [DecidableEq I] in
private theorem hasLastRed_vacuum (s : Seq (stendhalWeight (ℓ + 1) (0 : Multiset I)))
    (hs : IsRedOrdered s) : HasLastRed s := by
  let a := lastRedPosition ℓ (0 : Multiset I)
  have hmem : Sum.inr (Fin.last ℓ) ∈ Finset.univ.val.map s.lbl := by
    rw [s.2]
    simp only [stendhalWeight, Multiset.map_zero, zero_add]
    exact Multiset.mem_map.2 ⟨_, Finset.mem_univ_val _, rfl⟩
  obtain ⟨b, _, hb⟩ := Multiset.mem_map.1 hmem
  rcases lt_or_eq_of_le (lastRedPosition_ge b) with h | h
  · have ha := s.mem a
    simp only [stendhalWeight, Multiset.map_zero, zero_add] at ha
    obtain ⟨r, _, hr⟩ := Multiset.mem_map.1 ha
    exact (not_lt_of_ge (Fin.le_last r) (hs b a (Fin.last ℓ) r h hb hr.symm)).elim
  · subst b
    exact hb

private theorem lastRedIdem_vacuum :
    TensorProductAlgebra.lastRedIdem Q Λ (0 : Multiset I) = 1 := by
  suffices h : StendhalAlgebra.lastRedIdem Q Λ (0 : Multiset I) = 1 by
    rw [TensorProductAlgebra.lastRedIdem, h, map_one]
  classical
  let : Fintype {s : Seq (stendhalWeight (ℓ + 1) (0 : Multiset I)) // IsRedOrdered s} :=
    Fintype.ofFinite _
  apply Subtype.ext
  rw [StendhalAlgebra.lastRedIdem, Finset.filter_true_of_mem (fun s _ => hasLastRed_vacuum s.1 s.2),
    KLR.Corner.val_sum, KLR.Corner.val_one]
  change (∑ s : {s : Seq (stendhalWeight (ℓ + 1) (0 : Multiset I)) // IsRedOrdered s},
    StendhalAlgebraAllOrders.e s.1) = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ 0
  exact (Finset.sum_subtype _ (fun s => by simp) _).symm

/-- With no black strands the add-red map of Webster, arXiv:1309.3796v2,
Proposition 4.18, identifies the two top-weight lines. -/
def appendRedVacuumEquiv : TensorProductAlgebra k Q Λ₀ (0 : Multiset I) ≃ₐ[k]
    TensorProductAlgebra.lastRedCorner Q Λ 0 := by
  let f := appendRed Q Λ (0 : Multiset I)
  let a := tensorProductAlgebraZeroEquiv Q Λ₀
  let b := tensorProductAlgebraZeroEquiv Q Λ
  have hf (c : k) : (f (algebraMap k _ c)).val =
      algebraMap k (TensorProductAlgebra k Q Λ 0) c := by
    rw [AlgHom.commutes]
    change algebraMap k _ c * TensorProductAlgebra.lastRedIdem Q Λ 0 = _
    rw [lastRedIdem_vacuum, mul_one]
  have ha (x : TensorProductAlgebra k Q Λ₀ 0) : algebraMap k _ (a x) = x := by
    apply a.injective
    exact a.commutes _
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    rw [← ha x, ← ha y, hf, hf] at he
    exact a.injective (by simpa only [AlgEquiv.commutes, Algebra.algebraMap_self, RingHom.id_apply] using congrArg b he)
  · intro y
    use algebraMap k _ (b y.val)
    apply Subtype.ext
    rw [hf]
    apply b.injective
    exact b.commutes _

/-- When the appended strand is the first red strand, the add-red map of
Webster, arXiv:1309.3796v2, Proposition 4.18, is an isomorphism in every
black weight. The nonzero black weights are killed by a violated boundary. -/
def appendFirstRedEquiv (Λ : Fin 1 → I →₀ ℕ) :
    TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) ν ≃ₐ[k]
      TensorProductAlgebra.lastRedCorner Q Λ ν := by
  by_cases hν : ν = 0
  · subst ν
    exact appendRedVacuumEquiv Q Λ
  · let f := appendRed Q Λ ν
    have hΛ : (Λ ∘ Fin.castSucc) = (Fin.elim0 : Fin 0 → I →₀ ℕ) := funext fun j => j.elim0
    haveI : Subsingleton (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) ν) := by
      rw [hΛ]
      exact subsingleton_emptyTensorAlgebra Q hν
    haveI : Subsingleton (TensorProductAlgebra.lastRedCorner Q Λ ν) :=
      subsingleton_of_zero_eq_one ((map_zero f).symm.trans
        ((congrArg f (Subsingleton.elim 0 1)).trans (map_one f)))
    exact AlgEquiv.ofBijective f
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩

end Quotient

end AppendDiagrams

end Categorification.Stendhal

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

private theorem reversed_reduced {ρ : List ℕ} {m : ℕ} (h : IsReduced m ρ) :
    IsReduced m ρ.reverse :=
  ⟨validWord_reverse.2 h.1, by rw [List.length_reverse, wordProd_reverse, length_inv]; exact h.2⟩

/-- A reduced expression first permutes all strands but the final strand, then
moves that strand to its position in the target loading. -/
private theorem exists_terminal_shuffle {m n : ℕ} (h : n + 1 = m) (w : Perm (Fin m)) :
    ∃ rest : List ℕ, ValidWord n rest ∧
      let a := (w (lastFin h)).val
      let ρ := (descRun a (n-a)).reverse ++ rest
      IsReduced m ρ ∧ wordProd m ρ = w := by
  classical
  obtain ⟨u, v, z, hz, he⟩ := exists_blockPerm_mul h w⁻¹
  have hv : v = 1 := Subsingleton.elim _ _
  subst v
  let D := descRun (w (lastFin h)).val (n - (w (lastFin h)).val)
  have ha : (w (lastFin h)).val ≤ n := by have := (w (lastFin h)).isLt; omega
  have zD : z = wordProd m D := by
    have heq := eq_cycA h h rfl (⟨z, hz⟩ : Shuffle h)
    have heinv := congrArg Inv.inv he
    have hew : w = z⁻¹ * blockPerm h u⁻¹ 1 := by
      simpa [mul_inv_rev, blockPerm_inv] using heinv.symm
    have hlast : lastFin h = lastB h (rfl : 1 = 1) := Fin.ext rfl
    have hzpos : w (lastFin h) = z⁻¹ (lastB h rfl) := by
      rw [hew, hlast]
      simp [lastB]
    change z = KLR.cycA (n := n) (w (lastFin h)).val
    rw [hzpos]
    exact heq
  let γ := canWord n u
  have hγ := isReduced_canWord n u
  have hnil : IsReduced 1 [] := by simp [TypeA.IsReduced]
  have hD : IsReduced m D := isReduced_descRun h ha
  obtain ⟨hred, hprod⟩ := hγ.parabolic h hnil hD (zD ▸ hz)
  refine ⟨γ.reverse, validWord_reverse.2 hγ.1, ?_⟩
  have hs : (γ ++ shiftWord n [] ++ D).reverse = D.reverse ++ γ.reverse := by simp [shiftWord]
  have hp : wordProd m (γ ++ shiftWord n [] ++ D) = w⁻¹ := by
    rw [hprod, wordProd_canWord, wordProd_nil, ← zD, he]
  constructor
  · exact hs ▸ reversed_reduced hred
  · rw [← hs, wordProd_reverse, hp, inv_inv]


variable {I : Type} {ℓ : ℕ} {ν : Multiset I}
local notation "M" => stendhalWeight (ℓ + 1) ν
local notation "N₀" => ν.card + ℓ
private theorem terminalCard : N₀ + 1 = Multiset.card M := by simp [stendhalWeight]; omega

/-- Moving the final red strand rightward through the black strands to its right
keeps an originally violated slice violated. -/
private theorem slide_terminal_loading (s : KLR.Seq M) (hs : IsRedOrdered s)
    (hV : IsViolated s) (a : Fin (Multiset.card M)) (ha : s.lbl a = .inr (Fin.last ℓ)) :
    let s' := (KLR.cycA (m := Multiset.card M) (n := N₀) a.val) • s
    IsRedOrdered s' ∧ HasLastRed s' ∧ IsViolated s' := by
  classical
  let C : Perm (Fin (Multiset.card M)) := KLR.cycA (m := Multiset.card M) (n := N₀) a.val
  have hm : N₀ + 1 = Multiset.card M := terminalCard
  have ha' : a.val ≤ N₀ := by have := a.isLt; omega
  have hpos : C.symm (lastRedPosition ℓ ν) = a := by
    apply Fin.ext
    rw [cycA_symm_val hm ha']
    change (if N₀ < a.val then N₀ else if N₀ < N₀ then N₀ + 1 else a.val) = a.val
    simp [Nat.not_lt.2 ha']
  have hlast : HasLastRed (C • s) := by
    change s.lbl (C.symm _) = _
    rwa [hpos]
  refine ⟨?_, hlast, ?_⟩
  · intro x y r r' hxy hx hy
    by_cases hylast : y = lastRedPosition ℓ ν
    · subst y
      have hy' : r' = Fin.last ℓ := Sum.inr.inj (hy.symm.trans hlast)
      subst r'
      apply Fin.lt_last_iff_ne_last.2
      intro he
      subst r
      exact hxy.ne (eq_of_lbl_eq_inr (i := C • s) hx hlast)
    · change s.lbl (C.symm x) = _ at hx
      change s.lbl (C.symm y) = _ at hy
      apply hs _ _ _ _ _ hx hy
      rw [Fin.lt_def, cycA_symm_val hm ha', cycA_symm_val hm ha']
      have hy' : y.val ≠ N₀ := fun e => hylast (Fin.ext e)
      have hyt := y.isLt
      have hxy' : x.val < y.val := hxy
      split_ifs <;> omega
  · obtain ⟨h0, hV⟩ := hV
    have hap : 0 < a.val := by
      by_contra! hn
      have he : a = ⟨0, h0⟩ := Fin.ext (Nat.eq_zero_of_le_zero hn)
      rw [he] at ha
      rw [ha] at hV
      cases hV
    have hc : C.symm ⟨0, h0⟩ = ⟨0, h0⟩ := by
      apply Fin.ext
      rw [cycA_symm_val hm ha']
      simp only [hap, ↓reduceIte]
    exact ⟨h0, by change (s.lbl (C.symm ⟨0, h0⟩)).isLeft; rwa [hc]⟩

private def terminalRest (w : Perm (Fin (Multiset.card M))) : List ℕ :=
  (exists_terminal_shuffle terminalCard w).choose

private def terminalPrefix (w : Perm (Fin (Multiset.card M))) : List ℕ :=
  let a := (w (lastFin (terminalCard (ℓ := ℓ) (ν := ν)))).val
  (descRun a (N₀ - a)).reverse

private def terminalWord (w : Perm (Fin (Multiset.card M))) : List ℕ :=
  terminalPrefix w ++ terminalRest w

private theorem terminalWord_spec (w : Perm (Fin (Multiset.card M))) :
    IsReduced (Multiset.card M) (terminalWord w) ∧ wordProd (Multiset.card M) (terminalWord w) = w :=
  (exists_terminal_shuffle terminalCard w).choose_spec.2

private theorem terminalWord_prod (w : Perm (Fin (Multiset.card M))) :
    wordProd (Multiset.card M) (terminalWord w) = w := (terminalWord_spec w).2

variable [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)
variable (ν)

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "A" => StendhalAlgebraAllOrders k Q Λ ν
local notation "P" => StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
local notation "E" => StendhalAlgebra.lastRedIdem Q Λ ν
local notation "π" => StendhalAlgebraAllOrders.ofKLR k Q Λ ν
local notation "Φ" => appendRedStendhalValue Q Λ ν
local notation "old" => StendhalAlgebra k Q (Λ ∘ Fin.castSucc) ν
local notation "J₀" => StendhalAlgebra.violatedIdeal k Q (Λ ∘ Fin.castSucc) ν
local notation "hρ" => terminalWord_prod (ν := ν) (ℓ := ℓ)
local notation "Term" => {b // IsStendhalTerm (ν := ν) (ℓ := ℓ + 1) terminalWord b}

private theorem factor_through_terminal_violation (b : Term) (hs : HasLastRed b.1.1)
    (hv : IsViolated (b.1.2.1 • b.1.1)) :
    ∃ (t : KLR.Seq M), IsRedOrdered t ∧ HasLastRed t ∧ IsViolated t ∧
      ∃ l r : A, (stendhalTerm Q Λ hρ b).val = l * StendhalAlgebraAllOrders.e t * r := by
  let s := b.1.1
  let w := b.1.2.1
  let a := w (lastRedPosition ℓ ν)
  let t := (wordProd (Multiset.card M) (terminalRest w)) • s
  let C := KLR.cycA (m := Multiset.card M) (n := N₀) a.val
  have hp : wordProd (Multiset.card M) (terminalPrefix w) = C⁻¹ := wordProd_reverse _ _
  have hw := (terminalWord_spec w).2
  change wordProd (Multiset.card M) (terminalPrefix w ++ terminalRest w) = w at hw
  rw [wordProd_append, hp] at hw
  have hrest : wordProd (Multiset.card M) (terminalRest w) = C * w := by
    simpa only [mul_inv_cancel_left] using congrArg (C * ·) hw
  have ht : t = C • (w • s) := by rw [← mul_smul, ← hrest]
  have ha : (w • s).lbl a = Sum.inr (Fin.last ℓ) := by
    change s.lbl (w.symm (w _)) = _
    rwa [w.symm_apply_apply]
  have h := slide_terminal_loading (w • s) b.2.2.1 hv a ha
  rw [← ht] at h
  refine ⟨t, h.1, h.2.1, h.2.2,
    π (ψw (terminalPrefix w)), π (ψw (terminalRest w) * pol (MvPolynomial.monomial b.1.2.2 1) *
      KLRAlgebra.e s), ?_⟩
  have hcut : (KLRAlgebra.e t : KLRAlgebra k (stendhalQ Q Λ) M) *
      (ψw (terminalRest w) * pol (MvPolynomial.monomial b.1.2.2 1) * KLRAlgebra.e s) =
      ψw (terminalRest w) * pol (MvPolynomial.monomial b.1.2.2 1) * KLRAlgebra.e s := by
    rw [e_mul_gen]
    simp [t]
  rw [stendhalTerm_val, stdElt]
  change π ((ψw (terminalPrefix w ++ terminalRest w)) * _ * KLRAlgebra.e s) =
    π _ * π (KLRAlgebra.e t) * π _
  rw [ψw_append, mul_assoc (π (ψw (terminalPrefix w))),
    ← map_mul π (KLRAlgebra.e t), hcut]
  simp only [map_mul, mul_assoc]

private theorem exists_ambient_sandwich_preimage (z : A) :
    ∃ v : old, (Φ v).val = (E).val * z * (E).val := by
  have hP : P * P = P := StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem.eq
  let x : StendhalAlgebra k Q Λ ν := ⟨P * z * P, (Subsemigroup.mem_corner_iff
    StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).2
    ⟨by rw [← mul_assoc, ← mul_assoc, hP], by rw [mul_assoc, hP]⟩⟩
  obtain ⟨v, hv⟩ := exists_appendRedStendhalValue Q Λ ν x
  refine ⟨v, (congrArg Subtype.val hv).trans ?_⟩
  change (E).val * (P * z * P) * (E).val = _
  calc
    _ = ((E).val * P) * z * (P * (E).val) := by simp only [mul_assoc]
    _ = _ := by rw [KLR.Corner.val_mul_E, KLR.Corner.E_mul_val]

private theorem exists_violated_preimage_of_terminal_cut (s : KLR.Seq M) (ho : IsRedOrdered s)
    (hs : HasLastRed s) (hV : IsViolated s) (x y : A) :
    ∃ v ∈ J₀, (Φ v).val = (E).val * x * StendhalAlgebraAllOrders.e s * y * (E).val := by
  classical
  obtain ⟨u, hu⟩ := (appendRedOrderedEquiv (ℓ := ℓ) (ν := ν)).surjective ⟨s, ho, hs⟩
  have he : appendRedLoading u.1 = s := congrArg Subtype.val hu
  have hv : IsViolated u.1 := (appendRedLoading_violated_iff u.1).1 (he.symm ▸ hV)
  let e₀ : old := StendhalAlgebra.e u.1 u.2
  have h₀ : e₀ ∈ J₀ := TwoSidedIdeal.subset_span ⟨u.1, u.2, hv, rfl⟩
  obtain ⟨g, hg⟩ := exists_ambient_sandwich_preimage ν Q Λ x
  obtain ⟨h, hh⟩ := exists_ambient_sandwich_preimage ν Q Λ y
  refine ⟨g * e₀ * h, TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ h₀), ?_⟩
  have he₀ : (Φ e₀).val = StendhalAlgebraAllOrders.e s := by
    rw [show e₀ = StendhalAlgebra.e u.1 u.2 from rfl, appendRedStendhalValue_e]
    change StendhalAlgebraAllOrders.e (appendRedLoading u.1) = _
    rw [he]
  have hl : (E).val * StendhalAlgebraAllOrders.e s = StendhalAlgebraAllOrders.e s := by
    exact congrArg (fun z : StendhalAlgebra k Q Λ ν => z.val) (by simpa [hs] using StendhalAlgebra.lastRedIdem_mul_e Q Λ ν s ho)
  have hr : StendhalAlgebraAllOrders.e s * (E).val = StendhalAlgebraAllOrders.e s := by
    exact congrArg (fun z : StendhalAlgebra k Q Λ ν => z.val) (by simpa [hs] using StendhalAlgebra.e_mul_lastRedIdem Q Λ ν s ho)
  rw [map_mul, map_mul, KLR.Corner.val_mul, KLR.Corner.val_mul, hg, hh, he₀]
  calc
    _ = (E).val * x * ((E).val * StendhalAlgebraAllOrders.e s * (E).val) * y * (E).val := by
      simp only [mul_assoc]
    _ = _ := by rw [hl, hr]

/-- The part of the violating ideal in the terminal corner is the image of the
earlier violating ideal (Webster, arXiv:1309.3796v2, Proposition 4.18, proof). -/
theorem exists_violated_appendRed (x : StendhalAlgebra k Q Λ ν)
    (hx : x ∈ StendhalAlgebra.violatedIdeal k Q Λ ν) :
    ∃ v ∈ J₀, Φ v = E * x * E := by
  classical
  have h := (mem_violatedIdeal_iff (Q := Q) (Λ := Λ)
    (terminalWord_spec (ℓ := ℓ) (ν := ν)) x).1 hx
  clear hx
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, c, hv, hs, rfl⟩ := hx
    by_cases hc : HasLastRed c.1.1
    · obtain ⟨s, ho, he, hV, l, r, hEq⟩ :=
        factor_through_terminal_violation ν Q Λ c hc (hs ▸ hv)
      obtain ⟨v, h₀, hval⟩ := exists_violated_preimage_of_terminal_cut ν Q Λ s ho he hV
        ((stendhalTerm Q Λ hρ b).val * l) r
      refine ⟨v, h₀, Subtype.ext ?_⟩
      rw [KLR.Corner.val_mul, KLR.Corner.val_mul, KLR.Corner.val_mul, hEq, hval]
      simp only [mul_assoc]
    · have he : stendhalTerm Q Λ hρ c * E = 0 := by
        have hc' : stendhalTerm Q Λ hρ c * StendhalAlgebra.e c.1.1 c.2.1 =
            stendhalTerm Q Λ hρ c := by rw [stendhalTerm_mul_e]; simp
        rw [← hc', mul_assoc, StendhalAlgebra.e_mul_lastRedIdem]
        simp [hc]
      exact ⟨0, zero_mem _, by rw [map_zero]; simp only [mul_assoc, he, mul_zero]⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, heu⟩ := hx
    obtain ⟨v, hv, hev⟩ := hy
    exact ⟨u + v, add_mem hu hv, by rw [map_add, heu, hev, mul_add, add_mul]⟩
  | smul c x _ hx =>
    obtain ⟨v, hv, he⟩ := hx
    refine ⟨c • v, ?_, ?_⟩
    · rw [Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ hv
    · rw [appendRedStendhalValue_smul, he, mul_smul_comm, smul_mul_assoc]

/-- Once appending is injective before quotienting, the terminal-cut calculation
in the proof of Webster's Proposition 4.18 gives injectivity on the violating quotient. -/
theorem appendRed_injective_of_stendhal (hΦ : Function.Injective Φ) :
    Function.Injective (appendRed Q Λ ν) := by
  intro x y hxy
  obtain ⟨b, rfl⟩ := (J₀).ringCon.mk'_surjective x
  obtain ⟨c, rfl⟩ := (J₀).ringCon.mk'_surjective y
  let J := StendhalAlgebra.violatedIdeal k Q Λ ν
  have he : J.ringCon.mk' (Φ b) = J.ringCon.mk' (Φ c) := congrArg Subtype.val hxy
  have hmem : Φ (b - c) ∈ J := by
    rw [map_sub]
    exact (TwoSidedIdeal.rel_iff _ _ _).1 (J.ringCon.eq.1 he)
  obtain ⟨v, hv, h⟩ := exists_violated_appendRed ν Q Λ (Φ (b - c)) hmem
  have hh : E * Φ (b-c) * E = Φ (b-c) := by
    rw [← appendRedStendhalValue_one, ← map_mul, one_mul, ← map_mul, mul_one]
  have heq := hΦ (h.trans hh)
  exact (J₀).ringCon.eq.2 ((TwoSidedIdeal.rel_iff _ _ _).2 (heq ▸ hv))

end Categorification.Stendhal
