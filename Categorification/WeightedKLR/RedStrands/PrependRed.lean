/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AddRed
import Categorification.WeightedKLR.RedStrands.OrderProjection

/-!
# Adding a red strand on the left

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
§4.7, proof of Proposition 4.39. The functor `r_N` adds a red strand on the left of
every diagram of `T̃^λ` and then imposes the violating ideal of the longer sequence of
red strands. Since the new red strand is leftmost, no loading of the image is violated
on account of the old strands.

This file constructs the underlying algebra map
`T̃^λ_ν → T^{(λ₀, λ)}_ν` in every black weight and proves that it is a surjective
homomorphism of graded algebras.

## Main definitions

* `prependRedLoading` : the loading with the new red strand added at the far left.
* `prependRedAllOrders` : adding the red strand to diagrams with arbitrary red orders,
  landing in the corner of loadings that begin with the new red strand.
* `prependRed` : the unital map `T̃^λ_ν → T^{(λ₀, λ)}_ν`.

## Main results

* `prependRed_surjective`, `prependRed_mem_grade`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR

variable {I : Type*} {ℓ : ℕ} {ν : Multiset I}

section Loadings

/-- Embed the old labels into the labels after a new first red strand is added. -/
abbrev prependRedColor (ℓ : ℕ) : I ⊕ Fin ℓ → I ⊕ Fin (ℓ + 1) :=
  Sum.map id Fin.succ

theorem prependRedColor_injective (ℓ : ℕ) : Function.Injective (prependRedColor (I := I) ℓ) :=
  Sum.map_injective.mpr ⟨fun _ _ h => h, Fin.succ_injective ℓ⟩

local notation "ν₀" => Multiset.map (prependRedColor ℓ) (stendhalWeight ℓ ν)
local notation "νᵣ" => ({Sum.inr 0} : Multiset (I ⊕ Fin (ℓ + 1)))

/-- Prepending the new red label adds it once and retains all earlier labels. -/
theorem stendhalWeight_prependRed : νᵣ + ν₀ = stendhalWeight (ℓ + 1) ν := by
  simp only [stendhalWeight, Multiset.map_add, Multiset.map_map, Function.comp_def,
    prependRedColor, Sum.map_inl, Sum.map_inr, id_eq]
  rw [Fin.univ_succ, Finset.cons_val, Multiset.map_cons, Finset.map_val, Multiset.map_map]
  rw [Multiset.singleton_add, Multiset.add_cons]
  rfl

/-- The loading of the new red strand alone. -/
def firstRedSeq (ℓ : ℕ) : Seq ({Sum.inr 0} : Multiset (I ⊕ Fin (ℓ + 1))) :=
  ⟨fun _ => .inr 0, by simp⟩

theorem firstRedSeq_lbl (a : Fin (Multiset.card νᵣ)) :
    (firstRedSeq (I := I) ℓ).lbl a = .inr 0 :=
  Multiset.mem_singleton.mp (Seq.mem _ a)

theorem firstRedSeq_unique (s : Seq νᵣ) : s = firstRedSeq (I := I) ℓ := by
  apply Subtype.ext
  funext a
  exact (Multiset.mem_singleton.mp (Seq.mem s a)).trans (firstRedSeq_lbl a).symm

/-- Add the new red strand before all existing strands. -/
def prependRedLoading (s : Seq (stendhalWeight ℓ ν)) : Seq (stendhalWeight (ℓ + 1) ν) :=
  Seq.cast stendhalWeight_prependRed ((firstRedSeq ℓ).append (Seq.map (prependRedColor ℓ) s))

/-- The first position, occupied by the new red strand. -/
def firstPosition (ℓ : ℕ) (ν : Multiset I) : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν)) :=
  ⟨0, by simp [stendhalWeight]⟩

/-- The position of an old strand after adding the new red strand on the left. -/
def prependRedPosition (a : Fin (Multiset.card (stendhalWeight ℓ ν))) :
    Fin (Multiset.card (stendhalWeight (ℓ + 1) ν)) :=
  Fin.cast (congrArg Multiset.card stendhalWeight_prependRed)
    (Seq.posR νᵣ (Fin.cast (Multiset.card_map (prependRedColor ℓ) (stendhalWeight ℓ ν)).symm a))

@[simp] theorem prependRedPosition_val (a : Fin (Multiset.card (stendhalWeight ℓ ν))) :
    (prependRedPosition a).val = a.val + 1 := by
  change Multiset.card νᵣ + a.val = a.val + 1
  simp [add_comm]

theorem prependRedLoading_lbl (s : Seq (stendhalWeight ℓ ν))
    (a : Fin (Multiset.card (stendhalWeight ℓ ν))) :
    (prependRedLoading s).lbl (prependRedPosition a) = prependRedColor ℓ (s.lbl a) := by
  simp only [prependRedLoading, prependRedPosition, Seq.cast_apply, Fin.cast_cast,
    Fin.cast_eq_self, Seq.append_posR, Seq.map_lbl]

theorem prependRedLoading_head (s : Seq (stendhalWeight ℓ ν)) :
    (prependRedLoading s).lbl (firstPosition ℓ ν) = .inr 0 := by
  have hpos : firstPosition ℓ ν = Fin.cast (congrArg Multiset.card stendhalWeight_prependRed)
      (Seq.posL ν₀ (⟨0, by simp⟩ : Fin (Multiset.card νᵣ))) := Fin.ext rfl
  rw [hpos]
  simp only [prependRedLoading, Seq.cast_apply, Fin.cast_cast, Fin.cast_eq_self, Seq.append_posL,
    firstRedSeq_lbl]

theorem eq_firstPosition_or (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) :
    a = firstPosition ℓ ν ∨ ∃ b, a = prependRedPosition b := by
  rcases ha : a.val with _ | n
  · exact Or.inl (Fin.ext ha)
  · refine Or.inr ⟨⟨n, ?_⟩, Fin.ext (by simp [ha])⟩
    have := a.isLt
    simp [stendhalWeight] at this ⊢
    omega

theorem prependRedColor_eq_inr {c : I ⊕ Fin ℓ} {r : Fin (ℓ + 1)}
    (h : prependRedColor ℓ c = .inr r) : ∃ q, c = .inr q ∧ Fin.succ q = r := by
  cases c with
  | inl i => cases h
  | inr q => exact ⟨q, rfl, Sum.inr.inj h⟩

theorem prependRedColor_isLeft (c : I ⊕ Fin ℓ) :
    (prependRedColor ℓ c).isLeft = c.isLeft := by
  cases c <;> rfl

theorem prependRedColor_isRight (c : I ⊕ Fin ℓ) :
    (prependRedColor ℓ c).isRight = c.isRight := by
  cases c <;> rfl

/-- The new red strand carries the smallest label and the old labels keep their order. -/
theorem prependRedLoading_ordered_iff (s : Seq (stendhalWeight ℓ ν)) :
    IsRedOrdered (prependRedLoading s) ↔ IsRedOrdered s := by
  constructor
  · intro h a b r r' hab ha hb
    have h₁ : (prependRedLoading s).lbl (prependRedPosition a) = .inr (Fin.succ r) := by
      rw [prependRedLoading_lbl, ha]
      rfl
    have h₂ : (prependRedLoading s).lbl (prependRedPosition b) = .inr (Fin.succ r') := by
      rw [prependRedLoading_lbl, hb]
      rfl
    have := h (prependRedPosition a) (prependRedPosition b) _ _
      (by rw [Fin.lt_def, prependRedPosition_val, prependRedPosition_val]
          exact Nat.succ_lt_succ (Fin.lt_def.mp hab))
      h₁ h₂
    exact Fin.succ_lt_succ_iff.mp this
  · intro h a b r r' hab ha hb
    rcases eq_firstPosition_or b with rfl | ⟨b, rfl⟩
    · exact (Nat.not_lt_zero _ hab).elim
    rw [prependRedLoading_lbl] at hb
    obtain ⟨q', hq', rfl⟩ := prependRedColor_eq_inr hb
    rcases eq_firstPosition_or a with rfl | ⟨a, rfl⟩
    · rw [prependRedLoading_head] at ha
      cases ha
      exact Fin.succ_pos q'
    rw [prependRedLoading_lbl] at ha
    obtain ⟨q, hq, rfl⟩ := prependRedColor_eq_inr ha
    have hab' : a < b := by
      rw [Fin.lt_def] at hab ⊢
      simp only [prependRedPosition_val] at hab
      omega
    exact Fin.succ_lt_succ_iff.mpr (h a b q q' hab' hq hq')

/-- A loading beginning with the new red strand is never violated. -/
theorem not_violated_prependRedLoading (s : Seq (stendhalWeight ℓ ν)) :
    ¬ IsViolated (prependRedLoading s) := by
  rintro ⟨h, ha⟩
  rw [show (⟨0, h⟩ : Fin _) = firstPosition ℓ ν from rfl, prependRedLoading_head] at ha
  cases ha

theorem prependRedLoading_injective :
    Function.Injective (prependRedLoading (ℓ := ℓ) (ν := ν)) := by
  intro s t h
  apply Subtype.ext
  funext a
  apply prependRedColor_injective ℓ
  exact (prependRedLoading_lbl s a).symm.trans
    ((congrArg (fun u => u.lbl (prependRedPosition a)) h).trans (prependRedLoading_lbl t a))

/-- Every loading that begins with the new red strand is obtained by prepending it. -/
theorem prependRedLoading_surjOn
    (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : s.lbl (firstPosition ℓ ν) = .inr 0) :
    ∃ t, prependRedLoading t = s := by
  let h := stendhalWeight_prependRed (ℓ := ℓ) (ν := ν)
  let s' := Seq.cast h.symm s
  have hr (a : Fin (Multiset.card νᵣ)) : s'.lbl (Seq.posL ν₀ a) = .inr 0 := by
    change s.lbl (Fin.cast (congrArg Multiset.card h) (Seq.posL ν₀ a)) = _
    have hpos : Fin.cast (congrArg Multiset.card h) (Seq.posL ν₀ a) = firstPosition ℓ ν := by
      apply Fin.ext
      change a.val = 0
      have ha := a.isLt
      have hc : Multiset.card νᵣ = 1 := Multiset.card_singleton _
      omega
    rw [hpos]
    exact hs
  let lbl : Fin (Multiset.card (νᵣ + ν₀)) → I ⊕ Fin (ℓ + 1) := s'.lbl
  have hleft : Finset.univ.val.map (lbl ∘ Seq.posL ν₀) = νᵣ := by
    rw [show lbl ∘ Seq.posL ν₀ = fun _ => Sum.inr 0 from funext hr]
    simp
  have hsplit : Finset.univ.val.map lbl =
      Finset.univ.val.map (lbl ∘ Seq.posL ν₀) + Finset.univ.val.map (lbl ∘ Seq.posR νᵣ) := by
    conv_lhs => rw [← Multiset.map_univ_val_equiv (TypeA.blockEquiv (Seq.card_add' νᵣ ν₀))]
    rw [Multiset.map_map, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum,
      Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rfl
  have hs' : Finset.univ.val.map lbl = νᵣ + ν₀ := s'.2
  rw [hs', hleft] at hsplit
  let t' : Seq ν₀ := ⟨_, (add_left_cancel hsplit).symm⟩
  obtain ⟨t, ht⟩ := (Seq.map_bijective (prependRedColor_injective ℓ) (stendhalWeight ℓ ν)).2 t'
  have hst : (firstRedSeq ℓ).append t' = s' := by
    apply Subtype.ext
    funext a
    obtain ⟨a, rfl⟩ := (TypeA.blockEquiv (Seq.card_add' νᵣ ν₀)).surjective a
    cases a with
    | inl a =>
      exact (Seq.append_posL _ _ a).trans ((firstRedSeq_lbl a).trans (hr a).symm)
    | inr a => exact Seq.append_posR _ _ a
  refine ⟨t, ?_⟩
  rw [prependRedLoading, ht, hst]
  rfl

/-- A red-ordered loading is either violated or begins with the first red strand. -/
theorem violated_or_head_of_ordered (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s) :
    IsViolated s ∨ s.lbl (firstPosition ℓ ν) = .inr 0 := by
  cases h : s.lbl (firstPosition ℓ ν) with
  | inl i => exact Or.inl ⟨by simp [stendhalWeight], by
      rw [show (⟨0, _⟩ : Fin _) = firstPosition ℓ ν from rfl, h]; rfl⟩
  | inr r =>
    refine Or.inr (congrArg Sum.inr ?_)
    obtain ⟨a, ha⟩ := exists_lbl_eq_inr s 0
    by_contra hr
    rcases eq_firstPosition_or a with rfl | ⟨b, rfl⟩
    · exact hr (Sum.inr.inj (h.symm.trans ha))
    · have := hs (firstPosition ℓ ν) (prependRedPosition b) r 0
        (by rw [Fin.lt_def, prependRedPosition_val]; exact Nat.succ_pos _) h ha
      exact (Fin.not_lt_zero r this).elim

end Loadings

section PrependDiagrams

open KLRAlgebra

variable [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

local notation "Λ₀" => (Λ ∘ Fin.succ)
local notation "μ" => stendhalWeight ℓ ν
local notation "ν₀" => Multiset.map (prependRedColor ℓ) μ
local notation "νᵣ" => ({Sum.inr 0} : Multiset (I ⊕ Fin (ℓ + 1)))
local notation "S" => stendhalQ Q Λ
local notation "A" => StendhalAlgebraAllOrders k Q Λ ν

private def prependRedRelabel :
    SeqRelabel k (stendhalQ Q Λ₀) S μ ν₀ :=
  let R := SeqRelabel.ofInjective (prependRedColor_injective (I := I) ℓ) S μ
  { card_eq := R.card_eq
    equiv := R.equiv
    equiv_smul := R.equiv_smul
    lbl_eq_iff := R.lbl_eq_iff
    Q_eq := fun i a b hab =>
      (R.Q_eq i a b hab).trans (by
        cases i.lbl a <;> cases i.lbl b <;> rfl) }

private def prependRedAmbient : KLRAlgebra k S (νᵣ + ν₀) →ₐ[k] A :=
  (StendhalAlgebraAllOrders.ofKLR k Q Λ ν).comp
    (castKLR S (stendhalWeight_prependRed (ℓ := ℓ) (ν := ν))).toAlgHom

/-- The sum of the idempotents of loadings beginning with the new red strand. -/
def firstRedIdem : A :=
  prependRedAmbient Q Λ ν (oneConcat S νᵣ ν₀)

theorem isIdempotentElem_firstRedIdem : IsIdempotentElem (firstRedIdem Q Λ ν) :=
  (oneConcat_idem (Q := S) (ν := νᵣ) (ν' := ν₀)).map (prependRedAmbient Q Λ ν)

/-- The first-red idempotent is the sum over the loadings obtained by prepending. -/
theorem firstRedIdem_eq_sum :
    firstRedIdem Q Λ ν = ∑ s : Seq μ, StendhalAlgebraAllOrders.e (prependRedLoading s) := by
  classical
  rw [firstRedIdem, oneConcat_eq, map_sum, Fintype.sum_prod_type,
    Fintype.sum_eq_single (firstRedSeq ℓ) (fun a ha => (ha (firstRedSeq_unique a)).elim)]
  symm
  apply Fintype.sum_bijective (Seq.map (prependRedColor ℓ))
    (Seq.map_bijective (prependRedColor_injective ℓ) _)
  intro s
  rw [prependRedAmbient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, castKLR_e]
  rfl

instance (priority := 1200) firstRedCornerAlgebra :
    Algebra k (isIdempotentElem_firstRedIdem Q Λ ν).Corner :=
  KLR.cornerAlgebra _


private def prependRedConcatCorner :
    ConcatCorner S νᵣ ν₀ →ₐ[k] (isIdempotentElem_firstRedIdem Q Λ ν).Corner where
  toFun z := KLR.Corner.mk (prependRedAmbient Q Λ ν z.val) (by
    have hz : oneConcat S νᵣ ν₀ * z.val * oneConcat S νᵣ ν₀ = z.val :=
      (congrArg (· * oneConcat S νᵣ ν₀) (KLR.Corner.E_mul_val z)).trans
        (KLR.Corner.val_mul_E z)
    simpa only [map_mul, firstRedIdem] using congrArg (prependRedAmbient Q Λ ν) hz)
  map_one' := rfl
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)
  commutes' c := Subtype.ext (by
    change prependRedAmbient Q Λ ν (algebraMap k _ c * oneConcat S νᵣ ν₀) =
      algebraMap k A c * firstRedIdem Q Λ ν
    rw [map_mul, AlgHom.commutes]
    rfl)

private def prependRedKLR :
    KLRAlgebra k (stendhalQ Q Λ₀) μ →ₐ[k] (isIdempotentElem_firstRedIdem Q Λ ν).Corner :=
  (prependRedConcatCorner Q Λ ν).comp (((blockR νᵣ ν₀).hom S).comp
    (relabelHom (prependRedRelabel Q Λ ν)))

private theorem blockR_prependRed_fibre (s : Seq ν₀) :
    (blockR νᵣ ν₀).F s = {(firstRedSeq ℓ).append s} := by
  classical
  ext t
  change t ∈ Finset.univ.image (fun a : Seq νᵣ => a.append s) ↔ _
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [firstRedSeq_unique a]
  · intro h
    exact ⟨firstRedSeq ℓ, h.symm⟩

private theorem prependRedKLR_val (z : KLRAlgebra k (stendhalQ Q Λ₀) μ) :
    (prependRedKLR Q Λ ν z).val =
      prependRedAmbient Q Λ ν (((blockR νᵣ ν₀).hom S)
        (relabelHom (prependRedRelabel Q Λ ν) z)).val := rfl

private theorem prependRedKLR_e (s : Seq μ) :
    (prependRedKLR Q Λ ν (KLRAlgebra.e s)).val =
      StendhalAlgebraAllOrders.e (prependRedLoading s) := by
  rw [prependRedKLR_val, relabelHom_e, BlockEmb.hom_e, BlockEmb.val_gE]
  change prependRedAmbient Q Λ ν (eSum S ((blockR νᵣ ν₀).F (Seq.map (prependRedColor ℓ) s))) = _
  rw [blockR_prependRed_fibre, eSum, Finset.sum_singleton, prependRedAmbient, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, castKLR_e]
  rfl

private theorem prependRedKLR_x (a : Fin (Multiset.card μ)) :
    (prependRedKLR Q Λ ν (KLRAlgebra.x a)).val =
      StendhalAlgebraAllOrders.x (prependRedPosition a) * firstRedIdem Q Λ ν := by
  rw [prependRedKLR_val, relabelHom_x, BlockEmb.hom_x, val_polCorner, pol_X, map_mul]
  congr 1
  rw [prependRedAmbient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, castKLR_x]
  rfl

private theorem prependRedKLR_ψ {j : ℕ} (hj : j + 1 < Multiset.card μ) :
    (prependRedKLR Q Λ ν (KLRAlgebra.ψ j)).val =
      StendhalAlgebraAllOrders.ψ (j + 1) * firstRedIdem Q Λ ν := by
  have hj' : j + 1 < Multiset.card ν₀ := by simpa using hj
  rw [prependRedKLR_val, relabelHom_ψ, BlockEmb.hom_ψ, BlockEmb.val_gψ _ hj', map_mul]
  congr 1
  rw [prependRedAmbient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, castKLR_ψ]
  simp [StendhalAlgebraAllOrders.ψ, add_comm]

/-- Add the new red strand on the left of a diagram, before imposing the violating
ideal. The corner is the sum of the loadings that begin with the new red strand. -/
def prependRedAllOrders :
    StendhalAlgebraAllOrders k Q Λ₀ ν →ₐ[k] (isIdempotentElem_firstRedIdem Q Λ ν).Corner :=
  RingQuot.liftAlgHom k
    ⟨(prependRedKLR Q Λ ν).comp (KLRAlgebra.mk k (stendhalQ Q Λ₀) μ), fun x y h => by
      cases h with
      | klr h =>
        exact congrArg (prependRedKLR Q Λ ν) (RingQuot.mkAlgHom_rel k h)
      | red_dot a s ha =>
        apply KLR.Corner.ext
        simp only [AlgHom.comp_apply, map_mul, map_zero, KLR.Corner.val_mul, KLR.Corner.val_zero]
        change (prependRedKLR Q Λ ν (KLRAlgebra.x a)).val *
          (prependRedKLR Q Λ ν (KLRAlgebra.e s)).val = 0
        have hs := KLR.Corner.E_mul_val (prependRedKLR Q Λ ν (KLRAlgebra.e s))
        rw [prependRedKLR_e] at hs
        rw [prependRedKLR_x, prependRedKLR_e, mul_assoc]
        change StendhalAlgebraAllOrders.x (prependRedPosition a) *
          (firstRedIdem Q Λ ν * StendhalAlgebraAllOrders.e (prependRedLoading s)) = _
        rw [hs]
        have ha' : ((prependRedLoading s).lbl (prependRedPosition a)).isRight := by
          simpa only [prependRedLoading_lbl, prependRedColor_isRight] using ha
        exact StendhalAlgebraAllOrders.x_mul_e_of_red (prependRedPosition a)
          (prependRedLoading s) ha'
      | red_cross j hj s ha hb =>
        apply KLR.Corner.ext
        simp only [AlgHom.comp_apply, map_mul, map_zero, KLR.Corner.val_mul, KLR.Corner.val_zero]
        change (prependRedKLR Q Λ ν (KLRAlgebra.ψ j)).val *
          (prependRedKLR Q Λ ν (KLRAlgebra.e s)).val = 0
        have hs := KLR.Corner.E_mul_val (prependRedKLR Q Λ ν (KLRAlgebra.e s))
        rw [prependRedKLR_e] at hs
        rw [prependRedKLR_ψ Q Λ ν hj, prependRedKLR_e, mul_assoc]
        change StendhalAlgebraAllOrders.ψ (j + 1) *
          (firstRedIdem Q Λ ν * StendhalAlgebraAllOrders.e (prependRedLoading s)) = _
        rw [hs]
        have hj' : j + 1 + 1 < Multiset.card (stendhalWeight (ℓ + 1) ν) := by
          simp [stendhalWeight] at hj ⊢
          omega
        have ha' : ((prependRedLoading s).lbl ⟨j + 1, by omega⟩).isRight := by
          rw [show (⟨j + 1, by omega⟩ : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) =
            prependRedPosition ⟨j, by omega⟩ from Fin.ext (by simp),
            prependRedLoading_lbl, prependRedColor_isRight]
          exact ha
        have hb' : ((prependRedLoading s).lbl ⟨j + 1 + 1, hj'⟩).isRight := by
          rw [show (⟨j + 1 + 1, hj'⟩ : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) =
            prependRedPosition ⟨j + 1, hj⟩ from Fin.ext (by simp),
            prependRedLoading_lbl, prependRedColor_isRight]
          exact hb
        exact StendhalAlgebraAllOrders.ψ_mul_e_of_red (j + 1) hj' (prependRedLoading s) ha' hb'⟩

private theorem prependRedAllOrders_ofKLR (z : KLRAlgebra k (stendhalQ Q Λ₀) μ) :
    prependRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.ofKLR k Q Λ₀ ν z) =
      prependRedKLR Q Λ ν z := by
  obtain ⟨w, rfl⟩ := KLRAlgebra.mk_surjective z
  rw [StendhalAlgebraAllOrders.ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem prependRedAllOrders_e (s : Seq μ) :
    (prependRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.e s)).val =
      StendhalAlgebraAllOrders.e (prependRedLoading s) := by
  rw [StendhalAlgebraAllOrders.e, prependRedAllOrders_ofKLR, prependRedKLR_e]

theorem prependRedAllOrders_x (a : Fin (Multiset.card μ)) :
    (prependRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.x a)).val =
      StendhalAlgebraAllOrders.x (prependRedPosition a) * firstRedIdem Q Λ ν := by
  rw [StendhalAlgebraAllOrders.x, prependRedAllOrders_ofKLR, prependRedKLR_x]

theorem prependRedAllOrders_ψ (j : ℕ) (hj : j + 1 < Multiset.card μ) :
    (prependRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.ψ j)).val =
      StendhalAlgebraAllOrders.ψ (j + 1) * firstRedIdem Q Λ ν := by
  rw [StendhalAlgebraAllOrders.ψ, prependRedAllOrders_ofKLR, prependRedKLR_ψ Q Λ ν hj]

theorem prependRedAllOrders_one :
    (prependRedAllOrders Q Λ ν 1).val = firstRedIdem Q Λ ν := by
  rw [map_one]
  rfl

/-- The grading on the old red strands obtained by omitting the first red colour
(Webster, arXiv:1309.3796v3, Definition 4.4). -/
def restrictFirstRedGrading (G : GradingDatum S) : GradingDatum (stendhalQ Q Λ₀) where
  degX a := G.degX (prependRedColor ℓ a)
  degΨ a b := G.degΨ (prependRedColor ℓ a) (prependRedColor ℓ b)
  degΨ_self a := G.degΨ_self _
  isWeightedHomogeneous a b hab := by
    have h := G.isWeightedHomogeneous _ _ (fun he => hab (prependRedColor_injective ℓ he))
    cases a <;> cases b <;> exact h

private theorem prependRedRelabel_coaction (G : GradingDatum S)
    (z : KLRAlgebra k (stendhalQ Q Λ₀) μ) :
    G.coaction (relabelHom (prependRedRelabel Q Λ ν) z) =
      AddMonoidAlgebra.mapAlgHom ℤ (relabelHom (prependRedRelabel Q Λ ν))
        ((restrictFirstRedGrading Q Λ G).coaction z) := by
  classical
  let R := prependRedRelabel Q Λ ν
  induction z using klr_induction with
  | hr r => simp only [AlgHom.commutes]
  | hadd x y h₁ h₂ => simp only [map_add, h₁, h₂]
  | hmul x y h₁ h₂ => simp only [map_mul, h₁, h₂]
  | he s => simp only [relabelHom_e, GradingDatum.coaction_e, AddMonoidAlgebra.mapAlgHom_single]
  | hx a =>
    simp only [relabelHom_x, GradingDatum.coaction_x, map_sum, AddMonoidAlgebra.mapAlgHom_single,
      map_mul, relabelHom_e]
    symm
    apply Fintype.sum_equiv R.equiv
    intro s
    rfl
  | hψ j =>
    simp only [relabelHom_ψ, GradingDatum.coaction_ψ, map_sum, AddMonoidAlgebra.mapAlgHom_single,
      map_mul, relabelHom_e]
    symm
    apply Fintype.sum_equiv R.equiv
    intro s
    congr 1
    by_cases hj : j + 1 < Multiset.card μ
    · have hj' : j + 1 < Multiset.card ν₀ := by simpa using hj
      rw [GradingDatum.dψ_of_lt _ hj, G.dψ_of_lt hj']
      rfl
    · simp [GradingDatum.dψ, hj]

/-- Adding the first red strand preserves diagram degrees (Webster, arXiv:1309.3796v3,
Definition 4.4). -/
theorem prependRedAllOrders_mem_grade (G : GradingDatum S) {d : ℤ}
    {z : StendhalAlgebraAllOrders k Q Λ₀ ν}
    (hz : z ∈ allOrdersGrade (restrictFirstRedGrading Q Λ G) ν d) :
    (prependRedAllOrders Q Λ ν z).val ∈ allOrdersGrade G ν d := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  change (prependRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.ofKLR k Q Λ₀ ν a)).val ∈ _
  rw [prependRedAllOrders_ofKLR, prependRedKLR_val]
  apply Graded.mem_map_of_mem
  apply G.castKLR_mem_grade
  apply (blockR νᵣ ν₀).valHom_mem_grade
  rw [GradingDatum.mem_grade, prependRedRelabel_coaction,
    (restrictFirstRedGrading Q Λ G).mem_grade.mp ha, AddMonoidAlgebra.mapAlgHom_single]

end PrependDiagrams

section Quotient

open KLRAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

local notation "Λ₀" => (Λ ∘ Fin.succ)
local notation "μ" => stendhalWeight ℓ ν
local notation "μ'" => stendhalWeight (ℓ + 1) ν
local notation "A" => StendhalAlgebraAllOrders k Q Λ ν
local notation "T" => TensorProductAlgebra k Q Λ ν

/-- Cut by the red-ordered idempotent and impose the violating ideal. -/
def orderedQuotient : A →ₐ[k] T :=
  (TensorProductAlgebra.mk Q Λ ν).comp (orderProjection Q Λ ν)

open Classical in
theorem orderedQuotient_e (t : Seq μ') :
    orderedQuotient Q Λ ν (StendhalAlgebraAllOrders.e t) =
      if h : IsRedOrdered t then TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t h) else 0 := by
  classical
  have hv : (orderProjection Q Λ ν (StendhalAlgebraAllOrders.e t)).val =
      if IsRedOrdered t then StendhalAlgebraAllOrders.e t else 0 :=
    StendhalAlgebraAllOrders.e_mul_redOrderedIdem t
  by_cases h : IsRedOrdered t
  · simp only [h, ↓reduceDIte]
    change TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν _) = _
    congr 1
    exact Subtype.ext (by rw [hv]; simp [h]; rfl)
  · simp only [h, ↓reduceDIte]
    change TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν _) = 0
    rw [show orderProjection Q Λ ν (StendhalAlgebraAllOrders.e t) = 0 from
      Subtype.ext (by rw [hv]; simp [h]), map_zero]

theorem tensorProduct_mk_e_of_violated (t : Seq μ') (ht : IsRedOrdered t) (hv : IsViolated t) :
    TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht) = 0 := by
  change (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk' (StendhalAlgebra.e t ht) = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  exact TwoSidedIdeal.subset_span ⟨t, ht, hv, rfl⟩

/-- Only the loadings beginning with the new red strand survive the ordered quotient. -/
theorem orderedQuotient_e_eq_zero (t : Seq μ') (ht : ∀ s, prependRedLoading s ≠ t) :
    orderedQuotient Q Λ ν (StendhalAlgebraAllOrders.e t) = 0 := by
  classical
  rw [orderedQuotient_e]
  split_ifs with h
  · rcases violated_or_head_of_ordered t h with hv | hh
    · exact tensorProduct_mk_e_of_violated Q Λ ν t h hv
    · obtain ⟨s, hs⟩ := prependRedLoading_surjOn t hh
      exact (ht s hs).elim
  · rfl

theorem sum_orderedQuotient_prependRedLoading :
    ∑ s : Seq μ, orderedQuotient Q Λ ν (StendhalAlgebraAllOrders.e (prependRedLoading s)) = 1 := by
  classical
  have h1 : ∑ t : Seq μ', orderedQuotient Q Λ ν (StendhalAlgebraAllOrders.e t) = 1 := by
    rw [← map_sum, ← map_one (orderedQuotient Q Λ ν)]
    congr 1
    simp only [StendhalAlgebraAllOrders.e, ← map_sum, KLRAlgebra.sum_e, map_one]
  rw [← h1, ← Finset.sum_image (f := fun t => orderedQuotient Q Λ ν (StendhalAlgebraAllOrders.e t))
    (fun s _ t _ h => prependRedLoading_injective h)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro t _ ht
  apply orderedQuotient_e_eq_zero
  intro s hs
  exact ht (Finset.mem_image.2 ⟨s, Finset.mem_univ _, hs⟩)

open Classical in
private theorem redOrderedIdem_eq_sum_ite {n : ℕ} (Λ' : Fin n → I →₀ ℕ) :
    StendhalAlgebraAllOrders.redOrderedIdem k Q Λ' ν =
      ∑ s, if IsRedOrdered s then StendhalAlgebraAllOrders.e s else 0 := by
  rw [StendhalAlgebraAllOrders.redOrderedIdem, Finset.sum_filter]

private def prependRedValue : StendhalAlgebraAllOrders k Q Λ₀ ν →ₙ+* A :=
  (KLR.cornerVal (isIdempotentElem_firstRedIdem Q Λ ν)).comp
    (prependRedAllOrders Q Λ ν).toRingHom.toNonUnitalRingHom

private theorem prependRedValue_apply (z : StendhalAlgebraAllOrders k Q Λ₀ ν) :
    prependRedValue Q Λ ν z = (prependRedAllOrders Q Λ ν z).val := rfl

private theorem prependRedValue_smul (c : k) (z : StendhalAlgebraAllOrders k Q Λ₀ ν) :
    prependRedValue Q Λ ν (c • z) = c • prependRedValue Q Λ ν z := by
  rw [prependRedValue_apply, prependRedValue_apply, AlgHom.map_smul_of_tower, KLR.Corner.val_smul]

private theorem orderedQuotient_prependRedValue_redOrderedIdem :
    orderedQuotient Q Λ ν
      (prependRedValue Q Λ ν (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν)) = 1 := by
  classical
  rw [← sum_orderedQuotient_prependRedLoading Q Λ ν]
  rw [redOrderedIdem_eq_sum_ite (Λ' := Λ ∘ Fin.succ), map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs with h
  · rw [prependRedValue_apply, prependRedAllOrders_e]
  · rw [map_zero, map_zero, orderedQuotient_e]
    simp only [show ¬ IsRedOrdered (prependRedLoading s) from
      fun h' => h ((prependRedLoading_ordered_iff s).1 h'), ↓reduceDIte]

/-- **Adding a red strand on the left** (Webster, arXiv:1309.3796v3, proof of
Proposition 4.39): the algebra map `T̃^λ_ν → T^{(λ₀, λ)}_ν`, where the new red strand
carries the first label. -/
def prependRed : StendhalAlgebra k Q Λ₀ ν →ₐ[k] T where
  toFun z := orderedQuotient Q Λ ν (prependRedValue Q Λ ν z.val)
  map_one' := orderedQuotient_prependRedValue_redOrderedIdem Q Λ ν
  map_zero' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    change orderedQuotient Q Λ ν (prependRedValue Q Λ ν (x.val * y.val)) = _
    rw [map_mul, map_mul]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one c]
    change orderedQuotient Q Λ ν (prependRedValue Q Λ ν
      (c • StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν)) = _
    rw [prependRedValue_smul, map_smul, orderedQuotient_prependRedValue_redOrderedIdem,
      Algebra.algebraMap_eq_smul_one]

theorem prependRed_apply (z : StendhalAlgebra k Q Λ₀ ν) :
    prependRed Q Λ ν z = orderedQuotient Q Λ ν (prependRedAllOrders Q Λ ν z.val).val := rfl

/-- `prependRed` preserves diagram degrees, for the grading of `T̃^λ` obtained by omitting
the first red colour (Webster, arXiv:1309.3796v3, Definition 4.4). -/
theorem prependRed_mem_grade (G : GradingDatum (stendhalQ Q Λ)) {d : ℤ}
    {z : StendhalAlgebra k Q Λ₀ ν}
    (hz : z ∈ stendhalGrade (restrictFirstRedGrading Q Λ G) ν d) :
    prependRed Q Λ ν z ∈ tensorProductGrade G ν d := by
  rw [prependRed_apply, orderedQuotient, AlgHom.comp_apply]
  apply Graded.mem_map_of_mem (stendhalGrade G ν) (TensorProductAlgebra.mk Q Λ ν).toLinearMap
  change (prependRedAllOrders Q Λ ν z.val).val * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν ∈
    allOrdersGrade G ν d
  have hE : StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν ∈ allOrdersGrade G ν 0 :=
    Submodule.sum_mem _ fun i _ => Graded.mem_map_of_mem _ _ (G.e_mem_grade i)
  simpa using SetLike.GradedMul.mul_mem
    (prependRedAllOrders_mem_grade Q Λ ν G (show z.val ∈ _ from hz)) hE

private theorem orderedQuotient_firstRedIdem : orderedQuotient Q Λ ν (firstRedIdem Q Λ ν) = 1 := by
  rw [firstRedIdem_eq_sum, map_sum, sum_orderedQuotient_prependRedLoading]

private theorem orderedQuotient_mul_firstRedIdem (u : A) :
    orderedQuotient Q Λ ν (u * firstRedIdem Q Λ ν) = orderedQuotient Q Λ ν u := by
  rw [map_mul, orderedQuotient_firstRedIdem, mul_one]

private theorem prependRed_orderProjection (w : StendhalAlgebraAllOrders k Q Λ₀ ν) :
    prependRed Q Λ ν (orderProjection Q Λ₀ ν w) =
      orderedQuotient Q Λ ν (prependRedAllOrders Q Λ ν w).val := by
  rw [prependRed_apply]
  change orderedQuotient Q Λ ν (prependRedValue Q Λ ν
      (w * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν)) =
    orderedQuotient Q Λ ν (prependRedValue Q Λ ν w)
  rw [map_mul, map_mul, orderedQuotient_prependRedValue_redOrderedIdem, mul_one]

private theorem orderedQuotient_surjective : Function.Surjective (orderedQuotient Q Λ ν) := by
  intro y
  obtain ⟨z, rfl⟩ : ∃ z, TensorProductAlgebra.mk Q Λ ν z = y :=
    RingCon.mkₐ_surjective _ y
  obtain ⟨u, rfl⟩ := orderProjection_surjective Q Λ ν z
  exact ⟨u, rfl⟩

omit [DecidableEq I] in
private theorem prependRedLoading_ne_sadj (h1 : 1 < Multiset.card μ') (s s' : Seq μ) :
    prependRedLoading s' ≠ TypeA.sadj (Multiset.card μ') 0 • prependRedLoading s := by
  intro hs'
  have h0 : 0 < Multiset.card μ := by
    have : Multiset.card μ' = Multiset.card μ + 1 := by simp [stendhalWeight]; omega
    omega
  have hl : (prependRedLoading s').1 (firstPosition ℓ ν) =
      (TypeA.sadj (Multiset.card μ') 0 • prependRedLoading s).1 (firstPosition ℓ ν) := by
    rw [hs']
  have hpos : TypeA.sadj (Multiset.card μ') 0 (firstPosition ℓ ν) = prependRedPosition ⟨0, h0⟩ :=
    Fin.ext (by rw [show firstPosition ℓ ν = ⟨0, by omega⟩ from rfl, TypeA.sadj_apply_left h1]; simp)
  rw [show (prependRedLoading s').1 (firstPosition ℓ ν) = Sum.inr 0 from
    prependRedLoading_head s', KLRAlgebra.sadj_smul_apply, hpos] at hl
  have hc := (prependRedLoading_lbl s ⟨0, h0⟩).symm.trans hl.symm
  cases hs0 : s.lbl ⟨0, h0⟩ with
  | inl i => rw [hs0] at hc; exact Sum.inl_ne_inr hc
  | inr r => rw [hs0] at hc; exact Fin.succ_ne_zero r (Sum.inr.inj hc)

/-- **Adding a red strand on the left is surjective** (Webster, arXiv:1309.3796v3, proof of
Proposition 4.39): in `T^{(λ₀, λ)}` every surviving loading begins with the new red strand,
and crossing it with the first black strand produces a violated loading. -/
theorem prependRed_surjective : Function.Surjective (prependRed Q Λ ν) := by
  classical
  have hm : Multiset.card μ' = Multiset.card μ + 1 := by simp [stendhalWeight]; omega
  have key : ∀ u : A, orderedQuotient Q Λ ν u ∈ (prependRed Q Λ ν).range := by
    intro u
    obtain ⟨b, rfl⟩ := StendhalAlgebraAllOrders.ofKLR_surjective (k := k) (Q := Q) (Λ := Λ)
      (ν := ν) u
    induction b using KLRAlgebra.klr_induction with
    | hadd u v hu hv => rw [map_add, map_add]; exact add_mem hu hv
    | hmul u v hu hv => rw [map_mul, map_mul]; exact mul_mem hu hv
    | hr c => rw [AlgHom.commutes, AlgHom.commutes]; exact algebraMap_mem _ c
    | he t =>
      by_cases ht : ∃ s, prependRedLoading s = t
      · obtain ⟨s, rfl⟩ := ht
        refine (AlgHom.mem_range _).mpr ⟨orderProjection Q Λ₀ ν (StendhalAlgebraAllOrders.e s), ?_⟩
        rw [prependRed_orderProjection, prependRedAllOrders_e]
        rfl
      · push Not at ht
        change orderedQuotient Q Λ ν (StendhalAlgebraAllOrders.e t) ∈ _
        rw [orderedQuotient_e_eq_zero Q Λ ν t ht]
        exact zero_mem _
    | hx a =>
      change orderedQuotient Q Λ ν (StendhalAlgebraAllOrders.x a) ∈ _
      rcases eq_firstPosition_or a with rfl | ⟨b, rfl⟩
      · rw [← orderedQuotient_mul_firstRedIdem, firstRedIdem_eq_sum, Finset.mul_sum, map_sum]
        refine Subalgebra.sum_mem _ fun s _ => ?_
        rw [StendhalAlgebraAllOrders.x_mul_e_of_red _ _ (by rw [prependRedLoading_head]; rfl),
          map_zero]
        exact zero_mem _
      · refine (AlgHom.mem_range _).mpr ⟨orderProjection Q Λ₀ ν (StendhalAlgebraAllOrders.x b), ?_⟩
        rw [prependRed_orderProjection, prependRedAllOrders_x, orderedQuotient_mul_firstRedIdem]
    | hψ j =>
      change orderedQuotient Q Λ ν (StendhalAlgebraAllOrders.ψ j) ∈ _
      cases j with
      | zero =>
        by_cases h1 : 1 < Multiset.card μ'
        · rw [← orderedQuotient_mul_firstRedIdem, firstRedIdem_eq_sum, Finset.mul_sum, map_sum]
          refine Subalgebra.sum_mem _ fun s _ => ?_
          have hψe : StendhalAlgebraAllOrders.ψ 0 * StendhalAlgebraAllOrders.e (prependRedLoading s) =
              StendhalAlgebraAllOrders.e (TypeA.sadj (Multiset.card μ') 0 • prependRedLoading s) *
                (StendhalAlgebraAllOrders.ψ 0 : A) := by
            simp only [StendhalAlgebraAllOrders.ψ, StendhalAlgebraAllOrders.e, ← map_mul,
              KLRAlgebra.ψ_mul_e]
          rw [hψe, map_mul, orderedQuotient_e_eq_zero Q Λ ν _
            (fun s' => prependRedLoading_ne_sadj ν h1 s s'), zero_mul]
          exact zero_mem _
        · rw [StendhalAlgebraAllOrders.ψ, KLRAlgebra.ψ_eq_zero 0 (by omega), map_zero, map_zero]
          exact zero_mem _
      | succ j =>
        by_cases hj : j + 1 < Multiset.card μ
        · refine (AlgHom.mem_range _).mpr ⟨orderProjection Q Λ₀ ν (StendhalAlgebraAllOrders.ψ j), ?_⟩
          rw [prependRed_orderProjection, prependRedAllOrders_ψ Q Λ ν j hj,
            orderedQuotient_mul_firstRedIdem]
        · rw [StendhalAlgebraAllOrders.ψ, KLRAlgebra.ψ_eq_zero (j + 1) (by omega), map_zero,
            map_zero]
          exact zero_mem _
  intro y
  obtain ⟨u, rfl⟩ := orderedQuotient_surjective Q Λ ν y
  exact key u

end Quotient

end Categorification.Stendhal
