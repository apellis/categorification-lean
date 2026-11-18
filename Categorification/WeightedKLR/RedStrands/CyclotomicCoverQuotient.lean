/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RepresentationLift
import Categorification.KLR.Cyclotomic
import Categorification.WeightedKLR.RedStrands.StendhalCyclotomicParameters

/-!
# The cyclotomic cover presentation of the ordered Stendhal quotient

Webster, arXiv:1309.3796v2, Definitions 4.5–4.7. With a cyclotomic exponent
of zero at black colours and one at the auxiliary red colours, the
leftmost-black idempotents already vanish in the cyclotomic algebra.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
  (S : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)

local notation "μ" => stendhalWeight ℓ ν

/-- The cyclotomic polynomial is (1) at black colours and (x) at red colours. -/
def cyclotomicCoverPolynomial : I ⊕ Fin ℓ → Polynomial k :=
  Sum.elim (fun _ => 1) (fun _ => Polynomial.X)

local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "A" => KLRAlgebra k S μ
local notation "Cyc" => CycKLR k S p μ
local notation "π" => CycKLR.mk k S p μ

/-- The red-dot and red-order relations to be added to the cyclotomic algebra. -/
def cyclotomicCoverIdeal : TwoSidedIdeal Cyc :=
  TwoSidedIdeal.span
    ({x | ∃ (s : Seq μ) (a : Fin (Multiset.card μ)), (s.lbl a).isRight ∧
      x = π (KLRAlgebra.x a * KLRAlgebra.e s)} ∪
     {x | ∃ s : Seq μ, ¬ IsRedOrdered s ∧ x = π (KLRAlgebra.e s)})

/-- The cyclotomic cover modulo red dots and incorrectly ordered red loadings. -/
abbrev CyclotomicCoverQuotient := (cyclotomicCoverIdeal (k := k) ν S).ringCon.Quotient

private abbrev q : Cyc →ₐ[k] CyclotomicCoverQuotient (k := k) ν S :=
  (cyclotomicCoverIdeal (k := k) ν S).ringCon.mkₐ k

/-- The affine diagram map through the two successive quotients. -/
abbrev cyclotomicCoverProjection : A →ₐ[k] CyclotomicCoverQuotient (k := k) ν S :=
  (q ν S).comp π

theorem cyclotomicCoverProjection_surjective : Function.Surjective (cyclotomicCoverProjection ν S) :=
  (show Function.Surjective (q ν S) from RingCon.mkₐ_surjective _).comp
    CycKLR.mk_surjective

private theorem coverProjection_red_dot (s : Seq μ) (a : Fin (Multiset.card μ))
    (ha : (s.lbl a).isRight) : cyclotomicCoverProjection ν S (x a * e s) = 0 := by
  change (cyclotomicCoverIdeal (k := k) ν S).ringCon.mk' (π (x a * e s)) = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  exact TwoSidedIdeal.subset_span (Or.inl ⟨s, a, ha, rfl⟩)

private theorem coverProjection_unordered (s : Seq μ) (hs : ¬ IsRedOrdered s) :
    cyclotomicCoverProjection ν S (e s) = 0 := by
  change (cyclotomicCoverIdeal (k := k) ν S).ringCon.mk' (π (e s)) = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  exact TwoSidedIdeal.subset_span (Or.inr ⟨s, hs, rfl⟩)

private theorem coverProjection_violated (s : Seq μ) (hs : IsViolated s) :
    cyclotomicCoverProjection ν S (e s) = 0 := by
  obtain ⟨h, hv⟩ := hs
  have hp : p (s.lbl ⟨0, h⟩) = 1 := by
    cases hl : s.lbl ⟨0, h⟩ with
    | inl i => rfl
    | inr r => simp [hl] at hv
  rw [AlgHom.comp_apply, CycKLR.mk_e_eq_zero_of_eq_one s h hp, map_zero]

private theorem coverProjection_red_cross (s : Seq μ) (j : ℕ) (hj : j + 1 < Multiset.card μ)
    (hl : (s.lbl ⟨j, by omega⟩).isRight) (hr : (s.lbl ⟨j + 1, hj⟩).isRight) :
    cyclotomicCoverProjection ν S (ψ j * e s) = 0 := by
  by_cases hs : IsRedOrdered s
  · let l : Fin (Multiset.card μ) := ⟨j, by omega⟩
    let r : Fin (Multiset.card μ) := ⟨j + 1, hj⟩
    let t := TypeA.sadj (Multiset.card μ) j • s
    have hlt : l < r := by simp [l, r, Fin.lt_def]
    cases h₁ : s.lbl l with
    | inl i => simp [show s.lbl ⟨j, by omega⟩ = .inl i from h₁] at hl
    | inr a =>
      cases h₂ : s.lbl r with
      | inl i => simp [show s.lbl ⟨j + 1, hj⟩ = .inl i from h₂] at hr
      | inr b =>
        have ht : ¬ IsRedOrdered t := by
          intro ht
          exact (not_lt_of_ge (hs l r a b hlt h₁ h₂).le) (ht l r b a hlt
            ((lbl_sadj_left hj s).trans h₂) ((lbl_sadj_right hj s).trans h₁))
        rw [ψ_mul_e, map_mul, coverProjection_unordered ν S t ht, zero_mul]
  · rw [map_mul, coverProjection_unordered ν S s hs, mul_zero]

omit [DecidableEq I] in
private theorem cover_eval_specialize {B : Type*} [Ring B] [Algebra k B]
    (φ : MvPolynomial (Fin 2) k →ₐ[k] B) (E : B) (a b : I ⊕ Fin ℓ)
    (hc : ∀ t : Fin 2, Commute E (φ (MvPolynomial.X t)))
    (h₀ : a.isRight → φ (MvPolynomial.X 0) * E = 0)
    (h₁ : b.isRight → φ (MvPolynomial.X 1) * E = 0)
    (v : MvPolynomial (Fin 2) k) :
    φ (specializeRedDots a b v) * E = φ v * E := by
  have hX (t : Fin 2) : φ (specializeRedDots a b (MvPolynomial.X t)) * E =
      φ (MvPolynomial.X t) * E := by
    fin_cases t
    · by_cases h : a.isRight
      · simpa [specializeRedDots, h] using (h₀ h).symm
      · simp [specializeRedDots, h]
    · by_cases h : b.isRight
      · simpa [specializeRedDots, h] using (h₁ h).symm
      · simp [specializeRedDots, h]
  induction v using MvPolynomial.induction_on with
  | C c => simp
  | add v w hv hw => simp only [map_add, add_mul, hv, hw]
  | mul_X v t hv =>
    rw [map_mul, map_mul, map_mul, mul_assoc, hX, ← (hc t).eq, ← mul_assoc, hv,
      mul_assoc, (hc t).eq, ← mul_assoc]


private theorem cover_same_red {s : Seq μ} {a b : Fin (Multiset.card μ)} {r : Fin ℓ}
    (ha : s.lbl a = .inr r) (hb : s.lbl b = .inr r) : a = b := by
  classical
  let F := Finset.univ.filter (fun c => Sum.inr r = s.lbl c)
  have hc : F.card = 1 := by
    change (Finset.univ.val.filter (fun c => Sum.inr r = s.lbl c)).card = 1
    rw [← Multiset.count_map, show Finset.univ.val.map s.lbl = μ from s.2]
    rw [stendhalWeight, Multiset.count_add, Multiset.count_map_eq_count' Sum.inr _ Sum.inr_injective]
    simp
  exact Finset.card_le_one_iff.mp hc.le (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.symm⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.symm⟩)

private def coverChangeParameters {B : Type*} [Ring B] [Algebra k B]
    (R : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (f : A →ₐ[k] B)
    (hDot : ∀ (s : Seq μ) (a : Fin (Multiset.card μ)), (s.lbl a).isRight → f (x a * e s) = 0)
    (hSq : ∀ a b, specializeRedDots a b (S a b) = R a b ∨
      specializeRedDots a b (R a b) = S a b)
    (hBraid : ∀ i b, qbar (S (.inl i) b) = qbar (R (.inl i) b)) :
    KLRAlgebra k R μ →ₐ[k] B := by
  let g := f.comp (KLRAlgebra.mk k S μ)
  refine RingQuot.liftAlgHom k ⟨g, ?_⟩
  intro a b h
  have hrel : ∀ {u v}, KLR.Rel k S μ u v → g u = g v :=
    fun hr => congrArg f (RingQuot.mkAlgHom_rel k hr)
  cases h with
  | idem_mul s t => exact hrel (.idem_mul s t)
  | idem_sum => exact hrel .idem_sum
  | dot_idem j s => exact hrel (.dot_idem j s)
  | cross_idem j s => exact hrel (.cross_idem j s)
  | cross_zero j hj => exact hrel (.cross_zero j hj)
  | dot_dot i j => exact hrel (.dot_dot i j)
  | cross_cross j m hm => exact hrel (.cross_cross j m hm)
  | dot_cross a j ha hb => exact hrel (.dot_cross a j ha hb)
  | dot_cross_left j hj s => exact hrel (.dot_cross_left j hj s)
  | dot_cross_right j hj s => exact hrel (.dot_cross_right j hj s)
  | cross_sq j hj s =>
    refine (hrel (.cross_sq j hj s)).trans ?_
    split_ifs
    · rfl
    let pos : Fin 2 → Fin (Multiset.card μ) := ![⟨j, by omega⟩, ⟨j + 1, hj⟩]
    let φ := f.comp ((KLRAlgebra.pol (k := k) (Q := S) (ν := μ)).comp (MvPolynomial.rename pos))
    let l := s.lbl (pos 0)
    let r := s.lbl (pos 1)
    have hev (v : MvPolynomial (Fin 2) k) :
        g (ncEval (fun a => fx k μ (pos a)) v * fe k μ s) = φ v * f (e s) := by
      simp only [g, AlgHom.comp_apply, map_mul]
      rw [ncEval_map]
      change f (ncEval (fun a => x (pos a)) v) * f (e s) = _
      rw [ncEval_eq_pol]
      rfl
    change g (ncEval (fun a => fx k μ (pos a)) (S l r) * fe k μ s) =
      g (ncEval (fun a => fx k μ (pos a)) (R l r) * fe k μ s)
    rw [hev, hev]
    have hc (t : Fin 2) : Commute (f (e s)) (φ (MvPolynomial.X t)) := by
      simpa [φ] using Commute.map (show Commute (e s) (x (pos t)) from
        (x_mul_e (Q := S) (pos t) s).symm) f
    have h₀ (hl : l.isRight) : φ (MvPolynomial.X 0) * f (e s) = 0 := by
      simpa [φ, ← map_mul] using hDot s (pos 0) hl
    have h₁ (hr : r.isRight) : φ (MvPolynomial.X 1) * f (e s) = 0 := by
      simpa [φ, ← map_mul] using hDot s (pos 1) hr
    rcases hSq l r with he | he
    · rw [← he, cover_eval_specialize φ _ l r hc h₀ h₁]
    · rw [← he, cover_eval_specialize φ _ l r hc h₀ h₁]
  | braid j hj s =>
    refine (hrel (.braid j hj s)).trans ?_
    split_ifs with he
    swap
    · rfl
    cases hl : s.lbl ⟨j, by omega⟩ with
    | inl i => rw [hBraid]
    | inr r =>
      have heq := cover_same_red ν hl (he.1.symm.trans hl)
      have hval := congrArg Fin.val heq
      simp only at hval
      omega

private theorem coverChangeParameters_mk {B : Type*} [Ring B] [Algebra k B]
    (R : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k) (f : A →ₐ[k] B)
    (hDot : ∀ (s : Seq μ) (a : Fin (Multiset.card μ)), (s.lbl a).isRight → f (x a * e s) = 0)
    (hSq : ∀ a b, specializeRedDots a b (S a b) = R a b ∨
      specializeRedDots a b (R a b) = S a b)
    (hBraid : ∀ i b, qbar (S (.inl i) b) = qbar (R (.inl i) b))
    (v : FreeAlgebra k (Gen μ)) :
    coverChangeParameters ν S R f hDot hSq hBraid (KLRAlgebra.mk k R μ v) =
      f (KLRAlgebra.mk k S μ v) :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _


section Comparison

local notation "P" => stendhalQ Q Λ
local notation "D" => KLRAlgebra k P μ
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "τ" => AlgHom.comp (TensorProductAlgebra.mk Q Λ ν)
  (AlgHom.comp (orderProjection Q Λ ν) (StendhalAlgebraAllOrders.ofKLR k Q Λ ν))

variable (C : QuantumGroup.CartanDatum I)
local notation "S₀" => cyclotomicCoverQ C Λ Q
local notation "U" => CyclotomicCoverQuotient (k := k) ν S₀

private def coverForward : KLRAlgebra k S₀ μ →ₐ[k] T :=
  coverChangeParameters ν P S₀ τ
    (fun s a ha => (tensorRepresentationRelations_projection (Q := Q) (Λ := Λ) (ν := ν)).red_dot a s ha)
    (fun a b => Or.inr (specializeRedDots_cyclotomicCoverQ C Λ Q a b))
    (fun i b => (qbar_cyclotomicCoverQ_black C Λ Q i b).symm)

private def coverBackward : D →ₐ[k] U :=
  coverChangeParameters ν S₀ P (cyclotomicCoverProjection ν S₀)
    (coverProjection_red_dot ν S₀)
    (fun a b => Or.inl (specializeRedDots_cyclotomicCoverQ C Λ Q a b))
    (qbar_cyclotomicCoverQ_black C Λ Q)

private theorem coverForward_mk (v : FreeAlgebra k (Gen μ)) :
    coverForward (Q := Q) Λ ν C (KLRAlgebra.mk k S₀ μ v) = τ (KLRAlgebra.mk k P μ v) :=
  coverChangeParameters_mk ν P S₀ τ _ _ _ v

private theorem coverBackward_mk (v : FreeAlgebra k (Gen μ)) :
    coverBackward (Q := Q) Λ ν C (KLRAlgebra.mk k P μ v) =
      cyclotomicCoverProjection ν S₀ (KLRAlgebra.mk k S₀ μ v) :=
  coverChangeParameters_mk ν S₀ P (cyclotomicCoverProjection ν S₀) _ _ _ v

private theorem coverForward_cyclotomic (s : Seq μ) :
    coverForward (Q := Q) Λ ν C (cycElt S₀ p s) = 0 := by
  have he : ∀ t : Seq μ, coverForward (Q := Q) Λ ν C (e t) = τ (e t) :=
    fun t => coverForward_mk (Q := Q) Λ ν C (fe k μ t)
  have hx : ∀ a : Fin (Multiset.card μ), coverForward (Q := Q) Λ ν C (x a) = τ (x a) :=
    fun a => coverForward_mk (Q := Q) Λ ν C (fx k μ a)
  by_cases h : 0 < Multiset.card μ
  · rw [cycElt_of_pos S₀ p s h]
    cases hl : s.lbl ⟨0, h⟩ with
    | inl i =>
      change coverForward (Q := Q) Λ ν C (Polynomial.aeval _ 1 * _) = 0
      rw [map_one, one_mul, he]
      let hR := tensorRepresentationRelations_projection (Q := Q) (Λ := Λ) (ν := ν)
      by_cases ho : IsRedOrdered s
      · exact hR.violated s ho ⟨h, by simp [hl]⟩
      · exact hR.unordered s ho
    | inr r =>
      change coverForward (Q := Q) Λ ν C (Polynomial.aeval _ Polynomial.X * _) = 0
      rw [Polynomial.aeval_X, map_mul, hx, he, ← map_mul]
      exact (tensorRepresentationRelations_projection (Q := Q) (Λ := Λ) (ν := ν)).red_dot ⟨0, h⟩ s (by simp [hl])
  · simp [cycElt, h]

private def coverToTensor : U →ₐ[k] T := by
  let f : CycKLR k S₀ p μ →ₐ[k] T := CycKLR.lift (coverForward (Q := Q) Λ ν C) (coverForward_cyclotomic (Q := Q) Λ ν C)
  refine (cyclotomicCoverIdeal (k := k) ν S₀).ringCon.liftₐ f ?_
  apply (TwoSidedIdeal.ringCon_le_iff (J := TwoSidedIdeal.ker f.toRingHom)).mp
  apply TwoSidedIdeal.span_le.mpr
  intro z hz
  apply (TwoSidedIdeal.mem_ker _).mpr
  rcases hz with ⟨s, a, ha, rfl⟩ | ⟨s, hs, rfl⟩
  · change CycKLR.lift (coverForward (Q := Q) Λ ν C) _ (CycKLR.mk k S₀ p μ (x a * e s)) = 0
    rw [CycKLR.lift_mk]
    rw [← show KLRAlgebra.mk k S₀ μ (fx k μ a * fe k μ s) = x a * e s from map_mul _ _ _]
    rw [coverForward_mk, map_mul]
    exact (tensorRepresentationRelations_projection (Q := Q) (Λ := Λ) (ν := ν)).red_dot a s ha
  · change CycKLR.lift (coverForward (Q := Q) Λ ν C) _ (CycKLR.mk k S₀ p μ (e s)) = 0
    rw [CycKLR.lift_mk]
    change coverForward (Q := Q) Λ ν C (KLRAlgebra.mk k S₀ μ (fe k μ s)) = 0
    rw [coverForward_mk]
    exact (tensorRepresentationRelations_projection (Q := Q) (Λ := Λ) (ν := ν)).unordered s hs

private theorem coverToTensor_projection (a : KLRAlgebra k S₀ μ) :
    coverToTensor (Q := Q) Λ ν C (cyclotomicCoverProjection ν S₀ a) = coverForward (Q := Q) Λ ν C a := by
  change CycKLR.lift (coverForward (Q := Q) Λ ν C) (coverForward_cyclotomic (Q := Q) Λ ν C)
    (CycKLR.mk k S₀ p μ a) = _
  exact CycKLR.lift_mk _ _ _

private theorem coverTensorRelations : TensorRepresentationRelations (coverBackward (Q := Q) Λ ν C) where
  red_dot a s ha := by
    rw [← show KLRAlgebra.mk k P μ (fx k μ a * fe k μ s) = x a * e s from map_mul _ _ _]
    rw [coverBackward_mk, map_mul]
    exact coverProjection_red_dot ν S₀ s a ha
  red_cross j hj s hl hr := by
    rw [← show KLRAlgebra.mk k P μ (fψ k μ j * fe k μ s) = ψ j * e s from map_mul _ _ _]
    rw [coverBackward_mk, map_mul]
    exact coverProjection_red_cross ν S₀ s j hj hl hr
  unordered s hs := (coverBackward_mk (Q := Q) Λ ν C (fe k μ s)).trans (coverProjection_unordered ν S₀ s hs)
  violated s _ hs := (coverBackward_mk (Q := Q) Λ ν C (fe k μ s)).trans (coverProjection_violated ν S₀ s hs)

/-- The enlarged cyclotomic cover modulo red dots and unordered red
idempotents is Webster's tensor product algebra. -/
def cyclotomicCoverQuotientEquiv : U ≃ₐ[k] T := by
  let F := coverToTensor (Q := Q) Λ ν C
  let g := coverBackward (Q := Q) Λ ν C
  let H := tensorRepresentationLift g (coverTensorRelations (Q := Q) Λ ν C)
  have hF (v : FreeAlgebra k (Gen μ)) :
      F (cyclotomicCoverProjection ν S₀ (KLRAlgebra.mk k S₀ μ v)) = τ (KLRAlgebra.mk k P μ v) :=
    (coverToTensor_projection (Q := Q) Λ ν C _).trans (coverForward_mk (Q := Q) Λ ν C v)
  have hH (v : FreeAlgebra k (Gen μ)) :
      H (τ (KLRAlgebra.mk k P μ v)) = cyclotomicCoverProjection ν S₀ (KLRAlgebra.mk k S₀ μ v) :=
    (DFunLike.congr_fun (tensorRepresentationLift_comp g _) _).trans (coverBackward_mk (Q := Q) Λ ν C v)
  have ht : Function.Surjective τ :=
    (show Function.Surjective (TensorProductAlgebra.mk Q Λ ν) from RingCon.mkₐ_surjective _).comp
      ((orderProjection_surjective Q Λ ν).comp StendhalAlgebraAllOrders.ofKLR_surjective)
  exact AlgEquiv.ofAlgHom F H
    (AlgHom.ext fun t => by
      obtain ⟨a, rfl⟩ := ht t
      obtain ⟨v, rfl⟩ := KLRAlgebra.mk_surjective a
      exact (congrArg F (hH v)).trans (hF v))
    (AlgHom.ext fun u => by
      obtain ⟨a, rfl⟩ := cyclotomicCoverProjection_surjective ν S₀ u
      obtain ⟨v, rfl⟩ := KLRAlgebra.mk_surjective a
      exact (congrArg H (hF v)).trans (hH v))


/-- The comparison preserves every diagram represented in the free algebra. -/
theorem cyclotomicCoverQuotientEquiv_mk (v : FreeAlgebra k (Gen μ)) :
    cyclotomicCoverQuotientEquiv (Q := Q) Λ ν C
      (cyclotomicCoverProjection ν S₀ (KLRAlgebra.mk k S₀ μ v)) =
      τ (KLRAlgebra.mk k P μ v) :=
  (coverToTensor_projection (Q := Q) Λ ν C _).trans (coverForward_mk (Q := Q) Λ ν C v)

/-- The cyclotomic cover maps onto the tensor product algebra. -/
def cyclotomicCoverToTensor : CycKLR k S₀ p μ →ₐ[k] T :=
  (cyclotomicCoverQuotientEquiv (Q := Q) Λ ν C).toAlgHom.comp (q ν S₀)

theorem cyclotomicCoverToTensor_surjective :
    Function.Surjective (cyclotomicCoverToTensor (Q := Q) Λ ν C) :=
  (cyclotomicCoverQuotientEquiv (Q := Q) Λ ν C).surjective.comp
    (show Function.Surjective (q ν S₀) from RingCon.mkₐ_surjective _)

theorem cyclotomicCoverToTensor_mk (v : FreeAlgebra k (Gen μ)) :
    cyclotomicCoverToTensor (Q := Q) Λ ν C (CycKLR.mk k S₀ p μ (KLRAlgebra.mk k S₀ μ v)) =
      τ (KLRAlgebra.mk k P μ v) :=
  cyclotomicCoverQuotientEquiv_mk (Q := Q) Λ ν C v


/-- The kernel of the cyclotomic projection is generated by red dots and
unordered red idempotents. -/
theorem cyclotomicCoverToTensor_ker :
    TwoSidedIdeal.ker (cyclotomicCoverToTensor (Q := Q) Λ ν C).toRingHom =
      cyclotomicCoverIdeal (k := k) ν S₀ := by
  ext x
  rw [TwoSidedIdeal.mem_ker]
  change cyclotomicCoverQuotientEquiv (Q := Q) Λ ν C (q ν S₀ x) = 0 ↔ _
  rw [← map_zero (cyclotomicCoverQuotientEquiv (Q := Q) Λ ν C),
    (cyclotomicCoverQuotientEquiv (Q := Q) Λ ν C).injective.eq_iff]
  change (cyclotomicCoverIdeal (k := k) ν S₀).ringCon.mk' x = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

end Comparison

end Categorification.Stendhal
