/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalBasis
import Categorification.KLR.Symmetries
import Categorification.KLR.CyclotomicSplit
import Categorification.WeightedKLR.RedStrands.StendhalGrading

/-!
# Boundary characters in the first black weight

Webster, arXiv:1309.3796v2, Definitions 4.4–4.7 and the first black weight
in Theorem 4.38. Suppose every red multiplicity at the black colour is positive.
Each nonviolated ordered boundary word defines a scalar representation in which
all dots and crossings vanish. Positivity ensures that the mixed bigons evaluate
to zero. The characters separate the idempotents for the different black positions.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR StendhalAlgebraAllOrders
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace FirstWeight

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {i : I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)

omit [DecidableEq I] in
private lemma lbl_injective (s : Seq μ) : Function.Injective s.lbl := by
  classical
  have hnodup : (Finset.univ.val.map s.lbl).Nodup := by
    rw [show Finset.univ.val.map s.lbl = μ from s.2]
    simp [stendhalWeight, List.nodup_ofFn, Sum.inr_injective]
  exact fun a b h => Multiset.inj_on_of_nodup_map hnodup a (by simp) b (by simp) h

omit [DecidableEq I] in
private lemma black_eq (s : Seq μ) (a : Fin (Multiset.card μ)) {c : I} (ha : s.lbl a = .inl c) : c = i := by
  have h : Sum.inl c ∈ μ := by
    rw [← show Finset.univ.val.map s.lbl = μ from s.2, Multiset.mem_map]
    exact ⟨a, by simp, ha⟩
  simpa [stendhalWeight] using h

private def characterGen (s : Seq μ) : Gen μ → k
  | .idem t => if t = s then 1 else 0
  | .dot _ | .cross _ => 0

omit [DecidableEq I] in
private lemma eval_pair (hΛ : ∀ r, 0 < Λ r i) (s : Seq μ) (a b : Fin (Multiset.card μ)) (hab : a ≠ b) :
    MvPolynomial.aeval (fun _ : Fin 2 => (0 : k)) (stendhalQ Q Λ (s.lbl a) (s.lbl b)) = 0 := by
  cases ha : s.lbl a with
  | inl c =>
    have hc := black_eq s a ha
    subst c
    cases hb : s.lbl b with
    | inl c =>
      obtain rfl := black_eq s b hb
      exact (hab (lbl_injective s (ha.trans hb.symm))).elim
    | inr r => simp [stendhalQ, (hΛ r).ne']
  | inr r =>
    cases hb : s.lbl b with
    | inl c => obtain rfl := black_eq s b hb; simp [stendhalQ, (hΛ r).ne']
    | inr u => simp [stendhalQ]

private lemma respects (hΛ : ∀ r, 0 < Λ r i) (s : Seq μ) {x y : FreeAlgebra k (Gen μ)}
    (h : Rel k Q Λ {i} x y) :
    FreeAlgebra.lift k (characterGen (k := k) s) x = FreeAlgebra.lift k (characterGen s) y := by
  classical
  have hne (t : Seq μ) (a b : Fin (Multiset.card μ)) (h : a.val ≠ b.val) : t.lbl a ≠ t.lbl b :=
    fun hh => h (congrArg Fin.val (lbl_injective t hh))
  cases h with
  | red_dot | red_cross => simp [fx, fe, fψ, characterGen]
  | klr h =>
    cases h with
    | idem_mul u v =>
      by_cases huv : u = v <;> by_cases hu : u = s <;> by_cases hv : v = s <;> simp_all [fe, characterGen]
    | idem_sum => simp [fe, characterGen]
    | dot_idem | dot_dot | cross_idem | cross_zero | cross_cross | dot_cross =>
      simp [fx, fe, fψ, characterGen]
    | dot_cross_left j h t | dot_cross_right j h t =>
      simp [fx, fe, fψ, characterGen, hne t ⟨j, by omega⟩ ⟨j+1, by omega⟩ (by simp)]
    | braid j h t =>
      simp [fe, fψ, characterGen, hne t ⟨j, by omega⟩ ⟨j+2, by omega⟩ (by simp)]
    | cross_sq j h t =>
      let a : Fin (Multiset.card μ) := ⟨j, by omega⟩
      let b : Fin (Multiset.card μ) := ⟨j+1, h⟩
      have heval : ∀ p : MvPolynomial (Fin 2) k, ncEval (fun _ : Fin 2 => (0 : k)) p =
          MvPolynomial.aeval (fun _ : Fin 2 => (0 : k)) p := fun p => by
        simpa using ncEval_algHom_X (MvPolynomial.aeval (fun _ : Fin 2 => (0 : k))) id p
      have hv : (fun r : Fin 2 => FreeAlgebra.lift k (characterGen (k := k) s) (![fx k μ a, fx k μ b] r)) =
          fun _ => 0 := by funext r; fin_cases r <;> simp [fx, characterGen]
      simp only [hne t ⟨j, by omega⟩ ⟨j+1, by omega⟩ (by simp), ↓reduceIte, map_mul, fψ, FreeAlgebra.lift_ι_apply,
        characterGen, zero_mul, ncEval_map]
      rw [hv, heval, eval_pair Q Λ hΛ t a b (by intro hh; have := congrArg Fin.val hh; simp [a,b] at this), zero_mul]

private def evalAll (hΛ : ∀ r, 0 < Λ r i) (s : Seq μ) :
    StendhalAlgebraAllOrders k Q Λ {i} →ₐ[k] k :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (characterGen s), fun _ _ h => respects Q Λ hΛ s h⟩

private theorem evalAll_mk (hΛ : ∀ r, 0 < Λ r i) (s : Seq μ) (x : FreeAlgebra k (Gen μ)) :
    evalAll Q Λ hΛ s (RingQuot.mkAlgHom k (Rel k Q Λ {i}) x) = FreeAlgebra.lift k (characterGen s) x :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

private lemma evalAll_e (hΛ : ∀ r, 0 < Λ r i) (s t : Seq μ) :
    evalAll Q Λ hΛ s (e t) = if t = s then 1 else 0 := by
  rw [e, KLRAlgebra.e, ofKLR_mk, evalAll_mk]
  simp [fe, characterGen]

private lemma evalAll_order (hΛ : ∀ r, 0 < Λ r i) (s : Seq μ) (hs : IsRedOrdered s) :
    evalAll Q Λ hΛ s (redOrderedIdem k Q Λ {i}) = 1 := by
  classical
  simp [redOrderedIdem, evalAll_e, hs]

private def evalCorner (hΛ : ∀ r, 0 < Λ r i) (s : Seq μ) (hs : IsRedOrdered s) :
    StendhalAlgebra k Q Λ {i} →ₐ[k] k where
  toFun x := evalAll Q Λ hΛ s x.1
  map_one' := evalAll_order Q Λ hΛ s hs
  map_mul' _ _ := map_mul _ _ _
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _
  commutes' c := by
    change evalAll Q Λ hΛ s (c • redOrderedIdem k Q Λ {i}) = _
    rw [map_smul, evalAll_order Q Λ hΛ s hs, Algebra.smul_def, mul_one]

/-- The character at a nonviolated ordered boundary in the first lowering block.
The strictly positive red multiplicities are used in the mixed bigon relations. -/
def boundaryCharacter (hΛ : ∀ r, 0 < Λ r i) (s : Seq μ) (hs : IsRedOrdered s) (hv : ¬ IsViolated s) :
    TensorProductAlgebra k Q Λ {i} →ₐ[k] k :=
  (StendhalAlgebra.violatedIdeal k Q Λ {i}).ringCon.liftₐ (evalCorner Q Λ hΛ s hs) (by
    apply (TwoSidedIdeal.ringCon_le_iff (J := TwoSidedIdeal.ker (evalCorner Q Λ hΛ s hs).toRingHom)).mp
    apply TwoSidedIdeal.span_le.2
    rintro _ ⟨t, ho, ht, rfl⟩
    apply (TwoSidedIdeal.mem_ker _).mpr
    change evalAll Q Λ hΛ s (e t) = 0
    simp [evalAll_e, show t ≠ s from fun h => hv (h ▸ ht)])

@[simp] theorem boundaryCharacter_e (hΛ : ∀ r, 0 < Λ r i) (s t : Seq μ)
    (hs : IsRedOrdered s) (hv : ¬ IsViolated s) (ht : IsRedOrdered t) :
    boundaryCharacter Q Λ hΛ s hs hv (TensorProductAlgebra.mk Q Λ {i} (StendhalAlgebra.e t ht)) =
      if t = s then 1 else 0 :=
  evalAll_e Q Λ hΛ s t

/-- Evaluation at all surviving words in the first lowering block. -/
def boundaryCharacters (hΛ : ∀ r, 0 < Λ r i) :
    TensorProductAlgebra k Q Λ {i} →ₐ[k] ({s : Seq μ // IsRedOrdered s ∧ ¬ IsViolated s} → k) :=
  AlgHom.pi (fun s => boundaryCharacter Q Λ hΛ s.1 s.2.1 s.2.2)

/-- Each tuple of scalars is obtained from the corresponding linear combination
of surviving boundary idempotents. In particular, the scalar representations
at distinct black positions are distinct when the coefficient ring is nontrivial. -/
theorem boundaryCharacters_surjective (hΛ : ∀ r, 0 < Λ r i) :
    Function.Surjective (boundaryCharacters Q Λ hΛ) := by
  classical
  intro f
  let S := {s : Seq μ // IsRedOrdered s ∧ ¬ IsViolated s}
  refine ⟨∑ s : S, f s • TensorProductAlgebra.mk Q Λ {i} (StendhalAlgebra.e s.1 s.2.1), ?_⟩
  funext t
  change boundaryCharacter Q Λ hΛ t.1 t.2.1 t.2.2 _ = f t
  simp only [map_sum, map_smul, boundaryCharacter_e]
  rw [Finset.sum_eq_single t]
  · simp
  · intro s _ hst
    simp [show s.1 ≠ t.1 from fun h => hst (Subtype.ext h)]
  · simp

section Grading

open _root_.AddMonoidAlgebra

variable (G : GradingDatum (stendhalQ Q Λ))
  (hΛ : ∀ r, 0 < Λ r i)

local notation "π" => ofKLR k Q Λ ((Singleton.singleton i) : Multiset I)
private def evalKLR (s : Seq μ) :
    KLRAlgebra k (stendhalQ Q Λ) μ →ₐ[k] k :=
  (evalAll Q Λ hΛ s).comp π

private theorem evalAll_x (s : Seq μ) (a : Fin (Multiset.card μ)) : (evalKLR Q Λ hΛ s) (KLRAlgebra.x a) = 0 := by
  change evalAll Q Λ hΛ s (π (KLRAlgebra.x a)) = 0
  rw [KLRAlgebra.x, ofKLR_mk, evalAll_mk]
  simp [fx, characterGen]

private theorem evalAll_ψ (s : Seq μ) (j : ℕ) : (evalKLR Q Λ hΛ s) (KLRAlgebra.ψ j) = 0 := by
  change evalAll Q Λ hΛ s (π (KLRAlgebra.ψ j)) = 0
  rw [KLRAlgebra.ψ, ofKLR_mk, evalAll_mk]
  simp [fψ, characterGen]

private theorem evalAll_coaction (s : Seq μ) (x : KLRAlgebra k (stendhalQ Q Λ) μ) :
    AddMonoidAlgebra.mapAlgHom ℤ (evalKLR Q Λ hΛ s) (G.coaction x) = single 0 ((evalKLR Q Λ hΛ s) x) := by
  let f := (AddMonoidAlgebra.mapAlgHom ℤ (evalKLR Q Λ hΛ s)).comp G.coaction
  let g := (AddMonoidAlgebra.singleZeroAlgHom : k →ₐ[k] AddMonoidAlgebra k ℤ).comp (evalKLR Q Λ hΛ s)
  change f x = g x
  induction x using KLRAlgebra.klr_induction with
  | hr c => rw [AlgHom.commutes, AlgHom.commutes]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]
  | hmul x y hx hy => rw [map_mul, map_mul, hx, hy]
  | he t =>
    change AddMonoidAlgebra.mapAlgHom ℤ (evalKLR Q Λ hΛ s) (G.coaction (KLRAlgebra.e t)) = _
    rw [G.coaction_e, AddMonoidAlgebra.mapAlgHom_single]
    rfl
  | hx a =>
    change AddMonoidAlgebra.mapAlgHom ℤ (evalKLR Q Λ hΛ s) (G.coaction (KLRAlgebra.x a)) = single 0 ((evalKLR Q Λ hΛ s) _)
    rw [G.coaction_x, map_sum, evalAll_x Q Λ hΛ s]
    simp only [AddMonoidAlgebra.mapAlgHom_single, map_mul, evalAll_x Q Λ hΛ s, zero_mul,
      AddMonoidAlgebra.single_zero, Finset.sum_const_zero]
  | hψ j =>
    change AddMonoidAlgebra.mapAlgHom ℤ (evalKLR Q Λ hΛ s) (G.coaction (KLRAlgebra.ψ j)) = single 0 ((evalKLR Q Λ hΛ s) _)
    rw [G.coaction_ψ, map_sum, evalAll_ψ Q Λ hΛ s]
    simp only [AddMonoidAlgebra.mapAlgHom_single, map_mul, evalAll_ψ Q Λ hΛ s, zero_mul,
      AddMonoidAlgebra.single_zero, Finset.sum_const_zero]

/-- The first-weight character vanishes on homogeneous elements of any
nonzero diagram degree. -/
theorem boundaryCharacter_eq_zero_of_ne_grade (s : Seq μ) (hs : IsRedOrdered s) (hv : ¬ IsViolated s)
    {d : ℤ} (hd : d ≠ 0) {z : TensorProductAlgebra k Q Λ {i}}
    (hz : z ∈ tensorProductGrade G {i} d) : boundaryCharacter Q Λ hΛ s hs hv z = 0 := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
  change evalAll Q Λ hΛ s y.val = 0
  have hy' : y.val ∈ allOrdersGrade G {i} d := hy
  obtain ⟨x, hx, he⟩ := Submodule.mem_map.mp hy'
  have he' : π x = y.val := he
  rw [← he']
  change (evalKLR Q Λ hΛ s) x = 0
  have h := evalAll_coaction Q Λ G hΛ s x
  rw [G.mem_grade.mp hx, AddMonoidAlgebra.mapAlgHom_single] at h
  have h' := congrArg (fun x : AddMonoidAlgebra k ℤ => x.coeff d) h
  change Finsupp.single d (evalKLR Q Λ hΛ s x) d =
    Finsupp.single 0 (evalKLR Q Λ hΛ s x) d at h'
  rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hd] at h'
  exact h'

end Grading

end FirstWeight
end Categorification.Stendhal
