/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalBasis
import Categorification.KLR.Rouquier.Polynomial
import Categorification.KLR.Symmetries

/-!
# The Stendhal diagram basis for Webster's parameters

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§2.2 and Proposition 4.16. On the finite support of a fixed black weight, one
oriented edge per pair of distinct colors realizes the prescribed polynomials
as the parameters of a zero-weight graph. Edges of polynomial degree zero
retain constant units. The Stendhal presentation sees only off-diagonal
polynomials whose two colors occur in that weight.
-/

noncomputable section

namespace Categorification.Stendhal

open WeightedKLR KLR TypeA Equiv MvPolynomial

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k]

private abbrev Color (ν : Multiset I) := ↥ν.toFinset

private abbrev colorIndex (ν : Multiset I) := Fintype.equivFin (Color ν)

private abbrev Pair (ν : Multiset I) :=
  {p : Color ν × Color ν // colorIndex ν p.1 < colorIndex ν p.2}

private def parameterGraph (Q : I → I → MvPolynomial (Fin 2) k) (ν : Multiset I) :
    WeightedGraph I ℚ k where
  E := Pair ν
  tail e := e.1.1.1
  head e := e.1.2.1
  weight _ := 0
  Q e := Q e.1.2.1 e.1.1.1
  loop _ := none

variable (Q : I → I → MvPolynomial (Fin 2) k) (ν : Multiset I)

private theorem parameterGraph_dagger : (parameterGraph Q ν).Dagger := by
  refine ⟨fun e f ht hh _ => Subtype.ext (Prod.ext (Subtype.ext ht) (Subtype.ext hh)), ?_⟩
  intro e f ht hh
  have h₁ : e.1.1 = f.1.2 := Subtype.ext ht
  have h₂ : e.1.2 = f.1.1 := Subtype.ext hh
  exact ((not_lt_of_ge (le_of_lt e.2)) (h₂ ▸ h₁ ▸ f.2)).elim

private theorem parameterGraph_noLoop (e : (parameterGraph Q ν).E) : (parameterGraph Q ν).head e ≠ (parameterGraph Q ν).tail e := by
  intro h
  exact e.2.ne (congrArg (colorIndex ν) (Subtype.ext h).symm)

private theorem parameterGraph_standing (d : I → ℕ) (hd : ∀ i, 0 < d i)
    (hQ : ∀ a b, a ≠ b → ∃ c c', WeightedGraph.IsUnitHomogeneous (d a) (d b) c c' (Q a b)) :
    (parameterGraph Q ν).Standing :=
  ⟨d, hd, fun e => hQ _ _ (parameterGraph_noLoop Q ν e), fun _ _ h => by cases h⟩

private theorem edgeProd_parameterGraph (a b : Color ν) :
    (parameterGraph Q ν).edgeProd a.1 b.1 = if colorIndex ν a < colorIndex ν b then Q b.1 a.1 else 1 := by
  classical
  unfold WeightedGraph.edgeProd
  by_cases hab : colorIndex ν a < colorIndex ν b
  · let e : (parameterGraph Q ν).E := ⟨(a,b), hab⟩
    have he : Finset.univ.filter (fun f : (parameterGraph Q ν).E => (parameterGraph Q ν).tail f = a.1 ∧ (parameterGraph Q ν).head f = b.1) = {e} := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun H => Subtype.ext (Prod.ext (Subtype.ext H.1) (Subtype.ext H.2)), fun H => H ▸ ⟨rfl,rfl⟩⟩
    rw [he, Finset.prod_singleton, ite_eq_left hab]
    rfl
  · have he : Finset.univ.filter (fun f : (parameterGraph Q ν).E => (parameterGraph Q ν).tail f = a.1 ∧ (parameterGraph Q ν).head f = b.1) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      rintro f _ ⟨hf, hg⟩
      have hf' : f.1.1 = a := Subtype.ext hf
      have hg' : f.1.2 = b := Subtype.ext hg
      exact hab (hf' ▸ hg' ▸ f.2)
    simp [he, hab]

private theorem parameterGraph_q (hsym : KLRSymm Q) {a b : I} (ha : a ∈ ν)
    (hb : b ∈ ν) (hab : a ≠ b) : (parameterGraph Q ν).klrQ a b = Q a b := by
  let i : Color ν := ⟨a, Multiset.mem_toFinset.2 ha⟩
  let j : Color ν := ⟨b, Multiset.mem_toFinset.2 hb⟩
  have hij : colorIndex ν i ≠ colorIndex ν j := fun h =>
    hab (congrArg Subtype.val ((colorIndex ν).injective h))
  change (parameterGraph Q ν).edgeProd j.1 i.1 * rename ![1,0] ((parameterGraph Q ν).edgeProd i.1 j.1) = _
  rw [edgeProd_parameterGraph, edgeProd_parameterGraph]
  rcases lt_or_gt_of_ne hij with h | h
  · simpa [h, not_lt.mpr h.le] using (hsym b a hab.symm).symm
  · simp [h, not_lt.mpr h.le, i, j]


variable {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "S₀" => stendhalQ Q Λ
local notation "S₁" => stendhalQ (WeightedGraph.klrQ (parameterGraph Q ν)) Λ

private theorem parameterGraph_stendhal_q (hsym : KLRSymm Q)
    (s : KLR.Seq μ) (a b : Fin (Multiset.card μ)) (h : s.lbl a ≠ s.lbl b) :
    S₀ (s.lbl a) (s.lbl b) = S₁ (s.lbl a) (s.lbl b) := by
  have h₁ : s.lbl a ∈ μ := s.mem a
  have h₂ : s.lbl b ∈ μ := s.mem b
  cases ha : s.lbl a with
  | inr r => cases s.lbl b <;> rfl
  | inl i =>
    cases hb : s.lbl b with
    | inr r => rfl
    | inl j =>
      change Q i j = (parameterGraph Q ν).klrQ i j
      rw [ha] at h₁
      rw [hb] at h₂
      exact (parameterGraph_q Q ν hsym (by simpa [stendhalWeight] using h₁)
        (by simpa [stendhalWeight] using h₂) (fun he => h (ha.trans ((congrArg Sum.inl he).trans hb.symm)))).symm

private theorem parameterGraph_klr_rel (hsym : KLRSymm Q) {x y : FreeAlgebra k (KLR.Gen μ)}
    (h : KLR.Rel k S₀ μ x y) : KLR.Rel k S₁ μ x y := by
  cases h with
  | idem_mul i j => exact .idem_mul i j
  | idem_sum => exact .idem_sum
  | dot_idem a i => exact .dot_idem a i
  | cross_idem j i => exact .cross_idem j i
  | cross_zero j h => exact .cross_zero j h
  | dot_dot a b => exact .dot_dot a b
  | cross_cross i j h => exact .cross_cross i j h
  | dot_cross a j h₁ h₂ => exact .dot_cross a j h₁ h₂
  | dot_cross_left j h i => exact .dot_cross_left j h i
  | dot_cross_right j h i => exact .dot_cross_right j h i
  | cross_sq j h i =>
    have H := KLR.Rel.cross_sq (k := k) (Q := S₁) j h i
    by_cases hj : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩
    · simpa only [hj, ↓reduceIte] using H
    · simpa only [hj, ↓reduceIte, parameterGraph_stendhal_q Q ν Λ hsym i _ _ hj] using H
  | braid j h i =>
    have H := KLR.Rel.braid (k := k) (Q := S₁) j h i
    by_cases hj : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, by omega⟩
    · simpa only [hj, ne_self_iff_false, and_false, ↓reduceIte] using H
    · simpa only [parameterGraph_stendhal_q Q ν Λ hsym i _ _ hj] using H

private def parameterHom (hsym : KLRSymm Q) :
    StendhalAlgebraAllOrders k Q Λ ν →ₐ[k] StendhalAlgebraAllOrders k (parameterGraph Q ν).klrQ Λ ν :=
  RingQuot.liftAlgHom k ⟨RingQuot.mkAlgHom k (Rel k (parameterGraph Q ν).klrQ Λ ν), fun _ _ h => by
    apply RingQuot.mkAlgHom_rel
    cases h with
    | klr h => exact .klr (parameterGraph_klr_rel Q ν Λ hsym h)
    | red_cross j h i ha hb => exact .red_cross j h i ha hb
    | red_dot a i h => exact .red_dot a i h⟩

private theorem parameterHom_term (hsym : KLRSymm Q)
    {ρ : Perm (Fin (Multiset.card μ)) → List ℕ} (hρ : ∀ w, wordProd (Multiset.card μ) (ρ w) = w)
    (b : {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) ρ b}) :
    parameterHom Q ν Λ hsym (stendhalTerm Q Λ hρ b).val = (stendhalTerm (parameterGraph Q ν).klrQ Λ hρ b).val := by
  rw [stendhalTerm_val, stendhalTerm_val, ← mk_fStd, ← mk_fStd,
    StendhalAlgebraAllOrders.ofKLR_mk, StendhalAlgebraAllOrders.ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

/-- The standard Stendhal terms are linearly independent for the parameters of
Webster, arXiv:1309.3796v2, §2.2 and Proposition 4.16. The pure coefficients
are taken to be units over a commutative coefficient ring. Over a field
this is exactly the requirement that the two specified leading terms occur. -/
private theorem linearIndependent_stendhalTerm_of_parameters
    (hsym : KLRSymm Q) (d : I → ℕ) (hd : ∀ i, 0 < d i)
    (hQ : ∀ a b, a ≠ b → ∃ c c', WeightedGraph.IsUnitHomogeneous (d a) (d b) c c' (Q a b))
    {ρ : Perm (Fin (Multiset.card μ)) → List ℕ}
    (hρ : ∀ w, IsReduced (Multiset.card μ) (ρ w) ∧ wordProd (Multiset.card μ) (ρ w) = w) :
    LinearIndependent k (stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2)) := by
  let H := fun w => (hρ w).2
  have hi := linearIndependent_stendhalTerm (ν := ν) (Λ := Λ) (parameterGraph_dagger Q ν)
    (parameterGraph_noLoop Q ν) (fun _ => rfl) (fun _ => rfl)
    (parameterGraph_standing Q ν d hd hQ) hρ
  rw [linearIndependent_iff'] at hi ⊢
  intro t g ht b hb
  apply hi t g _ b hb
  apply stendhalValₗ_injective
  rw [map_sum, map_zero]
  have h := congrArg (parameterHom Q ν Λ hsym) (congrArg (stendhalValₗ (Q := Q) (Λ := Λ)) ht)
  simp only [map_sum, map_smul, map_zero] at h ⊢
  change ∑ i ∈ t, g i • parameterHom Q ν Λ hsym (stendhalTerm Q Λ H i).val = 0 at h
  change ∑ i ∈ t, g i • (stendhalTerm (parameterGraph Q ν).klrQ Λ H i).val = 0
  simpa only [parameterHom_term] using h

omit [DecidableEq I] in
private theorem unitHomogeneous_of_rouquier {C : QuantumGroup.CartanDatum I}
    (hQ : IsRouquierQ C Q) (i j : I) (hij : i ≠ j) :
    WeightedGraph.IsUnitHomogeneous (C.dot i i).toNat (C.dot j j).toNat
      (C.dij i j) (C.dij j i) (Q i j) := by
  have hi := Int.toNat_of_nonneg (C.dot_self_pos i).le
  have hj := Int.toNat_of_nonneg (C.dot_self_pos j).le
  have hm := C.dij_mul hij
  have hm' := C.dij_mul hij.symm
  rw [C.symm j i] at hm'
  refine ⟨?_, ?_, hQ.unit_coeff i j hij, ?_⟩
  · apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [hi, hj, mul_comm (C.dot i i), mul_comm (C.dot j j), hm, hm']
  · intro s hs
    have hh := hQ.homogeneous i j hij hs
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hh ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, nsmul_eq_mul] at hh ⊢
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [hi, hj, hh, ← hm, mul_comm]
  · have hu := hQ.unit_coeff j i hij.symm
    rw [← hQ.symm i j hij] at hu
    have hinj : Function.Injective (![1, 0] : Fin 2 → Fin 2) := by decide
    have h := coeff_rename_mapDomain _ hinj (Q i j) (Finsupp.single 1 (C.dij j i))
    simp only [Finsupp.mapDomain_single, Matrix.cons_val_one] at h
    rwa [← h]

/-- Independence in Webster, arXiv:1309.3796v2, Proposition 4.16,
for the homogeneous crossing polynomials specified in §2.2. -/
theorem linearIndependent_stendhalTerm_of_rouquier {C : QuantumGroup.CartanDatum I}
    (hQ : IsRouquierQ C Q)
    {ρ : Perm (Fin (Multiset.card μ)) → List ℕ}
    (hρ : ∀ w, IsReduced (Multiset.card μ) (ρ w) ∧ wordProd (Multiset.card μ) (ρ w) = w) :
    LinearIndependent k (stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2)) :=
  linearIndependent_stendhalTerm_of_parameters Q ν Λ
    (fun i j hij => (hQ.symm i j hij).symm) (fun i => (C.dot i i).toNat)
    (fun i => by have := C.dot_self_pos i; omega)
    (fun i j hij => ⟨_, _, unitHomogeneous_of_rouquier Q hQ i j hij⟩) hρ

end Categorification.Stendhal
