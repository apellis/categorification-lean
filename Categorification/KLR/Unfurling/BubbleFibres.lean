/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.BubbleMultiplicity

/-!
# Bubble multiplicities with finite fibres

Supporting Webster, *Unfurling KLR algebras*, arXiv:1603.06311v3, proof of the theorem
labelled `nondegenerate`, “Triviality of a relation”. The colour set need not be finite.
Only the slot set over each colour is finite. Restricting any putative algebraic relation
to its finite set of colours reduces independence to `algebraicIndependent_multVal`.

`fibreBubEval_indep` has the shape of `UnfurledEval.bub_indep`. It requires independent
spectral values and enough level-one slots; identification with the diagrammatic vacuum
action is separate. Other slots may have arbitrary integer multiplicities.
-/

noncomputable section
namespace Categorification.KLR.Unfurling
open PowerSeries
variable {I J R : Type*} [Fintype J] [CommRing R]

/-- A product with integer multiplicities over the finite slots of one colour. -/
def fibreMultSeries (m : I → J → ℤ) (z : I × J → R) (i : I) : PowerSeries R :=
  ((∏ j, oneSubUnit (z (i, j)) ^ m i j : (PowerSeries R)ˣ) : PowerSeries R)

/-- A coefficient of the finite-fibre multiplicity series. -/
def fibreMultVal (m : I → J → ℤ) (z : I × J → R) (i : I) (n : ℕ) : R :=
  coeff n (fibreMultSeries m z i)

private theorem prod_labelsOver_fst [Fintype I] [DecidableEq I]
    {A : Type*} [CommMonoid A] (f : I × J → A) (i : I) :
    ∏ p ∈ labelsOver Prod.fst i, f p = ∏ j, f (i, j) := by
  classical
  refine Finset.prod_bij (fun p _ => p.2) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro a ha b hb hab
    have ha := (mem_labelsOver Prod.fst).1 ha
    have hb := (mem_labelsOver Prod.fst).1 hb
    exact Prod.ext (ha.trans hb.symm) hab
  · intro j _
    exact ⟨(i, j), (mem_labelsOver Prod.fst).2 rfl, rfl⟩
  · intro p hp
    have hp := (mem_labelsOver Prod.fst).1 hp
    congr 1
    exact Prod.ext hp rfl

/-- Agreement with `multVal` when the colour set is finite. -/
theorem multVal_fst [Fintype I] [DecidableEq I]
    (m : I → J → ℤ) (z : I × J → R) (i : I) (n : ℕ) :
    multVal Prod.fst (fun p => m p.1 p.2) z i n = fibreMultVal m z i n := by
  simp only [multVal, multSeries, fibreMultVal, fibreMultSeries, prod_labelsOver_fst]

omit [Fintype J] in
private theorem card_labelsOver_fst [Fintype I] [DecidableEq I] (G : Finset J) (i : I) :
    (labelsOver (fun p : (Finset.univ.product G : Finset (I × J)) => p.1.1) i).card = G.card := by
  classical
  refine Finset.card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p _
    exact (Finset.mem_product.1 p.2).2
  · intro a ha b hb hab
    apply Subtype.ext
    exact Prod.ext (((mem_labelsOver _).1 ha).trans ((mem_labelsOver _).1 hb).symm) hab
  · intro j hj
    exact ⟨⟨(i, j), Finset.mem_product.2 ⟨Finset.mem_univ _, hj⟩⟩,
      (mem_labelsOver _).2 rfl, rfl⟩

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

private theorem algebraicIndependent_fibreMultVal_finite [Fintype I]
    (m : I → J → ℤ) {z : I × J → L} (hz : AlgebraicIndependent k z)
    (G : Finset J) (c : I → Bool)
    (hG : ∀ i j, j ∈ G → m i j = if c i then 1 else -1) {N : ℕ} (hN : N ≤ G.card) :
    AlgebraicIndependent k fun p : {p : I × ℕ // p.2 < N} =>
      fibreMultVal m z p.1.1 (p.1.2 + 1) := by
  classical
  have h := algebraicIndependent_multVal (k := k) (π := Prod.fst)
    (m := fun p : I × J => m p.1 p.2) hz (Finset.univ.product G) c
    (fun j hj => hG j.1 j.2 (Finset.mem_product.1 hj).2)
    (N := N) (fun i => (card_labelsOver_fst G i).symm ▸ hN)
  simpa only [multVal_fst] using h

/-- Independence of bounded bubble coefficients for arbitrary colour sets. -/
theorem algebraicIndependent_fibreMultVal (m : I → J → ℤ) {z : I × J → L}
    (hz : AlgebraicIndependent k z) (G : Finset J) (c : I → Bool)
    (hG : ∀ i j, j ∈ G → m i j = if c i then 1 else -1) {N : ℕ} (hN : N ≤ G.card) :
    AlgebraicIndependent k fun p : {p : I × ℕ // p.2 < N} =>
      fibreMultVal m z p.1.1 (p.1.2 + 1) := by
  classical
  apply algebraicIndependent_of_finite_type
  intro t ht
  let colours : Finset I := ht.toFinset.image (fun p => p.1.1)
  let emb : colours × J → I × J := fun p => (p.1.1, p.2)
  have hemb : Function.Injective emb := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg (fun p : I × J => p.1) h))
      (congrArg (fun p : I × J => p.2) h)
  have hind := algebraicIndependent_fibreMultVal_finite
    (fun i : colours => m i) (hz.comp emb hemb) G (fun i : colours => c i)
    (fun i j hj => hG i j hj) hN
  let e : t → {p : colours × ℕ // p.2 < N} := fun p =>
    ⟨(⟨p.1.1.1, Finset.mem_image.2 ⟨p.1, ht.mem_toFinset.2 p.2, rfl⟩⟩, p.1.1.2), p.1.2⟩
  have he : Function.Injective e := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg (fun x => x.1.1.1) h) (congrArg (fun x => x.1.2) h)
  have h := hind.comp e he
  exact h
/-- The polynomial action associated with the finite-fibre multiplicity coefficients. -/
def fibreBubEval (m : I → J → ℤ) (z : I × J → L) : KL3.Diagram.PiLam I k →ₐ[k] L :=
  MvPolynomial.aeval (fun p => fibreMultVal m z p.1 (p.2 + 1))

/-- The finite-fibre polynomial action satisfies the independence field of `UnfurledEval`. -/
theorem fibreBubEval_indep (m : I → J → ℤ) {z : I × J → L}
    (hz : AlgebraicIndependent k z) (G : Finset J) (c : I → Bool)
    (hG : ∀ i j, j ∈ G → m i j = if c i then 1 else -1) {N : ℕ} (hN : N ≤ G.card) :
    AlgebraicIndependent k fun p : {p : I × ℕ // p.2 < N} =>
      fibreBubEval (k := k) m z (MvPolynomial.X p.1) := by
  simpa only [fibreBubEval, MvPolynomial.aeval_X] using
    algebraicIndependent_fibreMultVal m hz G c hG hN

end Categorification.KLR.Unfurling
