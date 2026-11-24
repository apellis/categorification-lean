/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockInsideCrossing
import Categorification.WeightedKLR.RedStrands.BlockQuotientCoordinates

/-!
# Right crossings in quotient block coordinates

For Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8, an external right ascent extends the
incoming row shuffle. An internal right ascent acts by the crossing of that block.
At every shuffle above the error filtration the quotient coordinates read these
leading terms with their descended loading projectors.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA BraidedStendhalAlgebra
variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}

private theorem external_shuffle_error
    (Q : (I ⊕ Fin ℓ) → (I ⊕ Fin ℓ) → MvPolynomial (Fin 2) k)
    (row : List (RedBlock I ℓ)) (u v : ShuffleIndex row) {j : ℕ}
    (hj : j+1 < (weightSum row).card)
    (ha : shufflePerm row u ⟨j,by omega⟩ < shufflePerm row u ⟨j+1,hj⟩)
    (hv : shufflePerm row v = shufflePerm row u * sadj _ j)
    {δ : Multiset (I ⊕ Fin ℓ)} (h : weightSum row = δ) (s : Seq δ) :
    let a := shuffleWord row u
    let b := shuffleWord row v
    (ψw a * ψ j * e s - ψw b * e s ∈ filt k Q δ (a.length - 2)) ∧
      (a.length ≤ 1 → (ψw a * ψ j : KLRAlgebra k Q δ) = ψw b) := by
  subst δ
  intro a b
  have red := isReduced_shuffleWord row u
  have prod : wordProd (weightSum row).card (a ++ [j]) = wordProd _ b := by
    rw [wordProd_append, wordProd_singleton]
    exact hv.symm
  have ext : IsReduced (weightSum row).card (a ++ [j]) := by
    refine ⟨validWord_append.2 ⟨red.1, ?_⟩, ?_⟩
    · intro z hz
      obtain rfl := List.mem_singleton.1 hz
      exact hj
    · rw [List.length_append, List.length_singleton, wordProd_append, wordProd_singleton]
      exact (congrArg (· + 1) red.2).trans (length_mul_sadj_of_lt hj ha).symm
  exact ⟨rightCrossing_error_of_reduced ext (isReduced_shuffleWord row v) prod s,
    rightCrossing_eq_of_short_reduced ext (isReduced_shuffleWord row v) prod⟩

private theorem internal_shuffle_error (Q : (I ⊕ Fin ℓ) → (I ⊕ Fin ℓ) → MvPolynomial (Fin 2) k)
    (row : List (RedBlock I ℓ)) (u : ShuffleIndex row) {j : ℕ} (hj : j+1 < (weightSum row).card)
    (ha : shufflePerm row u ⟨j,by omega⟩ < shufflePerm row u ⟨j+1,hj⟩)
    (hsame : SameInputBlock row u j hj)
    {δ : Multiset (I ⊕ Fin ℓ)} (h : weightSum row = δ) (s : Seq δ) :
    let w := shuffleWord row u
    let a := (shufflePerm row u ⟨j,by omega⟩).val
    InsideBlock row a ∧
      (ψw w * ψ j * e s - (ψ a * ψw w) * e s ∈ filt k Q δ (w.length - 2)) ∧
      (w.length ≤ 1 → (ψw w * ψ j : KLRAlgebra k Q δ) = ψ a * ψw w) := by
  subst δ
  rcases shuffleWord_right_ascent_crossing Q row u j hj ha s with
    ⟨v, hv, _, hvbad, _⟩ | ⟨_, hi, _, _, hclose⟩
  · exact (hvbad ((sameInputBlock_swap_iff row u v j hj hv).2 hsame)).elim
  · exact ⟨hi, hclose⟩

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}

local notation "row" => adjacentRow L M f β
local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "P" => projection Q Λ row
local notation "α" => fun r i => boundaryCount (cut (f 0) (f 1) r) i row
local notation "κ" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1) α κ
local notation "π" => AlgHom.comp (RingCon.mkₐ k (TwoSidedIdeal.ringCon J))
  (AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν))

/-- Above the degree of a crossing-filtration difference, its two representatives
have equal quotient coordinates. -/
theorem quotientCoordinate_eq_of_filtered_sub (u : ShuffleIndex row)
    (G : (J).ringCon.Quotient →ₗ[k] quotients Q Λ row)
    (hfilt : ∀ y n, y ∈ filt k (stendhalQ Q Λ) μ n →
      G (π y) ∈ (blockShuffleFilt Q Λ row u n).map (P).toLinearMap)
    {n : ℕ} {x y : R} (hxy : x - y ∈ filt k (stendhalQ Q Λ) μ n)
    (hhi : n < (shuffleWord row u).length) : G (π x) = G (π y) := by
  have hz := hfilt (x - y) n hxy
  rw [blockShuffleFilt_eq_bot Q Λ row u hhi, Submodule.map_bot, Submodule.mem_bot,
    map_sub, map_sub] at hz
  exact sub_eq_zero.mp hz

/-- At an external right ascent the coordinate above the braid-error degree is the
bottom projector at the extended shuffle. For incoming words of length at most one,
this formula applies at every coordinate. -/
theorem quotientCoordinate_external_right_ascent (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
    {n : ℕ} (index : Fin n ≃ ShuffleIndex row)
    (w : Fin n → R) (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ row)
    (bottom : Fin n → Seq μ → diagrams Q Λ row)
    (hw : ∀ i, w i = (affineStackBlocks Q Λ L M f β h) 1 * ψw (shuffleWord row (index i)))
    (hfilt : ∀ i y n, y ∈ filt k (stendhalQ Q Λ) μ n →
      G i (π y) ∈ (blockShuffleFilt Q Λ row (index i) n).map (P).toLinearMap)
    (hmul : ∀ i x y, G i (π ((affineStackBlocks Q Λ L M f β h) x * y)) = P x * G i (π y))
    (hbottom : ∀ i y s, G i (π (y * e s)) = G i (π y) * P (bottom i s))
    (hself : ∀ i, G i (π (w i)) = 1)
    (hother : ∀ d i, d ≠ i → G d (π (w i)) = 0)
    (i v d : Fin n) (j : ℕ) (hj : j+1 < (weightSum row).card)
    (ha : shufflePerm row (index i) ⟨j,by omega⟩ < shufflePerm row (index i) ⟨j+1,hj⟩)
    (hv : shufflePerm row (index v) = shufflePerm row (index i) * sadj _ j)
    (s : Seq μ) (degree : (shuffleWord row (index i)).length ≤ 1 ∨
      (shuffleWord row (index i)).length - 2 < (shuffleWord row (index d)).length) :
    G d (π (w i * ψ j * e s)) = if d = v then P (bottom d s) else 0 := by
  let A := ψw (shuffleWord row (index i)) (Q := stendhalQ Q Λ) (ν := μ)
  let B := ψw (shuffleWord row (index v)) (Q := stendhalQ Q Λ) (ν := μ)
  have fixed (y : R) : G d (π ((affineStackBlocks Q Λ L M f β h) 1 * y)) = G d (π y) := by rw [hmul, map_one, one_mul]
  obtain ⟨lower, short⟩ := external_shuffle_error (stendhalQ Q Λ) row (index i) (index v) hj ha hv h s
  have same : G d (π (A * ψ j * e s)) = G d (π (B * e s)) := by
    rcases degree with hs | hh
    · exact congrArg (fun z : R => G d (π (z * e s))) (short hs)
    · exact quotientCoordinate_eq_of_filtered_sub Q Λ L M f β (index d) (G d) (hfilt d) lower hh
  calc
    _ = G d (π (A * ψ j * e s)) := by
      rw [hw i]
      change G d (π (((affineStackBlocks Q Λ L M f β h) 1 * A * ψ j) * e s)) = _
      rw [mul_assoc ((affineStackBlocks Q Λ L M f β h) 1) A, mul_assoc ((affineStackBlocks Q Λ L M f β h) 1), fixed]
    _ = G d (π (B * e s)) := same
    _ = G d (π (w v * e s)) := by
      rw [hw v]
      change _ = G d (π ((affineStackBlocks Q Λ L M f β h) 1 * B * e s))
      rw [mul_assoc ((affineStackBlocks Q Λ L M f β h) 1), fixed]
    _ = _ := by
      rw [hbottom]
      by_cases he : d = v
      · subst v; rw [ite_eq_left rfl, hself, one_mul]
      · rw [ite_eq_right he, hother d v he, zero_mul]

/-- At an internal ascent the leading quotient coordinate is the crossing in the
appropriate block, multiplied by the bottom projector at the unchanged shuffle. -/
theorem quotientCoordinate_internal_right_ascent (h : weightSum row = μ)
    {n : ℕ} (index : Fin n ≃ ShuffleIndex row)
    (w : Fin n → R) (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ row)
    (bottom : Fin n → Seq μ → diagrams Q Λ row)
    (hw : ∀ i, w i = (affineStackBlocks Q Λ L M f β h) 1 * ψw (shuffleWord row (index i)))
    (hfilt : ∀ i y n, y ∈ filt k (stendhalQ Q Λ) μ n →
      G i (π y) ∈ (blockShuffleFilt Q Λ row (index i) n).map (P).toLinearMap)
    (hmul : ∀ i x y, G i (π ((affineStackBlocks Q Λ L M f β h) x * y)) = P x * G i (π y))
    (hbottom : ∀ i y s, G i (π (y * e s)) = G i (π y) * P (bottom i s))
    (hself : ∀ i, G i (π (w i)) = 1)
    (hother : ∀ d i, d ≠ i → G d (π (w i)) = 0)
    (i d : Fin n) (j : ℕ) (hj : j+1 < (weightSum row).card)
    (ha : shufflePerm row (index i) ⟨j,by omega⟩ < shufflePerm row (index i) ⟨j+1,hj⟩)
    (hsame : SameInputBlock row (index i) j hj)
    (s : Seq μ) (degree : (shuffleWord row (index i)).length ≤ 1 ∨
      (shuffleWord row (index i)).length - 2 < (shuffleWord row (index d)).length) :
    let a := (shufflePerm row (index i) ⟨j,by omega⟩).val
    G d (π (w i * ψ j * e s)) =
      if d = i then P (insideCrossing Q Λ row a) * P (bottom d s) else 0 := by
  intro a
  let A := ψw (shuffleWord row (index i)) (Q := stendhalQ Q Λ) (ν := μ)
  let S := affineStackBlocks Q Λ L M f β h
  have fixed (y : R) : G d (π (S 1 * y)) = G d (π y) := by rw [hmul, map_one, one_mul]
  obtain ⟨hi, lower, short⟩ := internal_shuffle_error (stendhalQ Q Λ) row (index i) hj ha hsame h s
  have same : G d (π (A * ψ j * e s)) = G d (π (ψ a * A * e s)) := by
    rcases degree with hs | hh
    · exact congrArg (fun z : R => G d (π (z * e s))) (short hs)
    · exact quotientCoordinate_eq_of_filtered_sub Q Λ L M f β (index d) (G d) (hfilt d) lower hh
  calc
    _ = G d (π (A * ψ j * e s)) := by
      rw [hw i]
      change G d (π ((S 1 * A * ψ j) * e s)) = _
      rw [mul_assoc (S 1) A, mul_assoc (S 1), fixed]
    _ = G d (π (ψ a * A * e s)) := same
    _ = G d (π (S 1 * (ψ a * A * e s))) := (fixed _).symm
    _ = _ := internalCrossing_leading_coordinate Q Λ L M f β h w G bottom hmul hbottom
      hself hother i d s _ (hw i) hi

/-- The quotient coordinates of the partially standardized row realize the external
crossing formula, with their loading projectors and normalized representatives. -/
theorem exists_blockStack_external_crossing_coordinates (hQ : KLRSymm Q)
    (h : weightSum row = stendhalWeight ℓ ν) :
    let S := affineStackBlocks Q Λ L M f β h
    ∃ n, ∃ (index : Fin n ≃ ShuffleIndex row) (w : Fin n → R)
      (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ row)
      (bottom : Fin n → Seq μ → diagrams Q Λ row),
      (∀ i, w i = S 1 * ψw (shuffleWord row (index i))) ∧
      (∀ i, G i (π (w i)) = 1) ∧ (∀ d i, d ≠ i → G d (π (w i)) = 0) ∧
      (∀ d s, bottom d s = 0 ∨ ∃ x : Loadings row,
        ShuffleLoading row (Seq.cast h.symm s) x ∧ bottom d s = loadingIdem Q Λ row x) ∧
      ∀ i v d (j : ℕ) (hj : j+1 < (weightSum row).card),
        shufflePerm row (index i) ⟨j,by omega⟩ < shufflePerm row (index i) ⟨j+1,hj⟩ →
        shufflePerm row (index v) = shufflePerm row (index i) * sadj _ j →
        ∀ s : Seq μ, ((shuffleWord row (index i)).length ≤ 1 ∨
          (shuffleWord row (index i)).length - 2 < (shuffleWord row (index d)).length) →
        G d (π (w i * ψ j * e s)) = if d = v then P (bottom d s) else 0 := by
  obtain ⟨n, index, _, w, G, bottom, _, hw, hf, hm, hb, hloading, _, hs, ho, _⟩ :=
    exists_blockStack_filtered_quotient_coordinates Q Λ L M f β hQ h
  exact ⟨n, index, w, G, bottom, hw, hs, ho, hloading,
    quotientCoordinate_external_right_ascent Q Λ L M f β h index w G bottom hw hf hm hb hs ho⟩

end Categorification.Stendhal.RedBlock
