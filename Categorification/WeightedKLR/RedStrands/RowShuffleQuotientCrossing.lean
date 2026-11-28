/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockShuffleQuotientCrossing
import Categorification.WeightedKLR.RedStrands.RowQuotientCoordinates

/-!
# External right crossings in quotient coordinates, for any row

Webster, arXiv:1309.3796v3, §6.1, proof of Lemma 6.9 (v2: Lemma 6.8). The leading-term
rule of `BlockShuffleQuotientCrossing` for external right ascents, for an arbitrary row of red
blocks and the quotient by `blockUpperIdeal a b α κ`. With a row of singleton blocks and
`a = b` it applies to full standard modules: a crossing that moves a black strand right past a
strand of a later block extends the shuffle, and the coordinate at the extended shuffle is the
bottom projector (`rowQuotientCoordinate_external_right_ascent`,
`rowQuotientCoordinate_external_diagonal`).
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

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (row : List (RedBlock I ℓ)) (a b : Fin ℓ) (α : Fin ℓ → I → ℕ) (κ : List (Fin ℓ))
    {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "P" => projection Q Λ row
local notation "J" => blockUpperIdeal k Q Λ ν a b α κ
local notation "π" => AlgHom.comp (RingCon.mkₐ k (TwoSidedIdeal.ringCon J))
  (AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν))

/-- Above the degree of a crossing-filtration difference, its two representatives
have equal quotient coordinates. -/
theorem rowQuotientCoordinate_eq_of_filtered_sub (u : ShuffleIndex row)
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
theorem rowQuotientCoordinate_external_right_ascent (h : weightSum row = stendhalWeight ℓ ν)
    {n : ℕ} (index : Fin n ≃ ShuffleIndex row)
    (w : Fin n → R) (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ row)
    (bottom : Fin n → Seq μ → diagrams Q Λ row)
    (hw : ∀ i, w i = (rowStack Q Λ row h) 1 * ψw (shuffleWord row (index i)))
    (hfilt : ∀ i y n, y ∈ filt k (stendhalQ Q Λ) μ n →
      G i (π y) ∈ (blockShuffleFilt Q Λ row (index i) n).map (P).toLinearMap)
    (hmul : ∀ i x y, G i (π ((rowStack Q Λ row h) x * y)) = P x * G i (π y))
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
  have fixed (y : R) : G d (π ((rowStack Q Λ row h) 1 * y)) = G d (π y) := by rw [hmul, map_one, one_mul]
  obtain ⟨lower, short⟩ := external_shuffle_error (stendhalQ Q Λ) row (index i) (index v) hj ha hv h s
  have same : G d (π (A * ψ j * e s)) = G d (π (B * e s)) := by
    rcases degree with hs | hh
    · exact congrArg (fun z : R => G d (π (z * e s))) (short hs)
    · exact rowQuotientCoordinate_eq_of_filtered_sub Q Λ row a b α κ (index d) (G d) (hfilt d) lower hh
  calc
    _ = G d (π (A * ψ j * e s)) := by
      rw [hw i]
      change G d (π (((rowStack Q Λ row h) 1 * A * ψ j) * e s)) = _
      rw [mul_assoc ((rowStack Q Λ row h) 1) A, mul_assoc ((rowStack Q Λ row h) 1), fixed]
    _ = G d (π (B * e s)) := same
    _ = G d (π (w v * e s)) := by
      rw [hw v]
      change _ = G d (π ((rowStack Q Λ row h) 1 * B * e s))
      rw [mul_assoc ((rowStack Q Λ row h) 1), fixed]
    _ = _ := by
      rw [hbottom]
      by_cases he : d = v
      · subst v; rw [ite_eq_left rfl, hself, one_mul]
      · rw [ite_eq_right he, hother d v he, zero_mul]

/-- The external diagonal is the source loading projector. It acts as the identity
on every coefficient supported at that loading, including the coordinates of every
right-supported representative in the ambient KLR algebra. -/
theorem rowQuotientCoordinate_external_diagonal (h : weightSum row = stendhalWeight ℓ ν)
    {n : ℕ} (index : Fin n ≃ ShuffleIndex row)
    (w : Fin n → R) (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ row)
    (bottom : Fin n → Seq μ → diagrams Q Λ row)
    (hw : ∀ i, w i = (rowStack Q Λ row h) 1 * ψw (shuffleWord row (index i)))
    (hfilt : ∀ i y n, y ∈ filt k (stendhalQ Q Λ) μ n →
      G i (π y) ∈ (blockShuffleFilt Q Λ row (index i) n).map (P).toLinearMap)
    (hmul : ∀ i x y, G i (π ((rowStack Q Λ row h) x * y)) = P x * G i (π y))
    (hbottom : ∀ i y s, G i (π (y * e s)) = G i (π y) * P (bottom i s))
    (hself : ∀ i, G i (π (w i)) = 1)
    (hother : ∀ d i, d ≠ i → G d (π (w i)) = 0)
    (hprojector : ∀ d s, IndexedLoadingProjector Q Λ row (index d) (Seq.cast h.symm s) (bottom d s))
    (i v : Fin n) (j : ℕ) (hj : j+1 < (weightSum row).card)
    (ha : shufflePerm row (index i) ⟨j,by omega⟩ < shufflePerm row (index i) ⟨j+1,hj⟩)
    (hv : shufflePerm row (index v) = shufflePerm row (index i) * sadj _ j)
    (s : Seq μ) :
    let s₀ := sadj (Multiset.card μ) j • s
    let src := P (bottom i s₀)
    let diag := G v (π (w i * ψ j * e s))
    diag = src ∧ (∀ x : quotients Q Λ row, x * src = x → x * diag = x) ∧
      ∀ y : R, y * e s₀ = y → G i (π y) * diag = G i (π y) := by
  intro s₀ src diag
  have len (d : Fin n) : (shuffleWord row (index d)).length = length _ (shufflePerm row (index d)) :=
    (isReduced_shuffleWord row (index d)).2
  have above : (shuffleWord row (index i)).length - 2 < (shuffleWord row (index v)).length := by
    rw [len i, len v, hv, length_mul_sadj_of_lt hj ha]
    omega
  have he : diag = P (bottom v s) := by
    simpa only [diag, ↓reduceIte] using
      rowQuotientCoordinate_external_right_ascent Q Λ row a b α κ h index w G bottom hw hfilt hmul hbottom
        hself hother i v v j hj ha hv s (Or.inr above)
  have hb : bottom v s = bottom i s₀ :=
    IndexedLoadingProjector.eq_after_right_swap Q Λ row h _ _ j hv s (hprojector v s) (hprojector i s₀)
  have hd : diag = src := he.trans (congrArg P hb)
  refine ⟨hd, fun x hx => (congrArg (x * ·) hd).trans hx, ?_⟩
  intro y hy
  rw [hd]
  exact (hbottom i y s₀).symm.trans (congrArg (fun z : R => G i (π z)) hy)

end Categorification.Stendhal.RedBlock
