/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockShuffleCoordinateSupport
import Categorification.WeightedKLR.RedStrands.BlockShuffleJointLoading
import Categorification.WeightedKLR.RedStrands.BlockShuffleQuotientCrossing
import Categorification.WeightedKLR.RedStrands.BlockShuffleTriangular

/-!
# The right-crossing kernel on a block column

For the kernel test in Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8, the only
remaining kernel tests on a supported block column are the internal leading
crossings in the individual block coordinates.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA BraidedStendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
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
local notation "E" => orderedIdem Q Λ (fun _ => 1) row
local notation "S" => affineStackBlocks Q Λ L M f β

/-- Matrix formula for right multiplication on quotient elements. -/
theorem quotientCoordinate_mul_right (h : weightSum row = μ) {n : ℕ}
    (g : Fin n → R →ₗ[k] diagrams Q Λ row) (w : Fin n → R)
    (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ row)
    (hG : ∀ i y, G i (π y) = P (g i y))
    (hmul : ∀ i a y, G i (π (S h a * y)) = P a * G i (π y))
    (rebuild : ∀ y, π (S h 1 * y) = ∑ i, π (S h (g i y) * w i))
    (d : Fin n) (x : (J).ringCon.Quotient) (z : R) :
    G d (x * π z) = ∑ i, G i x * G d (π (w i * z)) := by
  have onto : Function.Surjective π :=
    (RingCon.mkₐ_surjective («α» := k) (TwoSidedIdeal.ringCon J)).comp
      (violMk_surjective.comp ofKLR_surjective)
  obtain ⟨y, rfl⟩ := onto x
  have hmatrix := quotientCoordinate_mul_right_sum Q Λ L M f β h g w G hG hmul rebuild d y z
  rw [← map_mul π, mul_assoc, hmul, map_one, one_mul, map_mul π] at hmatrix
  exact hmatrix

private def supportedCoefficients {A : Type*} [Ring A] [Algebra k A] (a b : A) : Submodule k A where
  carrier := {c | a * c = c ∧ c * b = c}
  zero_mem' := ⟨mul_zero _, zero_mul _⟩
  add_mem' := fun hx hy => ⟨by rw [mul_add, hx.1, hy.1], by rw [add_mul, hx.2, hy.2]⟩
  smul_mem' := fun r x hx =>
    ⟨by rw [mul_smul_comm, hx.1], by rw [smul_mul_assoc, hx.2]⟩

/-- If every internal crossing has zero kernel on its ordered upper and indexed
lower supports, right crossing at the black–red joint has zero kernel on the
entire supported column. -/
theorem blockColumn_eq_zero_of_internal_crossing (hQ : KLRSymm Q) (h : weightSum row = μ)
    (t s : Seq μ) (j : ℕ) (hj : j + 1 < (weightSum row).card)
    (ho : redWord t = κ) (i₀ : I) (r : Fin ℓ) :
    let s₀ := sadj (Multiset.card μ) j • s
    let source := Seq.cast h.symm s₀
    redWord s₀ = κ → source.lbl ⟨j, by omega⟩ = .inl i₀ → source.lbl ⟨j+1, hj⟩ = .inr r →
    (∀ (u : ShuffleIndex row) (z₀ z : diagrams Q Λ row),
      IndexedLoadingProjector Q Λ row u source z₀ →
      IndexedLoadingProjector Q Λ row u (Seq.cast h.symm s) z → P z₀ ≠ 0 →
      shufflePerm row u ⟨j,by omega⟩ < shufflePerm row u ⟨j+1,hj⟩ →
      SameInputBlock row u j hj → ∀ c : quotients Q Λ row,
      P E * c = c → c * P z₀ = c →
      c * (P (insideCrossing Q Λ row (shufflePerm row u ⟨j,by omega⟩).val) * P z) = 0 → c = 0) →
    ∀ x : blockColumn Q Λ L M f β h,
      π (e t) * x.1 = x.1 → x.1 * π (e s₀) = x.1 → x.1 * π (ψ j * e s) = 0 → x = 0 := by
  classical
  intro s₀ source horder hblack hred internal x htop hbot hker
  obtain ⟨n,index,g,w,G,b,hG,hw,hf,hm,hb,hp,hu,hs,hd,hr⟩ :=
    exists_blockStack_quotient_coordinates_with_indexed_projectors Q Λ L M f β hQ h
  let Asc (i : Fin n) := shufflePerm row (index i) ⟨j,by omega⟩ < shufflePerm row (index i) ⟨j+1,hj⟩
  let T (i d : Fin n) := G d (π (w i * ψ j * e s))
  let F (i : Fin n) := supportedCoefficients (k := k) (P E) (P (b i s₀))
  obtain ⟨lead,hcase,hlen,herror⟩ := exists_rightAscent_leading_coordinates Q Λ L M f β h
    index w G b hw hf hm hb hs hd j hj s
  have mem (i : Fin n) : G i x.1 ∈ F i :=
    quotientCoordinate_support_of_redLoading Q Λ L M f β h (G i) (b i) (hm i) (hb i) x.1 t s₀ ho htop hbot
  have diag (i : Subtype Asc) : Function.Injective (fun c : F i.val => (c : quotients Q Λ row) * T i.val (lead i)) := by
    rcases hcase i with ⟨he,hlocal⟩ | ⟨he,_⟩
    · rw [he] at hlocal ⊢
      have high : (shuffleWord row (index i.val)).length ≤ 1 ∨
          (shuffleWord row (index i.val)).length - 2 < (shuffleWord row (index i.val)).length := by omega
      have eq := quotientCoordinate_internal_right_ascent Q Λ L M f β h index w G b
        hw hf hm hb hs hd i.val i.val j hj i.property hlocal s high
      simp only [↓reduceIte] at eq
      intro c c' hcc
      apply Subtype.ext
      apply sub_eq_zero.mp
      let d := c - c'
      obtain ⟨hl,hright⟩ := d.property
      by_cases hz : P (b i.val s₀) = 0
      · change (d : quotients Q Λ row) = 0
        rwa [hz, mul_zero, eq_comm] at hright
      · apply internal (index i.val) (b i.val s₀) (b i.val s) (hp _ _) (hp _ _) hz i.property hlocal
          d.val hl hright
        change ((c : quotients Q Λ row) - (c' : quotients Q Λ row)) * _ = 0
        rw [← eq, sub_mul, sub_eq_zero]
        exact hcc
    · have ext := (quotientCoordinate_external_diagonal Q Λ L M f β h index w G b
          hw hf hm hb hs hd hp i.val (lead i) j hj i.property he s).2.1
      intro c c' heq
      have left := ext c.val c.property.2
      have right := ext c'.val c'.property.2
      exact Subtype.ext (left.symm.trans (heq.trans right))
  apply blockColumn_eq_zero_of_quotient_coordinates Q Λ L M f β h g w G hG hu hr x
  apply eq_zero_of_supported_rightAscentCoordinates row index Asc lead j hj (fun i => F i.val) T
    hcase hlen herror diag (fun i => G i x.1) (fun i => mem i.val)
  · intro i hno
    have hz : P (b i s₀) = 0 := by
      by_contra nz
      apply hno
      apply shufflePerm_lt_of_nonzero_indexedProjector Q Λ L M f β h (index i) source (b i s₀)
        (hp i s₀) nz _ hblack hred
      · exact Nat.lt_succ_self j
      · have back {δ δ' : Multiset (I ⊕ Fin ℓ)} (h' : δ = δ') (v : Seq δ') :
            Seq.cast h' (Seq.cast h'.symm v) = v := by subst δ'; rfl
        simpa only [source, back] using horder
    exact (mem i).2.symm.trans (by rw [hz, mul_zero])
  · intro d
    have sum := quotientCoordinate_mul_right Q Λ L M f β h g w G hG hm hr d x.1 (ψ j * e s)
    rw [hker, map_zero] at sum
    simpa only [T, mul_assoc] using sum.symm

end Categorification.Stendhal.RedBlock
