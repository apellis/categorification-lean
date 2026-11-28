/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapSliding

/-!
# The crossing of two passing strands slides through the window, up to exits

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈_i 𝔈_j ≅ 𝔈_i 𝔈_j ∘ K` with the crossing for `i ≠ j`
and a cap at the right end (`j = ℓ`). There the two appended strands pass under the window of the
strands at the maximum, one after the other, and the crossing of the two strands is to be slid
from the top of the two passages to their bottom.

Sliding the crossing through the window strand at position `c` is a KLR braid move between the two
passing strands and that window strand (`CupCap.crossSlideStage_sub_succ`). When the two passing
strands have different colours, the braid relation leaves a defect: the identity on the three
strands with dots on them, in which the passing strand on the right continues to the top in the
place of the window strand. That strand ends at the bottom right, so it leaves the window at the
top: a top window loading whose strand `c` is red would give an idempotent of a mismatched colour,
and one whose strand `c` is black is not of the form `μ ⋯ μ*` after moving that strand to the
right end of the window. Hence every defect lies in the span `exitSpan` of the diagrams in which a
strand leaves the window at the top (`CupCap.eSum_mul_crossSlide_mem`).

## Main results

* `CupCap.crossSlide_eq_sum`: the difference between the crossing at the top and at the bottom of
  the two passages, as a sum of braid defects.
* `CupCap.eSum_mul_crossSlide_mem`: the difference lies in `exitSpan`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MvPolynomial

section Generic

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {μ : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k}

variable (Q') in
/-- **The crossing slid past the first `c` strands of the block**: two strands at `q + n` and
`q + n + 1` pass the block `[q, q + n)`, and their crossing sits between the passages of the
strands `c - 1` and `c` of the block. -/
def crossSlideStage (q n c : ℕ) (t : Seq μ) : KLRAlgebra k Q' μ :=
  KLRAlgebra.ψw (List.range' (q + 1) c) * KLRAlgebra.ψw (List.range' q c) *
    KLRAlgebra.ψ (q + c) * KLRAlgebra.ψw (List.range' (q + 1 + c) (n - c)) *
    KLRAlgebra.ψw (List.range' (q + c) (n - c)) * KLRAlgebra.e t

/-- **One braid move**: sliding the crossing past the strand `c` of the block changes it by the
braid defect at `q + c`. -/
theorem crossSlideStage_sub_succ {q n c : ℕ} (hc : c < n) (t : Seq μ) :
    crossSlideStage Q' q n c t - crossSlideStage Q' q n (c + 1) t =
      KLRAlgebra.ψw (List.range' (q + 1) c) * KLRAlgebra.ψw (List.range' q c) *
        (KLRAlgebra.ψ (q + c) * KLRAlgebra.ψ (q + c + 1) * KLRAlgebra.ψ (q + c) -
          KLRAlgebra.ψ (q + c + 1) * KLRAlgebra.ψ (q + c) * KLRAlgebra.ψ (q + c + 1)) *
        KLRAlgebra.ψw (List.range' (q + 2 + c) (n - 1 - c)) *
        KLRAlgebra.ψw (List.range' (q + c + 1) (n - 1 - c)) * KLRAlgebra.e t := by
  unfold crossSlideStage
  have e1 : List.range' (q + 1 + c) (n - c) =
      (q + c + 1) :: List.range' (q + 2 + c) (n - 1 - c) := by
    rw [show n - c = (n - 1 - c) + 1 by omega, List.range'_succ,
      show q + 1 + c + 1 = q + 2 + c by omega, show q + 1 + c = q + c + 1 by omega]
  have e2 : List.range' (q + c) (n - c) = (q + c) :: List.range' (q + c + 1) (n - 1 - c) := by
    rw [show n - c = (n - 1 - c) + 1 by omega, List.range'_succ]
  have e3 : List.range' (q + 1 + (c + 1)) (n - (c + 1)) = List.range' (q + 2 + c) (n - 1 - c) := by
    rw [show q + 1 + (c + 1) = q + 2 + c by omega, show n - (c + 1) = n - 1 - c by omega]
  have e4 : List.range' (q + (c + 1)) (n - (c + 1)) = List.range' (q + c + 1) (n - 1 - c) := by
    rw [show q + (c + 1) = q + c + 1 by omega, show n - (c + 1) = n - 1 - c by omega]
  have e5 : List.range' (q + 1) (c + 1) = List.range' (q + 1) c ++ [q + c + 1] := by
    rw [List.range'_1_concat, show q + 1 + c = q + c + 1 by omega]
  have e6 : List.range' q (c + 1) = List.range' q c ++ [q + c] := List.range'_1_concat
  rw [e1, e2, e3, e4, e5, e6, show q + (c + 1) = q + c + 1 by omega, KLRAlgebra.ψw_append,
    KLRAlgebra.ψw_append, KLRAlgebra.ψw_cons, KLRAlgebra.ψw_cons, KLRAlgebra.ψw_cons,
    KLRAlgebra.ψw_cons, KLRAlgebra.ψw_nil, mul_one, mul_one]
  set A := (KLRAlgebra.ψw (List.range' (q + 1) c) : KLRAlgebra k Q' μ)
  set B := (KLRAlgebra.ψw (List.range' q c) : KLRAlgebra k Q' μ) with hB
  set A' := (KLRAlgebra.ψw (List.range' (q + 2 + c) (n - 1 - c)) : KLRAlgebra k Q' μ) with hA'
  set B' := (KLRAlgebra.ψw (List.range' (q + c + 1) (n - 1 - c)) : KLRAlgebra k Q' μ)
  set a := (KLRAlgebra.ψ (q + c) : KLRAlgebra k Q' μ)
  set b := (KLRAlgebra.ψ (q + c + 1) : KLRAlgebra k Q' μ)
  have ha : Commute a A' :=
    KLRAlgebra.commute_ψ_ψw fun l hl => by rw [List.mem_range'_1] at hl; omega
  have hb : Commute b B :=
    KLRAlgebra.commute_ψ_ψw fun l hl => by rw [List.mem_range'_1] at hl; omega
  have h1 : A * B * a * (b * A') * (a * B') * KLRAlgebra.e t =
      A * B * (a * b * a) * A' * B' * KLRAlgebra.e t := by
    rw [show A * B * a * (b * A') * (a * B') * KLRAlgebra.e t =
        A * B * a * b * (A' * a) * B' * KLRAlgebra.e t by noncomm_ring, ← ha.eq]
    noncomm_ring
  have h2 : A * b * (B * a) * b * A' * B' * KLRAlgebra.e t =
      A * B * (b * a * b) * A' * B' * KLRAlgebra.e t := by
    rw [show A * b * (B * a) * b * A' * B' * KLRAlgebra.e t =
        A * (b * B) * a * b * A' * B' * KLRAlgebra.e t by noncomm_ring, hb.eq]
    noncomm_ring
  rw [h1, h2]
  noncomm_ring

/-- **The crossing at the top of the two passages minus the crossing at the bottom**, as the sum
of the braid defects of the single moves. -/
theorem crossSlide_eq_sum (q n : ℕ) (t : Seq μ) :
    (KLRAlgebra.ψ q * KLRAlgebra.ψw (List.range' (q + 1) n) * KLRAlgebra.ψw (List.range' q n) *
        KLRAlgebra.e t - KLRAlgebra.ψw (List.range' (q + 1) n) *
        KLRAlgebra.ψw (List.range' q n) * KLRAlgebra.ψ (q + n) * KLRAlgebra.e t :
        KLRAlgebra k Q' μ) =
      ∑ c ∈ Finset.range n, (crossSlideStage Q' q n c t - crossSlideStage Q' q n (c + 1) t) := by
  rw [Finset.sum_range_sub']
  simp only [crossSlideStage, List.range'_zero, KLRAlgebra.ψw_nil, one_mul, mul_one, add_zero,
    Nat.sub_zero, Nat.sub_self]

end Generic

section Sliding

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max n:max hn:max =>
  (KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn) : Rp)
local notation "Aψ" q:max r:max => (KLRAlgebra.ψw (List.range' q r) : Rp)

omit [DecidableEq I] in
theorem add_add_one_lt_M {q : ℕ} (hq : q + 2 ≤ m) : q + N + 1 < M := by
  have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega

/-- The braid defect without dots: the passing strand on the right leaves the window at the top.
-/
theorem crossSlideBase_mem (u : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 2 ≤ m) {c : ℕ}
    (hc : c < N) (v : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (hv : ∀ r : Fin 2, v.lbl ⟨q + N + 1, add_add_one_lt_M hq⟩ ≠ cupColour j hj (.inr r)) :
    E u (q + 2) hq * (Aψ (q + 1) c * Aψ q c *
        (KLRAlgebra.e (wordProd M (List.range' (q + 2 + c) (N - 1 - c)) • v) *
          Aψ (q + 2 + c) (N - 1 - c))) ∈ exitSpan Q Λ Λc j hj u (q + 2) hq := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have he : (KLRAlgebra.e (wordProd M (List.range' (q + 2 + c) (N - 1 - c)) • v) *
      Aψ (q + 2 + c) (N - 1 - c) : Rp) = Aψ (q + 2 + c) (N - 1 - c) * KLRAlgebra.e v := by
    rw [KLRAlgebra.e_mul_ψw, inv_smul_smul]
  have hc1 : Commute (Aψ (q + 1) c) (Aψ (q + 2 + c) (N - 1 - c)) :=
    KLRAlgebra.commute_ψw_ψw fun p hp p' hp' => by
      rw [List.mem_range'_1] at hp hp'; omega
  have hc2 : Commute (Aψ q c) (Aψ (q + 2 + c) (N - 1 - c)) :=
    KLRAlgebra.commute_ψw_ψw fun p hp p' hp' => by
      rw [List.mem_range'_1] at hp hp'; omega
  rw [he, ← mul_assoc (Aψ (q + 1) c * Aψ q c), (hc1.mul_left hc2).eq, eSum_insertSet,
    Finset.sum_mul]
  refine Submodule.sum_mem _ fun w' _ => ?_
  by_cases hb : (w'.lbl ⟨c, hc⟩).isLeft
  · rw [mul_assoc (Aψ (q + 2 + c) (N - 1 - c)), ← mul_assoc (KLRAlgebra.e _),
      e_insertSeq_mul_exit u hq w' c]
    exact mem_exitSpan u hq (e_mul_exit_mem_capNull w' hc hb) _
  · rw [← KLRAlgebra.ψw_append, ← KLRAlgebra.ψw_append, ← mul_assoc, KLRAlgebra.e_mul_ψw,
      mul_assoc, KLRAlgebra.e_mul_e]
    split_ifs with heq
    swap
    · rw [mul_zero]; exact zero_mem _
    exfalso
    have h1 := congrArg (fun t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) =>
      t.lbl ⟨q + 2 + c, by omega⟩) (inv_smul_eq_iff.mp heq)
    rw [insertSeq_lbl_win u hq _ ⟨c, by rw [Multiset.card_map]; exact hc⟩ rfl, Seq.map_lbl,
      wordProd_append, wordProd_append, mul_smul, mul_smul,
      KL2.lbl_range'_smul (by omega) _ _ ⟨q + N + 1, by omega⟩
        (by unfold KL2.rfun; dsimp only; split_ifs <;> omega),
      KL2.lbl_range'_smul (by omega) _ _ ⟨q + N + 1, by omega⟩
        (by unfold KL2.rfun; dsimp only; split_ifs <;> omega),
      KL2.lbl_range'_smul (by omega) _ _ ⟨q + N + 1, by omega⟩
        (by unfold KL2.rfun; dsimp only; split_ifs <;> omega)] at h1
    rcases hw : w'.lbl ⟨c, hc⟩ with i | r
    · simp [hw] at hb
    · exact hv r (hw ▸ h1).symm

omit [DecidableEq I] in
theorem add_add_lt_M {q c : ℕ} (hq : q + 2 ≤ m) (hc : c < N) : q + 2 + c < M := by
  have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega

/-- **The braid defects lie in `exitSpan`**: dots on the two left strands at the defect slide down
to the bottom, a dot on the right strand slides up to the top of the window. -/
theorem crossSlideTerm_mem (u : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 2 ≤ m) {c : ℕ}
    (hc : c < N) (v : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (hv : ∀ r : Fin 2, v.lbl ⟨q + N + 1, add_add_one_lt_M hq⟩ ≠ cupColour j hj (.inr r))
    (p : MvPolynomial (Fin 3) k) :
    E u (q + 2) hq * (Aψ (q + 1) c * Aψ q c * (KLRAlgebra.pol (MvPolynomial.rename
        ![⟨q + c, Nat.lt_of_le_of_lt (by omega) (add_add_lt_M hq hc)⟩,
          ⟨q + c + 1, Nat.lt_of_le_of_lt (by omega) (add_add_lt_M hq hc)⟩,
          ⟨q + 2 + c, add_add_lt_M hq hc⟩] p) *
        (KLRAlgebra.e (wordProd M (List.range' (q + 2 + c) (N - 1 - c)) • v) *
          Aψ (q + 2 + c) (N - 1 - c)))) ∈ exitSpan Q Λ Λc j hj u (q + 2) hq := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  set G := (KLRAlgebra.e (wordProd M (List.range' (q + 2 + c) (N - 1 - c)) • v) *
    Aψ (q + 2 + c) (N - 1 - c) : Rp) with hG
  have hxG : ∀ b : Fin M, (∀ p ∈ List.range' (q + 2 + c) (N - 1 - c),
      (b : ℕ) ≠ p ∧ (b : ℕ) ≠ p + 1) → (KLRAlgebra.x b * G : Rp) = G * KLRAlgebra.x b :=
    fun b hb => by
      rw [hG, ← mul_assoc, KLRAlgebra.x_mul_e, mul_assoc, (KLRAlgebra.commute_x_ψw hb).eq,
        ← mul_assoc]
  have stepR : ∀ (b : Fin M), (∀ p ∈ List.range' (q + 2 + c) (N - 1 - c),
      (b : ℕ) ≠ p ∧ (b : ℕ) ≠ p + 1) → ∀ f : MvPolynomial (Fin M) k,
      E u (q + 2) hq * (Aψ (q + 1) c * Aψ q c * (KLRAlgebra.pol f * G)) ∈
        exitSpan Q Λ Λc j hj u (q + 2) hq →
      E u (q + 2) hq * (Aψ (q + 1) c * Aψ q c * (KLRAlgebra.pol f * KLRAlgebra.x b * G)) ∈
        exitSpan Q Λ Λc j hj u (q + 2) hq := fun b hb f hf => by
    rw [mul_assoc (KLRAlgebra.pol f), hxG b hb]
    convert exitSpan_mul_right u hq hf (KLRAlgebra.x b) using 1
    simp only [mul_assoc]
  have stepL : ∀ f : MvPolynomial (Fin M) k,
      E u (q + 2) hq * (Aψ (q + 1) c * Aψ q c * (KLRAlgebra.pol f * G)) ∈
        exitSpan Q Λ Λc j hj u (q + 2) hq →
      E u (q + 2) hq * (Aψ (q + 1) c * Aψ q c * (KLRAlgebra.pol f *
        KLRAlgebra.x ⟨q + 2 + c, add_add_lt_M hq hc⟩ * G)) ∈
        exitSpan Q Λ Λc j hj u (q + 2) hq := fun f hf => by
    set x₀ := (KLRAlgebra.x ⟨q + 2 + c, add_add_lt_M hq hc⟩ : Rp) with hx₀
    have hP : KLRAlgebra.pol f * x₀ = x₀ * KLRAlgebra.pol f := by
      rw [hx₀, ← KLRAlgebra.pol_X, ← map_mul, ← map_mul, mul_comm]
    have hA : Commute x₀ (Aψ (q + 1) c * Aψ q c) :=
      (KLRAlgebra.commute_x_ψw fun p hp => by
        rw [List.mem_range'_1] at hp; dsimp only; omega).mul_right
      (KLRAlgebra.commute_x_ψw fun p hp => by rw [List.mem_range'_1] at hp; dsimp only; omega)
    rw [hP, mul_assoc x₀, ← mul_assoc _ x₀, ← hA.eq, mul_assoc x₀, ← mul_assoc,
      ← KLRAlgebra.x_mul_eSum, show (x₀ * E u (q + 2) hq : Rp) = ι u (q + 2) hq
        (KLRAlgebra.x ⟨c, hc⟩) * E u (q + 2) hq by
        rw [insertMap_x, mul_assoc, (KLRAlgebra.eSum_idem _).eq], mul_assoc]
    exact insertMap_mul_mem_exitSpan u hq _ hf
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, MvPolynomial.algHom_C, ← Algebra.smul_def, mul_smul_comm,
      mul_smul_comm]
    exact Submodule.smul_mem _ a (crossSlideBase_mem u hq hc v hv)
  | add p p' hp hp' =>
    rw [map_add, map_add, add_mul, mul_add, mul_add]
    exact add_mem hp hp'
  | mul_X p n hp =>
    rw [map_mul, MvPolynomial.rename_X, map_mul, KLRAlgebra.pol_X]
    fin_cases n
    · exact stepR ⟨q + c, Nat.lt_of_le_of_lt (by omega) (add_add_lt_M hq hc)⟩
        (fun p' hp' => by rw [List.mem_range'_1] at hp'; dsimp only; omega) _ hp
    · exact stepR ⟨q + c + 1, Nat.lt_of_le_of_lt (by omega) (add_add_lt_M hq hc)⟩
        (fun p' hp' => by rw [List.mem_range'_1] at hp'; dsimp only; omega) _ hp
    · exact stepL _ hp

/-- **The crossing of two passing strands slides through the window, up to exits**: on a bottom
loading whose strand at `q + N + 1` is not red, the crossing at the top of the two passages under
the window `[q + 2, q + N + 2)` and the crossing at their bottom differ, below the top window
idempotents, by diagrams in which a strand leaves the window at the top. -/
theorem eSum_mul_crossSlide_mem (u : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 2 ≤ m)
    (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (ht : ∀ r : Fin 2, t.lbl ⟨q + N + 1, add_add_one_lt_M hq⟩ ≠ cupColour j hj (.inr r)) :
    E u (q + 2) hq * (KLRAlgebra.ψ q * Aψ (q + 1) N * Aψ q N * KLRAlgebra.e t -
        Aψ (q + 1) N * Aψ q N * KLRAlgebra.ψ (q + N) * KLRAlgebra.e t) ∈
      exitSpan Q Λ Λc j hj u (q + 2) hq := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  rw [crossSlide_eq_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  rw [Finset.mem_range] at hc
  rw [crossSlideStage_sub_succ hc]
  set v := wordProd M (List.range' (q + c + 1) (N - 1 - c)) • t with hvdef
  have hv : ∀ r : Fin 2, v.lbl ⟨q + N + 1, add_add_one_lt_M hq⟩ ≠ cupColour j hj (.inr r) := by
    intro r
    rw [hvdef, KL2.lbl_range'_smul (by omega) _ _ ⟨q + N + 1, add_add_one_lt_M hq⟩
      (by unfold KL2.rfun; dsimp only; split_ifs <;> omega)]
    exact ht r
  have h1 : (Aψ (q + 1) c * Aψ q c *
      (KLRAlgebra.ψ (q + c) * KLRAlgebra.ψ (q + c + 1) * KLRAlgebra.ψ (q + c) -
        KLRAlgebra.ψ (q + c + 1) * KLRAlgebra.ψ (q + c) * KLRAlgebra.ψ (q + c + 1)) *
      Aψ (q + 2 + c) (N - 1 - c) * Aψ (q + c + 1) (N - 1 - c) * KLRAlgebra.e t : Rp) =
      Aψ (q + 1) c * Aψ q c *
        ((KLRAlgebra.ψ (q + c) * KLRAlgebra.ψ (q + c + 1) * KLRAlgebra.ψ (q + c) -
          KLRAlgebra.ψ (q + c + 1) * KLRAlgebra.ψ (q + c) * KLRAlgebra.ψ (q + c + 1)) *
          KLRAlgebra.e (wordProd M (List.range' (q + 2 + c) (N - 1 - c)) • v)) *
        Aψ (q + 2 + c) (N - 1 - c) * Aψ (q + c + 1) (N - 1 - c) := by
    simp only [mul_assoc]
    rw [KLRAlgebra.ψw_mul_e, ← hvdef, ← mul_assoc (Aψ (q + 2 + c) (N - 1 - c)),
      KLRAlgebra.ψw_mul_e]
    simp only [mul_assoc]
  rw [h1, KLRAlgebra.braid (q + c) (by omega)]
  split_ifs
  · rw [ncEval_x_three, show (⟨q + c + 2, by omega⟩ : Fin M) =
        ⟨q + 2 + c, add_add_lt_M hq hc⟩ from Fin.ext (by dsimp only; omega)]
    convert exitSpan_mul_right u hq (crossSlideTerm_mem u hq hc v hv _)
      (Aψ (q + c + 1) (N - 1 - c)) using 1
    simp only [mul_assoc]
    rfl
  · rw [mul_zero, zero_mul, zero_mul, mul_zero]
    exact zero_mem _

end Sliding

end Categorification.Stendhal.CupCap
