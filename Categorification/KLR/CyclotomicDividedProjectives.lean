/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.Prop320KL2
import Categorification.KLR.CyclotomicQuotientK0
import Categorification.KLR.SymmetricFactorization
import Categorification.KLR.Rouquier.Polynomial

/-!
# Divided projective classes for general cyclotomic parameters

Webster, arXiv:1309.3796v2, §3.4, proof of Proposition 3.21. The factorial
splitting of a constant-colour block uses only its nilHecke relations, so it
applies to general KLR parameters. Applying the affine divided-projective
spanning theorem and extending to the cyclotomic quotient gives the integral
span by projected divided projectives.
-/

noncomputable section

namespace Categorification.KLR.GradingDatum

open Categorification.Graded KLRAlgebra QuantumGroup LaurentPolynomial KL2

variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  (G : GradingDatum Q) (hs : ∀ i j, G.degΨ i j = G.degΨ j i) {ν : Multiset I}

local notation "A" => KLRAlgebra k Q ν
local notation "m" => Multiset.card ν

private def blockProjective (t : Seq ν) (bs : List (ℕ × ℕ)) (h : IsBlocks t bs) : GProj (G.grade ν) :=
  GProj.ofIdempotent (hflip (divIdem t bs : A)) (isIdempotentElem_hflip_divIdem h)
    (G.hflip_mem_grade hs (divIdem_mem_grade G h))

private theorem block_succ {i : Seq ν} {p n : ℕ} {bs : List (ℕ × ℕ)}
    (h : IsBlocks i ((p, n + 1) :: bs)) {hh : ℤ}
    (hdeg : ∀ a : Fin m, p ≤ a → (a : ℕ) < p + (n + 1) → G.degX (i.lbl a) = 2 * hh) :
    K0.of (blockProjective G hs i ((p, n) :: bs) (h.cons_mono (Nat.le_succ n))) =
      (T (-(hh * n)) * qint (tUnit hh) (n + 1)) • K0.of (blockProjective G hs i ((p, n + 1) :: bs) h) := by
  have hpn := h.le _ List.mem_cons_self
  have hc := h.const _ List.mem_cons_self
  simp only at hpn
  have hcl : ∀ a : Fin (Multiset.card ν), p ≤ a → (a : ℕ) < p + (n + 1) →
      i.lbl a = i.lbl ⟨p, by omega⟩ := fun a h1 h2 => hc a _ h1 h2 le_rfl (by simp only; omega)
  have hc2 : G.degX (i.lbl ⟨p, by omega⟩) = 2 * hh :=
    hdeg ⟨p, by omega⟩ le_rfl (by simp only; omega)
  have S := (isSplitting_divIdem_succ (k := k) (Q := Q) h).map_anti GradingDatum.hflipAddHom hflip_mul

  have hflip_apply (a : A) : hflipAddHom a = hflip a := rfl
  simp only [hflip_apply] at S
  rw [blockProjective, blockProjective, K0.of_ofIdempotent_eq_sum_of_isSplitting (dg := fun j : Fin (n + 1) =>
    G.degX (i.lbl ⟨p, by omega⟩) * ((n : ℤ) - j)) S (fun j => ?_)
    (fun j => ?_) _ (fun _ => _) _ (fun _ => _), hc2, ← sum_T_mul_sub, Finset.sum_smul]
  · exact G.hflip_mem_grade hs (blockB_mem_grade G hpn hcl hc
      (show (j : ℕ) ≤ n by omega))
  · refine G.hflip_mem_grade hs ?_
    have := SetLike.mul_mem_graded (divIdem_mem_grade G h.tail)
      (blockA_mem_grade G hpn hcl hc j)
    convert this using 2
    ring

private theorem block_factorial {i : Seq ν} {p : ℕ} {bs : List (ℕ × ℕ)} (hbs : IsBlocks i bs)
    {hh : ℤ} :
    ∀ {n : ℕ} (h : IsBlocks i ((p, n) :: bs))
      (_hdeg : ∀ a : Fin m, p ≤ a → (a : ℕ) < p + n → G.degX (i.lbl a) = 2 * hh),
      K0.of (blockProjective G hs i bs hbs) = blockFactor2 hh n • K0.of (blockProjective G hs i ((p, n) :: bs) h)
  | 0, h, _ => by
    rw [blockFactor2_zero, one_smul]
    refine K0.of_ofIdempotent_congr (congrArg hflip ?_) _ _ _ _
    rw [divIdem, divIdem, blocksElt_cons]
    simp only
    rw [blockElt_zero, one_mul]
  | n + 1, h, hdeg => by
    rw [block_factorial hbs (h.cons_mono (Nat.le_succ n))
      (fun a h1 h2 => hdeg a h1 (by omega)), block_succ G hs h hdeg, ← mul_smul,
      blockFactor2_succ]

private theorem blocks_factorial {t : Seq ν} (hh : ℕ → ℤ) :
    ∀ {bs : List (ℕ × ℕ)} (h : IsBlocks t bs)
      (_hdeg : ∀ b ∈ bs, ∀ a : Fin m, b.1 ≤ a → (a : ℕ) < b.1 + b.2 →
        G.degX (t.lbl a) = 2 * hh b.1),
      K0.of (GProj.ofIdempotent (𝒜 := G.grade ν) (e t) (e_mul_self t) (G.e_mem_grade t)) =
        (bs.map fun b => blockFactor2 (hh b.1) b.2).prod • K0.of (blockProjective G hs t bs h)
  | [], h, _ => by
    rw [List.map_nil, List.prod_nil, one_smul]
    exact K0.of_ofIdempotent_congr (e := (e t : A)) (e' := hflip (divIdem t [] : A))
      (by rw [divIdem_nil, hflip_e]) _ _ _ _
  | b :: bs, h, hdeg => by
    rw [blocks_factorial hh h.tail (fun b' hb' => hdeg b' (List.mem_cons_of_mem _ hb')),
      block_factorial G hs (p := b.1) (n := b.2) h.tail h (hdeg b List.mem_cons_self),
      List.map_cons, List.prod_cons, ← mul_smul, mul_comm]

/-- The divided-power projective on a word, using the nilHecke idempotent of
its constant-colour blocks and the Cartan grading shift (KL I, §2.5 and KL II, §3). -/
def dividedProjective (C : CartanDatum I) (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    GProj (G.grade ν) := (blockProjective G hs _ _ (isBlocks_ofList d h)).shift (-divAngle2 C d)

/-- The quantum factorial decomposition for any KLR parameters whose grading
has the Cartan dot degrees and symmetric crossing degrees (KL I, §2.5 and KL II, §3). -/
theorem of_expanded_eq_factorial (C : CartanDatum I) (hX : ∀ i, G.degX i = C.dot i i)
    (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    K0.of (GProj.ofIdempotent (𝒜 := G.grade ν) (e (Seq.ofList _ h)) (e_mul_self _) (G.e_mem_grade _)) =
      divQFact2 C d • K0.of (dividedProjective G hs C d h) := by
  have hdeg : ∀ b ∈ blocksDiv d 0, ∀ a : Fin m, b.1 ≤ a → (a : ℕ) < b.1 + b.2 →
      G.degX ((Seq.ofList (expandDiv d) h).lbl a) = 2 * labHalf C (expandDiv d) b.1 := by
    intro b hb a h1 h2
    have hm : (expandDiv d).length = m := by rw [← Multiset.coe_card, h]
    have hb1 : b.1 < m := lt_of_le_of_lt h1 a.2
    have hc := (isBlocks_ofList d h).const b hb a ⟨b.1, hb1⟩ h1 h2 le_rfl (by simp only; omega)
    rw [hc, hX, Seq.ofList_lbl, labHalf_of_lt _ (by rw [hm]; exact hb1)]
    obtain ⟨r, hr⟩ := C.dot_self_even ((expandDiv d)[b.1]'(by rw [hm]; exact hb1))
    simp only []
    omega
  rw [blocks_factorial G hs _ (isBlocks_ofList d h) hdeg]
  have hprod := prod_blockFactor2_blocksDiv (C := C) d []
  simp only [List.length_nil, List.nil_append] at hprod
  rw [hprod, dividedProjective, ← K0.T_smul_of, ← mul_smul, mul_comm]

section Field

variable {J F : Type*} [DecidableEq J] [Field F] {S : J → J → MvPolynomial (Fin 2) F}
  (H : GradingDatum S) (hs' : ∀ i j, H.degΨ i j = H.degΨ j i) (C : CartanDatum J)
  (β : Multiset J)

/-- Divided-word projective classes span the affine algebra in each weight.
Only the diagonal of the Cartan datum enters the shifts of the nilHecke blocks. -/
theorem span_dividedProjective (hX : ∀ i, H.degX i = C.dot i i) (hsym : KLRSymm S)
    (hQ : ∀ i j, i ≠ j → S i j ≠ 0) :
    Submodule.span (LaurentPolynomial ℤ) {z | ∃ (d : List (J × ℕ))
      (h : (expandDiv d : Multiset J) = β), z = K0.of (H.dividedProjective hs' C d h)} = ⊤ := by
  have hpos (i) : 0 < H.degX i := (hX i).symm ▸ C.dot_self_pos i
  let FH := symmP_factor S hsym
  let FN := symmP_ne_zero S hQ
  apply top_unique
  rw [← (H.k0Basis FH FN hpos β).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  exact H.k0Basis_mem_span_of_div FH FN hpos β (H.dividedProjective hs' C) (divQFact2 C)
    (fun d h => H.of_expanded_eq_factorial hs' C hX d h) (KL2Gamma.evalOne_divQFact2 C) b

end Field

end Categorification.KLR.GradingDatum

namespace Categorification.KLR.CycKLR

open Categorification.Graded KLRAlgebra QuantumGroup LaurentPolynomial KL2

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (G : GradingDatum Q) (hs : ∀ i j, G.degΨ i j = G.degΨ j i)
  (C : CartanDatum I) (Λ : I → ℕ) (ν : Multiset I)

local notation "π" => mk k Q (fun i => Polynomial.X ^ Λ i) ν

/-- The cyclotomic principal projective on a divided word, with Cartan shift and the
projected nilHecke idempotent (Webster, proof of Proposition 3.21). -/
def dividedProjective (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    GProj (grade G Λ ν) :=
  let t := Seq.ofList (expandDiv d) h
  let e : KLRAlgebra k Q ν := hflip (divIdem t (blocksDiv d 0))
  (GProj.ofIdempotent (𝒜 := grade G Λ ν) (π e)
    ((isIdempotentElem_hflip_divIdem (Q := Q) (isBlocks_ofList d h)).map (π))
    (Graded.mem_map_of_mem _ (π).toLinearMap (G.hflip_mem_grade hs
      (divIdem_mem_grade G (isBlocks_ofList d h))))).shift (-divAngle2 C d)

/-- Projecting the affine divided projective preserves its nilHecke idempotent
and grading shift. -/
theorem quotientK0_dividedProjective (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    quotientK0 G Λ ν (K0.of (G.dividedProjective hs C d h)) =
      K0.of (dividedProjective G hs C Λ ν d h) := by
  unfold GradingDatum.dividedProjective dividedProjective
  rw [← K0.T_smul_of, map_smul, ← K0.T_smul_of]
  congr 1
  exact quotientK0_ofIdempotent G Λ ν _ _

/-- In the cyclotomic algebra the expanded black sequence projective is the
Cartan quantum factorial times the shifted divided projective in `K₀`. -/
theorem of_expanded_eq_factorial (hX : ∀ i, G.degX i = C.dot i i)
    (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    K0.of (GProj.ofIdempotent (𝒜 := grade G Λ ν) (π (e (Seq.ofList _ h)))
      (IsIdempotentElem.map (e_mul_self _) (π))
      (Graded.mem_map_of_mem _ (π).toLinearMap (G.e_mem_grade _))) =
        divQFact2 C d • K0.of (dividedProjective G hs C Λ ν d h) := by
  have H := congrArg (quotientK0 G Λ ν) (G.of_expanded_eq_factorial hs C hX d h)
  rw [map_smul, quotientK0_dividedProjective] at H
  exact (quotientK0_ofIdempotent G Λ ν (e_mul_self (Q := Q) (Seq.ofList _ h))
    (G.e_mem_grade _)).symm.trans H

/-- For general symmetric, nonzero off-diagonal parameters, the shifted divided-word
projectives span the cyclotomic integral Laurent lattice in every weight (Webster,
arXiv:1309.3796v2, §3.4, proof of Proposition 3.21). -/
theorem span_dividedProjective (hX : ∀ i, G.degX i = C.dot i i) (hsym : KLRSymm Q)
    (hQ : ∀ i j, i ≠ j → Q i j ≠ 0) :
    Submodule.span (LaurentPolynomial ℤ) {z | ∃ (d : List (I × ℕ))
      (h : (expandDiv d : Multiset I) = ν), z = K0.of (dividedProjective G hs C Λ ν d h)} = ⊤ := by
  have hpos (i) : 0 < G.degX i := (hX i).symm ▸ C.dot_self_pos i
  have ha := G.span_dividedProjective hs C ν hX hsym hQ
  apply top_unique
  rw [← LinearMap.range_eq_top.mpr (quotientK0_surjective G Λ ν hsym hpos),
    ← Submodule.map_top, ← ha, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨d, h, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨d, h, quotientK0_dividedProjective G hs C Λ ν d h⟩

/-- In the usual homogeneous Cartan parameter presentation, the projected divided
projective classes span with only the defining polynomial hypotheses (Webster,
§3.4, proof of Proposition 3.21). -/
theorem span_dividedProjective_of_rouquier (hQ : IsRouquierQ C Q) :
    Submodule.span (LaurentPolynomial ℤ) {z | ∃ (d : List (I × ℕ))
      (h : (expandDiv d : Multiset I) = ν), z = K0.of (dividedProjective hQ.gradingDatum
        (fun i j => congrArg Neg.neg (C.symm i j)) C Λ ν d h)} = ⊤ := by
  apply span_dividedProjective _ _ _ _ _ (fun _ => rfl) (fun i j hij => (hQ.symm i j hij).symm)
  intro i j hij hzero
  have hu := hQ.unit_coeff i j hij
  simp [hzero] at hu

/-- The divided-word projectives generate the total integral cyclotomic projective
Grothendieck group (Webster, §3.4, generation in Proposition 3.21). -/
theorem span_total_dividedProjective (hQ : IsRouquierQ C Q) :
    Submodule.span (LaurentPolynomial ℤ) {z : projectiveK0 hQ.gradingDatum Λ |
      ∃ (β : Multiset I) (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = β),
        z = DirectSum.lof (LaurentPolynomial ℤ) _ (fun γ => K0 (grade hQ.gradingDatum Λ γ)) β
          (K0.of (dividedProjective hQ.gradingDatum (fun i j => congrArg Neg.neg (C.symm i j)) C Λ β d h))} = ⊤ := by
  set V : Submodule (LaurentPolynomial ℤ) (projectiveK0 hQ.gradingDatum Λ) := Submodule.span _ _
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | of β y =>
    let l := DirectSum.lof (LaurentPolynomial ℤ) _ (fun γ => K0 (grade hQ.gradingDatum Λ γ)) β
    have H : ⊤ ≤ V.comap l := by
      rw [← span_dividedProjective_of_rouquier C Λ β hQ]
      apply Submodule.span_le.mpr
      rintro _ ⟨d, h, rfl⟩
      exact Submodule.subset_span ⟨β, d, h, rfl⟩
    exact H (Submodule.mem_top (x := y))

end Categorification.KLR.CycKLR
