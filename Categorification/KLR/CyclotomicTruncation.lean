/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.NilHeckeBlockSplitting
import Categorification.KLR.Cyclotomic
import Categorification.KLR.Examples.NilHecke

/-!
# Cyclotomic truncation of a constant block

Webster, arXiv:1309.3796v2, proof of Proposition 3.21 (integrability).
If the first dot of a constant block of length N+1 satisfies the relation
x^N e(s) = 0, its staircase idempotent vanishes, and nilHecke splitting
forces the whole boundary idempotent to vanish. In a pure-colour cyclotomic
block this gives the highest-weight truncation over a commutative ring.
-/

namespace Categorification.KLR
namespace KLRAlgebra

open MvPolynomial
variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
    {ν : Multiset I} {B : Type*} [Ring B]
local notation "R" => KLRAlgebra k Q ν

private lemma predecessor_zero (φ : R →+* B) {s : Seq ν} {p n : ℕ}
    (h : IsBlocks s [(p,n+1)]) (h₁ : φ (divIdem s [(p,n+1)]) = 0) :
    φ (divIdem s [(p,n)]) = 0 := by
  let H := isSplitting_divIdem_succ (k := k) (Q := Q) h
  let E : R := divIdem s [(p,n)]
  have he : IsIdempotentElem E := isIdempotentElem_divIdem (h.cons_mono (Nat.le_succ n))
  have ht := congrArg (E * ·) H.sum_eq
  simp only [Finset.mul_sum, ← mul_assoc] at ht
  change φ E = 0
  rw [← he.eq, ← ht, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [mul_assoc E (divIdem s []), H.left_mul_a j, map_mul, map_mul, h₁, mul_zero, zero_mul]

/-- NilHecke splitting kills a boundary word if its constant block is longer
than a nilpotence bound on the first dot of that block. -/
theorem map_e_eq_zero_of_block_dot_pow (φ : R →+* B) (s : Seq ν) (p N : ℕ)
    (hb : p + (N+1) ≤ ν.card) (hc : IsConstOn s p (N+1))
    (hx : φ (x ⟨p, by omega⟩ ^ N * e s) = 0) :
    φ (e s) = 0 := by
  classical
  have hblocks : IsBlocks s [(p,N+1)] := by
    refine ⟨?_, ?_, by simp⟩
    · intro b h
      obtain rfl := List.mem_singleton.mp h
      exact hb
    · intro b h
      obtain rfl := List.mem_singleton.mp h
      exact hc
  have stop : φ (divIdem s [(p,N+1)]) = 0 := by
    let v (a : Fin (N+1)) : MvPolynomial (Fin ν.card) k :=
      if h : p+a < ν.card then X ⟨p+a,h⟩ ^ (N+1-1-a) else 1
    have hδ : blockDelta p (N+1) = (∏ a ∈ Finset.univ.erase (0 : Fin (N+1)), v a) *
        X ⟨p, by omega⟩ ^ N := by
      change ∏ a, v a = _
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (0 : Fin (N+1)))]
      simp [v, show p < ν.card by omega]
    rw [divIdem, blocksElt_cons, blocksElt_nil, mul_one, blockElt, mul_assoc, blockψ_mul_e hc,
      hδ, map_mul (pol (Q := Q) (ν := ν)), map_pow (pol (Q := Q) (ν := ν)), pol_X, mul_assoc, ← mul_assoc (x _ ^ N), map_mul, map_mul, hx,
      zero_mul, mul_zero]
  have down (r : ℕ) (hr : r ≤ N+1) : φ (divIdem s [(p,N+1-r)]) = 0 := by
    induction r with
    | zero => simpa using stop
    | succ r ih =>
      have h := ih (by omega)
      let j := N+1-(r+1)
      have hj : j+1 = N+1-r := by dsimp [j]; omega
      have hle : j+1 ≤ N+1 := by omega
      exact predecessor_zero φ (hblocks.cons_mono hle) (hj ▸ h)
  simpa [divIdem, blocksElt, blockElt_zero] using down (N+1) le_rfl

end KLRAlgebra

namespace CycKLR

open KLRAlgebra
variable {I k : Type*} [DecidableEq I] [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : I → ℕ) (i : I) (n : ℕ)

/-- The single-colour cyclotomic algebra vanishes above its highest-weight
multiplicity, for any coefficient ring and any parameters. -/
theorem subsingleton_replicate_of_lt (hn : Λ i < n) :
    Subsingleton (CycKLR k Q (fun j => Polynomial.X ^ Λ j) (Multiset.replicate n i)) := by
  let ν := Multiset.replicate n i
  let π := mk k Q (fun j => Polynomial.X ^ Λ j) ν
  have hm : ν.card = n := Multiset.card_replicate ..
  have h0 : 0 < ν.card := by omega
  have hall : ∀ c ∈ ν, c = i := fun c h => Multiset.eq_of_mem_replicate h
  have hz (s : Seq ν) : π (e s) = 0 := by
    apply map_e_eq_zero_of_block_dot_pow π.toRingHom s 0 (Λ i) (by omega)
    · intro a b _ _ _ _
      exact Seq.lbl_eq_of_forall hall s a b
    · have h := mk_cycElt (k := k) (ν := ν) (Q := Q) (a := fun j => Polynomial.X ^ Λ j) s
      rw [cycElt_of_pos _ _ _ h0] at h
      have hci : s.lbl ⟨0,h0⟩ = i := hall _ (Seq.mem _ _)
      simpa [hci, π] using h
  apply subsingleton_of_zero_eq_one
  rw [← map_one π, ← sum_e (ν := ν), map_sum]
  exact (Finset.sum_eq_zero fun s _ => hz s).symm

end CycKLR
end Categorification.KLR
