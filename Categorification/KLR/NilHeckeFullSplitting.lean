/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.NilHeckeBlockSplitting
import Categorification.KLR.DividedPowerDecomposition

/-!
# `1 ∈ NH_n` splits into `n!` copies of `e_n`

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.2, Example 3: the regular representation of `NH_n` is the sum of `n!`
copies of the polynomial representation `NH_n e_n`. We record the underlying splitting
`1 = ∑_j a_j b_j`, `b_i a_j = δ_{ij} e_n` in the nilHecke ring `NH_n` with `n!` indices.

It is obtained by iterating the splitting of `e_N ⊗ 1` through `e_{N+1}`
(`KLRAlgebra.isSplitting_divIdem_succ`) along the block `[0, n)` in `R(n i) ≅ NH_n`
(`KLRAlgebra.nilHeckeEquiv`).

## Main results

* `Graded.IsSplitting.map`: splittings are preserved by ring homomorphisms.
* `NilHecke.exists_isSplitting_one_idemNH`: `1 ∈ NH_n` splits through `n!` copies of the
  idempotent `e_n = x^δ ∂_{w_0}` (`idemNH`).
-/

namespace Categorification

namespace Graded.IsSplitting

variable {A B : Type*} [Ring A] [Ring B] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E' : A} {E a b : ι → A}

/-- The image of a splitting under a ring homomorphism is a splitting. -/
theorem map {F : Type*} [FunLike F A B] [RingHomClass F A B] (h : IsSplitting E' E a b)
    (f : F) :
    IsSplitting (f E') (fun j => f (E j)) (fun j => f (a j)) (fun j => f (b j)) where
  mul_eq i j := by rw [← map_mul, h.mul_eq]; split_ifs <;> simp
  sum_eq := by rw [← h.sum_eq, map_sum]; simp only [map_mul]

end Graded.IsSplitting

namespace NilHecke

open KLR KLRAlgebra

variable (k : Type*) [CommRing k]

theorem congrRank_idemNH {n n' : ℕ} (h : n = n') :
    congrRank (k := k) h ⟨idemNH k n, idemNH_mem⟩ = ⟨idemNH k n', idemNH_mem⟩ := by
  subst h; rfl

section KLR

variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (n : ℕ)

local notation "ν" => Multiset.replicate n ()
local notation "A" => KLRAlgebra k Q ν

/-- The unique sequence of `R(n ·)`. -/
noncomputable abbrev seqUnit : Seq ν :=
  (Seq.uniqueOfForall (forall_mem_replicate () n)).default

theorem isBlocks_seqUnit {N : ℕ} (hN : N ≤ Multiset.card ν) :
    IsBlocks (seqUnit n) [(0, N)] where
  le b hb := by rw [List.mem_singleton] at hb; subst hb; simpa using hN
  const _ _ _ _ _ _ _ _ := Subsingleton.elim _ _
  disj := List.pairwise_singleton _ _

/-- The splitting of `1_{i^n}` through `N!` copies of `e_{i, N}` along the block `[0, N)`. -/
theorem exists_isSplitting_divIdem : ∀ N : ℕ, N ≤ Multiset.card ν →
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (a b : ι → A),
      Fintype.card ι = N.factorial ∧
      Graded.IsSplitting (e (seqUnit n)) (fun _ => divIdem (seqUnit n) [(0, N)]) a b
  | 0, _ => by
    refine ⟨Unit, inferInstance, inferInstance, fun _ => e (seqUnit n),
      fun _ => e (seqUnit n), rfl, ⟨fun _ _ => ?_, ?_⟩⟩
    · rw [ite_eq_left rfl, e_mul_self, divIdem, blocksElt_cons, blockElt_zero, one_mul,
        blocksElt_nil, one_mul]
    · simp [e_mul_self]
  | N + 1, hN => by
    obtain ⟨ι, _, _, a, b, hc, hS⟩ := exists_isSplitting_divIdem N (by omega)
    have hB := isBlocks_seqUnit n hN
    have hstep := isSplitting_divIdem_succ (k := k) (Q := Q) (bs := []) hB
    refine ⟨ι × Fin (N + 1), inferInstance, inferInstance, _, _, ?_,
      hS.trans hstep (isIdempotentElem_divIdem hB) (e_mul_self _)⟩
    rw [Fintype.card_prod, hc, Fintype.card_fin, Nat.factorial_succ, mul_comm]

theorem divIdem_seqUnit :
    (divIdem (seqUnit n) [(0, Multiset.card ν)] : A) =
      blockIdem (seqUnit n) 0 (Multiset.card ν) := by
  rw [divIdem, blocksElt_cons, blocksElt_nil, mul_one, blockIdem]

end KLR

variable [IsDomain k]

/-- **KL I §2.2, Example 3**: `1 ∈ NH_n` splits through `n!` copies of the idempotent
`e_n = x^δ ∂_{w_0}`: there are `a_j, b_j ∈ NH_n` (`n!` indices `j`) with `b_i a_j = δ_{ij} e_n`
and `∑_j a_j b_j = 1`. -/
theorem exists_isSplitting_one_idemNH (n : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (a b : ι → nilHecke k n),
      Fintype.card ι = n.factorial ∧
      Graded.IsSplitting 1 (fun _ => ⟨idemNH k n, idemNH_mem⟩) a b := by
  let Q : Unit → Unit → MvPolynomial (Fin 2) k := fun _ _ => 1
  obtain ⟨ι, _, _, a, b, hc, hS⟩ :=
    exists_isSplitting_divIdem k Q n (Multiset.card (Multiset.replicate n ())) le_rfl
  have hφ := hS.map (nilHeckeEquiv Q () n)
  refine ⟨ι, inferInstance, inferInstance, fun j => nilHeckeEquiv Q () n (a j),
    fun j => nilHeckeEquiv Q () n (b j), by rw [hc, Multiset.card_replicate], ?_⟩
  convert hφ using 2
  · exact (nilHeckeEquiv_e Q () n _).symm
  · rw [divIdem_seqUnit, nilHeckeEquiv, AlgEquiv.trans_apply,
      nilHeckeEquivOfForall_blockIdem, congrRank_idemNH]

end NilHecke

end Categorification
