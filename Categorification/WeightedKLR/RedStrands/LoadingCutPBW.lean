/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.QuotientBasis
import Categorification.WeightedKLR.RedStrands.LeftStandardModule
import Categorification.WeightedKLR.RedStrands.BlackIdempotent

/-!
# Loading-cut PBW support

To test the action of diagrams between two fixed loadings, it suffices
to test the projected reduced-word polynomial terms between those loadings.
-/

namespace Categorification.Stendhal
open KLR TypeA
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {l : ℕ} {ν : Multiset I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin l → I →₀ ℕ)
local notation "μ" => stendhalWeight l ν
local notation "n" => Multiset.card μ
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "π" => tensorOfKLR Q Λ ν

variable {M : Type*} [AddCommGroup M] [Module k M]
  [Module (TensorProductAlgebra k Q Λ ν) M] [IsScalarTower k (TensorProductAlgebra k Q Λ ν) M]

/-- A loading cut of any diagram action lies in a submodule containing all
projected reduced-word polynomial rows between the two loadings. -/
theorem loading_mul_smul_mem_of_projected_PBW
    {ρ : Equiv.Perm (Fin n) → List ℕ}
    (hρ : ∀ w, IsReduced n (ρ w) ∧ wordProd n (ρ w) = w)
    {s t : KLR.Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t) (z : M)
    (hz : seqIdem Q Λ s hs • z = z) (D : Submodule k M)
    (ann : ∀ w : Equiv.Perm (Fin n), w • s = t → ∀ p : MvPolynomial (Fin n) k,
      π (KLRAlgebra.ψw (ρ w) * KLRAlgebra.pol p * KLRAlgebra.e s) • z ∈ D)
    (a : T) : (seqIdem Q Λ t ht * a) • z ∈ D := by
  classical
  have ha : a ∈ Submodule.span k (Set.range (tensorProductTerm hρ Q Λ)) := by
    rw [span_tensorProductTerm hρ Q Λ]
    trivial
  induction ha using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨term,rfl⟩ := hd
    let row := tensorProductTerm hρ Q Λ term
    have hL : seqIdem Q Λ t ht * row = if term.1.2.1 • term.1.1 = t then row else 0 := by
      unfold row tensorProductTerm
      rw [← map_mul, e_mul_stendhalTerm]
      split_ifs <;> simp only [map_zero]
    have hR : row * seqIdem Q Λ s hs = if term.1.1 = s then row else 0 := by
      unfold row tensorProductTerm
      rw [← map_mul, stendhalTerm_mul_e]
      split_ifs <;> simp only [map_zero]
    change (seqIdem Q Λ t ht * row) • z ∈ D
    rw [hL]
    split_ifs with hw
    · rw [← hz, ← mul_smul, hR]
      split_ifs with hsrc
      · have hp : term.1.2.1 • s = t := hsrc ▸ hw
        have hrow : row = π (KLRAlgebra.stdElt ρ term.1) := by
          apply congrArg (TensorProductAlgebra.mk Q Λ ν)
          apply Subtype.ext
          exact ((Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).mp
            (stendhalTerm Q Λ (fun w => (hρ w).2) term).2).2.symm
        rw [hrow, KLRAlgebra.stdElt, hsrc]
        exact ann _ hp _
      · rw [zero_smul]; exact D.zero_mem
    · rw [zero_smul]; exact D.zero_mem
  | zero => rw [mul_zero, zero_smul]; exact D.zero_mem
  | add u v _ _ hu hv => rw [mul_add, add_smul]; exact D.add_mem hu hv
  | smul r b _ hb => rw [mul_smul_comm, smul_assoc]; exact D.smul_mem r hb

/-- A loading-fixed vector has zero component at a second loading under arbitrary
diagram action if all reduced-word terms between the two loadings kill it. -/
theorem loading_mul_smul_eq_zero_of_projected_PBW
    {ρ : Equiv.Perm (Fin n) → List ℕ}
    (hρ : ∀ w, IsReduced n (ρ w) ∧ wordProd n (ρ w) = w)
    {s t : KLR.Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t) (z : M)
    (hz : seqIdem Q Λ s hs • z = z)
    (ann : ∀ w : Equiv.Perm (Fin n), w • s = t → ∀ p : MvPolynomial (Fin n) k,
      π (KLRAlgebra.ψw (ρ w) * KLRAlgebra.pol p * KLRAlgebra.e s) • z = 0)
    (a : T) : (seqIdem Q Λ t ht * a) • z = 0 := by
  have h := loading_mul_smul_mem_of_projected_PBW Q Λ hρ hs ht z hz (⊥ : Submodule k M)
    (by
      intro w hw p
      simpa only [Submodule.mem_bot] using ann w hw p) a
  simpa only [Submodule.mem_bot] using h

end Categorification.Stendhal
