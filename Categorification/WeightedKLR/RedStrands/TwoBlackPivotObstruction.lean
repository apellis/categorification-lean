/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Stendhal

/-!
# A coupled right pivot at two black strands

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 and the cut after (6.21).
The two outgoing maps at the right extreme share a right-red crossing.
At exponent zero, its return crossing gives an explicit dependence and
a marked replacement with the same product at that pivot.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ
variable {A : Type*} [Ring A] [Algebra k A]
    (π : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν) →ₐ[k] A)

private theorem zeroExponent_rightLeg (v : Seq μ) (p : ℕ) (hp : p+1 < n)
    (b : Fin ℓ) (i : I) (hb : v.lbl ⟨p,by omega⟩ = .inr b)
    (hi : v.lbl ⟨p+1,hp⟩ = .inl i) (hex : Λ b i = 0) :
    π (ψ p * e (sadj n p • v)) * π (ψ p * e v) = π (e v) := by
  have sq := ψ_sq (Q := stendhalQ Q Λ) p hp v
  rw [hb,hi] at sq
  simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inr_inl, ncEval_x2,
    hex, pow_zero, map_one, one_mul] at sq
  have he : (ψ p * e v : KLRAlgebra k (stendhalQ Q Λ) μ) =
      e (sadj n p • v) * ψ p := ψ_mul_e _ _
  rw [← map_mul, mul_assoc, ← mul_assoc (e (sadj n p • v)), ← he,
    mul_assoc, e_mul_self, ← mul_assoc, sq]

/-- When the return exponent at the right pivot is zero, a single right
crossing and the same crossing preceded by the adjacent crossing cannot jointly
reflect marks at a surviving upper cut. The target algebra may in particular
be the globally violated quotient with its prescribed higher ideal. -/
theorem exists_unmarked_twoColumnRelation_of_zeroExponent
    (v : Seq μ) (p : ℕ) (hp : p+2 < n) (b : Fin ℓ) (i : I)
    (hb : v.lbl ⟨p,by omega⟩ = .inr b)
    (hi : v.lbl ⟨p+1,by omega⟩ = .inl i) (hex : Λ b i = 0)
    (J : TwoSidedIdeal A) :
    let u := sadj n p • v
    let e₀ := π (e u)
    let d := π (ψ p * e v)
    let τ := π (ψ (p+1) * e v)
    e₀ ∉ J → ∃ (x y : A), e₀*x*e₀=x ∧ e₀*y*e₀=y ∧ y ∉ J ∧
      x*d+y*(d*τ)=0 := by
  intro u e₀ d τ hJ
  let g := π (ψ p * e u)
  have hgd : g*d = π (e v) := zeroExponent_rightLeg Q Λ π v p (by omega) b i hb hi hex
  have hd : e₀*d=d := by
    simp only [e₀,d,← map_mul]
    rw [ψ_mul_e, ← mul_assoc, e_mul_self]
  have hg : g*e₀=g := by
    simp only [e₀,g,← map_mul,mul_assoc,e_mul_self]
  have hτ : τ*π (e v)=τ := by
    simp only [τ,← map_mul,mul_assoc,e_mul_self]
  have idem : e₀*e₀=e₀ := by simp only [e₀,← map_mul,e_mul_self]
  refine ⟨d*τ*g,-e₀,?_,?_,?_,?_⟩
  · simp only [← mul_assoc, hd]
    simp only [mul_assoc, hg]
  · simp only [mul_neg,neg_mul,idem]
  · intro h
    exact hJ (by simpa only [neg_neg] using J.neg_mem h)
  · rw [mul_assoc (d*τ) g, hgd, mul_assoc d τ, hτ, neg_mul, ← mul_assoc e₀, hd, add_neg_cancel]

/-- At a zero-exponent right pivot, two jointly marked columns can be replaced
at that pivot by a single marked coefficient with the same product. -/
theorem exists_marked_twoColumnPivotReplacement_of_zeroExponent
    (v : Seq μ) (p : ℕ) (hp : p+2 < n) (b : Fin ℓ) (i : I)
    (hb : v.lbl ⟨p,by omega⟩ = .inr b)
    (hi : v.lbl ⟨p+1,by omega⟩ = .inl i) (hex : Λ b i = 0)
    (J : TwoSidedIdeal A) (x y : A) :
    let u := sadj n p • v
    let e₀ := π (e u)
    let d := π (ψ p * e v)
    let τ := π (ψ (p+1) * e v)
    e₀*x=x → e₀*y=y → x*d+y*(d*τ) ∈ J →
      ∃ z ∈ J, e₀*z*e₀=z ∧ z*d=x*d+y*(d*τ) := by
  intro u e₀ d τ hx hy hm
  let z := x*d + y*(d*τ)
  let g := π (ψ p * e u)
  have hgd : g*d = π (e v) := zeroExponent_rightLeg Q Λ π v p (by omega) b i hb hi hex
  have hd : d*π (e v)=d := by simp only [d,← map_mul,mul_assoc,e_mul_self]
  have hτ : τ*π (e v)=τ := by simp only [τ,← map_mul,mul_assoc,e_mul_self]
  have hg : g*e₀=g := by simp only [e₀,g,← map_mul,mul_assoc,e_mul_self]
  have hleft : e₀*z=z := by simp only [z,mul_add,← mul_assoc,hx,hy]
  have hright : z*π (e v)=z := by simp only [z,add_mul,mul_assoc,hd,hτ]
  refine ⟨z*g, J.mul_mem_right z g hm, ?_, ?_⟩
  · rw [mul_assoc e₀ (z*g) e₀, mul_assoc z g e₀, hg, ← mul_assoc e₀ z, hleft]
  · rw [mul_assoc, hgd, hright]

end Categorification.Stendhal.BraidedStendhalAlgebra
