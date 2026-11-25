/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopCancellation
import Categorification.KLR.PolyRep.Sound

/-!
# Polynomial tests for the nearby left crossing

The source bottom corner factors through the left-extreme diagonal. An
oriented positional-polynomial action makes the two crossings to be tested
plain variable permutations. Equivariance of polynomial substitution under
a transposition passes the divided-difference action to black coordinates.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA Equiv

section Right
variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ
local notation "A" => BraidedStendhalAlgebra k Q Λ ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => ofKLR k Q Λ ν
local notation "π" => violMk k Q Λ ν
local notation "E" => fun v : Seq μ => F (e v)
local notation "P" => fun v : Seq μ => π (F (e v))

theorem exists_viol_rightFactor_of_descent (hQ : KLRSymm Q) (s t : Seq μ)
    (j : ℕ) (hj : j+1<n)
    (desc : ∀ w : Perm (Fin n), w • s=t → w ⟨j+1,hj⟩ < w ⟨j,by omega⟩)
    (x : V) (hx : P t*x*P s=x) :
    ∃ y : V, P t*y*P (sadj n j • s)=y ∧ y*π (F (ψ j*e s))=x := by
  obtain ⟨d,hd⟩ := violMk_surjective (Q := Q) (Λ := Λ) x
  let z : A := E t*d*E s
  have hz : E t*z*E s=z := by
    have idem (v : Seq μ) : E v * E v = E v := by rw [← map_mul, e_mul_self]
    change E t*(E t*d*E s)*E s=E t*d*E s
    calc
      _ = (E t*E t)*d*(E s*E s) := by simp only [mul_assoc]
      _ = _ := by rw [idem,idem]
  have hπ : π z=x := by
    change π (E t*d*E s)=x
    rw [map_mul,map_mul,hd]
    exact hx
  obtain ⟨y,hy,h⟩ := exists_supported_descent_factor Q Λ hQ s t j hj desc z hz
  exact ⟨π y, by simpa only [map_mul] using congrArg π hy,
    by simpa only [map_mul,hπ] using congrArg π h⟩

end Right

section Five
variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ₀
local notation "bottom" => fixedTopFourExitBottom
local notation "left" => fixedTopFourExitCut 0
local notation "mid₁" => sadj n₀ 1 • bottom
local notation "mid₂" => sadj n₀ 2 • mid₁
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "φ" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "p" => fun v : Seq μ₀ => φ (e v)

private theorem cut_leg (j : ℕ) (v : Seq μ₀) :
    e (sadj n₀ j • v) * (ψ j*e v : KLRAlgebra k (stendhalQ Q Λ) μ₀) = ψ j*e v := by
  rw [ψ_mul_e (Q := stendhalQ Q Λ) j v, ← mul_assoc, e_mul_self]

theorem fiveSlot_leftExtreme_source_factor (hQ : KLRSymm Q) (y : V)
    (hy : p left*y*p bottom=y) :
    ∃ z : V, p left*z*p left=z ∧ z*φ (ψw [3,2,1]*e bottom)=y := by
  have desc₁ : ∀ w : Perm (Fin n₀), w • bottom=left →
      w ⟨2,by decide⟩ < w ⟨1,by decide⟩ := by decide +kernel
  have desc₂ : ∀ w : Perm (Fin n₀), w • mid₁=left →
      w ⟨3,by decide⟩ < w ⟨2,by decide⟩ := by decide +kernel
  have desc₃ : ∀ w : Perm (Fin n₀), w • mid₂=left →
      w ⟨4,by decide⟩ < w ⟨3,by decide⟩ := by decide +kernel
  obtain ⟨a,ha,ea⟩ :=
    exists_viol_rightFactor_of_descent Q Λ hQ bottom left 1 (by decide) desc₁ y hy
  obtain ⟨b,hb,eb⟩ :=
    exists_viol_rightFactor_of_descent Q Λ hQ mid₁ left 2 (by decide) desc₂ a ha
  obtain ⟨z,hz,ez⟩ :=
    exists_viol_rightFactor_of_descent Q Λ hQ mid₂ left 3 (by decide) desc₃ b hb
  have hlast : sadj n₀ 3 • mid₂=left := by decide
  refine ⟨z,hlast ▸ hz,?_⟩
  have combine : (ψ 3*e mid₂ : KLRAlgebra k (stendhalQ Q Λ) μ₀) *
      (ψ 2*e mid₁) * (ψ 1*e bottom) = ψw [3,2,1]*e bottom := by
    simp only [mul_assoc,cut_leg,ψw_cons,ψw_nil,mul_one]
  calc
    _ = z*φ ((ψ 3*e mid₂)*(ψ 2*e mid₁)*(ψ 1*e bottom)) := congrArg (fun u => z*φ u) combine.symm
    _ = z*φ (ψ 3*e mid₂)*φ (ψ 2*e mid₁)*φ (ψ 1*e bottom) := by
      rw [map_mul,map_mul,← mul_assoc,← mul_assoc]
    _ = b*φ (ψ 2*e mid₁)*φ (ψ 1*e bottom) :=
      congrArg (fun u => u*φ (ψ 2*e mid₁)*φ (ψ 1*e bottom)) ez
    _ = a*φ (ψ 1*e bottom) := congrArg (fun u => u*φ (ψ 1*e bottom)) eb
    _ = y := ea

/-- A representation detecting the left-extreme diagonal and the completed
path from the two-interior bottom to the nearby top gives cancellation. -/
theorem fiveSlot_jA_leftCancellation_of_representation {R : Type*} [Ring R] [Algebra k R]
    (hQ : KLRSymm Q) (repr : V →ₐ[k] R)
    (faithful : ∀ z : V, p left*z*p left=z → repr z=0 → z=0)
    (detect : ∀ z : V, p left*z*p left=z →
      repr (φ (ψ 2*e left))*repr z*repr (φ (ψw [3,2,1]*e bottom))=0 → repr z=0)
    (y : V) (ly : p left*y=y) (ry : y*p bottom=y)
    (hy : φ (ψ 2*e left)*y=0) : y=0 := by
  obtain ⟨z,hz,hzy⟩ := fiveSlot_leftExtreme_source_factor Q Λ hQ y (by rw [ly,ry])
  have res : repr (φ (ψ 2*e left))*repr z*repr (φ (ψw [3,2,1]*e bottom))=0 := by
    have h := congrArg repr hy
    rw [← hzy] at h
    simpa only [map_mul, map_zero, mul_assoc] using h
  rw [← hzy,faithful z hz (detect z hz res),zero_mul]

end Five
end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra MvPolynomial

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

/-- The identity factors orient the nearby crossing and the entire left-extreme
exit as permutations of the positional variables. -/
def leftTopPolynomialFactors : Unit ⊕ Fin 3 → Unit ⊕ Fin 3 → MvPolynomial (Fin 2) k
  | .inl _, .inl _ => 0
  | .inl _, .inr r => if r=1 then 1 else X 1 ^ Λ r ()
  | .inr r, .inl _ => if r=1 then X 0 ^ Λ r () else 1
  | .inr r, .inr s => if r=2 ∧ s=1 then 1 else 0

theorem leftTopPolynomialFactors_factor (a b : Unit ⊕ Fin 3) (h : a ≠ b) :
    stendhalQ Q Λ a b =
      leftTopPolynomialFactors Λ b a * rename ![1,0] (leftTopPolynomialFactors Λ a b) := by
  cases a with
  | inl i =>
    cases i
    cases b with
    | inl j => cases j; exact (h rfl).elim
    | inr r =>
      fin_cases r <;> simp [leftTopPolynomialFactors]
  | inr r =>
    cases b with
    | inl j =>
      cases j
      fin_cases r <;> simp [leftTopPolynomialFactors]
    | inr s =>
      fin_cases r <;> fin_cases s <;> first | exact (h rfl).elim | simp [stendhalQ, leftTopPolynomialFactors]

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀

/-- The affine positional-polynomial action used to attempt the
spectator-cyclotomic descent. -/
def leftTopPolynomialRep :
    KLRAlgebra k (stendhalQ Q Λ) μ₀ →ₐ[k] Module.End k (PolyRep.Pol k μ₀) :=
  PolyRep.polyRep (leftTopPolynomialFactors_factor Q Λ)

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace MvPolynomial

open Equiv Categorification

/-- A substitution transporting an adjacent transposition commutes with
divided differences if the exchanged variables remain distinct. -/
theorem map_ddiff_of_swap_equivariant {k σ τ : Type*} [CommRing k]
    [DecidableEq σ] [DecidableEq τ] {a b : σ} {p q : τ}
    (hab : a ≠ b) (hpq : p ≠ q)
    (ev : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)
    (ha : ev (X a) = X p) (hb : ev (X b) = X q)
    (equiv : ∀ g : MvPolynomial σ k, ev (rename (swap a b) g) = rename (swap p q) (ev g))
    (g : MvPolynomial σ k) :
    ev (ddiff a b g) = ddiff p q (ev g) := by
  symm
  apply ddiff_eq_of_mul hpq
  have h := congrArg ev (ddiff_spec hab g)
  simpa only [map_mul,map_sub,ha,hb,equiv] using h

end MvPolynomial

namespace Categorification.Stendhal.BraidedStendhalAlgebra

/-- The rank-two nilHecke idempotent used as the polynomial generator is
full, over any ground ring and after any quotient. -/
theorem rankTwo_nilHecke_test {R : Type*} [Ring R] (x y d : R)
    (square : d*d=0) (left : x*d-d*y=1) (right : d*x-y*d=1) :
    IsIdempotentElem (d*x) ∧ d*(d*x)=0 ∧
      ∀ z : R, (∀ u : R, z*(u*(d*x))=0) → z=0 := by
  have dxD : d*x*d=d := by
    calc
      d*x*d = d*(x*d) := mul_assoc ..
      _ = d*(1+d*y) := congrArg (d*·) (sub_eq_iff_eq_add.mp left)
      _ = _ := by rw [mul_add,mul_one,← mul_assoc d d y,square,zero_mul,add_zero]
  refine ⟨?_,by rw [← mul_assoc,square,zero_mul],?_⟩
  · change d*x*(d*x)=d*x
    rw [← mul_assoc,dxD]
  · intro z vanishes
    have e : z*(d*x)=0 := by simpa only [one_mul] using vanishes 1
    have yy : z*(y*d)=0 := by
      calc
        _ = z*(y*(d*x)*d) := by rw [mul_assoc y, dxD]
        _ = z*(y*(d*x))*d := (mul_assoc ..).symm
        _ = _ := by rw [vanishes,zero_mul]
    calc
      z = z*1 := (mul_one z).symm
      _ = z*(d*x-y*d) := congrArg (z*·) right.symm
      _ = 0 := by rw [mul_sub,e,yy,sub_zero]

end Categorification.Stendhal.BraidedStendhalAlgebra
