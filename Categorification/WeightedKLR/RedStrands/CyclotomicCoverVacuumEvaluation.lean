/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Vacuum
import Categorification.KLR.CyclotomicAction.PresCL
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverOrderAction
import Categorification.WeightedKLR.RedStrands.DoubleDiagram
import Categorification.KLR.Rouquier.PolynomialDegree

/-! # Detection of tensor algebra elements on the projected cyclotomic vacuum

The cyclotomic KLR action on the empty block recovers diagrams through the
horizontal and vertical reflections of the word. Extension of scalars to
the tensor-product algebra projects these coordinates to the corresponding
ordinary Stendhal elements. This proves the vacuum detection calculation
used in Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, pp. 42–43,
for the extended-Cartan cover. Identification of a signed diagram
presentation with these operators requires a separate comparison of its relations.
The cited injectivity argument is the one revised in version 3; arXiv:1309.3796v2,
§4.5, Lemma 4.28, argues via Lemma 4.26 instead.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory TwoRep KLR KLRAlgebra CyclotomicAction InductionAlong QuantumGroup QuantumGroup.UDot

universe u v w

section Scalars

variable {A B : Type u} [Ring A] [Ring B] (φ : A →+* B)

/-- After extension of scalars, a coordinate into the regular module takes
the value `b φ(g m)` on a pure tensor. -/
def extendedCoordinate {N : Type*} [AddCommGroup N] [Module A N] (g : N →ₗ[A] A) :
    Ind N φ.toNonUnitalRingHom →ₗ[B] B :=
  Ind.lift (fun b n => b.val * φ (g n))
    (fun b c n => add_mul b.val c.val _)
    (fun b n n' => by rw [map_add, map_add, mul_add])
    (fun b a n => by change (b.val * φ a) * φ (g n) = b.val * φ (g (a • n))
                     rw [map_smul, smul_eq_mul, map_mul, mul_assoc])
    (fun b c n => mul_assoc b c.val _)

/-- A zero map after scalar extension has all its regular coordinates in
the kernel of the coefficient homomorphism. -/
theorem coordinate_eq_zero_of_extension {M N : ModuleCat.{max u w} A} (f : M ⟶ N)
    (hf : (functor φ.toNonUnitalRingHom).map f = 0) (g : N →ₗ[A] A) (x : M) :
    φ (g (f.hom x)) = 0 := by
  have hx := congrArg (fun h : (functor φ.toNonUnitalRingHom).obj M ⟶
    (functor φ.toNonUnitalRingHom).obj N =>
      extendedCoordinate φ g (h.hom (Ind.tmul (unitGen φ.toNonUnitalRingHom) x))) hf
  change φ 1 * φ (g (f.hom x)) = extendedCoordinate φ g 0 at hx
  simpa using hx

end Scalars

variable {I : Type u} [DecidableEq I] {k : Type v} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
  (C : CartanDatum I) (hQ : IsRouquierQ C Q)

local notation "D" => I ⊕ Fin ℓ
local notation "S" => cyclotomicCoverQ C Λ Q
local notation "μ" => stendhalWeight ℓ ν
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "π" => cyclotomicCoverToTensor (Q := Q) Λ ν C

/-- A realization of the extended Cartan matrix by its coroot coordinates. -/
def cyclotomicCoverWeightDatum : WeightDatum (extendedCartanDatum C Λ) (D → ℤ) ((D → ℤ) →+ ℤ) where
  pair := AddMonoidHom.id _
  iX j i := A (extendedCartanDatum C Λ) i j
  iY i := { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl }
  pair_iY_iX _ _ := rfl

/-- The cover vacuum has coroot coordinate one at each red label and zero
at every black label. -/
def cyclotomicCoverHighest : D → ℤ := Sum.elim (fun _ => 0) (fun _ => 1)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ

omit [DecidableEq I] in
/-- The cyclotomic polynomials of the cover are monic. -/
theorem cyclotomicCoverPolynomial_monic (j : D) : (p j).Monic := by
  cases j <;> simp [cyclotomicCoverPolynomial]

omit [DecidableEq I] in
/-- The cyclotomic polynomial of a label has degree its coroot coordinate of the vacuum. -/
theorem cyclotomicCoverPolynomial_natDegree (j : D) : ((p j).natDegree : ℤ) = WeightDatum.pair Wgt (WeightDatum.iY Wgt j) L := by
  cases j <;> simp [cyclotomicCoverPolynomial, cyclotomicCoverWeightDatum, cyclotomicCoverHighest]

local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "monic" => cyclotomicCoverPolynomial_monic (k := k)
local notation "topDeg" => cyclotomicCoverPolynomial_natDegree (k := k) Λ C
local notation "wt₀" => blockWeight Wgt L 0
set_option quotPrecheck false in
set_option hygiene false in
local notation "V" => regularObj.{u,v,w} (Q := S) (a := p) (RD := Wgt) (Λ := L)
set_option quotPrecheck false in
set_option hygiene false in
local notation "qAct" => cyclotomicFamily_upKLR.{u,v,w} sym lead monic Wgt L topDeg deg

/-- The genuine CL action of the extended Cartan datum with the red/black
cyclotomic exponents of the tensor-product cover. -/
abbrev cyclotomicCoverCLAction :=
  cyclotomicPresCL.{u,v,w} sym lead monic Wgt L topDeg deg (IsRouquierQ.homogeneous hS)

/-- An entry of the actual cyclotomic KLR action on the vacuum, followed by
extension of scalars to the ordinary tensor-product algebra. -/
def projectedCoverVacuumEntry (r : KLRAlgebra k S μ) (t s : Seq μ) :=
  (functor (RingHom.toNonUnitalRingHom (AlgHom.toRingHom π))).map
    (((RouqFamily.klrAct qAct wt₀ r) t s).hom.app (familyObj sym lead monic topDeg deg V)
      (topBlk (RD := Wgt) (Λ := L) (ν := μ) rfl))

/-- The projected cover action detects the reflected ordinary tensor-algebra
class: if every projected entry vanishes, that class vanishes. -/
theorem projectedCoverVacuum_detects (r : KLRAlgebra k S μ)
    (hr : ∀ t s : Seq μ, projectedCoverVacuumEntry.{u,v,w} Λ ν C hQ r t s = 0) :
    π (CycKLR.mk k S p μ (hflip (sigma sym r))) = 0 := by
  let g := (ULift.moduleEquiv : ULift.{w} (CycKLR k S p 0) ≃ₗ[CycKLR k S p 0] _).toLinearMap
  have hs (t s : Seq μ) : π (CycKLR.mk k S p μ (hflip (sigma sym (e s * r * e t)))) = 0 := by
    have hc := wcoord_klrAct_wgen sym lead monic topDeg deg V rfl (ULift.up 1) (Ψ₀ := g) rfl r t s
    rw [← hc]
    exact coordinate_eq_zero_of_extension (AlgHom.toRingHom π) _ (hr t s) _ _
  have he : r = ∑ s : Seq μ, ∑ t : Seq μ, e s * r * e t := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sum_e, one_mul, mul_one]
  rw [he, map_sum, hflip_sum, map_sum, map_sum]
  exact Finset.sum_eq_zero fun s _ => by
    rw [map_sum, hflip_sum, map_sum, map_sum]
    exact Finset.sum_eq_zero fun t _ => hs t s

/-- Every nonzero element of the ordinary tensor-product algebra is
detected by a projected matrix entry of the genuine cover action. -/
theorem exists_projectedCoverVacuumEntry_ne_zero
    (x : TensorProductAlgebra k Q Λ ν) (hx : x ≠ 0) :
    ∃ (r : KLRAlgebra k S μ) (t s : Seq μ),
      π (CycKLR.mk k S p μ (hflip (sigma sym r))) = x ∧
      projectedCoverVacuumEntry.{u,v,w} Λ ν C hQ r t s ≠ 0 := by
  classical
  obtain ⟨z, rfl⟩ := cyclotomicCoverToTensor_surjective (Q := Q) Λ ν C x
  obtain ⟨z, rfl⟩ := CycKLR.mk_surjective z
  let r := sigma sym (hflip z)
  have he : hflip (sigma sym r) = z := by simp [r]
  have h : ∃ t s, projectedCoverVacuumEntry.{u,v,w} Λ ν C hQ r t s ≠ 0 := by
    by_contra! h
    exact hx (he ▸ projectedCoverVacuum_detects Λ ν C hQ r h)
  obtain ⟨t,s,H⟩ := h
  exact ⟨r,t,s,by rw [he],H⟩

section Weights

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (B : WeightDatum C X Y) (weights : Fin ℓ → X)
  (hweights : ∀ r i, B.pair (B.iY i) (weights r) = (Λ r i : ℤ))

include hweights in
omit [DecidableEq I] in
/-- The black coordinate of a cover block is the negative physical region
weight of the same signed prefix, with zero left boundary weight. -/
theorem signedCoverWord_blockWeight {β : Multiset D} {xs : List (DoubleStrand I ℓ)}
    (t : SignedCoverWord I ℓ β xs) (i : I) :
    blockWeight Wgt L β (.inl i) =
      -B.pair (B.iY i) (DoubleDiagram.endWeight B weights 0 xs) := by
  have hs (q : X) (d : DoubleStrand I ℓ) :
      DoubleDiagram.endWeight B weights q [d] = q + DoubleStrand.weight B weights d := by
    simp [DoubleDiagram.endWeight]
  have hroot (j : I) : B.pair (B.iY i) (B.iX j) = A C i j := B.pair_iY_iX i j
  induction t with
  | nil => simp [blockWeight, cyclotomicCoverHighest, DoubleDiagram.endWeight]
  | @ind β xs t j ih =>
    rw [blockWeight_cons, Pi.add_apply, DoubleDiagram.endWeight_append, hs, map_add, ih]
    cases j with
    | inl j =>
      change _ + A C i j = -(_ + B.pair (B.iY i) ((-1 : ℤ) • B.iX j))
      rw [neg_one_zsmul, map_neg, hroot]
      omega
    | inr r =>
      change _ + A (extendedCartanDatum C Λ) (.inl i) (.inr r) = -(_ + B.pair (B.iY i) (weights r))
      rw [cover_black_red, hweights]
      omega
  | @res β xs j t ih =>
    rw [blockWeight_cons, Pi.add_apply] at ih
    change blockWeight Wgt L β (.inl i) + A C i j = _ at ih
    rw [DoubleDiagram.endWeight_append, hs, map_add]
    change _ = -(_ + B.pair (B.iY i) ((1 : ℤ) • B.iX j))
    rw [one_zsmul, hroot]
    omega

end Weights

end Categorification.Stendhal
