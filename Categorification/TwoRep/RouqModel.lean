/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqCyclicCross
import Categorification.Diagrams.BicatInterp
import Categorification.Diagrams.KL3.Basic
import Categorification.Diagrams.CL.Scalars

/-!
# Ungraded Rouquier families and their generator images

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1,
Definition 1.1 and Theorem 4.3. A `RouqFamily` consists of weight-indexed right adjunctions,
dots, upward crossings, and the single-colour Rouquier relations. The left adjunctions are
constructed from `RouqLoc.leftAdjunction`, not supplied as additional data.

This is the generator layer of the ungraded interpretation. Mixed KLR relations and
invertibility of mixed sideways crossings are not fields of this structure; respecting the
presentation is a separate assertion. In particular this file does not claim Brundan's main
theorem. No zero objects, grading, finite-dimensional Hom spaces or scalar endomorphism rings
are required. All region transports are explicit equalities.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp

universe w v u u₁

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y)

/-- Weight-indexed Rouquier generators with all single-colour relations. Mixed KLR relations
and mixed invertibility are deliberately not included in this generator-layer structure. -/
structure RouqFamily where
  obj : X → B
  E : ∀ (i : I) {x y : X}, x + RD.iX i = y → (obj x ⟶ obj y)
  F : ∀ (i : I) {x y : X}, x + RD.iX i = y → (obj y ⟶ obj x)
  adj : ∀ (i : I) {x y : X} (h : x + RD.iX i = y), E i h ⊣ F i h
  dot : ∀ (i : I) {x y : X} (h : x + RD.iX i = y), E i h ⟶ E i h
  cross : ∀ (i j : I) {a b c d : X} (h₁ : a + RD.iX j = b)
    (h₂ : b + RD.iX i = d) (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d),
    E j h₁ ≫ E i h₂ ⟶ E i h₃ ≫ E j h₄
  square : ∀ (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c),
    cross i i h₁ h₂ h₁ h₂ ≫ cross i i h₁ h₂ h₁ h₂ = 0
  braid : ∀ (i : I) {a b c d : X} (h₁ : a + RD.iX i = b)
    (h₂ : b + RD.iX i = c) (h₃ : c + RD.iX i = d),
    E i h₁ ◁ cross i i h₂ h₃ h₂ h₃ ≫
      ((α_ (E i h₁) (E i h₂) (E i h₃)).inv ≫ cross i i h₁ h₂ h₁ h₂ ▷ E i h₃ ≫
        (α_ (E i h₁) (E i h₂) (E i h₃)).hom) ≫ E i h₁ ◁ cross i i h₂ h₃ h₂ h₃ =
    ((α_ (E i h₁) (E i h₂) (E i h₃)).inv ≫ cross i i h₁ h₂ h₁ h₂ ▷ E i h₃ ≫
      (α_ (E i h₁) (E i h₂) (E i h₃)).hom) ≫ E i h₁ ◁ cross i i h₂ h₃ h₂ h₃ ≫
    ((α_ (E i h₁) (E i h₂) (E i h₃)).inv ≫ cross i i h₁ h₂ h₁ h₂ ▷ E i h₃ ≫
      (α_ (E i h₁) (E i h₂) (E i h₃)).hom)
  loc : ∀ (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c),
    RouqLoc (adj i h₁) (adj i h₂) (dot i h₁) (dot i h₂)
      (cross i i h₁ h₂ h₁ h₂) (RD.pair (RD.iY i) b)

namespace RouqFamily

variable {RD} (S : RouqFamily (B := B) RD)

/-- The Cartan pairing changes by two along a single-colour edge. -/
theorem pair_step (i : I) {x y : X} (h : x + RD.iX i = y) :
    RD.pair (RD.iY i) y = RD.pair (RD.iY i) x + 2 := by
  rw [← h, map_add, RD.pair_iY_iX_self]

variable [AdditiveWhiskering B]

/-- The left adjunction constructed from the two neighbouring local Rouquier inverses. -/
def adjL (i : I) {x y : X} (h : x + RD.iX i = y) : S.F i h ⊣ S.E i h :=
  (S.loc i (sub_add_cancel x (RD.iX i)) h).leftAdjunction
    (S.loc i h (rfl : y + RD.iX i = y + RD.iX i))
    (pair_step i h) (S.square i _ h) (S.square i h rfl) (S.braid i _ h rfl)

/-- With arbitrary neighbours, the constructed adjunction is the local one. -/
theorem adjL_eq (i : I) {a b c d : X} (h₁ : a + RD.iX i = b)
    (h₂ : b + RD.iX i = c) (h₃ : c + RD.iX i = d) :
    S.adjL i h₂ = (S.loc i h₁ h₂).leftAdjunction (S.loc i h₂ h₃)
      (pair_step i h₂) (S.square i h₁ h₂) (S.square i h₂ h₃) (S.braid i h₁ h₂ h₃) := by
  obtain rfl : a = b - RD.iX i := (eq_sub_iff_add_eq).2 h₁
  subst d
  rfl

/-- The downward dot defined by the prescribed left adjunction. -/
def dotDn (i : I) {x y : X} (h : x + RD.iX i = y) : S.F i h ⟶ S.F i h :=
  (conjugateEquiv (S.adjL i h) (S.adjL i h)).symm (S.dot i h)

/-- Brundan's dot cyclicity, now at arbitrary weights of the root datum. -/
theorem dotDn_eq_rightMate (i : I) {x y : X} (h : x + RD.iX i = y) :
    S.dotDn i h = conjugateEquiv (S.adj i h) (S.adj i h) (S.dot i h) := by
  apply (conjugateEquiv (S.adjL i h) (S.adjL i h)).injective
  rw [dotDn, Equiv.apply_symm_apply]
  exact ((S.loc i (sub_add_cancel x (RD.iX i)) h).cyclic_dot
    (S.loc i h rfl) (pair_step i h) (S.square i _ h)
    (S.square i h rfl) (S.braid i _ h rfl)).symm

/-- Same-colour crossing cyclicity for arbitrary neighbouring weights. -/
theorem cyclic_cross (i : I) {a b c : X} (h₁ : a + RD.iX i = b)
    (h₂ : b + RD.iX i = c) :
    conjugateEquiv ((S.adjL i h₂).comp (S.adjL i h₁))
      ((S.adjL i h₂).comp (S.adjL i h₁))
      (conjugateEquiv ((S.adj i h₁).comp (S.adj i h₂))
        ((S.adj i h₁).comp (S.adj i h₂)) (S.cross i i h₁ h₂ h₁ h₂)) =
      S.cross i i h₁ h₂ h₁ h₂ := by
  rw [S.adjL_eq i (sub_add_cancel a (RD.iX i)) h₁ h₂,
    S.adjL_eq i h₁ h₂ (rfl : c + RD.iX i = c + RD.iX i)]
  exact (S.loc i (sub_add_cancel a (RD.iX i)) h₁).cyclic_cross
    (S.loc i h₁ h₂) (S.loc i h₂ rfl) (pair_step i h₁) (pair_step i h₂)
    (S.square i _ h₁) (S.square i h₁ h₂) (S.square i h₂ rfl)
    (S.braid i _ h₁ h₂) (S.braid i h₁ h₂ rfl)

/-- Adjacent weights on a root string, with the transport kept explicit. -/
theorem string_step (i : I) (b : X) (r : ℤ) :
    b + r • RD.iX i + RD.iX i = b + (r + 1) • RD.iX i := by
  rw [add_smul, one_smul, add_assoc]

/-- Restriction to a root string is the existing ungraded `RouqSl2`, not a new local theory. -/
def toRouqSl2 (i : I) (b : X) : RouqSl2 B where
  n₀ := RD.pair (RD.iY i) b
  obj r := S.obj (b + r • RD.iX i)
  E r := S.E i (string_step i b r)
  F r := S.F i (string_step i b r)
  adj r := S.adj i (string_step i b r)
  x r := S.dot i (string_step i b r)
  τ r := S.cross i i (string_step i b r) (string_step i b (r + 1))
    (string_step i b r) (string_step i b (r + 1))
  τ_sq r := S.square i (string_step i b r) (string_step i b (r + 1))
  braid r := S.braid i (string_step i b r) (string_step i b (r + 1))
    (string_step i b (r + 1 + 1))
  loc r := by
    have hw : RD.pair (RD.iY i) (b + (r + 1) • RD.iX i) =
        RD.pair (RD.iY i) b + 2 * (r + 1) := by
      rw [map_add, map_zsmul, RD.pair_iY_iX_self, smul_eq_mul, mul_comm]
    exact hw ▸ S.loc i (string_step i b r) (string_step i b (r + 1))

/-- The upward region displacement. -/
theorem sh_up (i : I) : sh RD ((true, i) : Letter I) = RD.iX i := by simp [sh]

/-- The downward region displacement. -/
theorem sh_dn (i : I) : sh RD ((false, i) : Letter I) = -RD.iX i := by simp [sh]

theorem up_reg (i : I) {r x y : X} (hx : r = x)
    (hy : sh RD ((true, i) : Letter I) + r = y) : x + RD.iX i = y := by
  subst hx hy; rw [sh_up, add_comm]

theorem dn_reg (i : I) {r x y : X} (hx : r = x)
    (hy : sh RD ((false, i) : Letter I) + r = y) : y + RD.iX i = x := by
  subst hx hy; rw [sh_dn, neg_add_cancel_comm]

/-- The actual ungraded image of a strand with explicitly given endpoints. -/
def strandImg : (c : Col I X) → (x y : X) → c.r = x → sh RD c.l + c.r = y →
    (S.obj x ⟶ S.obj y)
  | ⟨(true, i), _⟩, _, _, hx, hy => S.E i (up_reg i hx hy)
  | ⟨(false, i), _⟩, _, _, hx, hy => S.F i (dn_reg i hx hy)

/-- The KL signature model in the original bicategory, without adjoining zero objects. -/
def model : Model (psig RD) B where
  obj := S.obj
  strandAt := S.strandImg

variable {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  (Sc : CL.CLScalars C k)

/-- The downward mixed crossing in the CL normalization. -/
def crossDn (i j : I) {a n n' b : X} (hj : n' + RD.iX j = b)
    (hi : a + RD.iX i = n') (hi' : n + RD.iX i = b) (hj' : a + RD.iX j = n) :
    S.F j hj ≫ S.F i hi ⟶ S.F i hi' ≫ S.F j hj' :=
  (((Sc.t j i)⁻¹ : kˣ) : k) •
    (conjugateEquiv ((S.adjL i hi').comp (S.adjL j hj'))
      ((S.adjL j hj).comp (S.adjL i hi))).symm (S.cross i j hj' hi' hi hj)

/-- For a single colour the downward generator is exactly the right mate of the upward one. -/
theorem crossDn_self (i : I) {a b c : X} (h₁ : a + RD.iX i = b)
    (h₂ : b + RD.iX i = c) :
    S.crossDn Sc i i h₂ h₁ h₂ h₁ =
      conjugateEquiv ((S.adj i h₁).comp (S.adj i h₂))
        ((S.adj i h₁).comp (S.adj i h₂)) (S.cross i i h₁ h₂ h₁ h₂) := by
  rw [crossDn, Sc.t_self, inv_one, Units.val_one, one_smul]
  apply (conjugateEquiv ((S.adjL i h₂).comp (S.adjL i h₁))
    ((S.adjL i h₂).comp (S.adjL i h₁))).injective
  rw [Equiv.apply_symm_apply, S.cyclic_cross]

theorem cross_up_reg (j : I) (ν : X) : ν + RD.iX j = sh RD ((true, j) : Letter I) + ν := by
  rw [sh_up, add_comm]

theorem cross_up_reg' (i j : I) {ν a : X}
    (ha : sh RD ((true, i) : Letter I) + (sh RD ((true, j) : Letter I) + ν) = a) :
    sh RD ((true, j) : Letter I) + ν + RD.iX i = a := by
  rw [← ha, sh_up, sh_up]; abel

theorem cross_dn_reg (j : I) (ν : X) : sh RD ((false, j) : Letter I) + ν + RD.iX j = ν := by
  rw [sh_dn]; abel

theorem cross_dn_reg' (i j : I) {ν a : X}
    (ha : sh RD ((false, i) : Letter I) + (sh RD ((false, j) : Letter I) + ν) = a) :
    a + RD.iX i = sh RD ((false, j) : Letter I) + ν := by
  rw [← ha, sh_dn]; abel

theorem cross_up_swap (i j : I) {ν a : X}
    (ha : sh RD ((true, i) : Letter I) + (sh RD ((true, j) : Letter I) + ν) = a) :
    sh RD ((true, i) : Letter I) + ν + RD.iX j = a := by
  rw [← ha, sh_up, sh_up]; abel

theorem cross_dn_swap (i j : I) {ν a : X}
    (ha : sh RD ((false, i) : Letter I) + (sh RD ((false, j) : Letter I) + ν) = a) :
    a + RD.iX j = sh RD ((false, i) : Letter I) + ν := by
  rw [← ha, sh_dn, sh_dn]; abel

/-- **The images of the generators** of `U` in the model of an ungraded Rouquier family, read
between regions `a` (left) and `b` (right). -/
def genImg : GenImg S.model where
  gen g := match g with
    | .gen (.dot ⟨(true, i), r⟩) => fun a b _ _ hd hde _ _ =>
        S.dot i (up_reg i hde hd.1)
    | .gen (.dot ⟨(false, i), r⟩) => fun a b _ _ hd hde _ _ =>
        S.dotDn i (dn_reg i hde hd.1)
    | .gen (.cross true i j ν) => fun a b _ _ hd hde _ _ => by
        obtain rfl : ν = b := hde
        exact S.cross i j (cross_up_reg j ν) (cross_up_reg' i j hd.1) (cross_up_reg i ν)
          (cross_up_swap i j hd.1)
    | .gen (.cross false i j ν) => fun a b _ _ hd hde _ _ => by
        obtain rfl : ν = b := hde
        exact S.crossDn Sc i j (cross_dn_reg j ν) (cross_dn_reg' i j hd.1)
          (cross_dn_reg i ν) (cross_dn_swap i j hd.1)
    | .cup ⟨(true, i), r⟩ => fun a b ha _ _ hde _ _ => by
        subst hde
        exact (S.adjL i (up_reg i rfl ha)).unit
    | .cup ⟨(false, i), r⟩ => fun a b ha _ _ hde _ _ => by
        subst hde
        exact (S.adj i (dn_reg i rfl ha)).unit
    | .cap ⟨(true, i), r⟩ => fun a b _ _ _ hde _ hce => by
        subst hce
        exact (S.adjL i (up_reg i hde rfl)).counit
    | .cap ⟨(false, i), r⟩ => fun a b _ _ _ hde _ hce => by
        subst hce
        exact (S.adj i (dn_reg i hde rfl)).counit

end RouqFamily
end Categorification.TwoRep
