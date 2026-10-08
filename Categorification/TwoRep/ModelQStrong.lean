/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelSl2
import Categorification.TwoRep.QStrongBBw
import Categorification.Diagrams.CL.Scalars

/-!
# The model of `U_Q(g)` given by a `Q`-strong 2-representation

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Theorem 1.1: a `Q`-strong 2-representation of `g` (Definition 1.2) satisfying
(BB_w) gives a 2-representation of `U_Q(g)`. This file sets up the data of that 2-functor on the
signature `psig RD` of `U` (`Categorification.Diagrams.KL3.Basic`), as a model in the
graded-Hom bicategory `K^•` in the sense of `Categorification.Diagrams.BicatInterp`, for a Cartan
datum with `(α_i, α_i) = 2` for all `i` (the restriction to `α_i`-strings `QStrong.toStrongSl2`
is formalized in this case):

* the region of weight `λ` goes to the object `obj λ` itself (no parity condition, unlike the
  `sl₂` model of `Categorification.TwoRep.ModelSl2`, which indexes the objects of a string by
  integers);
* an upward strand labelled `i` goes to `E_i 1_λ` (`Eg`), a downward strand to its right adjoint
  `1_λ F_i ⟨(α_i, λ) + d_i⟩` (`Rg`, the adjunction `QStrong.adj`, `adjR`);
* the upward dot goes to the normalized dot `r_i⁻¹ x` (`dotQ`), the upward crossing to the
  crossing `τ_{ij}` of the KLR action (`crossQ`);
* the left adjunctions `R ⊣ E` of an `α_i`-string are the normalized left adjunctions
  (`StrongSl2.BBw.leftAdjN`, CL (4.1)) of the restriction of `S` to that string, for one fixed
  base point of each coset `λ + ℤ α_i` (`strBase`; the index of `λ` along the string is
  `strIdx`), so that all strands of a string use the same choice (`adjL`);
* cups and caps go to the units and counits of `E ⊣ R` and `R ⊣ E` (table of
  `Categorification.Diagrams.KL3.Basic`), the downward dot and crossing to the mates of the upward
  ones under the left adjunctions; the downward crossing with bottom labels `i`, `j` carries the
  scalar `t_{ji}⁻¹` of a choice of scalars (`CLScalars`), as in CL's `Q`-cyclicity
  (`eq_almost_cyclic`; `t_{ii} = 1`).

## Main definitions

* `QStrong.strBase`, `QStrong.strIdx`: base points and indices along `α_i`-strings;
* `QStrong.Eg`, `QStrong.Rg`, `QStrong.adjR`, `QStrong.adjL`, `QStrong.dotQ`, `QStrong.crossQ`;
* `QStrong.model`: the model of `psig RD` in `K^•`;
* `QStrong.genImg`: the images of the generators.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u u₁

section Model

open GradedHomBicat GradedHomCat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

namespace QStrong

/-! ## Base points of the `α_i`-strings -/

section Strings

variable (RD) in
/-- The base point of the `α_i`-string through `λ`: a fixed representative of the coset
`λ + ℤ α_i`. -/
def strBase (i : I) (x : X) : X :=
  (QuotientAddGroup.mk x : X ⧸ AddSubgroup.zmultiples (RD.iX i)).out

theorem strBase_spec (i : I) (x : X) : ∃ r : ℤ, strBase RD i x + r • RD.iX i = x := by
  obtain ⟨⟨h, hh⟩, e⟩ := QuotientAddGroup.mk_out_eq_add (AddSubgroup.zmultiples (RD.iX i)) x
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hh
  exact ⟨-n, by rw [strBase, e, neg_smul, add_neg_cancel_right]⟩

variable (RD) in
/-- The index of `λ` along the `α_i`-string from its base point:
`λ = strBase i λ + (strIdx i λ) α_i`. -/
def strIdx (i : I) (x : X) : ℤ := (strBase_spec (RD := RD) i x).choose

theorem strBase_add_strIdx (i : I) (x : X) :
    strBase RD i x + strIdx RD i x • RD.iX i = x :=
  (strBase_spec i x).choose_spec

/-- The base point depends only on the coset `λ + ℤ α_i`. -/
theorem strBase_add_zsmul (i : I) (x : X) (r : ℤ) :
    strBase RD i (x + r • RD.iX i) = strBase RD i x := by
  unfold strBase
  rw [QuotientAddGroup.mk_add_of_mem x (AddSubgroup.zsmul_mem_zmultiples (RD.iX i) r)]

theorem strBase_add (i : I) (x : X) : strBase RD i (x + RD.iX i) = strBase RD i x := by
  simpa using strBase_add_zsmul i x 1

/-- The index along a string is unique (`⟨i, α_i⟩ = 2`). -/
theorem zsmul_iX_injective (i : I) {r s : ℤ} (h : r • RD.iX i = s • RD.iX i) : r = s := by
  have := congrArg (RD.pair (RD.iY i)) h
  rw [map_zsmul, map_zsmul, RD.pair_iY_iX_self, smul_eq_mul, smul_eq_mul] at this
  omega

theorem strIdx_eq (i : I) {x : X} {r : ℤ} (h : strBase RD i x + r • RD.iX i = x) :
    strIdx RD i x = r := by
  refine zsmul_iX_injective (RD := RD) i ?_
  have h' := strBase_add_strIdx (RD := RD) i x
  exact add_left_cancel (h'.trans h.symm)

/-- The base point of a base point is itself. -/
theorem strBase_strBase (i : I) (x : X) : strBase RD i (strBase RD i x) = strBase RD i x := by
  conv_rhs => rw [← strBase_add_strIdx (RD := RD) i x, strBase_add_zsmul]

/-- Along the string of a base point `b`, the base point is `b` and the index is `r`. -/
theorem strBase_string (i : I) (x : X) (r : ℤ) :
    strBase RD i (strBase RD i x + r • RD.iX i) = strBase RD i x := by
  rw [strBase_add_zsmul, strBase_strBase]

theorem strIdx_string (i : I) (x : X) (r : ℤ) :
    strIdx RD i (strBase RD i x + r • RD.iX i) = r :=
  strIdx_eq i (by rw [strBase_string])

theorem strBase_succ (i : I) {x y : X} (h : x + RD.iX i = y) :
    strBase RD i x + (strIdx RD i x + 1) • RD.iX i = y := by
  rw [add_smul, one_smul, ← add_assoc, strBase_add_strIdx, h]

end Strings

/-! ## Strands -/

section Strands

variable (S : QStrong B C RD k Q)

theorem sh_up (i : I) : sh RD ((true, i) : Letter I) = RD.iX i := by
  simp [sh]

theorem sh_dn (i : I) : sh RD ((false, i) : Letter I) = -RD.iX i := by
  simp [sh]

/-- `E_i 1_λ : λ → μ` (for `λ + α_i = μ`) in the graded-Hom bicategory. -/
abbrev Eg (i : I) {x y : X} (h : x + RD.iX i = y) : of (S.obj x) ⟶ of (S.obj y) :=
  of₁ (S.E i h)

/-- The right adjoint `1_λ F_i ⟨(α_i, λ) + d_i⟩` of `E_i 1_λ` (`QStrong.adj`, eq. `eq_defF`) in
the graded-Hom bicategory. -/
abbrev Rg (i : I) {x y : X} (h : x + RD.iX i = y) : of (S.obj y) ⟶ of (S.obj x) :=
  of₁ ((S.F i h)⟦di C i * (RD.pair (RD.iY i) x + 1)⟧)

/-- The adjunction `E_i 1_λ ⊣ 1_λ F_i ⟨(α_i, λ) + d_i⟩` in the graded-Hom bicategory (unit and
counit of degree `0`). -/
def adjR (i : I) {x y : X} (h : x + RD.iX i = y) : S.Eg i h ⊣ S.Rg i h :=
  mapAdjunction (S.adj i h)

theorem up_reg (i : I) {r x y : X} (hx : r = x) (hy : sh RD ((true, i) : Letter I) + r = y) :
    x + RD.iX i = y := by
  subst hx hy; rw [sh_up, add_comm]

theorem dn_reg (i : I) {r x y : X} (hx : r = x) (hy : sh RD ((false, i) : Letter I) + r = y) :
    y + RD.iX i = x := by
  subst hx hy; rw [sh_dn, neg_add_cancel_comm]

/-- The image of a strand between regions `x` (right) and `y` (left): `E_i` for an upward strand,
its right adjoint for a downward one. -/
def strandImg : (c : Col I X) → (x y : X) → c.r = x → sh RD c.l + c.r = y →
    (of (S.obj x) ⟶ of (S.obj y))
  | ⟨(true, i), _⟩, _, _, hx, hy => S.Eg i (up_reg i hx hy)
  | ⟨(false, i), _⟩, _, _, hx, hy => S.Rg i (dn_reg i hx hy)

/-- **The model of the signature of `U`** given by a `Q`-strong 2-representation, in the
graded-Hom bicategory: regions to the objects of the weights, strands to `E_i` and to their right
adjoints. -/
def model : Model (psig RD) (GradedHomBicat B) where
  obj x := of (S.obj x)
  strandAt c x y hx hy := S.strandImg c x y hx hy

@[simp] theorem model_obj (x : X) : S.model.obj x = of (S.obj x) := rfl

theorem model_strandAt_true (i : I) (r x y : X) (hx : r = x)
    (hy : sh RD ((true, i) : Letter I) + r = y) :
    S.model.strandAt ⟨(true, i), r⟩ x y hx hy = S.Eg i (up_reg i hx hy) := rfl

theorem model_strandAt_false (i : I) (r x y : X) (hx : r = x)
    (hy : sh RD ((false, i) : Letter I) + r = y) :
    S.model.strandAt ⟨(false, i), r⟩ x y hx hy = S.Rg i (dn_reg i hx hy) := rfl

end Strands

/-! ## Dots, crossings and adjunctions -/

section Gens

variable (S : QStrong B C RD k Q) [GradedBicategory.IsLinear B k]

/-- The normalized dot `r_i⁻¹ x` on `E_i 1_λ`, of degree `(α_i, α_i)`. -/
def dotQ (i : I) {x y : X} (h : x + RD.iX i = y) : S.Eg i h ⟶ S.Eg i h :=
  (((S.rQ i)⁻¹ : kˣ) : k) • of₂ (C.dot i i) (S.dot i h)

/-- The crossing `τ_{ij} : E_i E_j 1_λ → E_j E_i 1_λ` of the KLR action, of degree `-(α_i, α_j)`
(CL's bottom labels `i j`; Mathlib's composition order `E_j ≫ E_i`). -/
def crossQ (i j : I) {l n m n' : X} (h₁ : l + RD.iX j = n) (h₂ : n + RD.iX i = m)
    (h₃ : l + RD.iX i = n') (h₄ : n' + RD.iX j = m) :
    S.Eg j h₁ ≫ S.Eg i h₂ ⟶ S.Eg i h₃ ≫ S.Eg j h₄ :=
  of₂ (-C.dot i j) (S.cross i j h₁ h₂ h₃ h₄)

omit [GradedBicategory.IsLinear B k] in
/-- The right adjoint of the restriction to the `α_i`-string through `b`, at index `r`, is `Rg`
at the corresponding weights. -/
theorem grR_toStrongSl2 (hsl : ∀ i, C.dot i i = 2) (i : I) (b : X) (r : ℤ)
    (h : b + r • RD.iX i + RD.iX i = b + (r + 1) • RD.iX i) :
    (S.toStrongSl2 i (hsl i) b).grR r = S.Rg i h := by
  have e : RD.pair (RD.iY i) b + 2 * r + 1 =
      di C i * (RD.pair (RD.iY i) (b + r • RD.iX i) + 1) := by
    rw [di_eq_one i (hsl i), pair_string, one_mul]
  exact congrArg (fun n : ℤ => of₁ ((S.F i h)⟦n⟧)) e

variable [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
variable {S} (hsl : ∀ i, C.dot i i = 2) (hS : S.BBw)

/-- Transport of an adjunction along an equality of left adjoints. -/
def transportLeft {D : Type*} [Bicategory D] {a b : D} {R R' : b ⟶ a} {E : a ⟶ b} (h : R = R')
    (adj : R ⊣ E) : R' ⊣ E :=
  h ▸ adj

include hsl hS in
/-- The normalized left adjunction of the `α_i`-string through the base point `b`, at the index
`r`, transported to the weights `x = b + r α_i`, `y = b + (r + 1) α_i`. -/
def adjLAux (i : I) (b : X) (r : ℤ) {x y : X} (e : b + r • RD.iX i = x)
    (e' : b + (r + 1) • RD.iX i = y) (h : x + RD.iX i = y) : S.Rg i h ⊣ S.Eg i h := by
  subst e e'
  exact transportLeft (grR_toStrongSl2 S hsl i b r h) ((hS.toStrongSl2 i (hsl i) b).leftAdjN r)

theorem adjLAux_congr (i : I) {b b' : X} {r r' : ℤ} (hb : b = b') (hr : r = r') {x y : X}
    (e : b + r • RD.iX i = x) (e' : b + (r + 1) • RD.iX i = y)
    (f : b' + r' • RD.iX i = x) (f' : b' + (r' + 1) • RD.iX i = y) (h : x + RD.iX i = y) :
    adjLAux hsl hS i b r e e' h = adjLAux hsl hS i b' r' f f' h := by
  subst hb hr; rfl

include hsl hS in
/-- **The left adjunction `R ⊣ E`** of the model: the normalized left adjunction of the
restriction of `S` to the `α_i`-string through the base point of `λ`. -/
def adjL (i : I) {x y : X} (h : x + RD.iX i = y) : S.Rg i h ⊣ S.Eg i h :=
  adjLAux hsl hS i (strBase RD i x) (strIdx RD i x) (strBase_add_strIdx i x) (strBase_succ i h) h

/-- Along the string of a base point `b`, the left adjunction at `b + r α_i` is the normalized
left adjunction of the restriction to the string through `b`, at index `r`. -/
theorem adjL_eq (i : I) (b : X) (hb : strBase RD i b = b) (r : ℤ) {x y : X}
    (e : b + r • RD.iX i = x) (e' : b + (r + 1) • RD.iX i = y) (h : x + RD.iX i = y) :
    adjL hsl hS i h = adjLAux hsl hS i b r e e' h := by
  have hx : strBase RD i x = b := by rw [← e, strBase_add_zsmul, hb]
  have hr : strIdx RD i x = r := strIdx_eq i (by rw [hx, e])
  exact adjLAux_congr hsl hS i hx hr _ _ _ _ h

include hsl hS in
/-- The downward dot: the mate of the dot under the left adjunction (the rotation `rotDotR`). -/
def dotDnQ (i : I) {x y : X} (h : x + RD.iX i = y) : S.Rg i h ⟶ S.Rg i h :=
  (Bicategory.conjugateEquiv (adjL hsl hS i h) (adjL hsl hS i h)).symm (S.dotQ i h)

include hsl hS in
/-- The downward crossing with bottom labels `i`, `j` (CL's reading; Mathlib: `R_j ≫ R_i`): the
mate of the upward crossing `τ_{ij}` under the composites of the left adjunctions (the rotation
`rotCrossR`), times `t_{ji}⁻¹`. -/
def crossDnQ (Sc : CL.CLScalars C k) (i j : I) {a n n' b : X} (hj : n' + RD.iX j = b)
    (hi : a + RD.iX i = n') (hi' : n + RD.iX i = b) (hj' : a + RD.iX j = n) :
    S.Rg j hj ≫ S.Rg i hi ⟶ S.Rg i hi' ≫ S.Rg j hj' :=
  (((Sc.t j i)⁻¹ : kˣ) : k) •
    (Bicategory.conjugateEquiv ((adjL hsl hS i hi').comp (adjL hsl hS j hj'))
      ((adjL hsl hS j hj).comp (adjL hsl hS i hi))).symm (S.crossQ i j hj' hi' hi hj)

end Gens

/-! ## The images of the generators -/

section GenImg

variable {S : QStrong B C RD k Q} [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  (hsl : ∀ i, C.dot i i = 2) (hS : S.BBw) (Sc : CL.CLScalars C k)

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

include hsl hS Sc in
/-- **The images of the generators** of `U` in the model of a `Q`-strong 2-representation, read
between regions `a` (left) and `b` (right). -/
def genImg : GenImg S.model where
  gen g := match g with
    | .gen (.dot ⟨(true, i), r⟩) => fun a b _ _ hd hde _ _ =>
        S.dotQ i (up_reg i hde hd.1)
    | .gen (.dot ⟨(false, i), r⟩) => fun a b _ _ hd hde _ _ =>
        dotDnQ hsl hS i (dn_reg i hde hd.1)
    | .gen (.cross true i j ν) => fun a b _ _ hd hde _ _ => by
        obtain rfl : ν = b := hde
        exact S.crossQ i j (cross_up_reg j ν) (cross_up_reg' i j hd.1) (cross_up_reg i ν)
          (cross_up_swap i j hd.1)
    | .gen (.cross false i j ν) => fun a b _ _ hd hde _ _ => by
        obtain rfl : ν = b := hde
        exact crossDnQ hsl hS Sc i j (cross_dn_reg j ν) (cross_dn_reg' i j hd.1)
          (cross_dn_reg i ν) (cross_dn_swap i j hd.1)
    | .cup ⟨(true, i), r⟩ => fun a b ha _ _ hde _ _ => by
        subst hde
        exact (adjL hsl hS i (up_reg i rfl ha)).unit
    | .cup ⟨(false, i), r⟩ => fun a b ha _ _ hde _ _ => by
        subst hde
        exact (S.adjR i (dn_reg i rfl ha)).unit
    | .cap ⟨(true, i), r⟩ => fun a b _ _ _ hde _ hce => by
        subst hce
        exact (adjL hsl hS i (up_reg i hde rfl)).counit
    | .cap ⟨(false, i), r⟩ => fun a b _ _ _ hde _ hce => by
        subst hce
        exact (S.adjR i (dn_reg i hde rfl)).counit

end GenImg

end QStrong

end Model

end Categorification.TwoRep
