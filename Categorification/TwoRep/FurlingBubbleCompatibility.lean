/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingKM3

/-!
# Local generator and bubble compatibility for furling

The objects, adjunctions, dots and crossing of a local weight string are packed
as `RouqLocalData`. Equality of these data transports the local Rouquier
structure and its bubble evaluations. The pairing construction has precisely
the explicit furling data. This supports the vacuum evaluation in Webster,
*Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of
`nondegenerate`, without imposing a scalar bubble formula on the family.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u

/-- The objects and generators on two adjacent edges of a weight string. -/
structure RouqLocalData (B : Type u) [Bicategory.{w,v} B] where
  a : B
  b : B
  c : B
  E₁ : a ⟶ b
  F₁ : b ⟶ a
  E₂ : b ⟶ c
  F₂ : c ⟶ b
  adj₁ : E₁ ⊣ F₁
  adj₂ : E₂ ⊣ F₂
  x₁ : E₁ ⟶ E₁
  x₂ : E₂ ⟶ E₂
  τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂

namespace RouqLocalData
variable {B : Type u} [Bicategory.{w,v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  {D D' : RouqLocalData B} {h : ℤ}

/-- Rouquier local relations for a packed system of generators. -/
abbrev Loc (D : RouqLocalData B) (h : ℤ) :=
  RouqLoc D.adj₁ D.adj₂ D.x₁ D.x₂ D.τ h

/-- Transport local relations along an equality of all generator data. -/
def castLoc (e : D = D') (L : D.Loc h) : D'.Loc h := e ▸ L

theorem castLoc_cw (e : D = D') (L : D.Loc h) (n : ℤ) :
    HEq ((castLoc e L).cw n) (L.cw n) := by cases e; rfl

theorem castLoc_ccw (e : D = D') (L : D.Loc h) (n : ℤ) :
    HEq ((castLoc e L).ccw n) (L.ccw n) := by cases e; rfl
end RouqLocalData

namespace RouqFamily
open QuantumGroup QuantumGroup.UDot
variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {B : Type u} [Bicategory.{w,v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  (T : RouqFamily (B := B) RD)

def localData (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    RouqLocalData B where
  a := T.obj a
  b := T.obj b
  c := T.obj c
  E₁ := T.E i h₁
  F₁ := T.F i h₁
  E₂ := T.E i h₂
  F₂ := T.F i h₂
  adj₁ := T.adj i h₁
  adj₂ := T.adj i h₂
  x₁ := T.dot i h₁
  x₂ := T.dot i h₂
  τ := T.cross i i h₁ h₂ h₁ h₂
/-- The family local relations, viewed over its packed generator data. -/
def dataLoc (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    (T.localData i h₁ h₂).Loc (RD.pair (RD.iY i) b) := T.loc i h₁ h₂
theorem dataLoc_cw (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) (n : ℤ) :
    (T.dataLoc i h₁ h₂).cw n = (T.loc i h₁ h₂).cw n := rfl
theorem dataLoc_ccw (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) (n : ℤ) :
    (T.dataLoc i h₁ h₂).ccw n = (T.loc i h₁ h₂).ccw n := rfl
end RouqFamily
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits KLR KLR.Diagram

universe u₁ u₂ v₁ wk u₃ u₄

namespace Furling

variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc} {RD : QuantumGroup.UDot.WeightDatum C X Y}
  {Φ : Furling RDc RD}
  {S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc}
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {P : I → I → MvPolynomial (Fin 2) k} {D : KLR.Unfurling.UnfurlingDatum k P J}

variable (Φ S D)
def localData (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    RouqLocalData (LinearCat.{wk, max u₁ v₁, max u₁ u₂} k) where
  a := Φ.obj S a
  b := Φ.obj S b
  c := Φ.obj S c
  E₁ := Φ.E S i h₁
  F₁ := Φ.F S i h₁
  E₂ := Φ.E S i h₂
  F₂ := Φ.F S i h₂
  adj₁ := Φ.adj S i h₁
  adj₂ := Φ.adj S i h₂
  x₁ := Φ.dot S D.pw i h₁
  x₂ := Φ.dot S D.pw i h₂
  τ := (Φ.rouqData S D).cross i i h₁ h₂ h₁ h₂

def castLoc (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    {D₀ : RouqLocalData (LinearCat.{wk, max u₁ v₁, max u₁ u₂} k)}
    (e : D₀ = Φ.localData S D i h₁ h₂) (L : D₀.Loc (RD.pair (RD.iY i) b)) :
    RouqLoc (Φ.adj S i h₁) (Φ.adj S i h₂) (Φ.dot S D.pw i h₁) (Φ.dot S D.pw i h₂)
      ((Φ.rouqData S D).cross i i h₁ h₂ h₁ h₂) (RD.pair (RD.iY i) b) :=
  RouqLocalData.castLoc e L
theorem castLoc_cw (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    {D₀ : RouqLocalData (LinearCat.{wk, max u₁ v₁, max u₁ u₂} k)}
    (e : D₀ = Φ.localData S D i h₁ h₂) (L : D₀.Loc (RD.pair (RD.iY i) b)) (n : ℤ) :
    HEq ((Φ.castLoc S D i h₁ h₂ e L).cw n) (L.cw n) := RouqLocalData.castLoc_cw e L n
theorem castLoc_ccw (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    {D₀ : RouqLocalData (LinearCat.{wk, max u₁ v₁, max u₁ u₂} k)}
    (e : D₀ = Φ.localData S D i h₁ h₂) (L : D₀.Loc (RD.pair (RD.iY i) b)) (n : ℤ) :
    HEq ((Φ.castLoc S D i h₁ h₂ e L).ccw n) (L.ccw n) := RouqLocalData.castLoc_ccw e L n

/-- Transport the local relations of a family to explicit furling generators. -/
def castFamilyLoc
    (T : RouqFamily (B := LinearCat.{wk, max u₁ v₁, max u₁ u₂} k) RD)
    (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    (e : T.localData i h₁ h₂ = Φ.localData S D i h₁ h₂) :
    RouqLoc (Φ.adj S i h₁) (Φ.adj S i h₂) (Φ.dot S D.pw i h₁) (Φ.dot S D.pw i h₂)
      ((Φ.rouqData S D).cross i i h₁ h₂ h₁ h₂) (RD.pair (RD.iY i) b) :=
  Φ.castLoc S D i h₁ h₂ e (T.dataLoc i h₁ h₂)
theorem castFamilyLoc_cw
    (T : RouqFamily (B := LinearCat.{wk, max u₁ v₁, max u₁ u₂} k) RD)
    (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    (e : T.localData i h₁ h₂ = Φ.localData S D i h₁ h₂) (n : ℤ) :
    HEq ((Φ.castFamilyLoc S D T i h₁ h₂ e).cw n) ((T.loc i h₁ h₂).cw n) :=
  (Φ.castLoc_cw S D i h₁ h₂ e (T.dataLoc i h₁ h₂) n).trans (heq_of_eq (T.dataLoc_cw i h₁ h₂ n))
theorem castFamilyLoc_ccw
    (T : RouqFamily (B := LinearCat.{wk, max u₁ v₁, max u₁ u₂} k) RD)
    (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    (e : T.localData i h₁ h₂ = Φ.localData S D i h₁ h₂) (n : ℤ) :
    HEq ((Φ.castFamilyLoc S D T i h₁ h₂ e).ccw n) ((T.loc i h₁ h₂).ccw n) :=
  (Φ.castLoc_ccw S D i h₁ h₂ e (T.dataLoc i h₁ h₂) n).trans (heq_of_eq (T.dataLoc_ccw i h₁ h₂ n))

theorem apply_heq {A A' : Type u₅} {V : Type*} {f : A → V} {g : A' → V}
    (hf : HEq f g) {x : A} {y : A'} (hx : HEq x y) : f x = g y := by
  cases hx
  cases hf
  rfl
/-- Transfer a clockwise scalar formula from furling generators to the family. -/
theorem evalFamily_cw
    (T : RouqFamily (B := LinearCat.{wk, max u₁ v₁, max u₁ u₂} k) RD)
    (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    (e : T.localData i h₁ h₂ = Φ.localData S D i h₁ h₂)
    {V : Type*} (ev : End (𝟙 (T.obj b)) → V) (ev' : End (𝟙 (Φ.obj S b)) → V)
    (hev : HEq ev ev') (n : ℤ) (value : V)
    (hv : ∀ loc : RouqLoc (Φ.adj S i h₁) (Φ.adj S i h₂)
        (Φ.dot S D.pw i h₁) (Φ.dot S D.pw i h₂)
        ((Φ.rouqData S D).cross i i h₁ h₂ h₁ h₂) (RD.pair (RD.iY i) b),
      ev' (loc.cw n) = value) :
    ev ((T.loc i h₁ h₂).cw n) = value :=
  (apply_heq hev.symm (Φ.castFamilyLoc_cw S D T i h₁ h₂ e n)).symm.trans
    (hv (Φ.castFamilyLoc S D T i h₁ h₂ e))
/-- Transfer a counterclockwise scalar formula from furling generators to the family. -/
theorem evalFamily_ccw
    (T : RouqFamily (B := LinearCat.{wk, max u₁ v₁, max u₁ u₂} k) RD)
    (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    (e : T.localData i h₁ h₂ = Φ.localData S D i h₁ h₂)
    {V : Type*} (ev : End (𝟙 (T.obj b)) → V) (ev' : End (𝟙 (Φ.obj S b)) → V)
    (hev : HEq ev ev') (n : ℤ) (value : V)
    (hv : ∀ loc : RouqLoc (Φ.adj S i h₁) (Φ.adj S i h₂)
        (Φ.dot S D.pw i h₁) (Φ.dot S D.pw i h₂)
        ((Φ.rouqData S D).cross i i h₁ h₂ h₁ h₂) (RD.pair (RD.iY i) b),
      ev' (loc.ccw n) = value) :
    ev ((T.loc i h₁ h₂).ccw n) = value :=
  (apply_heq hev.symm (Φ.castFamilyLoc_ccw S D T i h₁ h₂ e n)).symm.trans
    (hv (Φ.castFamilyLoc S D T i h₁ h₂ e))

variable
  (hπ : ∀ a, Φ.π a = D.π a)
  (H : RouqUpKLR S (Unfurling.unfQ (k := k) D.arrows))
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
  {Q : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
variable
  (hmix : ∀ (j : I) (a b : J), a ≠ b → Φ.π a = j → Φ.π b = j → ∀ {x y y' z : Xc}
    (e₁ : x + RDc.iX a = y) (e₂ : y + RDc.iX b = z) (e₃ : x + RDc.iX b = y')
    (e₄ : y' + RDc.iX a = z) (M : (S.obj y' : Type u₂)),
    IsIso ((S.adj b e₂).unit.hom.app ((S.E a e₁).obj.obj ((S.F b e₃).obj.obj M)) ≫
      (S.F b e₂).obj.map ((swapCell S D (j = j) e₁ e₂ e₃ e₄).hom.app ((S.F b e₃).obj.obj M) ≫
        (S.E a e₄).obj.map ((S.adj b e₃).counit.hom.app M))))

variable (hpairOrZero : ∀ (i : I) (β : J →₀ ℤ),
    RD.pair (RD.iY i) (Φ.wtG β) =
      ∑ t : Fin (nLbl Φ i β), RDc.pair (RDc.iY (lab Φ i β t)) (Φ.wtT β) ∨
    ∀ M : blkCat Φ S β, IsZero M)


/-- The pairing construction has the explicit furling generator data. -/
theorem rouqFamilyOfPairing_localData (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    (rouqFamilyOfPairing hzero hmix hπ H hnil hPQ hpairOrZero).localData i h₁ h₂ =
      Φ.localData S D i h₁ h₂ := rfl
end Furling
end Categorification.TwoRep
