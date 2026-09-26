/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Sl2
import Categorification.QuantumGroup.UDotBlock
import Categorification.KLR.Basic

/-!
# `Q`-strong 2-representations (CL Definition 1.2)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.2 (`def_Qstrong`), with the KLR relations of §2.3
(`sec:KLR`, eqs. (2.8)–(2.14), TeX labels `eq_nil_rels`, `eq_nil_dotslide`, `eq_r2_ij-gen`,
`eq_pq`, `eq_dot_slide_ij-gen`, `eq_r3_easy-gen`, `eq_r3_hard-gen`).

## Conventions

* The Cartan datum is a `RootDatum C X Y` of this library: `X` is the weight lattice, `α_i` is
  `RD.iX i`, `⟨i, λ⟩` is `RD.pair (RD.iY i) λ`; `(α_i, α_j) = C.dot i j`, `d_i = (α_i, α_i)/2` is
  `UDot.di C i`, and `(α_i, λ) = d_i ⟨i, λ⟩` (CL: `⟨i, λ⟩ = 2 (α_i, λ)/(α_i, α_i)`).
* **Weights as indices.** To avoid transporting 1-morphisms along equalities of weights such as
  `λ + α_i + α_j = λ + α_j + α_i`, the 1-morphism `E_i 1_λ : λ → λ + α_i` is `E i h` for a proof
  `h : λ + α_i = μ`, for every `μ`; all statements quantify over the intermediate weights together
  with the equations relating them. (Weights are written `l, m, n, …` since `λ` is reserved.)
* **Composition is in Mathlib's diagrammatic order.** CL's `E_i E_j 1_λ` (first `E_j`) is
  `E j h₁ ≫ E i h₂`; in CL's diagrams (read bottom to top, strands labelled left to right) the
  leftmost strand is the *last* factor.
* Shifted 2-morphisms `X ⟶ Y⟨d⟩` are Mathlib's `ShiftedHom X Y d`; `f.comp g h` is "first `f`,
  then `g`" (bottom to top).

## Definition 1.2

`QStrong k B C RD Q` consists of objects `obj λ`, 1-morphisms `E_i 1_λ` and `1_λ F_i`, and:

* `adj`: `E_i 1_λ ⊣ 1_λ F_i ⟨(α_i, λ) + d_i⟩`, i.e. `1_λ F_i := (E_i 1_λ)_R ⟨-(α_i, λ) - d_i⟩`
  (eq. `eq_defF`); `exists_leftAdj`: `E_i 1_λ` also has a left adjoint;
* `integrable`: condition (1);
* `hom_neg`, `hom_zero`: condition (2), with CL's zero-object convention (one-dimensionality of
  `End(1_λ)` only for nonzero `λ`); finite-dimensionality of all 2-Hom spaces is the instance
  `[∀ a b, HomFinite k (a ⟶ b)]`;
* `EF`, `FE`: condition (3), with `⊕_{[n]_i} 1_λ = qsum (d_i) n (𝟙 _)`;
* `rQ`, `klr`: condition (4), the KLR action in generators and relations (`KLRGens`,
  `KLRGens.IsAction`), for a family `Q_{ij}` of polynomials and the scalars `r_i`;
* `mixed`: condition (5).

## Condition (4)

`KLRGens` carries dots `x : E_i 1_λ → E_i 1_λ ⟨(α_i, α_i)⟩` and crossings
`τ_{ij} : E_i E_j 1_λ → E_j E_i 1_λ ⟨-(α_i, α_j)⟩`; `KLRGens.IsAction k Q r` imposes CL's
relations (2.8)–(2.14): the nilHecke relations (with `r_i`) for equal labels, the quadratic
relation `τ_{ji} τ_{ij} = Q_{ij}(x_i, x_j)` and the free dot slides for `i ≠ j`, and the braid
relations, with the correction `r_i Q̄_{ij}(x, y, z)` (`KLR.qbar`, the divided difference) when
`i = k` and `(α_i, α_j) < 0`. Polynomials are evaluated through their homogeneous component of the
degree of the relation (`homogEval2`, `homogEval3`); for CL's weighted homogeneous `Q`
(`Diagrams/CL/Scalars.lean`, `qCL_isWeightedHomogeneous`, `qbar_qCL_isWeightedHomogeneous`) this
is the full evaluation. The polynomial variables follow `Categorification.KLR`: `X 0` is the dot
on the leftmost strand (in CL's pictures), `X 1` the next one, etc. CL's `Q_{ij}` is the
polynomial `qCL S i j` of `Diagrams/CL/Scalars.lean` (not imported here).

The KLR action of Definition 1.2 is in this generators-and-relations form (as in Rouquier's
definition); the equivalent formulation by algebra maps `R(ν) → End^•(⊕_{i ∈ Seq ν} E_i 1_λ)` is
not formalized.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open QuantumGroup QuantumGroup.UDot

universe w v u

variable (B : Type u) [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  {I : Type*} (C : CartanDatum I) {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y)

/-- **The generators of a KLR action** on the 1-morphisms `E_i 1_λ` (CL §2.3): objects indexed by
the weights, `E_i 1_λ` (as `E i h` for `h : λ + α_i = μ`), dots of degree `(α_i, α_i)` and
crossings `E_i E_j 1_λ → E_j E_i 1_λ` of degree `-(α_i, α_j)`. -/
structure KLRGens where
  /-- The object of the weight `λ`. -/
  obj : X → B
  /-- `E_i 1_λ : λ → μ` for `λ + α_i = μ`. -/
  E : ∀ (i : I) {l m : X}, l + RD.iX i = m → (obj l ⟶ obj m)
  /-- The dot on `E_i 1_λ`. -/
  dot : ∀ (i : I) {l m : X} (h : l + RD.iX i = m), ShiftedHom (E i h) (E i h) (C.dot i i)
  /-- The crossing `E_i E_j 1_λ → E_j E_i 1_λ` (CL: bottom labels `i j`, top labels `j i`). -/
  cross : ∀ (i j : I) {l n m n' : X} (h₁ : l + RD.iX j = n) (h₂ : n + RD.iX i = m)
    (h₃ : l + RD.iX i = n') (h₄ : n' + RD.iX j = m),
    ShiftedHom (E j h₁ ≫ E i h₂) (E i h₃ ≫ E j h₄) (-C.dot i j)

namespace KLRGens

variable {B C RD} (G : KLRGens B C RD)

/-- The crossing of the two left strands (CL's pictures; Mathlib: the last two factors) of
`E_i E_j E_c 1_λ`, i.e. `E c e1 ≫ E j e2 ≫ E i e3 → E c e1 ≫ E i e4 ≫ E j e5`. -/
def crossL (i j c : I) {l w₁ w₂ w₃ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX j = w₂)
    (e3 : w₂ + RD.iX i = m) (e4 : w₁ + RD.iX i = w₃) (e5 : w₃ + RD.iX j = m) :
    ShiftedHom (G.E c e1 ≫ G.E j e2 ≫ G.E i e3) (G.E c e1 ≫ G.E i e4 ≫ G.E j e5) (-C.dot i j) :=
  shWhiskerLeft (G.E c e1) (G.cross i j e2 e3 e4 e5)

/-- The crossing of the two right strands (CL's pictures; Mathlib: the first two factors) of
`E_i E_j E_c 1_λ`, i.e. `E c e1 ≫ E j e2 ≫ E i e3 → E j e6 ≫ E c e7 ≫ E i e3`. -/
def crossR (i j c : I) {l w₁ w₂ w₄ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX j = w₂)
    (e3 : w₂ + RD.iX i = m) (e6 : l + RD.iX j = w₄) (e7 : w₄ + RD.iX c = w₂) :
    ShiftedHom (G.E c e1 ≫ G.E j e2 ≫ G.E i e3) (G.E j e6 ≫ G.E c e7 ≫ G.E i e3) (-C.dot j c) :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ (G.E c e1) (G.E j e2) (G.E i e3)).inv).comp
    ((shWhiskerRight (G.cross j c e1 e2 e6 e7) (G.E i e3)).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ (G.E j e6) (G.E c e7) (G.E i e3)).hom)
      (by ring : (0 : ℤ) + -C.dot j c = -C.dot j c))
    (by ring : -C.dot j c + (0 : ℤ) = -C.dot j c)

/-- The composite "left crossing, right crossing, left crossing" (bottom to top) on
`E_i E_j E_c 1_λ` (CL's pictures, bottom labels `i j c`), ending at `E_c E_j E_i 1_λ`. -/
def braidLRL (i j c : I) {l w₁ w₂ w₃ w₄ w₅ m : X} (e1 : l + RD.iX c = w₁)
    (e2 : w₁ + RD.iX j = w₂) (e3 : w₂ + RD.iX i = m) (e4 : w₁ + RD.iX i = w₃)
    (e5 : w₃ + RD.iX j = m) (e6 : l + RD.iX i = w₄) (e7 : w₄ + RD.iX c = w₃)
    (e8 : w₄ + RD.iX j = w₅) (e9 : w₅ + RD.iX c = m) :
    ShiftedHom (G.E c e1 ≫ G.E j e2 ≫ G.E i e3) (G.E i e6 ≫ G.E j e8 ≫ G.E c e9)
      (-(C.dot i j + C.dot i c + C.dot j c)) :=
  ((G.crossL i j c e1 e2 e3 e4 e5).comp (G.crossR j i c e1 e4 e5 e6 e7)
      (by ring : -C.dot i c + -C.dot i j = -(C.dot i j + C.dot i c))).comp
    (G.crossL j c i e6 e7 e5 e8 e9)
    (by ring : -C.dot j c + -(C.dot i j + C.dot i c) = -(C.dot i j + C.dot i c + C.dot j c))

/-- The composite "right crossing, left crossing, right crossing" (bottom to top) on
`E_i E_j E_c 1_λ`, ending at `E_c E_j E_i 1_λ`. -/
def braidRLR (i j c : I) {l w₁ w₂ w₄ w₅ w₆ m : X} (e1 : l + RD.iX c = w₁)
    (e2 : w₁ + RD.iX j = w₂) (e3 : w₂ + RD.iX i = m) (e6 : l + RD.iX i = w₄)
    (e8 : w₄ + RD.iX j = w₅) (e9 : w₅ + RD.iX c = m) (e10 : l + RD.iX j = w₆)
    (e11 : w₆ + RD.iX c = w₂) (e12 : w₆ + RD.iX i = w₅) :
    ShiftedHom (G.E c e1 ≫ G.E j e2 ≫ G.E i e3) (G.E i e6 ≫ G.E j e8 ≫ G.E c e9)
      (-(C.dot i j + C.dot i c + C.dot j c)) :=
  ((G.crossR i j c e1 e2 e3 e10 e11).comp (G.crossL i c j e10 e11 e3 e12 e9)
      (by ring : -C.dot i c + -C.dot j c = -(C.dot j c + C.dot i c))).comp
    (G.crossR c i j e10 e12 e9 e6 e8)
    (by ring : -C.dot i j + -(C.dot j c + C.dot i c) = -(C.dot i j + C.dot i c + C.dot j c))

variable (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)]

/-- **The KLR relations** (CL §2.3, (2.8)–(2.14)) for the polynomials `Q` and the scalars `r`.
See the module docstring for the conventions. -/
structure IsAction (Q : I → I → MvPolynomial (Fin 2) k) (r : I → kˣ) : Prop where
  /-- (2.8), left: the square of an `ii`-crossing is zero. -/
  cross_sq_self : ∀ (i : I) {l n m : X} (h₁ : l + RD.iX i = n) (h₂ : n + RD.iX i = m),
    (G.cross i i h₁ h₂ h₁ h₂).comp (G.cross i i h₁ h₂ h₁ h₂)
      (by ring : -C.dot i i + -C.dot i i = -2 * C.dot i i) = 0
  /-- (2.9), first equality: `r_i · 1 = (dot on the left strand, then crossing) -
  (crossing, then dot on the right strand)`. -/
  dot_slide_self_left : ∀ (i : I) {l n m : X} (h₁ : l + RD.iX i = n) (h₂ : n + RD.iX i = m),
    ShiftedHom.mk₀ (0 : ℤ) rfl ((r i : k) • 𝟙 (G.E i h₁ ≫ G.E i h₂)) =
      (shWhiskerLeft (G.E i h₁) (G.dot i h₂)).comp (G.cross i i h₁ h₂ h₁ h₂)
          (by ring : -C.dot i i + C.dot i i = 0) -
        (G.cross i i h₁ h₂ h₁ h₂).comp (shWhiskerRight (G.dot i h₁) (G.E i h₂))
          (by ring : C.dot i i + -C.dot i i = 0)
  /-- (2.9), second equality: `r_i · 1 = (crossing, then dot on the left strand) -
  (dot on the right strand, then crossing)`. -/
  dot_slide_self_right : ∀ (i : I) {l n m : X} (h₁ : l + RD.iX i = n) (h₂ : n + RD.iX i = m),
    ShiftedHom.mk₀ (0 : ℤ) rfl ((r i : k) • 𝟙 (G.E i h₁ ≫ G.E i h₂)) =
      (G.cross i i h₁ h₂ h₁ h₂).comp (shWhiskerLeft (G.E i h₁) (G.dot i h₂))
          (by ring : C.dot i i + -C.dot i i = 0) -
        (shWhiskerRight (G.dot i h₁) (G.E i h₂)).comp (G.cross i i h₁ h₂ h₁ h₂)
          (by ring : -C.dot i i + C.dot i i = 0)
  /-- (2.10): for `i ≠ j`, `τ_{ji} τ_{ij} = Q_{ij}(x_i, x_j)` on `E_i E_j 1_λ`, where `x_i` is the
  dot on the (left) `i`-strand and `x_j` the dot on the (right) `j`-strand. -/
  cross_sq : ∀ (i j : I), i ≠ j → ∀ {l n m n' : X} (h₁ : l + RD.iX j = n)
    (h₂ : n + RD.iX i = m) (h₃ : l + RD.iX i = n') (h₄ : n' + RD.iX j = m),
    (G.cross i j h₁ h₂ h₃ h₄).comp (G.cross j i h₃ h₄ h₁ h₂)
        (by rw [C.symm j i]; ring : -C.dot j i + -C.dot i j = -2 * C.dot i j) =
      homogEval2 k (Q i j) (shWhiskerLeft (G.E j h₁) (G.dot i h₂))
        (shWhiskerRight (G.dot j h₁) (G.E i h₂)) (-2 * C.dot i j)
  /-- (2.12), for `i ≠ j`: a dot on the `i`-strand slides through the crossing. -/
  dot_slide_left : ∀ (i j : I), i ≠ j → ∀ {l n m n' : X} (h₁ : l + RD.iX j = n)
    (h₂ : n + RD.iX i = m) (h₃ : l + RD.iX i = n') (h₄ : n' + RD.iX j = m),
    (shWhiskerLeft (G.E j h₁) (G.dot i h₂)).comp (G.cross i j h₁ h₂ h₃ h₄)
        (by ring : -C.dot i j + C.dot i i = C.dot i i - C.dot i j) =
      (G.cross i j h₁ h₂ h₃ h₄).comp (shWhiskerRight (G.dot i h₃) (G.E j h₄))
        (by ring : C.dot i i + -C.dot i j = C.dot i i - C.dot i j)
  /-- (2.12), for `i ≠ j`: a dot on the `j`-strand slides through the crossing. -/
  dot_slide_right : ∀ (i j : I), i ≠ j → ∀ {l n m n' : X} (h₁ : l + RD.iX j = n)
    (h₂ : n + RD.iX i = m) (h₃ : l + RD.iX i = n') (h₄ : n' + RD.iX j = m),
    (shWhiskerRight (G.dot j h₁) (G.E i h₂)).comp (G.cross i j h₁ h₂ h₃ h₄)
        (by ring : -C.dot i j + C.dot j j = C.dot j j - C.dot i j) =
      (G.cross i j h₁ h₂ h₃ h₄).comp (shWhiskerLeft (G.E i h₃) (G.dot j h₄))
        (by ring : C.dot j j + -C.dot i j = C.dot j j - C.dot i j)
  /-- (2.13): the braid relation, unless `i = c` and `(α_i, α_j) < 0` (bottom labels `i j c`). -/
  braid : ∀ (i j c : I), ¬ (i = c ∧ C.dot i j < 0) →
    ∀ {l w₁ w₂ w₃ w₄ w₅ w₆ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX j = w₂)
      (e3 : w₂ + RD.iX i = m) (e4 : w₁ + RD.iX i = w₃) (e5 : w₃ + RD.iX j = m)
      (e6 : l + RD.iX i = w₄) (e7 : w₄ + RD.iX c = w₃) (e8 : w₄ + RD.iX j = w₅)
      (e9 : w₅ + RD.iX c = m) (e10 : l + RD.iX j = w₆) (e11 : w₆ + RD.iX c = w₂)
      (e12 : w₆ + RD.iX i = w₅),
    G.braidLRL i j c e1 e2 e3 e4 e5 e6 e7 e8 e9 = G.braidRLR i j c e1 e2 e3 e6 e8 e9 e10 e11 e12
  /-- (2.14): for `(α_i, α_j) < 0`, on `E_i E_j E_i 1_λ`,
  `r_i^{-1} (LRL - RLR) = Q̄_{ij}(x_left, x_middle, x_right)`. -/
  braid_corr : ∀ (i j : I), C.dot i j < 0 →
    ∀ {l w₁ w₂ w₃ w₆ m : X} (e1 : l + RD.iX i = w₁) (e2 : w₁ + RD.iX j = w₂)
      (e3 : w₂ + RD.iX i = m) (e4 : w₁ + RD.iX i = w₃) (e5 : w₃ + RD.iX j = m)
      (e10 : l + RD.iX j = w₆) (e11 : w₆ + RD.iX i = w₂),
    ((r i)⁻¹ : k) • (G.braidLRL i j i e1 e2 e3 e4 e5 e1 e4 e2 e3 -
        G.braidRLR i j i e1 e2 e3 e1 e2 e3 e10 e11 e11) =
      homogEval3 k (KLR.qbar (Q i j))
        (shWhiskerLeft (G.E i e1) (shWhiskerLeft (G.E j e2) (G.dot i e3)))
        (shWhiskerLeft (G.E i e1) (shWhiskerRight (G.dot j e2) (G.E i e3)))
        (shWhiskerRight (G.dot i e1) (G.E j e2 ≫ G.E i e3))
        (-(C.dot i j + C.dot i i + C.dot j i))

end KLRGens

variable (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]

/-- **A `Q`-strong 2-representation of `g`** (CL Definition 1.2, `def_Qstrong`) on the graded
additive `k`-linear bicategory `B`, for the Cartan datum `RD` and the KLR polynomials `Q`. See the
module docstring for the conventions and fields. -/
structure QStrong (Q : I → I → MvPolynomial (Fin 2) k) extends KLRGens B C RD where
  /-- `1_λ F_i : λ + α_i → λ`. -/
  F : ∀ (i : I) {l m : X}, l + RD.iX i = m → (obj m ⟶ obj l)
  /-- `1_λ F_i := (E_i 1_λ)_R ⟨-(α_i, λ) - d_i⟩` (eq. `eq_defF`), with `(α_i, λ) = d_i ⟨i, λ⟩`. -/
  adj : ∀ (i : I) {l m : X} (h : l + RD.iX i = m),
    E i h ⊣ (F i h)⟦di C i * (RD.pair (RD.iY i) l + 1)⟧
  /-- `E_i 1_λ` also has a left adjoint. -/
  exists_leftAdj : ∀ (i : I) {l m : X} (h : l + RD.iX i = m), ∃ L : obj m ⟶ obj l,
    Nonempty (L ⊣ E i h)
  /-- Condition (1), integrability. -/
  integrable : ∀ (i : I) (l : X), ∃ N : ℕ, ∀ r : ℤ, (N : ℤ) ≤ |r| →
    IsZero (𝟙 (obj (l + r • RD.iX i)))
  /-- Condition (2): `Hom(1_λ, 1_λ⟨d⟩) = 0` for `d < 0`. -/
  hom_neg : ∀ (l : X) (d : ℤ), d < 0 → finrank k (𝟙 (obj l) ⟶ (𝟙 (obj l))⟦d⟧) = 0
  /-- Condition (2): `Hom(1_λ, 1_λ)` is one-dimensional for nonzero `λ`. -/
  hom_zero : ∀ l : X, ¬ IsZero (𝟙 (obj l)) → finrank k (𝟙 (obj l) ⟶ 𝟙 (obj l)) = 1
  /-- Condition (3): `F_i E_i 1_λ ≅ E_i F_i 1_λ ⊕_{[-⟨i,λ⟩]_i} 1_λ` if `⟨i, λ⟩ ≤ 0`. -/
  FE : ∀ (i : I) {n l m : X} (h₁ : n + RD.iX i = l) (h₂ : l + RD.iX i = m),
    RD.pair (RD.iY i) l ≤ 0 →
    Nonempty (E i h₂ ≫ F i h₂ ≅
      (F i h₁ ≫ E i h₁) ⊞ qsum (di C i) (-RD.pair (RD.iY i) l).toNat (𝟙 (obj l)))
  /-- Condition (3): `E_i F_i 1_λ ≅ F_i E_i 1_λ ⊕_{[⟨i,λ⟩]_i} 1_λ` if `⟨i, λ⟩ ≥ 0`. -/
  EF : ∀ (i : I) {n l m : X} (h₁ : n + RD.iX i = l) (h₂ : l + RD.iX i = m),
    0 ≤ RD.pair (RD.iY i) l →
    Nonempty (F i h₁ ≫ E i h₁ ≅
      (E i h₂ ≫ F i h₂) ⊞ qsum (di C i) (RD.pair (RD.iY i) l).toNat (𝟙 (obj l)))
  /-- Condition (4): the scalars `r_i`. -/
  rQ : I → kˣ
  /-- Condition (4): the `E`'s carry an action of the KLR algebra. -/
  klr : toKLRGens.IsAction k Q rQ
  /-- Condition (5): `F_j E_i 1_λ ≅ E_i F_j 1_λ` for `i ≠ j`. -/
  mixed : ∀ (i j : I), i ≠ j → ∀ {l m p s : X} (h₁ : l + RD.iX i = m) (h₂ : p + RD.iX j = m)
    (h₃ : s + RD.iX j = l) (h₄ : s + RD.iX i = p),
    Nonempty (E i h₁ ≫ F j h₂ ≅ F j h₃ ≫ E i h₄)

end Categorification.TwoRep
