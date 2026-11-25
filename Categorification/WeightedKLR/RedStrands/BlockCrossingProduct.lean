/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderedBlockAction
import Categorification.Algebra.CornerBimodule

/-!
# The external product with a single two-red crossing

Webster, arXiv:1309.3796v2, §6.1, the bimodule immediately preceding Lemma 6.8.
Take the regular tensor product algebra at each singleton and the off-diagonal violated
corner at the pair. The external product splits off the product of the local violated
algebras by cutting with the top and bottom order projectors in each factor. This splitting
is over the ground ring; it does not cut a diagram in the global standardization column.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR BraidedStendhalAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe v
variable {k : Type v} [CommRing k]

/-- Horizontal coefficients, together with their inclusion into uncut diagrams and the
projection obtained by imposing the two boundary orders. -/
structure BlockCut (R : Type v) [Ring R] [Algebra k R] (p q : R) where
  space : ModuleCat.{v} k
  incl : space →ₗ[k] R
  cut : R →ₗ[k] space
  cut_incl : ∀ x, cut (incl x) = x
  incl_cut : ∀ x, incl (cut x) = p * x * q

namespace BlockCut
variable {R T : Type v} [Ring R] [Algebra k R] [Ring T] [Algebra k T]
    {p q : R} {u v' : T}

/-- Tensor the splittings, rather than assuming tensoring preserves an injection. -/
def tensor (C : BlockCut (k := k) R p q) (D : BlockCut (k := k) T u v') :
    BlockCut (k := k) (R ⊗[k] T) (p ⊗ₜ u) (q ⊗ₜ v') where
  space := ModuleCat.of k (C.space ⊗[k] D.space)
  incl := TensorProduct.map C.incl D.incl
  cut := TensorProduct.map C.cut D.cut
  cut_incl x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul x y => simp only [TensorProduct.map_tmul, C.cut_incl, D.cut_incl]
  incl_cut x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add, add_mul]
    | tmul x y => simp only [TensorProduct.map_tmul, C.incl_cut, D.incl_cut,
        Algebra.TensorProduct.tmul_mul_tmul]

end BlockCut

variable {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)
local notation "topOrd" => (fun (_ : RedBlock I ℓ) => Fin.revPerm)
local notation "P₀" => orderedValue Q Λ hQ botOrd
local notation "P₁" => orderedValue Q Λ hQ topOrd

private def diagonalCut (σ τ : (B : RedBlock I ℓ) → Equiv.Perm (Fin B.size)) (B : RedBlock I ℓ)
    (he : orderedValue Q Λ hQ τ B 1 = orderedValue Q Λ hQ σ B 1) :
    BlockCut (k := k) (quotientAlgebra Q Λ B) (orderedValue Q Λ hQ τ B 1) (orderedValue Q Λ hQ σ B 1) where
  space := ModuleCat.of k (TensorProductAlgebra k Q ((Λ ∘ B.label) ∘ σ B) B.black)
  incl := LinearMap.ofClass (orderedValue Q Λ hQ σ B)
  cut := orderedRetraction Q Λ hQ σ B
  cut_incl x := orderedRetraction_value Q Λ hQ σ B x
  incl_cut y := (orderedValue_retraction Q Λ hQ σ B y).trans (by rw [he])

/-- The regular algebra factor at an unchanged red strand. -/
def spectatorCut (x : Fin ℓ × Multiset I) :
    BlockCut (k := k) (quotientAlgebra Q Λ (spectator x)) (P₁ (spectator x) 1) (P₀ (spectator x) 1) :=
  diagonalCut Q Λ hQ botOrd topOrd (spectator x) (by
    rw [orderedValue_one, orderedValue_one]
    rw [show (Fin.revPerm : Equiv.Perm (Fin 1)) = 1 from Subsingleton.elim ..])

/-- The ground-ring submodule of the braiding bimodule `p V q`. -/
def crossingSpace {R : Type*} [Ring R] [Algebra k R] (p q : R) : Submodule k R where
  __ := cornerBimodule p q
  smul_mem' c x hx := ⟨by rw [mul_smul_comm, hx.1], by rw [smul_mul_assoc, hx.2]⟩

private abbrev pair (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) : RedBlock I ℓ := ⟨2, f, β⟩

/-- The distinguished factor is Webster's two-red crossing, not its image after stacking. -/
def pairCut (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) :
    BlockCut (k := k) (quotientAlgebra Q Λ (pair f β)) (P₁ (pair f β) 1) (P₀ (pair f β) 1) := by
  let p := P₁ (pair f β) 1
  let q := P₀ (pair f β) 1
  have hp : p * p = p := (map_mul (P₁ (pair f β)) 1 1).symm.trans (by rw [one_mul])
  have hq : q * q = q := (map_mul (P₀ (pair f β)) 1 1).symm.trans (by rw [one_mul])
  let C := crossingSpace (k := k) p q
  exact {
    space := ModuleCat.of k C
    incl := C.subtype
    cut := ((LinearMap.mulRight k q) ∘ₗ LinearMap.mulLeft k p).codRestrict C fun x =>
      ⟨by change p * (p*x*q) = p*x*q; rw [← mul_assoc, ← mul_assoc, hp],
       by change p*x*q*q = p*x*q; rw [mul_assoc _ q q, hq]⟩
    cut_incl := fun x => Subtype.ext (show p*x.1*q = x.1 by rw [x.2.1, x.2.2])
    incl_cut := fun _ => rfl }

theorem pairCut_addSubgroup (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) :
    (crossingSpace (k := k) (P₁ (pair f β) 1) (P₀ (pair f β) 1)).toAddSubgroup =
      cornerBimodule (violMk k Q (Λ ∘ f) β (redProj k Q (Λ ∘ f) β [1,0]))
        (violMk k Q (Λ ∘ f) β (redProj k Q (Λ ∘ f) β [0,1])) := by
  rw [orderedValue_one, orderedValue_one]; rfl

local notation "rowCut" Bs => BlockCut (k := k) (quotients Q Λ Bs)
  (orderedInclusion Q Λ hQ topOrd Bs 1) (orderedInclusion Q Λ hQ botOrd Bs 1)

/-- The regular algebra factors at a list of unchanged red strands. -/
def spectatorCuts : (M : List (Fin ℓ × Multiset I)) → rowCut (M.map spectator)
  | [] => { space := ModuleCat.of k (ULift.{0} k), incl := LinearMap.id, cut := LinearMap.id,
            cut_incl := fun _ => rfl, incl_cut := fun x => (by change x = 1*x*1; simp) }
  | x :: xs => (spectatorCut Q Λ hQ x).tensor (spectatorCuts xs)

/-- The ordered exterior tensor in Webster, §6.1, before Lemma 6.8: the regular spectator
factors flank `B([1,0],[0,1])`. `incl` tensors the inclusions of these local diagrams. -/
def crossingProduct (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) :
    (L : List (Fin ℓ × Multiset I)) → rowCut (adjacentRow L M f β)
  | [] => (pairCut Q Λ hQ f β).tensor (spectatorCuts Q Λ hQ M)
  | x :: xs => (spectatorCut Q Λ hQ x).tensor (crossingProduct M f β xs)

end Categorification.Stendhal.RedBlock
