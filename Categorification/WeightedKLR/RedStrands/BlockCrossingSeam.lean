/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingDiagramCut

/-!
# Marking an uncrossed seam above an interior relation

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8. Factor the part of the diagram
*above* an uncrossed loading using adapted reduced words. The part below it can then be
reattached without straightening across the cut. For a bad loading this gives a marked
representative which is zero in the balanced tensor, with equality of the unmarked
diagrams already in the affine KLR algebra. Independence of marked representatives is
a different assertion.
-/
noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra MvPolynomial
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "Bs" => adjacentRow L M f β
local notation "X" => diagrams Q Λ Bs
local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "κ₀" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "p" => redIdem k Q Λ (ν := ν) κ₀
local notation "E₀" => orderedIdem Q Λ (fun _ => 1) Bs
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)

/-- Juxtaposition in the affine algebra, before projecting to global braided diagrams. -/
def affineStackBlocks : X →ₙₐ[k] R where
  toFun x := castKLR (stendhalQ Q Λ) h (juxtapose Q Λ Bs x)
  map_zero' := by simp only [map_zero]
  map_add' _ _ := by simp only [map_add]
  map_smul' _ _ := by simp only [map_smul, MonoidHom.id_apply]
  map_mul' _ _ := by simp only [juxtapose_mul, map_mul]

local notation "G" => affineStackBlocks Q Λ L M f β h

/-- Forget the cut, inserting the uncrossed projector but imposing no global ideal. -/
def crossingSeamStack : X ⊗[k] R →ₗ[k] R :=
  LinearMap.mul' k R ∘ₗ TensorProduct.map ((LinearMap.ofClass G).comp (LinearMap.mulRight k E₀)) LinearMap.id

local notation "stack" => crossingSeamStack Q Λ L M f β h

theorem crossingSeamStack_tmul (a : X) (b : R) : stack (a ⊗ₜ b) = G (a * E₀) * b := rfl

private theorem loading_mem_seam (s : Loadings Bs) (i : Seq μ) (hi : redWord i = κ₀) (y : R) :
    e (Seq.cast h (place Bs s)) * y * e i ∈ LinearMap.range stack := by
  let t := Seq.cast h (place Bs s)
  choose A D hw hx using exists_reduced_crossing_cut_affine Q Λ L M f β h s i hi
  let ρ := fun w => A w ++ D w
  apply (show Submodule.span k _ ≤ LinearMap.range stack from Submodule.span_le.2 ?_)
    (mem_span_corner' ρ hw i t (r := e t * y * e i) (by
      rw [← mul_assoc, ← mul_assoc, e_mul_self, mul_assoc _ (e i), e_mul_self]))
  rintro _ ⟨w,d,ht,rfl⟩
  obtain ⟨x,hx₀,hX⟩ := hx w ht
  refine ⟨x ⊗ₜ (ψw (D w) * pol (monomial d 1) * e i), ?_⟩
  rw [crossingSeamStack_tmul, hx₀, show G x = e t * ψw (A w) from hX]
  have H := e_mul_gen (Q := stendhalQ Q Λ) t (ρ w) (monomial d 1) i
  rw [(hw w).2, ← ht, inv_smul_smul, ite_eq_left rfl] at H
  simpa only [ht, ρ, ψw_append, mul_assoc] using H

private theorem unit_mem_loadingSpan : ∀ row, (1 : diagrams Q Λ row) ∈
    Submodule.span k (Set.range (loadingIdem Q Λ row))
  | [] => Submodule.subset_span ⟨PUnit.unit,rfl⟩
  | B :: row => by
    let l s := ofKLR k Q (Λ ∘ B.label) B.black (e s)
    have hs : ∑ s, l s = 1 := by dsimp [l]; rw [← map_sum, sum_e, map_one]
    change (1 : diagramAlgebra Q Λ B) ⊗ₜ (1 : diagrams Q Λ row) ∈ _
    rw [← hs, TensorProduct.sum_tmul]
    apply Submodule.sum_mem; intro s _
    let T := TensorProduct.mk k (diagramAlgebra Q Λ B) (diagrams Q Λ row) (l s)
    change (1 : diagrams Q Λ row) ∈ (Submodule.span k (Set.range (loadingIdem Q Λ (B :: row)))).comap T
    apply (Submodule.span_le.2 ?_) (unit_mem_loadingSpan row)
    rintro _ ⟨u,rfl⟩; exact Submodule.subset_span ⟨(s,u),rfl⟩

/-- **Uncrossed seam before quotienting** (Webster, proof of Lemma 6.8). The column with
juxtaposed top and uncrossed bottom is generated with an uncrossed marked seam, already
in the affine algebra, not only after restacking in the standard column. -/
theorem exists_crossingSeamStack (y : R) : ∃ u, stack u = G 1 * y * p := by
  let T := (LinearMap.mulRight k p).comp ((LinearMap.mulRight k y).comp (LinearMap.ofClass G))
  change (1 : X) ∈ (LinearMap.range stack).comap T
  apply (Submodule.span_le.2 ?_) (unit_mem_loadingSpan Q Λ Bs)
  rintro _ ⟨s,rfl⟩
  change G (loadingIdem Q Λ Bs s) * y * p ∈ LinearMap.range stack
  have hl : G (loadingIdem Q Λ Bs s) = e (Seq.cast h (place Bs s)) := by
    change castKLR _ h _ = _; rw [juxtapose_loadingIdem, castKLR_e]
  rw [hl, redIdem, Finset.mul_sum]
  exact Submodule.sum_mem _ fun i hi => loading_mem_seam Q Λ L M f β h s i (Finset.mem_filter.1 hi).2 y

theorem crossingSeamStack_mul_right (u : X ⊗[k] R) (z : R) :
    stack (TensorProduct.map LinearMap.id (LinearMap.mulRight k z) u) = stack u * z := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, add_mul, hu, hv]
  | tmul x y => exact (mul_assoc (G (x * E₀)) y z).symm

variable (hQ : KLRSymm Q)
local notation "D₀" => orderedProduct Q Λ (fun _ => 1) Bs
local notation "D₁" => orderedProduct Q Λ (fun _ => Fin.revPerm) Bs
local notation "S₀" => orderedColumn Q Λ hQ (fun _ => 1) L M f β h
local notation "C" => crossingProduct Q Λ hQ M f β L
local notation "Z" => BalancedTensor k D₁ D₀ (BlockCut.space C) S₀
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1)
  (fun r i => boundaryCount (cut (f 0) (f 1) r) i Bs) κ₀
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)

/-- Send affine marked representatives to the ordinary balanced tensor. -/
def crossingSeamClass : X ⊗[k] R →ₗ[k] Z :=
  crossingCut Q Λ hQ L M f β h ∘ₗ TensorProduct.map LinearMap.id (π).toLinearMap

local notation "cl" => crossingSeamClass Q Λ L M f β h hQ

private theorem seamClass_mul_zero (u : X ⊗[k] R) (v : R) (hv : q (π v) = 0) :
    cl (TensorProduct.map LinearMap.id (LinearMap.mulRight k v) u) = 0 := by
  let g := (cl).comp (TensorProduct.map LinearMap.id (LinearMap.mulRight k v))
  change g u = 0
  induction u using TensorProduct.inductionOn with
  | add u w hu hw => exact (map_add g u w).trans (by rw [hu, hw, add_zero])
  | tmul x y =>
    change crossingCut Q Λ hQ L M f β h (x ⊗ₜ π (y*v)) = 0
    rw [crossingCut_tmul]
    have H : orderedColumnRep Q Λ hQ L M f β h (fun _ => 1) (π (y*v)) = 0 := by
      apply Subtype.ext; apply Subtype.ext
      rw [orderedColumnRep_val]
      change q (_ * (π (y*v) * _)) = 0
      rw [map_mul π, map_mul (q), map_mul (q), map_mul (q), hv, mul_zero, zero_mul, mul_zero]
    rw [H, BalancedTensor.tmul_zero]

/-- **Interior relations in the uncrossed order have zero marked lifts** (Webster,
arXiv:1309.3796v2, proof of Lemma 6.8). The lower tail `z` is arbitrary. More generally
`v` may be any killed element supported on the left in the uncrossed order. The witness
is a sum of cuts of the same affine diagram, not a preimage merely after quotienting. -/
theorem exists_zero_crossingSeamClass (v : R) (ho : p * v = v) (hv : q (π v) = 0) (y z : R) :
    ∃ u, stack u = G 1 * y * v * z ∧ cl u = 0 := by
  obtain ⟨t,ht⟩ := exists_crossingSeamStack Q Λ L M f β h y
  refine ⟨TensorProduct.map LinearMap.id (LinearMap.mulRight k (v*z)) t, ?_, ?_⟩
  · rw [crossingSeamStack_mul_right, ht, mul_assoc _ p, ← mul_assoc p, ho]; simp only [mul_assoc]
  · apply seamClass_mul_zero; rw [map_mul π, map_mul (q), hv, zero_mul]

end Categorification.Stendhal.RedBlock
