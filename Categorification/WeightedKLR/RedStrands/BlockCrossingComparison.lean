/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingRelations
import Categorification.WeightedKLR.RedStrands.BlockCrossingOrder
import Categorification.WeightedKLR.RedStrands.BlockCrossingCoordinates

/-!
# The ordinary crossing comparison

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8, naive tensor products. Parabolic PBW
coordinates read a marked affine stack independently of its marking: on separated
representatives the coordinates of the lower part can be put in the ordered corner
and slid through the seam by balancing. Lifting the interior ideal then proves
injectivity of the existing stacking map on the quotient. This is not the injectivity
of the map out of the tensor of the kernel in (6.21).
-/
noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA BraidedStendhalAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)
local notation "topOrd" => (fun (_ : RedBlock I ℓ) => Fin.revPerm)

private theorem lift_diagonal : ∀ row (x : diagrams Q Λ row), ∃ d,
    orderedInclusion Q Λ hQ botOrd row d = projection Q Λ row
      (orderedIdem Q Λ botOrd row * x * orderedIdem Q Λ botOrd row)
  | [], x => ⟨_,rfl⟩
  | B :: row, x => by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨u,hu⟩ := hx; obtain ⟨v,hv⟩ := hy
      exact ⟨u+v, by simp only [map_add, mul_add, add_mul, hu, hv]⟩
    | tmul x y =>
      obtain ⟨d,hd⟩ := lift_diagonal row y
      refine ⟨orderedRetraction Q Λ hQ botOrd B (violMk _ _ _ _ x) ⊗ₜ d, ?_⟩
      change TensorProduct.map _ _ (_ ⊗ₜ[k] d) = projection Q Λ (B::row) _
      rw [TensorProduct.map_tmul, orderedIdem, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, projection, Algebra.TensorProduct.map_tmul]
      change orderedValue Q Λ hQ botOrd B _ ⊗ₜ orderedInclusion Q Λ hQ botOrd row d = _
      rw [hd, orderedValue_retraction, orderedValue_one]; simp only [map_mul]

variable (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "row" => adjacentRow L M f β
local notation "X" => diagrams Q Λ row
local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "κ" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "p" => redIdem k Q Λ (ν := ν) κ
local notation "G" => affineStackBlocks Q Λ L M f β h
local notation "E₀" => orderedIdem Q Λ botOrd row
local notation "E₁" => orderedIdem Q Λ topOrd row
local notation "P" => projection Q Λ row
local notation "raw" => ofKLR k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "π" => AlgHom.comp mk raw
local notation "C" => crossingProduct Q Λ hQ M f β L
local notation "rep" => orderedColumnRep Q Λ hQ L M f β h botOrd
local notation "cl" => crossingSeamClass Q Λ L M f β h hQ
local notation "stk" => crossingStack Q Λ hQ L M f β h
local notation "mult" => crossingBoundaryStack Q Λ L M f β h
local notation "S₀" => orderedColumn Q Λ hQ botOrd L M f β h
local notation "Z" => BalancedTensor k (orderedProduct Q Λ topOrd row) (orderedProduct Q Λ botOrd row) (BlockCut.space C) S₀

local instance columnAddGroup (σ : (B : RedBlock I ℓ) → Equiv.Perm (Fin B.size)) :
    AddCommGroup (orderedColumn Q Λ hQ σ L M f β h) := Submodule.addCommGroup _

private theorem order_idem (σ) : ∀ Bs, IsIdempotentElem (orderedIdem Q Λ σ Bs)
  | [] => one_mul _
  | _ :: Bs => by
    change (_ ⊗ₜ[k] _) * (_ ⊗ₜ[k] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, (isIdempotentElem_redProj _).eq, (order_idem σ Bs).eq]; rfl

private theorem slide_coefficient (x c : X) (w : R) :
    cl ((E₁*x*E₀*c) ⊗ₜ w) = cl (x ⊗ₜ (G (E₀*c*E₀) * w)) := by
  let a := E₀*c*E₀
  obtain ⟨d,hd⟩ := lift_diagonal Q Λ hQ row c
  have hs := crossingCut_slide Q Λ hQ L M f β h x a d hd.symm (π w)
  change crossingCut Q Λ hQ L M f β h (_ ⊗ₜ π w) = crossingCut Q Λ hQ L M f β h (_ ⊗ₜ π (_ * w))
  rw [map_mul π]; refine Eq.trans ?_ hs
  rw [crossingCut_tmul, crossingCut_tmul]; congr 1
  apply (C).incl_injective
  rw [(C).incl_cut, (C).incl_cut, orderedInclusion_one, orderedInclusion_one]
  simp only [← map_mul, a]
  apply congrArg P
  have h₁ := (order_idem Q Λ topOrd row).eq
  have h₀ (v : X) : v * E₀ * E₀ = v * E₀ := by rw [mul_assoc, (order_idem Q Λ botOrd row).eq]
  simp only [LinearMap.id_apply, ← mul_assoc, h₁, h₀]

private theorem rep_normalize (y : R) : rep (π (G 1 * (y*p))) = rep (π y) := by
  apply Subtype.ext; apply Subtype.ext; rw [orderedColumnRep_val, orderedColumnRep_val]
  congr 1
  change π (G E₀) * (π (G 1 * (y*p)) * π p) = π (G E₀) * (π y * π p)
  simp only [← map_mul π, ← mul_assoc, ← map_mul G, mul_one]
  rw [mul_assoc _ p p, redIdem_mul_redIdem]

private theorem rep_coefficient (c : X) (w : R) :
    rep (π (G c*w)) = rep (π (G (E₀*c*E₀)*w)) := by
  apply Subtype.ext; apply Subtype.ext; rw [orderedColumnRep_val, orderedColumnRep_val]
  apply congrArg; change π (G E₀) * (π (G c*w) * π p) = π (G E₀) * (π (G (E₀*c*E₀)*w) * π p)
  simp only [← map_mul π, ← mul_assoc, ← map_mul G, (order_idem Q Λ botOrd row).eq]
  exact congrArg (mk) (insert_uncrossed_order Q Λ L M f β h hQ c w)

private theorem rebuild_lower {n : ℕ} (x : X) (y : R) (a : Fin n → X) (w : Fin n → R)
    (hw : raw (G 1 * (y*p)) = ∑ j, raw (G (a j) * w j)) :
    (∑ i, cl (x ⊗ₜ (G (E₀*a i*E₀)*w i))) = cl (x ⊗ₜ y) := by
  let b := ((BalancedTensor.mk k (orderedProduct Q Λ topOrd row) (orderedProduct Q Λ botOrd row)
    (BlockCut.space C) S₀).restrictScalars k).comp (TensorProduct.mk k _ S₀ ((C).cut (P x)))
  have he := congrArg (fun z => rep (mk z)) hw
  change rep (π (G 1*(y*p))) = rep (mk (∑ i, raw (G (a i)*w i))) at he
  rw [rep_normalize, map_sum (mk), map_sum (rep)] at he
  have hh (i : Fin n) : rep (mk (raw (G (a i)*w i))) = rep (π (G (E₀*a i*E₀)*w i)) :=
    rep_coefficient Q Λ hQ L M f β h _ _
  exact (map_sum b _ _).symm.trans (congrArg b (he.trans (Finset.sum_congr rfl fun i _ => hh i)).symm)

private theorem read_marking : ∃ cut : R →ₗ[k] Z, ∀ t : X ⊗[k] R, cut (mult t) = cl t := by
  classical
  obtain ⟨n,g,w,hg,hw⟩ := exists_blockStack_coordinates Q Λ hQ L M f β h
  let piece (i : Fin n) := (cl).comp (((TensorProduct.mk k X R).flip (w i)).comp (g i))
  let cut := ∑ j, piece j
  refine ⟨cut,fun t => LinearMap.congr_fun (f := cut.comp mult) (g := cl) ?_ t⟩
  apply TensorProduct.ext'; intro x y
  change cut (mult (x ⊗ₜ y)) = cl (x ⊗ₜ y)
  have stack_eq : mult (x ⊗ₜ y) = G (E₁*x*E₀) * (y*p) := by
    change G E₁ * ((G (x*E₀)*y)*p) = _
    simp only [map_mul, mul_assoc]
  have atcut : cut (mult (x ⊗ₜ y)) = ∑ i, cl (x ⊗ₜ (G (E₀*g i (y*p)*E₀)*w i)) := by
    rw [stack_eq]; change (∑ j, piece j) _ = _; rw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl; intro i _
    change cl (g i _ ⊗ₜ w i) = _
    rw [hg]; exact slide_coefficient Q Λ hQ L M f β h x _ _
  rw [atcut]
  exact rebuild_lower Q Λ hQ L M f β h x y (fun i => g i (y*p)) w (hw (y*p))

/-- **Injectivity of ordinary stacking** (Webster, arXiv:1309.3796v2, §6.1, ordinary
comparison in Lemma 6.8). Equal exchanged-top classes have equal balanced classes. -/
theorem crossingStack_injective : Function.Injective stk := by
  apply (LinearMap.ker_eq_bot (f := (stk).restrictScalars k)).1
  rw [ker_crossingStack_eq_map_ker_boundaryStack, eq_bot_iff]
  rintro _ ⟨t,ht,rfl⟩
  obtain ⟨cut,hc⟩ := read_marking Q Λ hQ L M f β h
  exact (hc t).symm.trans ((congrArg cut (show mult t = 0 from ht)).trans (map_zero cut))

/-- **Ordinary comparison of Lemma 6.8** (Webster v2, §6.1): the equivalence is stacking
on the local crossing tensor the uncrossed standardization column, not an independently
chosen isomorphism. Its right-corner compatibility is `crossingStack_right`. -/
noncomputable def crossingStackEquiv := LinearEquiv.ofBijective (stk)
  ⟨crossingStack_injective Q Λ hQ L M f β h, crossingStack_surjective Q Λ hQ L M f β h⟩

/-- The adapted diagram cut descends through the entire standard column: its value on
any representative is the inverse comparison on its projected class. -/
theorem crossingDiagramCut_eq_inverse (y : BraidedStendhalAlgebra k Q Λ ν) :
    crossingDiagramCut Q Λ hQ L M f β h y = (crossingStackEquiv Q Λ hQ L M f β h).symm
      (orderedColumnRep Q Λ hQ L M f β h topOrd (mk y)) := by
  apply crossingStack_injective Q Λ hQ L M f β h
  exact (crossingStack_diagramCut Q Λ hQ L M f β h y).trans
    ((crossingStackEquiv Q Λ hQ L M f β h).apply_symm_apply _).symm

end Categorification.Stendhal.RedBlock
