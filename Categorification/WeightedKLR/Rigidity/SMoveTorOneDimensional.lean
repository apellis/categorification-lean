/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalTorZeroCorner

/-!
# Proposition 7.22 (c): the S-move Tor is one-dimensional in degree `-|ν|`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c). For the resolutions of `L` and `L'` as in Proposition 7.8 the
S-move Tor `(SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L'` is concentrated in degree `-|ν|`, where
it is the `Tor₀` of the diagonal pair `((SMove.leftStd M_0)^r, SMove.rightStd S(T^{λ_1} e(t) ⊠
Y₀))` (`SMove.exists_stdSum_derivedTensorHomology_concentrated` and its proof). That `Tor₀` is
the ordinary tensor product (`ambientDerivedTensorH0Equiv`), of dimension `dim e(s) W / |J|`
with `W = SMove.leftStd M_0` and `s = (red₁ red₂ 𝐮' red₃)`
(`SMove.card_mul_finrank_tensorProductOver_diagonal`,
`SMove.finrank_tensorProductOver_reflectOne_leftStd_leftStandard`), and
`dim e(s) SMove.leftStd M_0 = dim e(s) SMove.leftStd L`
(`SMove.finrank_fixSub_leftStd_stdResolution_zero`). Under the normalization
`dim e(s) SMove.leftStd L = |J|` the S-move Tor is `k` in degree `-|ν|`.

## Main results

* `SMove.nonempty_addEquiv_derivedTensorHomology_zero_of_finrank_eq_one`.
* `SMove.derivedTensorHomology_reflect_leftStd_rightStd_one_dimensional`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits Abelian KLR Equiv MulOpposite BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w v

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + 1 + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)

local notation "Λ₃" => (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1) : Fin (1 + 1 + 1) → I →₀ ℕ)
local notation "T₃" => TensorProductAlgebra k Q Λ₃ ν

/-- **A one-dimensional `Tor₀`**: if `dim_k (W^r ⊗_T Y) = 1`, the degree-zero cohomology of
`W^r ⊗ᴸ Y` over `ℤ` is additively `k` (stated at any index `m = 0`). -/
theorem nonempty_addEquiv_derivedTensorHomology_zero_of_finrank_eq_one
    [HasDerivedCategory.{w, 0} T₃] [HasDerivedCategory.{w, 0} ℤ] (W Y : ModuleCat.{0} T₃)
    (h : Module.finrank k (TensorProductOver T₃ ((reflectOne Q Λ₃ hQ hρ).obj W) Y) = 1)
    (m : ℤ) (hm : m = 0) :
    Nonempty ((homologyFunctor (A := ℤ) ℤ m).obj ((derivedTensor.{w} ℤ T₃
        ((reflectOne Q Λ₃ hQ hρ).obj W)).obj
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj Y))) ≃+ k) := by
  subst hm
  have : Module.Finite k (TensorProductOver T₃ ((reflectOne Q Λ₃ hQ hρ).obj W) Y) :=
    Module.finite_of_finrank_eq_succ h
  let e₁ := ambientDerivedTensorH0Equiv (k := ℤ) (A := T₃)
    (N := (reflectOne Q Λ₃ hQ hρ).obj W) Y
  let e₂ := LinearEquiv.ofFinrankEq (R := k)
    (TensorProductOver T₃ ((reflectOne Q Λ₃ hQ hρ).obj W) Y) k
    (h.trans (Module.finrank_self k).symm)
  exact ⟨e₁.toAddEquiv.trans e₂.toAddEquiv⟩

/-- `SMove.leftStd N` as a module over `T^{λ_1, λ_2, λ_3}(ν)` with the labels `Λ₃` of the
assembly. -/
def leftStdThree (N : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν)) :
    ModuleCat.{0} T₃ :=
  (leftStd Q hQ Λ ν).obj N

/-- The loading corners of `leftStdThree N` and of `SMove.leftStd N` agree. -/
def fixSubLeftStdThreeEquiv (N : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν))
    (s : Seq (stendhalWeight (1 + 1 + 1) ν)) (hs : IsRedOrdered s) :
    fixSub k (leftStdThree Q hQ Λ N) (seqIdem Q Λ₃ s hs) ≃ₗ[k]
      fixSub k ((leftStd Q hQ Λ ν).obj N) (seqIdem Q Λ s hs) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (ν := ν)
      (List.map (1 : Perm (Fin (1 + 1 + 1))) (List.finRange (1 + 1 + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)]
  [HasDerivedCategory.{w, 0} ℤ]
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν))]
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q
    ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) ν))]

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

include hρ in
/-- **Proposition 7.22 (c): the S-move Tor is `k` in degree `-|ν|` and zero elsewhere**
(Webster, arXiv:1309.3796v3, §7.3, Proposition 7.22, gap (c) of its proof). Let `L` over
`T^{λ_2, λ_3}(ν)` and `L'` over `T^{λ_1, λ_2}(ν)` be finite-dimensional and killed by every
loading idempotent with a black strand right of the last red strand, and let `L'` satisfy the
hypotheses of the second clause of Proposition 7.8 (`exists_stdResolution_last`: last term
`S(T^{λ_1} e(t) ⊠ Y₀)`, `R^{λ_2} e(𝐮) ≅ Y₀^{⊕ J}`, `htop`). If
`dim e(s) SMove.leftStd L = |J|` for the diagonal loading `s = (red₁ red₂ 𝐮' red₃)`, then
`H^{-|ν|}((SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L') ≅ k` and `H^n = 0` for `n ≠ -|ν|`.

Comparison with Webster v3, Proposition 7.22, hypothesis by hypothesis:
* Webster's statement is graded (Tor concentrated in degree `-|ν|`, one-dimensional there, in
  internal degree zero); here it is ungraded: the cohomological degree `-|ν|` and the
  dimension are proved, the internal grading is not tracked.
* Webster's Tor is over `𝕜`; here the derived tensor product is taken in `ℤ`-modules and the
  degree `-|ν|` term is identified with `k` additively (it is the ordinary tensor product of
  `k`-dimension one, `nonempty_addEquiv_derivedTensorHomology_zero_of_finrank_eq_one`).
* The two sides are the evaluation/coevaluation modules `L`, `L'` of the S-move in the general
  form above (any `L`, `L'` killed after the last red strand, as in Proposition 7.8).
* Route hypotheses: a Rouquier choice of `Q` (Webster allows any `Q` with his
  nondegeneracy hypotheses), and the normalization `hnorm`, the expanded-word form of
  Webster's normalization that the divided-power idempotent `e(𝐢_λ)` has one-dimensional image
  in the coevaluation head; it is to be discharged by `e(s) SMove.leftStd L ≅ e(red₂ 𝐮' red₃) L`
  (`emptyLeftStdCornerEquiv`) and the count for `L` the coevaluation head at `dualHighest`. -/
theorem derivedTensorHomology_reflect_leftStd_rightStd_one_dimensional
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (L : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν)) [FiniteDimensional k L]
    (hL : ∀ (s : Seq (stendhalWeight (1 + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : L, loadingIdem Q (Λ ∘ Fin.natAdd 1) s hs • x = 0)
    (L' : ModuleCat.{0} (TensorProductAlgebra k Q (rightLabels Λ) ν))
    [FiniteDimensional k L']
    (hL' : ∀ (s : Seq (stendhalWeight (1 + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : L', loadingIdem Q (rightLabels Λ) s hs • x = 0)
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight 1 0)) (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q ((rightLabels Λ) ∘ Fin.castSucc) 0
      (StendhalAlgebra.e t ht) = 1)
    (Y₀ : ModuleCat.{0} (rightCyc Q Λ (wordWt u 0)))
    (hss : ∀ (M : Type) [AddCommGroup M] [Module (rightCyc Q Λ (wordWt u 0)) M]
      [Module.Finite (rightCyc Q Λ (wordWt u 0)) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[rightCyc Q Λ (wordWt u 0)] (Fin n → Y₀)))
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (ι : J → (Y₀ →ₗ[rightCyc Q Λ (wordWt u 0)] cycWord Q (rightLabels Λ) u))
    (π : J → (cycWord Q (rightLabels Λ) u →ₗ[rightCyc Q Λ (wordWt u 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id)
    (htop : Module.finrank k (Ext.{v}
      (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht) Y₀) L'
      (Multiset.card ν)) = 1)
    (hnorm : Module.finrank k (fixSub k ((leftStd Q hQ Λ ν).obj L)
      (seqIdem Q Λ (diagonalTwoPiece (diagonalInnerLoading u h₀ t ht)).1
        (diagonalTwoPiece (diagonalInnerLoading u h₀ t ht)).2)) = Fintype.card J) :
    Nonempty ((homologyFunctor (A := ℤ) ℤ (-(Multiset.card ν : ℤ))).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj L))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj L')))) ≃+ k) ∧
      ∀ n : ℤ, n ≠ -(Multiset.card ν : ℤ) → IsZero ((homologyFunctor (A := ℤ) ℤ (n)).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)
          ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
            ((leftStd Q hQ Λ ν).obj L))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj L'))))) := by
  obtain ⟨-, -, -, hconc⟩ := exists_stdSum_derivedTensorHomology_concentrated.{w, v} Q hQ Λ hρ
    hR L hL L' hL' u h₀ t ht het Y₀ hss ι π hιπ htot htop
  refine ⟨?_, hconc⟩
  have hall : AllFiniteDeltaInjective Q (Λ ∘ Fin.natAdd 1) hQ := by
    convert allFiniteDeltaInjective_of_rouquier hR hQ
  have hall' : AllFiniteDeltaInjective Q (rightLabels Λ) hQ := by
    convert allFiniteDeltaInjective_of_rouquier hR hQ
  obtain ⟨S, h0, hs, hS, hstd, hz⟩ :=
    exists_stdResolution.{v} Q (Λ ∘ Fin.natAdd 1) hQ hR hall L hL
  obtain ⟨S', h0', hs', hS', hstd', hz', ⟨eN⟩, -⟩ :=
    exists_stdResolution_last.{v} Q (rightLabels Λ) hQ hR hall' L' hL'
      u h₀ t ht het Y₀ hss ι π hιπ htot htop
  have hn : -(Multiset.card ν : ℤ) + Multiset.card ν = 0 := by omega
  have hdev := nonempty_linearEquiv_derivedTensorHomology_reflect_leftStd_rightStd.{w} Q hQ Λ
    hρ S h0 hs hS hstd hz S' h0' hs' hS' hstd' hz' hR (-(Multiset.card ν : ℤ))
  obtain ⟨e⟩ := hdev
  let X := oldProj Q (rightLabels Λ) 0 t ht
  let W := leftStdThree Q hQ Λ (S 0).X₂
  let Y : ModuleCat.{0} T₃ := (rightStd Q hQ Λ₃ ν).obj (tensorStd Q (rightLabels Λ) hQ h₀ X Y₀)
  let d := diagonalInnerLoading u h₀ t ht
  have hlast := fun i => blackCount_twoPieceLabel_last (add_zero ν) default d i
  have hcount := card_mul_finrank_tensorProductOver_diagonal Q hQ Λ hρ u h₀ t ht Y₀ ι π hιπ
    htot W
  have hgen := finrank_tensorProductOver_reflectOne_leftStandard (ℓ := 1 + 1) Q hQ Λ₃ hρ W
    (diagonalTwoPiece d).1 (diagonalTwoPiece d).2 fun t' ht' hst w =>
      seqIdem_smul_leftStd_eq_zero_of_stendhalLT Q hQ Λ ν (S 0).X₂ (diagonalTwoPiece d).1
        hlast t' ht' hst w
  have hfix := hgen.trans (((fixSubLeftStdThreeEquiv Q hQ Λ (S 0).X₂ (diagonalTwoPiece d).1
    (diagonalTwoPiece d).2).finrank_eq.trans
    (finrank_fixSub_leftStd_stdResolution_zero Q hQ Λ S h0 hs hS hstd hz d)).trans hnorm)
  have hone := Nat.eq_of_mul_eq_mul_left (Fintype.card_pos (α := J))
    ((hcount.trans hfix).trans (mul_one _).symm)
  obtain ⟨f⟩ := nonempty_addEquiv_derivedTensorHomology_zero_of_finrank_eq_one.{w} Q hQ Λ hρ W Y
    hone _ hn
  let g := (homologyFunctor (A := ℤ) ℤ (-(Multiset.card ν : ℤ) + Multiset.card ν)).mapIso
    ((derivedTensor.{w} ℤ T₃ ((reflectOne Q Λ₃ hQ hρ).obj W)).mapIso (DG.DerivedCategory.Q.mapIso
      ((degreeZeroModuleFunctor _).mapIso ((rightStd Q hQ Λ₃ ν).mapIso eN))))
  exact ⟨e.toAddEquiv.trans (g.toLinearEquiv.toAddEquiv.trans f)⟩

end Categorification.Stendhal.SMove
