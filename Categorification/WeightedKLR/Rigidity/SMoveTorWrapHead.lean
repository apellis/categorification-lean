/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalOuterCorner
import Categorification.WeightedKLR.Rigidity.SMoveWrapHeadCorner
import Categorification.WeightedKLR.Rigidity.RigidityExtCoevaluationLast

/-!
# Proposition 7.22 (c) with the head of the wrap projective on the left

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c). In the S-move, the module `L` over the last two red strands is the
head of the wrap projective of a divided word `d` (for the coevaluation word of Definition 7.1 at
the dual weight, the coevaluation head of Lemma 7.3). Its diagonal corner is

  `dim e(red₁ red₂ 𝐮' red₃) SMove.leftStd L = dim e(red₂ d̂ red₃) L = ∏ nₐ!`

for `𝐮 = d̂.reverse` (`SMove.finrank_fixSub_leftStd_diagonalTwoPiece`,
`SMove.diagonalOuterLoading_reverse_eq_wrap`, `finrank_fixedSubspace_flipLeft_wrapHead_wrap`).
When the summand decomposition `R^{λ_2} e(𝐮) ≅ Y₀^{⊕ J}` of the other side has `|J| = ∏ nₐ!`
(the case of the coevaluation side, `exists_bicone_cycWord_cycDivProj`, with `nₐ` the exponents
of the reversed word), this is the normalization `hnorm` of
`SMove.derivedTensorHomology_reflect_leftStd_rightStd_one_dimensional`, which therefore drops
out: `SMove.derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional`.

## Main results

* `SMove.diagonalOuterLoading_reverse_eq_wrap`.
* `SMove.finrank_fixSub_flipLeft_wrapHead_diagonalOuterLoading`.
* `SMove.derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits Abelian KLR KLRAlgebra Equiv MulOpposite
open BraidedStendhalAlgebra TwoRedErase
open DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w v

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) (d : List (I × ℕ))

local notation "νᵈ" => (expandDiv d : Multiset I)
local notation "Λ₂₃" => (Λ ∘ Fin.natAdd 1 : Fin (1 + 1) → I →₀ ℕ)
local notation "z₀" => CycKLR.mk k Q (fun i => Polynomial.X ^ (Λ ∘ Fin.natAdd 1 :
  Fin (1 + 1) → I →₀ ℕ) 0 i) (expandDiv d : Multiset I)
  (hflip (divIdem (KLRAlgebra.Seq.ofList (expandDiv d) rfl) (blocksDiv d 0)))

omit [DecidableEq I] in
/-- **The outer diagonal loading is the expanded wrap loading**: for `𝐮 = d̂.reverse`,
`(red₂ 𝐮' red₃) = (red₂ d̂ red₃)`. -/
theorem diagonalOuterLoading_reverse_eq_wrap
    (h₀ : 0 + wordWt (expandDiv d).reverse 0 = νᵈ) :
    diagonalOuterLoading (expandDiv d).reverse h₀ =
      wrap νᵈ (KLRAlgebra.Seq.ofList (expandDiv d) rfl) := by
  apply Seq.word_injective
  rw [word_wrap, diagonalOuterLoading, seqWord_appendRedLoading, Seq.word_cast,
    SingleRed.insertWord, Seq.word_cast, Seq.word_append, Seq.word_map,
    Seq.word_singleton, Seq.word_ofList, Seq.word_ofList, List.reverse_reverse]
  simp [addRedColor]

/-- **The diagonal corner of the head of the wrap projective**: for `L` the head of the wrap
projective of `d` over the last two red strands and `𝐮 = d̂.reverse`,
`dim e(red₂ 𝐮' red₃) L = ∏ nₐ!`, under the hypotheses of Lemma 7.3 as in
`finrank_fixedSubspace_flipLeft_wrapHead_wrap`. -/
theorem finrank_fixSub_flipLeft_wrapHead_diagonalOuterLoading
    (hR : LastDotRelation Q Λ₂₃ νᵈ) (hne : z₀ ≠ 0)
    (hgen : ∀ y : CycKLR k Q (fun i => Polynomial.X ^ Λ₂₃ 0 i) νᵈ, z₀ * y = y → y ≠ 0 →
      ∃ c, y * c = z₀)
    (hscalar : ∀ x : CycKLR k Q (fun i => Polynomial.X ^ Λ₂₃ 0 i) νᵈ, z₀ * x * z₀ = x →
      ∃ c : k, x = c • z₀)
    (h₀ : 0 + wordWt (expandDiv d).reverse 0 = νᵈ) :
    Module.finrank k (fixSub k
      (flipLeft Q Λ₂₃ νᵈ (rIdeal (wrapIdem Q Λ₂₃ νᵈ z₀) ⧸ coevaluationTrace (cutIdem Q Λ₂₃ νᵈ)))
      (tensorLoad Q Λ₂₃ νᵈ (diagonalOuterLoading (expandDiv d).reverse h₀))) =
      (d.map fun q => q.2.factorial).prod := by
  rw [diagonalOuterLoading_reverse_eq_wrap d h₀,
    tensorLoad_eq_seqIdem Q Λ₂₃ νᵈ _ (wrap_ordered νᵈ _)]
  exact finrank_fixedSubspace_flipLeft_wrapHead_wrap Q Λ₂₃ d hR hne hgen hscalar

local notation "Λ₃" => (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1) : Fin (1 + 1 + 1) → I →₀ ℕ)

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + 1 + 1) (expandDiv d : Multiset I)))) →
    List ℕ} (hρ : TypeA.IsReducedChoice ρ)

variable [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
      (ν := (expandDiv d : Multiset I))
      (List.map (1 : Perm (Fin (1 + 1 + 1))) (List.finRange (1 + 1 + 1))))]
  [HasDerivedCategory.{w, 0}
    (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (expandDiv d : Multiset I))]
  [HasDerivedCategory.{w, 0} ℤ]
  [HasExt.{v} (ModuleCat.{0}
    (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) (expandDiv d : Multiset I)))]
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q
    ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) (expandDiv d : Multiset I)))]

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

include hρ in
/-- **Proposition 7.22 (c) with the head of the wrap projective on the left** (Webster,
arXiv:1309.3796v3, §7.3, Proposition 7.22, gap (c) of its proof): the S-move Tor
`(SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L'` is `k` in degree `-|ν|` and zero elsewhere, where
`L` is the head of the wrap projective of the divided word `d` over the last two red strands
(the coevaluation head of Lemma 7.3 when `d` is the coevaluation word at the dual weight), and
`L'` is a module over the first two red strands satisfying the hypotheses of the second clause
of Proposition 7.8 for the word `𝐮 = d̂.reverse`.

Comparison with Webster v3, Proposition 7.22, hypothesis by hypothesis:
* Webster's statement is graded; here it is ungraded, with Tor over `ℤ` and the degree `-|ν|`
  term identified with `k` additively (as in
  `derivedTensorHomology_reflect_leftStd_rightStd_one_dimensional`).
* Webster's `L` is the simple coevaluation head at `λ*`. Here `L` is the head of the wrap
  projective of `d`, under the hypotheses of Lemma 7.3 in the form used by
  `finrank_ext_standard_cycDivProj_wrapHead`: the cyclotomic relation of the third red strand
  on the last black strand (`hRX`), and `z₀ R z₀ = k z₀` with every nonzero element of `z₀ R`
  generating `z₀` (`hne`, `hgen`, `hscalar`). For the coevaluation word these are proved in
  `finrank_ext_standard_coevaluationHead` from Proposition 7.2 and Theorem 5.2.
* Webster's `L'` is the coevaluation head at `λ`. Here `L'` is any module killed after the last
  red strand with the hypotheses of the second clause of Proposition 7.8
  (`exists_stdResolution_last`: `R^{λ_2} e(𝐮) ≅ Y₀^{⊕ J}`, `hss`, `htop`), together with
  `hJ : |J| = ∏ nₐ!`. For the coevaluation head these hold with `Y₀ = cycDivProj` of the
  reversed word (`exists_bicone_cycWord_cycDivProj`, `exists_stdResolution_coevaluationHead`,
  `finrank_ext_standard_coevaluationHead`); `hJ` and `htop` are the two forms of the
  expanded-word normalization, on the two sides of the S-move.
* Route hypothesis: a Rouquier choice of `Q` (Webster allows any `Q` with his nondegeneracy
  hypotheses). The normalization `hnorm` of the general form is discharged
  (`finrank_fixSub_leftStd_diagonalTwoPiece`,
  `finrank_fixSub_flipLeft_wrapHead_diagonalOuterLoading`). -/
theorem derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    (hRX : LastDotRelation Q Λ₂₃ νᵈ) (hne : z₀ ≠ 0)
    (hgen : ∀ y : CycKLR k Q (fun i => Polynomial.X ^ Λ₂₃ 0 i) νᵈ, z₀ * y = y → y ≠ 0 →
      ∃ c, y * c = z₀)
    (hscalar : ∀ x : CycKLR k Q (fun i => Polynomial.X ^ Λ₂₃ 0 i) νᵈ, z₀ * x * z₀ = x →
      ∃ c : k, x = c • z₀)
    (L' : ModuleCat.{0} (TensorProductAlgebra k Q (rightLabels Λ) νᵈ))
    [FiniteDimensional k L']
    (hL' : ∀ (s : Seq (stendhalWeight (1 + 1) νᵈ)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : L', loadingIdem Q (rightLabels Λ) s hs • x = 0)
    (h₀ : 0 + wordWt (expandDiv d).reverse 0 = νᵈ) (t : Seq (stendhalWeight 1 0))
    (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q ((rightLabels Λ) ∘ Fin.castSucc) 0
      (StendhalAlgebra.e t ht) = 1)
    (Y₀ : ModuleCat.{0} (rightCyc Q Λ (wordWt (expandDiv d).reverse 0)))
    (hss : ∀ (M : Type) [AddCommGroup M] [Module (rightCyc Q Λ (wordWt (expandDiv d).reverse 0)) M]
      [Module.Finite (rightCyc Q Λ (wordWt (expandDiv d).reverse 0)) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[rightCyc Q Λ (wordWt (expandDiv d).reverse 0)] (Fin n → Y₀)))
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (ι : J → (Y₀ →ₗ[rightCyc Q Λ (wordWt (expandDiv d).reverse 0)]
      cycWord Q (rightLabels Λ) (expandDiv d).reverse))
    (π : J → (cycWord Q (rightLabels Λ) (expandDiv d).reverse →ₗ[rightCyc Q Λ
      (wordWt (expandDiv d).reverse 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id)
    (htop : Module.finrank k (Ext.{v}
      (tensorStd Q (rightLabels Λ) hQ h₀ (oldProj Q (rightLabels Λ) 0 t ht) Y₀) L'
      (Multiset.card νᵈ)) = 1)
    (hJ : Fintype.card J = (d.map fun q => q.2.factorial).prod) :
    Nonempty ((homologyFunctor (A := ℤ) ℤ (-(Multiset.card νᵈ : ℤ))).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ₃ νᵈ)
          ((reflectOne Q Λ₃ hQ hρ).obj ((leftStd Q hQ Λ νᵈ).obj
            (flipLeft Q Λ₂₃ νᵈ (rIdeal (wrapIdem Q Λ₂₃ νᵈ z₀) ⧸
              coevaluationTrace (cutIdem Q Λ₂₃ νᵈ)))))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ Λ₃ νᵈ).obj L')))) ≃+ k) ∧
      ∀ n : ℤ, n ≠ -(Multiset.card νᵈ : ℤ) → IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
        ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ₃ νᵈ)
          ((reflectOne Q Λ₃ hQ hρ).obj ((leftStd Q hQ Λ νᵈ).obj
            (flipLeft Q Λ₂₃ νᵈ (rIdeal (wrapIdem Q Λ₂₃ νᵈ z₀) ⧸
              coevaluationTrace (cutIdem Q Λ₂₃ νᵈ)))))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ Λ₃ νᵈ).obj L'))))) := by
  have hz₀ := isIdempotentElem_wrapHeadIdem Q Λ₂₃ d
  have hz : IsIdempotentElem (wrapIdem Q Λ₂₃ νᵈ z₀) :=
    (wrapIdem_mul Q Λ₂₃ _ _ _).trans (congrArg _ hz₀.eq)
  have := tensorProductAlgebra_finite Λ₂₃ νᵈ hR
  have := finiteDimensional_flipLeft_quotient Q Λ₂₃ νᵈ hz (coevaluationTrace (cutIdem Q Λ₂₃ νᵈ))
  refine derivedTensorHomology_reflect_leftStd_rightStd_one_dimensional.{w, v} Q hQ Λ hρ hR
    (flipLeft Q Λ₂₃ νᵈ (rIdeal (wrapIdem Q Λ₂₃ νᵈ z₀) ⧸ coevaluationTrace (cutIdem Q Λ₂₃ νᵈ)))
    (fun s hs hcut y => by
      rw [flipLeft_smul, loadingIdem, tensorFlip_mk_e]
      exact wrapHead_cut Q Λ₂₃ z₀ s hs hcut _)
    L' hL' (expandDiv d).reverse h₀ t ht het Y₀ hss ι π hιπ htot htop ?_
  rw [finrank_fixSub_leftStd_diagonalTwoPiece Q hQ Λ _ (expandDiv d).reverse h₀ t ht, hJ]
  exact finrank_fixSub_flipLeft_wrapHead_diagonalOuterLoading Q Λ d hRX hne hgen hscalar h₀

end Categorification.Stendhal.SMove
