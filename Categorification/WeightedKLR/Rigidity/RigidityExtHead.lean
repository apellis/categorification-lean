/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtWrap
import Categorification.WeightedKLR.Rigidity.RigidityExtLowest
import Categorification.WeightedKLR.Rigidity.RigidityExtLastDot
import Categorification.WeightedKLR.Rigidity.ReducedDividedNorm
import Categorification.WeightedKLR.RedStrands.StringyLoading
import Categorification.KLR.Crystal.Delta

/-!
# The simple head of the coevaluation standard module

Webster, arXiv:1309.3796v3, §7.1, Lemma 7.3. Fix a dominant integral weight `λ`, a reduced
expression `w` of the longest element `w₀` and the coevaluation word `i_λ` of Definition 7.1, with
black weight `ν` and `|ν| = 2ρ^∨(λ)`. For the two red strands `(λ, λ*)`, `λ* = -w₀λ`, the standard
module `S = P^{(0, |ν|)}_{i_λ}` is the right projective of the wrap idempotent: the first red
strand, the divided-power idempotent of `i_λ`, the second red strand. Then
`coevaluationTrace_eq_iff_isSimpleModule` states that `S` has a unique simple quotient, whose
kernel is the sum of the images of all maps from projectives `P^κ_i` with `κ(2) < |ν|`.

## Proof

The proof differs from Webster's, which counts simples through the crystal of Theorem 5.14.
Here the statement is reduced (`TwoRedErase.coevaluationTrace_eq_iff_isSimpleModule_wrapIdem`)
to two properties of the cyclotomic quotient `R^λ(ν)` at the first red strand.

* The second red strand's cyclotomic relation `x_n^{⟨α_i^∨, λ*⟩} e(t) = 0` holds on the last
  black strand (`dot_pow_mul_e_eq_zero_of_lowest`). Since every simple reflection is a left
  descent of `w₀`, each block `R^λ(i + ν)` vanishes (`subsingleton_of_isLeftDescent_coevaluationWord`),
  and Kang–Kashiwara's Theorem 5.2 gives the relation (`dotElement_pow_mul_lastIdem_eq_zero`).
* Every nonzero element of `e R^λ(ν)` generates the divided-power idempotent `e` on the right
  (`GProj.exists_mul_eq_of_homGdim_eq_one`), since the block has Grothendieck rank one
  (Proposition 7.2, `finrank_coevaluation_projectiveBlock`) and `R^λ(ν) e` has graded
  endomorphism series one (`homGdim_dividedWord_of_websterNorm`).
-/

noncomputable section

namespace Categorification.KLR.CycKLR

open KLRAlgebra Categorification.Graded QuantumGroup QuantumGroup.UDot Module MulOpposite

variable {I : Type} {k : Type*} [Fintype I] [DecidableEq I] [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)

local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^ Λ j)

/-- The labels of the second red strand at black weight `ν`: `⟨α_i^∨, λ*⟩ = -⟨α_i^∨, λ - ν⟩`.
For the coevaluation word of the longest element, `λ - ν = w₀ λ`, so this is `λ* = -w₀ λ`. -/
def dualRedLabel (ν : Multiset I) : I →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i =>
    (-(RD.pair (RD.iY i) (highest - (ν.map RD.iX).sum))).toNat

/-- The two red labels `(λ, λ*)` of the coevaluation standard module. -/
def coevaluationLabels (ν : Multiset I) : Fin 2 → I →₀ ℕ :=
  ![Finsupp.equivFunOnFinite.symm Λ, dualRedLabel RD highest ν]

include hP hΛ in
/-- The last-dot relation on a word ending in `i`, from Kang–Kashiwara. -/
private theorem dot_pow_mul_cL_e_eq_zero (i : I) (β : Multiset I)
    [Nontrivial (CycKLR k Q aΛ ({i} + β))]
    (hvan : Subsingleton (CycKLR k Q aΛ ({i} + ({i} + β))))
    (hcen : ∀ z : CycKLR k Q aΛ ({i} + β), (∀ y, z * y = y * z) →
      ∃ c : k, z = algebraMap k _ c)
    (s : Seq β) :
    mk k Q aΛ ({i} + β) (x ⟨Multiset.card β, lastPos_lt i β⟩ ^
      (-(RD.pair (RD.iY i) (highest - (Multiset.map RD.iX ({i} + β)).sum))).toNat *
        cL Q i β (e s)) = 0 := by
  have hx : IsNilpotent (AbsentColour.InductionCalculus.dotElement Q i aΛ β) := by
    change IsNilpotent (mk k Q aΛ ({i} + β) (x ⟨Multiset.card β, lastPos_lt i β⟩))
    exact Stendhal.cycKLR_x_isNilpotent hP (Finsupp.equivFunOnFinite.symm Λ) ({i} + β)
      ⟨Multiset.card β, lastPos_lt i β⟩
  have hnil : IsNilpotent (AbsentColour.InductionCalculus.dotElement Q i aΛ β *
      AbsentColour.lastIdem Q i aΛ β) :=
    (AbsentColour.InductionCalculus.dot_commute Q i aΛ β 1).isNilpotent_mul_right hx
  have h := AbsentColour.dotElement_pow_mul_lastIdem_eq_zero Q i aΛ β hP.klrSymm
    hP.polyInY_leading (fun j => Polynomial.monic_X_pow (Λ j)) RD highest
    (by rw [Polynomial.natDegree_X_pow]; exact hΛ i)
    (fun j hj => hP.polyInY_degree_pair RD i j hj) hvan hcen hnil
  rw [map_mul, map_pow]
  change AbsentColour.InductionCalculus.dotElement Q i aΛ β ^ _ * _ = 0
  have he : mk k Q aΛ ({i} + β) (cL Q i β (e s)) =
      AbsentColour.lastIdem Q i aΛ β * mk k Q aΛ ({i} + β) (cL Q i β (e s)) := by
    rw [AbsentColour.lastIdem, AbsentColour.cyclotomicLast_one, ← map_mul, ← cL_mul, one_mul]
  rw [he, ← mul_assoc, h, zero_mul]

include hP hΛ in
/-- **The second red strand's cyclotomic relation at a lowest weight.** If `R^λ(ν)` is nonzero
with scalar centre and every block `R^λ(i + ν)` vanishes, then `x_n^{⟨α_i^∨, λ*⟩} e(t) = 0` for
the colour `i` of the last black strand of `t` (input for Webster, arXiv:1309.3796v3, §7.1,
Lemma 7.3). -/
theorem dot_pow_mul_e_eq_zero_of_lowest (ν : Multiset I) [Nontrivial (CycKLR k Q aΛ ν)]
    (hvan : ∀ i, Subsingleton (CycKLR k Q aΛ ({i} + ν)))
    (hcen : ∀ z : CycKLR k Q aΛ ν, (∀ y, z * y = y * z) → ∃ c : k, z = algebraMap k _ c)
    (t : Seq ν) (h : 0 < Multiset.card ν) :
    mk k Q aΛ ν (x ⟨Multiset.card ν - 1, by omega⟩ ^
      dualRedLabel RD highest ν (t.lbl ⟨Multiset.card ν - 1, by omega⟩) * e t) = 0 := by
  generalize hi : t.lbl ⟨Multiset.card ν - 1, by omega⟩ = i
  have hmem : i ∈ ν := hi ▸ Seq.mem t _
  obtain ⟨β, hβ⟩ : ∃ β, {i} + β = ν :=
    ⟨ν.erase i, by rw [Multiset.singleton_add, Multiset.cons_erase hmem]⟩
  subst hβ
  have htail : Seq.HasTail i (Seq.cast (add_comm _ _) t : Seq (β + {i}))
      (Multiset.card ({i} : Multiset I)) := by
    refine ⟨by simp, fun a ha => ?_⟩
    rw [Seq.cast_apply]
    refine Eq.trans (congrArg t.lbl ?_) hi
    ext
    simp only [Multiset.card_singleton, Multiset.card_add, Fin.val_cast] at ha ⊢
    have := a.isLt
    simp only [Multiset.card_add, Multiset.card_singleton] at this
    omega
  obtain ⟨s, hs⟩ := Seq.exists_eq_append_const_of_hasTail
    (fun a ha => Multiset.mem_singleton.1 ha) htail
  have ht : t = Seq.cast (add_comm β {i}) (s.append default) := by
    have h1 := congrArg (Seq.cast (add_comm β {i})) hs
    rw [Subsingleton.elim (Seq.constSeq _) default] at h1
    rw [h1]
    apply Subtype.ext
    funext a
    simp only [Seq.cast_apply]
    rfl
  have hpos : (⟨Multiset.card ({i} + β) - 1, by omega⟩ : Fin (Multiset.card ({i} + β))) =
      ⟨Multiset.card β, lastPos_lt i β⟩ := by
    ext
    simp
  have hne : Nontrivial (CycKLR k Q aΛ ({i} + β)) := inferInstance
  rw [hpos, ht, ← cL_e]
  exact dot_pow_mul_cL_e_eq_zero hP Λ RD highest hΛ i β (hvan i) hcen s

section Head

open KL2

variable (hR : (projectiveRootDatum RD).IsXRegular)

local notation "G" => hP.gradingDatum
local notation "dp" =>
  dividedProjective hP.gradingDatum (fun i j => congrArg Neg.neg (C.symm i j)) C Λ

/-- The divided-power idempotent of a divided word in the cyclotomic quotient, the generator of
`dividedProjective`. -/
def dividedIdem (d : List (I × ℕ)) : CycKLR k Q aΛ (expandDiv d : Multiset I) :=
  mk k Q aΛ _ (hflip (divIdem (KLRAlgebra.Seq.ofList (expandDiv d) rfl) (blocksDiv d 0)))

omit [Fintype I] in
theorem isIdempotentElem_dividedIdem (d : List (I × ℕ)) :
    IsIdempotentElem (dividedIdem Λ (Q := Q) d) :=
  (isIdempotentElem_hflip_divIdem (Q := Q) (isBlocks_ofList d rfl)).map (mk k Q aΛ _)

omit [Fintype I] in
private local instance finiteBlock' (ν : Multiset I) : HasGdim (grade G Λ ν) := by
  let := module_finite (Q := Q) (ν := ν) (fun i j hij => by
    obtain ⟨c, hc, h⟩ := hP.polyInY_leading i j hij
    rw [h]
    exact hc.map Polynomial.C) (fun i => Polynomial.monic_X_pow (R := k) (Λ i))
  exact HasGdim.of_finiteDimensional _

include hP hΛ hR in
/-- **Webster, arXiv:1309.3796v3, §7.1, Lemma 7.3.** Let `w` be a reduced expression of the
longest element (every simple reflection is a left descent of it), `d` the divided coevaluation
word of Definition 7.1 and `ν` its black weight. For the red labels `(λ, λ*)`, the standard module
`S` of the wrap idempotent of the divided-power idempotent has a unique simple quotient: a
submodule `N ⊆ S` has simple quotient exactly when `N` is the sum of the images of the maps from
the projectives `P^κ_i` with `κ(2) < |ν|` (`coevaluationTrace` of the cut idempotents). -/
theorem coevaluationTrace_eq_iff_isSimpleModule
    {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (P : Matrix.Realization C.toLusztig.cartanMatrix K H) (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I)
    (hw : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
    (hlong : ∀ i, (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsLeftDescent
      ((P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)
    (N : Submodule (Stendhal.TensorProductAlgebra k Q
        (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord
          (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w) : Multiset I))
        (expandDiv (Stendhal.coevaluationDividedWord
          (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w) : Multiset I))ᵐᵒᵖ
      (rIdeal (Stendhal.TwoRedErase.wrapIdem Q _ _ (dividedIdem Λ (Q := Q)
        (Stendhal.coevaluationDividedWord
          (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))))) :
    N = Stendhal.coevaluationTrace (Stendhal.TwoRedErase.cutIdem Q _ _) ↔
      IsSimpleModule (Stendhal.TensorProductAlgebra k Q
        (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord
          (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w) : Multiset I))
        (expandDiv (Stendhal.coevaluationDividedWord
          (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w) : Multiset I))ᵐᵒᵖ
        (rIdeal (Stendhal.TwoRedErase.wrapIdem Q _ _ (dividedIdem Λ (Q := Q)
        (Stendhal.coevaluationDividedWord
          (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))) ⧸ N) := by
  let d := Stendhal.coevaluationDividedWord
    (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w
  let ν : Multiset I := expandDiv d
  let z₀ := dividedIdem Λ (Q := Q) d
  have hz₀ : IsIdempotentElem z₀ := isIdempotentElem_dividedIdem Λ d
  have hz₀0 : z₀ ∈ grade G Λ ν 0 :=
    Graded.mem_map_of_mem _ (mk k Q aΛ ν).toLinearMap
      (hP.gradingDatum.hflip_mem_grade (fun i j => congrArg Neg.neg (C.symm i j))
        (divIdem_mem_grade G (isBlocks_ofList d rfl)))
  have hdp : dp ν d rfl = (GProj.ofIdempotent z₀ hz₀ hz₀0).shift (-divAngle2 C d) := rfl
  have hrank : finrank (LaurentPolynomial ℤ) (K0 (grade G Λ ν)) = 1 := by
    change finrank (LaurentPolynomial ℤ) (K0 (grade G Λ (expandDiv d : Multiset I))) = 1
    dsimp only [d]
    rw [Stendhal.expand_coevaluationDividedWord]
    exact finrank_coevaluation_projectiveBlock hP Λ RD highest hΛ hR P weight hweight
      match_weight w hw
  have hn : GProj.homGdim (dp ν d rfl) (dp ν d rfl) = 1 :=
    homGdim_dividedWord_of_websterNorm hP Λ RD highest hΛ hR d
      (Stendhal.websterForm_coevaluationDividedWord P (dominantWeight Λ RD highest hΛ) hR weight
        hweight match_weight w hw)
  have hsimple := isSimple_coevaluationProjective hP Λ RD highest hΛ hR P weight hweight
    match_weight w hw
  have hne : z₀ ≠ 0 := by
    intro h0
    have := IsSimpleModule.nontrivial (CycKLR k Q aΛ ν) (dp ν d rfl).carrier
    obtain ⟨y, hy⟩ := exists_ne (0 : (dp ν d rfl).carrier)
    let y' : leftIdeal z₀ := y
    have hy' : (y' : CycKLR k Q aΛ ν) * z₀ = y' := y'.2
    apply hy
    change y' = 0
    apply Subtype.ext
    have hz : ∀ a : CycKLR k Q aΛ ν, a * z₀ = a → a = 0 := fun a ha => by
      rw [← ha, h0, mul_zero]
    exact hz _ hy'
  have hnt : Nontrivial (CycKLR k Q aΛ ν) := ⟨⟨z₀, 0, hne⟩⟩
  have hcen : ∀ z : CycKLR k Q aΛ ν, (∀ y, z * y = y * z) → ∃ c : k, z = algebraMap k _ c :=
    fun z hz => GProj.exists_algebraMap_of_commute (dp ν d rfl) hrank hn z hz
  have hgen : ∀ y : CycKLR k Q aΛ ν, z₀ * y = y → y ≠ 0 → ∃ c, y * c = z₀ :=
    fun y hy hy0 => GProj.exists_mul_eq_of_homGdim_eq_one hz₀ hz₀0 _ hrank (hdp ▸ hn) y hy hy0
  have hvan : ∀ i, Subsingleton (CycKLR k Q aΛ ({i} + ν)) := by
    intro i
    have h := subsingleton_of_isLeftDescent_coevaluationWord hP Λ RD highest hΛ hR P weight
      hweight match_weight w hw i (hlong i)
    change Subsingleton (CycKLR k Q aΛ ({i} + (expandDiv d : Multiset I)))
    dsimp only [d]
    rw [Stendhal.expand_coevaluationDividedWord]
    exact h
  exact Stendhal.TwoRedErase.coevaluationTrace_eq_iff_isSimpleModule_wrapIdem Q
    (coevaluationLabels Λ RD highest ν) ν
    (fun t h => dot_pow_mul_e_eq_zero_of_lowest hP Λ RD highest hΛ ν hvan hcen t h) z₀ hz₀ hne hgen N

omit [Fintype I] in
variable (Q) in
/-- The simple head `L_λ` of the coevaluation wrap projective of a divided word `d` (Webster,
arXiv:1309.3796v3, §7.1, Lemma 7.3): the quotient of `wrapIdem z₀ · T` by the sum of the images
of the cut projectives, as a right module over the whole algebra `T`. -/
abbrev _root_.Categorification.Stendhal.coevaluationHead (d : List (I × ℕ)) : Type _ :=
  rIdeal (Stendhal.TwoRedErase.wrapIdem Q (coevaluationLabels Λ RD highest (expandDiv d))
      (expandDiv d) (dividedIdem Λ (Q := Q) d)) ⧸
    Stendhal.coevaluationTrace
      (Stendhal.TwoRedErase.cutIdem Q (coevaluationLabels Λ RD highest (expandDiv d))
        (expandDiv d))

include hP hΛ hR in
/-- **Webster, arXiv:1309.3796v3, §7.1, Lemma 7.3 (simplicity of the head).** For a reduced
expression `w` of the longest element, the head `L_λ` of the coevaluation wrap projective is a
simple right module. -/
theorem _root_.Categorification.Stendhal.isSimpleModule_coevaluationHead
    {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (P : Matrix.Realization C.toLusztig.cartanMatrix K H) (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I)
    (hw : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
    (hlong : ∀ i, (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsLeftDescent
      ((P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i) :
    IsSimpleModule (Stendhal.TensorProductAlgebra k Q
        (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord
          (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w) : Multiset I))
        (expandDiv (Stendhal.coevaluationDividedWord
          (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w) : Multiset I))ᵐᵒᵖ
      (Stendhal.coevaluationHead Q Λ RD highest (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w)) :=
  (coevaluationTrace_eq_iff_isSimpleModule hP Λ RD highest hΛ hR P weight hweight match_weight
    w hw hlong _).1 rfl

end Head

end Categorification.KLR.CycKLR
