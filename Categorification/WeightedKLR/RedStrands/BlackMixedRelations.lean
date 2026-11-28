/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackMixedSquare
import Categorification.WeightedKLR.RedStrands.BlackDerivedTwoMorphisms
import Categorification.Algebra.ResTwoStepEnd

/-!
# The quadratic KLR relation for the mixed crossings on right `T^λ`-modules

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
Khovanov–Lauda I, §2.1; Brundan, arXiv:1501.00350v1, (1.3) (the shape of
`TwoRep.RouqUpKLR.square`).

For `i ≠ j` and symmetric `Q` (`KLRSymm Q`), the composite of the two mixed crossings on
`Eⱼ ∘ Eᵢ` (restriction along first `j`, then `i`) is `Q_{ij}` evaluated at the dot on the
`i` strand and the dot on the `j` strand (`blackMixedCross_comp_blackMixedCrossRev`). The dots
are `blackDot` whiskered into the composite. The element identity is
`mixedCrossElem_mul_mixedCrossRevElem`; the dots on the appended strands are the images of the
KLR dots (`appendBlack_appendedDot_eq`, `appendedDot_mixed_eq`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong AbsentColour.MixedCrossing

set_option backward.isDefEq.respectTransparency false

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I} {i j : I}

set_option hygiene false in
local notation "σ" => stendhalWeight ℓ ν
set_option hygiene false in
local notation "S" => affineCoverQ Q Λ
set_option hygiene false in
local notation "b" => (Sum.inl i : I ⊕ Fin ℓ)
set_option hygiene false in
local notation "c" => (Sum.inl j : I ⊕ Fin ℓ)
set_option hygiene false in
local notation "νj" => ((Singleton.singleton j : Multiset I) + ν)
set_option hygiene false in
local notation "δ" => ((Singleton.singleton i : Multiset I) + νj)
set_option hygiene false in
local notation "U" => TensorProductAlgebra k Q Λ δ
set_option hygiene false in
local notation "p" => appendBlack (k := k) Q Λ i νj
set_option hygiene false in
local notation "fj" => appendBlack Q Λ j ν
set_option hygiene false in
local notation "fi" => appendBlack Q Λ i ν
set_option hygiene false in
local notation "νi" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "r" => appendBlackAt (k := k) (Q := Q) Λ j (mixedSwap ν i j)

/-! ### Dots on the appended strands -/

omit [DecidableEq I] in
private theorem card_δ : Multiset.card (stendhalWeight ℓ δ) = Multiset.card σ + 2 := by
  rw [card_stendhalWeight_cons, card_stendhalWeight_cons]

private theorem mixedProj_x (a : Fin (Multiset.card (({b} : Multiset (I ⊕ Fin ℓ)) + ({c} + σ)))) :
    mixedProj Λ ν i j (x a) =
      affineTensorProjection (Q := Q) Λ δ (x ⟨a.val, by
        have h1 := a.isLt
        have h2 := card_double (I := I ⊕ Fin ℓ) σ b c
        have h3 := card_δ (ℓ := ℓ) (ν := ν) (i := i) (j := j)
        omega⟩) := by
  change affineTensorProjection Λ δ (castKLR S _ (x a)) = _
  rw [castKLR_x]
  rfl

private theorem appendBlack_proj_x (a : Fin (Multiset.card (stendhalWeight ℓ νj))) :
    p (affineTensorProjection Λ νj (x a)) =
      affineTensorProjection (Q := Q) Λ δ (x ⟨a.val, by
        have h1 := a.isLt
        have h2 := card_stendhalWeight_cons (ℓ := ℓ) j ν
        have h3 := card_δ (ℓ := ℓ) (ν := ν) (i := i) (j := j)
        omega⟩) * p 1 := by
  have h1 : p 1 = affineTensorProjection Λ δ (castKLR S (stendhalWeight_black_cons i νj)
      (cL S b _ 1)) := by
    rw [← map_one (affineTensorProjection (Q := Q) Λ νj), appendBlack_affineTensorProjection]
  rw [appendBlack_affineTensorProjection, cL_x, map_mul, map_mul, h1, castKLR_x]
  rfl

/-- The dot on the strand appended first (`j`), transported along the second append, is the
image of the KLR dot `x_n`, cut by `p(f_j 1)`. -/
theorem appendBlack_appendedDot_eq :
    p (appendedDot Q Λ j ν) = mixedProj Λ ν i j (x ⟨Multiset.card σ, by
      rw [card_double]; omega⟩) * p (fj 1) := by
  rw [appendedDot_eq, map_mul, appendBlack_proj_x, mixedProj_x, mul_assoc, ← map_mul p 1,
    one_mul]

/-- The dot on the strand appended second (`i`) is the image of the KLR dot `x_{n+1}`, cut by
`p(1)`. -/
theorem appendedDot_mixed_eq :
    appendedDot Q Λ i νj = mixedProj Λ ν i j (x ⟨Multiset.card σ + 1, by
      rw [card_double]; omega⟩) * p 1 := by
  rw [appendedDot_eq, mixedProj_x]
  congr 3
  exact Fin.ext (card_stendhalWeight_cons j ν)

theorem appendBlack_fj_one_eq :
    p (fj 1) = mixedProj (Q := Q) Λ ν i j (doubleLast S σ b c 1) := by
  rw [← map_one (affineTensorProjection (Q := Q) Λ ν), mixedProj_doubleLast]

/-! ### Polynomials cut by a commuting idempotent -/

private theorem commute_ncEval {R : Type*} [Ring R] [Algebra k R] {n : ℕ} {e : R}
    (z : Fin n → R) (hz : ∀ a, Commute (z a) e) (P : MvPolynomial (Fin n) k) :
    Commute (KLR.ncEval z P) e := by
  unfold KLR.ncEval
  refine Commute.sum_left _ _ _ fun s _ => ?_
  refine (Algebra.commute_algebraMap_left _ e).mul_left ?_
  exact Commute.list_prod_left _ _ fun y hy => by
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hy
    exact (hz a).pow_left _

private theorem pow_mul_idem {R : Type*} [Ring R] {e y z : R} (hz : Commute z e)
    (h : y * e = z * e) (m : ℕ) : y ^ m * e = z ^ m * e := by
  induction m with
  | zero => rw [pow_zero, pow_zero]
  | succ m ih =>
    calc y ^ (m + 1) * e = y ^ m * (y * e) := by rw [pow_succ, mul_assoc]
      _ = y ^ m * e * z := by rw [h, hz.eq, ← mul_assoc]
      _ = z ^ m * e * z := by rw [ih]
      _ = z ^ (m + 1) * e := by rw [mul_assoc, ← hz.eq, ← mul_assoc, pow_succ]

private theorem prod_mul_idem {R : Type*} [Ring R] {e : R} :
    ∀ {n : ℕ} (f g : Fin n → R), (∀ a, Commute (g a) e) → (∀ a, f a * e = g a * e) →
      (List.ofFn f).prod * e = (List.ofFn g).prod * e
  | 0, _, _, _, _ => rfl
  | n + 1, f, g, hg, h => by
    have hc : Commute (List.ofFn fun a : Fin n => g a.succ).prod e :=
      Commute.list_prod_left _ _ fun y hy => by
        obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hy
        exact hg a.succ
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      prod_mul_idem _ _ (fun a => hg a.succ) (fun a => h a.succ), hc.eq, ← mul_assoc, h,
      mul_assoc, ← hc.eq, ← mul_assoc]

private theorem ncEval_mul_idem {R : Type*} [Ring R] [Algebra k R] {n : ℕ} {e : R}
    (y z : Fin n → R) (hz : ∀ a, Commute (z a) e) (h : ∀ a, y a * e = z a * e)
    (P : MvPolynomial (Fin n) k) : KLR.ncEval y P * e = KLR.ncEval z P * e := by
  unfold KLR.ncEval
  rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_assoc, mul_assoc, prod_mul_idem _ _ (fun a => (hz a).pow_left _)
    (fun a => pow_mul_idem (hz a) (h a) _)]


/-! ### The quadratic relation on modules -/

set_option hygiene false in
local notation "φ₁" => appendBlackOp Q Λ j ν
set_option hygiene false in
local notation "φ₂" => appendBlackOp Q Λ i νj

omit [DecidableEq I] in
private theorem rename_rev_swap (P : MvPolynomial (Fin 2) k) :
    MvPolynomial.rename Fin.rev (MvPolynomial.rename ![1, 0] P) = P := by
  rw [MvPolynomial.rename_rename]
  have : (Fin.rev ∘ ![(1 : Fin 2), 0]) = id := by
    funext t
    fin_cases t <;> rfl
  rw [this, MvPolynomial.rename_id_apply]

private theorem twoRes_algebraMap (c' : k) :
    φ₂ (φ₁ (algebraMap k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ c')) =
      algebraMap k Uᵐᵒᵖ c' * φ₂ (φ₁ 1) := by
  rw [MulOpposite.algebraMap_apply, MulOpposite.algebraMap_apply, ← op_one, appendBlackOp_op,
    appendBlackOp_op, appendBlackOp_op, appendBlackOp_op, ← op_mul,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, map_smul,
    mul_smul_comm, mul_one]

variable (Q Λ ν i j) in
/-- The dot on the strand appended first (`j`), as an element acting on `Eⱼ ∘ Eᵢ`. -/
def mixedDotFirst : twoResInt k φ₁ φ₂ :=
  ⟨p (appendedDot Q Λ j ν), fun a => by
    induction a using MulOpposite.rec' with | _ a => ?_
    rw [appendBlackOp_op, appendBlackOp_op, ← op_mul, ← op_mul, ← map_mul, ← map_mul,
      appendedDot_commute]⟩

variable (Q Λ ν i j) in
/-- The dot on the strand appended second (`i`), as an element acting on `Eⱼ ∘ Eᵢ`. -/
def mixedDotSecond : twoResInt k φ₁ φ₂ :=
  ⟨appendedDot Q Λ i νj, fun a => by
    induction a using MulOpposite.rec' with | _ a => ?_
    rw [appendBlackOp_op, appendBlackOp_op, ← op_mul, ← op_mul, appendedDot_commute]⟩

private theorem fj_one_idem : p (fj 1) * p (fj 1) = p (fj 1) := by
  rw [← map_mul, ← map_mul, one_mul]

private theorem mixed_cut_eq (hij : i ≠ j) :
    mixedCrossElem Λ ν i j * mixedCrossRevElem Λ ν i j =
      p (fj 1) * KLR.ncEval ![p (appendedDot Q Λ j ν), appendedDot Q Λ i νj] (Q j i) := by
  have hc₁ : Commute (p (appendedDot Q Λ j ν)) (p (fj 1)) := by
    change _ * _ = _ * _
    rw [← map_mul, ← map_mul, appendedDot_commute]
  have hc₂ : Commute (appendedDot Q Λ i νj) (p (fj 1)) := (appendedDot_commute Q Λ i νj _).symm
  have hz : ∀ a, Commute (![p (appendedDot Q Λ j ν), appendedDot Q Λ i νj] a) (p (fj 1)) := by
    intro a; fin_cases a
    exacts [hc₁, hc₂]
  rw [mixedCrossElem_mul_mixedCrossRevElem hij, ← (commute_ncEval _ hz _).eq]
  refine ncEval_mul_idem _ _ hz (fun a => ?_) _
  fin_cases a
  · change _ = p (appendedDot Q Λ j ν) * _
    rw [appendBlack_appendedDot_eq, mul_assoc, fj_one_idem]
    rfl
  · change _ = appendedDot Q Λ i νj * _
    rw [appendedDot_mixed_eq, mul_assoc, ← map_mul p 1, one_mul]
    rfl

/-- **The quadratic KLR relation for the mixed crossings** (KL I, §2.1; Brundan,
arXiv:1501.00350v1, (1.3)): for `i ≠ j` and symmetric `Q`, the composite
`Eⱼ ∘ Eᵢ ⟶ Eᵢ ∘ Eⱼ' ⟶ Eⱼ ∘ Eᵢ` of the two mixed crossings is `Q_{ij}` evaluated at the dot on
the `i` strand and the dot on the `j` strand. -/
theorem blackMixedCross_comp_blackMixedCrossRev (hsym : KLRSymm Q) (hij : i ≠ j) :
    blackMixedCross hsym hij ≫ blackMixedCrossRev hsym hij =
      KLR.ncEval (A := End (blackE Q Λ i νj ⋙ blackE Q Λ j ν))
        ![Functor.whiskerRight (blackDot Q Λ i νj) (blackE Q Λ j ν),
          Functor.whiskerLeft (blackE Q Λ i νj) (blackDot Q Λ j ν)] (Q i j) := by
  have hA : twoResEnd (mixedDotFirst Q Λ ν i j) =
      Functor.whiskerLeft (blackE Q Λ i νj) (blackDot Q Λ j ν) :=
    twoRes_end_ext fun _ _ => rfl
  have hB : twoResEnd (mixedDotSecond Q Λ ν i j) =
      Functor.whiskerRight (blackDot Q Λ i νj) (blackE Q Λ j ν) :=
    twoRes_end_ext fun _ _ => rfl
  calc blackMixedCross hsym hij ≫ blackMixedCrossRev hsym hij =
        twoResEnd (KLR.ncEval ![mixedDotFirst Q Λ ν i j, mixedDotSecond Q Λ ν i j] (Q j i)) :=
        twoRes_end_ext fun M w => by
          change op (mixedCrossRevElem Λ ν i j) • op (mixedCrossElem Λ ν i j) • w.val.val =
            op ((twoResInt k φ₁ φ₂).val (KLR.ncEval ![mixedDotFirst Q Λ ν i j,
              mixedDotSecond Q Λ ν i j] (Q j i))) • w.val.val
          rw [ncEval_map, smul_smul, ← op_mul, mixed_cut_eq hij]
          conv_rhs => rw [← twoRes_fixed w, smul_smul]
          rfl
    _ = KLR.ncEval (fun a => twoResEnd
          (![mixedDotFirst Q Λ ν i j, mixedDotSecond Q Λ ν i j] (Fin.rev a)))
          (MvPolynomial.rename Fin.rev (Q j i)) := twoResEnd_ncEval φ₁ φ₂ twoRes_algebraMap _ _
    _ = _ := by
        rw [hsym i j hij, rename_rev_swap]
        congr 1
        funext a; fin_cases a
        exacts [hB, hA]


/-! ### The second composite -/

private theorem castTPA_proj' {β β' : Multiset I} (h : β = β')
    (z : KLRAlgebra k S (stendhalWeight ℓ β)) :
    castTensorProductAlgebra Q Λ h (affineTensorProjection Λ β z) =
      affineTensorProjection Λ β' (castKLR S (congrArg (stendhalWeight ℓ) h) z) := by
  subst h; rfl

private theorem castTPA_proj_x {β β' : Multiset I} (h : β = β')
    (a : Fin (Multiset.card (stendhalWeight ℓ β))) :
    castTensorProductAlgebra Q Λ h (affineTensorProjection Λ β (x a)) =
      affineTensorProjection (Q := Q) Λ β' (x ⟨a.val, by subst h; exact a.isLt⟩) := by
  rw [castTPA_proj', castKLR_x]
  rfl

private theorem appendBlack_proj_x' (a₀ : I) (μ : Multiset I)
    (a : Fin (Multiset.card (stendhalWeight ℓ μ))) :
    appendBlack Q Λ a₀ μ (affineTensorProjection Λ μ (x a)) =
      affineTensorProjection (Q := Q) Λ (({a₀} : Multiset I) + μ) (x ⟨a.val, by
        have h1 := a.isLt
        have h2 := card_stendhalWeight_cons (ℓ := ℓ) a₀ μ
        omega⟩) * appendBlack Q Λ a₀ μ 1 := by
  have h1 : appendBlack Q Λ a₀ μ 1 = affineTensorProjection Λ _
      (castKLR S (stendhalWeight_black_cons a₀ μ) (cL S (Sum.inl a₀) _ 1)) := by
    rw [← map_one (affineTensorProjection (Q := Q) Λ μ), appendBlack_affineTensorProjection]
  rw [appendBlack_affineTensorProjection, cL_x, map_mul, map_mul, h1, castKLR_x]
  rfl

/-- The dot on the strand `j` appended second, transported to `T^λ_δ`. -/
def appendedDotAt : U :=
  castTensorProductAlgebra Q Λ (mixedSwap ν i j) (appendedDot Q Λ j νi)

theorem appendedDotAt_commute (a : TensorProductAlgebra k Q Λ νi) :
    r a * appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j) = appendedDotAt * r a := by
  have h := congrArg (castTensorProductAlgebra Q Λ (mixedSwap ν i j))
    (appendedDot_commute Q Λ j νi a)
  rwa [map_mul, map_mul, cast_appendBlack_mixed] at h

theorem appendBlackAt_appendedDot_eq :
    r (appendedDot Q Λ i ν) = mixedProj Λ ν i j (x ⟨Multiset.card σ, by
      rw [card_double]; omega⟩) * r (fi 1) := by
  rw [appendedDot_eq, map_mul, ← cast_appendBlack_mixed, appendBlack_proj_x', map_mul,
    castTPA_proj_x, cast_appendBlack_mixed, mixedProj_x, mul_assoc, ← map_mul r 1, one_mul]

theorem appendedDotAt_eq :
    appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j) =
      mixedProj Λ ν i j (x ⟨Multiset.card σ + 1, by rw [card_double]; omega⟩) * r 1 := by
  rw [appendedDotAt, appendedDot_eq, map_mul, castTPA_proj_x, cast_appendBlack_mixed,
    mixedProj_x]
  congr 3
  exact Fin.ext (card_stendhalWeight_cons i ν)

theorem appendBlackAt_fi_one_eq :
    r (fi 1) = mixedProj (Q := Q) Λ ν i j (castKLR S (square σ b c) (doubleLast S σ c b 1)) := by
  rw [← map_one (affineTensorProjection (Q := Q) Λ ν), mixedProj_cast_doubleLast]

/-- **The quadratic relation in the other order**: `χ_{ji} χ_{ij} = Q_{ij}(y_n, y_{n+1}) ·
r(f_i 1)`, with `y_n` the dot on the strand appended first (`i`). -/
theorem mixedCrossRevElem_mul_mixedCrossElem (hij : i ≠ j) :
    mixedCrossRevElem Λ ν i j * mixedCrossElem Λ ν i j =
      KLR.ncEval ![mixedProj Λ ν i j (x ⟨Multiset.card σ, by rw [card_double]; omega⟩),
        mixedProj Λ ν i j (x ⟨Multiset.card σ + 1, by rw [card_double]; omega⟩)] (Q i j) *
        r (fi 1) := by
  rw [mixedCrossRevElem_eq, mixedCrossElem, ← mixedProj_neg_psi_rev (i := i) (j := j),
    ← mixedProj_neg_psi (i := i) (j := j), appendBlack_fj_one_eq, appendBlackAt_fi_one_eq]
  have hD' : castKLR S (square σ b c) (doubleLast S σ c b 1) *
      castKLR S (square σ b c) (doubleLast S σ c b 1) =
      castKLR S (square σ b c) (doubleLast S σ c b 1) := by
    rw [← map_mul, doubleLast_one_mul_self]
  have key := intertwined_idem_sq (cast_doubleLast_one_mul_psi S σ b c)
    (doubleLast_one_intertwine S σ b c) (doubleLast_one_mul_self S σ b c) hD'
  have hsq := congrArg (castKLR S (square σ b c))
    (psi_sq_mul_doubleLast_one S σ c b (Sum.inl_injective.ne hij.symm))
  rw [map_mul, map_mul, castKLR_ψ, map_mul] at hsq
  rw [hsq] at key
  have key' := congrArg (mixedProj (Q := Q) Λ ν i j) key
  simp only [map_mul] at key'
  rw [key']
  congr 1
  refine (ncEval_map ((mixedProj (Q := Q) Λ ν i j).comp (castKLR S (square σ b c)).toAlgHom)
    _ _).trans ?_
  congr 1
  funext a
  fin_cases a
  · change mixedProj Λ ν i j (castKLR S _ (x _)) = _
    rw [castKLR_x]
    rfl
  · change mixedProj Λ ν i j (castKLR S _ (x _)) = _
    rw [castKLR_x]
    rfl


set_option hygiene false in
local notation "ψ₁" => appendBlackOp Q Λ i ν
set_option hygiene false in
local notation "ψ₂" => appendBlackAtOp Λ ν i j

theorem op_appendedDotAt_commute (a : (TensorProductAlgebra k Q Λ νi)ᵐᵒᵖ) :
    op (appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j)) * ψ₂ a =
      ψ₂ a * op appendedDotAt := by
  induction a using MulOpposite.rec' with | _ a => ?_
  change op _ * op (r a) = op (r a) * op _
  rw [← op_mul, ← op_mul, appendedDotAt_commute]

variable (Λ ν i j) in
/-- **The dot on `Eⱼ'`**, the restriction along `appendBlackAt j`: right multiplication by the
transported dot `appendedDotAt`. -/
def blackDotAt : blackEAt (Q := Q) Λ ν i j ⟶ blackEAt Λ ν i j where
  app M := ModuleCat.ofHom (resAct (op appendedDotAt) op_appendedDotAt_commute M)
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun w => Res.ext
    (f.hom.map_smul (op (appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j))) w.val).symm)

private theorem twoRes_algebraMap' (c' : k) :
    ψ₂ (ψ₁ (algebraMap k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ c')) =
      algebraMap k Uᵐᵒᵖ c' * ψ₂ (ψ₁ 1) := by
  rw [MulOpposite.algebraMap_apply, MulOpposite.algebraMap_apply, ← op_one, appendBlackOp_op,
    appendBlackOp_op]
  change op (r _) = op _ * op (r _)
  rw [← op_mul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul,
    unop_op, unop_op, map_smul, mul_smul_comm, mul_one]

variable (Q Λ ν i j) in
/-- The dot on the strand appended first (`i`), as an element acting on `Eᵢ ∘ Eⱼ'`. -/
def mixedDotFirstAt : twoResInt k ψ₁ ψ₂ :=
  ⟨r (appendedDot Q Λ i ν), fun a => by
    induction a using MulOpposite.rec' with | _ a => ?_
    change op _ * op (r (fi a)) = op (r (fi a)) * op _
    rw [← op_mul, ← op_mul, ← map_mul, ← map_mul, appendedDot_commute]⟩

variable (Q Λ ν i j) in
/-- The dot on the strand appended second (`j`), as an element acting on `Eᵢ ∘ Eⱼ'`. -/
def mixedDotSecondAt : twoResInt k ψ₁ ψ₂ :=
  ⟨appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j), fun a => by
    induction a using MulOpposite.rec' with | _ a => ?_
    change op _ * op (r (fi a)) = op (r (fi a)) * op _
    rw [← op_mul, ← op_mul, appendedDotAt_commute]⟩

private theorem fi_one_idem : r (fi 1) * r (fi 1) = r (fi 1) := by
  rw [← map_mul, ← map_mul, one_mul]

private theorem mixed_cut_eq' (hij : i ≠ j) :
    mixedCrossRevElem Λ ν i j * mixedCrossElem Λ ν i j =
      r (fi 1) * KLR.ncEval ![r (appendedDot Q Λ i ν),
        appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j)] (Q i j) := by
  have hc₁ : Commute (r (appendedDot Q Λ i ν)) (r (fi 1)) := by
    change _ * _ = _ * _
    rw [← map_mul, ← map_mul, appendedDot_commute]
  have hc₂ : Commute (appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j)) (r (fi 1)) :=
    (appendedDotAt_commute _).symm
  have hz : ∀ a, Commute (![r (appendedDot Q Λ i ν),
      appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j)] a) (r (fi 1)) := by
    intro a; fin_cases a
    exacts [hc₁, hc₂]
  rw [mixedCrossRevElem_mul_mixedCrossElem hij, ← (commute_ncEval _ hz _).eq]
  refine ncEval_mul_idem _ _ hz (fun a => ?_) _
  fin_cases a
  · change _ = r (appendedDot Q Λ i ν) * _
    rw [appendBlackAt_appendedDot_eq, mul_assoc, fi_one_idem]
    rfl
  · change _ = appendedDotAt * _
    rw [appendedDotAt_eq, mul_assoc, ← map_mul r 1, one_mul]
    rfl

/-- **The quadratic KLR relation for the mixed crossings, other order** (KL I, §2.1): for
`i ≠ j` and symmetric `Q`, the composite `Eᵢ ∘ Eⱼ' ⟶ Eⱼ ∘ Eᵢ ⟶ Eᵢ ∘ Eⱼ'` is `Q_{ji}` evaluated
at the dot on the `j` strand and the dot on the `i` strand. -/
theorem blackMixedCrossRev_comp_blackMixedCross (hsym : KLRSymm Q) (hij : i ≠ j) :
    blackMixedCrossRev hsym hij ≫ blackMixedCross hsym hij =
      KLR.ncEval (A := End (blackEAt Λ ν i j ⋙ blackE Q Λ i ν))
        ![Functor.whiskerRight (blackDotAt Λ ν i j) (blackE Q Λ i ν),
          Functor.whiskerLeft (blackEAt Λ ν i j) (blackDot Q Λ i ν)] (Q j i) := by
  have hA : twoResEnd (mixedDotFirstAt Q Λ ν i j) =
      Functor.whiskerLeft (blackEAt Λ ν i j) (blackDot Q Λ i ν) :=
    twoRes_end_ext fun _ _ => rfl
  have hB : twoResEnd (mixedDotSecondAt Q Λ ν i j) =
      Functor.whiskerRight (blackDotAt Λ ν i j) (blackE Q Λ i ν) :=
    twoRes_end_ext fun _ _ => rfl
  calc blackMixedCrossRev hsym hij ≫ blackMixedCross hsym hij =
        twoResEnd (KLR.ncEval ![mixedDotFirstAt Q Λ ν i j, mixedDotSecondAt Q Λ ν i j] (Q i j)) :=
        twoRes_end_ext fun M w => by
          change op (mixedCrossElem Λ ν i j) • op (mixedCrossRevElem Λ ν i j) • w.val.val =
            op ((twoResInt k ψ₁ ψ₂).val (KLR.ncEval ![mixedDotFirstAt Q Λ ν i j,
              mixedDotSecondAt Q Λ ν i j] (Q i j))) • w.val.val
          rw [ncEval_map, smul_smul, ← op_mul, mixed_cut_eq' hij]
          conv_rhs => rw [← twoRes_fixed w, smul_smul]
          rfl
    _ = KLR.ncEval (fun a => twoResEnd
          (![mixedDotFirstAt Q Λ ν i j, mixedDotSecondAt Q Λ ν i j] (Fin.rev a)))
          (MvPolynomial.rename Fin.rev (Q i j)) := twoResEnd_ncEval ψ₁ ψ₂ twoRes_algebraMap' _ _
    _ = _ := by
        rw [hsym j i hij.symm, rename_rev_swap]
        congr 1
        funext a; fin_cases a
        exacts [hB, hA]


/-! ### Dot slides -/

set_option hygiene false in
local notation "D" => doubleLast S σ b c 1
set_option hygiene false in
local notation "D'" => castKLR S (square σ b c) (doubleLast S σ c b 1)
set_option hygiene false in
local notation "x₀" => (x ⟨Multiset.card σ, by rw [card_double]; omega⟩ :
  KLRAlgebra k S (({b} : Multiset (I ⊕ Fin ℓ)) + ({c} + σ)))
set_option hygiene false in
local notation "x₁" => (x ⟨Multiset.card σ + 1, by rw [card_double]; omega⟩ :
  KLRAlgebra k S (({b} : Multiset (I ⊕ Fin ℓ)) + ({c} + σ)))

private theorem slide_aux {R : Type*} [Ring R] {E E' t a b' : R} (h : b' * t * E' = t * a * E')
    (hb : Commute b' E) (ha : Commute a E') (hE : E * E = E) (hE' : E' * E' = E') :
    b' * E * (E * -t * E') = E * -t * E' * (a * E') := by
  have e1 : b' * E * (E * -t * E') = -(E * (b' * t * E')) := by
    rw [show b' * E * (E * -t * E') = -(b' * (E * E) * t * E') by noncomm_ring, hE, hb.eq]
    noncomm_ring
  have e2 : E * -t * E' * (a * E') = -(E * (t * a * E')) := by
    calc E * -t * E' * (a * E') = -(E * t * (E' * a) * E') := by noncomm_ring
      _ = -(E * t * a * (E' * E')) := by rw [← ha.eq]; noncomm_ring
      _ = _ := by rw [hE']; noncomm_ring
  rw [e1, e2, h]

private theorem D'_idem : (D' * D' : KLRAlgebra k S (({b} : Multiset (I ⊕ Fin ℓ)) + ({c} + σ))) =
    D' := by
  rw [← map_mul, doubleLast_one_mul_self]

private theorem x_commute_D' (a : Fin (Multiset.card (({b} : Multiset (I ⊕ Fin ℓ)) + ({c} + σ)))) :
    Commute (x a) D' := by
  have h := congrArg (castKLR S (square σ b c))
    (x_commute_doubleLast_one S σ c b ⟨a.val, by
      have h1 := a.isLt; simp only [Multiset.card_add, Multiset.card_singleton] at h1 ⊢; omega⟩).eq
  rw [map_mul, map_mul, castKLR_x] at h
  exact h

private theorem slide_right_K (hij : i ≠ j) : x₁ * ψ (Multiset.card σ) * D' =
    ψ (Multiset.card σ) * x₀ * D' := by
  have h := congrArg (castKLR S (square σ b c))
    (dot_cross_right_mul_doubleLast_one S σ c b (Sum.inl_injective.ne hij.symm))
  rw [map_zero, map_mul, map_sub, map_mul, map_mul, castKLR_ψ, castKLR_x, castKLR_x] at h
  exact (sub_eq_zero.mp (by rw [← sub_mul]; exact h)).symm

private theorem slide_left_K (hij : i ≠ j) : x₀ * ψ (Multiset.card σ) * D' =
    ψ (Multiset.card σ) * x₁ * D' := by
  have h := congrArg (castKLR S (square σ b c))
    (dot_cross_left_mul_doubleLast_one S σ c b (Sum.inl_injective.ne hij.symm))
  rw [map_zero, map_mul, map_sub, map_mul, map_mul, castKLR_ψ, castKLR_x, castKLR_x] at h
  exact sub_eq_zero.mp (by rw [← sub_mul]; exact h)

private theorem fj_one_mul_appendedDot :
    p (fj 1) * appendedDot Q Λ i νj = mixedProj Λ ν i j (x₁ * D) := by
  rw [appendedDot_commute Q Λ i νj (fj 1), appendedDot_mixed_eq, mul_assoc,
    ← map_mul p 1, one_mul, appendBlack_fj_one_eq, map_mul]

private theorem fi_one_mul_appendedDotAt :
    r (fi 1) * appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j) =
      mixedProj Λ ν i j (x₁ * D') := by
  rw [appendedDotAt_commute (fi 1), appendedDotAt_eq, mul_assoc, ← map_mul r 1, one_mul,
    appendBlackAt_fi_one_eq, map_mul]

theorem mixedCrossElem_eq_mixedProj :
    mixedCrossElem Λ ν i j = mixedProj (Q := Q) Λ ν i j (D * -ψ (Multiset.card σ) * D') := by
  rw [mixedCrossElem, appendBlack_fj_one_eq, appendBlackAt_fi_one_eq, ← mixedProj_neg_psi,
    map_mul, map_mul]

/-- **Dot slide on the `i` strand** (KL I, §2.1, (2.4) for distinct labels): the dot on the `i`
strand moves through the mixed crossing. -/
theorem appendedDot_mul_mixedCrossElem (hij : i ≠ j) :
    appendedDot Q Λ i νj * mixedCrossElem Λ ν i j =
      mixedCrossElem Λ ν i j * r (appendedDot Q Λ i ν) := by
  have hl : mixedCrossElem Λ ν i j = p (fj 1) * mixedCrossElem Λ ν i j := by
    rw [mixedCrossElem, ← mul_assoc, ← mul_assoc, fj_one_idem]
  rw [hl, ← mul_assoc, ← appendedDot_commute Q Λ i νj (fj 1), fj_one_mul_appendedDot,
    ← hl, appendBlackAt_appendedDot_eq, appendBlackAt_fi_one_eq, mixedCrossElem_eq_mixedProj,
    ← map_mul, ← map_mul, ← map_mul]
  congr 1
  exact slide_aux (slide_right_K hij)
    (x_commute_doubleLast_one S σ b c _) (x_commute_D' _) (doubleLast_one_mul_self S σ b c)
    D'_idem

/-- **Dot slide on the `j` strand** (KL I, §2.1, (2.4) for distinct labels). -/
theorem appendBlack_appendedDot_mul_mixedCrossElem (hij : i ≠ j) :
    p (appendedDot Q Λ j ν) * mixedCrossElem Λ ν i j =
      mixedCrossElem Λ ν i j * appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j) := by
  have hr : mixedCrossElem Λ ν i j * appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j) =
      mixedCrossElem Λ ν i j * (r (fi 1) * appendedDotAt) := by
    rw [← mul_assoc, mixedCrossElem_mul_one]
  rw [hr, fi_one_mul_appendedDotAt, appendBlack_appendedDot_eq, appendBlack_fj_one_eq,
    mixedCrossElem_eq_mixedProj, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  exact slide_aux (slide_left_K hij)
    (x_commute_doubleLast_one S σ b c _) (x_commute_D' _) (doubleLast_one_mul_self S σ b c)
    D'_idem

/-- **Dot slide on the `i` strand for the mixed crossing** (KL I, §2.1, (2.4), distinct labels;
Rouquier's `τ x = x τ` for `i ≠ j`): `(xᵢ Eⱼ) ≫ τ = τ ≫ (Eⱼ' xᵢ)`. -/
theorem blackDot_whiskerRight_comp_blackMixedCross (hsym : KLRSymm Q) (hij : i ≠ j) :
    Functor.whiskerRight (blackDot Q Λ i νj) (blackE Q Λ j ν) ≫ blackMixedCross hsym hij =
      blackMixedCross hsym hij ≫ Functor.whiskerLeft (blackEAt Λ ν i j) (blackDot Q Λ i ν) :=
  NatTrans.ext (funext fun M => ModuleCat.hom_ext (LinearMap.ext fun w => Res.ext (Res.ext (by
    change op (mixedCrossElem (Q := Q) Λ ν i j) • op (appendedDot Q Λ i νj) • (w.val.val : M) =
      op (r (appendedDot Q Λ i ν)) • op (mixedCrossElem (Q := Q) Λ ν i j) • (w.val.val : M)
    rw [smul_smul, smul_smul, ← op_mul, ← op_mul, appendedDot_mul_mixedCrossElem hij]))))

/-- **Dot slide on the `j` strand for the mixed crossing** (KL I, §2.1, (2.4), distinct
labels): `(Eᵢ xⱼ) ≫ τ = τ ≫ (xⱼ' Eᵢ)`. -/
theorem blackDot_whiskerLeft_comp_blackMixedCross (hsym : KLRSymm Q) (hij : i ≠ j) :
    Functor.whiskerLeft (blackE Q Λ i νj) (blackDot Q Λ j ν) ≫ blackMixedCross hsym hij =
      blackMixedCross hsym hij ≫ Functor.whiskerRight (blackDotAt Λ ν i j) (blackE Q Λ i ν) :=
  NatTrans.ext (funext fun M => ModuleCat.hom_ext (LinearMap.ext fun w => Res.ext (Res.ext (by
    change op (mixedCrossElem (Q := Q) Λ ν i j) • op (p (appendedDot Q Λ j ν)) •
        (w.val.val : M) =
      op (appendedDotAt (Q := Q) (Λ := Λ) (ν := ν) (i := i) (j := j)) •
        op (mixedCrossElem (Q := Q) Λ ν i j) • (w.val.val : M)
    rw [smul_smul, smul_smul, ← op_mul, ← op_mul,
      appendBlack_appendedDot_mul_mixedCrossElem hij]))))

end Categorification.Stendhal
