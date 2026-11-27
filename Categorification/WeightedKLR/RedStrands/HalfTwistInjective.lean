/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistCokernel
import Categorification.WeightedKLR.RedStrands.HalfTwistInclusion
import Categorification.WeightedKLR.RedStrands.BraidingFunctorCompTor
import Categorification.WeightedKLR.RedStrands.BraidLengthInduction
import Categorification.WeightedKLR.RedStrands.BraidedIdentityGrading
import Categorification.WeightedKLR.RedStrands.RightStandardReflection
import Categorification.Algebra.DerivedKernelShift
import Categorification.Algebra.DerivedRightTensorInjective
import Categorification.Algebra.DerivedTensorFiltration

set_option backward.isDefEq.respectTransparency false

/-!
# Injectivity of `ι` in the half twist

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14. For a red-ordered loading `t` with red-first loading `t⁰ = τ_t • t`, left
multiplication by `θ̇_t` embeds the right projective `e(t) T^λ` into `e(t⁰) T^λ` (the reflection
of Lemma 5.25), with cokernel filtered by standard modules. Applying the braiding functor
`- ⊗ᴸ B(κ₁, κ)`, whose higher `Tor` vanish on standardly filtered modules once `B(κ, κ₁)` is
standardly filtered (step `f_n → s_n` of Lemma 6.11), keeps the embedding injective. On the
loading projectives the ordinary braid is the cut `e(t) V e_κ`, so `ι = θ̇_t ·` is injective on
`e(t) V e_κ` (`violShuffleDual_mul_eq_zero`). This discharges the injectivity input of
`halfTwistInclusionEquiv` (`halfTwistInclusionEquivOfFiltration`).

## Main results

* `violShuffleDualCorner`: `θ̇_t` in the corner at `(1, …, ℓ)`, carried by the reflection to the
  red/black shuffle `θ_t` of the tensor product algebra
  (`leftCoefficientEquiv_violShuffleDualCorner`).
* `violShuffleDual_mul_eq_zero`: injectivity of `ι` on `e(t) V e_κ`.
* `halfTwistInclusionEquivOfFiltration`: `e(t) V e_κ ≅ y · e(t⁰) V e_κ`.

Inputs beyond Webster's setting: the hypotheses of Lemma 5.25 (`BaseCrossing`, proved at the
standard Khovanov–Lauda scalars) and of Corollary 5.22 (`AllFiniteDeltaInjective`), and the
standard filtration of `B(κ, κ₁)`, which is Lemma 6.11.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MulOpposite

namespace Categorification

section TensorHomology

universe w u

open DG DG.DerivedCategory
open scoped DG.DegreeZero

variable {A B M N P : Type u} [Ring A] [Ring B] [DG.HasDerivedCategory.{w, u} A]
  [DG.HasDerivedCategory.{w, u} B]
  [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [AddCommGroup N] [Module B N] [AddCommGroup P] [Module B P]

/-- If the derived tensor of a module map is injective in degree zero, then so is every additive
map of ordinary tensor products with the pure-tensor formula of the module map. -/
theorem injective_of_mono_derivedTensorHomologyQ
    (f : DGModuleCat.of B (InDegreeZero N) ⟶ DGModuleCat.of B (InDegreeZero P))
    (τ : TensorProductOver B (InDegreeZero M) (InDegreeZero N) →+
      TensorProductOver B (InDegreeZero M) (InDegreeZero P))
    (hτ : ∀ (m : InDegreeZero M) (n : InDegreeZero N),
      τ (TensorProductOver.tmul B m n) = TensorProductOver.tmul B m (f n))
    (hmono : Mono ((DG.DerivedCategory.homologyFunctor ℤ 0).map
      ((derivedTensor A B M).map (Q.map f)))) :
    Function.Injective τ := by
  let H := DG.DerivedCategory.homologyFunctor (A := A) ℤ 0
  let eX := derivedTensorHomologyIsoOrdinary (A := A) (B := B) (M := M) N
  let eY := derivedTensorHomologyIsoOrdinary (A := A) (B := B) (M := M) P
  have hsq : H.map ((derivedTensor A B M).map (Q.map f)) ≫ eY.hom = eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f)) :=
    derivedTensorHomologyIsoOrdinary_naturality f
  have h₁ : Mono (eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f))) := by
    rw [← hsq]
    infer_instance
  have hm : Mono (H.map (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f))) := by
    have h' := mono_comp (inv eX.hom) (eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f)))
    rwa [IsIso.inv_hom_id_assoc] at h'
  exact injective_of_mono_tensorHomologyQ (A := A) (B := B) (M := M) (N := N) (P := P) f τ hτ hm

end TensorHomology

namespace Stendhal

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k}

/-- A standard module at a violated loading vanishes. -/
theorem subsingleton_leftStandard_of_isViolated (Ω : Fin ℓ → I →₀ ℕ)
    {b : KLR.Seq (stendhalWeight ℓ ν)} (hb : IsRedOrdered b) (hv : IsViolated b) :
    Subsingleton (leftStandard Q Ω b hb) := by
  have hz : seqIdem Q Ω b hb = 0 := by
    change (StendhalAlgebra.violatedIdeal k Q Ω ν).ringCon.mk' (StendhalAlgebra.e b hb) = 0
    rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
    exact TwoSidedIdeal.subset_span ⟨b, hb, hv, rfl⟩
  have h0 (x : lIdeal (seqIdem Q Ω b hb)) : (x : TensorProductAlgebra k Q Ω ν) = 0 :=
    calc (x : TensorProductAlgebra k Q Ω ν) = x * seqIdem Q Ω b hb := x.2.symm
      _ = x * 0 := congrArg (fun z => (x : TensorProductAlgebra k Q Ω ν) * z) hz
      _ = 0 := mul_zero _
  have : Subsingleton (lIdeal (seqIdem Q Ω b hb)) :=
    ⟨fun x y => Subtype.ext ((h0 x).trans (h0 y).symm)⟩
  exact (Submodule.Quotient.mk_surjective _).subsingleton

namespace BraidedStendhalAlgebra

open KLR KLRAlgebra Equiv CornerEndomorphism ModuleFiltration DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {Λ : Fin ℓ → I →₀ ℕ}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)

local notation "μ" => stendhalWeight ℓ ν
set_option quotPrecheck false in
local notation "κ₁" => List.map ⇑(1 : Perm (Fin ℓ)) (List.finRange ℓ)
set_option quotPrecheck false in
local notation "C" κ:arg => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
set_option quotPrecheck false in
local notation "T₁" => TensorProductAlgebra k Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) ν
set_option quotPrecheck false in
local notation "F" => leftCoefficientEquiv (Λ := Λ) hρ hQ 1
local notation "ι" => ofKLR k Q Λ ν
local notation "q" => violMk k Q Λ ν

omit [DecidableEq I] in
theorem redWord_eq_one_finRange {t : Seq μ} (ht : IsRedOrdered t) : redWord t = κ₁ := by
  rw [(redWord_eq_finRange_iff t).2 ht]
  simp

theorem redProj_mul_violShuffleDual {t : Seq μ} (ht : IsRedOrdered t) {κ : List (Fin ℓ)}
    (hκ : redWord t = κ) :
    q (redProj k Q Λ ν κ) * violShuffleDual (k := k) (Q := Q) (Λ := Λ) t =
      violShuffleDual (k := k) (Q := Q) (Λ := Λ) t := by
  have h0 : redWord (redShufflePerm t • t) = κ := by
    rw [← hκ, (redWord_eq_finRange_iff _).2 ht,
      (redWord_eq_finRange_iff _).2 (isRedOrdered_redShuffle ht)]
  rw [violShuffleDual, ← map_mul, map_mul ι, map_mul ι, ← mul_assoc, ← mul_assoc, redProj_mul_e,
    ite_eq_left h0]

theorem violShuffleDual_mul_redProj {t : Seq μ} {κ : List (Fin ℓ)} (hκ : redWord t = κ) :
    violShuffleDual (k := k) (Q := Q) (Λ := Λ) t * q (redProj k Q Λ ν κ) =
      violShuffleDual (k := k) (Q := Q) (Λ := Λ) t := by
  rw [violShuffleDual, ← map_mul, map_mul ι (_ * _), mul_assoc, e_mul_redProj, ite_eq_left hκ]

/-- The mirror image `θ̇_t ∈ e(t⁰) V e(t)` of the red/black shuffle, in the corner at
`(1, …, ℓ)`. -/
def violShuffleDualCorner {t : Seq μ} (ht : IsRedOrdered t) : C κ₁ :=
  ⟨violShuffleDual (k := k) (Q := Q) (Λ := Λ) t,
    (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν κ₁)).2
      ⟨redProj_mul_violShuffleDual ht (redWord_eq_one_finRange ht),
        violShuffleDual_mul_redProj (redWord_eq_one_finRange ht)⟩⟩

/-- The affine projection of the red/black shuffle diagram is the red/black shuffle. -/
theorem stendhalTensorProjection_shuffle {t : Seq μ} (ht : IsRedOrdered t) :
    stendhalTensorProjection (Q := Q) Λ ν (KLRAlgebra.e t *
        ψw (TypeA.canWord (Multiset.card μ) (redShufflePerm t)⁻¹) *
        KLRAlgebra.e (redShufflePerm t • t)) = redShuffle Q Λ t ht := by
  apply congrArg (TensorProductAlgebra.mk Q Λ ν)
  apply Subtype.ext
  change StendhalAlgebraAllOrders.ofKLR k Q Λ ν (KLRAlgebra.e t *
      ψw (TypeA.canWord (Multiset.card μ) (redShufflePerm t)⁻¹) *
      KLRAlgebra.e (redShufflePerm t • t)) * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν =
    StendhalAlgebraAllOrders.e t * StendhalAlgebraAllOrders.ofKLR k Q Λ ν
      (ψw (TypeA.canWord (Multiset.card μ) (redShufflePerm t)⁻¹)) *
      StendhalAlgebraAllOrders.e (redShufflePerm t • t)
  rw [map_mul, map_mul, mul_assoc]
  change _ * (StendhalAlgebraAllOrders.e (redShufflePerm t • t) *
    StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) = _
  rw [StendhalAlgebraAllOrders.e_mul_redOrderedIdem,
    ite_eq_left_of_eq_true _ _ (eq_true (isRedOrdered_redShuffle ht))]
  rfl

/-- **`θ̇_t` reflects to `θ_t`**: the coefficient change from the corner at `(1, …, ℓ)` to the
tensor product algebra sends `θ̇_t` to the red/black shuffle `θ_t`. -/
theorem leftCoefficientEquiv_violShuffleDualCorner {t : Seq μ} (ht : IsRedOrdered t) :
    F (op (violShuffleDualCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ht)) =
      redShuffle Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) t ht := by
  let a : KLRAlgebra k (stendhalQ Q Λ) μ := KLRAlgebra.e (redShufflePerm t • t) *
    ψw (TypeA.canWord (Multiset.card μ) (redShufflePerm t)⁻¹).reverse * KLRAlgebra.e t
  let d := affineDiagramInIdentityCorner (Q := Q) (Λ := Λ) (ν := ν) a
  have hd : d.1 = (violShuffleDualCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ht).1 := by
    have hval : d.1 = q (redProj k Q Λ ν (List.finRange ℓ)) * q (ι a) *
        q (redProj k Q Λ ν (List.finRange ℓ)) := by
      change q (redProj k Q Λ ν (List.finRange ℓ) * ι a * redProj k Q Λ ν (List.finRange ℓ)) = _
      rw [map_mul, map_mul]
    rw [hval]
    change q (redProj k Q Λ ν (List.finRange ℓ)) * violShuffleDual (k := k) (Q := Q) (Λ := Λ) t *
      q (redProj k Q Λ ν (List.finRange ℓ)) = violShuffleDual (k := k) (Q := Q) (Λ := Λ) t
    rw [redProj_mul_violShuffleDual ht ((redWord_eq_finRange_iff t).2 ht),
      violShuffleDual_mul_redProj ((redWord_eq_finRange_iff t).2 ht)]
  rw [leftCoefficientEquiv_one_op hρ hQ hd]
  change tensorFlip (violCornerEquiv hρ hQ d) = _
  rw [violCornerEquiv_diagonal hρ hQ a]
  have ha : a = hflip (KLRAlgebra.e t *
      ψw (TypeA.canWord (Multiset.card μ) (redShufflePerm t)⁻¹) *
      KLRAlgebra.e (redShufflePerm t • t)) := by
    simp only [a, hflip_mul, hflip_e, hflip_ψw, mul_assoc]
  rw [ha, ← tensorFlip_projection, tensorFlip_tensorFlip, stendhalTensorProjection_shuffle ht]
  rfl


section Injective

variable {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q) (hbase : BaseCrossing Q)

theorem violLoadingIdem_mul_violShuffleDualCorner {t : Seq μ} (ht : IsRedOrdered t) :
    violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel 1 (isRedOrdered_redShuffle ht)) *
        violShuffleDualCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ht =
      violShuffleDualCorner ht := by
  apply Subtype.ext
  change q (ι (KLRAlgebra.e (Seq.redPerm 1 (redShufflePerm t • t)))) *
    violShuffleDual (k := k) (Q := Q) (Λ := Λ) t = violShuffleDual (k := k) (Q := Q) (Λ := Λ) t
  rw [Seq.redPerm_one, violShuffleDual, ← map_mul, map_mul ι (_ * _), map_mul ι (KLRAlgebra.e _),
    ← mul_assoc, ← mul_assoc, ← map_mul ι, KLRAlgebra.e_mul_e,
    ite_eq_left_of_eq_true _ _ (eq_true rfl)]

/-- Reflection of a loading right ideal of the corner at `(1, …, ℓ)` to the loading left ideal
of the tensor product algebra, `x ↦ F(op x)`. -/
def loadingRightIdealEquiv {s : Seq μ} (hs : IsRedOrdered s) :
    rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel 1 hs)) ≃ₛₗ[
      (F : (C κ₁)ᵐᵒᵖ →+* T₁)] lIdeal (seqIdem Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) s hs) := by
  let G := leftCoefficientEquiv (Λ := Λ) hρ hQ 1
  let f := violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel 1 hs)
  have hf : G (op f) = seqIdem Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) s hs :=
    leftCoefficientEquiv_loadingIdem hρ hQ 1 hs
  refine { toFun := fun p => ⟨G (op p.1), ?_⟩
           invFun := fun p => ⟨unop (G.symm p.1), ?_⟩
           map_add' := fun x y => Subtype.ext (map_add G (op x.1) (op y.1))
           map_smul' := fun a x => Subtype.ext (map_mul G a (op x.1))
           left_inv := fun x => Subtype.ext (congrArg unop (G.symm_apply_apply (op x.1)))
           right_inv := fun x => Subtype.ext (G.apply_symm_apply x.1) }
  · change G (op p.1) * seqIdem Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) s hs = G (op p.1)
    rw [← hf, ← map_mul, ← op_mul, show f * p.1 = p.1 from p.2]
  · apply mem_rIdeal.2
    apply op_injective
    apply G.injective
    change G (op (f * (G.symm p.1).unop)) = G (G.symm p.1)
    rw [op_mul, op_unop, map_mul, hf, G.apply_symm_apply,
      show p.1 * seqIdem Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) s hs = p.1 from p.2]

theorem loadingRightIdealEquiv_val {s : Seq μ} (hs : IsRedOrdered s)
    (x : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel 1 hs))) :
    (loadingRightIdealEquiv (Λ := Λ) hρ hQ hs x).1 = F (op x.1) :=
  rfl

/-- `ι = θ̇_t ·` on the loading right ideals of the corner at `(1, …, ℓ)`. -/
def shuffleDualMul {t : Seq μ} (ht : IsRedOrdered t) :
    rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel 1 ht)) →ₗ[(C κ₁)ᵐᵒᵖ]
      rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ)
        (redWord_relabel 1 (isRedOrdered_redShuffle ht))) where
  toFun x := ⟨violShuffleDualCorner ht * x.1, by
    change _ * _ = _
    rw [← mul_assoc, violLoadingIdem_mul_violShuffleDualCorner]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (mul_assoc _ _ _).symm

theorem loadingRightIdealEquiv_shuffleDualMul {t : Seq μ} (ht : IsRedOrdered t)
    (x : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel 1 ht))) :
    loadingRightIdealEquiv (Λ := Λ) hρ hQ (isRedOrdered_redShuffle ht) (shuffleDualMul ht x) =
      shuffleMul Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) t ht (loadingRightIdealEquiv (Λ := Λ) hρ hQ ht x) := by
  apply Subtype.ext
  change F (op (violShuffleDualCorner ht * x.1)) = F (op x.1) * redShuffle Q _ t ht
  rw [op_mul, map_mul, leftCoefficientEquiv_violShuffleDualCorner]

/-- The cokernel of `θ̇_t ·`: the reflection of the cokernel of Lemma 5.25. -/
abbrev shuffleDualCokernel {t : Seq μ} (ht : IsRedOrdered t) : ModuleCat.{0} (C κ₁)ᵐᵒᵖ :=
  (ModuleCat.restrictScalars (F : (C κ₁)ᵐᵒᵖ →+* T₁)).obj
    (ModuleCat.of T₁ (shuffleCokernel Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) t ht))

/-- The quotient map onto the cokernel of `θ̇_t ·`. -/
def shuffleDualQuot {t : Seq μ} (ht : IsRedOrdered t) :
    rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ)
      (redWord_relabel 1 (isRedOrdered_redShuffle ht))) →ₗ[(C κ₁)ᵐᵒᵖ]
      shuffleDualCokernel (Λ := Λ) hρ hQ ht where
  toFun x := shuffleCokernel.mk Q _ t ht
    (loadingRightIdealEquiv (Λ := Λ) hρ hQ (isRedOrdered_redShuffle ht) x)
  map_add' x y := by rw [LinearEquiv.map_add, LinearMap.map_add]
  map_smul' a x := by
    rw [LinearEquiv.map_smulₛₗ, LinearMap.map_smul]
    rfl

include hρ hQ hR hbase in
theorem shuffleDualMul_injective {t : Seq μ} (ht : IsRedOrdered t) :
    Function.Injective (shuffleDualMul (k := k) (Q := Q) (Λ := Λ) (ν := ν) ht) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  apply (loadingRightIdealEquiv (Λ := Λ) hρ hQ ht).injective
  rw [LinearEquiv.map_zero]
  apply Subtype.ext
  refine mul_redShuffle_injective hR hQ hbase (Λ ∘ ⇑(1 : Perm (Fin ℓ))) t ht _
    (loadingRightIdealEquiv (Λ := Λ) hρ hQ ht x).2 ?_
  have h := congrArg Subtype.val (loadingRightIdealEquiv_shuffleDualMul hρ hQ ht x)
  rw [hx, LinearEquiv.map_zero] at h
  exact h.symm

theorem shuffleDualQuot_surjective {t : Seq μ} (ht : IsRedOrdered t) :
    Function.Surjective (shuffleDualQuot (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ ht) :=
  (shuffleCokernel.mk_surjective (Q := Q) (Λ := Λ ∘ ⇑(1 : Perm (Fin ℓ))) t ht).comp (loadingRightIdealEquiv (Λ := Λ) hρ hQ _).surjective

theorem shuffleDual_exact {t : Seq μ} (ht : IsRedOrdered t) :
    Function.Exact (shuffleDualMul (k := k) (Q := Q) (Λ := Λ) (ν := ν) ht)
      (shuffleDualQuot (Λ := Λ) hρ hQ ht) := by
  intro y
  constructor
  · intro h
    obtain ⟨z, hz⟩ : loadingRightIdealEquiv (Λ := Λ) hρ hQ (isRedOrdered_redShuffle ht) y ∈
        shuffleRange Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) t ht :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    refine ⟨(loadingRightIdealEquiv (Λ := Λ) hρ hQ ht).symm z, ?_⟩
    apply (loadingRightIdealEquiv (Λ := Λ) hρ hQ (isRedOrdered_redShuffle ht)).injective
    rw [loadingRightIdealEquiv_shuffleDualMul, LinearEquiv.apply_symm_apply]
    exact hz
  · rintro ⟨x, rfl⟩
    change shuffleCokernel.mk Q _ t ht (loadingRightIdealEquiv (Λ := Λ) hρ hQ _
      (shuffleDualMul ht x)) = 0
    rw [loadingRightIdealEquiv_shuffleDualMul]
    exact shuffleCokernel.mk_shuffleMul (Q := Q) (Λ := Λ ∘ ⇑(1 : Perm (Fin ℓ))) t ht _

include hρ hQ in
/-- The short exact sequence `0 → e(t) T → e(t⁰) T → coker → 0` of right corner modules. -/
def shuffleDualShortComplex {t : Seq μ} (ht : IsRedOrdered t) :
    ShortComplex (ModuleCat.{0} (C κ₁)ᵐᵒᵖ) :=
  ShortComplex.mk (ModuleCat.ofHom
      (X := ↥(rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel 1 ht))))
      (Y := ↥(rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ)
        (redWord_relabel 1 (isRedOrdered_redShuffle ht)))))
      (shuffleDualMul (k := k) (Q := Q) (Λ := Λ) (ν := ν) ht))
    (ModuleCat.ofHom (X := ↥(rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ)
        (redWord_relabel 1 (isRedOrdered_redShuffle ht)))))
      (Y := ↑(shuffleDualCokernel (Λ := Λ) hρ hQ ht))
      (shuffleDualQuot (Λ := Λ) hρ hQ ht))
    (by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change shuffleDualQuot (Λ := Λ) hρ hQ ht (shuffleDualMul ht x) = 0
      exact (shuffleDual_exact (Λ := Λ) hρ hQ ht _).2 ⟨x, rfl⟩)

include hR hbase in
theorem shuffleDualShortComplex_shortExact {t : Seq μ} (ht : IsRedOrdered t) :
    (shuffleDualShortComplex (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ ht).ShortExact :=
  { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      (shuffleDual_exact (Λ := Λ) hρ hQ ht)
    mono_f := (ModuleCat.mono_iff_injective _).mpr (shuffleDualMul_injective (Λ := Λ) hρ hQ hR hbase ht)
    epi_g := (ModuleCat.epi_iff_surjective _).mpr (shuffleDualQuot_surjective (Λ := Λ) hρ hQ ht) }

/-- A reflected standard module is the loading standard of the corner at `(1, …, ℓ)`. -/
def restrictLeftStandardEquiv {b : Seq μ} (hb : IsRedOrdered b) :
    (ModuleCat.restrictScalars (F : (C κ₁)ᵐᵒᵖ →+* T₁)).obj
        (ModuleCat.of T₁ (leftStandard Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) b hb)) ≃ₗ[(C κ₁)ᵐᵒᵖ]
      ModuleCat.of (C κ₁)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm 1 b) κ₁) :=
  { (loadingStandardLeftEquiv (Λ := Λ) hρ hQ 1 hb).symm.toEquiv with
    map_add' := (loadingStandardLeftEquiv (Λ := Λ) hρ hQ 1 hb).symm.map_add
    map_smul' := fun a x => by
      convert (loadingStandardLeftEquiv (Λ := Λ) hρ hQ 1 hb).symm.map_smulₛₗ (F a) x using 2 <;>
        first | rfl | exact ((leftCoefficientEquiv (Λ := Λ) hρ hQ 1).symm_apply_apply a).symm }

include hR hbase in
/-- **The cokernel of `θ̇_t ·` is standardly filtered** (Webster, arXiv:1309.3796v3, Lemma 5.25,
reflected): it has a filtration by the loading standards of the corner at `(1, …, ℓ)`. -/
theorem exists_hasFiltration_shuffleDualCokernel
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    {t : Seq μ} (ht : IsRedOrdered t) :
    ∃ m : List {s : Seq μ // redWord s = κ₁ ∧ ¬ IsViolated s},
      HasFiltration (fun s => ModuleCat.of (C κ₁)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ₁)) m
        (shuffleDualCokernel (Λ := Λ) hρ hQ ht) := by
  obtain ⟨l, -, hl⟩ :=
    exists_hasFiltration_shuffleCokernel hR hQ hbase hall (Λ ∘ ⇑(1 : Perm (Fin ℓ))) t ht
  have h1 := hl.restrictScalars (F : (C κ₁)ᵐᵒᵖ →+* T₁)
  classical
  refine ⟨_, h1.bind (M := fun j =>
    if hv : IsViolated (phiBottom (redShufflePerm t • t) j.1) then [] else
      [⟨Seq.redPerm 1 (phiBottom (redShufflePerm t • t) j.1),
        redWord_relabel 1 (j.isRedOrdered (isRedOrdered_redShuffle ht)),
        by rwa [Seq.redPerm_one]⟩]) fun j => ?_⟩
  split_ifs with hv
  · exact .zero (subsingleton_leftStandard_of_isViolated _ _ hv)
  · exact .single (restrictLeftStandardEquiv (Λ := Λ) hρ hQ _)

end Injective


section Braid

variable {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q) (hbase : BaseCrossing Q)

/-- `ι = θ̇_t ·` on the cuts `e(t) V e_κ`. -/
def shuffleDualCut {t : Seq μ} (ht : IsRedOrdered t) (κ : List (Fin ℓ)) :
    violCorner k Q Λ ν (Seq.redPerm 1 t) κ →+
      violCorner k Q Λ ν (Seq.redPerm 1 (redShufflePerm t • t)) κ where
  toFun y := ⟨violShuffleDual (k := k) (Q := Q) (Λ := Λ) t * y.1, mem_violCorner_iff.2
    ⟨by rw [← mul_assoc]
        exact congrArg (· * y.1) (congrArg Subtype.val
          (violLoadingIdem_mul_violShuffleDualCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ht)),
      by rw [mul_assoc, (mem_violCorner_iff.1 y.2).2]⟩⟩
  map_zero' := Subtype.ext (mul_zero _)
  map_add' y y' := Subtype.ext (mul_add _ _ _)

include hρ hR hbase in
/-- **`ι` is injective** (Webster, arXiv:1309.3796v3, proof of Theorem 6.14), at the loading
`Seq.redPerm 1 t = t`: if `B(κ, (1, …, ℓ))` is standardly filtered as a right module over the
corner at `(1, …, ℓ)`, then left multiplication by `θ̇_t` is injective on `e(t) V e_κ`. The
embedding `e(t) T → e(t⁰) T` has a standardly filtered cokernel (Lemma 5.25), on which the
braiding functor has no `Tor` in degree `-1`; on loading projectives the ordinary braid is the
cut. -/
theorem shuffleDualCut_injective
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    {κ : List (Fin ℓ)}
    [DG.HasDerivedCategory.{w, 0} (C κ₁)] [DG.HasDerivedCategory.{w, 0} ℤ]
    [DG.HasDerivedCategory.{w, 0} (C κ₁)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (C κ)ᵐᵒᵖ]
    {m : List {s : Seq μ // redWord s = κ₁ ∧ ¬ IsViolated s}}
    (hf : HasFiltration (fun s => ModuleCat.of (C κ₁)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ₁)) m
      (ModuleCat.of (C κ₁)ᵐᵒᵖ ↥(braidingBimodule k Q Λ ν κ κ₁)))
    {t : Seq μ} (ht : IsRedOrdered t) :
    Function.Injective (shuffleDualCut (k := k) (Q := Q) (Λ := Λ) (ν := ν) ht κ) := by
  let S₀ := shuffleDualShortComplex (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ ht
  let S := S₀.map (degreeZeroModuleFunctor (C κ₁)ᵐᵒᵖ)
  have hS : S.ShortExact :=
    degreeZeroModuleFunctor_shortExact _ (shuffleDualShortComplex_shortExact (Λ := Λ) hρ hQ hR hbase ht)
  obtain ⟨m', hX⟩ := exists_hasFiltration_shuffleDualCokernel (Λ := Λ) hρ hQ hR hbase hall ht
  let D := orderedStandardCovers Q (Λ ∘ ⇑(1 : Perm (Fin ℓ)))
    (fun s => exists_hasFiltration_leftUpper Q hQ hR hall (Λ ∘ ⇑(1 : Perm (Fin ℓ))) ν s.1 s.2)
  have hN := isZero_braidingFunctor_homology_of_standardFiltration.{w} hρ hQ 1 D hf hX (-1)
    (by decide)
  have hmono := DG.DerivedCategory.mono_homology_kernel_of_shortExact ℤ
    (braidingFunctor.{w} k Q Λ ν κ₁ κ) S hS hN
  let eX := loadingProjectiveTensorEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) (κ := κ)
    (redWord_relabel 1 ht)
  let eY := loadingProjectiveTensorEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) (κ := κ)
    (redWord_relabel 1 (isRedOrdered_redShuffle ht))
  let τ := eY.symm.toAddEquiv.toAddMonoidHom.comp
    ((shuffleDualCut (k := k) (Q := Q) (Λ := Λ) (ν := ν) ht κ).comp
      eX.toAddEquiv.toAddMonoidHom)
  have hτ := injective_of_mono_derivedTensorHomologyQ
    (A := (C κ)ᵐᵒᵖ) (B := (C κ₁)ᵐᵒᵖ)
    (M := OpBimodule (C κ₁) ↥(braidingBimodule k Q Λ ν κ₁ κ)) S.f τ (fun b p => by
      apply eY.injective
      change eY (eY.symm _) = _
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (mul_assoc _ _ _).symm) hmono
  intro y y' hyy
  apply eX.symm.injective
  apply hτ
  change eY.symm (shuffleDualCut ht κ (eX (eX.symm y))) =
    eY.symm (shuffleDualCut ht κ (eX (eX.symm y')))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hyy]

include hρ hR hbase in
/-- **`ι` is injective on `e(t) V e_κ`** (Webster, arXiv:1309.3796v3, proof of Theorem 6.14),
given the standard filtration of `B(κ, (1, …, ℓ))` (Lemma 6.11). -/
theorem violShuffleDual_mul_eq_zero
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    {κ : List (Fin ℓ)}
    [DG.HasDerivedCategory.{w, 0} (C κ₁)] [DG.HasDerivedCategory.{w, 0} ℤ]
    [DG.HasDerivedCategory.{w, 0} (C κ₁)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (C κ)ᵐᵒᵖ]
    {m : List {s : Seq μ // redWord s = κ₁ ∧ ¬ IsViolated s}}
    (hf : HasFiltration (fun s => ModuleCat.of (C κ₁)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ₁)) m
      (ModuleCat.of (C κ₁)ᵐᵒᵖ ↥(braidingBimodule k Q Λ ν κ κ₁)))
    {t : Seq μ} (ht : IsRedOrdered t) {v : ViolQuotient k Q Λ ν}
    (hv : v ∈ violCorner k Q Λ ν t κ)
    (h0 : violShuffleDual (k := k) (Q := Q) (Λ := Λ) t * v = 0) : v = 0 := by
  have hv' : v ∈ violCorner k Q Λ ν (Seq.redPerm 1 t) κ := by rwa [Seq.redPerm_one]
  have h := shuffleDualCut_injective.{w} hρ hQ hR hbase hall hf ht
    (a₁ := ⟨v, hv'⟩) (a₂ := 0) (by
      rw [map_zero]
      exact Subtype.ext h0)
  exact congrArg Subtype.val h

include hρ hR hbase in
/-- **`ι` as an isomorphism onto its image** (Webster, arXiv:1309.3796v3, proof of
Theorem 6.14): when `κ` reverses every pair of red strands and `B(κ, (1, …, ℓ))` is standardly
filtered, `ι = θ̇_t ·` identifies `e(t) V e_κ` with `y · e(t⁰) V e_κ`. -/
def halfTwistInclusionEquivOfFiltration
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    (κ : List (Fin ℓ)) (hκ : ∀ t' : Seq μ, redWord t' = κ → IsRedReversed t')
    [DG.HasDerivedCategory.{w, 0} (C κ₁)] [DG.HasDerivedCategory.{w, 0} ℤ]
    [DG.HasDerivedCategory.{w, 0} (C κ₁)ᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} (C κ)ᵐᵒᵖ]
    {m : List {s : Seq μ // redWord s = κ₁ ∧ ¬ IsViolated s}}
    (hf : HasFiltration (fun s => ModuleCat.of (C κ₁)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ₁)) m
      (ModuleCat.of (C κ₁)ᵐᵒᵖ ↥(braidingBimodule k Q Λ ν κ κ₁)))
    (t : Seq μ) (ht : IsRedOrdered t) :
    violCorner k Q Λ ν t κ ≃ₗ[k]
      (violCorner k Q Λ ν (redShufflePerm t • t) κ).map
        (LinearMap.mulLeft k (halfTwistY (k := k) (Q := Q) (Λ := Λ) t)) :=
  halfTwistInclusionEquiv hQ t ht κ hκ fun _ hv h0 =>
    violShuffleDual_mul_eq_zero.{w} hρ hQ hR hbase hall hf ht hv h0

end Braid

end BraidedStendhalAlgebra


namespace FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF Equiv
open BraidedStendhalAlgebra ModuleFiltration CategoryTheory CategoryTheory.Limits
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (κ : List (Fin ℓ)),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Ω) (ν := ν) κ)]
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (κ : List (Fin ℓ)),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Ω) (ν := ν) κ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} ℤ]

include hR in
/-- **The braiding bimodule `B(w (1, …, ℓ), (1, …, ℓ))` is standardly filtered** over the corner
at `(1, …, ℓ)` (Webster, arXiv:1309.3796v2, Lemma 6.11, for `𝔅_{w⁻¹}`), written with the red
order `1 ∘ (1, …, ℓ)`. Route hypotheses: those of Corollary 6.10. -/
theorem exists_hasFiltration_braidingBimodule_one
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (H : ∀ (n m : ℕ), n + 2 + m = ℓ → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
      (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []),
      RowFigureFiveHypotheses C hQ Ω u hu)
    (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    (ν : Multiset I) (w : Perm (Fin ℓ)) (hw : w ≠ 1) :
    ∃ m : List {s : Seq (stendhalWeight ℓ ν) //
        redWord s = (List.finRange ℓ).map ⇑(1 : Perm (Fin ℓ)) ∧ ¬ IsViolated s},
      HasFiltration (fun s => ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
          ((List.finRange ℓ).map ⇑(1 : Perm (Fin ℓ))))ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val
          ((List.finRange ℓ).map ⇑(1 : Perm (Fin ℓ))))) m
        (ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
          ((List.finRange ℓ).map ⇑(1 : Perm (Fin ℓ))))ᵐᵒᵖ
          ↥(braidingBimodule k Q Λ ν ((List.finRange ℓ).map w)
            ((List.finRange ℓ).map ⇑(1 : Perm (Fin ℓ))))) := by
  have hs := fun (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t) =>
    hasCornerStandardFiltration_braidF.{0} C hQ hR hall H w⁻¹ (inv_ne_one.2 hw)
      ((Λ ∘ ⇑(1 : Perm (Fin ℓ))) ∘ w) ((wt ∘ ⇑(1 : Perm (Fin ℓ))) ∘ w)
      (fun r i => hwt ((1 : Perm (Fin ℓ)) (w r)) i) t ht
  obtain ⟨m, hf⟩ := exists_hasFiltration_braidingBimodule (k := k) (Q := Q) (Λ := Λ) (ν := ν)
    ((List.finRange ℓ).map ⇑((1 : Perm (Fin ℓ)) * w)) ((List.finRange ℓ).map ⇑(1 : Perm (Fin ℓ)))
    fun u hu => by
      have hu' : redWord (Seq.redPerm (1 : Perm (Fin ℓ))⁻¹ u) = (List.finRange ℓ).map w := by
        rw [redWord_redPerm, hu, List.map_map]
        ext1
        simp
      have h2 := exists_hasFiltration_violCorner_relabel (k := k) (Q := Q) (Λ := Λ) (ν := ν) 1
        (exists_hasFiltration_violCorner_of_braidFunctor_inv (isReducedChoice_canChoice ν)
          hQ.klrSymm hQ (Λ ∘ ⇑(1 : Perm (Fin ℓ))) w hs _ hu')
      rwa [Seq.redPerm_redPerm, mul_inv_cancel, Seq.redPerm_one] at h2
  rw [one_mul] at hf
  exact ⟨m, hf⟩

include hR in
/-- **`ι` is injective** (Webster, arXiv:1309.3796v3, proof of Theorem 6.14): for a red-ordered
loading `t` and the bottom red order `w (1, …, ℓ)` with `w ≠ 1`, left multiplication by `θ̇_t` is
injective on `e(t) V e_{w(1, …, ℓ)}`. Route hypotheses: those of Corollary 6.10
(`AllFiniteDeltaInjective`, `RowFigureFiveHypotheses`, through Lemma 6.11) and `BaseCrossing`
(Lemma 5.25; proved at the standard Khovanov–Lauda scalars). -/
theorem violShuffleDual_mul_eq_zero (hbase : BaseCrossing Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (H : ∀ (n m : ℕ), n + 2 + m = ℓ → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
      (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []),
      RowFigureFiveHypotheses C hQ Ω u hu)
    (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    (ν : Multiset I) (w : Perm (Fin ℓ)) (hw : w ≠ 1) {t : Seq (stendhalWeight ℓ ν)}
    (ht : IsRedOrdered t) {v : ViolQuotient k Q Λ ν}
    (hv : v ∈ violCorner k Q Λ ν t ((List.finRange ℓ).map w))
    (h0 : violShuffleDual (k := k) (Q := Q) (Λ := Λ) t * v = 0) : v = 0 := by
  obtain ⟨m, hf⟩ := exists_hasFiltration_braidingBimodule_one C hQ hR hall H Λ wt hwt ν w hw
  exact BraidedStendhalAlgebra.violShuffleDual_mul_eq_zero.{0} (isReducedChoice_canChoice ν)
    hQ.klrSymm hQ hbase hall hf ht hv h0

include hR in
/-- **`ι` as an isomorphism onto its image** (Webster, arXiv:1309.3796v3, proof of
Theorem 6.14): when `w (1, …, ℓ)` reverses every pair of red strands (`w ≠ 1`),
`e(t) V e_{w(1, …, ℓ)} ≅ y · e(t⁰) V e_{w(1, …, ℓ)}`. Route hypotheses: as for
`violShuffleDual_mul_eq_zero`. -/
def halfTwistInclusionEquiv (hbase : BaseCrossing Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (H : ∀ (n m : ℕ), n + 2 + m = ℓ → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
      (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []),
      RowFigureFiveHypotheses C hQ Ω u hu)
    (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    (ν : Multiset I) (w : Perm (Fin ℓ)) (hw : w ≠ 1)
    (hκ : ∀ t' : Seq (stendhalWeight ℓ ν), redWord t' = (List.finRange ℓ).map w → IsRedReversed t')
    (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t) :
    violCorner k Q Λ ν t ((List.finRange ℓ).map w) ≃ₗ[k]
      (violCorner k Q Λ ν (redShufflePerm t • t) ((List.finRange ℓ).map w)).map
        (LinearMap.mulLeft k (halfTwistY (k := k) (Q := Q) (Λ := Λ) t)) :=
  BraidedStendhalAlgebra.halfTwistInclusionEquiv hQ.klrSymm t ht _ hκ fun _ hv h0 =>
    violShuffleDual_mul_eq_zero C hQ hR hbase hall H Λ wt hwt ν w hw ht hv h0

end FirstWeight

end Stendhal

end Categorification
