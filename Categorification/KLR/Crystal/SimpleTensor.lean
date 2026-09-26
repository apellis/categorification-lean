/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Delta

/-!
# Simple `R(μ) ⊗ R(ni)`-modules are of the form `N ⊠ L(i^n)`

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2 (TeX lines 2088–2163). The arguments of §3.2 (and of
Kleshchev's book, §5.1, which they follow) use that the irreducible `R(ν - ni) ⊗ R(ni)`-modules
are the modules `N ⊗ L(i^n)` with `N` an irreducible `R(ν - ni)`-module, `L(i^n)` being the unique
irreducible `R(ni)`-module (KL I §2.2, `Categorification.KLR.SimpleNilHecke`).

We prove this for ungraded finite-dimensional modules over any field `k`, in the category of
modules on which the dots of the second factor act nilpotently (this holds for all graded
finite-dimensional modules, the dots having positive degree; without it the statement fails:
`R(i) = k[x]` has the simple modules `k[x]/(x - c)`).

Let `ν'` be a weight all of whose labels are `i` (`hν'`), `n = card ν'`, and
`L = L(i^n) = k[x_1, …, x_n]/(Sym⁺)` (`KLRAlgebra.KLRRep hν' Q`).

## Main results

* `KLRAlgebra.exists_tmul_one_mem` (**lowering**): every nonzero `R(μ) ⊗ R(ν')`-submodule of
  `V ⊠ L` contains a vector `w ⊗ [1]` with `w ≠ 0`. The proof: a nonzero vector killed by all
  dots lies in `V ⊗ k[x^δ]` (KL I Lemma 2.1, `NilHecke.coinvSocle_eq_span_xDelta`), and
  `ψ_{w_0} [x^δ] = [1]`.
* `KLRAlgebra.isSimpleModule_extTensor` : **`N ⊠ L(i^n)` is simple if `N` is**.
* `KLRAlgebra.hwSub`, `KLRAlgebra.HWSpace` : for an `R(μ) ⊗ R(ν')`-module `S`, the vectors
  killed by all crossings `1 ⊗ ψ_j`, an `R(μ)`-module.
* `KLRAlgebra.isSimpleModule_hwSpace`, `KLRAlgebra.hwEquiv` : **if `S` is simple,
  finite-dimensional, and the dots `1 ⊗ x_b` act nilpotently, then `S ≅ HW(S) ⊠ L(i^n)` with
  `HW(S)` simple**. The symmetric polynomials without constant term in the dots of the second
  factor act by zero (they are central and nilpotent), and `v ⊗ [p] ↦ (1 ⊗ p(x)) v` is an
  isomorphism.

The results about `HW(S)` assume the hypotheses of the basis theorem (`hPQ`, `hP`), used only
to know that symmetric polynomials are central in `R(ν')` (`KLRAlgebra.polNu_mem_center`).
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite Categorification.NilHecke
open scoped TensorProduct

variable {I : Type*} [DecidableEq I]

/-! ### Nilpotent actions -/

section Nilpotent

variable {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]

/-- `a` acts nilpotently on `M`. -/
def SmulNilpotent (a : A) (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∃ N : ℕ, ∀ v : M, a ^ N • v = 0

/-- A central element acting nilpotently on a simple module acts by zero. -/
theorem smul_eq_zero_of_smulNilpotent [IsSimpleModule A M] {z : A} (hz : ∀ a, Commute z a)
    (hnil : SmulNilpotent z M) (v : M) : z • v = 0 := by
  let P : Submodule A M :=
    { carrier := {v | z • v = 0}
      add_mem' := fun ha hb => by
        simp only [Set.mem_setOf_eq, smul_add] at *; rw [ha, hb, add_zero]
      zero_mem' := smul_zero z
      smul_mem' := fun a v hv => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_smul, (hz a).eq, mul_smul, hv, smul_zero] }
  rcases IsSimpleOrder.eq_bot_or_eq_top P with hP | hP
  · exfalso
    obtain ⟨N, hN⟩ := hnil
    have hz0 : ∀ w : M, z • w = 0 → w = 0 := fun w hw => by
      have : w ∈ P := hw
      rw [hP] at this
      exact (Submodule.mem_bot A).1 this
    have hinj : ∀ m : ℕ, ∀ w : M, z ^ m • w = 0 → w = 0 := by
      intro m
      induction m with
      | zero => intro w hw; rwa [pow_zero, one_smul] at hw
      | succ m ih => intro w hw; rw [pow_succ, mul_smul] at hw; exact hz0 w (ih _ hw)
    haveI := IsSimpleModule.nontrivial A M
    obtain ⟨w, hw⟩ := exists_ne (0 : M)
    exact hw (hinj N w (hN w))
  · have : v ∈ P := hP ▸ Submodule.mem_top
    exact this

variable {K : Type*} [CommRing K] [Algebra K A] [Module K M] [IsScalarTower K A M]

theorem smulNilpotent_iff_isNilpotent {a : A} :
    SmulNilpotent a M ↔ IsNilpotent (Algebra.lsmul K K M a) := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, LinearMap.ext fun v => by rw [← map_pow]; exact hN v⟩
  · rintro ⟨N, hN⟩
    refine ⟨N, fun v => ?_⟩
    rw [← map_pow] at hN
    exact LinearMap.congr_fun hN v

end Nilpotent

namespace KLRAlgebra

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K} {μ ν' : Multiset I} {i : I}
  (hν' : ∀ a ∈ ν', a = i)

/-! ### The module `L(i^n)` -/

section LModule

/-- The class `[p] ∈ L(i^n) = k[x]/(Sym⁺)`. -/
def lMk (hν' : ∀ a ∈ ν', a = i) (Q : I → I → MvPolynomial (Fin 2) K)
    (p : MvPolynomial (Fin (Multiset.card ν')) K) : KLRRep hν' Q :=
  KLRRep.of hν' Q (Submodule.Quotient.mk p)

omit [DecidableEq I] in
theorem lMk_surjective (ℓ : KLRRep hν' Q) : ∃ p, lMk hν' Q p = ℓ := by
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ ((KLRRep.of hν' Q).symm ℓ)
  exact ⟨p, by rw [lMk, hp, LinearEquiv.apply_symm_apply]⟩

theorem smul_lMk (r : KLRAlgebra K Q ν') (p : MvPolynomial (Fin (Multiset.card ν')) K) :
    r • lMk hν' Q p = lMk hν' Q (toNH hν' Q r p) := rfl

theorem pol_smul_lMk (p q : MvPolynomial (Fin (Multiset.card ν')) K) :
    (pol p : KLRAlgebra K Q ν') • lMk hν' Q q = lMk hν' Q (p * q) := by
  rw [smul_lMk, toNH_pol, mulPoly_apply]

omit [DecidableEq I] in
theorem lMk_eq_zero_iff {p : MvPolynomial (Fin (Multiset.card ν')) K} :
    lMk hν' Q p = 0 ↔ p ∈ coinvIdeal K (Multiset.card ν') := by
  rw [lMk, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, mem_coinvSub]

omit [DecidableEq I] in
theorem lMk_one_ne_zero : lMk hν' Q 1 ≠ 0 := by
  rw [ne_eq, lMk_eq_zero_iff]; exact one_not_mem_coinvIdeal

theorem ψw_w0Word_smul_lMk_xDelta :
    (ψw (w0Word (Multiset.card ν')) : KLRAlgebra K Q ν') • lMk hν' Q (xDelta (Multiset.card ν')) =
      lMk hν' Q 1 := by
  rw [smul_lMk, toNH_ψw, ddw_w0Word_xDelta]

theorem lMk_xDelta_ne_zero : lMk hν' Q (xDelta (Multiset.card ν')) ≠ 0 := by
  intro h
  apply lMk_one_ne_zero hν' (Q := Q)
  rw [← ψw_w0Word_smul_lMk_xDelta, h, smul_zero]

theorem pol_smul_eq_zero {p : MvPolynomial (Fin (Multiset.card ν')) K}
    (hp : p ∈ coinvIdeal K (Multiset.card ν')) (ℓ : KLRRep hν' Q) :
    (pol p : KLRAlgebra K Q ν') • ℓ = 0 := by
  obtain ⟨q, rfl⟩ := lMk_surjective hν' ℓ
  rw [pol_smul_lMk, lMk_eq_zero_iff]
  exact Ideal.mul_mem_right _ _ hp

/-- **KL I, Lemma 2.1 (socle)**: the common kernel of the dots on `L(i^n)` is `k [x^δ]`. -/
theorem exists_eq_smul_lMk_xDelta {ℓ : KLRRep hν' Q}
    (h : ∀ b, (x b : KLRAlgebra K Q ν') • ℓ = 0) :
    ∃ c : K, ℓ = c • lMk hν' Q (xDelta (Multiset.card ν')) := by
  have hmem : (KLRRep.of hν' Q).symm ℓ ∈ coinvSocle K (Multiset.card ν') := by
    rw [mem_coinvSocle]
    intro b
    have := congrArg (KLRRep.of hν' Q).symm (h b)
    rwa [← LinearEquiv.apply_symm_apply (KLRRep.of hν' Q) ℓ, klr_smul_def,
      LinearEquiv.symm_apply_apply, klrAct_x, map_zero] at this
  rw [coinvSocle_eq_span_xDelta, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  rw [lMk, ← map_smul, hc, LinearEquiv.apply_symm_apply]

omit [DecidableEq I] in
/-- Words in the dots of length `> n(n-1)/2` act by zero on `L(i^n)`. -/
theorem prod_x_mem_coinvIdeal (ρ : List (Fin (Multiset.card ν')))
    (hρ : (Multiset.card ν').choose 2 < ρ.length) :
    (ρ.map (X (R := K))).prod ∈ coinvIdeal K (Multiset.card ν') := by
  refine mem_coinvIdeal_of_isHomogeneous ?_ hρ
  clear hρ
  induction ρ with
  | nil => simpa using isHomogeneous_one (Fin (Multiset.card ν')) K
  | cons b ρ ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, add_comm]
    exact (isHomogeneous_X K b).mul ih

end LModule

/-! ### External tensor products `V ⊠ L(i^n)` -/

section ExtTensorL

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (KLRAlgebra K Q μ) V]
  [IsScalarTower K (KLRAlgebra K Q μ) V]

theorem one_tmul_smul_tmul (b : KLRAlgebra K Q ν') (v : V) (ℓ : KLRRep hν' Q) :
    ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] b : TensorKLR Q μ ν') •
        (ExtTensor.tmul v ℓ : ExtTensor K V (KLRRep hν' Q)) =
      (ExtTensor.tmul v (b • ℓ) : ExtTensor K V (KLRRep hν' Q)) := by
  rw [ExtTensor.smul_tmul, one_smul]

theorem one_tmul_pol_smul_eq_zero {p : MvPolynomial (Fin (Multiset.card ν')) K}
    (hp : p ∈ coinvIdeal K (Multiset.card ν')) (y : ExtTensor K V (KLRRep hν' Q)) :
    ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] pol p : TensorKLR Q μ ν') • y = 0 := by
  induction y using ExtTensor.induction_on with
  | zero => rw [smul_zero]
  | tmul v ℓ => rw [one_tmul_smul_tmul, pol_smul_eq_zero hν' hp, ExtTensor.tmul_zero]
  | add y y' hy hy' => rw [smul_add, hy, hy', add_zero]

omit [DecidableEq I] in
/-- Pure tensors of nonzero vectors are nonzero. -/
theorem extTensor_tmul_ne_zero {A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    {W : Type*} [AddCommGroup W] [Module K W] {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) :
    (ExtTensor.tmul v w : ExtTensor K V W) ≠ 0 := by
  classical
  let B := Basis.ofVectorSpace K V
  intro h
  have h' := congrArg (TensorProduct.equivFinsuppOfBasisLeft B) (show v ⊗ₜ[K] w = 0 from h)
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, map_zero] at h'
  have hr : B.repr v ≠ 0 := fun h0 => hv (B.repr.map_eq_zero_iff.1 h0)
  obtain ⟨c, hc⟩ := Finsupp.ne_iff.1 hr
  have := congrArg (fun f => f c) h'
  simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply] at this hc
  exact hw ((smul_eq_zero.1 this).resolve_left hc)

theorem equivFinsupp_one_tmul_smul {ι : Type*} [DecidableEq ι] (B : Basis ι K V) (b : KLRAlgebra K Q ν')
    (y : ExtTensor K V (KLRRep hν' Q)) :
    TensorProduct.equivFinsuppOfBasisLeft B
        (ExtTensor.equivTensor (((1 : KLRAlgebra K Q μ) ⊗ₜ[K] b : TensorKLR Q μ ν') • y)) =
      (TensorProduct.equivFinsuppOfBasisLeft B (ExtTensor.equivTensor y)).mapRange (b • ·)
        (smul_zero b) := by
  induction y using ExtTensor.induction_on with
  | zero => simp
  | tmul v ℓ =>
    rw [one_tmul_smul_tmul]
    show TensorProduct.equivFinsuppOfBasisLeft B (v ⊗ₜ[K] (b • ℓ)) =
      (TensorProduct.equivFinsuppOfBasisLeft B (v ⊗ₜ[K] ℓ)).mapRange (b • ·) (smul_zero b)
    ext c
    simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]
    rw [smul_comm]
  | add y y' hy hy' =>
    rw [smul_add, map_add, map_add, hy, hy', map_add, map_add, Finsupp.mapRange_add]
    exact smul_add b

/-- A vector of `V ⊠ L(i^n)` killed by all dots of the second factor is `w ⊗ [x^δ]`. -/
theorem exists_eq_tmul_xDelta {y : ExtTensor K V (KLRRep hν' Q)}
    (hy : ∀ b, ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν') • y = 0) :
    ∃ w : V, y = ExtTensor.tmul w (lMk hν' Q (xDelta (Multiset.card ν'))) := by
  classical
  set u := lMk hν' Q (xDelta (Multiset.card ν'))
  let B := Basis.ofVectorSpace K V
  let F : ExtTensor K V (KLRRep hν' Q) ≃ₗ[K] _ :=
    ExtTensor.equivTensor.trans (TensorProduct.equivFinsuppOfBasisLeft B)
  have hF : ∀ z, F z = TensorProduct.equivFinsuppOfBasisLeft B (ExtTensor.equivTensor z) :=
    fun _ => rfl
  have hcoord : ∀ c, ∃ a : K, F y c = a • u := by
    intro c
    refine exists_eq_smul_lMk_xDelta hν' fun b => ?_
    have := congrArg (fun f => f c) (equivFinsupp_one_tmul_smul (μ := μ) hν' B (x b) y)
    simp only [Finsupp.mapRange_apply] at this
    rw [hF, ← this, hy b, map_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K (KLRRep hν' Q), φ u = 1 := by
    have hu : u ≠ 0 := lMk_xDelta_ne_zero hν'
    rw [ne_eq, ← Module.forall_dual_apply_eq_zero_iff K u, not_forall] at hu
    obtain ⟨φ₀, hφ₀⟩ := hu
    exact ⟨(φ₀ u)⁻¹ • φ₀, by simp [inv_mul_cancel₀ hφ₀]⟩
  refine ⟨B.repr.symm ((F y).mapRange φ (map_zero φ)), F.injective ?_⟩
  ext c
  obtain ⟨a, ha⟩ := hcoord c
  have : F (ExtTensor.tmul (B.repr.symm ((F y).mapRange φ (map_zero φ))) u) c =
      φ (F y c) • u := by
    rw [hF]
    show TensorProduct.equivFinsuppOfBasisLeft B
      (B.repr.symm ((F y).mapRange φ (map_zero φ)) ⊗ₜ[K] u) c = _
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, LinearEquiv.apply_symm_apply,
      Finsupp.mapRange_apply]
  rw [this, ha, map_smul, hφ, smul_eq_mul, mul_one]

theorem exists_ne_zero_x_smul_eq_zero {P : Submodule (TensorKLR Q μ ν') (ExtTensor K V (KLRRep hν' Q))}
    (hP : P ≠ ⊥) :
    ∃ y ∈ P, y ≠ 0 ∧ ∀ b, ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν') • y = 0 := by
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  let T : Fin (Multiset.card ν') → Module.End K (ExtTensor K V (KLRRep hν' Q)) := fun b =>
    Algebra.lsmul K K _ ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν')
  have hD : ∀ ρ : List (Fin (Multiset.card ν')), (Multiset.card ν').choose 2 < ρ.length →
      (ρ.map T).prod = 0 := by
    intro ρ hρ
    have h1 : (ρ.map T).prod = Algebra.lsmul K K (ExtTensor K V (KLRRep hν' Q))
        ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] pol (ρ.map (X (R := K))).prod : TensorKLR Q μ ν') := by
      rw [← Algebra.TensorProduct.includeRight_apply, map_list_prod, map_list_prod, map_list_prod,
        List.map_map, List.map_map]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro b _
      simp only [Function.comp_apply, pol_X, Algebra.TensorProduct.includeRight_apply, T]
    rw [h1]
    ext y
    simp only [Algebra.lsmul_coe, LinearMap.zero_apply]
    exact one_tmul_pol_smul_eq_zero hν' (prod_x_mem_coinvIdeal ρ hρ) y
  obtain ⟨y, hy, hy0, hyx⟩ := exists_ne_zero_forall_eq_zero T _ hD (P : Set _)
    (fun b v hv => P.smul_mem ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν') hv) hz hz0
  exact ⟨y, hy, hy0, hyx⟩

/-- **Lowering**: every nonzero `R(μ) ⊗ R(ν')`-submodule of `V ⊠ L(i^n)` contains a vector
`w ⊗ [1]` with `w ≠ 0`. -/
theorem exists_tmul_one_mem {P : Submodule (TensorKLR Q μ ν') (ExtTensor K V (KLRRep hν' Q))}
    (hP : P ≠ ⊥) : ∃ w : V, w ≠ 0 ∧ ExtTensor.tmul w (lMk hν' Q 1) ∈ P := by
  obtain ⟨y, hy, hy0, hyx⟩ := exists_ne_zero_x_smul_eq_zero hν' hP
  obtain ⟨w, rfl⟩ := exists_eq_tmul_xDelta hν' hyx
  refine ⟨w, fun h => hy0 (by rw [h, ExtTensor.zero_tmul]), ?_⟩
  have := P.smul_mem ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] ψw (w0Word (Multiset.card ν'))) hy
  rwa [one_tmul_smul_tmul, ψw_w0Word_smul_lMk_xDelta] at this

/-- **`N ⊠ L(i^n)` is simple if `N` is.** -/
theorem isSimpleModule_extTensor [IsSimpleModule (KLRAlgebra K Q μ) V] :
    IsSimpleModule (TensorKLR Q μ ν') (ExtTensor K V (KLRRep hν' Q)) := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q μ) V
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  haveI : Nontrivial (ExtTensor K V (KLRRep hν' Q)) :=
    ⟨⟨_, 0, extTensor_tmul_ne_zero (A := KLRAlgebra K Q μ) (B := KLRAlgebra K Q ν') hv₀
      (lMk_one_ne_zero hν')⟩⟩
  refine ⟨fun P => ?_⟩
  by_cases hP : P = ⊥
  · exact Or.inl hP
  right
  obtain ⟨w, hw0, hw⟩ := exists_tmul_one_mem hν' hP
  have hspan : Submodule.span (KLRAlgebra K Q μ) {w} = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left (by
      rw [Submodule.span_singleton_eq_bot]; exact hw0)
  rw [eq_top_iff]
  rintro y -
  induction y using ExtTensor.induction_on with
  | zero => exact zero_mem _
  | tmul v ℓ =>
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 (hspan ▸ Submodule.mem_top : v ∈ _)
    obtain ⟨p, rfl⟩ := lMk_surjective hν' ℓ
    have := P.smul_mem (a ⊗ₜ[K] pol p) hw
    rwa [ExtTensor.smul_tmul, pol_smul_lMk, mul_one] at this
  | add y y' hy hy' => exact add_mem hy hy'

end ExtTensorL

/-! ### The highest weight space -/

section HW

theorem tmul_one_mul_one_tmul (a : KLRAlgebra K Q μ) (b : KLRAlgebra K Q ν') :
    ((a ⊗ₜ[K] 1) * (1 ⊗ₜ[K] b) : TensorKLR Q μ ν') = (1 ⊗ₜ[K] b) * (a ⊗ₜ[K] 1) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    mul_one, one_mul]

variable (Q μ ν') (S : Type*) [AddCommGroup S] [Module K S] [Module (TensorKLR Q μ ν') S]
  [IsScalarTower K (TensorKLR Q μ ν') S]

/-- The subspace of vectors of an `R(μ) ⊗ R(ν')`-module killed by all crossings `1 ⊗ ψ_j` of the
second factor. -/
def hwSub : Submodule K S where
  carrier := {v | ∀ j : ℕ, ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] ψ j : TensorKLR Q μ ν') • v = 0}
  add_mem' ha hb j := by rw [smul_add, ha j, hb j, add_zero]
  zero_mem' j := smul_zero _
  smul_mem' c v hv j := by rw [smul_comm, hv j, smul_zero]

/-- **The highest weight space** `HW(S)`, an `R(μ)`-module. -/
abbrev HWSpace : Type _ := hwSub Q μ ν' S

variable {Q μ ν' S}

theorem mem_hwSub {v : S} :
    v ∈ hwSub Q μ ν' S ↔ ∀ j : ℕ, ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] ψ j : TensorKLR Q μ ν') • v = 0 :=
  Iff.rfl

theorem tmul_one_smul_mem_hwSub (a : KLRAlgebra K Q μ) {v : S} (hv : v ∈ hwSub Q μ ν' S) :
    ((a ⊗ₜ[K] 1 : TensorKLR Q μ ν') • v) ∈ hwSub Q μ ν' S := fun j => by
  rw [smul_smul, ← tmul_one_mul_one_tmul, mul_smul, hv j, smul_zero]

instance : SMul (KLRAlgebra K Q μ) (HWSpace Q μ ν' S) :=
  ⟨fun a v => ⟨(a ⊗ₜ[K] 1 : TensorKLR Q μ ν') • (v : S), tmul_one_smul_mem_hwSub a v.2⟩⟩

theorem coe_hw_smul (a : KLRAlgebra K Q μ) (v : HWSpace Q μ ν' S) :
    ((a • v : HWSpace Q μ ν' S) : S) = (a ⊗ₜ[K] 1 : TensorKLR Q μ ν') • (v : S) := rfl

instance : Module (KLRAlgebra K Q μ) (HWSpace Q μ ν' S) where
  one_smul v := Subtype.ext (by rw [coe_hw_smul, ← Algebra.TensorProduct.one_def, one_smul])
  mul_smul a b v := Subtype.ext (by
    simp only [coe_hw_smul]
    rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one])
  smul_zero a := Subtype.ext (by rw [coe_hw_smul, ZeroMemClass.coe_zero, smul_zero])
  smul_add a v w := Subtype.ext (by simp only [coe_hw_smul, Submodule.coe_add, smul_add])
  add_smul a b v := Subtype.ext (by
    simp only [coe_hw_smul, Submodule.coe_add, TensorProduct.add_tmul, add_smul])
  zero_smul v := Subtype.ext (by
    simp only [coe_hw_smul, TensorProduct.zero_tmul, zero_smul, ZeroMemClass.coe_zero])

instance : IsScalarTower K (KLRAlgebra K Q μ) (HWSpace Q μ ν' S) where
  smul_assoc c a v := Subtype.ext (by
    rw [coe_hw_smul, Submodule.coe_smul, coe_hw_smul, ← TensorProduct.smul_tmul', smul_assoc])

variable (hsym : ∀ p ∈ coinvIdeal K (Multiset.card ν'), ∀ v : S,
  ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] pol p : TensorKLR Q μ ν') • v = 0)

/-- `p ↦ (1 ⊗ p(x)) v`. -/
def hwPolMap (v : S) : MvPolynomial (Fin (Multiset.card ν')) K →ₗ[K] S :=
  ((Algebra.lsmul K K S).toLinearMap.flip v).comp
    ((Algebra.TensorProduct.includeRight (R := K) (A := KLRAlgebra K Q μ)).comp
      (pol (k := K) (Q := Q) (ν := ν'))).toLinearMap

theorem hwPolMap_apply (v : S) (p : MvPolynomial (Fin (Multiset.card ν')) K) :
    hwPolMap (Q := Q) (μ := μ) (ν' := ν') v p =
      ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] pol p : TensorKLR Q μ ν') • v := rfl

/-- `[p] ↦ (1 ⊗ p(x)) v`, well defined since `Sym⁺` acts by zero (`hsym`). -/
def hwVecMap (v : S) : KLRRep hν' Q →ₗ[K] S :=
  ((coinvSub K (Multiset.card ν')).liftQ (hwPolMap (Q := Q) (μ := μ) (ν' := ν') v) (fun p hp => by
    rw [LinearMap.mem_ker, hwPolMap_apply]; exact hsym p hp v)).comp
    (KLRRep.of hν' Q).symm.toLinearMap

theorem hwVecMap_lMk (v : S) (p : MvPolynomial (Fin (Multiset.card ν')) K) :
    hwVecMap hν' hsym v (lMk hν' Q p) =
      ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] pol p : TensorKLR Q μ ν') • v := by
  simp only [hwVecMap, lMk, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.liftQ_apply, hwPolMap_apply]

/-- For `v ∈ HW(S)`, `[p] ↦ (1 ⊗ p(x)) v` is `R(ν')`-linear. -/
theorem hwVecMap_smul {v : S} (hv : v ∈ hwSub Q μ ν' S) (b : KLRAlgebra K Q ν')
    (ℓ : KLRRep hν' Q) :
    hwVecMap hν' hsym v (b • ℓ) =
      ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] b : TensorKLR Q μ ν') • hwVecMap hν' hsym v ℓ := by
  have hb : b ∈ Algebra.adjoin K (Set.range (e (k := K) (Q := Q) (ν := ν')) ∪ Set.range x ∪
      Set.range ψ) := by rw [adjoin_gens]; trivial
  induction hb using Algebra.adjoin_induction generalizing ℓ with
  | mem y hy =>
    obtain ⟨p, rfl⟩ := lMk_surjective hν' ℓ
    rcases hy with (⟨t, rfl⟩ | ⟨a, rfl⟩) | ⟨j, rfl⟩
    · rw [e_eq_one_of_forall hν' Q t, one_smul, ← Algebra.TensorProduct.one_def, one_smul]
    · rw [← pol_X, pol_smul_lMk, hwVecMap_lMk, hwVecMap_lMk, smul_smul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_mul]
    · rw [smul_lMk, toNH_ψ, hwVecMap_lMk, hwVecMap_lMk, smul_smul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      obtain ⟨q, hq⟩ := exists_ψ_mul_pol hν' Q j p
      rw [hq, TensorProduct.tmul_add, add_smul, ← mul_one (1 : KLRAlgebra K Q μ),
        ← Algebra.TensorProduct.tmul_mul_tmul, mul_smul, hv j, smul_zero, add_zero, mul_one]
  | algebraMap c =>
    rw [algebraMap_smul, map_smul, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      ← Algebra.TensorProduct.one_def, smul_assoc, one_smul]
  | add y z _ _ hy hz =>
    rw [add_smul, map_add, hy, hz, TensorProduct.tmul_add, add_smul]
  | mul y z _ _ hy hz =>
    rw [mul_smul, hy, hz, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- The bilinear map `(v, [p]) ↦ (1 ⊗ p(x)) v` on `HW(S) × L(i^n)`. -/
def hwBil : HWSpace Q μ ν' S →ₗ[K] KLRRep hν' Q →ₗ[K] S :=
  LinearMap.mk₂ K (fun v ℓ => hwVecMap hν' hsym (v : S) ℓ)
    (fun v w ℓ => by
      obtain ⟨p, rfl⟩ := lMk_surjective hν' ℓ
      simp only [hwVecMap_lMk, Submodule.coe_add, smul_add])
    (fun c v ℓ => by
      obtain ⟨p, rfl⟩ := lMk_surjective hν' ℓ
      simp only [hwVecMap_lMk, Submodule.coe_smul_of_tower]
      rw [smul_comm])
    (fun v ℓ ℓ' => map_add _ _ _)
    (fun c v ℓ => map_smul _ _ _)

theorem hwBil_apply (v : HWSpace Q μ ν' S) (ℓ : KLRRep hν' Q) :
    hwBil hν' hsym v ℓ = hwVecMap hν' hsym (v : S) ℓ := rfl

/-- **The map `HW(S) ⊠ L(i^n) → S`, `v ⊗ [p] ↦ (1 ⊗ p(x)) v`.** -/
def hwMap : ExtTensor K (HWSpace Q μ ν' S) (KLRRep hν' Q) →ₗ[TensorKLR Q μ ν'] S where
  toFun y := TensorProduct.lift (hwBil hν' hsym) (ExtTensor.equivTensor y)
  map_add' y y' := by rw [map_add, map_add]
  map_smul' t y := by
    refine ExtTensor.smul_eq_induction (F := fun y =>
      TensorProduct.lift (hwBil hν' hsym) (ExtTensor.equivTensor y))
      (fun y y' => by simp only [map_add]) (by simp only [map_zero]) ?_ t y
    intro a b v ℓ
    obtain ⟨p, rfl⟩ := lMk_surjective hν' ℓ
    rw [ExtTensor.smul_tmul]
    show hwBil hν' hsym (a • v) (b • lMk hν' Q p) = (a ⊗ₜ[K] b) • hwBil hν' hsym v (lMk hν' Q p)
    rw [hwBil_apply, hwBil_apply, hwVecMap_smul hν' hsym (a • v).2, hwVecMap_lMk, hwVecMap_lMk,
      coe_hw_smul, smul_smul, smul_smul, smul_smul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, one_mul, mul_one]

theorem hwMap_tmul (v : HWSpace Q μ ν' S) (p : MvPolynomial (Fin (Multiset.card ν')) K) :
    hwMap hν' hsym (ExtTensor.tmul v (lMk hν' Q p)) =
      ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] pol p : TensorKLR Q μ ν') • (v : S) :=
  hwVecMap_lMk hν' hsym (v : S) p

theorem hwMap_tmul_one (v : HWSpace Q μ ν' S) :
    hwMap hν' hsym (ExtTensor.tmul v (lMk hν' Q 1)) = v := by
  rw [hwMap_tmul, map_one, ← Algebra.TensorProduct.one_def, one_smul]

end HW

/-! ### Simple modules -/

section Classification

variable {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {S : Type*} [AddCommGroup S] [Module K S] [Module (TensorKLR Q μ ν') S]
  [IsScalarTower K (TensorKLR Q μ ν') S]

include hPQ hP in
/-- Symmetric polynomials in the dots are central in `R(ν')`. -/
theorem commute_pol_of_isSymmetric {s : MvPolynomial (Fin (Multiset.card ν')) K}
    (hs : s.IsSymmetric) (r : KLRAlgebra K Q ν') : Commute (pol s : KLRAlgebra K Q ν') r := by
  have hpol : (pol s : KLRAlgebra K Q ν') = polNu (Function.const (Seq ν') s) := by
    rw [polNu_apply]
    simp only [Function.const_apply]
    rw [← Finset.mul_sum, sum_e, mul_one]
  rw [hpol]
  exact ((Subalgebra.mem_center_iff.1 (polNu_mem_center hPQ hP (const_mem_symNu hs))) r).symm

include hPQ hP in
/-- **`Sym⁺` of the second factor acts by zero on a simple module with nilpotent dots.** -/
theorem one_tmul_pol_smul_eq_zero_of_simple [IsSimpleModule (TensorKLR Q μ ν') S]
    (hnil : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν') S) :
    ∀ p ∈ coinvIdeal K (Multiset.card ν'), ∀ v : S,
      ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] pol p : TensorKLR Q μ ν') • v = 0 := by
  let ρ : MvPolynomial (Fin (Multiset.card ν')) K →ₐ[K] Module.End K S :=
    (Algebra.lsmul K K S).comp
      ((Algebra.TensorProduct.includeRight (R := K) (A := KLRAlgebra K Q μ)).comp
        (pol (k := K) (Q := Q) (ν := ν')))
  have hρ : ∀ p, ρ p = Algebra.lsmul K K S
      ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] pol p : TensorKLR Q μ ν') := fun _ => rfl
  -- polynomials without constant term act nilpotently
  have hnilp : ∀ p ∈ Ideal.span (Set.range (X : Fin (Multiset.card ν') → MvPolynomial _ K)),
      IsNilpotent (ρ p) := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [hρ, pol_X]
      exact (smulNilpotent_iff_isNilpotent (K := K) (A := TensorKLR Q μ ν') (M := S)).1 (hnil b)
    | zero => rw [map_zero]; exact IsNilpotent.zero
    | add y z _ _ hy hz =>
      rw [map_add]
      exact ((Commute.all y z).map ρ).isNilpotent_add hy hz
    | smul r y _ hy =>
      rw [smul_eq_mul, map_mul]
      exact ((Commute.all r y).map ρ).isNilpotent_mul_right hy
  -- the generators `s ∈ Sym⁺` act by zero
  have hgen : ∀ s ∈ symPlusSet K (Multiset.card ν'), ∀ v : S,
      ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] pol s : TensorKLR Q μ ν') • v = 0 := by
    intro s hs v
    refine smul_eq_zero_of_smulNilpotent (fun t => ?_) ?_ v
    · induction t using TensorProduct.induction_on with
      | zero => exact Commute.zero_right _
      | tmul a b =>
        rw [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
          (commute_pol_of_isSymmetric hPQ hP hs.1 b).eq]
      | add t t' ht ht' => exact ht.add_right ht'
    · refine (smulNilpotent_iff_isNilpotent (K := K) (A := TensorKLR Q μ ν') (M := S)).2
        (hnilp s ?_)
      rw [show (Set.range (X : Fin (Multiset.card ν') → MvPolynomial _ K)) = X '' Set.univ by
        rw [Set.image_univ], MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      by_contra hcon
      push_neg at hcon
      have hm0 : m = 0 := Finsupp.ext fun b => hcon b (Set.mem_univ b)
      rw [hm0, MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq, hs.2] at hm
      exact hm rfl
  intro p hp
  induction hp using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => intro v; rw [map_zero, TensorProduct.tmul_zero, zero_smul]
  | add y z _ _ hy hz => intro v; rw [map_add, TensorProduct.tmul_add, add_smul, hy, hz, add_zero]
  | smul r y _ hy =>
    intro v
    rw [smul_eq_mul, map_mul, ← one_mul (1 : KLRAlgebra K Q μ),
      ← Algebra.TensorProduct.tmul_mul_tmul, mul_smul, hy, smul_zero]

include hν' in
/-- A nonzero module has a nonzero highest weight vector. -/
theorem hwSub_ne_bot [Nontrivial S] : hwSub Q μ ν' S ≠ ⊥ := by
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : S)
  let T : ℕ → Module.End K S := fun j =>
    Algebra.lsmul K K S ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] ψ j : TensorKLR Q μ ν')
  have hD : ∀ ρ : List ℕ, (Multiset.card ν').choose 2 < ρ.length → (ρ.map T).prod = 0 := by
    intro ρ hρ
    have h1 : (ρ.map T).prod = Algebra.lsmul K K S
        ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] ψw ρ : TensorKLR Q μ ν') := by
      rw [← Algebra.TensorProduct.includeRight_apply, ψw, map_list_prod, map_list_prod,
        List.map_map, List.map_map]
      rfl
    rw [h1, ψw_eq_zero_of_choose_lt hν' Q hρ, TensorProduct.tmul_zero, map_zero]
  obtain ⟨v, -, hv0, hv⟩ := exists_ne_zero_forall_eq_zero T _ hD Set.univ
    (fun _ _ _ => Set.mem_univ _) (Set.mem_univ v₀) hv₀
  rw [Submodule.ne_bot_iff]
  exact ⟨v, fun j => hv j, hv0⟩

variable [IsSimpleModule (TensorKLR Q μ ν') S]
  (hnil : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν') S)

include hPQ hP hnil in
theorem hwMap_bijective :
    Function.Bijective (hwMap hν' (one_tmul_pol_smul_eq_zero_of_simple hPQ hP hnil)) := by
  set hsym := one_tmul_pol_smul_eq_zero_of_simple hPQ hP hnil
  haveI := IsSimpleModule.nontrivial (TensorKLR Q μ ν') S
  constructor
  · rw [← LinearMap.ker_eq_bot]
    by_contra hker
    obtain ⟨w, hw0, hw⟩ := exists_tmul_one_mem hν' hker
    rw [LinearMap.mem_ker, hwMap_tmul_one] at hw
    exact hw0 (Subtype.ext hw)
  · rw [← LinearMap.range_eq_top]
    refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left ?_
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hwSub_ne_bot hν' (Q := Q) (μ := μ) (S := S))
    rw [← ne_eq, Submodule.ne_bot_iff]
    exact ⟨_, ⟨ExtTensor.tmul (⟨w, hw⟩ : HWSpace Q μ ν' S) (lMk hν' Q 1), rfl⟩,
      by rw [hwMap_tmul_one]; exact hw0⟩

/-- **A simple `R(μ) ⊗ R(ν')`-module with nilpotent dots on the second factor is
`HW(S) ⊠ L(i^n)`.** -/
def hwEquiv : ExtTensor K (HWSpace Q μ ν' S) (KLRRep hν' Q) ≃ₗ[TensorKLR Q μ ν'] S :=
  LinearEquiv.ofBijective _ (hwMap_bijective hν' hPQ hP hnil)

theorem hwEquiv_tmul (v : HWSpace Q μ ν' S) (p : MvPolynomial (Fin (Multiset.card ν')) K) :
    hwEquiv hν' hPQ hP hnil (ExtTensor.tmul v (lMk hν' Q p)) =
      ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] pol p : TensorKLR Q μ ν') • (v : S) :=
  hwMap_tmul hν' _ v p

include hν' hPQ hP hnil in
/-- **`HW(S)` is a simple `R(μ)`-module** (for `S` simple, finite-dimensional, with nilpotent
dots on the second factor). -/
theorem isSimpleModule_hwSpace [FiniteDimensional K S] :
    IsSimpleModule (KLRAlgebra K Q μ) (HWSpace Q μ ν' S) := by
  haveI := IsSimpleModule.nontrivial (TensorKLR Q μ ν') S
  haveI : Nontrivial (HWSpace Q μ ν' S) := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hwSub_ne_bot hν' (Q := Q) (μ := μ) (S := S))
    exact ⟨⟨⟨w, hw⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
  refine ⟨fun W => ?_⟩
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  let g := ExtTensor.map (k := K) W.subtype (LinearMap.id : KLRRep hν' Q →ₗ[KLRAlgebra K Q ν'] _)
  let Φ := hwEquiv hν' hPQ hP hnil
  have hsurj : Function.Surjective (Φ.toLinearMap ∘ₗ g) := by
    rw [← LinearMap.range_eq_top]
    refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left ?_
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    rw [← ne_eq, Submodule.ne_bot_iff]
    refine ⟨_, ⟨ExtTensor.tmul (⟨w, hw⟩ : W) (lMk hν' Q 1), rfl⟩, ?_⟩
    rw [LinearMap.comp_apply, ExtTensor.map_tmul, LinearEquiv.coe_coe, LinearMap.id_apply,
      Submodule.subtype_apply]
    show hwEquiv hν' hPQ hP hnil (ExtTensor.tmul (w : HWSpace Q μ ν' S) (lMk hν' Q 1)) ≠ 0
    rw [hwEquiv_tmul, map_one, ← Algebra.TensorProduct.one_def, one_smul]
    exact fun h => hw0 (Subtype.ext h)
  have hgsurj : Function.Surjective g := fun y => by
    obtain ⟨z, hz⟩ := hsurj (Φ y)
    exact ⟨z, Φ.injective hz⟩
  haveI : FiniteDimensional K (HWSpace Q μ ν' S) := inferInstance
  haveI : FiniteDimensional K W :=
    Module.Finite.of_injective (W.subtype.restrictScalars K) Subtype.val_injective
  haveI : FiniteDimensional K (ExtTensor K W (KLRRep hν' Q)) :=
    inferInstanceAs (FiniteDimensional K (↥W ⊗[K] KLRRep hν' Q))
  have hfin : Module.finrank K (ExtTensor K (HWSpace Q μ ν' S) (KLRRep hν' Q)) ≤
      Module.finrank K (ExtTensor K W (KLRRep hν' Q)) := by
    have := LinearMap.finrank_range_le (g.restrictScalars K)
    rwa [LinearMap.range_eq_top.2 (show Function.Surjective (g.restrictScalars K) from hgsurj),
      finrank_top] at this
  rw [ExtTensor.equivTensor.finrank_eq, ExtTensor.equivTensor.finrank_eq,
    Module.finrank_tensorProduct, Module.finrank_tensorProduct] at hfin
  have hL : 0 < Module.finrank K (KLRRep hν' Q) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨_, lMk_one_ne_zero hν'⟩
  have hle : Module.finrank K (HWSpace Q μ ν' S) ≤ Module.finrank K W :=
    Nat.le_of_mul_le_mul_right hfin hL
  rw [← Submodule.restrictScalars_eq_top_iff K]
  apply Submodule.eq_top_of_finrank_eq
  exact le_antisymm (Submodule.finrank_le _) hle

end Classification

end KLRAlgebra

end Categorification.KLR
