/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Bialgebra
import Categorification.KLR.KL2.Theorem8

/-!
# KL II, Theorem 8: `γ : _𝒜 f → K₀(R)` is an isomorphism of twisted bialgebras

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3, paragraph "Grothendieck group as the quantum group", **Theorem 8**:
"`γ : _𝒜 f → K₀(R)` is an isomorphism of `ℕ[I]`-graded twisted bialgebras", for an arbitrary
Cartan datum ("The proof of [KL I, Theorem 1.1] carries over to an arbitrary Cartan datum").
The isomorphism part is `KL2Gamma.theorem_8` (`Categorification.KLR.KL2.Theorem8`); this file
proves the twisted-bialgebra part, following KL I (arXiv:0803.4121v2) §3.1, Propositions 3.1
and 3.2, as formalized for the KL I grading in `Categorification.KLR.Bialgebra`.

Here `C` is a Cartan datum (`QuantumGroup.CartanDatum`: symmetric, `i · i ∈ 2ℤ_{>0}`,
`2 (i·j)/(i·i) ∈ ℤ_{≤0}`), `R = ⊕_ν R(ν)` the KL II rings over a field `𝕜` (`klQ2`,
`klGradingDatum2`: `deg x_{a,i} = i_a · i_a`, `deg ψ_{k,i} = -i_k · i_{k+1}`), and `_𝒜 f` is
Lusztig's integral form for `C` (divided powers `θ_i^{(a)} = θ_i^a / [a]_{v_i}^!`,
`v_i = v^{(i·i)/2}`). The coproduct `Δ = [Res]` and the twisted multiplication (3.1)
`(x₁ ⊗ x₂)(x₁' ⊗ x₂') = q^{-|x₂|·|x₁'|} x₁x₁' ⊗ x₂x₂'` on `K₀(R) ⊗ K₀(R)` are the general ones
of `Categorification.KLR.Bialgebra` (`GradingDatum.coprod`, `GradingDatum.twMul`; for the KL II
grading `∑ degΨ(a, c) = -|x₂|·|x₁'|` with the Cartan pairing).

## General results (any grading datum, `GradingDatum` namespace)

For any grading datum satisfying the basis theorem (`hPQ`, `hP`) with dots of positive degree
(`hG`) over a field:

* `GradingDatum.exists_smul_mem_range_gammaG_of_div` : given a family of "divided-power
  projectives" `D` with `[P_{expandDiv d}] = f(d) [D_d]` and `f(d)(1) = ∏ n_a!` (the hypotheses of
  `GradingDatum.k0Basis_mem_span_of_div`, i.e. KL I Proposition 3.20 in general form), every
  `x ∈ K₀(R)` has a multiple `p x`, `p ≠ 0`, in `γ('f_{ℤ[q,q⁻¹]})`;
* `GradingDatum.noZeroSMulDivisors_tensor`, `GradingDatum.noZeroSMulDivisors_tensor₃` :
  `K₀(R) ⊗ K₀(R)` and `(K₀(R) ⊗ K₀(R)) ⊗ K₀(R)` are torsion-free (`K₀(R)` is free);
* `GradingDatum.coprod_mul_of_exists`, `GradingDatum.coassoc_of_exists` : if every class has a
  nonzero multiple in the image of `γ`, then `Δ` is multiplicative for (3.1) and coassociative
  on all of `K₀(R)` (from `coprod_mul_gammaG`, `coassoc_gammaG`);
* `GradingDatum.gammaG_mem_grade` : `γ('f_ν) ⊆ K₀(R(ν))`.

## KL II (`KL2Gamma` namespace)

* `KL2Gamma.coprodKL2` : `Δ = [Res]` for the KL II rings; `KL2Gamma.gammaZ2` : `γ` on
  `'f_{ℤ[q,q⁻¹]}` (`θ_i ↦ [P_i]`).
* `KL2Gamma.exists_smul_mem_range_gammaZ2` : via KL II's Proposition 3.20
  (`KL2Gamma.k0B2_mem_span_projDiv2`) and `[P_î] = i! [P_i]` (`KL2.K0_projSeq2_expandDiv`).
* `KL2Gamma.coprod_mul2`, `KL2Gamma.coprod_one2` : **KL I, Proposition 3.2, for KL II**;
  `KL2Gamma.coassoc2` : **KL I, Proposition 3.1, for KL II**.
* `KL2Gamma.coprod_gammaZ2` : `[Res] ∘ γ = (γ ⊗ γ) ∘ r` for Lusztig's `r` with the Cartan
  pairing `i · j` and `v = q⁻¹`.
* `KL2Gamma.map_gammaF2_rbar` : over `ℚ(v)`, `(γ ⊗ γ) ∘ r̄ = Δ_{ℚ(v)} ∘ γ` on `f`;
  `KL2Gamma.map_gammaF2_rbar_Af` : the same on `_𝒜 f` with the integral `Δ`;
  `KL2Gamma.toK0QTT2_injective`.
* `KL2Gamma.gammaInt2Equiv_mem_grade` : `γ(_𝒜 f ∩ f_ν) ⊆ K₀(R(ν))`.
* `KL2Gamma.theorem_8_bialgebra` : **KL II, Theorem 8 in full**.

## Hypotheses

As in `Categorification.KLR.KL2.Theorem8`, the quantum Gabber–Kac hypothesis
`hGK : C.GabberKac vQ C.c` (Lusztig 33.1.3) is used to define `f`, `_𝒜 f` and `γ`; it is an
explicit hypothesis of the `f`-level statements, not an axiom. The counit of `[Res]` is not
formalized.
-/

noncomputable section

namespace Categorification.KLR

open Graded GProj QuantumGroup PreF LaurentPolynomial KLRAlgebra
open scoped TensorProduct

local notation "LP" => LaurentPolynomial ℤ

/-! ### General results for any grading datum -/

namespace GradingDatum

variable {I : Type*} [DecidableEq I] {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a)

theorem of_smul_K0R (p : LP) {ν : Multiset I} (y : K0 (G.grade ν)) :
    DirectSum.of G.K0fam ν (p • y) = p • (DirectSum.of G.K0fam ν y : G.K0R) := by
  rw [← DirectSum.lof_eq_of LP, ← DirectSum.lof_eq_of LP, map_smul]

section Torsion

variable
  (D : ∀ (ν : Multiset I) (d : List (I × ℕ)), (expandDiv d : Multiset I) = ν → GProj (G.grade ν))
  (f : List (I × ℕ) → LP)
  (hD : ∀ ν d h, K0.of (G.projP (Seq.ofList (expandDiv d) h)) = f d • K0.of (D ν d h))
  (hf : ∀ d, evalOne (f d) = ((d.map fun q => q.2.factorial).prod : ℕ))

include hPQ hP hG hD hf in
/-- **Every class of `K₀(R)` has a nonzero multiple in `γ('f_{ℤ[q,q⁻¹]})`**, for any grading
datum satisfying the basis theorem with dots of positive degree and any family of divided-power
projectives `D` with `[P_{expandDiv d}] = f(d) [D_d]`, `f(d)(1) = ∏_a n_a!`: for `x ∈ K₀(R)` there
is `p ≠ 0` with `p x = γ(y)`. (The classes `[D_θ]` span `K₀(R(ν))`, KL I Proposition 3.20 in the
general form `k0Basis_mem_span_of_div`, and `f(θ) [D_θ] = γ(θ_{expandDiv θ})`.) -/
theorem exists_smul_mem_range_gammaG_of_div (x : G.K0R) :
    ∃ p : LP, p ≠ 0 ∧ ∃ y : PreF LP I, G.gammaG y = p • x := by
  classical
  let S : Submodule LP G.K0R :=
    { carrier := {x | ∃ p : LP, p ≠ 0 ∧ ∃ y : PreF LP I, G.gammaG y = p • x}
      add_mem' := by
        rintro x x' ⟨p, hp, y, hy⟩ ⟨p', hp', y', hy'⟩
        refine ⟨p * p', mul_ne_zero hp hp', p' • y + p • y', ?_⟩
        rw [map_add, map_smul, map_smul, hy, hy', smul_smul, smul_smul, smul_add, mul_comm p' p]
      zero_mem' := ⟨1, one_ne_zero, 0, by rw [map_zero, smul_zero]⟩
      smul_mem' := by
        rintro c x ⟨p, hp, y, hy⟩
        exact ⟨p, hp, c • y, by rw [map_smul, hy, smul_comm]⟩ }
  have hdiv : ∀ (ν : Multiset I) (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν),
      DirectSum.of G.K0fam ν (K0.of (D ν d h)) ∈ S := by
    intro ν d h
    refine ⟨f d, ne_zero_of_evalOne_eq f hf d, word (FreeMonoid.ofList (expandDiv d)), ?_⟩
    rw [gammaG_word, FreeMonoid.toList_ofList, G.clsW_eq _ h, hD ν d h, of_smul_K0R]
  have hb : ∀ (ν : Multiset I) (b : GProj.IndecClass (G.grade ν)),
      DirectSum.of G.K0fam ν (G.k0Basis hPQ hP hG ν b) ∈ S := by
    intro ν b
    have hle : Submodule.span LP
        {z | ∃ (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν), z = K0.of (D ν d h)} ≤
        S.comap (DirectSum.lof LP (Multiset I) G.K0fam ν) := by
      rw [Submodule.span_le]
      rintro _ ⟨d, h, rfl⟩
      show DirectSum.lof LP (Multiset I) G.K0fam ν _ ∈ S
      rw [DirectSum.lof_eq_of]
      exact hdiv ν d h
    have := hle (G.k0Basis_mem_span_of_div hPQ hP hG ν (D ν) f (hD ν) hf b)
    rwa [Submodule.mem_comap, DirectSum.lof_eq_of] at this
  have htop : S = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun z => ?_
    induction z using DirectSum.induction_on with
    | zero => exact S.zero_mem
    | of ν x =>
      haveI := (G.finite_and_card_indecClass_le hPQ hP hG ν).1
      haveI := Fintype.ofFinite (GProj.IndecClass (G.grade ν))
      rw [← (G.k0Basis hPQ hP hG ν).sum_repr x, map_sum]
      refine S.sum_mem fun b _ => ?_
      rw [of_smul_K0R]
      exact S.smul_mem _ (hb ν b)
    | add x y hx hy => exact S.add_mem hx hy
  exact (htop ▸ Submodule.mem_top : x ∈ S)

end Torsion

set_option synthInstance.maxHeartbeats 400000 in
include hPQ hP hG in
/-- `K₀(R) ⊗ K₀(R)` is torsion-free over `ℤ[q, q⁻¹]` (`K₀(R)` is free, `GradingDatum.K0R_free`). -/
theorem noZeroSMulDivisors_tensor : NoZeroSMulDivisors LP (G.K0R ⊗[LP] G.K0R) := by
  haveI := G.K0R_free hPQ hP hG
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
include hPQ hP hG in
/-- `(K₀(R) ⊗ K₀(R)) ⊗ K₀(R)` is torsion-free over `ℤ[q, q⁻¹]`. -/
theorem noZeroSMulDivisors_tensor₃ :
    NoZeroSMulDivisors LP ((G.K0R ⊗[LP] G.K0R) ⊗[LP] G.K0R) := by
  haveI := G.K0R_free hPQ hP hG
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
/-- **KL I, Proposition 3.2 on all of `K₀(R)`, for any grading datum** in which every class has
a nonzero multiple in the image of `γ`: `Δ(xy) = Δ(x) Δ(y)` for the twisted multiplication
(3.1). -/
theorem coprod_mul_of_exists
    (hex : ∀ x : G.K0R, ∃ p : LP, p ≠ 0 ∧ ∃ y : PreF LP I, G.gammaG y = p • x) (x y : G.K0R) :
    G.coprod hPQ hP hG (x * y) = G.twMul (G.coprod hPQ hP hG x) (G.coprod hPQ hP hG y) := by
  haveI := G.noZeroSMulDivisors_tensor hPQ hP hG
  obtain ⟨p, hp, a, ha⟩ := hex x
  obtain ⟨p', hp', b, hb⟩ := hex y
  have key := G.coprod_mul_gammaG hPQ hP hG a b
  rw [ha, hb, smul_mul_smul_comm, map_smul, map_smul, map_smul, map_smul, LinearMap.smul_apply,
    map_smul, smul_smul] at key
  exact smul_right_injective _ (mul_ne_zero hp hp') key

set_option synthInstance.maxHeartbeats 400000 in
/-- **KL I, Proposition 3.1 (coassociativity of `[Res]`) on all of `K₀(R)`, for any grading
datum** in which every class has a nonzero multiple in the image of `γ`. -/
theorem coassoc_of_exists
    (hex : ∀ x : G.K0R, ∃ p : LP, p ≠ 0 ∧ ∃ y : PreF LP I, G.gammaG y = p • x) (x : G.K0R) :
    (G.coprod hPQ hP hG).rTensor G.K0R (G.coprod hPQ hP hG x) =
      (TensorProduct.assoc LP G.K0R G.K0R G.K0R).symm
        ((G.coprod hPQ hP hG).lTensor G.K0R (G.coprod hPQ hP hG x)) := by
  haveI := G.noZeroSMulDivisors_tensor₃ hPQ hP hG
  obtain ⟨p, hp, a, ha⟩ := hex x
  have key := G.coassoc_gammaG hPQ hP hG a
  rw [ha, map_smul, map_smul, map_smul, map_smul] at key
  exact smul_right_injective _ hp key

/-- **`γ('f_ν) ⊆ K₀(R(ν))`** over `ℤ[q, q⁻¹]`, for any grading datum. -/
theorem gammaG_mem_grade {ν : Multiset I} {x : PreF LP I} (hx : x ∈ PreF.grade LP ν) :
    G.gammaG x ∈ LinearMap.range (DirectSum.lof LP (Multiset I) G.K0fam ν) := by
  rw [PreF.grade, PreF.supp_eq_span] at hx
  have hle : Submodule.span LP (PreF.word '' {w : FreeMonoid I | wt w = ν}) ≤
      (LinearMap.range (DirectSum.lof LP (Multiset I) G.K0fam ν)).comap
        G.gammaG.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply, gammaG_word,
      G.clsW_eq _ hw]
    exact ⟨_, DirectSum.lof_eq_of _ _ _ _ _⟩
  exact hle hx

end GradingDatum

/-! ### KL II -/

namespace KL2Gamma

open KL2 KLGamma

variable {I : Type*} [DecidableEq I] (k : Type*) [Field k] (C : CartanDatum I)

local notation "G2" => klGradingDatum2 k C

/-- `Δ = [Res] : K₀(R) → K₀(R) ⊗ K₀(R)` for the rings `R` of KL II (`GradingDatum.coprod`). -/
abbrev coprodKL2 : (G2).K0R →ₗ[LP] (G2).K0R ⊗[LP] (G2).K0R :=
  (G2).coprod (klQ2_eq_klP2 (o := KL1.stdOrient) KL2.stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) (klGradingDatum2_degX_pos k C)

/-- `γ : 'f_{ℤ[q,q⁻¹]} → K₀(R)`, `θ_i ↦ [P_i]`, for the KL II rings (`GradingDatum.gammaG`). -/
abbrev gammaZ2 : PreF LP I →ₐ[LP] (G2).K0R := (G2).gammaG

theorem gammaZ2_word (w : FreeMonoid I) :
    gammaZ2 k C (word w) = clsSeq2 k C (FreeMonoid.toList w) :=
  GradingDatum.gammaG_word _ w

/-- **Every class of `K₀(R)` (KL II) has a nonzero multiple in `γ('f_{ℤ[q,q⁻¹]})`** (KL II's
Proposition 3.20, `k0B2_mem_span_projDiv2`, and `[P_î] = i! [P_i]`). -/
theorem exists_smul_mem_range_gammaZ2 (x : (G2).K0R) :
    ∃ p : LP, p ≠ 0 ∧ ∃ y : PreF LP I, gammaZ2 k C y = p • x :=
  (G2).exists_smul_mem_range_gammaG_of_div (klQ2_eq_klP2 (o := KL1.stdOrient) KL2.stdOrient_spec)
    (fun a b hab => klP2_ne_zero a b hab) (klGradingDatum2_degX_pos k C)
    (fun _ => projDiv2 k C) (divQFact2 C) (fun _ d h => K0_projSeq2_expandDiv d h)
    (evalOne_divQFact2 C) x

/-- **KL I, Proposition 3.2, for KL II**: `[Res]` is an algebra homomorphism for the twisted
multiplication (3.1) on `K₀(R) ⊗ K₀(R)`: `Δ(xy) = Δ(x) Δ(y)` for all `x, y ∈ K₀(R)`. -/
theorem coprod_mul2 (x y : (G2).K0R) :
    coprodKL2 k C (x * y) = (G2).twMul (coprodKL2 k C x) (coprodKL2 k C y) :=
  (G2).coprod_mul_of_exists _ _ _ (exists_smul_mem_range_gammaZ2 k C) x y

/-- `Δ(1) = 1 ⊗ 1` (KL II). -/
theorem coprod_one2 : coprodKL2 k C 1 = 1 ⊗ₜ 1 :=
  (G2).coprod_one _ _ _

set_option synthInstance.maxHeartbeats 400000 in
/-- **KL I, Proposition 3.1, for KL II (coassociativity of `[Res]`)**: `(Δ ⊗ 1) ∘ Δ = (1 ⊗ Δ) ∘ Δ`
on `K₀(R)`, up to the associativity of `⊗`. -/
theorem coassoc2 (x : (G2).K0R) :
    (coprodKL2 k C).rTensor (G2).K0R (coprodKL2 k C x) =
      (TensorProduct.assoc LP (G2).K0R (G2).K0R (G2).K0R).symm
        ((coprodKL2 k C).lTensor (G2).K0R (coprodKL2 k C x)) :=
  (G2).coassoc_of_exists _ _ _ (exists_smul_mem_range_gammaZ2 k C) x

/-- `γ ⊗ γ` on Lusztig's twisted tensor square for `C` (Cartan pairing `i · j`, `v = q⁻¹`). -/
def gammaZTT2 : TwSq LP I C.dot qUnitLP⁻¹ →ₗ[LP] (G2).K0R ⊗[LP] (G2).K0R :=
  TwistedMonoidAlgebra.lift fun p => gammaZ2 k C (word p.1) ⊗ₜ gammaZ2 k C (word p.2)

theorem gammaZTT2_single (u w : FreeMonoid I) (c : LP) :
    gammaZTT2 k C (TwistedMonoidAlgebra.single (u, w) c) =
      c • (gammaZ2 k C (word u) ⊗ₜ gammaZ2 k C (word w)) :=
  TwistedMonoidAlgebra.lift_single _ _ _

/-- **KL II, Theorem 8 (compatibility of `γ` with the comultiplications), on
`'f_{ℤ[q,q⁻¹]}`**: `[Res] ∘ γ = (γ ⊗ γ) ∘ r` for Lusztig's `r` with the Cartan pairing `i · j`
and `v = q⁻¹` (KL's `q` is Lusztig's `v⁻¹`; the KL II grading has `deg ψ = -i · j`). -/
theorem coprod_gammaZ2 (x : PreF LP I) :
    coprodKL2 k C (gammaZ2 k C x) = gammaZTT2 k C (r C.dot qUnitLP⁻¹ x) := by
  have key : ∀ Z : TwSq LP I (G2).degΨ qUnitLP,
      (G2).gammaTT Z = gammaZTT2 k C (TwistedMonoidAlgebra.recast _ _ Z) := by
    intro Z
    induction Z using TwistedMonoidAlgebra.induction_linear with
    | zero => rw [map_zero, map_zero, map_zero]
    | add Z Z' hZ hZ' => rw [LinearMap.map_add, hZ, hZ', LinearMap.map_add, LinearMap.map_add]
    | single p c =>
      obtain ⟨u, w⟩ := p
      rw [GradingDatum.gammaTT_single, TwistedMonoidAlgebra.recast_single, gammaZTT2_single]
  rw [GradingDatum.coprod_gammaG, key]
  exact congrArg _ (recast_r_neg (dot := C.dot) (v := qUnitLP) x)

/-! ### Weights -/

section Grading

/-- **`γ('f_ν) ⊆ K₀(R(ν))`** over `ℤ[q, q⁻¹]` (KL II). -/
theorem gammaZ2_mem_grade {ν : Multiset I} {x : PreF LP I} (hx : x ∈ PreF.grade LP ν) :
    gammaZ2 k C x ∈ LinearMap.range (DirectSum.lof LP (Multiset I) (G2).K0fam ν) :=
  (G2).gammaG_mem_grade hx

/-- The weight-`ν` part of `K₀(R)_{ℚ(v)}` (KL II): the `ℚ(v)`-span of the image of `K₀(R(ν))`. -/
def K0Qgrade2 (ν : Multiset I) : Submodule (RatFunc ℚ) (K0Q2 k C) :=
  Submodule.span (RatFunc ℚ) (toK0Q2 k C '' Set.range (DirectSum.of (G2).K0fam ν))

/-- **`γ_{ℚ(q)}('f_ν) ⊆ K₀(R(ν))_{ℚ(q)}`** (KL II). -/
theorem gammaQ2_mem_grade {ν : Multiset I} {x : PreF (RatFunc ℚ) I}
    (hx : x ∈ PreF.grade (RatFunc ℚ) ν) : gammaQ2 k C x ∈ K0Qgrade2 k C ν := by
  rw [PreF.grade, PreF.supp_eq_span] at hx
  have hle : Submodule.span (RatFunc ℚ) (PreF.word '' {w : FreeMonoid I | wt w = ν}) ≤
      (K0Qgrade2 k C ν).comap (gammaQ2 k C).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply, gammaQ2_word,
      clsSeq2_eq k C _ hw]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle hx

/-- The projection `K₀(R) → K₀(R(ν)) ⊆ K₀(R)` (KL II). -/
def projK0R2 (ν : Multiset I) : (G2).K0R →ₗ[LP] (G2).K0R :=
  (DirectSum.lof LP (Multiset I) (G2).K0fam ν).comp
    (DirectSum.component LP (Multiset I) (G2).K0fam ν)

attribute [local instance] qToVAlgebra in
/-- Its base change to `K₀(R)_{ℚ(v)}`. -/
def projK0Q2 (ν : Multiset I) : K0Q2 k C →ₗ[RatFunc ℚ] K0Q2 k C :=
  LinearMap.baseChange (RatFunc ℚ) (projK0R2 k C ν)

attribute [local instance] qToVAlgebra in
theorem projK0Q2_toK0Q2 (ν : Multiset I) (x : (G2).K0R) :
    projK0Q2 k C ν (toK0Q2 k C x) = toK0Q2 k C (projK0R2 k C ν x) :=
  LinearMap.baseChange_tmul _ _ _

theorem projK0Q2_of_mem {ν : Multiset I} {y : K0Q2 k C} (hy : y ∈ K0Qgrade2 k C ν) :
    projK0Q2 k C ν y = y := by
  have hle : K0Qgrade2 k C ν ≤ LinearMap.eqLocus (projK0Q2 k C ν) LinearMap.id := by
    rw [K0Qgrade2, Submodule.span_le]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    show projK0Q2 k C ν (toK0Q2 k C _) = toK0Q2 k C _
    rw [projK0Q2_toK0Q2, projK0R2, LinearMap.comp_apply, ← DirectSum.lof_eq_of LP,
      DirectSum.component.lof_self]
  exact hle hy

/-- **`γ(_𝒜 f ∩ f_ν) ⊆ K₀(R(ν))`** for the integral `γ` of KL II (under `hGK`). -/
theorem gammaInt2Equiv_mem_grade (hGK : C.GabberKac vQ C.c) {ν : Multiset I} (x : C.Af)
    {y : PreF (RatFunc ℚ) I} (hy : y ∈ PreF.grade (RatFunc ℚ) ν)
    (hxy : (x : C.F) = PreF.π C.dot vQ C.c y) :
    gammaInt2Equiv k C hGK x ∈ LinearMap.range (DirectSum.lof LP (Multiset I) (G2).K0fam ν) := by
  refine ⟨DirectSum.component LP (Multiset I) (G2).K0fam ν (gammaInt2Equiv k C hGK x),
    toK0Q2_injective k C ?_⟩
  have h1 := projK0Q2_toK0Q2 k C ν (gammaInt2Equiv k C hGK x)
  rw [gammaInt2Equiv_apply, gammaInt2', toK0Q2_gammaInt2, hxy,
    projK0Q2_of_mem k C (y := gammaF2 k C hGK (PreF.π C.dot vQ C.c y))
      (gammaQ2_mem_grade k C hy), ← hxy,
    ← toK0Q2_gammaInt2 k C hGK (toK0Q2_injective k C)] at h1
  exact h1.symm

end Grading

/-! ### Over `ℚ(v)`: `γ` intertwines Lusztig's `r̄ : f → f ⊗ f` with `[Res]` -/

section Rational

attribute [local instance] qToVAlgebra

theorem gammaQ2_word_eq (w : FreeMonoid I) :
    gammaQ2 k C (PreF.word w) = toK0Q2 k C (gammaZ2 k C (PreF.word w)) := by
  rw [gammaQ2_word, gammaZ2_word]

set_option synthInstance.maxHeartbeats 400000 in
/-- `K₀(R) ⊗ K₀(R) → K₀(R)_{ℚ(v)} ⊗_{ℚ(v)} K₀(R)_{ℚ(v)}`, `x ⊗ y ↦ x ⊗ y` (KL II; additive,
and semilinear along `q ↦ v⁻¹`, `toK0QTT2_smul`). -/
def toK0QTT2 : (G2).K0R ⊗[LP] (G2).K0R →+ K0Q2 k C ⊗[RatFunc ℚ] K0Q2 k C :=
  TensorProduct.liftAddHom
    { toFun := fun x =>
        { toFun := fun y => toK0Q2 k C x ⊗ₜ[RatFunc ℚ] toK0Q2 k C y
          map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
          map_add' := fun y y' => by rw [map_add, TensorProduct.tmul_add] }
      map_zero' := by ext y; simp
      map_add' := fun x x' => by ext y; simp [TensorProduct.add_tmul] }
    (fun p x y => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, toK0Q2_smul]
      exact TensorProduct.smul_tmul _ _ _)

set_option synthInstance.maxHeartbeats 400000 in
theorem toK0QTT2_tmul (x y : (G2).K0R) :
    toK0QTT2 k C (x ⊗ₜ y) = toK0Q2 k C x ⊗ₜ[RatFunc ℚ] toK0Q2 k C y :=
  TensorProduct.liftAddHom_tmul _ _ _ _

set_option synthInstance.maxHeartbeats 400000 in
theorem toK0QTT2_smul (p : LP) (Z : (G2).K0R ⊗[LP] (G2).K0R) :
    toK0QTT2 k C (p • Z) = qToV p • toK0QTT2 k C Z := by
  induction Z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul x y =>
    rw [TensorProduct.smul_tmul', toK0QTT2_tmul, toK0QTT2_tmul, toK0Q2_smul,
      TensorProduct.smul_tmul']
  | add Z Z' hZ hZ' => rw [smul_add, map_add, map_add, hZ, hZ', smul_add]

set_option synthInstance.maxHeartbeats 400000 in
/-- `[Res]` over `ℚ(v)` (KL II): the base change of `Δ` along `q ↦ v⁻¹`,
`K₀(R)_{ℚ(v)} → K₀(R)_{ℚ(v)} ⊗_{ℚ(v)} K₀(R)_{ℚ(v)}`. -/
def coprodQ2 : K0Q2 k C →ₗ[RatFunc ℚ] K0Q2 k C ⊗[RatFunc ℚ] K0Q2 k C :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange LP (RatFunc ℚ) (G2).K0R
      (G2).K0R).toLinearMap ∘ₗ (coprodKL2 k C).baseChange (RatFunc ℚ)

set_option synthInstance.maxHeartbeats 400000 in
theorem distribBaseChange_one_tmul2 (Z : (G2).K0R ⊗[LP] (G2).K0R) :
    TensorProduct.AlgebraTensorModule.distribBaseChange LP (RatFunc ℚ) (G2).K0R (G2).K0R
      ((1 : RatFunc ℚ) ⊗ₜ Z) = toK0QTT2 k C Z := by
  induction Z using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, AddMonoidHom.map_zero]
  | tmul x y =>
    rw [toK0QTT2_tmul]
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange, LinearEquiv.symm_apply_eq,
      LinearEquiv.trans_apply]
    change _ = TensorProduct.AlgebraTensorModule.assoc LP LP (RatFunc ℚ) (RatFunc ℚ) (G2).K0R
      (G2).K0R (TensorProduct.AlgebraTensorModule.cancelBaseChange LP (RatFunc ℚ) (RatFunc ℚ)
        (RatFunc ℚ ⊗[LP] (G2).K0R) (G2).K0R
        (((1 : RatFunc ℚ) ⊗ₜ[LP] x) ⊗ₜ[RatFunc ℚ] ((1 : RatFunc ℚ) ⊗ₜ[LP] y)))
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
      TensorProduct.AlgebraTensorModule.assoc_tmul]
  | add Z Z' hZ hZ' =>
    rw [TensorProduct.tmul_add, LinearEquiv.map_add, hZ, hZ', AddMonoidHom.map_add]

set_option synthInstance.maxHeartbeats 400000 in
/-- `Δ_{ℚ(v)}` extends `Δ`: `Δ_{ℚ(v)}(x) = Δ(x)` for `x ∈ K₀(R)` (KL II). -/
theorem coprodQ2_toK0Q2 (y : (G2).K0R) :
    coprodQ2 k C (toK0Q2 k C y) = toK0QTT2 k C (coprodKL2 k C y) := by
  change coprodQ2 k C ((1 : RatFunc ℚ) ⊗ₜ y) = _
  rw [coprodQ2, LinearMap.comp_apply]
  erw [LinearMap.baseChange_tmul]
  exact distribBaseChange_one_tmul2 k C (coprodKL2 k C y)

variable (hGK : C.GabberKac vQ C.c)

set_option synthInstance.maxHeartbeats 400000 in
/-- `(γ ⊗ γ)(r̄ θ_w) = Δ(γ θ_w)` on words `θ_w = θ_{w_1} ⋯ θ_{w_m}` (KL II). -/
theorem map_gammaF2_rbar_word (w : FreeMonoid I) :
    TensorProduct.map (gammaF2 k C hGK).toLinearMap (gammaF2 k C hGK).toLinearMap
        (twSqFEquiv _ _ _ (rbar _ _ _ C.symm (PreF.π C.dot vQ C.c (word w)))) =
      toK0QTT2 k C (gammaZTT2 k C (r C.dot qUnitLP⁻¹ (word w))) := by
  obtain ⟨m, f, rfl⟩ : ∃ (m : ℕ) (f : Fin m → I), FreeMonoid.ofList (List.ofFn f) = w :=
    ⟨_, (FreeMonoid.toList w).get, by rw [List.ofFn_get]; rfl⟩
  rw [twSqFEquiv_rbar_π, r_ofFn, r_ofFn, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [toTensorF_single, LinearMap.map_smul, TensorProduct.map_tmul, gammaZTT2_single,
    toK0QTT2_smul, toK0QTT2_tmul, qToV_qUnitLP_inv_zpow]
  simp only [AlgHom.toLinearMap_apply]
  rw [gammaF2_π, gammaF2_π, gammaQ2_word_eq, gammaQ2_word_eq]

set_option synthInstance.maxHeartbeats 400000 in
/-- **KL II, Theorem 8 (coalgebra part) over `ℚ(v)`**: `γ ⊗ γ` intertwines Lusztig's
comultiplication `r̄ : f → f ⊗ f` (Cartan pairing of `C`) with `[Res]`:
`(γ ⊗ γ)(r̄ x) = Δ_{ℚ(v)}(γ x)` for all `x ∈ f` (`f` defined under the quantum Gabber–Kac
hypothesis `hGK`). -/
theorem map_gammaF2_rbar (x : C.F) :
    TensorProduct.map (gammaF2 k C hGK).toLinearMap (gammaF2 k C hGK).toLinearMap
        (twSqFEquiv _ _ _ (rbar _ _ _ C.symm x)) =
      coprodQ2 k C (gammaF2 k C hGK x) := by
  obtain ⟨y, rfl⟩ := PreF.π_surjective x
  induction y using PreF.induction_linear with
  | zero => simp
  | add y y' hy hy' => rw [map_add, map_add, map_add, map_add, hy, hy', map_add, map_add]
  | smul_word w c =>
    rw [map_smul, map_smul, LinearEquiv.map_smul, LinearMap.map_smul, map_smul,
      LinearMap.map_smul, map_gammaF2_rbar_word]
    congr 1
    change _ = coprodQ2 k C (gammaF2 k C hGK (PreF.π C.dot vQ C.c (word w)))
    rw [gammaF2_π, gammaQ2_word_eq, coprodQ2_toK0Q2, coprod_gammaZ2]

set_option synthInstance.maxHeartbeats 400000 in
/-- **KL II, Theorem 8 (coalgebra part) on `_𝒜 f`**: for `x ∈ _𝒜 f`,
`(γ ⊗ γ)(r̄ x) = Δ(γ x)`, the right-hand side computed integrally in `K₀(R) ⊗ K₀(R)` (with
`γ : _𝒜 f ≅ K₀(R)`, `KL2Gamma.gammaInt2Equiv`). -/
theorem map_gammaF2_rbar_Af (x : C.Af) :
    TensorProduct.map (gammaF2 k C hGK).toLinearMap (gammaF2 k C hGK).toLinearMap
        (twSqFEquiv _ _ _ (rbar _ _ _ C.symm x)) =
      toK0QTT2 k C (coprodKL2 k C (gammaInt2Equiv k C hGK x)) := by
  rw [map_gammaF2_rbar, gammaInt2Equiv_apply, gammaInt2', ← coprodQ2_toK0Q2, toK0Q2_gammaInt2]

omit hGK in
set_option synthInstance.maxHeartbeats 400000 in
/-- `K₀(R) ⊗ K₀(R) → K₀(R)_{ℚ(v)} ⊗ K₀(R)_{ℚ(v)}` is injective for the KL II rings
(`K₀(R) ⊗ K₀(R)` is free over `ℤ[q, q⁻¹]`, and `q ↦ v⁻¹` is injective); so `r̄` determines `Δ`
on `_𝒜 f`. -/
theorem toK0QTT2_injective : Function.Injective (toK0QTT2 k C) := by
  haveI := K0R_free2 k C
  have h1 : Function.Injective fun Z : (G2).K0R ⊗[LP] (G2).K0R =>
      ((1 : RatFunc ℚ) ⊗ₜ[LP] Z : RatFunc ℚ ⊗[LP] ((G2).K0R ⊗[LP] (G2).K0R)) :=
    Algebra.TensorProduct.includeRight_injective (A := RatFunc ℚ) (qToV_injective)
  intro Z Z' h
  apply h1
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange LP (RatFunc ℚ) (G2).K0R
    (G2).K0R).injective
  simp only
  rw [distribBaseChange_one_tmul2, distribBaseChange_one_tmul2, h]

set_option synthInstance.maxHeartbeats 400000 in
/-- **KL II, Theorem 8 in full: `γ : _𝒜 f → K₀(R)` is an isomorphism of `ℕ[I]`-graded twisted
bialgebras**, for an arbitrary Cartan datum `C` and any field `𝕜` (under the quantum Gabber–Kac
hypothesis `hGK` used to define `f`):

1. `γ` is bijective (`KL2Gamma.theorem_8`; it is a ring isomorphism, `gammaInt2Equiv`);
2. it respects the `ℕ[I]`-gradings (`KL2Gamma.gammaInt2Equiv_mem_grade`);
3. `Δ = [Res]` is an algebra homomorphism for the twisted multiplication (3.1), which is
   associative and unital (KL I, Proposition 3.2, for KL II);
4. `Δ` is coassociative (KL I, Proposition 3.1, for KL II);
5. `γ` intertwines Lusztig's `r̄` with `Δ`: for `x ∈ _𝒜 f`, `(γ ⊗ γ)(r̄ x) = Δ(γ x)` (compared in
   `K₀(R)_{ℚ(v)} ⊗ K₀(R)_{ℚ(v)}`, into which `K₀(R) ⊗ K₀(R)` embeds). -/
theorem theorem_8_bialgebra :
    Function.Bijective (gammaInt2' k C hGK) ∧
    (∀ {ν : Multiset I} (x : C.Af) {y : PreF (RatFunc ℚ) I},
      y ∈ PreF.grade (RatFunc ℚ) ν → (x : C.F) = PreF.π C.dot vQ C.c y →
        gammaInt2Equiv k C hGK x ∈
          LinearMap.range (DirectSum.lof LP (Multiset I) (G2).K0fam ν)) ∧
    (∀ x y : (G2).K0R, coprodKL2 k C (x * y) = (G2).twMul (coprodKL2 k C x) (coprodKL2 k C y)) ∧
    coprodKL2 k C 1 = 1 ⊗ₜ 1 ∧
    (∀ X Y Z : (G2).K0R ⊗[LP] (G2).K0R,
      (G2).twMul ((G2).twMul X Y) Z = (G2).twMul X ((G2).twMul Y Z)) ∧
    (∀ X, (G2).twMul (1 ⊗ₜ 1) X = X ∧ (G2).twMul X (1 ⊗ₜ 1) = X) ∧
    (∀ x : (G2).K0R, (coprodKL2 k C).rTensor (G2).K0R (coprodKL2 k C x) =
      (TensorProduct.assoc LP (G2).K0R (G2).K0R (G2).K0R).symm
        ((coprodKL2 k C).lTensor (G2).K0R (coprodKL2 k C x))) ∧
    (∀ x : C.Af,
      TensorProduct.map (gammaF2 k C hGK).toLinearMap (gammaF2 k C hGK).toLinearMap
          (twSqFEquiv _ _ _ (rbar _ _ _ C.symm x)) =
        toK0QTT2 k C (coprodKL2 k C (gammaInt2Equiv k C hGK x))) ∧
    Function.Injective (toK0QTT2 k C) :=
  ⟨theorem_8 k C hGK, fun x _ hy hxy => gammaInt2Equiv_mem_grade k C hGK x hy hxy,
    coprod_mul2 k C, coprod_one2 k C, (G2).twMul_assoc,
    fun X => ⟨(G2).twMul_one_left X, (G2).twMul_one_right X⟩, coassoc2 k C,
    map_gammaF2_rbar_Af k C hGK, toK0QTT2_injective k C⟩

end Rational

end KL2Gamma

end Categorification.KLR
