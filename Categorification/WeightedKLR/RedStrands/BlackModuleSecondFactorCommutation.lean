/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensorFactorLiftRight
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossNaturality
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeftNaturality
import Categorification.WeightedKLR.RedStrands.SingleRedInduction
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastInduction

/-!
# Commutation of `₂Eⱼ` and `₂Fᵢ` on modules over the factor algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Theorem 4.31, in the proof of Proposition 5.5.

The cyclotomic KLR algebra `R^{λ_ℓ}` is the tensor product algebra with one red strand
(`SingleRed.cyclotomicEquiv`, Theorem 4.20 there), and this isomorphism intertwines appending a
black strand on the right with the last-colour inclusion `AbsentColour.cyclotomicLast`
(`SingleRed.appendBlack_cyclotomicEquiv`). So the commutation relations of `Eⱼ` and `Fᵢ` on left
`T^λ`-modules at one red strand (`clLeftBlackModuleCrossEquiv`, `clLeftBlackModuleEFEquiv`,
`clLeftBlackModuleFEEquiv`, standard Khovanov–Lauda black scalars) transport to modules over
`R^{λ_ℓ}` (`cycCrossEquiv`, `cycEFEquiv`, `cycFEEquiv`), naturally in the module. Over the
factor algebra `D = T^{λ₁}_θ ⊗ R^{λ_ℓ}_β`, the functors `₂Eⱼ` (restriction along
`1 ⊗ cyclotomicLast`) and `₂Fᵢ` (induction along it) then satisfy the same relations: these are
the lifts to the right tensor factor (`InductionAlong.liftResIndEquivRight`,
`liftResIndProdEquivRight`, `liftIndResProdEquivRight`).

## Main definitions

* `secondFactorCrossEquiv`: `₂Eⱼ ₂Fᵢ N ≅ ₂Fᵢ ₂Eⱼ N` for `i ≠ j`.
* `secondFactorEFEquiv`: `₂Eᵢ ₂Fᵢ N ≅ ₂Fᵢ ₂Eᵢ N ⊕ N^{⊕ n}` when the weight pairing `n` of the
  cyclotomic factor is `≥ 0`.
* `secondFactorFEEquiv`: `₂Fᵢ ₂Eᵢ N ≅ ₂Eᵢ ₂Fᵢ N ⊕ N^{⊕ -n}` when it is `≤ 0`.

## Main results

* `finrank_secondFactorCross_eq`, `finrank_secondFactorEF_eq`: the dimension forms.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite
open scoped TensorProduct

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w

section CycView

variable {I : Type u} {k : Type u} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ₁ : Fin 1 → I →₀ ℕ)

local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ₁ 0 j
local notation "Cyc" => CycKLR k Q aΛ

/-- Theorem 4.20 of Webster as a ring isomorphism `R^λ_ν ≃ T^λ_ν` (one red strand). -/
abbrev cycRingEquiv (ν : Multiset I) : Cyc ν ≃+* TensorProductAlgebra k Q Λ₁ ν :=
  (SingleRed.cyclotomicEquiv Q Λ₁ ν).toRingEquiv

/-- The last-colour inclusion `R^λ_ν → R^λ_{i+ν}` as a nonunital ring map. -/
abbrev cycLastHom (i : I) (ν : Multiset I) : Cyc ν →ₙ+* Cyc ((Singleton.singleton i) + ν) :=
  NonUnitalRingHomClass.toNonUnitalRingHom (KLRAlgebra.AbsentColour.cyclotomicLast Q i aΛ ν)

/-- `cycLastHom` with the content of the target given by an equality. -/
def cycLastHomOfEq (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν') : Cyc μ →ₙ+* Cyc ν' :=
  hc ▸ cycLastHom Q Λ₁ j μ

theorem cycLastHom_smul (i : I) (ν : Multiset I) (c : k) (t : Cyc ν) :
    cycLastHom Q Λ₁ i ν (c • t) = c • cycLastHom Q Λ₁ i ν t :=
  map_smul (KLRAlgebra.AbsentColour.cyclotomicLast Q i aΛ ν) c t

theorem appendBlackNU_cycRingEquiv (i : I) (ν : Multiset I) (t : Cyc ν) :
    appendBlackNU (Q := Q) (Λ := Λ₁) i ν (cycRingEquiv Q Λ₁ ν t) =
      cycRingEquiv Q Λ₁ ((Singleton.singleton i) + ν) (cycLastHom Q Λ₁ i ν t) :=
  SingleRed.appendBlack_cyclotomicEquiv i ν Q Λ₁ t

theorem appendBlackNUOfEq_cycRingEquiv (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν')
    (t : Cyc μ) :
    appendBlackNUOfEq Q Λ₁ j hc (cycRingEquiv Q Λ₁ μ t) =
      cycRingEquiv Q Λ₁ ν' (cycLastHomOfEq Q Λ₁ j hc t) := by
  subst hc
  exact appendBlackNU_cycRingEquiv Q Λ₁ j μ t

/-- A module over `R^λ_ν`, viewed as a module over `T^λ_ν` through Theorem 4.20. -/
@[nolint unusedArguments]
def CycView (_ : I → I → MvPolynomial (Fin 2) k) (_ : Fin 1 → I →₀ ℕ) (_ : Multiset I)
    (M : Type w) : Type w := M

-- The algebra is written out: notation is not hygienic inside `variable` binders.
variable (ν : Multiset I) (M : Type w) [AddCommGroup M]
  [Module (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ₁ 0 j) ν) M]

instance : AddCommGroup (CycView Q Λ₁ ν M) := inferInstanceAs (AddCommGroup M)

instance : Module (TensorProductAlgebra k Q Λ₁ ν) (CycView Q Λ₁ ν M) :=
  Module.compHom M (cycRingEquiv Q Λ₁ ν).symm.toRingHom

/-- The identity of `M`, from the `R^λ_ν`-module to its `T^λ_ν`-module view. -/
def toCycView : M ≃+ CycView Q Λ₁ ν M := AddEquiv.refl M

theorem toCycView_smul (t : Cyc ν) (m : M) :
    toCycView Q Λ₁ ν M (t • m) = cycRingEquiv Q Λ₁ ν t • toCycView Q Λ₁ ν M m := by
  change t • m = (cycRingEquiv Q Λ₁ ν).symm (cycRingEquiv Q Λ₁ ν t) • m
  rw [RingEquiv.symm_apply_apply]

variable {M} {M₂ : Type w} [AddCommGroup M₂]
  [Module (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ₁ 0 j) ν) M₂]

/-- A map of `R^λ_ν`-modules, as a map of their `T^λ_ν`-module views. -/
def cycViewMap (f : M →ₗ[Cyc ν] M₂) :
    CycView Q Λ₁ ν M →ₗ[TensorProductAlgebra k Q Λ₁ ν] CycView Q Λ₁ ν M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' t m := f.map_smul ((cycRingEquiv Q Λ₁ ν).symm t) m

end CycView

section CycCL

variable {I : Type u} {Λ₁ : Fin 1 → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RD₁" => coordinateDatum Λ₁ C
local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "Cyc" => CycKLR k (CL.qCL KL) (fun j => (Polynomial.X : Polynomial k) ^ Λ₁ 0 j)
local notation "cR" => cycRingEquiv (CL.qCL KL) Λ₁
local notation "cL" => cycLastHom (CL.qCL KL) Λ₁

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ₁ C) (redWeight (cyclotomicCoverWeightDatum Λ₁ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ₁ C hQ (coverDotCentral Λ₁ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ₁ C) (cyclotomicCoverHighest (I := I) (ℓ := 1)) 0 :
      I ⊕ Fin 1 → ℤ) P)
  (hwf : P.WFDom)

section Cross

variable (i j : I) (ρ : Multiset I)

local notation "Sj" => (Singleton.singleton j : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)

variable {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (CycKLR k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))
    (fun j => (Polynomial.X : Polynomial k) ^ Λ₁ 0 j) ({j} + ρ)) M]
  [Module (CycKLR k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))
    (fun j => (Polynomial.X : Polynomial k) ^ Λ₁ 0 j) ({j} + ρ)) M₂]

/-- **`Eⱼ Fᵢ` against `Fᵢ Eⱼ` on modules over the cyclotomic KLR algebra**, `i ≠ j` (Webster,
arXiv:1309.3796v3, Theorem 4.31 at one red strand, through Theorem 4.20): for every module `M`
over `R^λ_{j+ρ}`, `Eⱼ Fᵢ M ≅ Fᵢ Eⱼ M` over `R^λ_{i+ρ}`, with `Fᵢ` induction and `Eⱼ` restriction
along the last-colour inclusions. -/
def cycCrossEquiv (hji : j ≠ i) (M : Type u) [AddCommGroup M] [Module (Cyc (Sj + ρ)) M] :
    Res (cycLastHomOfEq (CL.qCL KL) Λ₁ j (cross_content i j ρ)) (Ind M (cL i (Sj + ρ)))
      ≃ₗ[Cyc (Si + ρ)] Ind (Res (cL j ρ) M) (cL i ρ) :=
  resIndCrossEquivTransport (cR ρ) (cR (Sj + ρ)) (cR (Si + ρ)) (cR (Si + (Sj + ρ)))
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ j ρ)
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i (Sj + ρ))
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i ρ)
    (appendBlackNUOfEq_cycRingEquiv (CL.qCL KL) Λ₁ j (cross_content i j ρ))
    (toCycView (CL.qCL KL) Λ₁ (Sj + ρ) M) (toCycView_smul (CL.qCL KL) Λ₁ (Sj + ρ) M)
    (clLeftBlackModuleCrossEquiv hstd hP hwf i j ρ (CycView (CL.qCL KL) Λ₁ (Sj + ρ) M) hji)

/-- **Naturality of `cycCrossEquiv`**: it carries `Eⱼ Fᵢ f` to `Fᵢ Eⱼ f`. -/
theorem cycCrossEquiv_map (hji : j ≠ i) (f : M →ₗ[Cyc (Sj + ρ)] M₂)
    (x : Res (cycLastHomOfEq (CL.qCL KL) Λ₁ j (cross_content i j ρ)) (Ind M (cL i (Sj + ρ)))) :
    cycCrossEquiv hstd hP hwf i j ρ hji M₂ (Res.map (Ind.map f) x) =
      Ind.map (Res.map f) (cycCrossEquiv hstd hP hwf i j ρ hji M x) := by
  kernel_exact resIndCrossEquivTransport_map (cR ρ) (cR (Sj + ρ)) (cR (Si + ρ))
    (cR (Si + (Sj + ρ)))
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ j ρ)
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i (Sj + ρ))
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i ρ)
    (appendBlackNUOfEq_cycRingEquiv (CL.qCL KL) Λ₁ j (cross_content i j ρ))
    (toCycView (CL.qCL KL) Λ₁ (Sj + ρ) M) (toCycView_smul (CL.qCL KL) Λ₁ (Sj + ρ) M)
    (toCycView (CL.qCL KL) Λ₁ (Sj + ρ) M₂) (toCycView_smul (CL.qCL KL) Λ₁ (Sj + ρ) M₂)
    f (cycViewMap (CL.qCL KL) Λ₁ (Sj + ρ) f) (fun _ => rfl)
    (clLeftBlackModuleCrossEquiv hstd hP hwf i j ρ (CycView (CL.qCL KL) Λ₁ (Sj + ρ) M) hji)
    (clLeftBlackModuleCrossEquiv hstd hP hwf i j ρ (CycView (CL.qCL KL) Λ₁ (Sj + ρ) M₂) hji)
    (fun y => by
      kernel_exact clLeftBlackModuleCrossEquiv_map hstd hP hwf i j ρ hji
        (cycViewMap (CL.qCL KL) Λ₁ (Sj + ρ) f) y) x

end Cross

section EF

variable (i : I) (ν : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "n₂" =>
  ip (RD₁) i (downRightWeight (RD₁) (coordinateRedWeights Λ₁ C) (Si + ν))

variable {M M₂ : Type u} [AddCommGroup M] [AddCommGroup M₂]
  [Module (CycKLR k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))
    (fun j => (Polynomial.X : Polynomial k) ^ Λ₁ 0 j) ({i} + ν)) M]
  [Module (CycKLR k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))
    (fun j => (Polynomial.X : Polynomial k) ^ Λ₁ 0 j) ({i} + ν)) M₂]

/-- **`Eᵢ Fᵢ` against `Fᵢ Eᵢ` on modules over the cyclotomic KLR algebra** (Webster,
arXiv:1309.3796v3, Theorem 4.31 at one red strand, through Theorem 4.20): for `n = ⟨i, λ⟩ ≥ 0`,
with `λ` the right weight of content `i + ν`, `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` for every module
`M` over `R^λ_{i+ν}`. -/
def cycEFEquiv (hn : 0 ≤ n₂) (M : Type u) [AddCommGroup M] [Module (Cyc (Si + ν)) M] :=
  resIndEquivTransport (cR ν) (cR (Si + ν)) (cR (Si + (Si + ν)))
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i ν)
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i (Si + ν))
    (toCycView (CL.qCL KL) Λ₁ (Si + ν) M) (toCycView_smul (CL.qCL KL) Λ₁ (Si + ν) M) _
    (clLeftBlackModuleEFEquiv hstd hP hwf i ν (CycView (CL.qCL KL) Λ₁ (Si + ν) M) hn)

/-- **`Fᵢ Eᵢ` against `Eᵢ Fᵢ` on modules over the cyclotomic KLR algebra** (Webster,
arXiv:1309.3796v3, Theorem 4.31 at one red strand, through Theorem 4.20): for `n = ⟨i, λ⟩ ≤ 0`,
`Fᵢ Eᵢ M ≅ Eᵢ Fᵢ M ⊕ M^{⊕ -n}` for every module `M` over `R^λ_{i+ν}`. -/
def cycFEEquiv (hn : n₂ ≤ 0) (M : Type u) [AddCommGroup M] [Module (Cyc (Si + ν)) M] :=
  indResEquivTransport (cR ν) (cR (Si + ν)) (cR (Si + (Si + ν)))
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i ν)
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i (Si + ν))
    (toCycView (CL.qCL KL) Λ₁ (Si + ν) M) (toCycView_smul (CL.qCL KL) Λ₁ (Si + ν) M) _
    (clLeftBlackModuleFEEquiv hstd hP hwf i ν (CycView (CL.qCL KL) Λ₁ (Si + ν) M) hn)

/-- **Naturality of `cycEFEquiv`**: it carries `Eᵢ Fᵢ f` to `Fᵢ Eᵢ f × f^n`. -/
theorem cycEFEquiv_map (f : M →ₗ[Cyc (Si + ν)] M₂) (hn : 0 ≤ n₂)
    (x : Res (cL i (Si + ν)) (Ind M (cL i (Si + ν)))) :
    cycEFEquiv hstd hP hwf i ν hn M₂ (Res.map (Ind.map f) x) =
      (Ind.map (Res.map f) (cycEFEquiv hstd hP hwf i ν hn M x).1,
        fun s => f ((cycEFEquiv hstd hP hwf i ν hn M x).2 s)) := by
  kernel_exact resIndEquivTransport_map (cR ν) (cR (Si + ν)) (cR (Si + (Si + ν)))
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i ν)
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i (Si + ν))
    (toCycView (CL.qCL KL) Λ₁ (Si + ν) M) (toCycView_smul (CL.qCL KL) Λ₁ (Si + ν) M)
    (toCycView (CL.qCL KL) Λ₁ (Si + ν) M₂) (toCycView_smul (CL.qCL KL) Λ₁ (Si + ν) M₂)
    f (cycViewMap (CL.qCL KL) Λ₁ (Si + ν) f) (fun _ => rfl) _
    (clLeftBlackModuleEFEquiv hstd hP hwf i ν (CycView (CL.qCL KL) Λ₁ (Si + ν) M) hn)
    (clLeftBlackModuleEFEquiv hstd hP hwf i ν (CycView (CL.qCL KL) Λ₁ (Si + ν) M₂) hn)
    (fun y => by
      kernel_exact clLeftBlackModuleEFEquiv_map hstd hP hwf i ν
        (cycViewMap (CL.qCL KL) Λ₁ (Si + ν) f) hn y) x

/-- **Naturality of `cycFEEquiv`**: it carries `Fᵢ Eᵢ f` to `Eᵢ Fᵢ f × f^{-n}`. -/
theorem cycFEEquiv_map (f : M →ₗ[Cyc (Si + ν)] M₂) (hn : n₂ ≤ 0)
    (x : Ind (Res (cL i ν) M) (cL i ν)) :
    cycFEEquiv hstd hP hwf i ν hn M₂ (Ind.map (Res.map f) x) =
      (Res.map (Ind.map f) (cycFEEquiv hstd hP hwf i ν hn M x).1,
        fun s => f ((cycFEEquiv hstd hP hwf i ν hn M x).2 s)) := by
  kernel_exact indResEquivTransport_map (cR ν) (cR (Si + ν)) (cR (Si + (Si + ν)))
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i ν)
    (appendBlackNU_cycRingEquiv (CL.qCL KL) Λ₁ i (Si + ν))
    (toCycView (CL.qCL KL) Λ₁ (Si + ν) M) (toCycView_smul (CL.qCL KL) Λ₁ (Si + ν) M)
    (toCycView (CL.qCL KL) Λ₁ (Si + ν) M₂) (toCycView_smul (CL.qCL KL) Λ₁ (Si + ν) M₂)
    f (cycViewMap (CL.qCL KL) Λ₁ (Si + ν) f) (fun _ => rfl) _
    (clLeftBlackModuleFEEquiv hstd hP hwf i ν (CycView (CL.qCL KL) Λ₁ (Si + ν) M) hn)
    (clLeftBlackModuleFEEquiv hstd hP hwf i ν (CycView (CL.qCL KL) Λ₁ (Si + ν) M₂) hn)
    (fun y => by
      kernel_exact clLeftBlackModuleFEEquiv_map hstd hP hwf i ν
        (cycViewMap (CL.qCL KL) Λ₁ (Si + ν) f) hn y) x

end EF

end CycCL

section Cast

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

/-- `parabolicRightHom` with the content of the target given by an equality. -/
def parabolicRightHomOfEq (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν') (θ : Multiset I) :
    parabolicFactorAlgebra Q Λ θ μ →ₙ+* parabolicFactorAlgebra Q Λ θ ν' :=
  hc ▸ parabolicRightHom Q Λ j θ μ

theorem parabolicRightHom_tmul (j : I) (θ μ : Multiset I)
    (c : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ)
    (a : CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) μ) :
    parabolicRightHom Q Λ j θ μ (c ⊗ₜ a) =
      c ⊗ₜ cycLastHom Q (fun _ : Fin 1 => Λ (Fin.last ℓ)) j μ a := rfl

theorem parabolicRightHomOfEq_tmul (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν')
    (θ : Multiset I) (c : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ)
    (a : CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) μ) :
    parabolicRightHomOfEq Q Λ j hc θ (c ⊗ₜ a) =
      c ⊗ₜ cycLastHomOfEq Q (fun _ : Fin 1 => Λ (Fin.last ℓ)) j hc a := by
  subst hc
  rfl

end Cast

section Dimension

variable {k T : Type*} [Field k] [Ring T] [Algebra k T]
  {X Y : Type*} [AddCommGroup X] [Module T X] [AddCommGroup Y] [Module T Y]

/-- The `k`-dimension form of an isomorphism of modules over a `k`-algebra `T`, with
`k`-structures through `T`. -/
theorem finrank_restrictScalars_eq_of_equiv (L : X ≃ₗ[T] Y) :
    Module.finrank k (RestrictScalars k T X) = Module.finrank k (RestrictScalars k T Y) := by
  let e : RestrictScalars k T X ≃ₗ[k] RestrictScalars k T Y :=
    { toFun := fun x => (RestrictScalars.addEquiv k T Y).symm
        (L ((RestrictScalars.addEquiv k T X) x))
      invFun := fun y => (RestrictScalars.addEquiv k T X).symm
        (L.symm ((RestrictScalars.addEquiv k T Y) y))
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        change L (algebraMap k T c • (RestrictScalars.addEquiv k T X) x) = _
        rw [L.map_smul]; rfl
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  exact e.finrank_eq

end Dimension

section CL

variable {I : Type u} {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "Λ₁" => (fun _ : Fin 1 => Λ (Fin.last ℓ))
local notation "RD₁" => coordinateDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C
local notation "D" => parabolicFactorAlgebra (CL.qCL KL) Λ
local notation "cL" => cycLastHom (CL.qCL KL) (fun _ : Fin 1 => Λ (Fin.last ℓ))
local notation "ψ" => parabolicRightHom (CL.qCL KL) Λ

-- The weight `Λ₁` is written out: notation is not hygienic inside `variable` binders.
variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C)
      (redWeight (cyclotomicCoverWeightDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C))) k}
  (hP : CoverRelsNegligible.{u, u, w} (fun _ : Fin 1 => Λ (Fin.last ℓ)) C hQ
    (coverDotCentral (fun _ : Fin 1 => Λ (Fin.last ℓ)) C hQ)
    (blockWeight (cyclotomicCoverWeightDatum (fun _ : Fin 1 => Λ (Fin.last ℓ)) C)
      (cyclotomicCoverHighest (I := I) (ℓ := 1)) 0 : I ⊕ Fin 1 → ℤ) P)
  (hwf : P.WFDom) (θ : Multiset I)

section Cross

variable (i j : I) (ρ : Multiset I)

local notation "Sj" => (Singleton.singleton j : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)

/-- **`₂Eⱼ ₂Fᵢ` against `₂Fᵢ ₂Eⱼ` over the factor algebra**, `i ≠ j` (Webster,
arXiv:1309.3796v3, Theorem 4.31 on the second factor, in the proof of Proposition 5.5): for every
module `N` over `D_{θ, j+ρ}`, `₂Eⱼ ₂Fᵢ N ≅ ₂Fᵢ ₂Eⱼ N` over `D_{θ, i+ρ}`. -/
def secondFactorCrossEquiv (hji : j ≠ i) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D θ (Sj + ρ)) N] [IsScalarTower k (D θ (Sj + ρ)) N] :
    Res (parabolicRightHomOfEq (CL.qCL KL) Λ j (cross_content i j ρ) θ)
        (IndK k N (ψ i θ (Sj + ρ))) ≃ₗ[D θ (Si + ρ)]
      IndK k (Res (ψ j θ ρ) N) (ψ i θ ρ) :=
  liftResIndEquivRight
    (cycLastHomOfEq (CL.qCL KL) Λ₁ j (cross_content i j ρ))
    (parabolicRightHomOfEq (CL.qCL KL) Λ j (cross_content i j ρ) θ)
    (parabolicRightHomOfEq_tmul (CL.qCL KL) Λ j (cross_content i j ρ) θ)
    (cL i (Sj + ρ)) (cycLastHom_smul (CL.qCL KL) Λ₁ i (Sj + ρ))
    (ψ i θ (Sj + ρ)) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ (Sj + ρ))
    (cL j ρ) (ψ j θ ρ) (parabolicRightHom_tmul (CL.qCL KL) Λ j θ ρ)
    (cL i ρ) (cycLastHom_smul (CL.qCL KL) Λ₁ i ρ)
    (ψ i θ ρ) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ ρ)
    (fun M _ _ => cycCrossEquiv hstd hP hwf i j ρ hji M)
    (fun _ _ _ _ _ _ f x => cycCrossEquiv_map hstd hP hwf i j ρ hji f x) N

include hstd hP hwf in
/-- **The dimension form of `secondFactorCrossEquiv`** (Webster, arXiv:1309.3796v3, in the
dimension count of the proof of Proposition 5.5): `dim ₂Eⱼ ₂Fᵢ N = dim ₂Fᵢ ₂Eⱼ N` over `k`, for
`i ≠ j`. -/
theorem finrank_secondFactorCross_eq (hji : j ≠ i) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D θ (Sj + ρ)) N] [IsScalarTower k (D θ (Sj + ρ)) N] :
    Module.finrank k (RestrictScalars k (D θ (Si + ρ))
        (Res (parabolicRightHomOfEq (CL.qCL KL) Λ j (cross_content i j ρ) θ)
          (IndK k N (ψ i θ (Sj + ρ))))) =
      Module.finrank k (RestrictScalars k (D θ (Si + ρ))
        (IndK k (Res (ψ j θ ρ) N) (ψ i θ ρ))) :=
  finrank_restrictScalars_eq_of_equiv (secondFactorCrossEquiv hstd hP hwf θ i j ρ hji N)

end Cross

section EF

variable (i : I) (ν : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "n₂" =>
  ip (RD₁) i (downRightWeight (RD₁) (coordinateRedWeights Λ₁ C) (Si + ν))

/-- **`₂Eᵢ ₂Fᵢ` against `₂Fᵢ ₂Eᵢ` over the factor algebra** (Webster, arXiv:1309.3796v3,
Theorem 4.31 on the second factor, in the proof of Proposition 5.5): for `n = ⟨i, λ⟩ ≥ 0`, with
`λ` the right weight of content `i + ν` of the one-red-strand algebra of the cyclotomic factor
`R^{λ_ℓ}`, `₂Eᵢ ₂Fᵢ N ≅ ₂Fᵢ ₂Eᵢ N ⊕ N^{⊕ n}` for every module `N` over `D_{θ, i+ν}`. -/
def secondFactorEFEquiv (hn : 0 ≤ n₂) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D θ (Si + ν)) N] [IsScalarTower k (D θ (Si + ν)) N] :=
  liftResIndProdEquivRight _
    (cL i (Si + ν)) (ψ i θ (Si + ν)) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ (Si + ν))
    (cL i (Si + ν)) (cycLastHom_smul (CL.qCL KL) Λ₁ i (Si + ν))
    (ψ i θ (Si + ν)) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ (Si + ν))
    (cL i ν) (ψ i θ ν) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ ν)
    (cL i ν) (cycLastHom_smul (CL.qCL KL) Λ₁ i ν)
    (ψ i θ ν) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ ν)
    (fun M _ _ => cycEFEquiv hstd hP hwf i ν hn M)
    (fun _ _ _ _ _ _ f x => cycEFEquiv_map hstd hP hwf i ν f hn x) N

/-- **`₂Fᵢ ₂Eᵢ` against `₂Eᵢ ₂Fᵢ` over the factor algebra** (Webster, arXiv:1309.3796v3,
Theorem 4.31 on the second factor, in the proof of Proposition 5.5): for `n = ⟨i, λ⟩ ≤ 0`,
`₂Fᵢ ₂Eᵢ N ≅ ₂Eᵢ ₂Fᵢ N ⊕ N^{⊕ -n}` for every module `N` over `D_{θ, i+ν}`. -/
def secondFactorFEEquiv (hn : n₂ ≤ 0) (N : Type u) [AddCommGroup N] [Module k N]
    [Module (D θ (Si + ν)) N] [IsScalarTower k (D θ (Si + ν)) N] :=
  liftIndResProdEquivRight _
    (cL i (Si + ν)) (ψ i θ (Si + ν)) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ (Si + ν))
    (cL i (Si + ν)) (cycLastHom_smul (CL.qCL KL) Λ₁ i (Si + ν))
    (ψ i θ (Si + ν)) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ (Si + ν))
    (cL i ν) (ψ i θ ν) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ ν)
    (cL i ν) (cycLastHom_smul (CL.qCL KL) Λ₁ i ν)
    (ψ i θ ν) (parabolicRightHom_tmul (CL.qCL KL) Λ i θ ν)
    (fun M _ _ => cycFEEquiv hstd hP hwf i ν hn M)
    (fun _ _ _ _ _ _ f x => cycFEEquiv_map hstd hP hwf i ν f hn x) N

variable (N : Type u) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ θ ({i} + ν)) N]
  [IsScalarTower k
    (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ θ ({i} + ν)) N]

local notation "EF₂" => Res (parabolicRightHom (CL.qCL KL) Λ i θ (Si + ν))
  (IndK k N (parabolicRightHom (CL.qCL KL) Λ i θ (Si + ν)))
local notation "FE₂" => IndK k (Res (parabolicRightHom (CL.qCL KL) Λ i θ ν) N)
  (parabolicRightHom (CL.qCL KL) Λ i θ ν)
local notation "D₁" => parabolicFactorAlgebra (CL.qCL KL) Λ θ (Si + ν)

include hstd hP hwf in
/-- **The dimension form of the `₂Eᵢ`/`₂Fᵢ` commutation relation** (Webster,
arXiv:1309.3796v3, in the dimension count of the proof of Proposition 5.5):
`dim ₂Eᵢ ₂Fᵢ N = dim ₂Fᵢ ₂Eᵢ N + n dim N` over `k`, in both signs of `n`. -/
theorem finrank_secondFactorEF_eq
    [FiniteDimensional k (RestrictScalars k D₁ EF₂)]
    [FiniteDimensional k (RestrictScalars k D₁ FE₂)]
    [FiniteDimensional k (RestrictScalars k D₁ N)] :
    (Module.finrank k (RestrictScalars k D₁ EF₂) : ℤ) =
      Module.finrank k (RestrictScalars k D₁ FE₂) +
        n₂ * Module.finrank k (RestrictScalars k D₁ N) := by
  rcases le_total 0 n₂ with h | h
  · have e := finrank_restrictScalars_eq_of_equiv_prod (k := k)
      (secondFactorEFEquiv hstd hP hwf θ i ν h N)
    rw [e, Fintype.card_fin]
    push_cast
    rw [Int.toNat_of_nonneg h]
  · have e := congrArg (Nat.cast : ℕ → ℤ) (finrank_restrictScalars_eq_of_equiv_prod (k := k)
      (secondFactorFEEquiv hstd hP hwf θ i ν h N))
    rw [Fintype.card_fin] at e
    push_cast at e
    rw [Int.toNat_of_nonneg (by omega)] at e
    linear_combination -e

end EF

end CL

end Categorification.Stendhal
