/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ReflectedStandardWeightResolution
import Categorification.WeightedKLR.RedStrands.BraidedLoadingStandardSupport
import Categorification.WeightedKLR.RedStrands.BraidedReflectedFiltration

/-!
# Graded braid vanishing for reflected standard filtrations

The order on loading labels determines when the strictly higher projectors
annihilate the coefficient layers in Webster, arXiv:1309.3796v2, Lemma 6.11.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR MulOpposite CornerEndomorphism
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
local notation "B" => braidingBimodule k Q Λ ν
local notation "μ" => stendhalWeight ℓ ν

/-- A loading that annihilates every reflected standard layer also annihilates
the actual braid coefficient, by idempotence. This is the coefficient-side
filtration step in Webster, arXiv:1309.3796v2, Lemma 6.11. -/
theorem violLoadingIdem_mul_braidingBimodule_eq_zero_of_reflected_filtration
    (κ' κ : List (Fin ℓ)) {s : Seq μ} (hs : redWord s = κ')
    {m : List {t : Seq μ // redWord t = κ' ∧ ¬ IsViolated t}}
    (hf : ModuleFiltration.HasFiltration
      (fun c => ModuleCat.of (C κ')ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) c.val κ'))
      m (ModuleCat.of (C κ')ᵐᵒᵖ (B κ κ')))
    (hk : ∀ c ∈ m, ∀ x : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) c.val κ',
      op (cornerFlip (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) hs)) • x = 0)
    (p : B κ' κ) :
    (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) hs).val * p.val = 0 := by
  have hf' := hasReflectedStandardFiltration_braidingBimodule (Q := Q) (Λ := Λ) κ' κ hf
  let e := violLoadingIdem (k := k) (Q := Q) (Λ := Λ) hs
  have he : IsIdempotentElem e := isIdempotentElem_violLoadingIdem hs
  have hp : e • p = 0 := hf'.idempotent_smul_eq_zero e he (fun c hc x => hk c hc x) p
  exact congrArg Subtype.val hp

variable (σ : Equiv.Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)

/-- A loading strictly above the support of the reflected standard filtration
annihilates the braid coefficient. -/
theorem violLoadingIdem_mul_braidingBimodule_eq_zero_of_filtration_not_lt
    (killLayer : ∀ {s t d : Seq μ} (_ht : IsRedOrdered t) (hd : IsRedOrdered d),
      StendhalLT s d → ¬ StendhalLT s t →
      ∀ x : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t) κ,
      op (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hd)) • x = 0)
    (κ' : List (Fin ℓ)) {s t : Seq μ} (ht : IsRedOrdered t) (hst : StendhalLT s t)
    {m : List {u : Seq μ // redWord u = κ ∧ ¬ IsViolated u}}
    (hf : ModuleFiltration.HasFiltration
      (fun c => ModuleCat.of (C κ)ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) c.val κ))
      m (ModuleCat.of (C κ)ᵐᵒᵖ (B κ' κ)))
    (hbound : ∀ c ∈ m, ¬ StendhalLT s ((Seq.redPermEquiv σ).symm c.val))
    (p : B κ κ') :
    (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ ht)).val * p.val = 0 := by
  apply violLoadingIdem_mul_braidingBimodule_eq_zero_of_reflected_filtration κ κ'
    (redWord_relabel σ ht) hf _ p
  intro c hc x
  obtain ⟨u, hu⟩ := (Seq.redPermEquiv σ).surjective c.val
  have huo : IsRedOrdered u := by
    have hw := c.property.1
    rw [← hu] at hw
    change redWord (Seq.redPerm σ u) = _ at hw
    rw [redWord_redPerm] at hw
    exact (redWord_eq_finRange_iff _).1 ((List.map_injective_iff.2 σ.injective) hw)
  have hus := hbound c hc
  rw [← hu, (Seq.redPermEquiv σ).symm_apply_apply] at hus
  have hflip : cornerFlip (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ ht)) =
      violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ ht) := by
    apply Subtype.ext
    rw [cornerFlip_val]
    exact (violFlip_violMk _).trans (congrArg (violMk k Q Λ ν) (flip_e _))
  rw [hflip]
  change Seq.redPerm σ u = c.1 at hu
  revert x
  rw [← hu]
  exact killLayer huo ht hst hus

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR QuantumGroup DG ModuleFiltration MulOpposite
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe v

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  {cartan : CartanDatum I} (hR : IsRouquierQ cartan Q)
  (σ : Equiv.Perm (Fin ℓ))
  {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)

private abbrev coefficientGrading (Ω : Fin ℓ → I →₀ ℕ) : KLR.GradingDatum (stendhalQ Q Ω) :=
  stendhalGradingDatum Ω hR.gradingDatum (UDot.di cartan)
    (fun i => (hR.gradingDatum_degX i).trans (UDot.two_mul_di cartan i).symm)

local notation "κ" => List.map σ (List.finRange ℓ)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
local notation "D" => TensorProductAlgebra k Q (Λ ∘ σ) ν
local notation "G" => coefficientGrading hR Λ
local notation "G'" => coefficientGrading hR (Λ ∘ σ)
local notation "V" => violAuxiliaryGrade (ν := ν) G
local notation "hE" => isIdempotentElem_violMk_redProj k Q Λ ν κ
local notation "CG" => Graded.oppositeGrade (Graded.cornerGrading V hE)
local notation "DG'" => tensorProductGrade (G') ν
local notation "ψ" => leftCoefficientEquiv (Λ := Λ) hρ hQ σ
private abbrev OrderedLoading (l : ℕ) (weight : Multiset I) :=
  {t : Seq (stendhalWeight l weight) // IsRedOrdered t}

local notation "Label" => OrderedLoading ℓ ν

private abbrev standardModule (Q : I → I → MvPolynomial (Fin 2) k)
    (Ω : Fin ℓ → I →₀ ℕ) (s : Label) :=
  ModuleCat.of (TensorProductAlgebra k Q Ω ν) (leftStandard Q Ω s.1 s.2)

local notation "Std" => standardModule (ν := ν) Q (Λ ∘ σ)
private abbrev loadingIdem (Q : I → I → MvPolynomial (Fin 2) k)
    (Ω : Fin ℓ → I →₀ ℕ) (t : Label) := seqIdem Q Ω t.1 t.2

private abbrev loadingOrder (t u : Label) := StendhalLT t.1 u.1

local notation "e" => loadingIdem (ν := ν) Q (Λ ∘ σ)
local notation "above" => loadingOrder (ℓ := ℓ) (ν := ν)

private abbrev standardKernel (Q : I → I → MvPolynomial (Fin 2) k)
    (Ω : Fin ℓ → I →₀ ℕ) (t : Label) :=
  (leftUpper Q Ω t.1 t.2).comap (lIdeal (seqIdem Q Ω t.1 t.2)).subtype

variable (hU : ∀ t : OrderedLoading ℓ ν, ∃ m : List (OrderedLoading ℓ ν),
  (∀ u ∈ m, StendhalLT t.1 u.1) ∧
    HasFiltration (standardModule Q (Λ ∘ σ)) m
      (ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ σ) ν) (standardKernel Q (Λ ∘ σ) t)))
  (s : OrderedLoading ℓ ν)

local notation "data" => orderedStandardCovers Q (Λ ∘ σ) hU

local notation "TargetGrade" c:arg =>
  Graded.oppositeGrade (Graded.cornerGrading V (isIdempotentElem_violMk_redProj k Q Λ ν c))

include hU in
/-- A reflected filtration with no layer strictly above the input loading
gives concentration in cohomological degree zero. -/
theorem reflectedStandardWeightBraiding_isZero_of_not_lt_filtration (κ' : List (Fin ℓ))
    {layers : List {t : Seq (stendhalWeight ℓ ν) // redWord t = κ ∧ ¬ IsViolated t}}
    (hF : HasFiltration
      (fun t => ModuleCat.of Cᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t.val κ))
      layers (ModuleCat.of Cᵐᵒᵖ (braidingBimodule k Q Λ ν κ' κ)))
    (hbound : ∀ t ∈ layers, ¬ StendhalLT s.val ((Seq.redPermEquiv σ).symm t.val)) :
    letI := Graded.cornerGradedAlgebra V hE (redProj_mem_violAuxiliaryGrade G κ)
    letI := Graded.cornerGradedAlgebra V (isIdempotentElem_violMk_redProj k Q Λ ν κ')
      (redProj_mem_violAuxiliaryGrade G κ')
    letI := gradedAlgebraInternalGrading CG
    letI := gradedAlgebraInternalGrading (TargetGrade κ')
    letI := gradedAlgebraBigradedDGRing CG
    letI := gradedAlgebraBigradedDGRing (TargetGrade κ')
    ∀ [CatModule.HasDerivedCategory.{v,0} (WeightCategory (hE).Cornerᵐᵒᵖ)]
      [CatModule.HasDerivedCategory.{v,0}
        (WeightCategory (isIdempotentElem_violMk_redProj k Q Λ ν κ').Cornerᵐᵒᵖ)]
      (X : WeightCategory (isIdempotentElem_violMk_redProj k Q Λ ν κ').Cornerᵐᵒᵖ) (n : ℤ),
      n ≠ 0 →
      CategoryTheory.Limits.IsZero
        (reflectedStandardWeightBraidingCohomology hR σ hρ hQ s κ' X n) := by
  have killLayer : ∀ {u t d : Seq (stendhalWeight ℓ ν)} (_ht : IsRedOrdered t) (hd : IsRedOrdered d),
      StendhalLT u d → ¬ StendhalLT u t →
      ∀ x : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t) κ,
      op (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hd)) • x = 0 := by
    intro u t d ht hd hud hut x
    exact violLoadingIdem_smul_violLoadingStandard_eq_zero_of_not_lt
      (Λ := Λ) hρ hQ σ ht hd hud hut x
  intro hSource hTarget X n hn
  exact reflectedStandardWeightBraiding_isZero hR σ hρ hQ hU s κ' X n hn
    (fun t ht p =>
      violLoadingIdem_mul_braidingBimodule_eq_zero_of_filtration_not_lt
        σ killLayer κ' t.property ht hF hbound p)

end Categorification.Stendhal.BraidedStendhalAlgebra
