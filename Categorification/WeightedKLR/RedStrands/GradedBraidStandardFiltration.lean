/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardConcentrated
import Categorification.WeightedKLR.RedStrands.GradedBraidResolution
import Categorification.WeightedKLR.RedStrands.RightStandardProjectiveDimension
import Categorification.WeightedKLR.RedStrands.StandardProjectiveDimension
import Categorification.Algebra.Graded.FiniteResolution
import Categorification.WeightedKLR.RedStrands.OrderedStandardResolution
import Categorification.WeightedKLR.RedStrands.StandardStratification

set_option backward.isDefEq.respectTransparency false

/-!
# Graded modules with standard filtrations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11. A finite-dimensional graded right `T^λ`-module `N` has a *standard filtration*
when its restriction to the corner `e_λ V e_λ` is filtered by the loading standards of the
identity red order (`HasCornerStandardFiltration`). Such a module

* has a finite graded projective resolution (Corollary 5.22 and Lemma 5.26;
  `exists_resolution_of_hasCornerStandardFiltration`), and
* is braid-concentrated for `σ` once the braiding bimodule `B(σ, 1)` has a standard filtration as
  a right module (step `f_n → s_n`; `braidConcentrated_of_hasCornerStandardFiltration`).

Route hypothesis of the first item: `AllFiniteDeltaInjective` (as in Corollary 5.22).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv Categorification.Graded MulOpposite CategoryTheory CategoryTheory.Limits
open DG DG.DegreeZero ModuleFiltration

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe w

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q)
  {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q)

local notation "ord" => List.finRange ℓ
local notation "μ" => stendhalWeight ℓ ν
local notation "𝒞" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ord
local notation "𝒢" => rouquierGrading Q hR Λ
local notation "𝒜" Ω => oppositeGrade (tensorProductGrade (rouquierGrading Q hR Ω) ν)

variable (Λ ν) in
/-- **Standard filtrations of graded right `T^λ`-modules**: the restriction of `N` to the corner
`e_λ V e_λ` has a finite filtration by the loading standards of the identity red order. -/
def HasCornerStandardFiltration (N : GFin (𝒜 Λ)) : Prop :=
  ∃ m : List {s : Seq μ // redWord s = ord ∧ ¬ IsViolated s},
    HasFiltration
      (fun s => ModuleCat.of 𝒞ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val ord)) m
      (ModuleCat.of 𝒞ᵐᵒᵖ (CornerRes 𝒢 hρ hQ N))

/-- A right `T^λ`-module and its corner restriction, along `rightCornerEquiv`. -/
def cornerResSemilinearEquiv (N : GFin (𝒜 Λ)) :
    N.carrier ≃ₛₗ[(rightCornerEquiv (Λ := Λ) (ν := ν) hρ hQ :
      (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ →+* 𝒞ᵐᵒᵖ)] CornerRes 𝒢 hρ hQ N where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' t x := by
    change t • x = cornerOpRingHom hρ hQ (rightCornerHom hρ hQ t) • x
    congr 1
    exact congrArg op ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).apply_symm_apply
      t.unop).symm

include hρ hQ in
/-- **Standardly filtered modules have finite graded projective resolutions** (Webster,
arXiv:1309.3796v2, Corollary 5.22 with Lemma 5.26). Route hypothesis: `AllFiniteDeltaInjective`,
as for Corollary 5.22. -/
theorem exists_resolution_of_hasCornerStandardFiltration
    [Module.Finite k (TensorProductAlgebra k Q Λ ν)] (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    {N : GFin (𝒜 Λ)} (hN : HasCornerStandardFiltration Λ ν hρ hQ hR N) :
    ∃ Ps : List (GProj (𝒜 Λ)), Nonempty (GFin.Resolution N (Ps.map GProj.toGFin)) := by
  obtain ⟨m, hm⟩ := hN
  have hd : ∀ s : {s : Seq μ // redWord s = ord ∧ ¬ IsViolated s}, ∃ n : ℕ,
      HasProjectiveDimensionLT
        (ModuleCat.of 𝒞ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val ord)) n :=
    fun s => exists_hasProjectiveDimensionLT_loadingStandard (Λ := Λ) hρ hQ hR hall
      ((redWord_eq_finRange_iff _).1 s.2.1)
  choose d hd using hd
  let n := (m.map d).sum
  have hle : ∀ s ∈ m, d s ≤ n := fun s hs =>
    List.le_sum_of_mem (List.mem_map_of_mem hs)
  have hX := hm.hasProjectiveDimensionLT n fun s hs => by
    have := hd s
    exact hasProjectiveDimensionLT_of_ge _ (d s) n (hle s hs)
  have hT := hasProjectiveDimensionLT_of_semilinearEquiv _ (cornerResSemilinearEquiv hρ hQ hR N)
    n hX
  have := hT
  exact GFin.exists_resolution_of_hasProjectiveDimensionLT n N
    (hasProjectiveDimensionLT_of_ge (X := ModuleCat.of _ N.carrier) n (n + 1) (Nat.le_succ n))

variable (σ : Perm (Fin ℓ))

include hρ hQ in
/-- **Standardly filtered modules are braid-concentrated** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.11, step `f_n → s_n`): if the braiding bimodule `B(σ, 1)` has a filtration by the right
standards of the identity red order, every graded right `T^λ`-module with a standard filtration
is braid-concentrated for `σ`. Route hypothesis: `AllFiniteDeltaInjective` (Corollary 5.21). -/
theorem braidConcentrated_of_hasCornerStandardFiltration
    [∀ κ : List (Fin ℓ), HasDerivedCategory.{w, 0}
      (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)]
    [HasDerivedCategory.{w, 0} ℤ]
    [∀ κ : List (Fin ℓ), HasDerivedCategory.{w, 0}
      (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ]
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    {m : List {s : Seq μ // redWord s = ord ∧ ¬ IsViolated s}}
    (hf : HasFiltration
      (fun s => ModuleCat.of 𝒞ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val ord)) m
      (ModuleCat.of 𝒞ᵐᵒᵖ (braidingBimodule k Q Λ ν ((List.finRange ℓ).map σ) ord)))
    {N : GFin (𝒜 Λ)} (hN : HasCornerStandardFiltration Λ ν hρ hQ hR N) :
    BraidConcentrated.{w} Λ ν hρ hQ σ hR N := by
  obtain ⟨m', hX⟩ := hN
  let D := orderedStandardCovers Q (Λ ∘ ⇑(1 : Perm (Fin ℓ)))
    (fun s => exists_hasFiltration_leftUpper Q hQ hR hall (Λ ∘ ⇑(1 : Perm (Fin ℓ))) ν s.1 s.2)
  have key : ∀ κ : List (Fin ℓ), (List.finRange ℓ).map ⇑(1 : Perm (Fin ℓ)) = κ →
      ∀ {m : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}}
        {m' : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}}
        {X : ModuleCat.{0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ},
      HasFiltration (fun s => ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ)) m
        (ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ
          (braidingBimodule k Q Λ ν ((List.finRange ℓ).map σ) κ)) →
      HasFiltration (fun s => ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ)) m' X →
      ∀ n : ℤ, n ≠ 0 → IsZero ((DG.DerivedCategory.homologyFunctor
        (A := (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ((List.finRange ℓ).map σ))ᵐᵒᵖ)
          ℤ n).obj ((braidingFunctor.{w} k Q Λ ν κ ((List.finRange ℓ).map σ)).obj
            (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor
              (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ).obj X)))) := by
    rintro _ rfl m m' X hf hX n hn
    exact isZero_braidingFunctor_homology_of_standardFiltration hρ hQ 1 D hf hX n hn
  exact fun n hn => key ord (by simp) hf hX n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
