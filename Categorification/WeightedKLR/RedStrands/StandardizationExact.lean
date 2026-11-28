/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StandardizationHomFullyFaithful
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact

/-!
# The standardization of Definition 5.4 is exact

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.7: the standardization functor is exact. For blocks `b` with `b_0 = 0` and right
modules over the block algebra `B = R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_ℓ}(b_ℓ)` of Proposition 5.3, the
standardization `S(M) = M ⊗_B S_α` of Definition 5.4 sends injective maps to injective maps
(`standardizationMap_injective`), surjective maps to surjective maps
(`standardizationMap_surjective`), and sequences exact in the middle to sequences exact in the
middle (`standardizationMap_exact`).

The proof is by induction on the number of red strands, as for full faithfulness
(`StandardizationHomFullyFaithful.lean`). With no red strands `S(M) = M`, naturally in `M`. For
`ℓ + 1` red strands, `S(M)` is the two-piece standardization of `X_M = M ⊗_{B'} S^L_{α'}`,
naturally in `M` (`splitStandardEquiv_mapRight_hom`); `M ↦ X_M` preserves injections and exactness
by induction, and the two-piece standardization does (`parabolicStandardMap_injective`,
`parabolicStandardMap_exact`). The left-module form `M ⊗_B S^L_α` is identified with `S(M)`
naturally in `M` (`standardizationReflectEquiv_map`). The root function of `b` has no violated
sequence when `b_0 = 0`, so no hypothesis on it is needed in the headline statements.

## Main results

* `standardizationHom_injective`, `standardizationHom_exact`: the left-module form.
* `standardizationMap_injective`, `standardizationMap_surjective`, `standardizationMap_exact`:
  Proposition 5.7 for the standardization of Definition 5.4.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Conj

variable {A B C A' B' C' : Type*}

/-- Injectivity is invariant under conjugation by bijections. -/
theorem injective_iff_of_conj (f : A → B) (f' : A' → B') (e₁ : A ≃ A') (e₂ : B ≃ B')
    (hf : ∀ a, f' (e₁ a) = e₂ (f a)) : Function.Injective f ↔ Function.Injective f' := by
  constructor
  · intro h a₁ a₂ ha
    obtain ⟨a₁, rfl⟩ := e₁.surjective a₁
    obtain ⟨a₂, rfl⟩ := e₁.surjective a₂
    rw [hf, hf] at ha
    rw [h (e₂.injective ha)]
  · intro h a₁ a₂ ha
    exact e₁.injective (h (by rw [hf, hf, ha]))

/-- Exactness in the middle is invariant under conjugation by bijections preserving zero. -/
theorem exact_iff_of_conj [AddZeroClass C] [AddZeroClass C'] (f : A → B) (g : B → C)
    (f' : A' → B')
    (g' : B' → C') (e₁ : A ≃ A') (e₂ : B ≃ B') (e₃ : C ≃+ C')
    (hf : ∀ a, f' (e₁ a) = e₂ (f a)) (hg : ∀ b, g' (e₂ b) = e₃ (g b)) :
    Function.Exact f g ↔ Function.Exact f' g' := by
  have hr : ∀ y, y ∈ Set.range f ↔ e₂ y ∈ Set.range f' := fun y => by
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e₁ a, hf a⟩
    · rintro ⟨a', ha'⟩
      obtain ⟨a, rfl⟩ := e₁.surjective a'
      exact ⟨a, e₂.injective ((hf a).symm.trans ha')⟩
  have hz : ∀ y, g y = 0 ↔ g' (e₂ y) = 0 := fun y => by
    rw [hg, ← map_zero e₃, e₃.injective.eq_iff]
  constructor
  · intro h y'
    obtain ⟨y, rfl⟩ := e₂.surjective y'
    rw [← hz, ← hr]
    exact h y
  · intro h y
    rw [hz, hr]
    exact h (e₂ y)

end Conj

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- The statement that standardization with `n` red strands preserves injections. -/
def StandardizationPreservesInjective (n : ℕ) : Prop :=
  ∀ (Λ : Fin n → I →₀ ℕ) (b : Fin (n + 1) → Multiset I) (ν : Multiset I)
    (hb : blockPrefix b (n + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot b)), b 0 = 0 →
    ∀ (M M' : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
      [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
      [AddCommGroup M'] [Module k M'] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M']
      [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M']
      (g : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M'), Function.Injective g →
      Function.Injective (standardizationHom Q Λ hb hα M M' g)

/-- The statement that standardization with `n` red strands preserves exactness in the
middle. -/
def StandardizationPreservesExact (n : ℕ) : Prop :=
  ∀ (Λ : Fin n → I →₀ ℕ) (b : Fin (n + 1) → Multiset I) (ν : Multiset I)
    (hb : blockPrefix b (n + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot b)), b 0 = 0 →
    ∀ (M M' M'' : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
      [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
      [AddCommGroup M'] [Module k M'] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M']
      [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M']
      [AddCommGroup M''] [Module k M''] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M'']
      [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M'']
      (f : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M') (g : M' →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M''),
      Function.Exact f g →
      Function.Exact (standardizationHom Q Λ hb hα M M' f) (standardizationHom Q Λ hb hα M' M'' g)

/-- With no red strands, standardization preserves injections. -/
theorem standardizationPreservesInjective_zero : StandardizationPreservesInjective Q 0 := by
  intro Λ b ν hb hα hb0 M M' _ _ _ _ _ _ _ _ g hg
  obtain rfl : ν = 0 := hb.symm.trans (blockPrefix_one_eq_zero b hb0)
  exact (injective_iff_of_conj (standardizationHom Q Λ hb hα M M' g) g
    (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).toEquiv
    (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M').toEquiv
    fun y => (leftStandardizationZeroEquiv_mapRight_hom Q Λ b hb0 hb hα g y).symm).2 hg

/-- With no red strands, standardization preserves exactness. -/
theorem standardizationPreservesExact_zero : StandardizationPreservesExact Q 0 := by
  intro Λ b ν hb hα hb0 M M' M'' _ _ _ _ _ _ _ _ _ _ _ _ f g h
  obtain rfl : ν = 0 := hb.symm.trans (blockPrefix_one_eq_zero b hb0)
  exact (exact_iff_of_conj (standardizationHom Q Λ hb hα M M' f)
    (standardizationHom Q Λ hb hα M' M'' g) f g
    (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).toEquiv
    (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M').toEquiv
    (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M'').toAddEquiv
    (fun y => (leftStandardizationZeroEquiv_mapRight_hom Q Λ b hb0 hb hα f y).symm)
    (fun y => (leftStandardizationZeroEquiv_mapRight_hom Q Λ b hb0 hb hα g y).symm)).2 h

section Step

variable (hQ : KLRSymm Q) {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (b : Fin (ℓ + 2) → Multiset I)
  (hα' : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hα : RootNonViolated (ν := initWeight b + lastBlock b) (blockRoot b))
  (M M' M'' : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M']
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M']
  [AddCommGroup M''] [Module k M''] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M'']
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M'']

local notation "𝔹" => BlockAlgebra k Q Λ b
local notation "B'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "ofR" => initRestrictOf Q Λ b (M := M)
local notation "ofR'" => initRestrictOf Q Λ b (M := M')
local notation "ofR''" => initRestrictOf Q Λ b (M := M'')
local notation "ofX" => twoPieceInputOf Q Λ b M hα'
local notation "ofX'" => twoPieceInputOf Q Λ b M' hα'
local notation "ofX''" => twoPieceInputOf Q Λ b M'' hα'
local notation "sH'" => standardizationHom Q (Λ ∘ Fin.castSucc)
  (rfl : blockPrefix (initBlocks b) (ℓ + 1) = initWeight b) hα'

include hQ in
/-- **The induction step for injections.** -/
theorem standardizationHom_injective_step
    (ih : ∀ g : InitRestrict Q Λ b M →ₗ[B'ᵐᵒᵖ] InitRestrict Q Λ b M', Function.Injective g →
      Function.Injective (sH' (InitRestrict Q Λ b M) (InitRestrict Q Λ b M') g))
    (g : M →ₗ[𝔹ᵐᵒᵖ] M') (hg : Function.Injective g) :
    Function.Injective (standardizationHom Q Λ (blockPrefix_last b) hα M M' g) := by
  have h1 : Function.Injective (initRestrictHom Q Λ b g) :=
    (injective_iff_of_conj g _ (ofR).toEquiv (ofR').toEquiv
      fun m => initRestrictHom_of Q Λ b g m).1 hg
  have h2 : Function.Injective (twoPieceHom Q Λ b hα' g) :=
    (injective_iff_of_conj _ _ (ofX).toEquiv (ofX').toEquiv
      fun x => twoPieceHom_of Q Λ b hα' g x).1 (ih _ h1)
  have h3 : Function.Injective (parabolicStandardMapT Q Λ hQ (twoPieceHom Q Λ b hα' g)) :=
    parabolicStandardMap_injective Q Λ (initWeight b) (lastBlock b) hQ _ h2
  exact (injective_iff_of_conj _ _ (splitStandardEquiv Q Λ hQ b hα' hα M).toEquiv
    (splitStandardEquiv Q Λ hQ b hα' hα M').toEquiv
    fun y => (splitStandardEquiv_mapRight_hom Q hQ Λ b hα' hα g y).symm).2 h3

include hQ in
/-- **The induction step for exactness.** -/
theorem standardizationHom_exact_step
    (ih : ∀ (f : InitRestrict Q Λ b M →ₗ[B'ᵐᵒᵖ] InitRestrict Q Λ b M')
      (g : InitRestrict Q Λ b M' →ₗ[B'ᵐᵒᵖ] InitRestrict Q Λ b M''), Function.Exact f g →
      Function.Exact (sH' (InitRestrict Q Λ b M) (InitRestrict Q Λ b M') f)
        (sH' (InitRestrict Q Λ b M') (InitRestrict Q Λ b M'') g))
    (f : M →ₗ[𝔹ᵐᵒᵖ] M') (g : M' →ₗ[𝔹ᵐᵒᵖ] M'') (h : Function.Exact f g) :
    Function.Exact (standardizationHom Q Λ (blockPrefix_last b) hα M M' f)
      (standardizationHom Q Λ (blockPrefix_last b) hα M' M'' g) := by
  have h1 : Function.Exact (initRestrictHom Q Λ b f) (initRestrictHom Q Λ b g) :=
    (exact_iff_of_conj f g _ _ (ofR).toEquiv (ofR').toEquiv (ofR'').toAddEquiv
      (fun m => initRestrictHom_of Q Λ b f m) (fun m => initRestrictHom_of Q Λ b g m)).1 h
  have h2 : Function.Exact (twoPieceHom Q Λ b hα' f) (twoPieceHom Q Λ b hα' g) :=
    (exact_iff_of_conj _ _ _ _ (ofX).toEquiv (ofX').toEquiv (ofX'').toAddEquiv
      (fun x => twoPieceHom_of Q Λ b hα' f x) (fun x => twoPieceHom_of Q Λ b hα' g x)).1
      (ih _ _ h1)
  have h3 : Function.Exact (parabolicStandardMapT Q Λ hQ (twoPieceHom Q Λ b hα' f))
      (parabolicStandardMapT Q Λ hQ (twoPieceHom Q Λ b hα' g)) :=
    parabolicStandardMap_exact Q Λ (initWeight b) (lastBlock b) hQ _ _ h2
  exact (exact_iff_of_conj _ _ _ _ (splitStandardEquiv Q Λ hQ b hα' hα M).toEquiv
    (splitStandardEquiv Q Λ hQ b hα' hα M').toEquiv
    (splitStandardEquiv Q Λ hQ b hα' hα M'').toAddEquiv
    (fun y => (splitStandardEquiv_mapRight_hom Q hQ Λ b hα' hα f y).symm)
    (fun y => (splitStandardEquiv_mapRight_hom Q hQ Λ b hα' hα g y).symm)).2 h3

end Step

/-- The black weight and root function of the first `ℓ + 1` blocks, for `b_0 = 0`. -/
theorem initBlocks_zero_and_rootNonViolated {ℓ : ℕ} (b : Fin (ℓ + 2) → Multiset I) (hb0 : b 0 = 0) :
    initBlocks b 0 = 0 ∧ RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)) := by
  have hb0' : initBlocks b 0 = 0 := by
    change b (Fin.castSucc 0) = 0
    simpa using hb0
  refine ⟨hb0', ?_⟩
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · exact rootNonViolated_of_eq_zero (blockPrefix_one_eq_zero (initBlocks b) hb0') _
  · exact rootNonViolated_blockRoot hℓ hb0'

theorem standardizationPreservesInjective_succ (hQ : KLRSymm Q) {ℓ : ℕ}
    (ih : StandardizationPreservesInjective Q ℓ) :
    StandardizationPreservesInjective Q (ℓ + 1) := by
  intro Λ b ν hb hα hb0 M M' _ _ _ _ _ _ _ _ g hg
  obtain rfl : ν = initWeight b + lastBlock b := hb.symm.trans (blockPrefix_last b)
  obtain ⟨hb0', hα'⟩ := initBlocks_zero_and_rootNonViolated b hb0
  exact standardizationHom_injective_step Q hQ Λ b hα' hα M M'
    (fun g hg => ih (Λ ∘ Fin.castSucc) _ _ rfl hα' hb0' (InitRestrict Q Λ b M)
      (InitRestrict Q Λ b M') g hg) g hg

theorem standardizationPreservesExact_succ (hQ : KLRSymm Q) {ℓ : ℕ}
    (ih : StandardizationPreservesExact Q ℓ) :
    StandardizationPreservesExact Q (ℓ + 1) := by
  intro Λ b ν hb hα hb0 M M' M'' _ _ _ _ _ _ _ _ _ _ _ _ f g h
  obtain rfl : ν = initWeight b + lastBlock b := hb.symm.trans (blockPrefix_last b)
  obtain ⟨hb0', hα'⟩ := initBlocks_zero_and_rootNonViolated b hb0
  exact standardizationHom_exact_step Q hQ Λ b hα' hα M M' M''
    (fun f g h => ih (Λ ∘ Fin.castSucc) _ _ rfl hα' hb0' (InitRestrict Q Λ b M)
      (InitRestrict Q Λ b M') (InitRestrict Q Λ b M'') f g h) f g h

/-- **Standardization preserves injections** for every number of red strands. -/
theorem standardizationPreservesInjective (hQ : KLRSymm Q) :
    ∀ n, StandardizationPreservesInjective Q n
  | 0 => standardizationPreservesInjective_zero Q
  | n + 1 => standardizationPreservesInjective_succ Q hQ (standardizationPreservesInjective hQ n)

/-- **Standardization preserves exactness** for every number of red strands. -/
theorem standardizationPreservesExact (hQ : KLRSymm Q) :
    ∀ n, StandardizationPreservesExact Q n
  | 0 => standardizationPreservesExact_zero Q
  | n + 1 => standardizationPreservesExact_succ Q hQ (standardizationPreservesExact hQ n)

/-- The root function of blocks with `b_0 = 0` has no violated sequence. -/
theorem rootNonViolated_of_zero {n : ℕ} (b : Fin (n + 1) → Multiset I) (hb0 : b 0 = 0) :
    RootNonViolated (ν := blockPrefix b (n + 1)) (blockRoot b) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact rootNonViolated_of_eq_zero (blockPrefix_one_eq_zero b hb0) _
  · exact rootNonViolated_blockRoot hn hb0

section Headline

variable {n : ℕ} {Λ : Fin n → I →₀ ℕ} {b : Fin (n + 1) → Multiset I}
  {M M' M'' : Type} [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M']
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M']
  [AddCommGroup M''] [Module k M''] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M'']
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M'']

/-- The identification `S(M) ≅ M ⊗_B S^L_α` is natural in `M`. -/
theorem standardizationReflectEquiv_map
    (hα : RootNonViolated (ν := blockPrefix b (n + 1)) (blockRoot b))
    (g : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M') (z : Standardization Q Λ b M) :
    standardizationReflectEquiv Q Λ b hα M' (standardizationMap g z) =
      standardizationHom Q Λ rfl hα M M' g (standardizationReflectEquiv Q Λ b hα M z) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v m => rfl

/-- **Standardization preserves injections** (Webster, arXiv:1309.3796v3, Proposition 5.7, for
the standardization of Definition 5.4), for blocks with `b_0 = 0`. -/
theorem standardizationMap_injective (hQ : KLRSymm Q) (hb0 : b 0 = 0)
    (g : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M') (hg : Function.Injective g) :
    Function.Injective (standardizationMap g) :=
  (injective_iff_of_conj _ _
    (standardizationReflectEquiv Q Λ b (rootNonViolated_of_zero b hb0) M).toEquiv
    (standardizationReflectEquiv Q Λ b (rootNonViolated_of_zero b hb0) M').toEquiv
    fun z => (standardizationReflectEquiv_map Q _ g z).symm).2
    (standardizationPreservesInjective Q hQ n Λ b _ rfl _ hb0 M M' g hg)

/-- **Standardization preserves surjections** (Webster, arXiv:1309.3796v3, Proposition 5.7, for
the standardization of Definition 5.4). -/
theorem standardizationMap_surjective (g : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M')
    (hg : Function.Surjective g) : Function.Surjective (standardizationMap g) :=
  BalancedTensor.mapRight_surjective hg

/-- **Standardization is exact** (Webster, arXiv:1309.3796v3, Proposition 5.7, for the
standardization of Definition 5.4): for blocks with `b_0 = 0`, a sequence `M → M' → M''` of
right modules over the block algebra which is exact at `M'` gives a sequence
`S(M) → S(M') → S(M'')` exact at `S(M')`. -/
theorem standardizationMap_exact (hQ : KLRSymm Q) (hb0 : b 0 = 0)
    (f : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M') (g : M' →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M'')
    (h : Function.Exact f g) :
    Function.Exact (standardizationMap f) (standardizationMap g) :=
  (exact_iff_of_conj _ _ _ _
    (standardizationReflectEquiv Q Λ b (rootNonViolated_of_zero b hb0) M).toEquiv
    (standardizationReflectEquiv Q Λ b (rootNonViolated_of_zero b hb0) M').toEquiv
    (standardizationReflectEquiv Q Λ b (rootNonViolated_of_zero b hb0) M'').toAddEquiv
    (fun z => (standardizationReflectEquiv_map Q _ f z).symm)
    (fun z => (standardizationReflectEquiv_map Q _ g z).symm)).2
    (standardizationPreservesExact Q hQ n Λ b _ rfl _ hb0 M M' M'' f g h)

end Headline

end StendhalAlgebra

end Categorification.Stendhal
