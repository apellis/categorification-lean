/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistDualityGeneral
import Categorification.WeightedKLR.RedStrands.BraidRightSequenceCut
import Categorification.WeightedKLR.RedStrands.BraidLengthInduction
import Categorification.WeightedKLR.RedStrands.BraidedBimoduleFlip

set_option backward.isDefEq.respectTransparency false

/-!
# `𝔅_τ P^κ` and its dual have standard filtrations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 6.14
(first clause). A right module `M` over the corner `e_κ V e_κ` has the dual `M⋆ = Hom_k(M, k)`,
made a right module through the flip of diagrams: `(φ c)(m) = φ(m ċ)` (`FlipDual`). For a
red-ordered loading `t` and a red order `κ = w(1, …, ℓ)` reversing every pair of red strands,
the cut `𝔅_τ P^κ = e(t) V e_κ` has a filtration by the loading standards of red order `κ`
(Lemma 6.12, `p_n → f_n`), and it is isomorphic to its dual as a right module (the pairing of
the proof of Theorem 6.14), so the dual has the same filtration (`halfTwist_hasFiltration`).
Standards are the standardizations of projectives, so both conditions of Webster's definition of
a tilting module hold.

## Main definitions and results

* `FlipDual`: the dual of a cut, a right module through the flip.
* `flipDualEquiv`: a contravariant form identifies the cut with its flip dual, right-linearly.
* `halfTwist_hasFiltration`: the cut and its flip dual both have standard filtrations.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite CornerEndomorphism ModuleFiltration

section FlipDual

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
local notation "μ" => stendhalWeight ℓ ν

/-- Right multiplication by an element of the corner, as a `k`-linear map of a cut. -/
def cutRightMul (t : Seq μ) (κ : List (Fin ℓ)) (c : (C κ)ᵐᵒᵖ) :
    violCorner k Q Λ ν t κ →ₗ[k] violCorner k Q Λ ν t κ where
  toFun m := c • m
  map_add' := smul_add c
  map_smul' r m := Subtype.ext (by
    change (r • m.1) * c.unop.val = r • (m.1 * c.unop.val)
    exact smul_mul_assoc r m.1 c.unop.val)

theorem cutRightMul_apply_val (t : Seq μ) (κ : List (Fin ℓ)) (c : (C κ)ᵐᵒᵖ)
    (m : violCorner k Q Λ ν t κ) : (cutRightMul t κ c m).1 = m.1 * c.unop.val := rfl

variable (k Q Λ) in
/-- **The flip dual of a cut**: `Hom_k(e(t) V e_κ, k)`, a right module over `e_κ V e_κ` by
`(φ c)(m) = φ(m ċ)`, with `ċ` the flip of `c`. -/
def FlipDual (t : Seq μ) (κ : List (Fin ℓ)) : Type :=
  Module.Dual k (violCorner k Q Λ ν t κ)

instance (t : Seq μ) (κ : List (Fin ℓ)) : AddCommGroup (FlipDual k Q Λ t κ) :=
  inferInstanceAs (AddCommGroup (Module.Dual k (violCorner k Q Λ ν t κ)))

/-- A functional on the cut, read as an element of `Module.Dual`. -/
def FlipDual.toDual {t : Seq μ} {κ : List (Fin ℓ)} (φ : FlipDual k Q Λ t κ) :
    Module.Dual k (violCorner k Q Λ ν t κ) := φ

/-- The flip of the corner, as a corner element of the opposite side. -/
def flipOp {κ : List (Fin ℓ)} (c : (C κ)ᵐᵒᵖ) : (C κ)ᵐᵒᵖ := op (cornerFlip c.unop)

theorem flipOp_one (κ : List (Fin ℓ)) : flipOp (1 : (C κ)ᵐᵒᵖ) = 1 := by
  change op (cornerFlip (1 : C κ)) = op 1
  congr 1
  exact Subtype.ext (violFlip_idem (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)

theorem flipOp_mul {κ : List (Fin ℓ)} (a b : (C κ)ᵐᵒᵖ) :
    flipOp (a * b) = flipOp b * flipOp a := by
  change op (cornerFlip (b.unop * a.unop)) = op (cornerFlip a.unop * cornerFlip b.unop)
  congr 1
  exact Subtype.ext (violFlip_mul' _ _)

instance (t : Seq μ) (κ : List (Fin ℓ)) : Module (C κ)ᵐᵒᵖ (FlipDual k Q Λ t κ) where
  smul c φ := LinearMap.comp (FlipDual.toDual φ)
    (cutRightMul t κ (flipOp c))
  one_smul φ := LinearMap.ext fun m => by
    change (FlipDual.toDual φ) (flipOp (1 : (C κ)ᵐᵒᵖ) • m) = FlipDual.toDual φ m
    rw [flipOp_one, one_smul]
  mul_smul a b φ := LinearMap.ext fun m => by
    change (FlipDual.toDual φ) (flipOp (a * b) • m) =
      (FlipDual.toDual φ) (flipOp b • flipOp a • m)
    rw [flipOp_mul, mul_smul]
  smul_zero c := LinearMap.ext fun m => rfl
  smul_add c φ ψ := LinearMap.ext fun m => rfl
  add_smul a b φ := LinearMap.ext fun m => by
    change (FlipDual.toDual φ) (flipOp (a + b) • m) =
      (FlipDual.toDual φ) (flipOp a • m) +
        (FlipDual.toDual φ) (flipOp b • m)
    rw [← map_add, ← add_smul]
    congr 2
    change op (cornerFlip (a.unop + b.unop)) = op (cornerFlip a.unop + cornerFlip b.unop)
    congr 1
    exact Subtype.ext (violFlip_add' _ _)
  zero_smul φ := LinearMap.ext fun m => by
    change (FlipDual.toDual φ) (flipOp (0 : (C κ)ᵐᵒᵖ) • m) =
      (0 : Module.Dual k (violCorner k Q Λ ν t κ)) m
    have : flipOp (0 : (C κ)ᵐᵒᵖ) = 0 := by
      change op (cornerFlip (0 : C κ)) = op 0
      congr 1
      exact Subtype.ext (violFlip_zero' (k := k) (Q := Q) (Λ := Λ) (ν := ν))
    have h0 : (0 : (C κ)ᵐᵒᵖ) • m = 0 := Subtype.ext (by
      change m.1 * (0 : C κ).1 = 0
      exact mul_zero _)
    rw [this, h0, map_zero, LinearMap.zero_apply]

theorem flipDual_smul_apply {t : Seq μ} {κ : List (Fin ℓ)} (c : (C κ)ᵐᵒᵖ)
    (φ : FlipDual k Q Λ t κ) (m : violCorner k Q Λ ν t κ) :
    (FlipDual.toDual (c • φ)) m =
      (FlipDual.toDual φ) (flipOp c • m) := rfl

/-- **A contravariant form identifies a cut with its flip dual**: if
`Φ : e(t) V e_κ ≃ Hom_k(e(t) V e_κ, k)` satisfies `Φ(m c)(m') = Φ(m)(m' ċ)` for every `c` in the
corner, then `Φ` is an isomorphism of right modules onto the flip dual. -/
def flipDualEquiv {t : Seq μ} {κ : List (Fin ℓ)}
    (Φ : violCorner k Q Λ ν t κ ≃ₗ[k] Module.Dual k (violCorner k Q Λ ν t κ))
    (hΦ : CornerSelfDual.IsContravariant
      (fun c : ViolQuotient k Q Λ ν =>
        violMk k Q Λ ν (redProj k Q Λ ν κ) * c * violMk k Q Λ ν (redProj k Q Λ ν κ) = c)
      violFlip Φ.toLinearMap) :
    violCorner k Q Λ ν t κ ≃ₗ[(C κ)ᵐᵒᵖ] FlipDual k Q Λ t κ where
  toFun := Φ
  invFun := Φ.symm
  left_inv := Φ.left_inv
  right_inv := Φ.right_inv
  map_add' := Φ.map_add
  map_smul' c m := LinearMap.ext fun m' => by
    have hS : violMk k Q Λ ν (redProj k Q Λ ν κ) * c.unop.val *
        violMk k Q Λ ν (redProj k Q Λ ν κ) = c.unop.val := by
      rw [corner_mul_left _ c.unop, corner_mul_right _ c.unop]
    exact hΦ m m' c.unop.val hS (c • m).2 (flipOp c • m').2

end FlipDual

section KhovanovLauda

open QuantumGroup KL3.Diagram
open scoped Classical DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} {k : Type} [Field k] (C : CartanDatum I)
  (hQ : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {ℓ : ℕ}
  (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (w : Perm (Fin (ℓ + 1)))
  {Y : Type*} [AddCommGroup Y] [Finite I]
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I),
    Module.Finite k (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Ω ν)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} ℤ]
  (H : ∀ (n m : ℕ), n + 2 + m = ℓ + 1 → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
    (u : Fin (n + 2 + m) → List I) (hu : u (FirstWeight.rightPos n m) = []),
    FirstWeight.RowFigureFiveHypotheses C hQ Ω u hu)
  (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
  (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (hw : w ≠ 1)

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "κ" => List.map w (List.finRange (ℓ + 1))
local notation "𝒞" => ViolOrderCorner (k := k) (Q := QL) (Λ := Λ) (ν := ν) κ
set_option quotPrecheck false in
local notation "𝕃" => fun s : {s : Seq (stendhalWeight (ℓ + 1) ν) // redWord s = κ ∧
  ¬ IsViolated s} => ModuleCat.of 𝒞ᵐᵒᵖ
    (ViolLoadingStandard (k := k) (Q := QL) (Λ := Λ) s.1 κ)

include hQ hR H hwt hw in
/-- **`𝔅_τ P^κ` and its dual have standard filtrations** (Webster, arXiv:1309.3796v3,
Theorem 6.14, first clause), at the Khovanov–Lauda scalars: for a red-ordered loading `t` and a
red order `κ = w(1, …, ℓ)` reversing every pair of red strands, the cut `e(t) V e_κ` and its flip
dual both have finite filtrations by the loading standards of red order `κ`. Standards are
standardizations of projectives, so `e(t) V e_κ` is tilting in Webster's sense. Route
hypothesis: the injectivity of Lemma 6.8 (`RowFigureFiveHypotheses`);
`AllFiniteDeltaInjective` and `BaseCrossing` are proved at these scalars. -/
theorem halfTwist_hasFiltration
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
    (t : Seq (stendhalWeight (ℓ + 1) ν)) (ht : IsRedOrdered t) :
    (∃ m, HasFiltration 𝕃 m (ModuleCat.of 𝒞ᵐᵒᵖ (violCorner k QL Λ ν t κ))) ∧
      ∃ m, HasFiltration 𝕃 m (ModuleCat.of 𝒞ᵐᵒᵖ (FlipDual k QL Λ t κ)) := by
  obtain ⟨m, hm⟩ := exists_hasFiltration_violCorner_of_braidFunctor
    (FirstWeight.isReducedChoice_canChoice ν) hQ.klrSymm hQ w t ht
    (FirstWeight.hasCornerStandardFiltration_braidF.{0} C hQ hR
      (fun _ _ => allFiniteDeltaInjective_of_rouquier hQ hQ.klrSymm) H w hw Λ wt hwt t ht)
  obtain ⟨Φ, hΦ⟩ := exists_halfTwistSelfDual C hQ Λ ν w hR H wt hwt hw hκ t ht
  exact ⟨⟨m, hm⟩, m, hm.of_equiv (Y' := ModuleCat.of 𝒞ᵐᵒᵖ (FlipDual k QL Λ t κ)) (flipDualEquiv Φ hΦ)⟩

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
