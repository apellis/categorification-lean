/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerBimoduleEnd
import Categorification.WeightedKLR.RedStrands.BraidHomBijective
import Categorification.WeightedKLR.RedStrands.LoadingGenerators

set_option backward.isDefEq.respectTransparency false

/-!
# The Ringel dual of `T^λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Corollary 6.19. The Ringel dual of a standardly stratified category is the category of modules
over the endomorphism ring of a tilting generator. For a red order `κ = w(1, …, ℓ)` reversing
every pair of red strands, the cuts `e(t) V e_κ` at red-ordered loadings `t` are tilting over
the corner `e_κ V e_κ` (Theorem 6.14, `halfTwist_hasFiltration`), every indecomposable tilting
module is a summand of one of them (`exists_leftInverse_violCorner_of_tilting`), and their sum
is the braiding bimodule `B(1, κ) = e_{(1,…,ℓ)} V e_κ`. Its endomorphism ring as a right module is
the corner at `(1, …, ℓ)`, acting by left multiplication
(`bijective_toModuleEnd_braidingBimodule_halfTwist`, `ringelDualEquiv`): the Ringel dual of the
category at the order `κ` is the category at the order `(1, …, ℓ)`.

## Main definitions and results

* `loadingMulHom`: left multiplication by an element of `e(t') C e(t)`, as a morphism of loading
  projectives.
* `bijective_toModuleEnd_braidingBimodule_halfTwist`, `ringelDualEquiv`: Corollary 6.19.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite DG
open scoped DG.DegreeZero

attribute [local instance] cornerBimodule.instModuleLeft cornerBimodule.instModuleRight

section Cut

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)

variable {t t' : Seq (stendhalWeight ℓ ν)} (ht : redWord t = List.finRange ℓ)
  (ht' : redWord t' = List.finRange ℓ)

/-- Left multiplication by an element `x` of `e(t') C`, as a morphism of loading projectives
`e(t) C → e(t') C` of the corner `C` at the order `(1, …, ℓ)`. -/
def loadingMulHom (x : C (List.finRange ℓ))
    (hx : violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht' * x = x) :
    rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht) →ₗ[(C (List.finRange ℓ))ᵐᵒᵖ]
      rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht') where
  toFun p := ⟨x * p.1, by rw [mem_rIdeal, ← mul_assoc, hx]⟩
  map_add' p p' := Subtype.ext (mul_add _ _ _)
  map_smul' a p := Subtype.ext (by
    change x * (p.1 * a.unop) = x * p.1 * a.unop
    rw [mul_assoc])

theorem genVal_loadingMulHom (x : C (List.finRange ℓ))
    (hx : violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht' * x = x)
    (hx' : x * violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht = x) :
    genVal ht ht' (loadingMulHom ht ht' x hx) = x.1 := by
  change (x * violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht).1 = x.1
  rw [hx']


attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation:max "E" s:arg => violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s))
local notation "hE" => isIdempotentElem_violMk_redProj k Q Λ ν

variable (κ : List (Fin ℓ))

/-- Injectivity of the braid on morphisms of loading projectives, read on the blocks of the
corner bimodule: an element of `e(t') C e(t)` killing the cut `e(t) V e_κ` vanishes. -/
theorem eq_zero_of_mul_cornerBimodule_of_injective_cutMul
    (h : Function.Injective (cutMul (k := k) (Q := Q) (Λ := Λ) ht ht' κ))
    (x : ViolQuotient k Q Λ ν) (hx : x ∈ cornerBimodule (E t') (E t))
    (hy : ∀ y ∈ cornerBimodule (E t) (violMk k Q Λ ν (redProj k Q Λ ν κ)), x * y = 0) :
    x = 0 := by
  have hP := (Subsemigroup.mem_corner_iff (hE (List.finRange ℓ))).1
    (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht').2
  have hP' := (Subsemigroup.mem_corner_iff (hE (List.finRange ℓ))).1
    (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht).2
  have hP1 : _ * E t' = E t' := hP.1
  have hP2 : E t * _ = E t := hP'.2
  let xc : C (List.finRange ℓ) :=
    ⟨x, (Subsemigroup.mem_corner_iff (hE (List.finRange ℓ))).2
      ⟨by rw [← hx.1, ← mul_assoc, hP1], by rw [← hx.2, mul_assoc, hP2]⟩⟩
  have hxl : violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht' * xc = xc := Subtype.ext hx.1
  have hxr : xc * violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht = xc := Subtype.ext hx.2
  have hg : cutMul (k := k) (Q := Q) (Λ := Λ) ht ht' κ (loadingMulHom ht ht' xc hxl) =
      cutMul ht ht' κ 0 := by
    rw [map_zero]
    refine LinearMap.ext fun y => Subtype.ext ?_
    rw [cutMul_apply_val, genVal_loadingMulHom ht ht' xc hxl hxr]
    exact hy y.1 (mem_violCorner_iff.1 y.2)
  have h0 := congrArg (genVal ht ht') (h hg)
  rw [genVal_loadingMulHom ht ht' xc hxl hxr] at h0
  exact h0

/-- The cut `e(t) V e_κ`, as the block `e(t) V e_κ` of the corner bimodule. -/
def violCornerToCornerBimodule (t : Seq (stendhalWeight ℓ ν)) :
    violCorner k Q Λ ν t κ → cornerBimodule (E t) (violMk k Q Λ ν (redProj k Q Λ ν κ)) :=
  fun y => ⟨y.1, mem_violCorner_iff.1 y.2⟩

/-- Surjectivity of the braid on morphisms of loading projectives, read on the blocks of the
corner bimodule: every right-linear map `e(t) V e_κ → e(t') V e_κ` is left multiplication by an
element of `e(t') C e(t)`. -/
theorem exists_mul_cornerBimodule_of_surjective_cutMul
    (h : Function.Surjective (cutMul (k := k) (Q := Q) (Λ := Λ) ht ht' κ))
    (φ : cornerBimodule (E t) (violMk k Q Λ ν (redProj k Q Λ ν κ)) →ₗ[(hE κ).Cornerᵐᵒᵖ]
      cornerBimodule (E t') (violMk k Q Λ ν (redProj k Q Λ ν κ))) :
    ∃ x ∈ cornerBimodule (E t') (E t), ∀ y, (φ y).1 = x * y.1 := by
  let φ' : violCorner k Q Λ ν t κ →ₗ[(C κ)ᵐᵒᵖ] violCorner k Q Λ ν t' κ :=
    { toFun := fun y => ⟨(φ (violCornerToCornerBimodule κ t y)).1,
        mem_violCorner_iff.2 (φ (violCornerToCornerBimodule κ t y)).2⟩
      map_add' := fun y y' => Subtype.ext (by
        change (φ (violCornerToCornerBimodule κ t (y + y'))).1 =
          (φ (violCornerToCornerBimodule κ t y)).1 + (φ (violCornerToCornerBimodule κ t y')).1
        exact congrArg Subtype.val (map_add φ (violCornerToCornerBimodule κ t y)
          (violCornerToCornerBimodule κ t y')))
      map_smul' := fun a y => Subtype.ext (by
        change (φ (violCornerToCornerBimodule κ t (a • y))).1 =
          (φ (violCornerToCornerBimodule κ t y)).1 * a.unop.1
        exact congrArg Subtype.val (map_smul φ a (violCornerToCornerBimodule κ t y))) }
  obtain ⟨g, hg⟩ := h φ'
  refine ⟨genVal ht ht' g, ⟨violLoadingIdem_mul_genVal ht ht' g,
    genVal_mul_violLoadingIdem ht ht' g⟩, fun y => ?_⟩
  exact (congrArg (fun F => (F ⟨y.1, mem_violCorner_iff.2 y.2⟩).1) hg).symm

omit ht ht' in
/-- **Endomorphisms of `B(1, κ)` from the braid on loading projectives**: if the braid
`g ↦ g ⊗ B(1, κ)` is bijective on morphisms between loading projectives of the order
`(1, …, ℓ)`, then the corner at `(1, …, ℓ)` acts on `B(1, κ)` by all of its right-linear
endomorphisms, faithfully. -/
theorem bijective_toModuleEnd_braidingBimodule_of_bijective_cutMul
    (h : ∀ {t t' : Seq (stendhalWeight ℓ ν)} (ht : redWord t = List.finRange ℓ)
      (ht' : redWord t' = List.finRange ℓ),
      Function.Bijective (cutMul (k := k) (Q := Q) (Λ := Λ) ht ht' κ)) :
    Function.Bijective (Module.toModuleEnd (hE κ).Cornerᵐᵒᵖ (S := (hE (List.finRange ℓ)).Corner)
      (braidingBimodule k Q Λ ν (List.finRange ℓ) κ)) := by
  refine bijective_toModuleEnd_cornerBimodule (hE (List.finRange ℓ)) (hE κ)
    (fun t : {t : Seq (stendhalWeight ℓ ν) // redWord t = List.finRange ℓ} => E t.1)
    (fun t => congrArg Subtype.val (isIdempotentElem_violLoadingIdem (k := k) (Q := Q)
      (Λ := Λ) t.2).eq)
    (fun t t' hne => by
      have h : t.1 ≠ t'.1 := fun h => hne (Subtype.ext h)
      rw [← map_mul, ← map_mul, KLRAlgebra.e_mul_e]
      simp only [h, ↓reduceIte, map_zero]) ?_
    (fun t t' => eq_zero_of_mul_cornerBimodule_of_injective_cutMul t.2 t'.2 κ (h t.2 t'.2).1)
    (fun t t' => exists_mul_cornerBimodule_of_surjective_cutMul t.2 t'.2 κ (h t.2 t'.2).2)
  let v : C (List.finRange ℓ) →+ ViolQuotient k Q Λ ν :=
    { toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h := congrArg v (sum_violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (ν := ν)
    (List.finRange ℓ))
  rw [map_sum] at h
  exact h

end Cut

section KhovanovLauda

open QuantumGroup KL3.Diagram
open scoped Classical

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
local notation "hE" => isIdempotentElem_violMk_redProj k QL Λ ν
local notation "fin" => List.finRange (ℓ + 1)
local notation "κw" => List.map w (List.finRange (ℓ + 1))
local notation:max "E" s:arg => violMk k QL Λ ν (ofKLR k QL Λ ν (KLRAlgebra.e s))

include hR H hwt hw in
/-- **The Ringel dual of `T^λ`** (Webster, arXiv:1309.3796v3, Corollary 6.19), at the
Khovanov–Lauda scalars: for a red order `κ = w(1, …, ℓ)` reversing every pair of red strands, the
left action of the corner at `(1, …, ℓ)` on the braiding bimodule `B(1, κ) = e_{(1,…,ℓ)} V e_κ`
is a bijection onto the endomorphisms of `B(1, κ)` as a right module over the corner at `κ`.
`B(1, κ)` is the sum of the cuts `e(t) V e_κ`, which are tilting (`halfTwist_hasFiltration`) and
have every indecomposable tilting module as a summand
(`exists_leftInverse_violCorner_of_tilting`), so it is a tilting generator. Route hypothesis:
the injectivity of Lemma 6.8 (`RowFigureFiveHypotheses`). -/
theorem bijective_toModuleEnd_braidingBimodule_halfTwist
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t') :
    Function.Bijective (Module.toModuleEnd (hE κw).Cornerᵐᵒᵖ (S := (hE fin).Corner)
      (braidingBimodule k QL Λ ν fin κw)) :=
  bijective_toModuleEnd_braidingBimodule_of_bijective_cutMul _ fun ht ht' =>
    bijective_cutMul_halfTwist C hQ Λ ν w hR H wt hwt hw hκ ht ht'

include hR H hwt hw in
/-- **The Ringel dual of `T^λ`** (Webster, arXiv:1309.3796v3, Corollary 6.19), as a ring
isomorphism: the corner at `(1, …, ℓ)` is the endomorphism ring of the tilting generator
`B(1, κ)` over the corner at the red order `κ = w(1, …, ℓ)` reversing every pair of red strands.
Route hypothesis: the injectivity of Lemma 6.8 (`RowFigureFiveHypotheses`). -/
def ringelDualEquiv
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t') :
    (hE fin).Corner ≃+*
      Module.End (hE κw).Cornerᵐᵒᵖ (braidingBimodule k QL Λ ν fin κw) :=
  RingEquiv.ofBijective _
    (bijective_toModuleEnd_braidingBimodule_halfTwist C hQ Λ ν w hR H wt hwt hw hκ)

theorem ringelDualEquiv_apply_val
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
    (c : (hE fin).Corner) (y : braidingBimodule k QL Λ ν fin κw) :
    (ringelDualEquiv C hQ Λ ν w hR H wt hwt hw hκ c y).1 = c.1 * y.1 := rfl

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
