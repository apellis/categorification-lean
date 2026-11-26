/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardModule
import Categorification.WeightedKLR.RedStrands.BraidingFunctor
import Categorification.Algebra.ModuleFiltrationIdempotents

/-!
# Filtrations of braiding bimodules from their loading pieces

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11. As a right module over the corner at `κ₂`, the braiding bimodule
`B(κ₁, κ₂) = e_{κ₁} V e_{κ₂}` is the direct sum of the cuts `e(t) V e_{κ₂}` over the loadings `t`
of red word `κ₁`, since `e_{κ₁} = Σ_t e(t)` is a sum of orthogonal idempotents. So `B(κ₁, κ₂)`
has a finite filtration by a family of modules once every cut has one
(`exists_hasFiltration_braidingBimodule`).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR ModuleFiltration

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
local notation "ι" => ofKLR k Q Λ ν
local notation "q" => violMk k Q Λ ν
local notation:max "E" j:arg => ι (KLRAlgebra.e j)
local notation:max "P" κ:arg => redProj k Q Λ ν κ
set_option quotPrecheck false in
local notation "B" κ':arg κ:arg => ↥(braidingBimodule k Q Λ ν κ' κ)

variable (κ₁ κ₂ : List (Fin ℓ))

theorem redProj_mul_e_mul_redProj {t : Seq μ} (ht : redWord t = κ₁) :
    P κ₁ * E t * P κ₁ = E t := by
  rw [redProj, ← map_mul, ← map_mul, redIdem_mul_e]
  simp only [ht, ↓reduceIte]
  rw [e_mul_redIdem]
  simp only [ht, ↓reduceIte]

/-- Left multiplication by `e_{κ₁} e(t) e_{κ₁}` on `B(κ₁, κ₂)`, a map of right modules over the
corner at `κ₂`. -/
def loadingMul (t : Seq μ) : Module.End (C κ₂)ᵐᵒᵖ (B κ₁ κ₂) where
  toFun x := ⟨q (P κ₁ * E t * P κ₁) * x.1, by
    rw [← mul_assoc, ← map_mul, ← mul_assoc, ← mul_assoc,
      (isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₁).eq], by
    rw [mul_assoc, x.2.2]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (mul_assoc _ _ _).symm

theorem loadingMul_val (t : Seq μ) (x : B κ₁ κ₂) :
    (loadingMul (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₁ κ₂ t x).1 = q (P κ₁ * E t * P κ₁) * x.1 := rfl

/-- The image of `loadingMul t` is the cut `e(t) V e_{κ₂}`. -/
def rangeLoadingMulEquiv {t : Seq μ} (ht : redWord t = κ₁) :
    LinearMap.range (loadingMul (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₁ κ₂ t) ≃ₗ[(C κ₂)ᵐᵒᵖ] violCorner k Q Λ ν t κ₂ where
  toFun y := ⟨y.1.1, by
    obtain ⟨_, x, rfl⟩ := y
    refine (mem_violCorner_iff (s := t) (κ := κ₂)).2 ⟨?_, ?_⟩
    · rw [loadingMul_val, redProj_mul_e_mul_redProj κ₁ ht, ← mul_assoc, ← map_mul, ← map_mul,
        KLRAlgebra.e_mul_e]
      simp only [↓reduceIte]
    · rw [loadingMul_val, mul_assoc, x.2.2]⟩
  invFun z := ⟨⟨z.1, by
      have hz := (mem_violCorner_iff (s := t) (κ := κ₂)).1 z.2
      rw [← hz.1, ← mul_assoc, ← map_mul, ← redProj_mul_e_mul_redProj κ₁ ht, ← mul_assoc,
        ← mul_assoc, (isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₁).eq], by
      have hz := (mem_violCorner_iff (s := t) (κ := κ₂)).1 z.2
      exact hz.2⟩, ⟨⟨z.1, by
      have hz := (mem_violCorner_iff (s := t) (κ := κ₂)).1 z.2
      rw [← hz.1, ← mul_assoc, ← map_mul, ← redProj_mul_e_mul_redProj κ₁ ht, ← mul_assoc,
        ← mul_assoc, (isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₁).eq], by
      have hz := (mem_violCorner_iff (s := t) (κ := κ₂)).1 z.2
      exact hz.2⟩, by
      apply Subtype.ext
      have hz := (mem_violCorner_iff (s := t) (κ := κ₂)).1 z.2
      change q (P κ₁ * E t * P κ₁) * z.1 = z.1
      rw [redProj_mul_e_mul_redProj κ₁ ht]
      exact hz.1⟩⟩
  left_inv y := rfl
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Filtrations of the braiding bimodule from its cuts** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.11): if every cut `e(t) V e_{κ₂}` with `redWord t = κ₁` has a finite filtration by `L`,
so does `B(κ₁, κ₂)`, as a right module over the corner at `κ₂`. -/
theorem exists_hasFiltration_braidingBimodule {ι' : Type*} {L : ι' → ModuleCat (C κ₂)ᵐᵒᵖ}
    (h : ∀ t : Seq μ, redWord t = κ₁ →
      ∃ m : List ι', HasFiltration L m (ModuleCat.of (C κ₂)ᵐᵒᵖ (violCorner k Q Λ ν t κ₂))) :
    ∃ m : List ι', HasFiltration L m (ModuleCat.of (C κ₂)ᵐᵒᵖ (B κ₁ κ₂)) := by
  classical
  let s := Finset.univ.filter fun t : Seq μ => redWord t = κ₁
  have hs : ∀ t ∈ s, redWord t = κ₁ := fun t ht => (Finset.mem_filter.mp ht).2
  refine exists_hasFiltration_of_orthogonal (M := ModuleCat.of (C κ₂)ᵐᵒᵖ (B κ₁ κ₂))
    (loadingMul κ₁ κ₂) s ?_ ?_ ?_ fun t ht => ?_
  · intro t ht
    refine LinearMap.ext fun x => Subtype.ext ?_
    change q (P κ₁ * E t * P κ₁) * (q (P κ₁ * E t * P κ₁) * x.1) = q (P κ₁ * E t * P κ₁) * x.1
    rw [redProj_mul_e_mul_redProj κ₁ (hs t ht), ← mul_assoc, ← map_mul, ← map_mul,
      KLRAlgebra.e_mul_e]
    simp only [↓reduceIte]
  · intro t ht u hu htu
    refine LinearMap.ext fun x => Subtype.ext ?_
    change q (P κ₁ * E t * P κ₁) * (q (P κ₁ * E u * P κ₁) * x.1) = 0
    rw [redProj_mul_e_mul_redProj κ₁ (hs t ht), redProj_mul_e_mul_redProj κ₁ (hs u hu),
      ← mul_assoc, ← map_mul, ← map_mul, KLRAlgebra.e_mul_e]
    simp only [htu, ↓reduceIte, map_zero, zero_mul]
  · refine LinearMap.ext fun x => Subtype.ext ?_
    rw [LinearMap.sum_apply, AddSubgroup.val_finsetSum]
    change ∑ t ∈ s, q (P κ₁ * E t * P κ₁) * x.1 = x.1
    rw [← Finset.sum_mul, Finset.sum_congr rfl fun t ht => by
      rw [redProj_mul_e_mul_redProj κ₁ (hs t ht)], ← map_sum, ← map_sum]
    change q (ι (redIdem k Q Λ κ₁)) * x.1 = x.1
    exact x.2.1
  · obtain ⟨m, hm⟩ := h t (hs t ht)
    exact ⟨m, hm.of_equiv (rangeLoadingMulEquiv κ₁ κ₂ (hs t ht)).symm⟩

end Categorification.Stendhal.BraidedStendhalAlgebra
