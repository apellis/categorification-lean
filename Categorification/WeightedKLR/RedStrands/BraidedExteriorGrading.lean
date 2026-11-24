/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardization

/-!
# The exterior standardization in the graded Figure 5 braid cut

Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 and Figure 5. The comparison uses the
intrinsic gradings on the diagram cut (Definitions 4.4 and 6.2) and on the balanced-tensor
standardization (Definition 5.4). This is a calculation on module pieces, not a graded
derived tensor construction.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv QuantumGroup Categorification.Graded DirectSum

private theorem homogeneous_preimage {k R M N : Type*} [CommRing k] [Semiring R]
    [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N] [Module R M] [Module R N]
    {𝒨 : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N} [Decomposition 𝒨] [Decomposition 𝒩]
    {f : M →ₗ[R] N} (hf : Function.Surjective f) (hgr : PreservesGrading 𝒨 𝒩 f)
    {n : ℤ} {y : N} (hy : y ∈ 𝒩 n) : ∃ x ∈ 𝒨 n, f x = y := by
  obtain ⟨x, rfl⟩ := hf y
  refine ⟨decompose 𝒨 x n, (decompose 𝒨 x n).2, ?_⟩
  rw [← decompose_map hgr, decompose_of_mem_same _ hy]

variable {I k : Type} [DecidableEq I] [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 2 → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight 2 ν))) → List ℕ}
  (C : CartanDatum I) (hR : IsRouquierQ C Q) (hρ : TypeA.IsReducedChoice ρ)

private abbrev stendhalGradeDatum (Ω : Fin 2 → I →₀ ℕ) : GradingDatum (stendhalQ Q Ω) :=
  stendhalGradingDatum Ω hR.gradingDatum (UDot.di C)
    (fun i => (hR.gradingDatum_degX i).trans (UDot.two_mul_di C i).symm)

omit [DecidableEq I] in
private theorem rouquierSymm {D : CartanDatum I} (h : IsRouquierQ D Q) : KLRSymm Q :=
  fun i j hij => (h.symm i j hij).symm

local notation "G" Ω:arg => stendhalGradeDatum C hR Ω
local notation "hS" => rouquierSymm hR
local notation "σ₁" => Equiv.swap (0 : Fin 2) 1
local notation "Right" κ:arg => (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ

private def vacuumBlack : Seq (0 : Multiset I) := KLRAlgebra.Seq.ofList [] (by simp)

local notation "vacuum" => SingleRed.insertWord 0 (vacuumBlack (I := I))
local notation "Upper" u:arg => ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (figureFiveUpper u) [1, 0]
local notation "Cut" u:arg => violCorner k Q Λ ν (figureFiveLower u) [1, 0]

private abbrev upperExterior (u : Seq ν) : ModuleCat.{0} (Right [1, 0]) :=
  exteriorStandardizationRight (Λ₂ := Λ) (σ₂ := σ₁) hS hρ (zero_add ν) vacuum u

local notation "UpperExt" u:arg => upperExterior (Λ := Λ) C hR hρ u

private instance upperExteriorModule (u : Seq ν) : Module k (UpperExt u) :=
  inferInstanceAs (Module k (StdLayer.carrier Q (Λ ∘ σ₁)
    (tensorLayer Q (Λ ∘ σ₁) (zero_add ν)
      (oldProj Q (Λ ∘ σ₁) 0 vacuum (SingleRed.ordered 0 vacuum)) (cycProj Q (Λ ∘ σ₁) ν u))))

private def upperEndpoint (u : Seq ν) : Upper u ≃ₗ[Right [1, 0]] UpperExt u :=
  loadingStandardEquivExteriorStandardization (Λ₂ := Λ) (σ₂ := σ₁) hS hρ (zero_add ν) vacuum u

/-- The degree indices of the exterior standardization at the upper Figure 5 loading are
integers, included in Webster's complex index group (arXiv:1309.3796v2, Definitions 5.4 and 6.2).
The pieces at other indices are zero, before shifting. -/
def figureFiveUpperExteriorGrade (u : Seq ν) : ℂ → Submodule k (UpperExt u) :=
  let E : ℤ → Submodule k (UpperExt u) :=
    exteriorStandardGrade (Λ ∘ σ₁) hR (G (Λ ∘ σ₁)) hS vacuum u (zero_add ν)
  Function.extend (fun n : ℤ => (n : ℂ)) E ⊥

private theorem upperEndpoint_mem_grade_iff (u : Seq ν) (z : ℂ) (x : Upper u) :
    (upperEndpoint (Λ := Λ) C hR hρ u).toEquiv x ∈
        figureFiveUpperExteriorGrade (Λ := Λ) C hR hρ u z ↔
      x ∈ violLoadingGrade (Λ := Λ) C hR (figureFiveUpper u) [1, 0] z := by
  classical
  let t := figureFiveUpper u
  let M := violCorner k Q Λ ν t [1, 0]
  let p : M →ₗ[Right [1, 0]] Upper u := (violStandardUpper (Λ := Λ) t [1, 0]).mkQ
  let e : Upper u ≃ₗ[Right [1, 0]] UpperExt u := upperEndpoint C hR hρ u
  let A : ℤ → Submodule k M := violCornerAuxiliaryGrade (Λ := Λ) C hR t [1, 0]
  let E : ℤ → Submodule k (UpperExt u) :=
    exteriorStandardGrade (Λ ∘ σ₁) hR (G (Λ ∘ σ₁)) hS vacuum u (zero_add ν)
  have hg : PreservesGrading A E (e.toLinearMap.comp p) := by
    intro n y hy
    exact loadingStandardEquivExteriorStandardization_mk_mem_grade hR hS σ₁ hρ
      (zero_add ν) vacuum u y hy
  change e.toEquiv x ∈ Function.extend (fun n : ℤ => (n : ℂ)) E ⊥ z ↔
    x ∈ violLoadingGrade (Λ := Λ) C hR t [1, 0] z
  by_cases hz : ∃ n : ℤ, (n : ℂ) = z
  · obtain ⟨n, rfl⟩ := hz
    rw [(Int.cast_injective (α := ℂ)).extend_apply, violLoadingGrade,
      (Int.cast_injective (α := ℂ)).extend_apply]
    change e.toEquiv x ∈ E n ↔ ∃ y ∈ A n, p y = x
    constructor
    · intro hx
      let : Decomposition E := exteriorStandardDecomposition (Λ ∘ σ₁) hR (G (Λ ∘ σ₁)) hS
        vacuum u (zero_add ν)
      have hf : Function.Surjective (e.toLinearMap.comp p) :=
        e.surjective.comp (Submodule.mkQ_surjective _)
      obtain ⟨y, hy, h⟩ := homogeneous_preimage hf hg hx
      exact ⟨y, hy, e.injective h⟩
    · rintro ⟨y, hy, rfl⟩
      exact hg hy
  · rw [Function.extend_apply' _ _ _ hz, violLoadingGrade, Function.extend_apply' _ _ _ hz]
    change e.toEquiv x ∈ (⊥ : Submodule k (UpperExt u)) ↔ x ∈ (⊥ : Submodule k (Upper u))
    simp only [Submodule.mem_bot]
    exact ⟨fun h => e.injective (h.trans e.map_zero.symm), fun h => h ▸ e.map_zero⟩

section Shifted

variable [Fintype I] {H : Type*} [AddCommGroup H] [Module ℂ H]
  (P : Matrix.Realization (UDot.A C) ℂ H)
  (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) (η : Fin 2 → Module.Dual ℂ H)
  (hB : ∀ i x, B (P.root i) x = (UDot.di C i : ℂ) * x (P.coroot i))
  (hΛ : ∀ j i, η j (P.coroot i) = (Λ j i : ℂ)) (hSym : B.IsSymm)

private abbrev pairingShift (ν : Multiset I) : ℂ := B (η 0 - (ν.map P.root).sum) (η 1)

local notation "a" => pairingShift C P B η ν
local notation "loadingBraid" u:arg =>
  figureFiveGradedLoadingEquiv_word (Λ := Λ) C hR P B η hB hΛ hSym hρ u

/-- The right-module map in Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9, Figure 5:
read the exterior standard as the upper loading quotient, then apply the Figure 5 braid map. -/
def figureFiveExteriorToCut (u : Seq ν) : UpperExt u ≃ₗ[Right [1, 0]] Cut u :=
  (upperEndpoint C hR hρ u).symm.trans (loadingBraid u).toLinearEquiv

/-- Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9, Figure 5, on the two-red module pieces.
Under the actual right-module comparison, the cut's degree `z` piece is the exterior
standardization's degree `z + ⟨λ₀ - α, λ₁⟩` piece in Webster's convention. The assertion is
for every complex index: outside the shifted integral coset both pieces are zero. -/
theorem figureFiveExteriorToCut_mem_grade_iff (u : Seq ν) (z : ℂ) (x : UpperExt u) :
    (figureFiveExteriorToCut C hR hρ P B η hB hΛ hSym u).toEquiv x ∈
        figureFiveCutGrade (Λ := Λ) C hR B η (figureFiveLower u) 1 0 z ↔
      x ∈ figureFiveUpperExteriorGrade (Λ := Λ) C hR hρ u (z + a) := by
  let e : Upper u ≃ₗ[Right [1, 0]] UpperExt u := upperEndpoint C hR hρ u
  let y : Upper u := e.symm x
  let b := loadingBraid u
  have he : (upperEndpoint (Λ := Λ) C hR hρ u).toEquiv y = x := e.apply_symm_apply x
  have hb : b.toLinearEquiv y ∈ figureFiveCutGrade (Λ := Λ) C hR B η (figureFiveLower u) 1 0 z ↔
      y ∈ violLoadingGrade (Λ := Λ) C hR (figureFiveUpper u) [1, 0] (z + a) := by
    rw [← sub_neg_eq_add]
    constructor
    · intro hy
      have h := b.symm_map_mem' hy
      rw [LinearEquiv.symm_apply_apply] at h
      exact h
    · intro hy
      exact b.map_mem' (d := z) hy
  change b.toLinearEquiv y ∈ _ ↔ x ∈ _
  rw [hb, ← upperEndpoint_mem_grade_iff C hR hρ u (z + a) y, he]

end Shifted

section LowerProjective

omit [DecidableEq I] in
private theorem lowerRedWord (u : Seq ν) : redWord (figureFiveLower u) = [0, 1] := by
  unfold figureFiveLower
  rw [Seq.redPerm_one]
  exact (redWord_eq_finRange_iff _).2 (isRedOrdered_seqCast _
    (isRedOrdered_twoPieceLoading (SingleRed.ordered ν _) vacuumBlack))

local notation "LowerCut" u:arg => violCorner k Q Λ ν (figureFiveLower u) [0, 1]
local notation "lowerIdem" u:arg => violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (lowerRedWord u)
local notation "Lower" u:arg => rIdeal (lowerIdem u)
local notation "hp₀" => isIdempotentElem_violMk_redProj k Q Λ ν [0, 1]

-- Both the same-order cut and the right ideal consist of the very same ambient diagrams.
-- Use the cut to take components, with its existing decomposition as a submodule over k.
private def lowerCutToProjective (u : Seq ν) : LowerCut u →ₗ[Right [0, 1]] Lower u where
  toFun y := by
    have hy := mem_violCorner_iff.1 y.2
    have hf : (lowerIdem u).val * y.val = y.val := hy.1
    refine ⟨⟨y.val, (Subsemigroup.mem_corner_iff hp₀).2 ⟨?_, hy.2⟩⟩, Subtype.ext hf⟩
    rw [← hf, ← mul_assoc, CornerEndomorphism.corner_mul_left hp₀ (lowerIdem u)]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem lowerCutToProjective_surjective (u : Seq ν) :
    Function.Surjective (lowerCutToProjective (Λ := Λ) (Q := Q) u) := by
  intro x
  let y : LowerCut u := ⟨x.val.val, mem_violCorner_iff.2
    ⟨congrArg Subtype.val x.2, CornerEndomorphism.corner_mul_right hp₀ x.val⟩⟩
  exact ⟨y, Subtype.ext (Subtype.ext rfl)⟩

private abbrev lowerExterior (u : Seq ν) : ModuleCat.{0} (Right [0, 1]) :=
  exteriorStandardizationRight (Λ₂ := Λ) (σ₂ := 1) hS hρ
    (add_zero ν) (SingleRed.insertWord ν u) vacuumBlack

local notation "LowerExt" u:arg => lowerExterior (Λ := Λ) C hR hρ u

local instance lowerExteriorModule (u : Seq ν) : Module k (LowerExt u) :=
  inferInstanceAs (Module k (StdLayer.carrier Q (Λ ∘ (1 : Perm (Fin 2)))
    (tensorLayer Q _ (add_zero ν)
      (oldProj Q _ ν (SingleRed.insertWord ν u) (SingleRed.ordered ν _)) (cycProj Q _ 0 vacuumBlack))))

private def lowerEndpoint (u : Seq ν) : Lower u ≃ₗ[Right [0, 1]] LowerExt u :=
  loadingProjectiveEquivExteriorStandardization (Λ₂ := Λ) (σ₂ := 1) hS hρ
    (add_zero ν) (SingleRed.insertWord ν u) vacuumBlack

/-- At the lower endpoint in Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 and Figure 5,
with last-factor vacuum, the loading projective's ambient diagram pieces are exactly the
intrinsic exterior standardization pieces under the existing comparison. There is no shift. -/
theorem figureFiveLowerProjective_mem_grade_iff (u : Seq ν) (n : ℤ) (x : Lower u) :
    (lowerEndpoint C hR hρ u).toEquiv x ∈
      exteriorStandardGrade (Λ ∘ (1 : Perm (Fin 2))) hR (G (Λ ∘ (1 : Perm (Fin 2)))) hS
        (SingleRed.insertWord ν u) vacuumBlack (add_zero ν) n ↔
      x.val.val ∈ violAuxiliaryGrade (G Λ) n := by
  let e : Lower u ≃ₗ[Right [0, 1]] LowerExt u := lowerEndpoint C hR hρ u
  let p : LowerCut u →ₗ[Right [0, 1]] Lower u := lowerCutToProjective u
  let A : ℤ → Submodule k (LowerCut u) :=
    violCornerAuxiliaryGrade (Λ := Λ) C hR (figureFiveLower u) [0, 1]
  let Ω := Λ ∘ (1 : Perm (Fin 2))
  let E : ℤ → Submodule k (LowerExt u) := exteriorStandardGrade Ω hR (G Ω) hS
    (SingleRed.insertWord ν u) vacuumBlack (add_zero ν)
  have hg : PreservesGrading A E (e.toLinearMap.comp p) := fun _ y hy =>
    loadingProjectiveEquivExteriorStandardization_mem_grade hR hS 1 hρ
      (add_zero ν) (SingleRed.insertWord ν u) vacuumBlack (p y) hy
  constructor
  · intro hx
    let : Decomposition E := exteriorStandardDecomposition Ω hR (G Ω) hS
      (SingleRed.insertWord ν u) vacuumBlack (add_zero ν)
    have hs : Function.Surjective (e.toLinearMap.comp p) :=
      e.surjective.comp (lowerCutToProjective_surjective u)
    obtain ⟨y, hy, h⟩ := homogeneous_preimage hs hg hx
    have hxy : p y = x := e.injective h
    rw [← hxy]
    exact hy
  · exact loadingProjectiveEquivExteriorStandardization_mem_grade hR hS 1 hρ
      (add_zero ν) (SingleRed.insertWord ν u) vacuumBlack x

end LowerProjective

end Categorification.Stendhal.BraidedStendhalAlgebra
