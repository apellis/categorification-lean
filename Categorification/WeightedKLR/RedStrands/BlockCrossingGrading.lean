/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingRowStandard
import Categorification.WeightedKLR.RedStrands.BraidedStandardGrading
import Categorification.WeightedKLR.RedStrands.ParabolicInputGrading

/-!
# The grading shift at a Figure 5 row loading

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 (v3: Proposition
6.10), step 4. The identification of the cut quotient at the crossed Figure 5 row loading with
the standard module at the uncrossed one (`rowBraidCutEquivStandard`) is left multiplication by
the stacked generator. That generator is represented by the Figure 5 diagram of the distinguished
block juxtaposed with the spectator loading idempotents (`rowRep`), which is homogeneous.

The cuts `e(s) V e_κ` carry the auxiliary grading of the braided diagrams
(`violCornerGrade`), and so do their quotients (`braidCutGrade`, `loadingStandardGrade`). As in
`figureFiveCutGrade`, Webster's degree on the cut at the crossed loading replaces the
auxiliary degree `-2` of the single red/red crossing by `-⟨λ_{f 0}, λ_{f 1}⟩`
(`rowCutGrade`). Then the identification is homogeneous: the standard module shifted by
`-⟨λ_{f 1} - α, λ_{f 0}⟩` is isomorphic as a graded module to the cut quotient, where `α` is the
black content of the distinguished block (`rowGradedBraidCutEquivStandard`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Categorification.Stendhal.RedBlock
open KLR BraidedStendhalAlgebra MulOpposite Categorification.Graded DirectSum QuantumGroup
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section CornerGrading

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "μ" => stendhalWeight ℓ ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "Agrade" => violAuxiliaryGrade (ν := ν) G
local notation "Right" κ:arg => (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ

local instance violOrderCornerRing (κ : List (Fin ℓ)) :
    Ring (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ) := _root_.instRingCorner _ _

theorem violIdem_mem_violAuxiliaryGrade (j : Seq μ) :
    violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e j)) ∈ Agrade 0 :=
  Graded.mem_map_of_mem _ _ (Graded.mem_map_of_mem _ _ (G.e_mem_grade j))

theorem violRedProj_mem_violAuxiliaryGrade (κ : List (Fin ℓ)) :
    violMk k Q Λ ν (redProj k Q Λ ν κ) ∈ Agrade 0 := by
  rw [redProj, redIdem, map_sum, map_sum]
  exact Submodule.sum_mem _ fun j _ => violIdem_mem_violAuxiliaryGrade G j

/-- The auxiliary grading restricted to the cut `e(s) V e_κ`. -/
def violCornerGrade (s : Seq μ) (κ : List (Fin ℓ)) :
    ℤ → Submodule k (violCorner k Q Λ ν s κ) :=
  Graded.comap Agrade (violCorner k Q Λ ν s κ).subtype

instance violCornerGradeDecomposition (s : Seq μ) (κ : List (Fin ℓ)) :
    Decomposition (violCornerGrade G s κ) := by
  apply IsInternal.chooseDecomposition
  apply Graded.isInternal_comap _ _ Subtype.val_injective
  intro x n
  have h := mem_violCorner_iff.1 x.2
  refine ⟨⟨(decompose Agrade x.1 n : V), mem_violCorner_iff.2 ⟨?_, ?_⟩⟩, rfl⟩
  · rw [← coe_decompose_mul_of_left_mem_zero Agrade (violIdem_mem_violAuxiliaryGrade G s), h.1]
  · rw [← coe_decompose_mul_of_right_mem_zero Agrade (violRedProj_mem_violAuxiliaryGrade G κ),
      h.2]

theorem violCornerGrade_subtype (s : Seq μ) (κ : List (Fin ℓ)) :
    PreservesGrading (violCornerGrade G s κ) Agrade (violCorner k Q Λ ν s κ).subtype :=
  fun _ _ hx => hx

theorem decompose_violCornerGrade_val (s : Seq μ) (κ : List (Fin ℓ))
    (x : violCorner k Q Λ ν s κ) (n : ℤ) :
    ((decompose (violCornerGrade G s κ) x n : violCorner k Q Λ ν s κ) : V) =
      decompose Agrade x.1 n :=
  (Graded.decompose_map (violCornerGrade_subtype G s κ) x n).symm

private instance violCornerScalarTower (t : Seq μ) (κ : List (Fin ℓ)) :
    IsScalarTower k (Right κ) (violCorner k Q Λ ν t κ) where
  smul_assoc c a x := Subtype.ext <| by
    rw [violCorner_smul_val, Submodule.coe_smul_of_tower, violCorner_smul_val]
    change x.1 * (c • a.unop.val) = c • (x.1 * a.unop.val)
    rw [mul_smul_comm]

private instance violLoadingModule (t : Seq μ) (κ : List (Fin ℓ)) :
    Module k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ) :=
  Submodule.Quotient.module' (violStandardUpper t κ)

private instance braidCutModule (t : Seq μ) (a b : Fin ℓ) (κ : List (Fin ℓ)) :
    Module k (BraidCutQuotient Q Λ t a b κ) :=
  Submodule.Quotient.module' (braidCutUpper Q Λ t a b κ)

private instance braidCutScalarTower (t : Seq μ) (a b : Fin ℓ) (κ : List (Fin ℓ)) :
    IsScalarTower k (Right κ) (BraidCutQuotient Q Λ t a b κ) :=
  Submodule.Quotient.isScalarTower _ _

/-- The quotient map onto the cut quotient, as a map of `k`-modules. -/
def braidCutMkK (t : Seq μ) (a b : Fin ℓ) (κ : List (Fin ℓ)) :
    violCorner k Q Λ ν t κ →ₗ[k] BraidCutQuotient Q Λ t a b κ :=
  (braidCutMk Q Λ t a b κ).restrictScalars k

theorem braidCutMkK_apply (t : Seq μ) (a b : Fin ℓ) (κ : List (Fin ℓ))
    (x : violCorner k Q Λ ν t κ) : braidCutMkK t a b κ x = braidCutMk Q Λ t a b κ x := rfl

/-- The quotient map onto the standard module, as a map of `k`-modules. -/
def loadingMkK (t : Seq μ) (κ : List (Fin ℓ)) :
    violCorner k Q Λ ν t κ →ₗ[k] ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ :=
  (violStandardUpper t κ).mkQ.restrictScalars k

theorem loadingMkK_apply (t : Seq μ) (κ : List (Fin ℓ)) (x : violCorner k Q Λ ν t κ) :
    loadingMkK t κ x = (violStandardUpper t κ).mkQ x := rfl

/-- The auxiliary grading of the cut quotient `e(t) V e_κ / J` of step 2. -/
def braidCutGrade (t : Seq μ) (a b : Fin ℓ) (κ : List (Fin ℓ)) :
    ℤ → Submodule k (BraidCutQuotient Q Λ t a b κ) :=
  Graded.map (violCornerGrade G t κ) (braidCutMkK t a b κ)

instance braidCutGradeDecomposition (t : Seq μ) (a b : Fin ℓ) (κ : List (Fin ℓ)) :
    Decomposition (braidCutGrade G t a b κ) :=
  Graded.mapDecomposition (π := braidCutMkK t a b κ)
    (braidCutMk_surjective Q Λ t a b κ) fun x hx n => by
      have hx' : x.1 ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) κ :=
        (Submodule.Quotient.mk_eq_zero (braidCutUpper Q Λ t a b κ)).1 hx
      apply (Submodule.Quotient.mk_eq_zero (braidCutUpper Q Λ t a b κ)).2
      change ((decompose (violCornerGrade G t κ) x n : violCorner k Q Λ ν t κ) : V) ∈
        blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) κ
      rw [decompose_violCornerGrade_val]
      apply Graded.decompose_mem_twoSidedSpan Agrade _ hx' n
      rintro _ ⟨u, -, -, rfl⟩
      exact ⟨0, violIdem_mem_violAuxiliaryGrade G u⟩

theorem braidCutMk_preservesGrading (t : Seq μ) (a b : Fin ℓ) (κ : List (Fin ℓ)) :
    PreservesGrading (violCornerGrade G t κ) (braidCutGrade G t a b κ)
      (braidCutMkK t a b κ) :=
  fun _ _ hx => Submodule.mem_map_of_mem hx

/-- The auxiliary grading of the standard module at a loading. -/
def loadingStandardGrade (t : Seq μ) (κ : List (Fin ℓ)) :
    ℤ → Submodule k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ) :=
  Graded.map (violCornerGrade G t κ) (loadingMkK t κ)

/-- Left multiplication by an element `x` with `e(s) x = x`, from the cut at `t` to the cut at
`s`. -/
def leftMulCorner {s t : Seq μ} {κ : List (Fin ℓ)} (x : V)
    (hx : violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) * x = x) :
    violCorner k Q Λ ν t κ →ₗ[k] violCorner k Q Λ ν s κ where
  toFun y := ⟨x * y.1, mem_violCorner_iff.2
    ⟨by rw [← mul_assoc, hx], by rw [mul_assoc, (mem_violCorner_iff.1 y.2).2]⟩⟩
  map_add' y z := Subtype.ext (mul_add _ _ _)
  map_smul' c y := Subtype.ext (mul_smul_comm c x y.1)

theorem leftMulCorner_preservesGrading {s t : Seq μ} {κ : List (Fin ℓ)} {x : V} {D : ℤ}
    (hD : x ∈ Agrade D) (hx : violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) * x = x) :
    PreservesGrading (violCornerGrade G t κ) (Graded.shift (violCornerGrade G s κ) (-D))
      (leftMulCorner (κ := κ) (t := t) x hx) := by
  intro n y hy
  change x * y.1 ∈ Agrade (n - -D)
  rw [show n - -D = D + n by abel]
  exact SetLike.GradedMul.mul_mem hD hy

/-- If left multiplication by a homogeneous element induces an isomorphism from the standard
module at `t` onto the cut quotient at `s`, the grading of the standard module is internal. -/
theorem isInternal_violLoadingGrade {s t : Seq μ} {a b : Fin ℓ} {κ : List (Fin ℓ)} {x : V}
    {D : ℤ} (hD : x ∈ Agrade D)
    (hx : violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) * x = x)
    (Φ : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ ≃ₗ[Right κ]
      BraidCutQuotient Q Λ s a b κ)
    (hΦ : ∀ y, Φ ((violStandardUpper t κ).mkQ y) =
      braidCutMk Q Λ s a b κ (leftMulCorner x hx y)) :
    DirectSum.IsInternal (loadingStandardGrade G t κ) := by
  let ψ := braidCutMkK (a := a) (b := b) s κ ∘ₗ leftMulCorner (κ := κ) (t := t) x hx
  have hψ : PreservesGrading (violCornerGrade G t κ) (Graded.shift (braidCutGrade G s a b κ) (-D))
      ψ := fun n y hy =>
    braidCutMk_preservesGrading G s a b κ (leftMulCorner_preservesGrading G hD hx hy)
  let _ : Decomposition (loadingStandardGrade G t κ) :=
    Graded.mapDecomposition (π := loadingMkK t κ) (𝒳 := violCornerGrade G t κ)
      (Submodule.mkQ_surjective (violStandardUpper (k := k) (Q := Q) (Λ := Λ) t κ))
      fun y hy n => by
        rw [loadingMkK_apply]
        refine (map_eq_zero_iff Φ Φ.injective).1 ?_
        rw [hΦ]
        have h0 : ψ y = 0 := by
          change braidCutMk Q Λ s a b κ _ = 0
          rw [← hΦ, ← loadingMkK_apply, hy, map_zero]
        have hm := Graded.decompose_map hψ y n
        rw [h0, decompose_zero] at hm
        change ψ _ = 0
        rw [← hm]
        rfl
  exact Decomposition.isInternal _

end CornerGrading

section Representative

universe v
variable {k : Type v} [CommRing k]
variable {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
local notation "B₂" => (RedBlock.mk 2 f β : RedBlock I ℓ)
local notation "m₂" => Multiset.card (stendhalWeight 2 β)

/-- The row diagram with `a` in the distinguished block and the loading idempotents of `s` in
the spectator blocks. -/
def rowRep (a : diagramAlgebra Q Λ B₂) :
    (L : List (Fin ℓ × Multiset I)) → Loadings (adjacentRow L M f β) →
      diagrams Q Λ (adjacentRow L M f β)
  | [], s => a ⊗ₜ loadingIdem Q Λ (M.map spectator) s.2
  | x :: L, s => ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e s.1) ⊗ₜ rowRep a L s.2

theorem spectatorsGen_eq_cut : ∀ (M : List (Fin ℓ × Multiset I)) (w : Loadings (M.map spectator)),
    spectatorsGen Q Λ hQ M w =
      (spectatorCuts Q Λ hQ M).cut (projection Q Λ _ (loadingIdem Q Λ _ w))
  | [], _ => rfl
  | x :: xs, w => by
    have e1 : projection Q Λ (spectator x :: xs.map spectator)
        (ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e w.1) ⊗ₜ
          loadingIdem Q Λ _ w.2) =
        violMk k Q (Λ ∘ (spectator x).label) x.2
            (ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e w.1)) ⊗ₜ
          projection Q Λ _ (loadingIdem Q Λ _ w.2) :=
      Algebra.TensorProduct.map_tmul _ _ _ _
    change _ = (spectatorCuts Q Λ hQ (x :: xs)).cut
      (projection Q Λ (spectator x :: xs.map spectator) (_ ⊗ₜ _))
    rw [e1]
    change _ = TensorProduct.map (spectatorCut Q Λ hQ x).cut (spectatorCuts Q Λ hQ xs).cut (_ ⊗ₜ _)
    rw [TensorProduct.map_tmul, ← spectatorsGen_eq_cut xs w.2]
    rfl

/-- The row generator built from the cut of `z` is the cut of `rowRep z`. -/
theorem rowGen_eq_cut (z : diagramAlgebra Q Λ B₂) : ∀ (L : List (Fin ℓ × Multiset I))
    (s : Loadings (adjacentRow L M f β)),
    rowGen Q Λ hQ M f β ((pairCut Q Λ hQ f β).cut (violMk k Q (Λ ∘ f) β z)) L s =
      (crossingProduct Q Λ hQ M f β L).cut (projection Q Λ _ (rowRep Q Λ M f β z L s))
  | [], s => by
    have e1 : projection Q Λ (B₂ :: M.map spectator) (z ⊗ₜ loadingIdem Q Λ _ s.2) =
        violMk k Q (Λ ∘ f) β z ⊗ₜ projection Q Λ _ (loadingIdem Q Λ _ s.2) :=
      Algebra.TensorProduct.map_tmul _ _ _ _
    change _ = (crossingProduct Q Λ hQ M f β []).cut
      (projection Q Λ (B₂ :: M.map spectator) (_ ⊗ₜ _))
    rw [e1]
    change _ = TensorProduct.map (pairCut Q Λ hQ f β).cut (spectatorCuts Q Λ hQ M).cut (_ ⊗ₜ _)
    rw [TensorProduct.map_tmul, ← spectatorsGen_eq_cut Q Λ hQ M s.2]
    rfl
  | x :: L, s => by
    have e1 : projection Q Λ (spectator x :: adjacentRow L M f β)
        (ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e s.1) ⊗ₜ
          rowRep Q Λ M f β z L s.2) =
        violMk k Q (Λ ∘ (spectator x).label) x.2
            (ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e s.1)) ⊗ₜ
          projection Q Λ _ (rowRep Q Λ M f β z L s.2) :=
      Algebra.TensorProduct.map_tmul _ _ _ _
    change _ = (crossingProduct Q Λ hQ M f β (x :: L)).cut
      (projection Q Λ (spectator x :: adjacentRow L M f β) (_ ⊗ₜ _))
    rw [e1]
    change _ = TensorProduct.map (spectatorCut Q Λ hQ x).cut
      (crossingProduct Q Λ hQ M f β L).cut (_ ⊗ₜ _)
    rw [TensorProduct.map_tmul, ← rowGen_eq_cut z L s.2]
    rfl

theorem loadingIdem_mul_self : ∀ (Bs : List (RedBlock I ℓ)) (s : Loadings Bs),
    loadingIdem Q Λ Bs s * loadingIdem Q Λ Bs s = loadingIdem Q Λ Bs s
  | [], _ => mul_one _
  | B :: Bs, s => by
    change (_ ⊗ₜ _) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, KLRAlgebra.e_mul_self,
      loadingIdem_mul_self Bs s.2]

theorem loadingIdem_mul_rowRep {σ : Seq (B₂).localWeight} {a : diagramAlgebra Q Λ B₂}
    (ha : ofKLR k Q (Λ ∘ f) β (KLRAlgebra.e σ) * a = a) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β)),
      loadingIdem Q Λ _ (setPairLoading M f β σ L s) * rowRep Q Λ M f β a L s =
        rowRep Q Λ M f β a L s
  | [], s => by
    change (ofKLR k Q (Λ ∘ f) β (KLRAlgebra.e σ) ⊗ₜ loadingIdem Q Λ _ s.2) *
      (a ⊗ₜ loadingIdem Q Λ _ s.2) = a ⊗ₜ loadingIdem Q Λ _ s.2
    rw [Algebra.TensorProduct.tmul_mul_tmul, ha, loadingIdem_mul_self]
  | x :: L, s => by
    change (ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e s.1) ⊗ₜ
        loadingIdem Q Λ _ (setPairLoading M f β σ L s.2)) *
      (ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e s.1) ⊗ₜ rowRep Q Λ M f β a L s.2) =
      ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e s.1) ⊗ₜ rowRep Q Λ M f β a L s.2
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, KLRAlgebra.e_mul_self,
      loadingIdem_mul_rowRep ha L s.2]

theorem rowRep_mul_loadingIdem {σ : Seq (B₂).localWeight} {a : diagramAlgebra Q Λ B₂}
    (ha : a * ofKLR k Q (Λ ∘ f) β (KLRAlgebra.e σ) = a) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β)),
      rowRep Q Λ M f β a L s * loadingIdem Q Λ _ (setPairLoading M f β σ L s) =
        rowRep Q Λ M f β a L s
  | [], s => by
    change (a ⊗ₜ loadingIdem Q Λ _ s.2) *
      (ofKLR k Q (Λ ∘ f) β (KLRAlgebra.e σ) ⊗ₜ loadingIdem Q Λ _ s.2) =
      a ⊗ₜ loadingIdem Q Λ _ s.2
    rw [Algebra.TensorProduct.tmul_mul_tmul, ha, loadingIdem_mul_self]
  | x :: L, s => by
    change (ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e s.1) ⊗ₜ
        rowRep Q Λ M f β a L s.2) *
      (ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e s.1) ⊗ₜ
        loadingIdem Q Λ _ (setPairLoading M f β σ L s.2)) =
      ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e s.1) ⊗ₜ rowRep Q Λ M f β a L s.2
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, KLRAlgebra.e_mul_self,
      rowRep_mul_loadingIdem ha L s.2]

/-- The juxtaposition of `rowRep a` has the degree of `a`, the spectator idempotents having
degree zero. -/
theorem juxtapose_rowRep_mem_grade (G : KLR.GradingDatum (stendhalQ Q Λ))
    {a : diagramAlgebra Q Λ B₂} {d : ℤ} (ha : readBlock Q Λ B₂ a ∈ G.grade (B₂).weight d) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β)),
      juxtapose Q Λ _ (rowRep Q Λ M f β a L s) ∈ G.grade (weightSum (adjacentRow L M f β)) d
  | [], s => by
    change juxtapose Q Λ (B₂ :: M.map spectator) (_ ⊗ₜ _) ∈ _
    rw [juxtapose_tmul, juxtapose_loadingIdem]
    have hm := G.concat_tmul_mem_grade ha (G.e_mem_grade (place (M.map spectator) s.2))
    rw [add_zero] at hm
    exact hm
  | x :: L, s => by
    change juxtapose Q Λ (spectator x :: adjacentRow L M f β) (_ ⊗ₜ _) ∈ _
    rw [juxtapose_tmul, readBlock_idem]
    have hm := G.concat_tmul_mem_grade (G.e_mem_grade (Seq.map (spectator x).colour s.1))
      (juxtapose_rowRep_mem_grade G ha L s.2)
    rw [zero_add] at hm
    exact hm

end Representative

section Shift

universe v
variable {k : Type v} [CommRing k]
variable {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
    (C : CartanDatum I) (hR : IsRouquierQ C Q)
local notation "B₂" => (RedBlock.mk 2 f β : RedBlock I ℓ)
local notation "m₂" => Multiset.card (stendhalWeight 2 β)
local notation "G" => stendhalGradingDatum Λ hR.gradingDatum (UDot.di C) (cartanDotDegree C hR)
local notation "Δ" => Multiset.sum (Multiset.map (fun i => UDot.di C i * (Λ (f 0) i : ℤ)) β)

local instance shiftCornerRing {ν : Multiset I} (κ : List (Fin ℓ)) :
    Ring (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ) := _root_.instRingCorner _ _

include hR in
/-- Webster, arXiv:1309.3796v2, Figure 5, read in the row: the Figure 5 diagram of the
distinguished block has auxiliary degree `⟨α, λ_{f 0}⟩ - 2`. -/
theorem readBlock_figureFive_mem_grade {ρ : Equiv.Perm (Fin m₂) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)}
    (h0 : 0 < m₂) (ht₀ : t₂.lbl ⟨0, h0⟩ = .inr 0) (hb : EdgeBraid h0 0 g σ t₂) :
    readBlock Q Λ B₂ (ofKLR k Q (Λ ∘ f) β (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t₂)) ∈
      (G).grade (B₂).weight (Δ - 2) := by
  let H := redSubfamilyGrading Λ (⇑f) f.injective (G)
  have hdeg : H.degW (ρ g) t₂ = Δ - 2 :=
    hb.degW_eq H (fun i => UDot.di C i * (Λ (f 0) i : ℤ)) (fun x => by cases x <;> rfl) hρ h0 ht₀
  have hψ := GradingDatum.ψw_mul_pol_mul_e_mem_grade H (ρ g) t₂ (p := 1) (D := 0)
    (MvPolynomial.isWeightedHomogeneous_one k _)
  rw [map_one, mul_one, add_zero, hdeg] at hψ
  rw [readBlock, AlgHom.comp_apply, map_mul, map_mul, toKLR_ofKLR_ψw, toKLR_ofKLR_e]
  exact redSubfamilyRelabel_mem_grade Λ (⇑f) f.injective (G) β hψ



/-- The stacked Figure 5 diagram: `rowRep` of the Figure 5 diagram, juxtaposed in the violated
quotient. -/
def rowFigureFive {ρ : Equiv.Perm (Fin m₂) → List ℕ} (g : Equiv.Perm (Fin m₂))
    (t₂ : Seq (stendhalWeight 2 β)) (L : List (Fin ℓ × Multiset I)) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
    (u : Loadings (adjacentRow L M f β)) : ViolQuotient k Q Λ ν :=
  stackBlocks Q Λ L M f β h
    (rowRep Q Λ M f β (ofKLR k Q (Λ ∘ f) β (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t₂)) L u)

include hR in
theorem rowFigureFive_mem_grade {ρ : Equiv.Perm (Fin m₂) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)}
    (h0 : 0 < m₂) (ht₀ : t₂.lbl ⟨0, h0⟩ = .inr 0) (hb : EdgeBraid h0 0 g σ t₂)
    (L : List (Fin ℓ × Multiset I)) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
    (u : Loadings (adjacentRow L M f β)) :
    rowFigureFive Q Λ M f β (ρ := ρ) g t₂ L h u ∈ violAuxiliaryGrade (ν := ν) (G) (Δ - 2) :=
  Graded.mem_map_of_mem _ _ (Graded.mem_map_of_mem _ _ ((G).castKLR_mem_grade h
    (juxtapose_rowRep_mem_grade Q Λ M f β (G)
      (readBlock_figureFive_mem_grade Q Λ f β C hR hρ h0 ht₀ hb) L u)))

theorem loading_mul_rowFigureFive {ρ : Equiv.Perm (Fin m₂) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ) {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)}
    (h0 : 0 < m₂) (hb : EdgeBraid h0 0 g σ t₂)
    (L : List (Fin ℓ × Multiset I)) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
    (u : Loadings (adjacentRow L M f β)) :
    violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e (Seq.cast h (place _ (setPairLoading M f β σ L u))))) *
        rowFigureFive Q Λ M f β (ρ := ρ) g t₂ L h u =
      rowFigureFive Q Λ M f β (ρ := ρ) g t₂ L h u := by
  have hl := stackBlocks_loadingIdem Q Λ L M f β h (setPairLoading M f β σ L u)
  rw [AlgHom.comp_apply] at hl
  rw [rowFigureFive, ← hl, ← map_mul,
    loadingIdem_mul_rowRep Q Λ M f β (e_mul_psi_e hρ hb.smul_eq)]

/-- The identification of Proposition 6.9 at a Figure 5 row loading is left multiplication by
the stacked Figure 5 diagram. -/
theorem rowBraidCutEquivStandard_mk {ρ : Equiv.Perm (Fin m₂) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ)
    {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)} (h1 : 1 < m₂)
    (ht₀ : t₂.lbl ⟨0, by omega⟩ = .inr 0) (ht₁ : t₂.lbl ⟨1, h1⟩ = .inr 1)
    (hb : EdgeBraid (show 0 < m₂ by omega) 0 g σ t₂) (hσ : redWord σ = [1, 0])
    (ht₂ : redWord t₂ = [0, 1]) (L : List (Fin ℓ × Multiset I)) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν) (u : Loadings (adjacentRow L M f β))
    (hs : ¬ Violated _ (setPairLoading M f β σ L u))
    (ht : redWord (Seq.cast h (place _ (setPairLoading M f β σ L u))) = L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hstd : StackedStandard hQ h (rowRelations Q Λ hQ M f β
      (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e t₂)) (pairRelations Q Λ hQ f β t₂) L u)
      (setPairLoading M f β t₂ L u))
    (y : violCorner k Q Λ ν (Seq.cast h (place _ (setPairLoading M f β t₂ L u))) (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)) :
    rowBraidCutEquivStandard Q Λ hQ M f β hρ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd
        ((violStandardUpper (Seq.cast h (place _ (setPairLoading M f β t₂ L u))) (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)).mkQ y) =
      braidCutMk Q Λ (Seq.cast h (place _ (setPairLoading M f β σ L u))) (f 0) (f 1) (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)
        (leftMulCorner _ (loading_mul_rowFigureFive Q Λ M f β hρ _ hb L h u) y) := by
  have ht₂' : redWord t₂ = List.finRange 2 := ht₂.trans (by decide)
  rw [rowBraidCutEquivStandard, braidCutQuotientEquivStandard_mk]
  apply (Submodule.Quotient.eq _).2
  change (_ - _ : ViolQuotient k Q Λ ν) ∈ blockUpperIdeal k Q Λ ν (f 0) (f 1)
    (adjacentBlockRoot (f 0) (f 1) (Seq.cast h (place _ (setPairLoading M f β σ L u)))) (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)
  rw [adjacentBlockRoot_place hs ht, ← TwoSidedIdeal.ker_ringCon_mk' (blockUpperIdeal _ _ _ _ _ _ _ _),
    TwoSidedIdeal.mem_ker]
  change RingCon.mkₐ k _ _ = 0
  rw [map_sub, sub_eq_zero, generatorStack_val]
  let x := rowRep Q Λ M f β (ofKLR k Q (Λ ∘ f) β (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t₂)) L u
  have hsx := loadingIdem_mul_rowRep Q Λ M f β (σ := σ) (e_mul_psi_e hρ hb.smul_eq) L u
  have hxs : x * loadingIdem Q Λ _ (setPairLoading M f β t₂ L u) = x :=
    rowRep_mul_loadingIdem Q Λ M f β (by rw [← map_mul, mul_assoc, KLRAlgebra.e_mul_self]) L u
  have he : orderedInclusion Q Λ hQ (fun _ => Fin.revPerm) _ 1 *
      projection Q Λ _ (loadingIdem Q Λ _ (setPairLoading M f β σ L u)) =
      projection Q Λ _ (loadingIdem Q Λ _ (setPairLoading M f β σ L u)) :=
    orderedInclusion_top_one_mul Q Λ hQ M f β σ hσ L u
  have he' : projection Q Λ _ (loadingIdem Q Λ _ (setPairLoading M f β t₂ L u)) *
      orderedInclusion Q Λ hQ (fun _ => 1) _ 1 =
      projection Q Λ _ (loadingIdem Q Λ _ (setPairLoading M f β t₂ L u)) := by
    rw [← orderedInclusion_rowTau Q Λ hQ M f β t₂ ht₂' L u, ← map_mul, mul_one]
  have hx : projection Q Λ _ x = (crossingProduct Q Λ hQ M f β L).incl
      (rowGen Q Λ hQ M f β (pairGen Q Λ hQ f β ρ g t₂) L u) := by
    have hY : projection Q Λ _ x =
        projection Q Λ _ (loadingIdem Q Λ _ (setPairLoading M f β σ L u)) * projection Q Λ _ x *
          projection Q Λ _ (loadingIdem Q Λ _ (setPairLoading M f β t₂ L u)) := by
      rw [← map_mul, ← map_mul, hsx, hxs]
    rw [pairGen, rowGen_eq_cut, BlockCut.incl_cut, hY, ← mul_assoc (orderedInclusion _ _ _ _ _ 1),
      ← mul_assoc (orderedInclusion _ _ _ _ _ 1), he, mul_assoc _ _ (orderedInclusion _ _ _ _ _ 1),
      he']
  exact stackedGenerator_mul_eq hx hsx y


/-- **Proposition 6.9 at a Figure 5 row loading, in the auxiliary grading** (Webster,
arXiv:1309.3796v2, §6.1, proof, step 4). The identification `rowBraidCutEquivStandard` of the
standard module at the uncrossed loading with the cut quotient at the crossed loading is
homogeneous of auxiliary degree `⟨α, λ_{f 0}⟩ - 2`, where `α` is the black content of the
distinguished block. Hypotheses: those of `rowBraidCutEquivStandard`. -/
def rowAuxiliaryGradedEquiv {ρ : Equiv.Perm (Fin m₂) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ)
    {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)} (h1 : 1 < m₂)
    (ht₀ : t₂.lbl ⟨0, by omega⟩ = .inr 0) (ht₁ : t₂.lbl ⟨1, h1⟩ = .inr 1)
    (hb : EdgeBraid (show 0 < m₂ by omega) 0 g σ t₂) (hσ : redWord σ = [1, 0])
    (ht₂ : redWord t₂ = [0, 1]) (L : List (Fin ℓ × Multiset I)) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν) (u : Loadings (adjacentRow L M f β))
    (hs : ¬ Violated _ (setPairLoading M f β σ L u))
    (ht : redWord (Seq.cast h (place _ (setPairLoading M f β σ L u))) = L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hstd : StackedStandard hQ h (rowRelations Q Λ hQ M f β
      (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e t₂)) (pairRelations Q Λ hQ f β t₂) L u)
      (setPairLoading M f β t₂ L u)) :
    Graded.shift (loadingStandardGrade (G) (Seq.cast h (place _ (setPairLoading M f β t₂ L u))) (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)) (Δ - 2) ≃ᵍ[(ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst))ᵐᵒᵖ]
      braidCutGrade (G) (Seq.cast h (place _ (setPairLoading M f β σ L u))) (f 0) (f 1) (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst) :=
  letI := (isInternal_violLoadingGrade (G) (rowFigureFive_mem_grade Q Λ M f β C hR hρ _ ht₀ hb L h u)
      (loading_mul_rowFigureFive Q Λ M f β hρ _ hb L h u)
      (rowBraidCutEquivStandard Q Λ hQ M f β hρ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd)
      (rowBraidCutEquivStandard_mk Q Λ hQ M f β hρ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd)
      ).chooseDecomposition
  GradedEquiv.ofPreserves (rowBraidCutEquivStandard Q Λ hQ M f β hρ h1 ht₀ ht₁ hb hσ ht₂ L h u hs
      ht hstd) fun n x hx => by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    change rowBraidCutEquivStandard Q Λ hQ M f β hρ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd
      ((violStandardUpper _ _).mkQ y) ∈ _
    rw [rowBraidCutEquivStandard_mk]
    have hm := braidCutMk_preservesGrading (G) (Seq.cast h (place _ (setPairLoading M f β σ L u))) (f 0) (f 1) (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)
      (leftMulCorner_preservesGrading (G) (rowFigureFive_mem_grade Q Λ M f β C hR hρ _ ht₀ hb L h u)
        (loading_mul_rowFigureFive Q Λ M f β hρ _ hb L h u) hy)
    rwa [show n - (Δ - 2) - -(Δ - 2) = n by abel] at hm


/-- Webster's grading of the cut quotient at the crossed loading (Definitions 4.4 and 6.2): the
single red/red crossing counts `-⟨λ_{f 0}, λ_{f 1}⟩` instead of its auxiliary degree `-2`. The
complex numbers are degree indices. -/
def rowCutGrade {H : Type*} [AddCommGroup H] [Module ℂ H]
    (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) (η : Fin ℓ → Module.Dual ℂ H)
    (L : List (Fin ℓ × Multiset I)) {ν : Multiset I} (t : Seq (stendhalWeight ℓ ν)) :
    ℂ → Submodule k (BraidCutQuotient Q Λ t (f 0) (f 1) (L.map Prod.fst ++ f 0 :: f 1 ::
      M.map Prod.fst)) :=
  Function.extend (fun n : ℤ => (n : ℂ) + (2 - B (η (f 0)) (η (f 1))))
    (braidCutGrade (G) t (f 0) (f 1) _) ⊥

/-- The grading of a standard module at the uncrossed order, with complex degree indices. There
is no red/red crossing, so Webster's degree is the auxiliary degree. -/
def rowLoadingGrade (L : List (Fin ℓ × Multiset I)) {ν : Multiset I}
    (t : Seq (stendhalWeight ℓ ν)) :
    ℂ → Submodule k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t
      (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)) :=
  Function.extend (fun n : ℤ => (n : ℂ)) (loadingStandardGrade (G) t _) ⊥

omit [DecidableEq I] in
private theorem blackContent_pairing {H : Type*} [AddCommGroup H] [Module ℂ H] [Fintype I]
    (P : Matrix.Realization (UDot.A C) ℂ H) (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H))
    (η : Fin ℓ → Module.Dual ℂ H)
    (hB : ∀ i x, B (P.root i) x = (UDot.di C i : ℂ) * x (P.coroot i))
    (hΛ : ∀ j i, η j (P.coroot i) = (Λ j i : ℂ)) (j : Fin ℓ) (β : Multiset I) :
    B (β.map P.root).sum (η j) =
      ((Multiset.sum (Multiset.map (fun i => UDot.di C i * (Λ j i : ℤ)) β) : ℤ) : ℂ) := by
  induction β using Multiset.induction_on with
  | empty => simp
  | cons i β ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, map_add, LinearMap.add_apply,
      hB, hΛ, ih, Int.cast_add, Int.cast_mul, Int.cast_natCast]

/-- **Proposition 6.9 at a Figure 5 row loading, graded** (Webster, arXiv:1309.3796v2, §6.1,
proof, step 4). With Webster's degrees, the identification `rowBraidCutEquivStandard` of the
standard module at the uncrossed row loading with the cut quotient at the crossed row loading
is homogeneous: the standard module shifted by `-⟨λ_{f 1} - α, λ_{f 0}⟩` is isomorphic to the
cut quotient as a graded module, where `α` is the black content of the distinguished block.
In Webster's notation `M(a)_n = M_(n+a)` this is the shift `⟨λ_{f 1} - α, λ_{f 0}⟩` of the
standard module.

The weights `η j` of the red strands are linear forms with `η j (α_i^∨) = Λ j i`, paired by a
symmetric form `B` with `B(α_i, x) = d_i x(α_i^∨)`. Hypotheses: those of
`rowBraidCutEquivStandard`. -/
def rowGradedBraidCutEquivStandard {ρ : Equiv.Perm (Fin m₂) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ)
    {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)} (h1 : 1 < m₂)
    (ht₀ : t₂.lbl ⟨0, by omega⟩ = .inr 0) (ht₁ : t₂.lbl ⟨1, h1⟩ = .inr 1)
    (hb : EdgeBraid (show 0 < m₂ by omega) 0 g σ t₂) (hσ : redWord σ = [1, 0])
    (ht₂ : redWord t₂ = [0, 1]) (L : List (Fin ℓ × Multiset I)) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν) (u : Loadings (adjacentRow L M f β))
    (hs : ¬ Violated _ (setPairLoading M f β σ L u))
    (ht : redWord (Seq.cast h (place _ (setPairLoading M f β σ L u))) =
      L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hstd : StackedStandard hQ h (rowRelations Q Λ hQ M f β
      (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e t₂)) (pairRelations Q Λ hQ f β t₂) L u)
      (setPairLoading M f β t₂ L u))
    {H : Type*} [AddCommGroup H] [Module ℂ H] [Fintype I]
    (P : Matrix.Realization (UDot.A C) ℂ H) (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H))
    (η : Fin ℓ → Module.Dual ℂ H)
    (hB : ∀ i x, B (P.root i) x = (UDot.di C i : ℂ) * x (P.coroot i))
    (hΛ : ∀ j i, η j (P.coroot i) = (Λ j i : ℂ)) (hSym : B.IsSymm) :
    Graded.shift (rowLoadingGrade (Q := Q) (Λ := Λ) (M := M) (f := f) (C := C) (hR := hR) L (Seq.cast h (place _ (setPairLoading M f β t₂ L u))))
        (-B (η (f 1) - (β.map P.root).sum) (η (f 0))) ≃ᵍ[(ViolOrderCorner (k := k) (Q := Q)
          (Λ := Λ) (ν := ν) (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst))ᵐᵒᵖ]
      rowCutGrade (Q := Q) (Λ := Λ) (M := M) (f := f) (C := C) (hR := hR) B η L (Seq.cast h (place _ (setPairLoading M f β σ L u))) := by
  let e := rowAuxiliaryGradedEquiv Q Λ hQ M f β C hR hρ h1 ht₀ ht₁ hb hσ ht₂ L h u hs ht hstd
  have hc : -B (η (f 1) - (β.map P.root).sum) (η (f 0)) =
      (((Δ - 2) : ℤ) : ℂ) + (2 - B (η (f 0)) (η (f 1))) := by
    rw [map_sub, LinearMap.sub_apply, blackContent_pairing Λ C P B η hB hΛ, Int.cast_sub,
      Int.cast_two, hSym.eq (η (f 1)) (η (f 0))]
    ring
  refine { toLinearEquiv := e.toLinearEquiv, map_mem' := ?_, symm_map_mem' := ?_ }
  · intro z x hx
    change x ∈ Function.extend (fun n : ℤ => (n : ℂ)) (loadingStandardGrade (G) _ _) ⊥
      (z - -B (η (f 1) - (β.map P.root).sum) (η (f 0))) at hx
    by_cases hz : ∃ n : ℤ, (n : ℂ) = z - -B (η (f 1) - (β.map P.root).sum) (η (f 0))
    · obtain ⟨n, hn⟩ := hz
      rw [← hn, (Int.cast_injective (α := ℂ)).extend_apply] at hx
      have hz' : z = (((Δ - 2) + n : ℤ) : ℂ) + (2 - B (η (f 0)) (η (f 1))) := by
        rw [Int.cast_add]
        linear_combination hc - hn
      rw [hz', rowCutGrade, (intCast_add_injective _).extend_apply]
      apply e.map_mem
      change x ∈ loadingStandardGrade (G) _ _ (Δ - 2 + n - (Δ - 2))
      rwa [show Δ - 2 + n - (Δ - 2) = n by abel]
    · rw [Function.extend_apply' _ _ _ hz] at hx
      have hx0 : x = 0 := (Submodule.mem_bot k).1 hx
      rw [hx0, LinearEquiv.map_zero]
      exact zero_mem _
  · intro z y hy
    change y ∈ Function.extend (fun n : ℤ => (n : ℂ) + (2 - B (η (f 0)) (η (f 1))))
      (braidCutGrade (G) _ _ _ _) ⊥ z at hy
    change e.toLinearEquiv.symm y ∈ Function.extend (fun n : ℤ => (n : ℂ))
      (loadingStandardGrade (G) _ _) ⊥ (z - -B (η (f 1) - (β.map P.root).sum) (η (f 0)))
    by_cases hz : ∃ n : ℤ, (n : ℂ) + (2 - B (η (f 0)) (η (f 1))) = z
    · obtain ⟨n, hn⟩ := hz
      rw [← hn, (intCast_add_injective _).extend_apply] at hy
      have hz' : (n : ℂ) + (2 - B (η (f 0)) (η (f 1))) -
          -B (η (f 1) - (β.map P.root).sum) (η (f 0)) = ((n - (Δ - 2) : ℤ) : ℂ) := by
        rw [hc]
        push_cast
        ring
      rw [← hn, hz', (Int.cast_injective (α := ℂ)).extend_apply]
      exact e.symm_map_mem' hy
    · rw [Function.extend_apply' _ _ _ hz] at hy
      have hy0 : y = 0 := (Submodule.mem_bot k).1 hy
      rw [hy0, LinearEquiv.map_zero]
      exact zero_mem _

end Shift

end Categorification.Stendhal.RedBlock
