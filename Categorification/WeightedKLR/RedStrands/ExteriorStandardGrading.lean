/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedStandardization
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardEquiv
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFiniteFiltration
import Categorification.KLR.ExtTensorK0Equiv

/-!
# Internal grading of the standardization of exterior projectives

Webster, arXiv:1309.3796v2, §5.1, Definition 5.4, at the exterior projectives in
§6.1, Proposition 6.9 and Figure 5. The grading is obtained by taking the graded
left ideals at the two input idempotents, their external tensor, the balanced
tensor for affine induction, and the ordered quotient. Neither a loading-standard
comparison nor a cohomological grading enters its construction.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR Categorification.Graded DirectSum QuantumGroup

section Projective
variable {k A : Type} [Field k] [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜] [Module.Finite k A] {e : A}

private abbrev LoadingIdeal := KMod (k := k) (ModuleCat.of A (lIdeal e))

private def loadingIdealVal : LoadingIdeal (k := k) (e := e) →ₗ[k] A where
  toFun x := (show lIdeal e from x).val
  map_add' _ _ := rfl
  map_smul' c x := (Algebra.smul_def c (show lIdeal e from x).val).symm

private def loadingIdealGraded (h₀ : e ∈ 𝒜 0) : GFin 𝒜 := by
  let f := loadingIdealVal (k := k) (e := e)
  have hf : Function.Injective f := Subtype.val_injective
  let : Module.Finite k (LoadingIdeal (k := k) (e := e)) := Module.Finite.of_injective f hf
  let ℳ := Graded.comap 𝒜 f
  let : Decomposition ℳ := (Graded.isInternal_comap 𝒜 f hf fun x n =>
    ⟨⟨_, leftIdeal_isHomogeneous h₀ n (show (f x) * e = f x from (show lIdeal e from x).2)⟩, rfl⟩).chooseDecomposition
  let : SetLike.GradedSMul 𝒜 ℳ := ⟨fun i j a x ha hx => by
    change a * f x ∈ 𝒜 (i + j)
    exact SetLike.GradedMul.mul_mem ha hx⟩
  exact { carrier := LoadingIdeal (k := k) (e := e), grading := ℳ }

end Projective

section TwoRed
variable {I k : Type} [DecidableEq I] [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin 2 → I →₀ ℕ)
  {C : CartanDatum I} (hR : IsRouquierQ C Q)
  (G : GradingDatum (stendhalQ Q Λ)) (hQ : KLRSymm Q) {θ β : Multiset I}
  (x : Seq (stendhalWeight 1 θ)) (u : Seq β)

local notation "hx" => SingleRed.ordered θ x
local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ
local notation "L" => tensorProductGrade (restrictRedGrading Q Λ G) θ
local notation "R" => CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last 1)) β
local notation "ex" => seqIdem Q (Λ ∘ Fin.castSucc) x hx
local notation "eu" => CycKLR.mk k Q (fun i => Polynomial.X ^ Λ (Fin.last 1) i) β (KLRAlgebra.e u)
local notation "X" => oldProj Q Λ θ x hx
local notation "Y" => cycProj Q Λ β u
local notation "N" => FactorModule.carrier (tensorFactor Q Λ X Y)
local notation "α" => Multiset.map (addRedColor 1) (stendhalWeight 1 θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last 1))
  (stendhalWeight 1 β)

private def exteriorLeftFactor : GFin L := by
  let : Module.Finite k Told := tensorProductAlgebra_finite (Λ ∘ Fin.castSucc) θ hR
  exact loadingIdealGraded L (mk_e_mem_tensorProductGrade _ θ x hx)

private def exteriorRightFactor : GFin R := by
  let : Module.Finite k (CycKLR k Q (fun i => Polynomial.X ^ Λ (Fin.last 1) i) β) :=
    CycKLR.module_finite (ν := β) (Q := Q) (fun i j hij => by
      obtain ⟨c, hc, h⟩ := hR.polyInY_leading i j hij
      rw [h]
      exact hc.map Polynomial.C) (fun i => Polynomial.monic_X_pow (Λ (Fin.last 1) i))
  exact loadingIdealGraded R (Graded.mem_map_of_mem _ _ ((restrictBlackGrading Q Λ G).e_mem_grade u))

/-- The actual exterior factor module, graded by the sum of the two projective degrees. -/
def exteriorFactorGFin : GFin (tensorGrading L R) :=
  (exteriorLeftFactor Λ hR G x).extTensor (exteriorRightFactor Λ hR G u)

/-- The actual ordered quotient of the affine balanced tensor on the exterior projectives. -/
def exteriorStandardGFin : GFin (tensorProductGrade G (θ + β)) :=
  standardizationGFin Λ G θ β hQ (exteriorFactorGFin Λ hR G x u)

private instance exteriorLayerModule {ν : Multiset I} (h : θ + β = ν) :
    Module k (StdLayer.carrier Q Λ (tensorLayer Q Λ h X Y)) :=
  inferInstanceAs (Module k (ParabolicStandard Q Λ θ β N))

/-- The internal grading on the carrier of `stdLayerModule`, before any coefficient change. -/
def exteriorStandardGrade {ν : Multiset I} (h : θ + β = ν) :
    ℤ → Submodule k (StdLayer.carrier Q Λ (tensorLayer Q Λ h X Y)) :=
  (exteriorStandardGFin Λ hR G hQ x u).grading

/-- The quotient grading on the actual standard layer is a direct sum. -/
instance exteriorStandardDecomposition {ν : Multiset I} (h : θ + β = ν) :
    Decomposition (exteriorStandardGrade Λ hR G hQ x u h) :=
  (exteriorStandardGFin Λ hR G hQ x u).decomposition

local notation "Ngr" => GMod.grading (GFin.toGMod (exteriorFactorGFin Λ hR G x u))

/-- The genuine input generator is the tensor of the two degree-zero loading idempotents. -/
def exteriorInputUnit : N :=
  ExtTensor.tmul (P := KMod (k := k) X) (Q := KMod (k := k) Y)
    ⟨ex, seqIdem_mul_self Q (Λ ∘ Fin.castSucc) x hx⟩ (cycUnit Q Λ u)

/-- Each exterior input generator has internal degree zero (Webster, Definitions 4.4, 5.4). -/
theorem exteriorInputUnit_mem_grade : exteriorInputUnit Λ x u ∈ Ngr 0 := by
  have h₁ : (⟨ex, seqIdem_mul_self Q (Λ ∘ Fin.castSucc) x hx⟩ :
      (exteriorLeftFactor Λ hR G x).carrier) ∈ (exteriorLeftFactor Λ hR G x).grading 0 :=
    mk_e_mem_tensorProductGrade _ θ x hx
  have h₂ : (cycUnit Q Λ u : (exteriorRightFactor Λ hR G u).carrier) ∈
      (exteriorRightFactor Λ hR G u).grading 0 :=
    Graded.mem_map_of_mem _ _ ((restrictBlackGrading Q Λ G).e_mem_grade u)
  exact (zero_add (0 : ℤ)) ▸ tmul_mem_tensorGrading h₁ h₂

/-- The canonical generator of the standard layer, represented by the identity shuffle on
`e(x) ⊗ e(u)`. -/
def exteriorStandardUnit : StdLayer.carrier Q Λ (tensorLayer Q Λ rfl X Y) :=
  parabolicStandardUnit Q Λ θ β N (exteriorInputUnit Λ x u)

/-- The identity shuffle and both input idempotents have degree zero. -/
theorem exteriorStandardUnit_mem_grade :
    exteriorStandardUnit Λ x u ∈ exteriorStandardGrade Λ hR G hQ x u rfl 0 := by
  apply Graded.mem_map_of_mem
  let ℳ : ℤ → Submodule k (ParabolicInput Q Λ θ β N) := Ngr
  change BalancedTensor.tmul _ _ ∈ G.indGrading α δ ℳ 0
  exact (zero_add (0 : ℤ)) ▸ tmul_mem_balancedGrading
    (show (KLRAlgebra.oneConcatSubBimod : KLRAlgebra.IndBimod (stendhalQ Q Λ) α δ) ∈
      G.bimodGrading α δ 0 from G.oneConcat_mem_grade)
    (show (exteriorInputUnit Λ x u : ParabolicInput Q Λ θ β N) ∈ ℳ 0 from
      exteriorInputUnit_mem_grade Λ hR G x u)

/-- The tensor product algebra acts homogeneously on the actual standard layer. -/
theorem exteriorStandardGrade_smul {i j : ℤ} {a : TensorProductAlgebra k Q Λ (θ + β)}
    {z : stdLayerModule Q Λ hQ (tensorLayer Q Λ rfl X Y)}
    (ha : a ∈ tensorProductGrade G (θ + β) i) (hz : z ∈ exteriorStandardGrade Λ hR G hQ x u rfl j) :
    a • z ∈ exteriorStandardGrade Λ hR G hQ x u rfl (i + j) :=
  (exteriorStandardGFin Λ hR G hQ x u).gradedSMul.smul_mem ha hz

end TwoRed
end Categorification.Stendhal
