/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleStandardGrading
import Categorification.KLR.GradedFree

/-!
# Internal degrees in the label-two diagrammatic middle standard

Webster, arXiv:1309.3796v2, §8.2. The cyclic middle generator has degree
zero, and the two actual dot differentials have internal degree two.
The terminal shuffle words give the degrees of the incoming diagram
and its black-crossing translate.
-/


noncomputable section

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra TypeA Categorification.Graded DirectSum
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "oneBlack" => ({()} : Multiset Unit)
local notation "ν" => oneBlack + oneBlack
local notation "q" => parameter k
local notation "A" => TensorProductAlgebra k q weights ν
local notation "D" => parabolicFactorAlgebra q weights oneBlack oneBlack
local notation "D₀" => ParabolicInput q weights oneBlack oneBlack D
local notation "V" => ParabolicStandard q weights oneBlack oneBlack D
local notation "X" => ParabolicShuffle q weights oneBlack oneBlack D
local notation "α" => Multiset.map (addRedColor 1) (stendhalWeight 1 oneBlack)
local notation "lc" => Sum.map (id : Unit → Unit) (fun _ : Fin 1 => Fin.last 1)
local notation "δ" => Multiset.map lc (stendhalWeight 1 oneBlack)
local notation "G" => labelTwoGradingDatum k
local notation "E" => seqIdem q weights loading loading_ordered
local notation "S" => Standard k
local notation "g" => leftStandardUnit q weights loading loading_ordered
local notation "π" => stendhalTensorProjection (Q := q) weights ν
local notation "𝒜" => middleTensorGrade k (G)
local notation "𝒮" => middleStandardGFin k (G)
local notation "ℳ" => middleStandardGrade k (G)
local notation "P" => middleParabolicGFin k (G)
local notation "U" => parabolicStandardUnit q weights oneBlack oneBlack D

private abbrev factorGrade : ℤ → Submodule k D :=
  tensorGrading
    (tensorProductGrade (restrictRedGrading q weights (G)) oneBlack)
    (CycKLR.grade (restrictBlackGrading q weights (G)) (weights (Fin.last 1)) oneBlack)

private abbrev inputGrade : ℤ → Submodule k D₀ := factorGrade k

private theorem parabolicUnit_degree_zero :
    (U (1 : D)) ∈ (P).grading 0 := by
  apply Graded.mem_map_of_mem
  let u : D₀ := (1 : D)
  change BalancedTensor.tmul (oneConcatSubBimod : IndBimod (stendhalQ q weights) α δ)
    u ∈ (G).indGrading α δ (inputGrade k) 0
  have h₁ : (oneConcatSubBimod : IndBimod (stendhalQ q weights) α δ) ∈
      (G).bimodGrading α δ 0 := (G).oneConcat_mem_grade
  have h₂ : u ∈ inputGrade k 0 := (SetLike.GradedOne.one_mem : (1 : D) ∈ factorGrade k 0)
  exact (zero_add (0 : ℤ)) ▸ tmul_mem_balancedGrading h₁ h₂

/-- The cyclic diagrammatic middle generator is normalized to degree zero. -/
theorem middleStandardGenerator_mem_grade :
    g ∈ ℳ 0 := by
  change testModuleMap k g ∈ (P).grading 0
  exact (congrArg (fun z : V => z ∈ (P).grading 0) (testModuleMap_generator k)).mpr (parabolicUnit_degree_zero k)

private theorem generator_fixed : E • g = g := by
  rw [leftStandardUnit, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (seqIdem_mul_self q weights loading loading_ordered)

private theorem positionalDot_generator_degree_two
    (j : Fin (Multiset.card (stendhalWeight 2 ν))) :
    π (KLRAlgebra.x j) • g ∈ ℳ 2 := by
  have hdeg : ∀ c : Unit ⊕ Fin 2, (G).degX c = 2 := by rintro (c | c) <;> rfl
  have hx₀ := (G).x_mul_e_mem_grade j loading
  rw [hdeg] at hx₀
  have hx : π (KLRAlgebra.x j * e loading) ∈ 𝒜 2 :=
    stendhalTensorProjection_mem_grade weights (G) ν hx₀
  have h : π (KLRAlgebra.x j * e loading) • g ∈ ℳ ((2 : ℤ) + 0) :=
    (𝒮).gradedSMul.smul_mem hx (middleStandardGenerator_mem_grade k)
  have he : π (e loading) = E := stendhalTensorProjection_e weights ν loading loading_ordered
  rwa [map_mul, he, mul_smul, generator_fixed, add_zero] at h

private theorem end_mem_homGrade_of_generator
    (f : Module.End A S) (d : ℤ) (hf : f g ∈ ℳ d) :
    f ∈ homGrade A ℳ ℳ d := by
  intro i z hz
  let eval : A →ₗ[k] S :=
    { toFun := fun a => a • g
      map_add' := fun a c => add_smul a c g
      map_smul' := fun c a => smul_assoc c a g }
  let : Decomposition ℳ := (𝒮).decomposition
  have heval : PreservesGrading 𝒜 ℳ eval := by
    intro j a ha
    change a • g ∈ ℳ j
    have h : a • g ∈ ℳ (j + 0) := (𝒮).gradedSMul.smul_mem ha (middleStandardGenerator_mem_grade k)
    simpa only [add_zero] using h
  obtain ⟨a, ha⟩ := leftStandard_exists_smul_unit (Q := q) (Λ := weights) loading loading_ordered z
  have h₁ : (decompose ℳ (eval a) i).val = eval (decompose 𝒜 a i) :=
    decompose_map heval a i
  have h₂ : (decompose ℳ (eval a) i).val = z := by
    rw [show eval a = z from ha.symm, decompose_of_mem_same _ hz]
  have h₃ : f z = (decompose 𝒜 a i).val • f g :=
    (congrArg f (h₂.symm.trans h₁)).trans (f.map_smul _ g)
  have h₄ : (decompose 𝒜 a i).val • f g ∈ ℳ (i + d) :=
    (𝒮).gradedSMul.smul_mem (decompose 𝒜 a i).property hf
  exact h₃.symm ▸ h₄

/-- Each of the two actual right-dot endomorphisms has internal degree two. -/
theorem dotEnd_degree_two (i : Fin 2) : dotEnd k i ∈ homGrade A ℳ ℳ 2 := by
  apply end_mem_homGrade_of_generator k
  fin_cases i
  · exact (dotEnd_zero_gen k).symm ▸ positionalDot_generator_degree_two k ⟨1,by decide⟩
  · exact (dotEnd_one_gen k).symm ▸ positionalDot_generator_degree_two k ⟨3,by decide⟩

/-- The actual sum differential has internal degree two. -/
theorem diagramPlus_degree_two : diagramPlus k ∈ homGrade A ℳ ℳ 2 :=
  Submodule.add_mem _ (dotEnd_degree_two k 0) (dotEnd_degree_two k 1)

/-- The actual difference differential has internal degree two. -/
theorem diagramMinus_degree_two : diagramMinus k ∈ homGrade A ℳ ℳ 2 :=
  Submodule.sub_mem _ (dotEnd_degree_two k 0) (dotEnd_degree_two k 1)

local notation "μ" => stendhalWeight 2 (({()} : Multiset Unit) + {()})
local notation "n" => Multiset.card μ

private theorem firstCrossing_degree : (G).dψ 1 loading = 2 := by
  rw [(G).dψ_of_lt (show 1 + 1 < n by decide) loading]
  have h₁ : loading.lbl ⟨1, by decide⟩ = .inl () := by decide +kernel
  have h₂ : loading.lbl ⟨2, by decide⟩ = .inr 1 := by decide +kernel
  rw [h₁, h₂]
  change (1 : ℤ) * (weights 1 ()) = 2
  simp [weights]

/-- The red-black exit into the terminal loading has internal degree two. -/
theorem terminalFirstShuffle_degree : (G).degW [1] loading = 2 := by
  simpa only [GradingDatum.degW, wordProd_nil, one_smul, add_zero] using firstCrossing_degree k

/-- Adding the black crossing makes the second terminal shuffle degree zero. -/
theorem terminalSecondShuffle_degree : (G).degW [2, 1] loading = 0 := by
  have ht : wordProd n [1] • loading = terminalLoading := by decide +kernel
  have hx : (G).dψ 2 terminalLoading = -2 := by
    rw [(G).dψ_of_lt (show 2 + 1 < n by decide) terminalLoading]
    have h₂ : terminalLoading.lbl ⟨2, by decide⟩ = .inl () := by decide +kernel
    have h₃ : terminalLoading.lbl ⟨3, by decide⟩ = .inl () := by decide +kernel
    rw [h₂,h₃]
    rfl
  rw [GradingDatum.degW, ht, hx, terminalFirstShuffle_degree]
  norm_num

private theorem shuffle_act_mem_grade (word : List ℕ) {d : ℤ} {z : S}
    (hfixed : E • z = z) (hz : z ∈ ℳ d) :
    π (ψw word) • z ∈ ℳ ((G).degW word loading + d) := by
  have hword : π (ψw word * e loading) ∈ 𝒜 ((G).degW word loading) :=
    stendhalTensorProjection_mem_grade weights (G) ν ((G).ψw_mul_e_mem_grade word loading)
  have hact : π (ψw word * e loading) • z ∈ ℳ ((G).degW word loading + d) :=
    (𝒮).gradedSMul.smul_mem hword hz
  have he : π (e loading) = E := stendhalTensorProjection_e weights ν loading loading_ordered
  rwa [map_mul, he, mul_smul, hfixed] at hact

/-- The incoming exterior diagram in the middle standard is homogeneous of degree two. -/
theorem incomingExteriorDiagram_mem_grade :
    π (ψw [1]) • g + π (ψw [2,1]) • (rightMiddleDot k • g) ∈ ℳ 2 := by
  have h₁ := shuffle_act_mem_grade k [1] (generator_fixed k) (middleStandardGenerator_mem_grade k)
  rw [terminalFirstShuffle_degree, add_zero] at h₁
  have hfix : E • (rightMiddleDot k • g) = rightMiddleDot k • g := by
    rw [← dotEnd_one_gen, ← (dotEnd k 1).map_smul, generator_fixed]
  have hd : rightMiddleDot k • g ∈ ℳ 2 :=
    positionalDot_generator_degree_two k ⟨3,by decide⟩
  have h₂ := shuffle_act_mem_grade k [2,1] hfix hd
  rw [terminalSecondShuffle_degree, zero_add] at h₂
  exact Submodule.add_mem _ h₁ h₂

/-- The black-crossing translate of the incoming diagram has degree zero. -/
theorem incomingExteriorTranslate_mem_grade :
    π (ψw [2,1]) • g ∈ ℳ 0 := by
  have h := shuffle_act_mem_grade k [2,1] (generator_fixed k) (middleStandardGenerator_mem_grade k)
  rwa [terminalSecondShuffle_degree, zero_add] at h

end Categorification.Stendhal.LabelTwo
