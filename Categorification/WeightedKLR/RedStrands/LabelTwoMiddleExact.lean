/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleSupport
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleTerminalParabolic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Exactness of the label-two diagrammatic middle complex

Webster, arXiv:1309.3796v2, §8.2, preceding Proposition 8.4. At the
terminal loading two shuffle columns carry the same differential as at
the separated middle loading. The other ordered loading idempotents
act by zero, yielding exactness of the alternating dot maps on the
full diagrammatic standard.
-/


noncomputable section
namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra TypeA CategoryTheory
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "μ" => stendhalWeight 2 ν
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "S" => Standard k
local notation "E" => seqIdem (parameter k) weights loading loading_ordered
local notation "Et" => seqIdem (parameter k) weights terminalLoading terminalLoading_ordered
local notation "W" => fixSub k S E
local notation "T" => fixSub k S Et
local notation "π" => tensorOfKLR (parameter k) weights ν
local notation "F" => Module.End A S

private theorem projected_loading (s : Seq μ) (hs : IsRedOrdered s) :
    π (e s) = seqIdem (parameter k) weights s hs := by
  apply congrArg (TensorProductAlgebra.mk (parameter k) weights ν)
  apply Subtype.ext
  exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs)

private theorem terminal_fixed_crossing (w : List ℕ)
    (hw : wordProd (Multiset.card μ) w • loading = terminalLoading) (x : W) :
    Et • (π (ψw w) • x.val) = π (ψw w) • x.val := by
  have h : Et * π (ψw w) = π (ψw w) * E := by
    rw [← projected_loading k _ terminalLoading_ordered, ← projected_loading k _ loading_ordered]
    have ht := congrArg (π) (ψw_mul_e (Q := stendhalQ (parameter k) weights) w loading)
    rw [hw] at ht
    simpa only [tensorOfKLR, map_mul] using ht.symm
  rw [← mul_smul, h, mul_smul, x.property]

private def pairMap : W × W →ₗ[k] T where
  toFun x := ⟨π (ψw [1]) • x.1.val + π (ψw [2, 1]) • x.2.val, by
    change Et • (π (ψw [1]) • x.1.val + π (ψw [2, 1]) • x.2.val) = _
    rw [smul_add, terminal_fixed_crossing k [1] (by decide +kernel),
      terminal_fixed_crossing k [2, 1] (by decide +kernel)]⟩
  map_add' x y := by
    apply Subtype.ext
    change π (ψw [1]) • (x.1.val + y.1.val) + π (ψw [2, 1]) • (x.2.val + y.2.val) = _
    simp only [Submodule.coe_add, smul_add]
    abel
  map_smul' c x := by
    apply Subtype.ext
    change _ = c • (π (ψw [1]) • x.1.val + π (ψw [2, 1]) • x.2.val)
    simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, smul_add,
      smul_comm (π (ψw [1])) c, smul_comm (π (ψw [2, 1])) c]

private theorem pairMap_surjective : Function.Surjective (pairMap k) := by
  intro z
  obtain ⟨p, hp⟩ := terminalPolynomialEval_surjective_on_fixed k z.val z.property
  let v (q : MvPolynomial (Fin 2) k) : W :=
    ⟨dotPolynomialEval k q, dotPolynomialEval_fixed k q⟩
  refine ⟨(v p.1, v p.2), Subtype.ext ?_⟩
  exact hp

private theorem detectFactors_injective :
    Function.Injective (standardEnd_detectFactors k) := by
  have hV := middleEndomorphism_finrank k
  have : Module.Finite k (MvPolynomial (Fin 2) k ⧸ middleDotIdeal k) :=
    Webster.LabelTwo.squareQuotient_finite k
  have : Module.Finite k F :=
    Module.Finite.of_surjective (middleDotQuotientAction k).toLinearMap
      (middleDotQuotientAction_surjective k)
  have : Module.Finite k (parabolicFactorAlgebra (parameter k) weights ({()} : Multiset Unit) {()}) :=
    Module.Finite.of_surjective (standardEnd_detectFactors k) (standardEnd_detectFactors_surjective k)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := standardEnd_detectFactors k) (hV.trans (separatedFactors_finrank k).symm)).mpr
      (standardEnd_detectFactors_surjective k)

set_option maxHeartbeats 1200000 in
private theorem pairMap_injective : Function.Injective (pairMap k) := by
  intro x y h
  let E' := leftStandardEndEquivFixed (parameter k) weights loading loading_ordered
  let coord (w : W) := standardEnd_detectFactors k (E'.symm w)
  have hmap := congrArg (fun z : T => testModuleMap k z.val) h
  change testModuleMap k (π (ψw [1]) • x.1.val + π (ψw [2, 1]) • x.2.val) =
    testModuleMap k (π (ψw [1]) • y.1.val + π (ψw [2, 1]) • y.2.val) at hmap
  simp only [(testModuleMap k).map_add, (testModuleMap k).map_smul, testModuleMap_fixed] at hmap
  have he : (coord x.1, coord x.2) = (coord y.1, coord y.2) :=
    terminalParabolicColumns_injective k hmap
  exact Prod.ext
    (E'.symm.injective (detectFactors_injective k (congrArg Prod.fst he)))
    (E'.symm.injective (detectFactors_injective k (congrArg Prod.snd he)))

/-- At the terminal loading, the two shuffles identify the fixed
diagrammatic standard with two copies of the middle fixed space. -/
def terminalToTwoMiddle : T ≃ₗ[k] W × W :=
  (LinearEquiv.ofBijective (pairMap k) ⟨pairMap_injective k, pairMap_surjective k⟩).symm

private def fFixed {a : A} (f : F) : fixSub k S a →ₗ[k] fixSub k S a where
  toFun x := ⟨f x.val, by
    change a • f x.val = f x.val
    rw [← f.map_smul, show a • x.val = x.val from x.property]⟩
  map_add' x y := Subtype.ext (f.map_add x.val y.val)
  map_smul' c x := Subtype.ext ((f.restrictScalars k).map_smul c x.val)

private theorem pairMap_transport (f : F) (x : W × W) :
    fFixed k f (pairMap k x) = pairMap k (fFixed k f x.1, fFixed k f x.2) := by
  apply Subtype.ext
  exact (f.map_add _ _).trans (congrArg₂ (· + ·) (f.map_smul _ _) (f.map_smul _ _))


set_option maxHeartbeats 1600000 in
private theorem terminal_pair_exact (f g : F)
    (h : Function.Exact (fFixed k (a := E) f) (fFixed k (a := E) g)) :
    Function.Exact (fFixed k (a := Et) f) (fFixed k (a := Et) g) := by
  intro z
  obtain ⟨⟨x, y⟩, rfl⟩ := pairMap_surjective k z
  constructor
  · intro hz
    rw [pairMap_transport, ← (pairMap k).map_zero] at hz
    have hp : (fFixed k g x, fFixed k g y) = 0 := pairMap_injective k hz
    obtain ⟨a, ha⟩ := (h x).mp (congrArg Prod.fst hp)
    obtain ⟨b, hb⟩ := (h y).mp (congrArg Prod.snd hp)
    have hpair : (fFixed k f a, fFixed k f b) = (x, y) := Prod.ext ha hb
    exact ⟨pairMap k (a,b), (pairMap_transport k f (a,b)).trans (congrArg (pairMap k) hpair)⟩
  · rintro ⟨a, ha⟩
    obtain ⟨⟨x', y'⟩, rfl⟩ := pairMap_surjective k a
    have hx := (h (fFixed k f x')).mpr ⟨x', rfl⟩
    have hy := (h (fFixed k f y')).mpr ⟨y', rfl⟩
    have hp : (fFixed k g (fFixed k f x'), fFixed k g (fFixed k f y')) = 0 :=
      Prod.ext hx hy
    calc
      fFixed k g (pairMap k (x,y)) = fFixed k g (fFixed k f (pairMap k (x',y'))) :=
        congrArg (fFixed k g) ha.symm
      _ = fFixed k g (pairMap k (fFixed k f x', fFixed k f y')) :=
        congrArg (fFixed k g) (pairMap_transport k f (x',y'))
      _ = pairMap k (fFixed k g (fFixed k f x'), fFixed k g (fFixed k f y')) :=
        pairMap_transport k g _
      _ = 0 := (congrArg (pairMap k) hp).trans (pairMap k).map_zero

/-- The terminal fixed space is exact at the transition from the
difference differential to the sum differential. -/
theorem terminalMinusPlus_exact :
    Function.Exact (fFixed k (a := Et) (diagramMinus k))
      (fFixed k (a := Et) (diagramPlus k)) :=
  terminal_pair_exact k _ _ (fixedMinusPlus_exact k)

/-- The terminal fixed space is exact at the transition from the
sum differential to the difference differential. -/
theorem terminalPlusMinus_exact :
    Function.Exact (fFixed k (a := Et) (diagramPlus k))
      (fFixed k (a := Et) (diagramMinus k)) :=
  terminal_pair_exact k _ _ (fixedPlusMinus_exact k)


private abbrev orderedLoading := {s : Seq μ // IsRedOrdered s}

private theorem sum_seqIdem_labelTwo :
    ∑ s : orderedLoading, seqIdem (parameter k) weights s.val s.property = 1 := by
  classical
  have h : (∑ s : orderedLoading, StendhalAlgebra.e s.val s.property :
      StendhalAlgebra k (parameter k) weights ν) = 1 := by
    apply Subtype.ext
    rw [KLR.Corner.val_sum, KLR.Corner.val_one]
    change (∑ s : orderedLoading, StendhalAlgebraAllOrders.e s.val) =
      StendhalAlgebraAllOrders.redOrderedIdem k (parameter k) weights ν
    exact (Finset.sum_subtype _ (fun s => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _).symm
  simpa only [map_sum, map_one] using congrArg (TensorProductAlgebra.mk (parameter k) weights ν) h

private theorem middle_terminal_decompose (z : S) : E • z + Et • z = z := by
  classical
  let a : orderedLoading := ⟨loading, loading_ordered⟩
  let b : orderedLoading := ⟨terminalLoading, terminalLoading_ordered⟩
  have hab : a ≠ b := by
    intro h
    exact (show loading ≠ terminalLoading by decide +kernel) (congrArg Subtype.val h)
  calc
    E • z + Et • z =
        ∑ s ∈ ({a,b} : Finset orderedLoading), seqIdem (parameter k) weights s.val s.property • z := by
      rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton]
    _ = ∑ s : orderedLoading, seqIdem (parameter k) weights s.val s.property • z := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s _ hs
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      exact middleStandard_smul_eq_zero_of_other_loading k s.val s.property
        (fun h => hs.1 (Subtype.ext h)) (fun h => hs.2 (Subtype.ext h)) z
    _ = z := by rw [← Finset.sum_smul, sum_seqIdem_labelTwo, one_smul]

private def projectFixed (s : Seq μ) (hs : IsRedOrdered s) (z : S) :
    fixSub k S (seqIdem (parameter k) weights s hs) :=
  ⟨seqIdem (parameter k) weights s hs • z, by
    change seqIdem (parameter k) weights s hs • (seqIdem (parameter k) weights s hs • z) = _
    rw [← mul_smul, seqIdem_mul_self]⟩

private theorem diagram_exact_of_fixed (f g : F)
    (hm : Function.Exact (fFixed k (a := E) f) (fFixed k (a := E) g))
    (ht : Function.Exact (fFixed k (a := Et) f) (fFixed k (a := Et) g)) :
    Function.Exact f g := by
  intro z
  constructor
  · intro hz
    let x : W := projectFixed k loading loading_ordered z
    let y : T := projectFixed k terminalLoading terminalLoading_ordered z
    have hx : fFixed k g x = 0 := by
      apply Subtype.ext
      change g (E • z) = 0
      rw [g.map_smul, hz, smul_zero]
    have hy : fFixed k g y = 0 := by
      apply Subtype.ext
      change g (Et • z) = 0
      rw [g.map_smul, hz, smul_zero]
    obtain ⟨x', hx'⟩ := (hm x).mp hx
    obtain ⟨y', hy'⟩ := (ht y).mp hy
    refine ⟨x'.val + y'.val, ?_⟩
    have hfx : f x'.val = E • z := congrArg Subtype.val hx'
    have hfy : f y'.val = Et • z := congrArg Subtype.val hy'
    rw [f.map_add, hfx, hfy]
    exact middle_terminal_decompose k z
  · rintro ⟨a,rfl⟩
    have hm' : g (f (E • a)) = 0 := by
      let x : W := projectFixed k loading loading_ordered a
      exact congrArg Subtype.val ((hm (fFixed k f x)).mpr ⟨x, rfl⟩)
    have ht' : g (f (Et • a)) = 0 := by
      let y : T := projectFixed k terminalLoading terminalLoading_ordered a
      exact congrArg Subtype.val ((ht (fFixed k f y)).mpr ⟨y, rfl⟩)
    have h := congrArg (fun z : S => g (f z)) (middle_terminal_decompose k a)
    rw [f.map_add, g.map_add, hm', ht', zero_add] at h
    exact h.symm

/-- The difference and sum maps on the full diagrammatic standard
form an exact pair. -/
theorem diagramMinusPlus_exact : Function.Exact (diagramMinus k) (diagramPlus k) :=
  diagram_exact_of_fixed k _ _ (fixedMinusPlus_exact k) (terminalMinusPlus_exact k)

/-- The sum and difference maps on the full diagrammatic standard
form an exact pair. -/
theorem diagramPlusMinus_exact : Function.Exact (diagramPlus k) (diagramMinus k) :=
  diagram_exact_of_fixed k _ _ (fixedPlusMinus_exact k) (terminalPlusMinus_exact k)


private theorem diagramMiddle_d (n : ℕ) :
    (diagramMiddleComplex k).d (n + 1) n = diagramDifferential k n := by
  exact ChainComplex.of_d (fun _ : ℕ => ModuleCat.of A S) (diagramDifferential k) n

/-- The actual diagrammatic middle complex is exact in every positive
homological degree. -/
theorem diagramMiddleComplex_exactAt (n : ℕ) : (diagramMiddleComplex k).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
    (ComplexShape.prev_eq' _ (by rfl)) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact ((diagramMiddleComplex k).d (n + 2) (n + 1))
    ((diagramMiddleComplex k).d (n + 1) n)
  have h₁ : (diagramMiddleComplex k).d (n + 2) (n + 1) = diagramDifferential k (n + 1) :=
    diagramMiddle_d k (n + 1)
  rw [h₁, diagramMiddle_d k n]
  by_cases h : Even n
  · have hs : ¬ Even (n + 1) := by simpa [Nat.even_add_one] using h
    simpa only [diagramDifferential, ite_eq_right hs, ite_eq_left h] using! diagramMinusPlus_exact k
  · have hs : Even (n + 1) := by simpa [Nat.even_add_one] using h
    simpa only [diagramDifferential, ite_eq_left hs, ite_eq_right h] using! diagramPlusMinus_exact k

/-- Reflection preserves exactness in positive homological degrees. -/
theorem rightMiddleComplex_exactAt (n : ℕ) : (rightMiddleComplex k).ExactAt (n + 1) := by
  have h := diagramMiddleComplex_exactAt k n
  have hp : (ComplexShape.down ℕ).prev (n + 1) = n + 2 :=
    ComplexShape.prev_eq' _ (by rfl)
  have hn : (ComplexShape.down ℕ).next (n + 1) = n := by simp
  rw [HomologicalComplex.exactAt_iff' _ _ _ _ hp hn,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

/-- The degree-zero dot-sum quotient is the cokernel of the first
diagrammatic differential. -/
theorem diagramMiddleAugmentation_exact :
    Function.Exact (diagramPlus k) (diagramMiddleAugmentation k) := by
  intro z
  exact Submodule.Quotient.mk_eq_zero (LinearMap.range (diagramPlus k))


local notation "M" => ModuleCat.of A (StandardDotSumQuotient k)
local notation "C" => diagramMiddleComplex k
local notation "shape" => ComplexShape.down ℕ

/-- The diagrammatic middle augmentation as a chain map to the
dot-sum quotient placed in degree zero. -/
def diagramMiddleToQuotient : C ⟶ (ChainComplex.single₀ (ModuleCat A)).obj M :=
  (ChainComplex.toSingle₀Equiv C M).symm ⟨diagramMiddleAugmentation k, by
    rw [diagramMiddle_d k 0]
    exact diagramDifferential_zero_aug k⟩

/-- The diagrammatic periodic complex represents the actual dot-sum
quotient in the derived category. -/
theorem diagramMiddleToQuotient_quasiIso : QuasiIso (diagramMiddleToQuotient k) := by
  constructor
  intro n
  cases n with
  | succ n =>
      apply (quasiIsoAt_iff_exactAt' _ (n + 1)
        (ChainComplex.exactAt_succ_single_obj _ _)).mpr
      exact diagramMiddleComplex_exactAt k n
  | zero =>
      let f := ((HomologicalComplex.shortComplexFunctor' (ModuleCat A) shape 1 0 0).map
        (diagramMiddleToQuotient k))
      apply (ChainComplex.quasiIsoAt₀_iff _).mpr
      change ShortComplex.QuasiIso f
      have hg : ((C).sc' 1 0 0).g = 0 := (C).shape 0 0 (by decide)
      have hf' : (((ChainComplex.single₀ (ModuleCat A)).obj M).sc' 1 0 0).f = 0 := rfl
      have hg' : (((ChainComplex.single₀ (ModuleCat A)).obj M).sc' 1 0 0).g = 0 := rfl
      have haug : (diagramMiddleToQuotient k).f 0 = diagramMiddleAugmentation k :=
        ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
      refine (ShortComplex.quasiIso_iff_of_zeros' f hg hf' hg').mpr ⟨?_, ?_⟩
      · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
        change Function.Exact ((C).d 1 0) ((diagramMiddleToQuotient k).f 0)
        rw [haug, diagramMiddle_d k 0]
        exact diagramMiddleAugmentation_exact k
      · change Epi ((diagramMiddleToQuotient k).f 0)
        rw [haug]
        exact (ModuleCat.epi_iff_surjective _).mpr
          (Submodule.mkQ_surjective (LinearMap.range (diagramPlus k)))

end Categorification.Stendhal.LabelTwo
