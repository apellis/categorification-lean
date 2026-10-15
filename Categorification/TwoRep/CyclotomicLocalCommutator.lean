import Categorification.KLR.CyclotomicInductionDotted
import Categorification.TwoRep.RouqSl2

/-!
# The finite-sum commutator on the original cyclotomic functors

The existing positive and negative module equivalences are transported to the
original induction/restriction composites. Their complete forward maps are the
original mixed crossing mate and all categorical dotted ordinary cups or caps.
Both maps and their inverses are natural. `actualSumInvFrom` and `actualSumInvTo`
provide every inverse equation in the finite-sum presentation.

The equivalences retain the integral-domain, nonzero polynomial factorization,
unit-leading-coefficient, monic cyclotomic-polynomial and Cartan-degree hypotheses.
For the middle category at beta + alpha_i, the Kang–Kashiwara weight is
`pair i (Lambda - beta - alpha_i)`. Induction is source E and Kang–Kashiwara F,
so the source weight is the negative of this value. Thus the nonnegative KK case
is source `invNeg`, and the nonpositive KK case is source `invPos`.

This is a finite-sum local inversion theorem, not an assertion of a global action
or an opposite adjunction. The additive bicategory/weight-indexed packaging,
absent-colour boundary, and application of adjacent local data to the two
opposite-adjunction triangles remain separate obligations. The source convention
is Brundan, Definition 1.1, (1.6), (1.8)–(1.9), and Theorem 4.3.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.InductionCalculus
open CategoryTheory
open CategoryTheory.Functor (whiskerLeft whiskerRight)
open scoped ModuleCat.Algebra
open TwoRep
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k) (β : Multiset I)
local notation "R" => CycKLR k Q a β
local notation "β₁" => ((Singleton.singleton i : Multiset I) + β)
local notation "S" => CycKLR k Q a β₁

/-- Original mate, on arbitrary FE elements, in the actual tensor coordinates. -/
theorem mixedMate_rebase (M : ModuleCat.{max u v w} S) (t : PresentColour.FE Q i β a M) :
    (mixedMate Q i a β M).hom (feRebase Q i a β M t) =
      (PresentColour.efMiddleEquiv Q i β a M).symm
        (BalancedTensor.mapLeft (sigmaOuter Q i a β) (cyclotomicSigma_op_smul Q i β a)
          (PresentColour.feToLower Q i β a M t)) := by
  apply (PresentColour.efMiddleEquiv Q i β a M).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (mixedMate_sigma Q i a β M)
    (PresentColour.feToLower Q i β a M t)
  change (PresentColour.efMiddleEquiv Q i β a M)
    ((mixedMate Q i a β M).hom (feRebase Q i a β M
      (PresentColour.lowerToFE Q i β a M (PresentColour.feToLower Q i β a M t)))) = _ at h
  rw [PresentColour.lowerToFE_feToLower] at h
  exact h

/-- The original mixed mate, assembled from natural adjunction and crossing maps. -/
def mixedMateNat : restrictionFunctor.{u,v,w} Q i a β ⋙ inductionFunctor Q i a β ⟶
    inductionFunctor Q i a β₁ ⋙ restrictionFunctor Q i a β₁ :=
  (Functor.rightUnitor _).inv ≫
    whiskerLeft _ (cyclotomicAdjunction Q i a β₁).unit ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (Functor.associator _ _ _).hom _ ≫
    whiskerRight (whiskerLeft (restrictionFunctor Q i a β) (crossingNat Q i a β)) _ ≫
    whiskerRight (Functor.associator _ _ _).inv _ ≫
    whiskerRight (whiskerRight (cyclotomicAdjunction Q i a β).counit
      (inductionFunctor Q i a β₁)) _ ≫
    whiskerRight (Functor.leftUnitor _).hom _

@[simp] theorem mixedMateNat_app (M : ModuleCat.{max u v w} S) :
    (mixedMateNat Q i a β).app M = mixedMate Q i a β M := by
  ext t
  rfl

variable (hsym : KLRSymm Q)
  (hQ : ∀ i j : I, i ≠ j → ∃ c : k, IsUnit c ∧ (polyInY (Q i j)).leadingCoeff = Polynomial.C c)
  (ha : ∀ i, (a i).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β₁))

/-- Actual original-functor commutator at nonnegative KK weight (nonpositive source weight). -/
def originalPositiveEquiv (M : ModuleCat.{max u v w} S) (hwt : 0 ≤ wt) :
    ((restrictionFunctor Q i a β ⋙ inductionFunctor Q i a β).obj M × (Fin (wt).toNat → M)) ≃ₗ[S]
      (inductionFunctor Q i a β₁ ⋙ restrictionFunctor Q i a β₁).obj M :=
  ((feRebaseEquiv Q i a β M).symm.prodCongr (LinearEquiv.refl S _)).trans
    (PresentColour.positiveEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg hwt)

/-- Actual original-functor commutator at nonpositive KK weight (nonnegative source weight). -/
def originalNegativeEquiv (M : ModuleCat.{max u v w} S) (hwt : wt ≤ 0) :
    (restrictionFunctor Q i a β ⋙ inductionFunctor Q i a β).obj M ≃ₗ[S]
      ((inductionFunctor Q i a β₁ ⋙ restrictionFunctor Q i a β₁).obj M × (Fin (-wt).toNat → M)) :=
  (feRebaseEquiv Q i a β M).symm.trans
    (PresentColour.negativeEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg hwt)

include hsym hQ ha hΛ hdeg in
theorem positive_original_mate (M : ModuleCat.{max u v w} S) (hwt : 0 ≤ wt) (t : PresentColour.FE Q i β a M) :
    (PresentColour.positiveEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg) hwt (t, 0) = (mixedMate Q i a β M).hom (feRebase Q i a β M t) := by
  rw [mixedMate_rebase]
  obtain ⟨t, rfl⟩ := (PresentColour.indResEquiv Q i β a M).symm.surjective t
  change (PresentColour.positiveEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg) hwt (PresentColour.lowerToFE Q i β a M t, 0) = _
  change _ = (PresentColour.efMiddleEquiv Q i β a M).symm
    (BalancedTensor.mapLeft (sigmaOuter Q i a β) (cyclotomicSigma_op_smul Q i β a)
      ((PresentColour.indResEquiv Q i β a M) ((PresentColour.indResEquiv Q i β a M).symm t)))
  rw [LinearEquiv.apply_symm_apply]
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]; exact map_zero ((PresentColour.positiveEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg) hwt)
  | add t u ht hu =>
    rw [map_add]
    have hz : (PresentColour.lowerToFE Q i β a M t + PresentColour.lowerToFE Q i β a M u,
        (0 : Fin (wt).toNat → M)) =
        (PresentColour.lowerToFE Q i β a M t, 0) +
          (PresentColour.lowerToFE Q i β a M u, 0) := by simp only [Prod.mk_add_mk, add_zero]
    rw [hz, map_add, ht, hu, map_add, map_add]
  | tmul l n => exact PresentColour.positiveEquiv_crossing Q i β a M hsym hQ ha RD Λ hΛ hdeg hwt l n

include hsym hQ ha hΛ hdeg in
theorem negative_original_mate (M : ModuleCat.{max u v w} S) (hwt : wt ≤ 0) (t : PresentColour.FE Q i β a M) :
    ((PresentColour.negativeEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg) hwt t).1 = (mixedMate Q i a β M).hom (feRebase Q i a β M t) := by
  rw [mixedMate_rebase]
  obtain ⟨t, rfl⟩ := (PresentColour.indResEquiv Q i β a M).symm.surjective t
  change ((PresentColour.negativeEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg) hwt (PresentColour.lowerToFE Q i β a M t)).1 = _
  change _ = (PresentColour.efMiddleEquiv Q i β a M).symm
    (BalancedTensor.mapLeft (sigmaOuter Q i a β) (cyclotomicSigma_op_smul Q i β a)
      ((PresentColour.indResEquiv Q i β a M) ((PresentColour.indResEquiv Q i β a M).symm t)))
  rw [LinearEquiv.apply_symm_apply]
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero, Prod.fst_zero]
  | add t u ht hu => simp only [map_add, Prod.fst_add, ht, hu]
  | tmul l n =>
    rw [PresentColour.negativeEquiv_tmul]
    rfl


/-- The forward crossing component of the actual equivalence is the original mixed mate. -/
theorem originalPositiveEquiv_mate (M : ModuleCat.{max u v w} S) (hwt : 0 ≤ wt)
    (t : (restrictionFunctor Q i a β ⋙ inductionFunctor Q i a β).obj M) :
    originalPositiveEquiv Q i a β hsym hQ ha RD Λ hΛ hdeg M hwt (t, 0) =
      (mixedMate Q i a β M).hom t := by
  obtain ⟨t, rfl⟩ := (feRebaseEquiv Q i a β M).surjective t
  change (PresentColour.positiveEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg hwt)
    ((feRebaseEquiv Q i a β M).symm ((feRebaseEquiv Q i a β M) t), 0) = _
  rw [LinearEquiv.symm_apply_apply]
  exact positive_original_mate Q i a β hsym hQ ha RD Λ hΛ hdeg M hwt t

/-- The first component of the actual equivalence is the original mixed mate. -/
theorem originalNegativeEquiv_mate (M : ModuleCat.{max u v w} S) (hwt : wt ≤ 0)
    (t : (restrictionFunctor Q i a β ⋙ inductionFunctor Q i a β).obj M) :
    (originalNegativeEquiv Q i a β hsym hQ ha RD Λ hΛ hdeg M hwt t).1 =
      (mixedMate Q i a β M).hom t := by
  obtain ⟨t, rfl⟩ := (feRebaseEquiv Q i a β M).surjective t
  change (PresentColour.negativeEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg hwt
    ((feRebaseEquiv Q i a β M).symm ((feRebaseEquiv Q i a β M) t))).1 = _
  rw [LinearEquiv.symm_apply_apply]
  exact negative_original_mate Q i a β hsym hQ ha RD Λ hΛ hdeg M hwt t

local notation "Pos" => originalPositiveEquiv Q i a β hsym hQ ha RD Λ hΛ hdeg
local notation "Neg" => originalNegativeEquiv Q i a β hsym hQ ha RD Λ hΛ hdeg
local notation "FEF" => (restrictionFunctor Q i a β ⋙ inductionFunctor Q i a β)
local notation "EFF" => (inductionFunctor Q i a β₁ ⋙ restrictionFunctor Q i a β₁)

/-- All finite-sum columns are the categorical dotted ordinary units. -/
theorem originalPositiveEquiv_dots (M : ModuleCat.{max u v w} S) (hwt : 0 ≤ wt)
    (v : Fin (wt).toNat → M) :
    Pos M hwt (0, v) = ∑ d : Fin (wt).toNat, (dottedUnit Q i a β₁ d).app M (v d) := by
  change PresentColour.positiveEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg hwt
    ((feRebaseEquiv Q i a β M).symm 0, v) = _
  rw [map_zero, PresentColour.positiveEquiv_dots, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [PresentColour.positiveEquiv_dot_coefficient]
  exact (LinearEquiv.symm_apply_eq _).mpr (dottedUnit_comparison Q i a β M d (v d)).symm

/-- The entire positive commutator, not only individual generators. -/
theorem originalPositiveEquiv_apply (M : ModuleCat.{max u v w} S) (hwt : 0 ≤ wt)
    (z : (FEF).obj M × (Fin (wt).toNat → M)) :
    Pos M hwt z = (mixedMate Q i a β M).hom z.1 +
      ∑ d : Fin (wt).toNat, (dottedUnit Q i a β₁ d).app M (z.2 d) := by
  have hz : z = ((z.1, 0) : (FEF).obj M × (Fin (wt).toNat → M)) + (0, z.2) := by
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  calc
    Pos M hwt z = Pos M hwt (z.1, 0) + Pos M hwt (0, z.2) := by
      conv_lhs => rw [hz]
      exact map_add _ _ _
    _ = _ := congrArg₂ (· + ·)
      (originalPositiveEquiv_mate Q i a β hsym hQ ha RD Λ hΛ hdeg M hwt z.1)
      (originalPositiveEquiv_dots Q i a β hsym hQ ha RD Λ hΛ hdeg M hwt z.2)

/-- All finite-sum rows are the categorical dotted ordinary counits. -/
theorem originalNegativeEquiv_dots (M : ModuleCat.{max u v w} S) (hwt : wt ≤ 0)
    (t : (FEF).obj M) (d : Fin (-wt).toNat) :
    (Neg M hwt t).2 d = (dottedCounit Q i a β d).app M t := by
  obtain ⟨t, rfl⟩ := (feRebaseEquiv Q i a β M).surjective t
  obtain ⟨l, rfl⟩ := (PresentColour.indResEquiv Q i β a M).symm.surjective t
  change (PresentColour.negativeEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg hwt
    ((feRebaseEquiv Q i a β M).symm ((feRebaseEquiv Q i a β M)
      (PresentColour.lowerToFE Q i β a M l)))).2 d = _
  rw [LinearEquiv.symm_apply_apply]
  induction l using BalancedTensor.induction_on with
  | zero => simp only [map_zero, Prod.snd_zero, Pi.zero_apply]
  | add l l' hl hl' => simp only [map_add, Prod.snd_add, Pi.add_apply, hl, hl']
  | tmul x m =>
    rw [PresentColour.negativeEquiv_tmul]
    exact (dottedCounit_comparison Q i a β M d x m).symm

theorem originalNegativeEquiv_apply (M : ModuleCat.{max u v w} S) (hwt : wt ≤ 0)
    (t : (FEF).obj M) :
    Neg M hwt t = ((mixedMate Q i a β M).hom t,
      fun d : Fin (-wt).toNat => (dottedCounit Q i a β d).app M t) := by
  apply Prod.ext
  · exact originalNegativeEquiv_mate Q i a β hsym hQ ha RD Λ hΛ hdeg M hwt t
  · funext d
    exact originalNegativeEquiv_dots Q i a β hsym hQ ha RD Λ hΛ hdeg M hwt t d

/-- The scalar-presentation comparison is natural for every module homomorphism. -/
theorem feUnbase_natural {M M' : ModuleCat.{max u v w} S} (f : M ⟶ M') (t : (FEF).obj M) :
    feUnbase Q i a β M' ((FEF).map f t) =
      PresentColour.feMap Q i β a M f.hom (feUnbase Q i a β M t) := by
  have h : (feUnbase Q i a β M').comp ((FEF).map f).hom =
      (PresentColour.feMap Q i β a M f.hom).comp (feUnbase Q i a β M) :=
    BalancedTensor.extB fun _ _ => rfl
  exact DFunLike.congr_fun h t

theorem originalPositiveEquiv_natural (hwt : 0 ≤ wt)
    {M M' : ModuleCat.{max u v w} S} (f : M ⟶ M')
    (z : (FEF).obj M × (Fin (wt).toNat → M)) :
    (EFF).map f (Pos M hwt z) = Pos M' hwt ((FEF).map f z.1, fun d => f (z.2 d)) := by
  change AbsentColour.efMap Q i a β₁ M f.hom
    (PresentColour.positiveEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg hwt
      (feUnbase Q i a β M z.1, z.2)) = _
  rw [PresentColour.positiveEquiv_natural]
  change _ = PresentColour.positiveEquiv Q i β a M' hsym hQ ha RD Λ hΛ hdeg hwt
    (feUnbase Q i a β M' ((FEF).map f z.1), fun d => f (z.2 d))
  rw [feUnbase_natural]

theorem originalNegativeEquiv_natural (hwt : wt ≤ 0)
    {M M' : ModuleCat.{max u v w} S} (f : M ⟶ M') (t : (FEF).obj M) :
    Neg M' hwt ((FEF).map f t) =
      ((EFF).map f (Neg M hwt t).1, fun d => f ((Neg M hwt t).2 d)) := by
  change PresentColour.negativeEquiv Q i β a M' hsym hQ ha RD Λ hΛ hdeg hwt
    (feUnbase Q i a β M' ((FEF).map f t)) = _
  rw [feUnbase_natural, PresentColour.negativeEquiv_natural]
  rfl

theorem originalPositiveEquiv_symm_natural (hwt : 0 ≤ wt)
    {M M' : ModuleCat.{max u v w} S} (f : M ⟶ M') (t : (EFF).obj M) :
    (Pos M' hwt).symm ((EFF).map f t) =
      ((FEF).map f ((Pos M hwt).symm t).1, fun d => f (((Pos M hwt).symm t).2 d)) := by
  apply (Pos M' hwt).injective
  rw [LinearEquiv.apply_symm_apply, ← originalPositiveEquiv_natural, LinearEquiv.apply_symm_apply]

theorem originalNegativeEquiv_symm_natural (hwt : wt ≤ 0)
    {M M' : ModuleCat.{max u v w} S} (f : M ⟶ M')
    (z : (EFF).obj M × (Fin (-wt).toNat → M)) :
    (Neg M' hwt).symm ((EFF).map f z.1, fun d => f (z.2 d)) =
      (FEF).map f ((Neg M hwt).symm z) := by
  apply (Neg M' hwt).injective
  rw [LinearEquiv.apply_symm_apply, originalNegativeEquiv_natural, LinearEquiv.apply_symm_apply]

/-- The inverse crossing column at nonnegative Kang–Kashiwara weight. -/
def positiveInverseCrossing (hwt : 0 ≤ wt) :
    inductionFunctor.{u,v,w} Q i a β₁ ⋙ restrictionFunctor Q i a β₁ ⟶ FEF where
  app M := ModuleCat.ofHom ((LinearMap.fst S _ _).comp (Pos M hwt).symm.toLinearMap)
  naturality M M' f := by
    ext t
    exact congrArg Prod.fst
      (originalPositiveEquiv_symm_natural Q i a β hsym hQ ha RD Λ hΛ hdeg hwt f t)

/-- The finite inverse rows; unused indices are zero. -/
def positiveInverseDot (hwt : 0 ≤ wt) (d : ℕ) : EFF ⟶ 𝟭 (ModuleCat.{max u v w} S) := by
  classical
  exact if hd : d < (wt).toNat then
    { app := fun M => ModuleCat.ofHom
        ((LinearMap.proj (⟨d, hd⟩ : Fin (wt).toNat)).comp
          ((LinearMap.snd S _ _).comp (Pos M hwt).symm.toLinearMap))
      naturality := fun M M' f => by
        ext t
        exact congrArg (fun z => z.2 ⟨d, hd⟩)
          (originalPositiveEquiv_symm_natural Q i a β hsym hQ ha RD Λ hΛ hdeg hwt f t) }
  else 0

theorem positiveInverseDot_app (hwt : 0 ≤ wt) (d : ℕ) (hd : d < (wt).toNat)
    (M : ModuleCat.{max u v w} S) (t : (EFF).obj M) :
    (positiveInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d).app M t =
      ((Pos M hwt).symm t).2 ⟨d, hd⟩ := by
  simp only [positiveInverseDot, dite_eq_left hd]
  rfl

theorem originalPositiveEquiv_single (M : ModuleCat.{max u v w} S) (hwt : 0 ≤ wt)
    (d : Fin (wt).toNat) (m : M) :
    Pos M hwt (0, Pi.single d m) = (dottedUnit Q i a β₁ d).app M m := by
  classical
  rw [originalPositiveEquiv_dots, Finset.sum_eq_single d]
  · rw [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, map_zero]
  · exact fun hd => (hd (Finset.mem_univ d)).elim

private theorem positiveInverse_total (hwt : 0 ≤ wt) :
    positiveInverseCrossing.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt ≫ mixedMateNat.{u,v,w} Q i a β + ∑ d ∈ Finset.range (wt).toNat, positiveInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d ≫ dottedUnit Q i a β₁ d = 𝟙 _ := by
    ext M : 2
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    simp only [NatTrans.comp_app, NatTrans.app_add, NatTrans.app_sum,
      ModuleCat.hom_add, ModuleCat.hom_sum, LinearMap.add_apply, LinearMap.sum_apply,
      ModuleCat.hom_comp, LinearMap.comp_apply, mixedMateNat_app]
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [positiveInverseDot_app _ _ _ _ _ _ _ _ _ _ _ _ _ (Fin.isLt _)]
    exact (originalPositiveEquiv_apply Q i a β hsym hQ ha RD Λ hΛ hdeg M hwt
      ((Pos M hwt).symm t)).symm.trans ((Pos M hwt).apply_symm_apply t)

private theorem positiveInverse_ff (hwt : 0 ≤ wt) :
    mixedMateNat.{u,v,w} Q i a β ≫ positiveInverseCrossing.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt = 𝟙 _ := by
    ext M : 2
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change ((Pos M hwt).symm ((mixedMateNat Q i a β).app M t)).1 = t
    rw [mixedMateNat_app]
    have h := (Pos M hwt).symm_apply_apply (t, 0)
    rw [originalPositiveEquiv_mate] at h
    exact congrArg Prod.fst h

private theorem positiveInverse_fg (hwt : 0 ≤ wt) :
    ∀ d, d < (wt).toNat → mixedMateNat.{u,v,w} Q i a β ≫ positiveInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d = 0 := by
    intro d hd
    ext M : 2
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change (positiveInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d).app M
      ((mixedMateNat Q i a β).app M t) = 0
    rw [positiveInverseDot_app _ _ _ _ _ _ _ _ _ _ _ _ _ hd, mixedMateNat_app]
    have h := (Pos M hwt).symm_apply_apply (t, 0)
    rw [originalPositiveEquiv_mate] at h
    exact congrArg (fun z => z.2 ⟨d, hd⟩) h

private theorem positiveInverse_gf (hwt : 0 ≤ wt) :
    ∀ d, d < (wt).toNat → dottedUnit Q i a β₁ d ≫ positiveInverseCrossing.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt = 0 := by
    intro d hd
    ext M : 2
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change M at m
    change ((Pos M hwt).symm ((dottedUnit Q i a β₁ d).app M m)).1 = 0
    have h := (Pos M hwt).symm_apply_apply (0, Pi.single (⟨d, hd⟩ : Fin (wt).toNat) m)
    rw [originalPositiveEquiv_single] at h
    exact congrArg Prod.fst h

private theorem positiveInverse_gg (hwt : 0 ≤ wt) :
    ∀ d e, d < (wt).toNat → e < (wt).toNat → dottedUnit Q i a β₁ d ≫ positiveInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt e = if d = e then 𝟙 _ else 0 := by
    classical
    intro d e hd he
    ext M : 2
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change M at m
    have h := (Pos M hwt).symm_apply_apply (0, Pi.single (⟨d, hd⟩ : Fin (wt).toNat) m)
    rw [originalPositiveEquiv_single] at h
    have hh := congrArg (fun z => z.2 ⟨e, he⟩) h
    change (positiveInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt e).app M
      ((dottedUnit Q i a β₁ d).app M m) = _
    rw [positiveInverseDot_app _ _ _ _ _ _ _ _ _ _ _ _ _ he, hh]
    by_cases hde : d = e
    · subst e
      rw [ite_eq_left rfl]
      change (Pi.single (⟨d, hd⟩ : Fin (wt).toNat) m : Fin (wt).toNat → M) ⟨d, he⟩ = m
      rw [Pi.single_eq_same]
    · rw [ite_eq_right hde]
      change (Pi.single (⟨d, hd⟩ : Fin (wt).toNat) m : Fin (wt).toNat → M) ⟨e, he⟩ = 0
      exact Pi.single_eq_of_ne (M := fun _ : Fin (wt).toNat => M)
        (fun h => hde (congrArg Fin.val h).symm) m

/-- The actual finite-sum inverse, on the original functors and original dotted cups.
This is the source nonpositive inversion, since source weight is minus KK weight. -/
def actualSumInvFrom (hwt : 0 ≤ wt) :
    SumInvFrom (mixedMateNat.{u,v,w} Q i a β) (dottedUnit Q i a β₁) (wt).toNat where
  f' := positiveInverseCrossing.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  g' := positiveInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  total := positiveInverse_total Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  ff := positiveInverse_ff Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  fg := positiveInverse_fg Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  gf := positiveInverse_gf Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  gg := positiveInverse_gg Q i a β hsym hQ ha RD Λ hΛ hdeg hwt

/-- The inverse crossing row at nonpositive Kang–Kashiwara weight. -/
def negativeInverseCrossing (hwt : wt ≤ 0) :
    inductionFunctor.{u,v,w} Q i a β₁ ⋙ restrictionFunctor Q i a β₁ ⟶ FEF where
  app M := ModuleCat.ofHom ((Neg M hwt).symm.toLinearMap.comp (LinearMap.inl S _ _))
  naturality M M' f := by
    ext t
    have h := originalNegativeEquiv_symm_natural Q i a β hsym hQ ha RD Λ hΛ hdeg hwt f (t, 0)
    change (Neg M' hwt).symm ((EFF).map f t, 0) = (FEF).map f ((Neg M hwt).symm (t, 0))
    have hz : (fun d : Fin (-wt).toNat => f ((0 : Fin (-wt).toNat → M) d)) = 0 := by
      funext d
      exact map_zero f.hom
    dsimp only [Prod.fst, Prod.snd] at h
    rw [hz] at h
    exact h

/-- The finite inverse columns, with zero at unused indices. -/
def negativeInverseDot (hwt : wt ≤ 0) (d : ℕ) : 𝟭 (ModuleCat.{max u v w} S) ⟶ FEF := by
  classical
  exact if hd : d < (-wt).toNat then
    { app := fun M => ModuleCat.ofHom ((Neg M hwt).symm.toLinearMap.comp
        ((LinearMap.inr S _ _).comp (LinearMap.single S (fun _ : Fin (-wt).toNat => M) ⟨d, hd⟩)))
      naturality := fun M M' f => by
        ext m
        change M at m
        have h := originalNegativeEquiv_symm_natural Q i a β hsym hQ ha RD Λ hΛ hdeg hwt f
          (0, Pi.single (⟨d, hd⟩ : Fin (-wt).toNat) m)
        have hs : (fun e => f ((Pi.single (⟨d, hd⟩ : Fin (-wt).toNat) m : Fin (-wt).toNat → M) e)) =
            Pi.single ⟨d, hd⟩ (f m) := by
          funext e
          exact LinearMap.apply_single (fun _ : Fin (-wt).toNat => f.hom) ⟨d, hd⟩ e m
        change (Neg M' hwt).symm (0, Pi.single (⟨d, hd⟩ : Fin (-wt).toNat) (f m)) =
          (FEF).map f ((Neg M hwt).symm (0, Pi.single (⟨d, hd⟩ : Fin (-wt).toNat) m))
        simpa only [map_zero, hs] using h }
  else 0

theorem negativeInverseDot_app (hwt : wt ≤ 0) (d : ℕ) (hd : d < (-wt).toNat)
    (M : ModuleCat.{max u v w} S) (m : M) :
    (negativeInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d).app M m =
      (Neg M hwt).symm (0, Pi.single (⟨d, hd⟩ : Fin (-wt).toNat) m) := by
  simp only [negativeInverseDot, dite_eq_left hd]
  rfl

theorem originalNegativeEquiv_symm_apply (M : ModuleCat.{max u v w} S) (hwt : wt ≤ 0)
    (z : (EFF).obj M × (Fin (-wt).toNat → M)) :
    (Neg M hwt).symm z =
      (negativeInverseCrossing.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt).app M z.1 +
        ∑ d : Fin (-wt).toNat,
          (negativeInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d).app M (z.2 d) := by
  classical
  have hz : z = ((z.1, 0) : (EFF).obj M × (Fin (-wt).toNat → M)) +
      ∑ d : Fin (-wt).toNat, ((0, Pi.single d (z.2 d)) : (EFF).obj M × (Fin (-wt).toNat → M)) := by
    rw [← prod_mk_sum, Finset.sum_const_zero, LinearMap.sum_single_apply]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  conv_lhs => rw [hz]
  rw [map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  exact (negativeInverseDot_app Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d d.isLt M (z.2 d)).symm

private theorem negativeInverse_total (hwt : wt ≤ 0) :
    mixedMateNat.{u,v,w} Q i a β ≫ negativeInverseCrossing.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt +
      ∑ d ∈ Finset.range (-wt).toNat, dottedCounit Q i a β d ≫
        negativeInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d = 𝟙 _ := by
  ext M : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  simp only [NatTrans.comp_app, NatTrans.app_add, NatTrans.app_sum,
    ModuleCat.hom_add, ModuleCat.hom_sum, LinearMap.add_apply, LinearMap.sum_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply, mixedMateNat_app]
  rw [← Fin.sum_univ_eq_sum_range]
  have h := originalNegativeEquiv_symm_apply Q i a β hsym hQ ha RD Λ hΛ hdeg M hwt
    (Neg M hwt t)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [originalNegativeEquiv_apply] at h
  exact h.symm

private theorem negativeInverse_ff (hwt : wt ≤ 0) :
    negativeInverseCrossing.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt ≫ mixedMateNat Q i a β = 𝟙 _ := by
  ext M : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have h := (Neg M hwt).apply_symm_apply (t, 0)
  rw [originalNegativeEquiv_apply] at h
  exact congrArg Prod.fst h

private theorem negativeInverse_fg (hwt : wt ≤ 0) :
    ∀ d, d < (-wt).toNat → negativeInverseCrossing.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt ≫
      dottedCounit Q i a β d = 0 := by
  intro d hd
  ext M : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have h := (Neg M hwt).apply_symm_apply (t, 0)
  rw [originalNegativeEquiv_apply] at h
  exact congrArg (fun z => z.2 ⟨d, hd⟩) h

private theorem negativeInverse_gf (hwt : wt ≤ 0) :
    ∀ d, d < (-wt).toNat → negativeInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d ≫
      mixedMateNat Q i a β = 0 := by
  intro d hd
  ext M : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M at m
  change (mixedMateNat Q i a β).app M
    ((negativeInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d).app M m) = 0
  rw [negativeInverseDot_app _ _ _ _ _ _ _ _ _ _ _ _ _ hd, mixedMateNat_app]
  have h := (Neg M hwt).apply_symm_apply (0, Pi.single (⟨d, hd⟩ : Fin (-wt).toNat) m)
  rw [originalNegativeEquiv_apply] at h
  exact congrArg Prod.fst h

private theorem negativeInverse_gg (hwt : wt ≤ 0) :
    ∀ d e, d < (-wt).toNat → e < (-wt).toNat →
      negativeInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d ≫ dottedCounit Q i a β e =
        if d = e then 𝟙 _ else 0 := by
  classical
  intro d e hd he
  ext M : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M at m
  change (dottedCounit Q i a β e).app M
    ((negativeInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt d).app M m) = _
  rw [negativeInverseDot_app _ _ _ _ _ _ _ _ _ _ _ _ _ hd]
  have h := (Neg M hwt).apply_symm_apply (0, Pi.single (⟨d, hd⟩ : Fin (-wt).toNat) m)
  rw [originalNegativeEquiv_apply] at h
  have hh := congrArg (fun z => z.2 ⟨e, he⟩) h
  change (dottedCounit Q i a β e).app M _ = _ at hh
  rw [hh]
  by_cases hde : d = e
  · subst e
    rw [ite_eq_left rfl]
    change (Pi.single (⟨d, hd⟩ : Fin (-wt).toNat) m : Fin (-wt).toNat → M) ⟨d, he⟩ = m
    rw [Pi.single_eq_same]
  · rw [ite_eq_right hde]
    change (Pi.single (⟨d, hd⟩ : Fin (-wt).toNat) m : Fin (-wt).toNat → M) ⟨e, he⟩ = 0
    exact Pi.single_eq_of_ne (M := fun _ : Fin (-wt).toNat => M)
      (fun h => hde (congrArg Fin.val h).symm) m

/-- The source nonnegative inversion on the original functors, with all inverse equations. -/
def actualSumInvTo (hwt : wt ≤ 0) :
    SumInvTo (mixedMateNat.{u,v,w} Q i a β) (dottedCounit Q i a β) (-wt).toNat where
  f' := negativeInverseCrossing.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  g' := negativeInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  total := negativeInverse_total.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  ff := negativeInverse_ff Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  fg := negativeInverse_fg Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  gf := negativeInverse_gf Q i a β hsym hQ ha RD Λ hΛ hdeg hwt
  gg := negativeInverse_gg Q i a β hsym hQ ha RD Λ hΛ hdeg hwt

/-- The two inverse crossing choices agree when both sign presentations apply. -/
theorem inverseCrossing_zero_agree (hp : 0 ≤ wt) (hn : wt ≤ 0) :
    positiveInverseCrossing.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hp =
      negativeInverseCrossing Q i a β hsym hQ ha RD Λ hΛ hdeg hn := by
  let p := actualSumInvFrom.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hp
  let n := actualSumInvTo.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hn
  change p.f' = n.f'
  calc
    p.f' = (n.f' ≫ mixedMateNat Q i a β) ≫ p.f' := by rw [n.ff, Category.id_comp]
    _ = n.f' := by rw [Category.assoc, p.ff, Category.comp_id]

/-- At zero KK weight there are no identity summands: the actual mixed mate is a
natural isomorphism. This is the weight-zero case, not an absent-colour boundary. -/
def mixedMateIsoAtZero (hwt : wt = 0) :
    restrictionFunctor.{u,v,w} Q i a β ⋙ inductionFunctor Q i a β ≅ EFF where
  hom := mixedMateNat Q i a β
  inv := positiveInverseCrossing Q i a β hsym hQ ha RD Λ hΛ hdeg (by omega)
  hom_inv_id := positiveInverse_ff Q i a β hsym hQ ha RD Λ hΛ hdeg (by omega)
  inv_hom_id := by
    have h := positiveInverse_total.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg (by omega)
    simpa only [hwt, Int.toNat_zero, Finset.range_zero, Finset.sum_empty, add_zero] using h

end Categorification.KLR.KLRAlgebra.AbsentColour.InductionCalculus
