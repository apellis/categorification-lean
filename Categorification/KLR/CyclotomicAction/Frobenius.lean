/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumCyclic
import Categorification.KLR.CyclotomicAction.VacuumSupport
import Categorification.KLR.CyclotomicAbsentColour
import Categorification.TwoRep.WordAdjunction
import Categorification.TwoRep.LinFunBiproduct
import Categorification.Algebra.AmbidextrousTraceSeparating
import Categorification.Diagrams.KLR.MatEndTrace
import Categorification.KLR.Rouquier.PolynomialDegree

/-!
# Cyclotomic KLR algebras are Frobenius

Webster, arXiv:1309.3796v2, Theorem 3.18: over a field, the cyclotomic KLR algebra `R^Λ(ν)`
carries a nondegenerate trace. Following Webster's proof, the trace closes the strands of a
word with the biadjunction of `E_i` and `F_i` in the cyclotomic categorical action
(Theorem 3.17, `cyclotomicFamily`), landing in the endomorphisms of the vacuum `R^Λ(∅) = k`.

The words `E_t 𝕍`, `t ∈ Seq ν`, applied to the vacuum `𝕍` supported on the empty block are the
cyclotomic modules `R^Λ(ν) e(rev t)` (`Vacuum`, `VacuumCyclic`). This file shows:

* `eq_of_wgen`: a morphism out of `E_t 𝕍` is determined by its value on the generator;
* `vacEnd`, `vacEnd_bijective`, `vacEnd_mul`: the matrix algebra of morphisms between the words
  `E_t 𝕍` is anti-isomorphic to `R^Λ(ν)`, through the action of `R(ν)` on words read through
  the anti-involution `hflip ∘ σ`;
* `cyclotomic_trace_nondegenerate`: the Frobenius trace;
* `IsRouquierQ.cyclotomic_frobenius`: Theorem 3.18 for the parameters of Webster's setting
  (Rouquier's homogeneous parameters `Q` and a cyclotomic quotient of weight `Λ`).
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits TwoRep KLRAlgebra

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y} {Λ : X}
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg

set_option quotPrecheck false in
set_option hygiene false in
local notation "𝕍" => emptyBlockObj.{u, v, w} Q a RD Λ

local notation "μ₀" => blockWeight RD Λ 0

/-! ### The vacuum supported on the empty block -/

/-- The generator `1` of the vacuum `R^Λ(∅)`. -/
def vac₀ : (𝕍) ⟨0, rfl⟩ := fun _ => ULift.up 1

/-- The coordinate of the vacuum. -/
def vacCoord : (𝕍) ⟨0, rfl⟩ →ₗ[CycKLR k Q a 0] CycKLR k Q a 0 where
  toFun f := (f ⟨rfl⟩).down
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vacCoord_vac₀ : vacCoord.{u, v, w} (Q := Q) (a := a) (RD := RD) (Λ := Λ) vac₀ = 1 := rfl

theorem vac_cyclic (x : (𝕍) ⟨0, rfl⟩) :
    ∃ z : CycKLR k Q a 0, x = z • vac₀.{u, v, w} (Q := Q) (a := a) (RD := RD) (Λ := Λ) := by
  refine ⟨(x ⟨rfl⟩).down, funext fun p => ?_⟩
  obtain rfl : p = ⟨rfl⟩ := Subsingleton.elim _ _
  exact ULift.ext _ _ (mul_one _).symm

theorem vac_isZero (β : WeightBlocks RD Λ μ₀) (hβ : β.1 ≠ 0) :
    IsZero ((𝕍) β) :=
  isZero_emptyBlockObj hβ

/-! ### Separation at the vacuum -/

omit [DecidableEq I] in
/-- The block of weight `-Λ` with no strands. -/
theorem eq_zeroBlk {β : WeightBlocks RD Λ μ₀} (hβ : β.1 = 0) : β = ⟨0, rfl⟩ :=
  Subtype.ext hβ

/-- Over `R^Λ(∅) = k`, every nonzero vector of a module has a nonzero linear functional. -/
theorem exists_cycZero_functional {M : Type*} [AddCommGroup M] [Module (CycKLR k Q a 0) M]
    {z : M} (hz : z ≠ 0) :
    ∃ φ : M →ₗ[CycKLR k Q a 0] CycKLR k Q a 0, φ z ≠ 0 := by
  let e := cyclotomicZeroEquiv (k := k) (Q := Q) (a := a)
  let _ : Module k M := Module.compHom M (algebraMap k (CycKLR k Q a 0))
  have hsmul : ∀ (c : k) (m : M), c • m = algebraMap k (CycKLR k Q a 0) c • m := fun _ _ => rfl
  have halg : ∀ r : CycKLR k Q a 0, algebraMap k (CycKLR k Q a 0) (e r) = r := fun r => by
    have := e.symm.commutes (e r)
    simpa using this.symm
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hz
  have hinj : Function.Injective (algebraMap k (CycKLR k Q a 0)) := by
    intro x y hxy
    simpa using congrArg e hxy
  refine ⟨{ toFun := fun m => algebraMap k (CycKLR k Q a 0) (φ m)
            map_add' := fun m n => by simp
            map_smul' := fun r m => ?_ }, ?_⟩
  · change algebraMap k (CycKLR k Q a 0) (φ (r • m)) = r * algebraMap k (CycKLR k Q a 0) (φ m)
    conv_lhs => rw [← halg r, ← hsmul, map_smul, smul_eq_mul, map_mul, halg]
  · intro h
    exact hφ (hinj (h.trans (map_zero _).symm))

/-- A morphism of weight spaces concentrated on the empty block. -/
def atZeroBlk {Z Z' : (weightSpace.{u, v, w} Q a RD Λ μ₀).carrier}
    (f : Z ⟨0, rfl⟩ ⟶ Z' ⟨0, rfl⟩) : Z ⟶ Z' := fun β =>
  if h : β = ⟨0, rfl⟩ then by subst h; exact f else 0

theorem atZeroBlk_zero {Z Z' : (weightSpace.{u, v, w} Q a RD Λ μ₀).carrier}
    (f : Z ⟨0, rfl⟩ ⟶ Z' ⟨0, rfl⟩) : (atZeroBlk f : Z ⟶ Z') ⟨0, rfl⟩ = f := by
  simp only [atZeroBlk, ↓reduceDIte]

/-- A nonzero morphism out of the vacuum is nonzero on its generator. -/
theorem exists_vac_ne {Z : (weightSpace.{u, v, w} Q a RD Λ μ₀).carrier} {f : (𝕍) ⟶ Z}
    (hf : f ≠ 0) : (f ⟨0, rfl⟩).hom vac₀ ≠ 0 := by
  intro h0
  apply hf
  funext β
  by_cases hβ : β.1 = 0
  · obtain rfl := eq_zeroBlk hβ
    ext x
    obtain ⟨z, rfl⟩ := vac_cyclic x
    rw [map_smul, h0, smul_zero]
    rfl
  · exact (vac_isZero β hβ).eq_of_src _ _

/-- **Left separation at the vacuum**: a nonzero morphism `𝕍 ⟶ Z` has a nonzero composite with
some morphism `Z ⟶ 𝕍`. -/
theorem vac_sep_left (Z : (weightSpace.{u, v, w} Q a RD Λ μ₀).carrier) (f : (𝕍) ⟶ Z)
    (hf : f ≠ 0) : ∃ π : Z ⟶ (𝕍), f ≫ π ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_cycZero_functional (k := k) (Q := Q) (a := a) (exists_vac_ne hf)
  let π₀ : Z ⟨0, rfl⟩ ⟶ (𝕍) ⟨0, rfl⟩ := ModuleCat.ofHom
    { toFun := fun m _ => ULift.up (φ m)
      map_add' := fun m n => funext fun _ => ULift.ext _ _ (map_add φ m n)
      map_smul' := fun r m => funext fun _ => ULift.ext _ _ (map_smul φ r m) }
  refine ⟨atZeroBlk π₀, fun h => hφ ?_⟩
  have h1 : (f ≫ atZeroBlk π₀) ⟨0, rfl⟩ = f ⟨0, rfl⟩ ≫ π₀ := by
    change f ⟨0, rfl⟩ ≫ atZeroBlk π₀ ⟨0, rfl⟩ = _
    rw [atZeroBlk_zero]
  exact congrArg (fun g : (𝕍) ⟨0, rfl⟩ ⟶ (𝕍) ⟨0, rfl⟩ => ((g.hom vac₀) ⟨rfl⟩).down)
    (h1.symm.trans (congrArg (fun F : (𝕍) ⟶ (𝕍) => F ⟨0, rfl⟩) h))

/-- **Right separation at the vacuum**: a nonzero morphism `Z ⟶ 𝕍` has a nonzero composite with
some morphism `𝕍 ⟶ Z`. -/
theorem vac_sep_right (Z : (weightSpace.{u, v, w} Q a RD Λ μ₀).carrier) (g : Z ⟶ (𝕍))
    (hg : g ≠ 0) : ∃ ι : (𝕍) ⟶ Z, ι ≫ g ≠ 0 := by
  have : g ⟨0, rfl⟩ ≠ 0 := by
    intro h0
    apply hg
    funext β
    by_cases hβ : β.1 = 0
    · obtain rfl := eq_zeroBlk hβ
      exact h0
    · exact (vac_isZero β hβ).eq_of_tgt _ _
  obtain ⟨z, hz⟩ : ∃ z, (g ⟨0, rfl⟩).hom z ≠ 0 := by
    by_contra h
    push Not at h
    exact this (ModuleCat.hom_ext (LinearMap.ext h))
  let ι₀ : (𝕍) ⟨0, rfl⟩ ⟶ Z ⟨0, rfl⟩ := ModuleCat.ofHom
    { toFun := fun p => (p ⟨rfl⟩).down • z
      map_add' := fun p q => add_smul _ _ _
      map_smul' := fun r p => mul_smul _ _ _ }
  refine ⟨atZeroBlk ι₀, fun h => hz ?_⟩
  have h1 : (atZeroBlk ι₀ ≫ g) ⟨0, rfl⟩ = ι₀ ≫ g ⟨0, rfl⟩ := by
    change atZeroBlk ι₀ ⟨0, rfl⟩ ≫ g ⟨0, rfl⟩ = _
    rw [atZeroBlk_zero]
  have h2 := congrArg (fun F : (𝕍) ⟨0, rfl⟩ ⟶ (𝕍) ⟨0, rfl⟩ => F.hom vac₀)
    (h1.symm.trans (congrArg (fun F : (𝕍) ⟶ (𝕍) => F ⟨0, rfl⟩) h))
  change (g ⟨0, rfl⟩).hom ((1 : CycKLR k Q a 0) • z) = 0 at h2
  rwa [one_smul] at h2
/-! ### Morphisms out of the words at the vacuum -/

variable {ν : Multiset I}

/-- The word of `t` applied to the vacuum: the cyclotomic module `R^Λ(ν) e(rev t)`. -/
abbrev wObj (t : Seq ν) : ((S).obj (wtop RD μ₀ ν)).carrier :=
  (RouqData.wordCell (S).toRouqData μ₀ t).obj.obj (familyObj hQ hlead ha hΛ hdeg (𝕍))

/-- The generator of the word of `t` applied to the vacuum. -/
abbrev wg (t : Seq ν) :=
  wgen hQ hlead ha hΛ hdeg (𝕍) rfl (vac₀.{u, v, w} (Q := Q) (a := a) (RD := RD) (Λ := Λ)) t

/-- **A morphism out of a word at the vacuum is determined by its value on the generator.** -/
theorem eq_of_wgen {t : Seq ν} {Z : ((S).obj (wtop RD μ₀ ν)).carrier}
    {f g : wObj.{u, v, w} hQ hlead ha hΛ hdeg t ⟶ Z}
    (h : (f (topBlk rfl)).hom (wg.{u, v, w} hQ hlead ha hΛ hdeg t) =
      (g (topBlk rfl)).hom (wg.{u, v, w} hQ hlead ha hΛ hdeg t)) : f = g := by
  funext δ
  by_cases hδ : δ.1 = ν
  · obtain rfl : δ = topBlk (μ := μ₀) rfl := Subtype.ext hδ
    ext x
    obtain ⟨z, rfl⟩ := exists_eq_smul_vgen hQ hlead ha hΛ hdeg (𝕍) rfl vac₀ vac_cyclic _ _
      (wValid_wordL μ₀ t) _ (topBlk_eq rfl t) x
    exact ((f _).hom.map_smul z _).trans ((congrArg (z • ·) h).trans ((g _).hom.map_smul z _).symm)
  · exact (isZero_wcell_of_ne hQ hlead ha hΛ hdeg (𝕍) (fun β hβ => vac_isZero β hβ) _ _
      (wValid_wordL μ₀ t) δ (by rw [← topBlk_eq (μ := μ₀) rfl t]; exact hδ)).eq_of_src _ _

/-! ### The action of `R(ν)` on the words at the vacuum -/

/-- The matrix of morphisms between the words at the vacuum by which `r ∈ R(ν)` acts. -/
def vacAct (r : KLRAlgebra k Q ν) : Diagram.MatEnd (wObj.{u, v, w} hQ hlead ha hΛ hdeg (ν := ν)) :=
  fun t s => ((RouqFamily.klrAct (cyclotomicFamily_upKLR hQ hlead ha RD Λ hΛ hdeg) μ₀ r) t s).hom.app
    (familyObj hQ hlead ha hΛ hdeg (𝕍))

/-- Evaluation of 2-morphisms at the vacuum, as an additive map. -/
def evVac {F G : (S).obj μ₀ ⟶ (S).obj (wtop RD μ₀ ν)} :
    (F ⟶ G) →+ (F.obj.obj (familyObj hQ hlead ha hΛ hdeg (𝕍)) ⟶
      G.obj.obj (familyObj hQ hlead ha hΛ hdeg (𝕍))) :=
  AddMonoidHom.mk' (fun f => f.hom.app _) fun _ _ => rfl

theorem vacAct_mul (r r' : KLRAlgebra k Q ν) :
    vacAct.{u, v, w} hQ hlead ha hΛ hdeg (r * r') =
      vacAct.{u, v, w} hQ hlead ha hΛ hdeg r * vacAct.{u, v, w} hQ hlead ha hΛ hdeg r' := by
  ext t s
  simp only [vacAct, map_mul, Diagram.MatEnd.mul_apply]
  exact map_sum (evVac.{u, v, w} hQ hlead ha hΛ hdeg) _ _

theorem vacAct_add (r r' : KLRAlgebra k Q ν) :
    vacAct.{u, v, w} hQ hlead ha hΛ hdeg (r + r') =
      vacAct.{u, v, w} hQ hlead ha hΛ hdeg r + vacAct.{u, v, w} hQ hlead ha hΛ hdeg r' := by
  ext t s
  simp only [vacAct, map_add, Diagram.MatEnd.add_apply]
  rfl

theorem vacAct_smul (c : k) (r : KLRAlgebra k Q ν) :
    vacAct.{u, v, w} hQ hlead ha hΛ hdeg (c • r) = c • vacAct.{u, v, w} hQ hlead ha hΛ hdeg r := by
  ext t s
  simp only [vacAct, map_smul, Diagram.MatEnd.smul_apply]
  rfl

theorem vacAct_sub (r r' : KLRAlgebra k Q ν) :
    vacAct.{u, v, w} hQ hlead ha hΛ hdeg (r - r') =
      vacAct.{u, v, w} hQ hlead ha hΛ hdeg r - vacAct.{u, v, w} hQ hlead ha hΛ hdeg r' := by
  rw [sub_eq_add_neg, vacAct_add, ← neg_one_smul k r', vacAct_smul, neg_one_smul,
    ← sub_eq_add_neg]

theorem vacAct_wgen (r : KLRAlgebra k Q ν) (t s : Seq ν) :
    ((vacAct.{u, v, w} hQ hlead ha hΛ hdeg r t s) (topBlk rfl)).hom (wg.{u, v, w} hQ hlead ha hΛ hdeg t) =
      CycKLR.mk k Q a ν (hflip (sigma hQ (e s * r * e t))) • wg.{u, v, w} hQ hlead ha hΛ hdeg s :=
  klrAct_wgen hQ hlead ha hΛ hdeg (𝕍) rfl vac₀ r t s

/-- **The kernel of the action at the vacuum.** `r ∈ R(ν)` acts by zero on the words at the
vacuum exactly when `hflip (σ r)` vanishes in `R^Λ(ν)`. -/
theorem vacAct_eq_zero_iff (r : KLRAlgebra k Q ν) :
    vacAct.{u, v, w} hQ hlead ha hΛ hdeg r = 0 ↔ CycKLR.mk k Q a ν (hflip (sigma hQ r)) = 0 := by
  constructor
  · intro hr
    have hst : ∀ t s : Seq ν, CycKLR.mk k Q a ν (hflip (sigma hQ (e s * r * e t))) = 0 := by
      intro t s
      refine (wcoord_klrAct_wgen hQ hlead ha hΛ hdeg (𝕍) rfl vac₀ (Ψ₀ := vacCoord) rfl r t
        s).symm.trans ?_
      have h0 : vacAct.{u, v, w} hQ hlead ha hΛ hdeg r t s = 0 := by rw [hr]; rfl
      change wcoord hQ hlead ha hΛ hdeg (𝕍) rfl vacCoord s
        (((vacAct.{u, v, w} hQ hlead ha hΛ hdeg r t s) (topBlk rfl)).hom
          (wg.{u, v, w} hQ hlead ha hΛ hdeg t)) = 0
      rw [h0]
      exact map_zero _
    have hsum : r = ∑ s : Seq ν, ∑ t : Seq ν, e s * r * e t := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sum_e, one_mul, mul_one]
    rw [hsum, map_sum, hflip_sum, map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [map_sum, hflip_sum, map_sum]
    exact Finset.sum_eq_zero fun t _ => hst t s
  · intro hr
    ext t s
    refine eq_of_wgen hQ hlead ha hΛ hdeg ?_
    rw [vacAct_wgen, map_mul, map_mul, hflip_mul, hflip_mul, map_mul, map_mul, hr]
    simp only [zero_mul, mul_zero, zero_smul]
    rfl

/-! ### The cyclotomic algebra as the endomorphisms of the words at the vacuum -/

/-- The matrix of morphisms by which `c ∈ R^Λ(ν)` acts on the words at the vacuum, read through
the anti-involution `σ ∘ hflip`. -/
def cycAct (c : CycKLR k Q a ν) : Diagram.MatEnd (wObj.{u, v, w} hQ hlead ha hΛ hdeg (ν := ν)) :=
  vacAct.{u, v, w} hQ hlead ha hΛ hdeg (sigma hQ (hflip (Function.surjInv (CycKLR.mk_surjective (k := k) (Q := Q) (a := a) (ν := ν)) c)))

theorem cycAct_mk (x : KLRAlgebra k Q ν) :
    cycAct.{u, v, w} hQ hlead ha hΛ hdeg (CycKLR.mk k Q a ν x) =
      vacAct.{u, v, w} hQ hlead ha hΛ hdeg (sigma hQ (hflip x)) := by
  rw [cycAct, ← sub_eq_zero, ← vacAct_sub, ← map_sub, ← hflip_sub, vacAct_eq_zero_iff,
    sigma_sigma, hflip_hflip, map_sub,
    Function.surjInv_eq (CycKLR.mk_surjective (k := k) (Q := Q) (a := a) (ν := ν)), sub_self]

theorem cycAct_add (c d : CycKLR k Q a ν) :
    cycAct.{u, v, w} hQ hlead ha hΛ hdeg (c + d) =
      cycAct.{u, v, w} hQ hlead ha hΛ hdeg c + cycAct.{u, v, w} hQ hlead ha hΛ hdeg d := by
  obtain ⟨x, rfl⟩ := CycKLR.mk_surjective c
  obtain ⟨y, rfl⟩ := CycKLR.mk_surjective d
  rw [← map_add, cycAct_mk, cycAct_mk, cycAct_mk, hflip_add, map_add, vacAct_add]

theorem cycAct_smul (r : k) (c : CycKLR k Q a ν) :
    cycAct.{u, v, w} hQ hlead ha hΛ hdeg (r • c) = r • cycAct.{u, v, w} hQ hlead ha hΛ hdeg c := by
  obtain ⟨x, rfl⟩ := CycKLR.mk_surjective c
  rw [← map_smul, cycAct_mk, cycAct_mk, hflip_smul, map_smul, vacAct_smul]

/-- The action of `R^Λ(ν)` on the words at the vacuum is anti-multiplicative. -/
theorem cycAct_mul (c d : CycKLR k Q a ν) :
    cycAct.{u, v, w} hQ hlead ha hΛ hdeg (c * d) =
      cycAct.{u, v, w} hQ hlead ha hΛ hdeg d * cycAct.{u, v, w} hQ hlead ha hΛ hdeg c := by
  obtain ⟨x, rfl⟩ := CycKLR.mk_surjective c
  obtain ⟨y, rfl⟩ := CycKLR.mk_surjective d
  rw [← map_mul, cycAct_mk, cycAct_mk, cycAct_mk, hflip_mul, map_mul, vacAct_mul]

theorem cycAct_injective : Function.Injective (cycAct.{u, v, w} hQ hlead ha hΛ hdeg (ν := ν)) := by
  intro c d h
  obtain ⟨x, rfl⟩ := CycKLR.mk_surjective c
  obtain ⟨y, rfl⟩ := CycKLR.mk_surjective d
  rw [cycAct_mk, cycAct_mk, ← sub_eq_zero, ← vacAct_sub, ← map_sub, ← hflip_sub,
    vacAct_eq_zero_iff, sigma_sigma, hflip_hflip, map_sub, sub_eq_zero] at h
  exact h

theorem cycAct_wgen (c : CycKLR k Q a ν) (t s : Seq ν) :
    ((cycAct.{u, v, w} hQ hlead ha hΛ hdeg c t s) (topBlk rfl)).hom (wg.{u, v, w} hQ hlead ha hΛ hdeg t) =
      (CycKLR.mk k Q a ν (e t.rev) * c * CycKLR.mk k Q a ν (e s.rev)) •
        wg.{u, v, w} hQ hlead ha hΛ hdeg s := by
  obtain ⟨x, rfl⟩ := CycKLR.mk_surjective c
  rw [cycAct_mk, vacAct_wgen, map_mul, map_mul, hflip_mul, hflip_mul, sigma_sigma, hflip_hflip,
    sigma_e, sigma_e, hflip_e, hflip_e, map_mul, map_mul, mul_assoc]

theorem mk_e_mul_mk_e (t s : Seq ν) :
    CycKLR.mk k Q a ν (e t) * CycKLR.mk k Q a ν (e s) =
      if t = s then CycKLR.mk k Q a ν (e t) else 0 := by
  rw [← map_mul, e_mul_e]
  split_ifs <;> simp

/-- **Every endomorphism of the words at the vacuum comes from `R^Λ(ν)`.** -/
theorem cycAct_surjective : Function.Surjective (cycAct.{u, v, w} hQ hlead ha hΛ hdeg (ν := ν)) := by
  intro M
  have hy : ∀ t s : Seq ν, ∃ y : CycKLR k Q a ν,
      ((M t s) (topBlk rfl)).hom (wg.{u, v, w} hQ hlead ha hΛ hdeg t) = y • wg.{u, v, w} hQ hlead ha hΛ hdeg s :=
    fun t s => exists_eq_smul_vgen hQ hlead ha hΛ hdeg (𝕍) rfl vac₀ vac_cyclic _ _
      (wValid_wordL μ₀ s) _ (topBlk_eq rfl s) _
  choose y hy using hy
  let E : Seq ν → CycKLR k Q a ν := fun t => CycKLR.mk k Q a ν (e t.rev)
  refine ⟨∑ t', ∑ s', E t' * y t' s' * E s', ?_⟩
  ext t s
  refine eq_of_wgen hQ hlead ha hΛ hdeg ?_
  rw [cycAct_wgen, hy]
  have hEE : ∀ t t' : Seq ν, E t * E t' = if t = t' then E t else 0 := fun t t' => by
    simp only [E, mk_e_mul_mk_e, Seq.rev_inj]
  have hterm : ∀ t' s' : Seq ν, E t * (E t' * y t' s' * E s') * E s =
      if t' = t then (if s' = s then E t * y t s * E s else 0) else 0 := fun t' s' => by
    rw [show E t * (E t' * y t' s' * E s') * E s = E t * E t' * y t' s' * (E s' * E s) by
      simp only [mul_assoc], hEE, hEE]
    by_cases h1 : t' = t
    · subst h1
      by_cases h2 : s' = s
      · subst h2
        simp
      · simp [h2]
    · simp [h1, Ne.symm h1]
  have hc : E t * (∑ t', ∑ s', E t' * y t' s' * E s') * E s = E t * y t s * E s := by
    simp only [Finset.mul_sum, Finset.sum_mul, hterm]
    simp
  change (E t * (∑ t', ∑ s', E t' * y t' s' * E s') * E s) • _ = _
  rw [hc, mul_smul, mul_smul, e_smul_wgen, ← hy, ← map_smul, e_smul_wgen]

/-! ### The trace -/

/-- The closing trace on the endomorphisms of the word of `t` at the vacuum, through the
biadjunction of the word with its reversed word of `F`'s (Theorem 3.17). -/
def wordTrace (t : Seq ν) :
    (wObj.{u, v, w} hQ hlead ha hΛ hdeg t ⟶ wObj.{u, v, w} hQ hlead ha hΛ hdeg t) →+
      (familyObj hQ hlead ha hΛ hdeg (𝕍) ⟶ familyObj hQ hlead ha hΛ hdeg (𝕍)) :=
  AmbidextrousTrace.closeTraceIso
    (LinearCat.toAdjunction (RouqFamily.wadj (S) μ₀ (wordL RD μ₀ t) _ (wValid_wordL μ₀ t)))
    (LinearCat.toAdjunction (RouqFamily.wadjL (S) μ₀ (wordL RD μ₀ t) _ (wValid_wordL μ₀ t)))
    _ (Iso.refl _)

theorem wordTrace_smul (t : Seq ν) (c : k) (f : wObj.{u, v, w} hQ hlead ha hΛ hdeg t ⟶ wObj.{u, v, w} hQ hlead ha hΛ hdeg t) :
    wordTrace.{u, v, w} hQ hlead ha hΛ hdeg t (c • f) = c • wordTrace.{u, v, w} hQ hlead ha hΛ hdeg t f :=
  AmbidextrousTrace.closeTraceIso_smul _ _ _ _ c f

theorem wordTrace_nondeg (t : Seq ν) :
    AmbidextrousTrace.IsNondegTrace (familyObj hQ hlead ha hΛ hdeg (𝕍))
      (wObj.{u, v, w} hQ hlead ha hΛ hdeg t) (wordTrace.{u, v, w} hQ hlead ha hΛ hdeg t)
      fun Y => ∃ s, wObj.{u, v, w} hQ hlead ha hΛ hdeg s = Y :=
  AmbidextrousTrace.isNondegTrace_closeTraceIso_of_separating _ _ _ _ _
    (fun _ _ f hf => vac_sep_left _ f hf) (fun _ _ g hg => vac_sep_right _ g hg)

/-- The vacuum endomorphisms are `R^Λ(∅) = k`. -/
def vacScalar (f : familyObj hQ hlead ha hΛ hdeg (𝕍) ⟶ familyObj hQ hlead ha hΛ hdeg (𝕍)) : k :=
  cyclotomicZeroEquiv Q a (vacCoord ((f ⟨0, rfl⟩).hom vac₀))

theorem vacScalar_add (f g : familyObj hQ hlead ha hΛ hdeg (𝕍) ⟶ familyObj hQ hlead ha hΛ hdeg (𝕍)) :
    vacScalar.{u, v, w} hQ hlead ha hΛ hdeg (f + g) =
      vacScalar.{u, v, w} hQ hlead ha hΛ hdeg f + vacScalar.{u, v, w} hQ hlead ha hΛ hdeg g := by
  change cyclotomicZeroEquiv Q a (vacCoord ((f ⟨0, rfl⟩).hom vac₀ + (g ⟨0, rfl⟩).hom vac₀)) = _
  exact (congrArg (cyclotomicZeroEquiv Q a) (vacCoord.map_add _ _)).trans (map_add _ _ _)

theorem vacScalar_smul (c : k)
    (f : familyObj hQ hlead ha hΛ hdeg (𝕍) ⟶ familyObj hQ hlead ha hΛ hdeg (𝕍)) :
    vacScalar.{u, v, w} hQ hlead ha hΛ hdeg (c • f) = c • vacScalar.{u, v, w} hQ hlead ha hΛ hdeg f := by
  change cyclotomicZeroEquiv Q a (vacCoord (algebraMap k (CycKLR k Q a 0) c • (f ⟨0, rfl⟩).hom vac₀)) = _
  exact (congrArg (cyclotomicZeroEquiv Q a) (vacCoord.map_smul _ _)).trans
    ((map_mul (cyclotomicZeroEquiv Q a) _ _).trans
      (congrArg (· * _) ((cyclotomicZeroEquiv Q a).commutes c)))

theorem vacScalar_injective {f : familyObj hQ hlead ha hΛ hdeg (𝕍) ⟶ familyObj hQ hlead ha hΛ hdeg (𝕍)}
    (hf : vacScalar.{u, v, w} hQ hlead ha hΛ hdeg f = 0) : f = 0 := by
  by_contra hne
  apply exists_vac_ne hne
  have h1 : vacCoord ((f ⟨0, rfl⟩).hom vac₀) = 0 :=
    (cyclotomicZeroEquiv Q a).injective (by
      change cyclotomicZeroEquiv Q a _ = _
      rw [map_zero]
      exact hf)
  funext p
  exact ULift.ext _ _ h1

include hQ hlead ha hΛ hdeg in
/-- **Webster, arXiv:1309.3796v2, Theorem 3.18.** Over a field, the cyclotomic KLR algebra
`R^Λ(ν)` of the cyclotomic categorical action (Theorem 3.17) is Frobenius: it carries a
`k`-linear trace `tr` whose pairing `(x, y) ↦ tr (x y)` is nondegenerate on both sides. The
trace closes the strands of each word `E_t` applied to the vacuum `R^Λ(∅) = k` with the
biadjunction of `E_t` and the reversed word of `F`'s. -/
theorem cyclotomic_trace_nondegenerate (ν : Multiset I) :
    ∃ tr : CycKLR k Q a ν →ₗ[k] k,
      (∀ x, x ≠ 0 → ∃ y, tr (x * y) ≠ 0) ∧ ∀ y, y ≠ 0 → ∃ x, tr (x * y) ≠ 0 := by
  let τ := fun t : Seq ν => wordTrace.{u, v, 0} hQ hlead ha hΛ hdeg t
  obtain ⟨h₁, h₂⟩ := Diagram.MatEnd.trace_nondegenerate τ (wordTrace_nondeg hQ hlead ha hΛ hdeg)
  let T := Diagram.MatEnd.trace τ
  let tr : CycKLR k Q a ν →ₗ[k] k :=
    { toFun := fun c => vacScalar.{u, v, 0} hQ hlead ha hΛ hdeg (T (cycAct.{u, v, 0} hQ hlead ha hΛ hdeg c))
      map_add' := fun c d => by
        rw [cycAct_add, map_add, vacScalar_add]
      map_smul' := fun r c => by
        rw [cycAct_smul, Diagram.MatEnd.trace_smul τ (wordTrace_smul hQ hlead ha hΛ hdeg),
          vacScalar_smul]
        rfl }
  have htr : ∀ x y, tr (x * y) = vacScalar.{u, v, 0} hQ hlead ha hΛ hdeg
      (T (cycAct.{u, v, 0} hQ hlead ha hΛ hdeg y * cycAct.{u, v, 0} hQ hlead ha hΛ hdeg x)) := fun x y => by
    change vacScalar.{u, v, 0} hQ hlead ha hΛ hdeg (T (cycAct.{u, v, 0} hQ hlead ha hΛ hdeg (x * y))) = _
    rw [cycAct_mul]
  have hne : ∀ x : CycKLR k Q a ν, x ≠ 0 → cycAct.{u, v, 0} hQ hlead ha hΛ hdeg x ≠ 0 := fun x hx h0 =>
    hx (cycAct_injective hQ hlead ha hΛ hdeg (h0.trans (by
      simpa using (cycAct_smul hQ hlead ha hΛ hdeg (0 : k) (0 : CycKLR k Q a ν)).symm)))
  refine ⟨tr, fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨M, hM⟩ := h₂ _ (hne x hx)
    obtain ⟨y, rfl⟩ := cycAct_surjective hQ hlead ha hΛ hdeg M
    exact ⟨y, fun h => hM (vacScalar_injective hQ hlead ha hΛ hdeg ((htr x y).symm.trans h))⟩
  · obtain ⟨N, hN⟩ := h₁ _ (hne y hy)
    obtain ⟨x, rfl⟩ := cycAct_surjective hQ hlead ha hΛ hdeg N
    exact ⟨x, fun h => hN (vacScalar_injective hQ hlead ha hΛ hdeg ((htr x y).symm.trans h))⟩

end

/-- **Webster, arXiv:1309.3796v2, Theorem 3.18**, in Webster's setting: for Rouquier's
homogeneous parameters `Q` (arXiv:0812.5023v1, §3.2.3) over a field and a cyclotomic quotient
of weight `Λ` (monic `a i` of degree `⟨i, Λ⟩`), the cyclotomic KLR algebra `R^Λ(ν)` carries a
`k`-linear trace whose pairing `(x, y) ↦ tr (x y)` is nondegenerate on both sides. -/
theorem _root_.Categorification.KLR.IsRouquierQ.cyclotomic_frobenius
    {I : Type u} [DecidableEq I] {k : Type v} [Field k]
    {C : QuantumGroup.CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
    {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : QuantumGroup.UDot.WeightDatum C X Y)
    (Λ : X) {a : I → Polynomial k} (ha : ∀ j, (a j).Monic)
    (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ) (ν : Multiset I) :
    ∃ tr : CycKLR k Q a ν →ₗ[k] k,
      (∀ x, x ≠ 0 → ∃ y, tr (x * y) ≠ 0) ∧ ∀ y, y ≠ 0 → ∃ x, tr (x * y) ≠ 0 :=
  cyclotomic_trace_nondegenerate.{u, v, u₁} hQ.klrSymm hQ.polyInY_leading ha hΛ
    (fun i j hji => hQ.polyInY_degree_pair RD i j hji) ν

end Categorification.KLR.CyclotomicAction
