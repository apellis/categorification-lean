/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ModuleTowerK0
import Categorification.Sl2Categorification.WeakCategorification

/-!
# Weak `𝔰𝔩₂`-categorifications on module towers

Let `A 0, A 1, …` be a tower of noetherian and artinian rings vanishing from some level on, and
let `E`, `F` be biadjoint endofunctors of the abelian category `FGTower A` that lower and raise
the level by one. If, level by level, the composition factors of `EF X` and `FE X` differ by
`w n` copies of those of `X`, for integers `w n` decreasing by two from level to level, then
`(FGTower A, E, F)` is a weak `𝔰𝔩₂`-categorification in the sense of Chuang–Rouquier
(arXiv:math/0407205v2, §5.1.1), with `[E]`, `[F]` the classes of the exact functors and the
simple objects at level `n` of weight `w n` (`ModuleTower.weakSl2`).

This is the form in which Webster's `Eᵢ`, `Fᵢ` on the modules along an `i`-string of tensor
product algebras (arXiv:1309.3796v2, §5) give a weak `𝔰𝔩₂`-categorification.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.ModuleTower

open CategoryTheory Limits Sl2

universe u

variable {A : ℕ → Type u} [∀ m, Ring (A m)] [∀ m, IsNoetherianRing (A m)]
  [∀ m, IsArtinianRing (A m)] {N : ℕ} (hN : ∀ m, N ≤ m → Subsingleton (A m))

omit [∀ m, IsNoetherianRing (A m)] [∀ m, IsArtinianRing (A m)] in
include hN in
lemma clsN_apply (X : FGTower A) (n : ℕ) (c : Module.SimpleClass.{u, u} (A n)) :
    clsN A N X ⟨n, c⟩ = Module.compositionFactors (A n) (X.obj n) c := by
  rw [clsN, Finsupp.finsetSum_apply]
  by_cases hn : n < N
  · rw [Finset.sum_eq_single n]
    · exact Finsupp.mapDomain_apply_of_injective
        (sigma_mk_injective (β := fun m => Module.SimpleClass.{u, u} (A m)) (i := n)) _ c
    · intro m _ hm
      refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨d, hd⟩
      exact hm (congrArg Sigma.fst hd)
    · intro h
      exact absurd (Finset.mem_range.mpr hn) h
  · rw [Finset.sum_eq_zero]
    · have : Subsingleton (A n) := hN n (not_lt.mp hn)
      have : Subsingleton (X.obj n) := Module.subsingleton (A n) _
      rw [Module.compositionFactors_of_subsingleton]
      rfl
    · intro m hm
      refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨d, hd⟩
      have := congrArg Sigma.fst hd
      simp only at this
      subst this
      exact hn (Finset.mem_range.mp hm)

include hN in
lemma k0Data_cls_apply (X : FGTower A) (n : ℕ) (c : Module.SimpleClass.{u, u} (A n)) :
    (k0Data A hN).cls X ⟨n, c⟩ = (Module.compositionFactors (A n) (X.obj n) c : ℚ) := by
  simp [k0Data, clsN_apply hN]

variable (A) in
/-- The diagonal operator multiplying the classes at level `n` by `w n`. -/
def diagOp (w : ℕ → ℤ) : Module.End ℚ (K0Index A →₀ ℚ) :=
  Finsupp.lsum ℚ fun j => ((w j.1 : ℚ)) • Finsupp.lsingle j

omit [∀ m, IsNoetherianRing (A m)] [∀ m, IsArtinianRing (A m)] in
lemma diagOp_apply (w : ℕ → ℤ) (v : K0Index A →₀ ℚ) (j : K0Index A) :
    diagOp A w v j = (w j.1 : ℚ) * v j := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' => simp [hv, hv', mul_add]
  | single k a =>
    simp only [diagOp, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply,
      Finsupp.smul_apply, smul_eq_mul]
    by_cases h : k = j
    · subst h; rfl
    · rw [Finsupp.single_eq_of_ne (Ne.symm h), mul_zero, mul_zero]

/-- An object concentrated at level `p`. -/
def IsConcentrated (X : FGTower A) (p : ℕ) : Prop := ∀ n, n ≠ p → IsZero (X.obj n)

include hN in
lemma diagOp_cls_of_isConcentrated (w : ℕ → ℤ) {X : FGTower A} {p : ℕ}
    (hX : IsConcentrated X p) :
    diagOp A w ((k0Data A hN).cls X) = (w p : ℚ) • (k0Data A hN).cls X := by
  ext ⟨n, c⟩
  rw [diagOp_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases hn : n = p
  · subst hn; rfl
  · have : Subsingleton (X.obj n) := ModuleCat.subsingleton_of_isZero (hX n hn)
    rw [k0Data_cls_apply hN, Module.compositionFactors_of_subsingleton]
    simp

omit [∀ m, IsNoetherianRing (A m)] [∀ m, IsArtinianRing (A m)] in
lemma isConcentrated_simpleObj (j : K0Index A) : IsConcentrated (simpleObj A j) j.1 :=
  fun _ hn => isZero_singleObj _ hn

variable (E F : FGTower A ⥤ FGTower A) (adjEF : E ⊣ F) (adjFE : F ⊣ E)
  (w : ℕ → ℤ) (hw : ∀ n, w (n + 1) = w n - 2)
  (hE : ∀ (X : FGTower A) n, IsZero (X.obj (n + 1)) → IsZero ((E.obj X).obj n))
  (hF0 : ∀ X : FGTower A, IsZero ((F.obj X).obj 0))
  (hF : ∀ (X : FGTower A) n, IsZero (X.obj n) → IsZero ((F.obj X).obj (n + 1)))
  (hEF : ∀ (X : FGTower A) n (c : Module.SimpleClass.{u, u} (A n)),
    (Module.compositionFactors (A n) ((E.obj (F.obj X)).obj n) c : ℤ) -
      Module.compositionFactors (A n) ((F.obj (E.obj X)).obj n) c =
    w n * Module.compositionFactors (A n) (X.obj n) c)

omit [∀ m, IsNoetherianRing (A m)] [∀ m, IsArtinianRing (A m)] in
include hE in
lemma isConcentrated_E {X : FGTower A} {p : ℕ} (hX : IsConcentrated X (p + 1)) :
    IsConcentrated (E.obj X) p :=
  fun n hn => hE X n (hX (n + 1) (by omega))

omit [∀ m, IsNoetherianRing (A m)] [∀ m, IsArtinianRing (A m)] in
include hE in
lemma isZero_E {X : FGTower A} (hX : IsConcentrated X 0) : IsZero (E.obj X) :=
  FGTower.isZero_iff.mpr fun n => hE X n (hX (n + 1) (by omega))

omit [∀ m, IsNoetherianRing (A m)] [∀ m, IsArtinianRing (A m)] in
include hF0 hF in
lemma isConcentrated_F {X : FGTower A} {p : ℕ} (hX : IsConcentrated X p) :
    IsConcentrated (F.obj X) (p + 1) := by
  intro n hn
  cases n with
  | zero => exact hF0 X
  | succ n => exact hF X n (hX n (by omega))

include hN adjEF adjFE in
lemma cls_E (X : FGTower A) :
    (k0Data A hN).cls (E.obj X) = (k0Data A hN).clsMap E ((k0Data A hN).cls X) := by
  have : ∀ X : FGTower A, IsArtinianObject X := isArtinianObject hN
  have : E.IsLeftAdjoint := ⟨F, ⟨adjEF⟩⟩
  have : PreservesLimitsOfSize E := adjFE.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize E := adjEF.leftAdjoint_preservesColimits
  exact (k0Data A hN).cls_map_clsMap E X

include hN adjEF adjFE in
lemma cls_F (X : FGTower A) :
    (k0Data A hN).cls (F.obj X) = (k0Data A hN).clsMap F ((k0Data A hN).cls X) :=
  cls_E hN F E adjFE adjEF X

include hEF adjEF adjFE in
lemma hOp_cls (X : FGTower A) :
    hOp ((k0Data A hN).clsMap E) ((k0Data A hN).clsMap F) ((k0Data A hN).cls X) =
      diagOp A w ((k0Data A hN).cls X) := by
  simp only [hOp, LinearMap.sub_apply, Module.End.mul_apply]
  rw [← cls_F hN E F adjEF adjFE, ← cls_E hN E F adjEF adjFE, ← cls_E hN E F adjEF adjFE,
    ← cls_F hN E F adjEF adjFE]
  ext ⟨n, c⟩
  rw [Finsupp.sub_apply, diagOp_apply, k0Data_cls_apply hN, k0Data_cls_apply hN,
    k0Data_cls_apply hN]
  exact_mod_cast hEF X n c

lemma k0Data_cls_simpleObj (j : K0Index A) :
    (k0Data A hN).cls (simpleObj A j) = (k0Data A hN).B j :=
  ((k0Data A hN).cls_simple _ (simple_simpleObj j)).trans
    (congrArg (k0Data A hN).B (simpleIdx_simpleObj j))

include hEF adjEF adjFE in
lemma hOp_eq_diagOp :
    hOp ((k0Data A hN).clsMap E) ((k0Data A hN).clsMap F) = diagOp A w := by
  refine (k0Data A hN).B.ext fun j => ?_
  rw [← k0Data_cls_simpleObj hN, hOp_cls hN E F adjEF adjFE w hEF]

include hw hE hF0 hF hEF adjEF adjFE in
lemma isSl2Pair : IsSl2Pair ((k0Data A hN).clsMap E) ((k0Data A hN).clsMap F) := by
  constructor <;> rw [hOp_eq_diagOp hN E F adjEF adjFE w hEF]
  · refine (k0Data A hN).B.ext fun j => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply]
    rw [← k0Data_cls_simpleObj hN, diagOp_cls_of_isConcentrated hN w (isConcentrated_simpleObj j),
      map_smul, ← cls_E hN E F adjEF adjFE]
    obtain ⟨p, hp⟩ | hp : (∃ p, j.1 = p + 1) ∨ j.1 = 0 := by
      rcases j.1 with _ | p
      · exact Or.inr rfl
      · exact Or.inl ⟨p, rfl⟩
    · have hc : IsConcentrated (E.obj (simpleObj A j)) p :=
        isConcentrated_E E hE (hp ▸ isConcentrated_simpleObj j)
      rw [diagOp_cls_of_isConcentrated hN w hc, hp, hw]
      module
    · have hz := isZero_E E hE (hp ▸ isConcentrated_simpleObj j)
      rw [(k0Data A hN).cls_zero_obj hz]
      simp
  · refine (k0Data A hN).B.ext fun j => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.neg_apply]
    rw [← k0Data_cls_simpleObj hN, diagOp_cls_of_isConcentrated hN w (isConcentrated_simpleObj j),
      map_smul, ← cls_F hN E F adjEF adjFE,
      diagOp_cls_of_isConcentrated hN w (isConcentrated_F F hF0 hF (isConcentrated_simpleObj j)),
      hw]
    module

include hw hE hF0 hF hEF in
/-- **A weak `𝔰𝔩₂`-categorification on a module tower** (Chuang–Rouquier, arXiv:math/0407205v2,
§5.1.1). For a tower of noetherian and artinian rings vanishing from level `N` on, biadjoint
endofunctors `E`, `F` of `FGTower A` lowering and raising the level by one, and integers `w n`
decreasing by two with `[EF X] - [FE X] = w n [X]` on composition factors at each level `n`, the
classes of `E` and `F` form an `𝔰𝔩₂`-action on the Grothendieck group in which the simple objects
at level `n` have weight `w n`. -/
def weakSl2 : WeakSl2 (FGTower A) (K0Index A) (K0Index A →₀ ℚ) where
  toK0Data := k0Data A hN
  E := E
  F := F
  adjEF := adjEF
  adjFE := adjFE
  e := (k0Data A hN).clsMap E
  f := (k0Data A hN).clsMap F
  cls_E := cls_E hN E F adjEF adjFE
  cls_F := cls_F hN E F adjEF adjFE
  sl2 := isSl2Pair hN E F adjEF adjFE w hw hE hF0 hF hEF
  wt j := w j.1
  wt_eq j := by
    rw [hOp_eq_diagOp hN E F adjEF adjFE w hEF, ← k0Data_cls_simpleObj hN,
      diagOp_cls_of_isConcentrated hN w (isConcentrated_simpleObj j)]
  locFin v := by
    have := finite_k0Index hN
    exact ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ => Submodule.mem_top,
      fun _ _ => Submodule.mem_top⟩

end Categorification.ModuleTower
