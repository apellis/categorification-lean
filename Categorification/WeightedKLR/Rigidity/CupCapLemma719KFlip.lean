/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeCoe
import Categorification.WeightedKLR.RedStrands.BlackInductionExact
import Categorification.Algebra.BalancedTensorRightExact

/-!
# The coevaluation functor on left modules, through horizontal reflection

Webster, arXiv:1309.3796v3, Definition 7.18 and Lemma 7.19 (K). The coevaluation functor
`𝕂 = - ⊗_{T^λ} K^{λ⁺}_λ` acts on right `T^λ`-modules, while the standardization functors
(`singStandard`, `plusStagedStd`) produce left modules. Through the horizontal reflection
`σ : T ≃+* Tᵐᵒᵖ` (`tensorFlipRingEquiv`) the bimodule `K^{λ⁺}_λ` becomes a
`T^{λ⁺}`–`T^λ` bimodule (`ReflectedCap`), and `𝕂` becomes the functor
`M ↦ K^σ ⊗_{T^λ} M` on left modules (`CoeTensor`). This is the reading of Lemma 7.19 (K) used
here: a convention change, with the reflection taken over a field as in Webster's paper.

Since `K^{λ⁺}_λ` is projective as a left `T^λ`-module (`projective_midCapBimodule`), its
reflection is projective as a right `T^λ`-module (`projective_reflectedCap`), so `CoeTensor`
is exact (`coeTensorMap_exact`).

## Main definitions

* `Stendhal.CupCap.ReflectedCap`: `K^{λ⁺}_λ` with both actions reflected.
* `Stendhal.CupCap.CoeTensor`, `coeTensorMap`: the reflected coevaluation functor on left
  modules.

## Main results

* `BalancedTensor.mapRight_injective_of_projective`, `BalancedTensor.mapRight_exact_of_projective`:
  `M ⊗_A -` is exact when `M` is a projective right `A`-module.
* `Stendhal.CupCap.projective_reflectedCap`, `coeTensorMap_injective`, `coeTensorMap_exact`.

Route hypotheses: those of `projective_midCapBimodule` (symmetric `Q`, invertible cup scalars,
the pull-off identities, and finitely generated projective pieces `L e(t)`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification

open MulOpposite

namespace BalancedTensor

/-! ### Exactness of `M ⊗_A -` for projective `M` -/

section Projective

variable {B : Type*} [Ring B] {A : Type*} [Ring A]
  {M : Type*} [AddCommGroup M] [Module B M] [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M]
  {N N' N'' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
  [AddCommGroup N''] [Module A N'']

variable (s : M →ₗ[Aᵐᵒᵖ] (M →₀ Aᵐᵒᵖ))

/-- The coordinates `(m, n) ↦ (y ↦ s(m)_y n)` attached to `s`. -/
def projCoordFun (m : M) (n : N) : M →₀ N :=
  (s m).mapRange (fun r => r.unop • n) (by simp)

omit [Module B M] [SMulCommClass B Aᵐᵒᵖ M] in
theorem projCoordFun_apply (m : M) (n : N) (y : M) :
    projCoordFun s m n y = (s m y).unop • n :=
  Finsupp.mapRange_apply (hf := by simp)

omit [Module B M] [SMulCommClass B Aᵐᵒᵖ M] in
/-- The coordinates as a biadditive map. -/
def projCoordBil : M →ₗ[ℤ] N →ₗ[ℤ] (M →₀ N) :=
  LinearMap.mk₂ ℤ (projCoordFun s)
    (fun m m' n => by ext y; simp [projCoordFun_apply, add_smul])
    (fun c m n => by
      ext y
      rw [Finsupp.smul_apply, projCoordFun_apply, projCoordFun_apply, map_zsmul,
        Finsupp.smul_apply, unop_smul, smul_assoc])
    (fun m n n' => by ext y; simp [projCoordFun_apply])
    (fun c m n => by ext y; simp [projCoordFun_apply, smul_comm _ c])

/-- The coordinates `M ⊗_A N → (M →₀ N)` attached to `s`. -/
def projCoord : BalancedTensor ℤ B A M N →ₗ[ℤ] (M →₀ N) :=
  lift (projCoordBil s) fun m a n => by
    ext y
    change projCoordFun s (op a • m) n y = projCoordFun s m (a • n) y
    rw [projCoordFun_apply, projCoordFun_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
      unop_mul, unop_op, mul_smul]

theorem projCoord_tmul (m : M) (n : N) :
    projCoord s (tmul m n : BalancedTensor ℤ B A M N) = projCoordFun s m n := rfl

variable (B N) in
/-- The summation map `(M →₀ N) → M ⊗_A N`, `f ↦ ∑_y y ⊗ f(y)`. -/
def projBack : (M →₀ N) →+ BalancedTensor ℤ B A M N :=
  Finsupp.liftAddHom fun y => AddMonoidHom.mk' (tmul y) (tmul_add y)

omit [SMulCommClass B Aᵐᵒᵖ M] in
theorem projBack_single (y : M) (n : N) :
    projBack B N (Finsupp.single y n) = (tmul y n : BalancedTensor ℤ B A M N) :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem projBack_projCoord (hs : Finsupp.linearCombination Aᵐᵒᵖ id ∘ₗ s = LinearMap.id)
    (t : BalancedTensor ℤ B A M N) : projBack B N (projCoord s t) = t := by
  induction t using induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul z n =>
    rw [projCoord_tmul, projCoordFun, projBack, Finsupp.liftAddHom_apply,
      Finsupp.sum_mapRange_index (fun y => by simp)]
    have hz : z = (s z).sum fun y r => r • y := by
      have := LinearMap.congr_fun hs z
      rw [LinearMap.comp_apply, Finsupp.linearCombination_apply] at this
      exact this.symm
    conv_rhs => rw [hz]
    rw [Finsupp.sum, Finsupp.sum, show (tmul (∑ a ∈ (s z).support, s z a • a) n :
      BalancedTensor ℤ B A M N) = (mkBil ℤ B A M N).flip n (∑ a ∈ (s z).support, s z a • a)
      from rfl, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [AddMonoidHom.mk'_apply, LinearMap.flip_apply, mkBil_apply, ← op_smul_tmul, op_unop]

theorem projCoord_mapRight (g : N →ₗ[A] N') (t : BalancedTensor ℤ B A M N) :
    projCoord s (mapRight (k := ℤ) (B := B) g t) =
      Finsupp.mapRange g (map_zero g) (projCoord s t) := by
  induction t using induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, Finsupp.mapRange_add (map_add g)]
  | tmul z n =>
    ext y
    rw [mapRight_tmul, projCoord_tmul, projCoord_tmul, Finsupp.mapRange_apply,
      projCoordFun_apply, projCoordFun_apply, map_smul]

theorem projBack_mapRange (g : N →ₗ[A] N') (f : M →₀ N) :
    projBack B N' (Finsupp.mapRange g (map_zero g) f) =
      mapRight (k := ℤ) (B := B) g (projBack B N f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' =>
    rw [Finsupp.mapRange_add (map_add g), map_add, map_add, map_add, hf, hf']
  | single y n => rw [Finsupp.mapRange_single, projBack_single, projBack_single, mapRight_tmul]

/-- `M ⊗_A -` preserves injections when `M` is a projective right `A`-module. -/
theorem mapRight_injective_of_projective [Module.Projective Aᵐᵒᵖ M] {g : N →ₗ[A] N'}
    (hg : Function.Injective g) :
    Function.Injective (mapRight (k := ℤ) (B := B) (M := M) g) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective Aᵐᵒᵖ M›
  intro x y hxy
  rw [← projBack_projCoord s hs x, ← projBack_projCoord s hs y]
  congr 1
  apply Finsupp.mapRange_injective g (map_zero g) hg
  rw [← projCoord_mapRight, ← projCoord_mapRight, hxy]

/-- `M ⊗_A -` is exact in the middle when `M` is a projective right `A`-module. -/
theorem mapRight_exact_of_projective [Module.Projective Aᵐᵒᵖ M] {f : N →ₗ[A] N'}
    {g : N' →ₗ[A] N''} (hfg : Function.Exact f g) :
    Function.Exact (mapRight (k := ℤ) (B := B) (M := M) f)
      (mapRight (k := ℤ) (B := B) (M := M) g) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective Aᵐᵒᵖ M›
  intro x
  constructor
  · intro hx
    have hmem : ∀ y, projCoord s x y ∈ Set.range f := fun y => by
      rw [← hfg]
      have := DFunLike.congr_fun (congrArg (projCoord s) hx) y
      rwa [projCoord_mapRight, map_zero, Finsupp.mapRange_apply, Finsupp.zero_apply] at this
    choose c hc using hmem
    classical
    let u : M →₀ N :=
      Finsupp.onFinset (projCoord s x).support
        (fun y => if projCoord s x y = 0 then 0 else c y) fun y hy => by
          rw [Finsupp.mem_support_iff]
          intro h
          exact hy (by simp [h])
    refine ⟨projBack B N u, ?_⟩
    rw [← projBack_mapRange]
    conv_rhs => rw [← projBack_projCoord s hs x]
    congr 1
    ext y
    simp only [Finsupp.mapRange_apply, u, Finsupp.onFinset_apply]
    split_ifs with h
    · rw [h, map_zero]
    · exact hc y
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← mapRight_comp]
    have : g.comp f = 0 := LinearMap.ext fun m => hfg.apply_apply_eq_zero m
    rw [this]
    induction y using induction_on with
    | zero => simp
    | tmul z n => simp
    | add a b ha hb => rw [map_add, ha, hb, add_zero]

end Projective

end BalancedTensor

namespace Stendhal.CupCap

open KLR KLRAlgebra TypeA

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

set_option hygiene false in
local notation "T" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "σ" => tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν
set_option hygiene false in
local notation "σp" => tensorFlipRingEquiv (Q := Q) (Λ := plusLabels Λ Λc j hj) (ν + ν₀)

variable (L : Type) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The reflection of `K^{λ⁺}_λ`**: the bimodule `K^{λ⁺}_λ` with `T^{λ⁺}` acting on the left
and `T^λ` on the right through the horizontal reflections, `s · z · t = σ(t) z σ(s)`. -/
def ReflectedCap : Type := CapBimodule k Q Λ Λc j hj ν ν₀ L

instance : AddCommGroup (ReflectedCap j hj Q Λ Λc ν ν₀ L) :=
  inferInstanceAs (AddCommGroup (CapBimodule k Q Λ Λc j hj ν ν₀ L))

instance : Module Tp (ReflectedCap j hj Q Λ Λc ν ν₀ L) :=
  Module.compHom (CapBimodule k Q Λ Λc j hj ν ν₀ L) (σp : Tp →+* Tpᵐᵒᵖ)

instance : Module Tᵐᵒᵖ (ReflectedCap j hj Q Λ Λc ν ν₀ L) :=
  Module.compHom (CapBimodule k Q Λ Λc j hj ν ν₀ L) ((σ).symm : Tᵐᵒᵖ →+* T)

variable {j hj Q Λ Λc ν ν₀ L}

/-- The identity of the underlying group, from the reflection of `K^{λ⁺}_λ` to `K^{λ⁺}_λ`. -/
def ofReflectedCap (z : ReflectedCap j hj Q Λ Λc ν ν₀ L) : CapBimodule k Q Λ Λc j hj ν ν₀ L := z

/-- The identity of the underlying group, from `K^{λ⁺}_λ` to its reflection. -/
def toReflectedCap (z : CapBimodule k Q Λ Λc j hj ν ν₀ L) : ReflectedCap j hj Q Λ Λc ν ν₀ L := z

theorem smul_toReflectedCap (s : Tp) (z : CapBimodule k Q Λ Λc j hj ν ν₀ L) :
    s • toReflectedCap z = toReflectedCap ((σp s) • z) := rfl

theorem op_smul_toReflectedCap (t : Tᵐᵒᵖ) (z : CapBimodule k Q Λ Λc j hj ν ν₀ L) :
    t • toReflectedCap z = toReflectedCap ((σ).symm t • z) := rfl

instance : SMulCommClass Tp Tᵐᵒᵖ (ReflectedCap j hj Q Λ Λc ν ν₀ L) where
  smul_comm s t z := by
    change toReflectedCap ((σp s) • ((σ).symm t • ofReflectedCap z)) =
      toReflectedCap ((σ).symm t • ((σp s) • ofReflectedCap z))
    exact congrArg toReflectedCap (smul_comm _ _ _).symm

/-- **The reflection of `K^{λ⁺}_λ` is a projective right `T^λ`-module** (reflection of
`projective_midCapBimodule`, Webster, arXiv:1309.3796v3, §7.3, after Lemma 7.19). -/
theorem projective_reflectedCap [Module k L]
    [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hQ : KLRSymm Q) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hP : PullOff k Q Λc ν₀ L)
    (hPL : PullOffLeft k Q Λc ν₀ L)
    (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
    (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht)))) :
    Module.Projective Tᵐᵒᵖ (ReflectedCap j hj Q Λ Λc ν ν₀ L) := by
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  obtain ⟨s, hs⟩ := Module.projective_def'.1 this
  refine Module.projective_def'.2 ⟨
    { toFun := fun z => (s z).mapRange (σ) (map_zero _)
      map_add' := fun z z' => by
        rw [show s (z + z') = s z + s z' from map_add s _ _]
        exact Finsupp.mapRange_add (map_add _) _ _
      map_smul' := fun t z => by
        ext y
        change (s ((σ).symm t • ofReflectedCap z)).mapRange (σ) _ y =
          t * (s (ofReflectedCap z)).mapRange (σ) _ y
        rw [map_smul, Finsupp.mapRange_apply, Finsupp.mapRange_apply, Finsupp.smul_apply,
          smul_eq_mul, map_mul, RingEquiv.apply_symm_apply] }, ?_⟩
  refine LinearMap.ext fun z => ?_
  have hz := LinearMap.congr_fun hs z
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply, LinearMap.id_apply] at hz
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply, LinearMap.id_apply]
  change ((s (ofReflectedCap z)).mapRange (σ) (map_zero _)).sum
    (fun y r => r • toReflectedCap y) = z
  rw [Finsupp.sum_mapRange_index (fun y => zero_smul Tᵐᵒᵖ (toReflectedCap y))]
  conv_rhs => rw [← hz]
  refine Finset.sum_congr rfl fun y _ => ?_
  change toReflectedCap ((σ).symm ((σ) (s z y)) • y) = toReflectedCap (s z y • y)
  rw [RingEquiv.symm_apply_apply]

variable (j hj Q Λ Λc ν ν₀ L)

/-- **The reflected coevaluation functor on left modules**: `M ↦ K^σ ⊗_{T^λ} M`, a left
`T^{λ⁺}`-module (Webster's `𝕂 = - ⊗_{T^λ} K^{λ⁺}_λ` of Definition 7.18, read through the
horizontal reflections). -/
abbrev CoeTensor (M : Type*) [AddCommGroup M] [Module T M] : Type _ :=
  BalancedTensor ℤ Tp T (ReflectedCap j hj Q Λ Λc ν ν₀ L) M

variable {j hj Q Λ Λc ν ν₀ L}
variable {M M' M'' : Type*} [AddCommGroup M] [Module T M] [AddCommGroup M'] [Module T M']
  [AddCommGroup M''] [Module T M'']

/-- The reflected coevaluation functor on maps. -/
def coeTensorMap (g : M →ₗ[T] M') :
    CoeTensor j hj Q Λ Λc ν ν₀ L M →ₗ[Tp] CoeTensor j hj Q Λ Λc ν ν₀ L M' :=
  BalancedTensor.mapRight g

theorem coeTensorMap_tmul (g : M →ₗ[T] M') (z : ReflectedCap j hj Q Λ Λc ν ν₀ L) (m : M) :
    coeTensorMap g (BalancedTensor.tmul z m : CoeTensor j hj Q Λ Λc ν ν₀ L M) =
      BalancedTensor.tmul z (g m) := rfl

theorem coeTensorMap_id :
    coeTensorMap (j := j) (hj := hj) (Λc := Λc) (ν₀ := ν₀) (L := L)
      (LinearMap.id : M →ₗ[T] M) = LinearMap.id :=
  BalancedTensor.mapRight_id

theorem coeTensorMap_comp (g : M →ₗ[T] M') (g' : M' →ₗ[T] M'') :
    coeTensorMap (j := j) (hj := hj) (Λc := Λc) (ν₀ := ν₀) (L := L) (g'.comp g) =
      (coeTensorMap g').comp (coeTensorMap g) :=
  BalancedTensor.mapRight_comp g g'

section Exact

variable [Module.Projective Tᵐᵒᵖ (ReflectedCap j hj Q Λ Λc ν ν₀ L)]

/-- The reflected coevaluation functor preserves injections (`K^{λ⁺}_λ` is left projective). -/
theorem coeTensorMap_injective {g : M →ₗ[T] M'} (hg : Function.Injective g) :
    Function.Injective (coeTensorMap (j := j) (hj := hj) (Λc := Λc) (ν₀ := ν₀) (L := L) g) :=
  BalancedTensor.mapRight_injective_of_projective hg

/-- **The reflected coevaluation functor is exact** (`K^{λ⁺}_λ` is left projective). -/
theorem coeTensorMap_exact {f : M →ₗ[T] M'} {g : M' →ₗ[T] M''} (hfg : Function.Exact f g) :
    Function.Exact (coeTensorMap (j := j) (hj := hj) (Λc := Λc) (ν₀ := ν₀) (L := L) f)
      (coeTensorMap (j := j) (hj := hj) (Λc := Λc) (ν₀ := ν₀) (L := L) g) :=
  BalancedTensor.mapRight_exact_of_projective hfg

end Exact

end Stendhal.CupCap

end Categorification
