/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAbsentModule

/-!
# The ordinary cyclotomic induction/restriction adjunction

`cyclotomicHomEquiv` proves Frobenius reciprocity for the actual modules
`Ind N = (S e) ⊗_Rl N` and `Res M = e M` from `CyclotomicAbsentModule`.
The forward map is `f ↦ (n ↦ f(e ⊗ n))`; the inverse is
`g ↦ (z ⊗ n ↦ z • g(n))`. Balancing uses the nonunital inclusion
`cyclotomicLast`, whose unit image is `e`, not the ambient unit of `S`.
Both directions are natural for the existing `indMap` and `resMap`.

`inductionFunctor` and `restrictionFunctor` bundle these same objects and maps
on `ModuleCat`; `cyclotomicAdjunction` supplies the unit, counit and both
triangle identities. The displayed formulas identify the unit as `n ↦ e ⊗ n`
and the counit as `z ⊗ m ↦ z • m`. Bundled modules carry the canonical
restriction of scalars from their cyclotomic algebra. The unbundled Hom
equivalence permits any compatible ground-ring module structure.

These are the induction and restriction of Kang–Kashiwara,
arXiv:1102.4677v4, §4.2. In that paper's notation the direction proved here
is `F_i^Λ ⊣ E_i^Λ`. No domain, monicity, projectivity, flatness, finite-rank
or nonzero-quotient hypothesis is needed for this ordinary adjunction.
The opposite adjunction (and graded shifts), the identification with a chosen
upward/downward convention in Brundan's presentation, and the remaining
categorical-action relations are not asserted here.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour
open MulOpposite
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k) (β : Multiset I)
local notation "Rl" => CycKLR k Q a β
local notation "S" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + β)
local notation "ι" => cyclotomicLast Q i a β

/-- The distinguished generator of the actual induction corner. -/
def indGenerator : IndCorner Q i a β := ⟨lastIdem Q i a β, lastIdem_mul Q i a β⟩

theorem indGenerator_fixed :
    lastIdem Q i a β • indGenerator Q i a β = indGenerator Q i a β :=
  Subtype.ext (lastIdem_mul Q i a β)

theorem indGenerator_balance (r : Rl) :
    op r • indGenerator Q i a β = ι r • indGenerator Q i a β := by
  apply Subtype.ext
  change ι 1 * ι r = ι r * ι 1
  rw [← map_mul, ← map_mul, one_mul, mul_one]

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (CycKLR k Q a β) N]
  [IsScalarTower k (CycKLR k Q a β) N]
  {M : Type*} [AddCommGroup M] [Module k M] [Module (CycKLR k Q a ({i} + β)) M]
  [IsScalarTower k (CycKLR k Q a ({i} + β)) M]

/-- Evaluation at `e ⊗ n`, valued in the actual fixed submodule. -/
def homToRes (f : Ind Q i a β N →ₗ[S] M) : N →ₗ[Rl] Res Q i a β M where
  toFun n := ⟨f (BalancedTensor.tmul (indGenerator Q i a β) n), by
    change lastIdem Q i a β • f _ = f _
    rw [← map_smul, BalancedTensor.smul_tmul', indGenerator_fixed]⟩
  map_add' n n' := Subtype.ext (by simp only [BalancedTensor.tmul_add, map_add, Submodule.coe_add])
  map_smul' r n := Subtype.ext (by
    change f (BalancedTensor.tmul (indGenerator Q i a β) (r • n)) =
      ι r • f (BalancedTensor.tmul (indGenerator Q i a β) n)
    rw [← BalancedTensor.op_smul_tmul, indGenerator_balance,
      ← BalancedTensor.smul_tmul', map_smul])

omit [IsScalarTower k (CycKLR k Q a β) N] in
@[simp] theorem homToRes_val (f : Ind Q i a β N →ₗ[S] M) (n : N) :
    (homToRes Q i a β f n).1 = f (BalancedTensor.tmul (indGenerator Q i a β) n) := rfl

/-- Coefficients act on the left, in their original noncommutative order. -/
def homFromResBil (g : N →ₗ[Rl] Res Q i a β M) : IndCorner Q i a β →ₗ[k] N →ₗ[k] M :=
  LinearMap.mk₂ k (fun z n => z.1 • (g n).1)
    (fun z w n => by simp only [Submodule.coe_add, add_smul])
    (fun c z n => by
      change (c • z.1) • (g n).1 = c • (z.1 • (g n).1)
      rw [smul_assoc])
    (fun z n n' => by simp only [map_add, Submodule.coe_add, smul_add])
    (fun c z n => by
      rw [LinearMap.map_smul_of_tower, Submodule.coe_smul, smul_comm])

/-- The inverse map descends `z ⊗ n ↦ z • g(n)` through actual right balancing. -/
def homFromRes (g : N →ₗ[Rl] Res Q i a β M) : Ind Q i a β N →ₗ[S] M :=
  BalancedTensor.liftB (homFromResBil Q i a β g)
    (fun z r n => by
      change (z.1 * ι r) • (g n).1 = z.1 • (g (r • n)).1
      rw [map_smul]
      exact mul_smul _ _ _)
    (fun s z n => mul_smul s z.1 (g n).1)

@[simp] theorem homFromRes_tmul (g : N →ₗ[Rl] Res Q i a β M)
    (z : IndCorner Q i a β) (n : N) :
    homFromRes Q i a β g (BalancedTensor.tmul z n) = z.1 • (g n).1 := rfl

theorem homFromRes_homToRes (f : Ind Q i a β N →ₗ[S] M) :
    homFromRes Q i a β (homToRes Q i a β f) = f :=
  BalancedTensor.extB fun z n => by
    rw [homFromRes_tmul, homToRes_val, ← map_smul, BalancedTensor.smul_tmul']
    congr 2
    exact Subtype.ext z.2

theorem homToRes_homFromRes (g : N →ₗ[Rl] Res Q i a β M) :
    homToRes Q i a β (homFromRes Q i a β g) = g :=
  LinearMap.ext fun n => Subtype.ext (by
    rw [homToRes_val, homFromRes_tmul]
    exact (g n).2)

/-- Frobenius reciprocity for the genuine cyclotomic induction and restriction. -/
def cyclotomicHomEquiv : (Ind Q i a β N →ₗ[S] M) ≃ₗ[k] (N →ₗ[Rl] Res Q i a β M) where
  toFun := homToRes Q i a β
  invFun := homFromRes Q i a β
  left_inv := homFromRes_homToRes Q i a β
  right_inv := homToRes_homFromRes Q i a β
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Naturality
variable {N' : Type*} [AddCommGroup N'] [Module k N'] [Module (CycKLR k Q a β) N']
  [IsScalarTower k (CycKLR k Q a β) N']
  {M' : Type*} [AddCommGroup M'] [Module k M'] [Module (CycKLR k Q a ({i} + β)) M']
  [IsScalarTower k (CycKLR k Q a ({i} + β)) M']

/-- Naturality in the input module, with the existing induction map. -/
theorem cyclotomicHomEquiv_natural_left (f : N' →ₗ[Rl] N) (g : Ind Q i a β N →ₗ[S] M) :
    cyclotomicHomEquiv Q i a β (g.comp (indMap Q i a β N' f)) =
      (cyclotomicHomEquiv Q i a β g).comp f := rfl

/-- Naturality in the target module, with actual idempotent restriction. -/
theorem cyclotomicHomEquiv_natural_right (f : Ind Q i a β N →ₗ[S] M) (g : M →ₗ[S] M') :
    cyclotomicHomEquiv Q i a β (g.comp f) =
      (resMap Q i a β M g).comp (cyclotomicHomEquiv Q i a β f) := rfl

theorem cyclotomicHomEquiv_symm_natural_left (f : N' →ₗ[Rl] N) (g : N →ₗ[Rl] Res Q i a β M) :
    (cyclotomicHomEquiv Q i a β).symm (g.comp f) =
      ((cyclotomicHomEquiv Q i a β).symm g).comp (indMap Q i a β N' f) :=
  BalancedTensor.extB fun _ _ => rfl

theorem cyclotomicHomEquiv_symm_natural_right (f : N →ₗ[Rl] Res Q i a β M) (g : M →ₗ[S] M') :
    (cyclotomicHomEquiv Q i a β).symm ((resMap Q i a β M g).comp f) =
      g.comp ((cyclotomicHomEquiv Q i a β).symm f) :=
  BalancedTensor.extB fun z n => (g.map_smul z.1 (f n).1).symm
end Naturality

section Bundled
open CategoryTheory
open scoped ModuleCat.Algebra

/-- Genuine cyclotomic induction, bundled on all modules. -/
def inductionFunctor : ModuleCat.{max u v w} Rl ⥤ ModuleCat.{max u v w} S where
  obj N := ModuleCat.of S (Ind Q i a β N)
  map f := ModuleCat.ofHom (indMap Q i a β _ f.hom)
  map_id _ := ModuleCat.hom_ext BalancedTensor.mapRight_id
  map_comp f g := ModuleCat.hom_ext (BalancedTensor.mapRight_comp f.hom g.hom)

/-- Genuine cyclotomic idempotent restriction, bundled on all modules. -/
def restrictionFunctor : ModuleCat.{max u v w} S ⥤ ModuleCat.{max u v w} Rl where
  obj M := ModuleCat.of Rl (Res Q i a β M)
  map f := ModuleCat.ofHom (resMap Q i a β _ f.hom)
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The ordinary cyclotomic induction/restriction adjunction. -/
def cyclotomicAdjunction : inductionFunctor Q i a β ⊣ restrictionFunctor Q i a β :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N M =>
        { toFun := fun f => ModuleCat.ofHom (homToRes Q i a β f.hom)
          invFun := fun g => ModuleCat.ofHom (homFromRes Q i a β g.hom)
          left_inv := fun f => ModuleCat.hom_ext (homFromRes_homToRes Q i a β f.hom)
          right_inv := fun g => ModuleCat.hom_ext (homToRes_homFromRes Q i a β g.hom) }
      homEquiv_naturality_left_symm := fun f g =>
        ModuleCat.hom_ext (BalancedTensor.extB fun z n => rfl)
      homEquiv_naturality_right := fun f g => by ext n; rfl }

@[simp] theorem cyclotomicAdjunction_unit_val (N : ModuleCat.{max u v w} Rl) (n : N) :
    ((cyclotomicAdjunction Q i a β).unit.app N n).1 =
      BalancedTensor.tmul (indGenerator Q i a β) n := rfl

@[simp] theorem cyclotomicAdjunction_counit_tmul (M : ModuleCat.{max u v w} S)
    (z : IndCorner Q i a β) (m : Res Q i a β M) :
    (cyclotomicAdjunction Q i a β).counit.app M (BalancedTensor.tmul z m) = z.1 • m.1 := rfl

/-- The unit is natural for every morphism, not only isomorphisms or projectives. -/
theorem cyclotomicAdjunction_unit_natural {N N' : ModuleCat.{max u v w} Rl} (f : N ⟶ N') :
    f ≫ (cyclotomicAdjunction Q i a β).unit.app N' =
      (cyclotomicAdjunction Q i a β).unit.app N ≫
        (restrictionFunctor Q i a β).map ((inductionFunctor Q i a β).map f) :=
  (cyclotomicAdjunction Q i a β).unit.naturality f

theorem cyclotomicAdjunction_counit_natural {M M' : ModuleCat.{max u v w} S} (f : M ⟶ M') :
    (inductionFunctor Q i a β).map ((restrictionFunctor Q i a β).map f) ≫
        (cyclotomicAdjunction Q i a β).counit.app M' =
      (cyclotomicAdjunction Q i a β).counit.app M ≫ f :=
  (cyclotomicAdjunction Q i a β).counit.naturality f

/-- The induction triangle, for the actual functor and the displayed tensor maps. -/
theorem cyclotomicAdjunction_ind_triangle (N : ModuleCat.{max u v w} Rl) :
    (inductionFunctor Q i a β).map ((cyclotomicAdjunction Q i a β).unit.app N) ≫
        (cyclotomicAdjunction Q i a β).counit.app ((inductionFunctor Q i a β).obj N) =
      𝟙 ((inductionFunctor Q i a β).obj N) :=
  (cyclotomicAdjunction Q i a β).left_triangle_components N

/-- The restriction triangle, on the actual idempotent-fixed submodule. -/
theorem cyclotomicAdjunction_res_triangle (M : ModuleCat.{max u v w} S) :
    (cyclotomicAdjunction Q i a β).unit.app ((restrictionFunctor Q i a β).obj M) ≫
        (restrictionFunctor Q i a β).map ((cyclotomicAdjunction Q i a β).counit.app M) =
      𝟙 ((restrictionFunctor Q i a β).obj M) :=
  (cyclotomicAdjunction Q i a β).right_triangle_components M

end Bundled
end Categorification.KLR.KLRAlgebra.AbsentColour
