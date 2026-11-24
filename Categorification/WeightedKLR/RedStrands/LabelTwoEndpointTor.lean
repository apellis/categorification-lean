import Categorification.WeightedKLR.RedStrands.SingleRedTerminalProjective
import Categorification.Algebra.BalancedTensor
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# The label-two exterior factor

Webster, arXiv:1309.3796v2, §8.2 Proposition 8.4. The exterior allocations
of two black strands have a saturated one-red factor. The balanced tensor
of the terminal right and left divided-power projectives is their scalar
corner. The left projective makes the higher derived tensor vanish.
-/

namespace Categorification.Stendhal.SingleRed

open KLR MulOpposite CategoryTheory

noncomputable section

universe u
variable {k : Type u} [Field k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)

local notation "A" => TensorProductAlgebra k Q (fun (_ : Fin 1) => Finsupp.single () 2)
  (Multiset.replicate 2 ())
local notation "E" => twoBlackTerminalWebsterIdem Q
local notation "hE" => twoBlackTerminalWebsterIdem_idempotent Q

private local instance (priority := 2000) endpointScalars (N : ModuleCat.{u} A) : Module k N :=
  Module.compHom N (algebraMap k A)

private local instance endpointScalarTower (N : ModuleCat.{u} A) : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

local notation "V" => ModuleCat.of A (lIdeal E)
local notation "C" => IsIdempotentElem.Corner hE
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- Tensoring the right divided-power endpoint projective with a left module. -/
def labelTwoEndpointTensor : ModuleCat.{u} A ⥤ ModuleCat.{u} k where
  obj N := ModuleCat.of k (BalancedTensor k k A (rIdeal E) N)
  map f := ModuleCat.ofHom (BalancedTensor.mapRight f.hom)
  map_id _ := ModuleCat.hom_ext (BalancedTensor.ext fun _ _ => rfl)
  map_comp _ _ := ModuleCat.hom_ext (BalancedTensor.ext fun _ _ => rfl)

instance : (labelTwoEndpointTensor Q).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    change BalancedTensor.tmul m (f n+g n) =
      BalancedTensor.tmul m (f n)+BalancedTensor.tmul m (g n)
    exact BalancedTensor.tmul_add _ _ _

private def leftEndpointProjection : A →ₗ[A] lIdeal E where
  toFun x := ⟨x*E, by rw [mem_lIdeal,mul_assoc,(hE).eq]⟩
  map_add' x y := Subtype.ext (add_mul x y E)
  map_smul' a x := Subtype.ext (mul_assoc a x E)

private theorem leftEndpoint_projective : Projective (V) := by
  have split : (leftEndpointProjection Q).comp (lIdeal E).subtype = LinearMap.id :=
    LinearMap.ext fun x => Subtype.ext x.property
  let : Module.Projective A (lIdeal E) :=
    Module.Projective.of_split (lIdeal E).subtype (leftEndpointProjection Q) split
  infer_instance

private local instance (priority := 2100) leftEndpointScalars : Module k (lIdeal E) :=
  endpointScalars Q (V)

private def endpointProduct (x : rIdeal E) (y : lIdeal E) : C :=
  ⟨x.val*y.val,(Subsemigroup.mem_corner_iff hE).mpr
    ⟨by rw [← mul_assoc,mem_rIdeal.mp x.property],
     by rw [mul_assoc,mem_lIdeal.mp y.property]⟩⟩

private def endpointProductBil : (rIdeal E) →ₗ[k] (V) →ₗ[k] C :=
  LinearMap.mk₂ k (endpointProduct Q)
    (fun x y z => Subtype.ext (add_mul x.val y.val z.val))
    (fun c x y => Subtype.ext (smul_mul_assoc c x.val y.val))
    (fun x y z => Subtype.ext (mul_add x.val y.val z.val))
    (fun c x y => Subtype.ext (by
      change x.val * (algebraMap k A c * y.val) = c • (x.val*y.val)
      rw [← Algebra.smul_def,mul_smul_comm]))

private def endpointProductMap : (labelTwoEndpointTensor Q).obj (V) →ₗ[k] C :=
  BalancedTensor.lift (endpointProductBil Q)
    (fun m a n => Subtype.ext (mul_assoc m.val a n.val))

private def cornerToLeft : C →ₗ[k] (V) where
  toFun z := ⟨z.val,((Subsemigroup.mem_corner_iff hE).mp z.property).2⟩
  map_add' _ _ := rfl
  map_smul' c z := Subtype.ext (Algebra.smul_def c z.val)

private def endpointProductInv : C →ₗ[k] (labelTwoEndpointTensor Q).obj (V) :=
  (BalancedTensor.mkBil k k A (rIdeal E) (V) ⟨E,(hE).eq⟩).comp (cornerToLeft Q)

/-- Multiplication identifies the paired endpoint modules with the scalar corner. -/
def labelTwoEndpointPairing :
    (labelTwoEndpointTensor Q).obj (V) ≃ₗ[k] C :=
  LinearEquiv.ofLinearMap (endpointProductMap Q) (endpointProductInv Q)
    (LinearMap.ext fun z => Subtype.ext (by
      change E * z.val = z.val
      exact ((Subsemigroup.mem_corner_iff hE).mp z.property).1))
    (BalancedTensor.ext fun m n => by
      change BalancedTensor.tmul (⟨E,(hE).eq⟩ : rIdeal E) (m.val • n) =
        BalancedTensor.tmul m n
      rw [← BalancedTensor.op_smul_tmul]
      congr 1
      exact Subtype.ext (mem_rIdeal.mp m.property))

/-- Left-derived tensor of the paired terminal endpoint modules. -/
abbrev labelTwoEndpointTor (n : ℕ) : ModuleCat k :=
  ((labelTwoEndpointTensor Q).leftDerived n).obj (V)

/-- The non-vacuum exterior factor in degree zero contributes one scalar. -/
def labelTwoEndpointTorZero : labelTwoEndpointTor Q 0 ≅ ModuleCat.of k k := by
  letI : Projective (V) := leftEndpoint_projective Q
  exact asIso ((labelTwoEndpointTensor Q).fromLeftDerivedZero.app (V)) ≪≫
    ((labelTwoEndpointPairing Q).trans (twoBlackTerminalWebsterCornerEquiv Q).toLinearEquiv).toModuleIso

/-- The exterior factor contributes no higher tensor homology. -/
theorem labelTwoEndpointTor_succ_isZero (n : ℕ) :
    Limits.IsZero (labelTwoEndpointTor Q (n+1)) := by
  let : Projective (V) := leftEndpoint_projective Q
  exact (labelTwoEndpointTensor Q).isZero_leftDerived_obj_projective_succ n (V)

end

end Categorification.Stendhal.SingleRed
