import Categorification.KLR.CyclotomicMixedInversionQuotient

/-!
# Cyclotomic rectangular mixed-crossing equivalence

Kang–Kashiwara, arXiv:1102.4677v4, Theorem 5.1, especially equation (5.2) in its proof:
the actual affine crossing maps the span of the two cyclotomic factor ideals
onto the upper cyclotomic ideal intersected with the full rectangular corner.
The signed crossing `tau = -psi` therefore descends between actual cyclotomic
bimodules; both inverses and both differently ordered coefficient actions are proved.
The empty lower weight is included. Injectivity retains `IsDomain k`, the specified
nonzero factorization of `Q`, and `KLRSymm Q`: this is narrower than the source's
commutative-base generality. No arbitrary-Q or `BrundanMixedInversion` claim is made.
Tensor-with-modules naturality and comparison with Brundan's ordinary-adjunction
mixed mate are separate remaining obligations.
-/
noncomputable section
namespace Categorification.KLR.KLRAlgebra.MixedCyclotomic
open scoped TensorProduct
open MixedAffine Lower
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k)
  (γ : Multiset I) (i j : I) (a : I → Polynomial k)
local notation "U" => KLRAlgebra k Q ((γ + Multiset.cons j 0) + Multiset.cons i 0)
local notation "A" => KLRAlgebra k Q (γ + Multiset.cons j 0)
local notation "C" => KLRAlgebra k Q (γ + Multiset.cons i 0)
local notation "T" => Source Q γ i j
variable (hsym : KLRSymm Q) (hij : i ≠ j)

theorem tensorRelations_map_le :
    Submodule.map (affineEquiv Q γ i j hsym hij).toLinearMap
      (tensorRelations Q γ i j a) ≤ cornerIdeal Q γ i j a := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.2
  rintro z ⟨x, y, hxy, rfl⟩
  change (affineEquiv Q γ i j hsym hij (BalancedTensor.tmul x y) : U) ∈
    cycIdeal Q a ((γ + {j}) + {i})
  rw [affineEquiv_tmul]
  rcases hxy with hx | hy
  · exact TwoSidedIdeal.mul_mem_right _ _ _
      (TwoSidedIdeal.mul_mem_right _ _ _ (inc_mem_cycIdeal Q a (γ + {j}) i hx))
  · apply TwoSidedIdeal.mul_mem_left
    apply (castKLR_mem_cycIdeal a (weightSquare γ i j) _).2
    exact inc_mem_cycIdeal Q a (γ + {i}) j hy


theorem lowerCoefficients_decode_le :
    MixedInversion.lowerCoefficientRelations (Q := Q) a (Multiset.card γ + 1)
      (by simp) i j ≤
    Submodule.comap ((affineEquiv Q γ i j hsym hij).symm.toLinearMap ∘ₗ project Q γ i j)
      (tensorRelations Q γ i j a) := by
  apply Submodule.span_le.2
  rintro z ⟨u, v, huv, rfl⟩
  change (affineEquiv Q γ i j hsym hij).symm
    (project Q γ i j (MixedInversion.cut ⟨Multiset.card γ + 1, by simp⟩ i j
      (u * cycAt a ⟨0, by simp⟩ * v))) ∈ tensorRelations Q γ i j a
  rw [← project_val, project_fixed]
  rcases huv with hu | hv
  · obtain ⟨b, hb, he⟩ := left_coefficient_lift Q γ i j a u v hu
    rw [he, affineEquiv_symm_left]
    exact left_ideal_smul Q γ i j a hb _
  · obtain ⟨b, hb, he⟩ := right_coefficient_lift Q γ i j a u v hv
    rw [he, affineEquiv_symm_right]
    exact right_ideal_act Q γ i j a hb _

theorem tensorRelations_map_eq (hsym : KLRSymm Q) :
    Submodule.map (affineEquiv Q γ i j hsym hij).toLinearMap
      (tensorRelations Q γ i j a) = cornerIdeal Q γ i j a := by
  apply le_antisymm (tensorRelations_map_le Q γ i j a hsym hij)
  intro z hz
  have hc : MixedInversion.cut ⟨Multiset.card γ + 1, by simp⟩ i j (z : U) ∈
      MixedInversion.lowerCoefficientRelations (Q := Q) a (Multiset.card γ + 1)
        (by simp) i j := by
    rw [MixedInversion.lowerCoefficientRelations_eq_cyclotomicIdeal a _ _ i j hsym hij]
    exact Submodule.mem_map.2 ⟨z, hz, rfl⟩
  have hd := lowerCoefficients_decode_le Q γ i j a hsym hij hc
  change (affineEquiv Q γ i j hsym hij).symm
    (project Q γ i j (MixedInversion.cut ⟨Multiset.card γ + 1, by simp⟩ i j (z : U))) ∈
      tensorRelations Q γ i j a at hd
  rw [← project_val, project_fixed, project_fixed] at hd
  exact Submodule.mem_map.2 ⟨_, hd, (affineEquiv Q γ i j hsym hij).apply_symm_apply z⟩


theorem affine_mem_cornerIdeal_iff (hsym : KLRSymm Q) (z : T) :
    affineEquiv Q γ i j hsym hij z ∈ cornerIdeal Q γ i j a ↔ z ∈ tensorRelations Q γ i j a := by
  rw [← tensorRelations_map_eq Q γ i j a hij hsym]
  constructor
  · intro hz
    obtain ⟨w, hw, he⟩ := Submodule.mem_map.1 hz
    exact (affineEquiv Q γ i j hsym hij).injective he ▸ hw
  · intro hz
    exact Submodule.mem_map.2 ⟨z, hz, rfl⟩

theorem tau_mem_cornerIdeal_iff (hsym : KLRSymm Q) (z : T) :
    tauEquiv Q γ i j hsym hij z ∈ cornerIdeal Q γ i j a ↔ z ∈ tensorRelations Q γ i j a := by
  change -affineEquiv Q γ i j hsym hij z ∈ _ ↔ _
  rw [Submodule.neg_mem_iff, affine_mem_cornerIdeal_iff Q γ i j a hij hsym]

variable (hsym : KLRSymm Q)

def quotientTau : QuotientSource Q γ i j a →ₗ[k] QuotientCorner Q γ i j a :=
  descend (tensorMk Q γ i j a) (tensorMk_surjective Q γ i j a)
    ((cornerMk Q γ i j a).comp (tauEquiv Q γ i j hsym hij).toLinearMap) (by
      intro z hz
      apply (cornerMk_zero_iff Q γ i j a _).2
      apply (tau_mem_cornerIdeal_iff Q γ i j a hij hsym z).2
      rw [← tensorMk_ker_eq]
      exact hz)

theorem quotientTau_mk (z : T) :
    quotientTau Q γ i j a hij hsym (tensorMk Q γ i j a z) =
      cornerMk Q γ i j a (tauEquiv Q γ i j hsym hij z) := descend_apply _ _ _ _ z

def quotientTauInv : QuotientCorner Q γ i j a →ₗ[k] QuotientSource Q γ i j a :=
  descend (cornerMk Q γ i j a) (cornerMk_surjective Q γ i j a)
    ((tensorMk Q γ i j a).comp (tauEquiv Q γ i j hsym hij).symm.toLinearMap) (by
      intro z hz
      change (tauEquiv Q γ i j hsym hij).symm z ∈ LinearMap.ker (tensorMk Q γ i j a)
      rw [tensorMk_ker_eq, ← tau_mem_cornerIdeal_iff Q γ i j a hij hsym,
        LinearEquiv.apply_symm_apply]
      exact (cornerMk_zero_iff Q γ i j a z).1 hz)

theorem quotientTauInv_mk (z : bimod Q (weightSquare γ i j)) :
    quotientTauInv Q γ i j a hij hsym (cornerMk Q γ i j a z) =
      tensorMk Q γ i j a ((tauEquiv Q γ i j hsym hij).symm z) := descend_apply _ _ _ _ z

theorem quotientTauInv_tau (z : QuotientSource Q γ i j a) :
    quotientTauInv Q γ i j a hij hsym (quotientTau Q γ i j a hij hsym z) = z := by
  obtain ⟨z, rfl⟩ := tensorMk_surjective Q γ i j a z
  rw [quotientTau_mk, quotientTauInv_mk, LinearEquiv.symm_apply_apply]

theorem quotientTau_tauInv (z : QuotientCorner Q γ i j a) :
    quotientTau Q γ i j a hij hsym (quotientTauInv Q γ i j a hij hsym z) = z := by
  obtain ⟨z, rfl⟩ := cornerMk_surjective Q γ i j a z
  rw [quotientTauInv_mk, quotientTau_mk, LinearEquiv.apply_symm_apply]

def quotientTauEquiv : QuotientSource Q γ i j a ≃ₗ[k] QuotientCorner Q γ i j a :=
  { quotientTau Q γ i j a hij hsym with
    invFun := quotientTauInv Q γ i j a hij hsym
    left_inv := quotientTauInv_tau Q γ i j a hij hsym
    right_inv := quotientTau_tauInv Q γ i j a hij hsym }

theorem quotientTau_tmul (x : Left Q γ j) (y : Right Q γ i) :
    (quotientTau Q γ i j a hij hsym
      (BalancedTensor.tmul (leftMk Q γ j a x) (rightMk Q γ i a y)) :
        CycKLR k Q a ((γ + {j}) + {i})) =
    CycKLR.mk k Q a ((γ + {j}) + {i})
      (-(inc Q (γ + {j}) i (x : A) * ψ (Multiset.card γ) *
        castKLR Q (weightSquare γ i j) (inc Q (γ + {i}) j (y : C)))) := by
  rw [← tensorMk_tmul, quotientTau_mk]
  have h := tauEquiv_tmul Q γ i j hsym hij x y
  simp only [mul_neg, neg_mul] at h
  exact congrArg (CycKLR.mk k Q a ((γ + {j}) + {i})) h


theorem quotientTau_left (b : CycKLR k Q a (γ + {j})) (z : QuotientSource Q γ i j a) :
    quotientTau Q γ i j a hij hsym (b • z) =
      quotientCornerLeft Q γ i j a b (quotientTau Q γ i j a hij hsym z) := by
  obtain ⟨b, rfl⟩ := CycKLR.mk_surjective b
  obtain ⟨z, rfl⟩ := tensorMk_surjective Q γ i j a z
  rw [← tensorMk_left, quotientTau_mk, quotientTau_mk, ← cornerMk_left]
  congr 1
  change -affineEquiv Q γ i j hsym hij (b • z) =
    cornerLeft Q γ i j b (-affineEquiv Q γ i j hsym hij z)
  apply Subtype.ext
  change -(affineEquiv Q γ i j hsym hij (b • z) : U) =
    inc Q (γ + {j}) i b * -(affineEquiv Q γ i j hsym hij z : U)
  rw [affineEquiv_left, mul_neg]
  rfl

theorem quotientTau_right (b : CycKLR k Q a (γ + {i})) (z : QuotientSource Q γ i j a) :
    quotientTau Q γ i j a hij hsym (quotientRightAct Q γ i j a b z) =
      quotientCornerRight Q γ i j a b (quotientTau Q γ i j a hij hsym z) := by
  obtain ⟨b, rfl⟩ := CycKLR.mk_surjective b
  obtain ⟨z, rfl⟩ := tensorMk_surjective Q γ i j a z
  rw [← tensorMk_right, quotientTau_mk, quotientTau_mk, ← cornerMk_right]
  congr 1
  change -affineEquiv Q γ i j hsym hij (rightAct Q γ i j b z) =
    cornerRight Q γ i j b (-affineEquiv Q γ i j hsym hij z)
  apply Subtype.ext
  change -(affineEquiv Q γ i j hsym hij (rightAct Q γ i j b z) : U) =
    -(affineEquiv Q γ i j hsym hij z : U) * botConcat Q (weightSquare γ i j) (b ⊗ₜ 1)
  rw [affineEquiv_right, neg_mul]

theorem quotientTauInv_left (b : CycKLR k Q a (γ + {j})) (z : QuotientCorner Q γ i j a) :
    quotientTauInv Q γ i j a hij hsym (quotientCornerLeft Q γ i j a b z) =
      b • quotientTauInv Q γ i j a hij hsym z := by
  apply (quotientTauEquiv Q γ i j a hij hsym).injective
  change quotientTau Q γ i j a hij hsym _ = quotientTau Q γ i j a hij hsym _
  rw [quotientTau_tauInv, quotientTau_left, quotientTau_tauInv]

theorem quotientTauInv_right (b : CycKLR k Q a (γ + {i})) (z : QuotientCorner Q γ i j a) :
    quotientTauInv Q γ i j a hij hsym (quotientCornerRight Q γ i j a b z) =
      quotientRightAct Q γ i j a b (quotientTauInv Q γ i j a hij hsym z) := by
  apply (quotientTauEquiv Q γ i j a hij hsym).injective
  change quotientTau Q γ i j a hij hsym _ = quotientTau Q γ i j a hij hsym _
  rw [quotientTau_tauInv, quotientTau_right, quotientTau_tauInv]

end Categorification.KLR.KLRAlgebra.MixedCyclotomic
