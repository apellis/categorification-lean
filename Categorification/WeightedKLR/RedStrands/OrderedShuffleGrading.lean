/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderedShuffleRepresentation
import Categorification.Algebra.Graded.G0
import Categorification.Algebra.Graded.Quotient

/-!
# Grading the quotient supported on ordered loadings

Webster, arXiv:1309.3796v2, Definitions 4.4–4.7 and §5, Theorem 5.8.
The quotient by excluded loadings inherits the grading of the affine
representation. Projection gives a graded isomorphism on each included
loading, so all of its homogeneous multiplicities survive.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded DirectSum

universe w
variable {I k : Type*} [DecidableEq I] [Field k] {μ : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} (G : GradingDatum Q)
  (S : Finset (Seq μ))
local notation "Aff" => KLRAlgebra k Q μ
variable (M : Type w) [AddCommGroup M] [Module k M] [Module (KLRAlgebra k Q μ) M] [IsScalarTower k (KLRAlgebra k Q μ) M]
  (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul (G.grade μ) ℳ]

local notation "ρ" => Algebra.lsmul k k M (A := Aff)
local notation "K" => excludedSpace (ρ) S
local notation "W" => (M ⧸ K)
local notation "𝓦" => quotGrading ℳ (K)

include G in
/-- The excluded affine sectors form a homogeneous subspace. -/
theorem excludedSpace_isHomogeneous : (K).IsHomogeneous ℳ := by
  intro d x hx
  change eSum Q S • (decompose ℳ x d : M) = 0
  rw [← decompose_smul_of_mem_zero ℳ (show eSum Q S ∈ G.grade μ 0 from Submodule.sum_mem _ fun i _ => G.e_mem_grade i)]
  change eSum Q S • x = 0 at hx
  simp [hx]

variable {T : Type w} [Ring T] [Algebra k T] (𝒯 : ℤ → Submodule k T)
  (π : KLRAlgebra k Q μ →ₐ[k] T) (σ : T →ₐ[k] Module.End k (M ⧸ excludedSpace (Algebra.lsmul k k M (A := KLRAlgebra k Q μ)) S))
  (hact : ∀ a m, σ (π a) ((excludedSpace (Algebra.lsmul k k M (A := KLRAlgebra k Q μ)) S).mkQ m) =
    (excludedSpace (Algebra.lsmul k k M (A := KLRAlgebra k Q μ)) S).mkQ (a • m))
  (hlift : ∀ d t, t ∈ 𝒯 d → ∃ a ∈ G.grade μ d, π a = t)

/-- The finite graded module obtained from a descended action. Degreewise
lifting along the algebra projection and the intertwining of the quotient
map suffice. -/
def orderedShuffleGFin [FiniteDimensional k M] : GFin 𝒯 := by
  let : Module T W := Module.compHom W σ.toRingHom
  let : IsScalarTower k T W := ⟨fun c t x => by
    change σ (c • t) x = c • σ t x
    rw [map_smul]
    rfl⟩
  let := quotDecomposition ℳ (K) (fun d _ hx => excludedSpace_isHomogeneous G S M ℳ d hx)
  let : SetLike.GradedSMul 𝒯 𝓦 := ⟨fun i j t y ht hy => by
    obtain ⟨a,ha,rfl⟩ := hlift i t ht
    obtain ⟨x,hx,rfl⟩ := Submodule.mem_map.mp hy
    exact ⟨a • x,SetLike.GradedSMul.smul_mem (A := G.grade μ) (B := ℳ) ha hx,(hact a x).symm⟩⟩
  let := Module.Finite.of_surjective (K).mkQ (K).mkQ_surjective
  exact {carrier := W,grading := 𝓦}

variable [FiniteDimensional k M]
local notation "D" => orderedShuffleGFin G S M ℳ 𝒯 π σ hact hlift

/-- On each included idempotent sector, projection to the descended module
is an isomorphism of graded vector spaces. -/
def orderedShuffleFixedGradedEquiv (s : Seq μ) (hs : s ∈ S) :
    idem ℳ (e (Q := Q) s) ≃ᵍ[k] idem (D).grading (π (e s)) := by
  let : Module T W := Module.compHom W σ.toRingHom
  let : IsScalarTower k T W := ⟨fun c t x => by
    change σ (c • t) x = c • σ t x
    rw [map_smul]
    rfl⟩
  change idem ℳ (e (Q := Q) s) ≃ᵍ[k] idem 𝓦 (π (e s))
  have ha (x : M) : π (e s) • ((K).mkQ x : W) = (K).mkQ (e s • x) := hact _ _
  have hP (m : idemSubspace k M (e (Q := Q) s)) : (ρ) (eSum Q S) m = m := by
    change eSum Q S • m.1 = m.1
    rw [← show (e s : Aff) • m.1 = m.1 from m.2, ← mul_smul, eSum_mul_e, ite_eq_left hs]
  let f : idemSubspace k M (e (Q := Q) s) →ₗ[k] idemSubspace k W (π (e s)) :=
    { toFun := fun x => ⟨(K).mkQ x.1, (ha _).trans (congrArg (K).mkQ x.2)⟩
      map_add' _ _ := Subtype.ext (map_add _ _ _)
      map_smul' _ _ := Subtype.ext (map_smul _ _ _) }
  have hinj : Function.Injective f := fun x y he => Subtype.ext
    (orderedShuffle_mkQ_injOn (ρ) S (hP x) (hP y) (congrArg Subtype.val he))
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨m,hm⟩ := (K).mkQ_surjective y.1
    refine ⟨⟨(e s : Aff) • m,by change (e s : Aff) • ((e s : Aff) • m) = _; rw [← mul_smul,e_mul_self]⟩,Subtype.ext ?_⟩
    change (K).mkQ ((e s : Aff) • m) = y.1
    rw [← ha,hm]
    exact y.2
  let g := LinearEquiv.ofBijective f ⟨hinj,hsurj⟩
  refine ⟨g,fun _ x hx => ⟨x.1,hx,rfl⟩,?_⟩
  intro d y hy
  obtain ⟨m,hm,he⟩ := Submodule.mem_map.mp (show (y.1 : W) ∈ 𝓦 d from hy)
  let x : idemSubspace k M (e (Q := Q) s) := ⟨(e s : Aff) • m,by
    change (e s : Aff) • ((e s : Aff) • m) = _
    rw [← mul_smul,e_mul_self]⟩
  have hx : g x = y := Subtype.ext (by
    change (K).mkQ ((e s : Aff) • m) = y.1
    exact (ha m).symm.trans ((congrArg (π (e s) • ·) he).trans y.2))
  change g.symm y ∈ idem ℳ (e (Q := Q) s) d
  rw [← hx,g.symm_apply_apply]
  change (e s : Aff) • m ∈ ℳ d
  simpa using SetLike.GradedSMul.smul_mem (A := G.grade μ) (B := ℳ) (G.e_mem_grade s) hm

end Categorification.Stendhal
