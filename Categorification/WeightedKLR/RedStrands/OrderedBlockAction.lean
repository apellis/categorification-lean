/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBlockAction
import Categorification.WeightedKLR.RedStrands.BraidedRelabel
import Categorification.WeightedKLR.RedStrands.BlackIdempotent

/-!
# Ordered tensor product algebras acting on the adjacent-block column

Webster, arXiv:1309.3796v2, §5.1 after Definition 5.4 and §6.1, Lemma 6.8.
Restrict the juxtaposition action to the diagonal red order in each factor. The source is
now literally the external tensor product of Webster's `TensorProductAlgebra`s. The unit
projects onto the ordered summand, on which this action is unital. Relabelling the factors
allows either order of the paired weights on the same ordinary diagram quotient.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR TypeA BraidedStendhalAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)

section Diagonal
variable (ν : Multiset I)
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "P" => redProj k Q Λ ν (List.finRange ℓ)
local notation "hp" => isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.finRange ℓ)
local notation "hpv" => IsIdempotentElem.map hp (violMk k Q Λ ν)
private theorem canReduced (n : ℕ) : IsReducedChoice (canWord n) :=
  fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩

/-- The diagonal identification with Webster's tensor product algebra preserves scalars. -/
private def diagonalEquiv : (hpv).Corner ≃ₐ[k] T := by
  apply AlgEquiv.ofRingEquiv (f := violCornerEquiv (Λ := Λ) (ν := ν) (canReduced _) hQ)
  intro c
  have hv : algebraMap k (hpv).Corner c = violCornerHom k Q Λ ν (algebraMap k (hp).Corner c) :=
    Subtype.ext (show c • violMk k Q Λ ν P = violMk k Q Λ ν (c • P) from (map_smul _ _ _).symm)
  rw [hv, violCornerEquiv_violCornerHom, ← (TensorProductAlgebra.mk Q Λ ν).commutes c]
  apply congrArg; apply Subtype.ext
  change toAllOrders k Q Λ ν (c • P) = c • StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
  rw [map_smul, redProj, toAllOrders_redIdem]

/-- Regard a tensor product algebra diagram as a diagonal diagram in the local braided algebra. -/
private def diagonalValue : T →ₙₐ[k] ViolQuotient k Q Λ ν where
  toFun x := ((diagonalEquiv Q Λ hQ ν).symm x).1
  map_mul' x y := congrArg Subtype.val (map_mul (diagonalEquiv Q Λ hQ ν).symm x y)
  map_add' x y := congrArg Subtype.val (map_add (diagonalEquiv Q Λ hQ ν).symm x y)
  map_zero' := congrArg Subtype.val (map_zero (diagonalEquiv Q Λ hQ ν).symm)
  map_smul' c x := congrArg Subtype.val (map_smul (diagonalEquiv Q Λ hQ ν).symm c x)

private theorem diagonalValue_one : diagonalValue Q Λ hQ ν 1 = violMk k Q Λ ν P :=
  congrArg Subtype.val (map_one (diagonalEquiv Q Λ hQ ν).symm)

private theorem diagonalValue_ofKLR
    (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
    (ha : ofKLR k Q Λ ν a ∈ Subsemigroup.corner P) :
    diagonalValue Q Λ hQ ν (tensorOfKLR Q Λ ν a) =
      violMk k Q Λ ν (ofKLR k Q Λ ν a) := by
  let x : (hp).Corner := ⟨ofKLR k Q Λ ν a, ha⟩
  have hr : ofKLR k Q Λ ν a * P = ofKLR k Q Λ ν a :=
    ((Subsemigroup.mem_corner_iff hp).1 ha).2
  have hx : diagonalEquiv Q Λ hQ ν (violCornerHom k Q Λ ν x) = tensorOfKLR Q Λ ν a := by
    change violCornerEquiv (canReduced _) hQ _ = _
    rw [violCornerEquiv_violCornerHom]
    apply congrArg (TensorProductAlgebra.mk Q Λ ν)
    apply Subtype.ext
    rw [identityCornerHom_val]
    change toAllOrders k Q Λ ν (ofKLR k Q Λ ν a) =
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν a *
        StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
    rw [← toAllOrders_ofKLR, ← toAllOrders_redIdem, ← map_mul]
    exact (congrArg (toAllOrders k Q Λ ν) hr).symm
  change ((diagonalEquiv Q Λ hQ ν).symm (tensorOfKLR Q Λ ν a)).1 = _
  rw [← hx, AlgEquiv.symm_apply_apply, violCornerHom_val]

end Diagonal

variable (σ : (B : RedBlock I ℓ) → Equiv.Perm (Fin B.size))

/-- The ordered local algebras, tensored over `k`. -/
abbrev orderedProduct := external (fun B : RedBlock I ℓ => AlgCat.of k
  (TensorProductAlgebra k Q ((Λ ∘ B.label) ∘ σ B) B.black))

/-- A local ordered diagram in the violated quotient, after relabelling its red strands. -/
def orderedValue (B : RedBlock I ℓ) :
    TensorProductAlgebra k Q ((Λ ∘ B.label) ∘ σ B) B.black →ₙₐ[k] quotientAlgebra Q Λ B :=
  (violRedPermEquiv (Λ := Λ ∘ B.label) (σ B) (fun _ => rfl)).toAlgHom.toNonUnitalAlgHom.comp
    (diagonalValue Q _ hQ B.black)

theorem orderedValue_one (B : RedBlock I ℓ) : orderedValue Q Λ hQ σ B 1 =
    violMk k Q (Λ ∘ B.label) B.black
      (redProj k Q (Λ ∘ B.label) B.black ((List.finRange B.size).map (σ B))) := by
  change violRedPermEquiv _ _ (diagonalValue Q _ hQ B.black 1) = _
  rw [diagonalValue_one, violRedPermEquiv_violMk, redPermAlgEquiv_redProj]

private theorem orderedValue_ofKLR (B : RedBlock I ℓ)
    (a : KLRAlgebra k (stendhalQ Q ((Λ ∘ B.label) ∘ σ B)) B.localWeight)
    (ha : ofKLR k Q ((Λ ∘ B.label) ∘ σ B) B.black a ∈
      Subsemigroup.corner (redProj k Q ((Λ ∘ B.label) ∘ σ B) B.black (List.finRange B.size))) :
    orderedValue Q Λ hQ σ B (tensorOfKLR Q ((Λ ∘ B.label) ∘ σ B) B.black a) =
      violMk k Q (Λ ∘ B.label) B.black
        (redPermAlgEquiv (σ B) (fun _ => rfl) (ofKLR k Q ((Λ ∘ B.label) ∘ σ B) B.black a)) := by
  change (violRedPermEquiv (σ B) (fun _ => rfl))
    (diagonalValue Q ((Λ ∘ B.label) ∘ σ B) hQ B.black
      (tensorOfKLR Q ((Λ ∘ B.label) ∘ σ B) B.black a)) = _
  rw [diagonalValue_ofKLR Q ((Λ ∘ B.label) ∘ σ B) hQ B.black _ ha]
  exact violRedPermEquiv_violMk (Λ := Λ ∘ B.label) (Λ' := (Λ ∘ B.label) ∘ σ B)
    (σ B) (fun _ => rfl) (ofKLR k Q _ B.black a)

section IdentityGenerators

open KLRAlgebra

/-- An identity-order loading idempotent in the ordered algebra includes as the same
loading idempotent in the local violated braided quotient. -/
theorem orderedValue_identity_e (B : RedBlock I ℓ) (s : Seq B.localWeight)
    (hs : redWord s = List.finRange B.size) :
    orderedValue Q Λ hQ (fun _ => 1) B (tensorOfKLR Q (Λ ∘ B.label) B.black (e s)) =
      violMk k Q (Λ ∘ B.label) B.black (ofKLR k Q (Λ ∘ B.label) B.black (e s)) := by
  let W := Λ ∘ B.label
  let W' := W ∘ (1 : Equiv.Perm (Fin B.size))
  have ha : ofKLR k Q W' B.black (e s) ∈
      Subsemigroup.corner (redProj k Q W' B.black (List.finRange B.size)) :=
    (Subsemigroup.mem_corner_iff (isIdempotentElem_redProj _)).2
      ⟨by rw [redProj_mul_e, ite_eq_left hs], by rw [e_mul_redProj, ite_eq_left hs]⟩
  refine (orderedValue_ofKLR Q Λ hQ (fun _ => 1) B (e s) ha).trans ?_
  apply congrArg (violMk k Q W B.black)
  calc
    _ = ofKLR k Q W B.black (e (Seq.redPerm 1 s)) := redPermAlgEquiv_e 1 (fun _ => rfl) s
    _ = ofKLR k Q W B.black (e s) := by rw [Seq.redPerm_one]

/-- An elementary crossing whose two loadings have identity red order includes as the
same crossing with its bottom idempotent in the local violated braided quotient. -/
theorem orderedValue_identity_ψ_mul_e (B : RedBlock I ℓ) (a : ℕ) (t : Seq B.localWeight)
    (ht : redWord t = List.finRange B.size)
    (hs : redWord (sadj B.localWeight.card a • t) = List.finRange B.size) :
    orderedValue Q Λ hQ (fun _ => 1) B (tensorOfKLR Q (Λ ∘ B.label) B.black (ψ a * e t)) =
      violMk k Q (Λ ∘ B.label) B.black (ofKLR k Q (Λ ∘ B.label) B.black (ψ a * e t)) := by
  let W := Λ ∘ B.label
  let W' := W ∘ (1 : Equiv.Perm (Fin B.size))
  let F := ofKLR k Q W' B.black
  have ha : F (ψ a * e t) ∈
      Subsemigroup.corner (redProj k Q W' B.black (List.finRange B.size)) := by
    apply (Subsemigroup.mem_corner_iff (isIdempotentElem_redProj _)).2
    constructor
    · change _ * ofKLR k Q W' B.black (ψ a * e t) = _
      rw [ψ_mul_e, map_mul, ← mul_assoc, redProj_mul_e, ite_eq_left hs]
    · change ofKLR k Q W' B.black (ψ a * e t) * _ = _
      rw [map_mul, mul_assoc, e_mul_redProj, ite_eq_left ht]
  refine (orderedValue_ofKLR Q Λ hQ (fun _ => 1) B (ψ a * e t) ha).trans ?_
  apply congrArg (violMk k Q W B.black)
  let r := redPermAlgEquiv (Q := Q) (Λ := W) (Λ' := W') (ν := B.black)
    (1 : Equiv.Perm (Fin B.size)) (fun _ => rfl)
  have hψ : r (F (ψ a)) = ofKLR k Q W B.black (ψ a) := by
    change redPermAlgEquiv _ _ (ofKLR k Q W' B.black (ψ a)) = _
    rw [redPermAlgEquiv, relabelAlgEquiv_ofKLR, relabelHom_ψ]
  have he : r (F (e t)) = ofKLR k Q W B.black (e t) :=
    (redPermAlgEquiv_e 1 (fun _ => rfl) t).trans
      (congrArg (fun s => ofKLR k Q W B.black (e s)) (Seq.redPerm_one t))
  change r (F (ψ a * e t)) = _
  rw [map_mul F, map_mul r, hψ, he, map_mul]

end IdentityGenerators

/-- Cut a diagram down to its diagonal ordered algebra, retaining both order projectors. -/
def orderedRetraction (B : RedBlock I ℓ) : quotientAlgebra Q Λ B →ₗ[k]
    TensorProductAlgebra k Q ((Λ ∘ B.label) ∘ σ B) B.black := by
  let W := (Λ ∘ B.label) ∘ σ B
  let p := violMk k Q W B.black (redProj k Q W B.black (List.finRange B.size))
  let hp : IsIdempotentElem p := (isIdempotentElem_redProj _).map _
  let cut : ViolQuotient k Q W B.black →ₗ[k] hp.Corner :=
    { toFun := fun x => ⟨p * x * p, x, rfl⟩
      map_add' := fun x y => Subtype.ext (by simp only [mul_add, add_mul]; rfl)
      map_smul' := fun c x => Subtype.ext (by simp only [mul_smul_comm, smul_mul_assoc]; rfl) }
  exact (diagonalEquiv Q W hQ B.black).toLinearMap ∘ₗ cut ∘ₗ
    (violRedPermEquiv (Λ := Λ ∘ B.label) (σ B) (fun _ => rfl)).symm.toLinearMap

theorem orderedValue_retraction (B : RedBlock I ℓ) (x : quotientAlgebra Q Λ B) :
    orderedValue Q Λ hQ σ B (orderedRetraction Q Λ hQ σ B x) =
      orderedValue Q Λ hQ σ B 1 * x * orderedValue Q Λ hQ σ B 1 := by
  let g := violRedPermEquiv (Λ := Λ ∘ B.label) (σ B) (fun _ => rfl) (Q := Q) (ν := B.black)
  let d := diagonalEquiv Q ((Λ ∘ B.label) ∘ σ B) hQ B.black
  change g ((d.symm (d _)).1) = g (d.symm 1).1 * x * g (d.symm 1).1
  rw [AlgEquiv.symm_apply_apply, map_one d.symm]
  change g (_ * g.symm x * _) = _
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  rfl

theorem orderedRetraction_value (B : RedBlock I ℓ) (x) :
    orderedRetraction Q Λ hQ σ B (orderedValue Q Λ hQ σ B x) = x := by
  let g := violRedPermEquiv (Λ := Λ ∘ B.label) (σ B) (fun _ => rfl) (Q := Q) (ν := B.black)
  let d := diagonalEquiv Q ((Λ ∘ B.label) ∘ σ B) hQ B.black
  have hi : Function.Injective (orderedValue Q Λ hQ σ B) := fun _ _ he =>
    d.symm.injective (Subtype.ext (g.injective he))
  apply hi
  rw [orderedValue_retraction, ← map_mul, one_mul, ← map_mul, mul_one]

/-- Include every tensor factor in its prescribed red order. -/
def orderedInclusion : (Bs : List (RedBlock I ℓ)) → orderedProduct Q Λ σ Bs →ₙₐ[k] quotients Q Λ Bs
  | [] => (AlgHom.id k _).toNonUnitalAlgHom
  | B :: Bs => by
    let l := orderedValue Q Λ hQ σ B
    let r := orderedInclusion Bs
    let g := TensorProduct.map (LinearMap.ofClass l) (LinearMap.ofClass r)
    refine { toFun := g, map_zero' := map_zero g, map_add' := map_add g,
             map_smul' := map_smul g, map_mul' := ?_ }
    intro x y
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => rw [add_mul, map_add, map_add, add_mul, hx, hz]
    | tmul x z =>
      induction y using TensorProduct.inductionOn with
      | add y w hy hw => rw [mul_add, map_add, map_add, mul_add, hy, hw]
      | tmul y w =>
        simp only [g, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul]
        change l (x*y) ⊗ₜ r (z*w) = (l x*l y) ⊗ₜ (r z*r w)
        rw [map_mul, map_mul]

/-- The tensor of the prescribed local red-order projectors, before imposing violations. -/
def orderedIdem : (Bs : List (RedBlock I ℓ)) → diagrams Q Λ Bs
  | [] => 1
  | B :: Bs => redProj k Q (Λ ∘ B.label) B.black ((List.finRange B.size).map (σ B)) ⊗ₜ orderedIdem Bs

theorem orderedInclusion_one : ∀ Bs, orderedInclusion Q Λ hQ σ Bs 1 =
    projection Q Λ Bs (orderedIdem Q Λ σ Bs)
  | [] => rfl
  | B :: Bs => by
    change TensorProduct.map _ _ ((1 : TensorProductAlgebra k Q ((Λ ∘ B.label) ∘ σ B) B.black) ⊗ₜ
      (1 : orderedProduct Q Λ σ Bs)) = _
    rw [TensorProduct.map_tmul, orderedIdem, projection, Algebra.TensorProduct.map_tmul]
    change violRedPermEquiv (Λ := Λ ∘ B.label) (σ B) (fun _ => rfl) (diagonalValue Q _ hQ B.black 1) ⊗ₜ
      orderedInclusion Q Λ hQ σ Bs 1 = _
    rw [diagonalValue_one, violRedPermEquiv_violMk, redPermAlgEquiv_redProj, orderedInclusion_one Bs]

variable (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
local notation "Bs" => adjacentRow L M f β
variable (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "N" => blockColumn Q Λ L M f β h
local notation "D" => orderedProduct Q Λ σ Bs
local notation "A" => NonUnitalAlgHom.comp (AlgHom.toNonUnitalAlgHom (blockProductAction Q Λ L M f β h))
  (orderedInclusion Q Λ hQ σ Bs)

/-- The summand of the block column with the specified internal red order. -/
def orderedColumn : Submodule k N := LinearMap.range (A 1)

/-- The ordered column is the image of stacking the tensor of the local red-order projectors. -/
theorem orderedColumn_eq : orderedColumn Q Λ hQ σ L M f β h = LinearMap.range
    (blockProductAction Q Λ L M f β h (projection Q Λ Bs (orderedIdem Q Λ σ Bs))) := by
  change LinearMap.range (blockProductAction Q Λ L M f β h (orderedInclusion Q Λ hQ σ Bs 1)) = _
  rw [orderedInclusion_one]

private def onUnitRange {R E : Type*} [Ring R] [Algebra k R] [AddCommGroup E] [Module k E]
    (g : R →ₙₐ[k] Module.End k E) : R →ₐ[k] Module.End k (LinearMap.range (g 1)) where
  toFun x := (g x).restrict fun z _ => by
    refine ⟨g x z, ?_⟩
    change (g 1 * g x) z = _
    rw [← map_mul, one_mul]
  map_zero' := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    exact congrFun (congrArg DFunLike.coe (map_zero g)) z.1
  map_add' x y := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    exact congrFun (congrArg DFunLike.coe (map_add g x y)) z.1
  map_mul' x y := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    exact congrFun (congrArg DFunLike.coe (map_mul g x y)) z.1
  map_one' := by
    apply LinearMap.ext; rintro ⟨_,v,rfl⟩; apply Subtype.ext
    change (g 1 * g 1) v = g 1 v
    rw [← map_mul, one_mul]
  commutes' c := by
    apply LinearMap.ext; rintro ⟨_,v,rfl⟩; apply Subtype.ext
    change g (algebraMap k R c) (g 1 v) = c • g 1 v
    rw [Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.smul_apply,
      ← Module.End.mul_apply, ← map_mul, one_mul]

/-- **Action of the exterior product of the ordered block algebras** (Webster,
arXiv:1309.3796v2, §5.1, partial standardization in Lemma 6.8). On its ordered summand,
`⊗_c T^{λ_c}` acts unitally by horizontal juxtaposition. -/
def orderedBlockAction : D →ₐ[k] Module.End k (orderedColumn Q Λ hQ σ L M f β h) := onUnitRange A

/-- The ordered action is the juxtaposition action of the same diagrams. -/
theorem orderedBlockAction_apply (x : D) (z : orderedColumn Q Λ hQ σ L M f β h) :
    (orderedBlockAction Q Λ hQ σ L M f β h x z).1 =
      blockProductAction Q Λ L M f β h (orderedInclusion Q Λ hQ σ Bs x) z.1 := rfl

local notation "R" => IsIdempotentElem.Corner (bottomIdempotent Q Λ L M f (ν := ν))
local notation "S" => orderedColumn Q Λ hQ σ L M f β h

private def orderedRightSubmodule : Submodule Rᵐᵒᵖ N where
  carrier := S
  zero_mem' := (S).zero_mem
  add_mem' := (S).add_mem
  smul_mem' b _ hz := by
    obtain ⟨v,rfl⟩ := hz
    exact ⟨b • v, blockProductAction_right Q Λ L M f β h _ b v⟩

instance orderedRightModule : Module Rᵐᵒᵖ S :=
  inferInstanceAs (Module Rᵐᵒᵖ (orderedRightSubmodule Q Λ hQ σ L M f β h))

instance orderedLeftModule : Module D S := Module.compHom _ (orderedBlockAction Q Λ hQ σ L M f β h).toRingHom

/-- Top juxtaposition and bottom stacking make each ordered column a bimodule
(Webster, arXiv:1309.3796v2, §5.1 after Definition 5.4 and the ordinary step of
Lemma 6.8). Matching red orders give the partial-standardization column; the exchanged
top order gives the crossing column, not an identification of the two tensor functors. -/
instance orderedColumn_smulCommClass : SMulCommClass D Rᵐᵒᵖ S where
  smul_comm x b z := Subtype.ext (blockProductAction_right Q Λ L M f β h
    (orderedInclusion Q Λ hQ σ Bs x) b z.1)

end Categorification.Stendhal.RedBlock
