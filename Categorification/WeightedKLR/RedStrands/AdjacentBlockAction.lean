/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBlockRow
import Categorification.WeightedKLR.RedStrands.BlockDiagramProduct
import Categorification.WeightedKLR.RedStrands.AdjacentBlockTensor

/-!
# The adjacent-block action on the ordinary diagram quotient

Webster, arXiv:1309.3796v2, §5.1 after Definition 5.4 and §6.1, Lemma 6.8.
The external product of the local violated quotients acts by horizontal juxtaposition
followed by top multiplication. It acts on the column with a fixed bottom red order
modulo the higher cuts of that very order. Both orders of the local two-red algebra are
retained, so its off-diagonal diagrams include the local braiding bimodule.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra BraidedStendhalAlgebra

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
local notation "Bs" => adjacentRow L M f β
local notation "κ₀" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "κ₁" => L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst
local notation "α" => fun r i => boundaryCount (cut (f 0) (f 1) r) i Bs
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1) α κ₀
local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)
local notation "p" => violMk k Q Λ ν (redProj k Q Λ ν κ₀)
variable (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)

/-- Stack a juxtaposition in the ambient violated quotient, before imposing the higher cuts. -/
def stackBlocks : diagrams Q Λ Bs →ₙₐ[k] V where
  toFun x := π (castKLR (stendhalQ Q Λ) h (juxtapose Q Λ Bs x))
  map_zero' := by simp only [map_zero]
  map_add' x y := by simp only [map_add]
  map_smul' c x := by simp only [map_smul, MonoidHom.id_apply]
  map_mul' x y := by simp only [juxtapose_mul, map_mul]

local notation "F" => stackBlocks Q Λ L M f β h

theorem stackBlocks_loadingIdem (s : Loadings Bs) :
    F (loadingIdem Q Λ Bs s) = π (e (Seq.cast h (place Bs s))) := by
  change π (castKLR _ h _) = _
  rw [juxtapose_loadingIdem, castKLR_e]

/-- Diagrams with a juxtaposed top and bottom order `κ₀`, modulo the bottom-order higher
block relations. The range is taken from the original violated algebra, before quotienting. -/
def blockColumn : Submodule k (J).ringCon.Quotient :=
  LinearMap.range ((q).toLinearMap ∘ₗ LinearMap.mulLeft k (F 1) ∘ₗ LinearMap.mulRight k p)

local notation "N" => blockColumn Q Λ L M f β h

private def stackEnd (x : diagrams Q Λ Bs) : Module.End k N :=
  (LinearMap.mulLeft k (q (F x))).restrict fun z hz => by
    obtain ⟨v,rfl⟩ := hz
    refine ⟨F x * v, ?_⟩
    change q (F 1 * (F x * v * p)) = q (F x) * q (F 1 * (v * p))
    rw [← map_mul, mul_assoc (F x) v p, ← mul_assoc (F 1) (F x), ← mul_assoc (F x) (F 1),
      ← map_mul, ← map_mul, one_mul, mul_one]

private def stackAction : diagrams Q Λ Bs →ₐ[k] Module.End k N where
  toFun := stackEnd Q Λ L M f β h
  map_one' := by
    apply LinearMap.ext; rintro ⟨_,v,rfl⟩; apply Subtype.ext
    change q (F 1) * q (F 1 * (v*p)) = q (F 1 * (v*p))
    rw [← map_mul, ← mul_assoc, ← map_mul, one_mul]
  map_zero' := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    change q (F 0) * z.1 = 0
    rw [map_zero F, map_zero (q), zero_mul]
  map_add' x y := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    change q (F (x+y)) * z.1 = q (F x) * z.1 + q (F y) * z.1
    rw [map_add, map_add, add_mul]
  map_mul' x y := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    change q (F (x*y)) * z.1 = q (F x) * (q (F y) * z.1)
    rw [map_mul, map_mul, mul_assoc]
  commutes' c := by
    apply LinearMap.ext; rintro ⟨_,v,rfl⟩; apply Subtype.ext
    change q (F (algebraMap k _ c)) * q (F 1 * (v*p)) = c • q (F 1 * (v*p))
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, smul_mul_assoc, ← map_mul,
      ← mul_assoc, ← map_mul, one_mul]

private theorem stackAction_violated (s : Loadings Bs) (hv : Violated Bs s) :
    stackAction Q Λ L M f β h (loadingIdem Q Λ Bs s) = 0 := by
  let t := Seq.cast h (place Bs s)
  have ho := redWord_place_adjacent L M f β h s
  have hn : (κ₀).Nodup := by
    rcases ho with ho | ho
    · exact ho ▸ redWord_nodup t
    · exact ((List.Perm.swap (f 0) (f 1) (M.map Prod.fst)).append_left (L.map Prod.fst)).nodup_iff.1
        (ho ▸ redWord_nodup t)
  have hu := root_lt_of_violated h (aligned_adjacent L M f β hn) s hv
  apply LinearMap.ext; rintro ⟨_,v,rfl⟩; apply Subtype.ext
  change q (F (loadingIdem Q Λ Bs s)) * q (F 1 * (v*p)) = 0
  rw [stackBlocks_loadingIdem, ← map_mul, ← mul_assoc (F 1), ← mul_assoc]
  change (J).ringCon.mk' (π (e t) * (F 1 * v) * p) = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  rcases ho with ho | ho
  · exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_right _ _ _
      (TwoSidedIdeal.subset_span ⟨t,ho,hu,rfl⟩))
  · exact higher_loading_mul_order_mem ho hu _

/-- A locally violated loading acts by zero even when its juxtaposition has no black strand
to the left of the first global red (Webster, §5.1 and the slide in Lemma 6.8). -/
theorem stackBlocks_violated_mul (s : Loadings Bs) (hv : Violated Bs s) (z : N) :
    q (F (loadingIdem Q Λ Bs s)) * z.1 = 0 :=
  congrArg Subtype.val (LinearMap.congr_fun (stackAction_violated Q Λ L M f β h s hv) z)

/-- **The action by horizontal juxtaposition** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.8). A local violation in either order of the two-red block acts by zero on the
ordinary column; the relation in the opposite order is moved to the bottom by the slide. -/
def blockProductAction : quotients Q Λ Bs →ₐ[k] Module.End k N :=
  (exists_factor (C := Module.End k N) Q Λ Bs (stackAction Q Λ L M f β h) (stackAction_violated Q Λ L M f β h)).choose

/-- On representatives the action is left multiplication by the juxtaposition, with no
choice of a representative in the global column. -/
theorem blockProductAction_projection (x : diagrams Q Λ Bs) (z : N) :
    (blockProductAction Q Λ L M f β h (projection Q Λ Bs x) z).1 = q (F x) * z.1 := by
  rw [blockProductAction, (exists_factor (C := Module.End k N) Q Λ Bs _ (stackAction_violated Q Λ L M f β h)).choose_spec]
  rfl

/-- The idempotent of the ordered bottom of the block column. -/
theorem bottomIdempotent : IsIdempotentElem p := (isIdempotentElem_redProj κ₀).map _
local notation "hp" => bottomIdempotent (k := k) Q Λ L M f (ν := ν)

/-- The right action of the bottom-order corner on partial standardization (Webster,
arXiv:1309.3796v2, §5.1, Definition 5.4). It is stacking at the bottom, in the same
quotient as the external action, not a right action transported by a vector-space isomorphism. -/
instance columnRightModule : Module (hp).Cornerᵐᵒᵖ N where
  smul b z := ⟨z.1 * q b.unop.1, by
    obtain ⟨v,hv⟩ := z.2
    refine ⟨v * b.unop.1, ?_⟩
    rw [← hv]
    change q (F 1 * (v * b.unop.1 * p)) = q (F 1 * (v * p)) * q b.unop.1
    obtain ⟨hl,hr⟩ := (Subsemigroup.mem_corner_iff hp).1 b.unop.2
    rw [← map_mul, mul_assoc v, hr, mul_assoc, mul_assoc, hl]⟩
  one_smul z := Subtype.ext (by
    obtain ⟨v,hv⟩ := z.2
    change z.1 * q p = z.1
    rw [← hv]; change q (F 1 * (v*p)) * q p = q (F 1 * (v*p))
    rw [← map_mul, mul_assoc, mul_assoc, (hp).eq])
  mul_smul b c z := Subtype.ext (by
    change z.1 * q (c.unop.1 * b.unop.1) = z.1 * q c.unop.1 * q b.unop.1
    rw [map_mul, mul_assoc])
  smul_zero b := Subtype.ext (zero_mul _)
  smul_add b x y := Subtype.ext (add_mul _ _ _)
  zero_smul z := Subtype.ext (by change z.1 * q 0 = 0; rw [map_zero (q), mul_zero])
  add_smul b c z := Subtype.ext (by
    change z.1 * q (b.unop.1 + c.unop.1) = z.1 * q b.unop.1 + z.1 * q c.unop.1
    rw [map_add, mul_add])

/-- Juxtaposing on top commutes with the right action of the full bottom-order algebra. -/
theorem blockProductAction_right (x : quotients Q Λ Bs) (b : (hp).Cornerᵐᵒᵖ) (z : N) :
    blockProductAction Q Λ L M f β h x (b • z) = b • blockProductAction Q Λ L M f β h x z := by
  obtain ⟨y,rfl⟩ := projection_surjective Q Λ Bs x
  apply Subtype.ext
  change _ = (blockProductAction Q Λ L M f β h _ z).1 * q b.unop.1
  rw [blockProductAction_projection, blockProductAction_projection]
  exact (mul_assoc _ _ _).symm

/-- The loading summand cut out by the *external* tensor of local idempotents. -/
def loadingSummand (s : Loadings Bs) : Submodule k (J).ringCon.Quotient :=
  LinearMap.range ((N).subtype ∘ₗ blockProductAction Q Λ L M f β h
    (projection Q Λ Bs (loadingIdem Q Λ Bs s)))

private theorem loadingSummand_eq (s : Loadings Bs) :
    loadingSummand Q Λ L M f β h s = LinearMap.range
      ((q).toLinearMap ∘ₗ LinearMap.mulLeft k (π (e (Seq.cast h (place Bs s)))) ∘ₗ
        LinearMap.mulRight k p) := by
  let u := loadingIdem Q Λ Bs s
  have he : F u * F 1 = F u := by rw [← map_mul, mul_one]
  rw [← stackBlocks_loadingIdem Q Λ L M f β h s]
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩
    obtain ⟨v,hv⟩ := z.property
    refine ⟨v,?_⟩
    change q (F u * (v*p)) = (blockProductAction Q Λ L M f β h (projection Q Λ Bs u) z).1
    rw [blockProductAction_projection, ← hv]
    change _ = q (F u) * q (F 1 * (v*p))
    rw [← map_mul, ← mul_assoc (F u) (F 1), he]
  · rintro _ ⟨v,rfl⟩
    let z : N := ⟨q (F 1 * (v*p)),v,rfl⟩
    refine ⟨z,?_⟩
    change (blockProductAction Q Λ L M f β h (projection Q Λ Bs u) z).1 = q (F u * (v*p))
    rw [blockProductAction_projection]
    change q (F u) * q (F 1 * (v*p)) = _
    rw [← map_mul, ← mul_assoc (F u) (F 1), he]

/-- **The fixed-top ordinary tensor as a summand of the block action** (Webster,
arXiv:1309.3796v2, proof of Lemma 6.8). At a nonviolated tuple in the exchanged top
order, the ordinary quotient tensor of `blockTensorEquiv` is precisely the image of the
corresponding tensor of local loading idempotents acting on the column. -/
def blockTensorLoadingEquiv (s : Loadings Bs) (hs : ¬ Violated Bs s)
    (ht : redWord (Seq.cast h (place Bs s)) = κ₁) :
    let t := Seq.cast h (place Bs s)
    (_ ⧸ blockTensorRelations k Q Λ (L.map Prod.fst) (M.map Prod.fst) (f 0) (f 1) t) ≃ₗ[k]
      loadingSummand Q Λ L M f β h s := by
  let t := Seq.cast h (place Bs s)
  have hn : (κ₀).Nodup :=
    ((List.Perm.swap (f 0) (f 1) (M.map Prod.fst)).append_left (L.map Prod.fst)).nodup_iff.1
      (ht ▸ redWord_nodup t)
  have ha : adjacentBlockRoot (f 0) (f 1) t = α := by
    funext r i
    change blockBlackCount (Seq.cast h (place Bs s)) (cut (f 0) (f 1) r) i = _
    have hc {u w : Multiset (I ⊕ Fin ℓ)} (e : u = w) (z : Seq u) (C : Finset (Fin ℓ)) :
        blockBlackCount (Seq.cast e z) C i = blockBlackCount z C i := by subst w; rfl
    rw [hc]; exact count_place_of_not_violated r i s (aligned_adjacent L M f β hn) hs
  have compare : blockQuotientCorner k Q Λ (L.map Prod.fst) (M.map Prod.fst) (f 0) (f 1) t ≃ₗ[k]
      loadingSummand Q Λ L M f β h s := by
    unfold blockQuotientCorner
    rw [ha, loadingSummand_eq]
  exact (blockTensorEquiv k Q Λ (L.map Prod.fst) (M.map Prod.fst) (f 0) (f 1) t ht).trans compare

end Categorification.Stendhal.RedBlock
