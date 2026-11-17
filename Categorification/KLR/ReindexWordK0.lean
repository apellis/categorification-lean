/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Prop32Mult
import Categorification.KLR.GradeTransfer
import Categorification.KLR.Reindex
import Categorification.Algebra.Graded.K0Map

/-!
# Relabelling word projectives on affine Grothendieck groups

For the black action of Webster, arXiv:1309.3796v2, §4.6 and Theorem 4.38,
injectively relabelling the colours identifies the projective classes on black
words with the same word classes in the augmented KLR algebra.
-/
noncomputable section
namespace Categorification.KLR.GradingDatum
open KLRAlgebra Categorification.Graded
universe u
variable {I J : Type u} {k : Type*} [CommRing k] [DecidableEq I] [DecidableEq J]
  {f : I → J} (hf : Function.Injective f) {Q : J → J → MvPolynomial (Fin 2) k}
  (G : GradingDatum (fun i j => Q (f i) (f j))) (H : GradingDatum Q)
  (hx : ∀ i, G.degX i = H.degX (f i)) (hψ : ∀ i j, G.degΨ i j = H.degΨ (f i) (f j))
  (ν : Multiset I)
local notation "σ" => reindexEquiv hf Q ν

include hx hψ in
theorem reindex_grade {d : ℤ} {z} (hz : z ∈ G.grade ν d) :
    σ z ∈ H.grade (ν.map f) d := by
  apply grade_transfer G (H.grade _) SetLike.GradedOne.one_mem
    (fun a b => SetLike.GradedMul.mul_mem a b) (σ).toAlgHom _ _ _ hz
  · intro s
    change σ (e s) ∈ _
    rw [reindexEquiv_e]
    exact H.e_mem_grade _
  · intro a s
    change σ (x a * e s) ∈ _
    rw [map_mul, reindexEquiv_x, reindexEquiv_e, hx]
    exact H.x_mul_e_mem_grade _ _
  · intro j s
    change σ (ψ j * e s) ∈ _
    rw [map_mul, reindexEquiv_ψ, reindexEquiv_e]
    have h := H.ψ_mul_e_mem_grade' j (Seq.map f s)
    by_cases hj : j + 1 < ν.card
    · rw [G.dψ_of_lt hj, hψ]
      rw [H.dψ_of_lt (by simpa using hj)] at h
      exact h
    · simpa [dψ, hj] using h

include hx hψ in
private theorem reindex_grade_symm {d : ℤ} {z} (hz : z ∈ H.grade (ν.map f) d) :
    (σ).symm z ∈ G.grade ν d :=
  (GradedEquiv.ofPreserves (ℳ := G.grade ν) (𝒩 := H.grade (ν.map f)) (σ).toLinearEquiv
    (fun _ _ h => reindex_grade hf G H hx hψ ν h)).symm_map_mem' hz

variable {F : Type*} [Field F] {P : J → J → MvPolynomial (Fin 2) F}
  (D : GradingDatum (fun i j => P (f i) (f j))) (E : GradingDatum P)
  (hd : ∀ i, D.degX i = E.degX (f i)) (hc : ∀ i j, D.degΨ i j = E.degΨ (f i) (f j))
local notation "R" => LaurentPolynomial ℤ

private def reindexBlockK0 (β : Multiset I) : K0 (D.grade β) →ₗ[R] K0 (E.grade (β.map f)) :=
  K0.map (𝒜 := D.grade β) (𝒜' := E.grade (β.map f)) (reindexEquiv hf P β)
    (fun _ _ h => reindex_grade_symm hf D E hd hc β h)

/-- The linear map on the direct sum induced by injecting the set of colours. -/
def reindexWordK0 : D.K0R →ₗ[R] E.K0R :=
  DirectSum.toModule R _ _ fun β => DirectSum.lof R _ E.K0fam (β.map f) ∘ₗ
    reindexBlockK0 hf D E hd hc β

theorem reindexWordK0_clsW (w : List I) :
    reindexWordK0 hf D E hd hc (D.clsW w) = E.clsW (w.map f) := by
  let β := (w : Multiset I)
  let s := Seq.ofList w (rfl : (w : Multiset I) = β)
  let rename := reindexEquiv hf P β
  have hν : (w.map f : Multiset J) = β.map f := rfl
  have hseq : Seq.map f s = Seq.ofList (w.map f) hν := by
    apply Subtype.ext
    funext a
    change f (w[a.val]'(by simpa [β] using a.isLt)) = (w.map f)[a.val]'(by simpa [β] using a.isLt)
    simp
  rw [D.clsW_eq w (rfl : (w : Multiset I) = β), E.clsW_eq _ hν]
  change reindexWordK0 hf D E hd hc (DirectSum.lof R _ D.K0fam β _) = _
  rw [reindexWordK0, DirectSum.toModule_lof, LinearMap.comp_apply]
  apply congrArg (DirectSum.lof R _ E.K0fam (β.map f))
  let t := Seq.map f s
  let eqv : leftIdeal (e (Q := fun i j => P (f i) (f j)) s) ≃+ leftIdeal (e (Q := P) t) :=
    { toFun := fun x => ⟨rename x.val, by rw [mem_leftIdeal, ← reindexEquiv_e hf, ← map_mul, mem_leftIdeal.mp x.2]⟩
      invFun := fun y => ⟨rename.symm y.val, rename.injective (by rw [map_mul, rename.apply_symm_apply, reindexEquiv_e]; exact y.2)⟩
      left_inv x := Subtype.ext (rename.symm_apply_apply _)
      right_inv y := Subtype.ext (rename.apply_symm_apply _)
      map_add' x y := Subtype.ext (map_add rename x.val y.val) }
  rw [← hseq]
  exact K0.map_of_semilinear rename _ (D.projP s) (E.projP t) eqv
    (fun c x => Subtype.ext (map_mul rename c x.val))
    (fun _ _ h => reindex_grade hf D E hd hc β h)
    (fun _ _ h => reindex_grade_symm hf D E hd hc β h)
end Categorification.KLR.GradingDatum
