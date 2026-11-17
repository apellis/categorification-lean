/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicGrading

/-!
# Dimensions of cyclotomic quotients by degree

Kang–Kashiwara, arXiv:1102.4677v4, §4.1, Definition 4.1, and Khovanov–Lauda I,
arXiv:0803.4121v2, Theorem 2.5. The cyclotomic ideal is spanned by the products
of two ordinary basis terms with a cyclotomic generator inserted between them.
Retaining the products in degree `d` gives a finite family. The degree-`d` dimension of
the quotient is the number of ordinary basis terms in that degree minus the rank
of these relations in the ordinary KLR algebra, including interacting and repeated
colours. This calculation uses the undeformed cyclotomic polynomial `X ^ Λ i`.
-/

namespace Categorification.KLR.CycKLR

open KLRAlgebra Categorification.Graded Equiv TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}
  (G : GradingDatum Q) (Λ : I → ℕ)
  (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)

local notation "aΛ" => (fun i => Polynomial.X ^ Λ i : I → Polynomial k)
local notation "R" => KLRAlgebra k Q ν
local notation "Std" => Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)

/-- A product with a first-dot cyclotomic generator inserted between two standard diagrams. -/
noncomputable def relationTerm (u : Std × Seq ν × Std) : R :=
  stdElt ρ u.1 * cycElt Q aΛ u.2.1 * stdElt ρ u.2.2

/-- Degree of a product through a first-dot cyclotomic generator. -/
noncomputable def relationDegree (u : Std × Seq ν × Std) : ℤ :=
  G.stdDeg ρ u.1 + cycEltDegree G Λ ν u.2.1 + G.stdDeg ρ u.2.2

/-- Products through a cyclotomic generator in the specified degree, in the affine KLR algebra. -/
noncomputable def relationsInGrade (d : ℤ) : Set R :=
  relationTerm (Q := Q) Λ ρ '' {u | relationDegree G Λ ρ u = d}

private theorem relationTerm_mem_grade (u : Std × Seq ν × Std) :
    relationTerm (Q := Q) Λ ρ u ∈ G.grade ν (relationDegree G Λ ρ u) :=
  SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem (G.stdElt_mem_grade ρ u.1)
    (cycElt_mem_grade G Λ ν u.2.1)) (G.stdElt_mem_grade ρ u.2.2)

include hρ in
private theorem ker_mk_eq_span_relationTerm :
    LinearMap.ker (mk k Q aΛ ν).toLinearMap =
      Submodule.span k (Set.range (relationTerm (Q := Q) Λ ρ)) := by
  let V := Submodule.span k (Set.range (relationTerm (Q := Q) Λ ρ))
  let T := Set.range (stdElt ρ : Std → R)
  have hT : Submodule.span k T = ⊤ := KLRAlgebra.span_stdElt ρ hρ
  have hab (a b : R) (i : Seq ν) : a * cycElt Q aΛ i * b ∈ V := by
    have ha : a ∈ Submodule.span k T := hT ▸ Submodule.mem_top
    have hb : b ∈ Submodule.span k T := hT ▸ Submodule.mem_top
    have hc : cycElt Q aΛ i ∈ Submodule.span k (Set.range (cycElt (ν := ν) Q aΛ)) :=
      Submodule.subset_span ⟨i, rfl⟩
    have hh := Submodule.mul_mem_mul (Submodule.mul_mem_mul ha hc) hb
    rw [Submodule.span_mul_span, Submodule.span_mul_span] at hh
    refine (Submodule.span_le (p := V) |>.2 ?_) hh
    rintro _ ⟨_, ⟨_, ⟨u, rfl⟩, _, ⟨j, rfl⟩, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨(u, j, t), rfl⟩
  apply le_antisymm
  · intro x hx
    have h := (mk_eq_zero_iff x).1 (LinearMap.mem_ker.mp hx)
    rw [cycIdeal, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at h
    exact (AddSubgroup.closure_le (K := V.toAddSubgroup) |>.2
      (by rintro _ ⟨_, ⟨a, _, _, ⟨i, rfl⟩, rfl⟩, b, _, rfl⟩; exact hab a b i)) h
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, i, t⟩, rfl⟩
    change mk k Q aΛ ν (stdElt ρ u * cycElt Q aΛ i * stdElt ρ t) = 0
    simp

include hρ in
/-- All homogeneous linear relations of the cyclotomic quotient are spanned by the
products through first-dot generators of the prescribed total degree. -/
theorem grade_inf_ker_mk (d : ℤ) :
    G.grade ν d ⊓ LinearMap.ker (mk k Q aΛ ν).toLinearMap =
      Submodule.span k (relationsInGrade G Λ ρ d) := by
  rw [ker_mk_eq_span_relationTerm Λ ρ hρ]
  have h := inf_span_eq (G.grade ν) (relationDegree G Λ ρ) (relationTerm_mem_grade G Λ ρ) Set.univ d
  simpa [relationsInGrade] using h

/-- Positive dot degrees leave only finitely many products of any prescribed degree. -/
theorem finite_relationsInGrade (hX : ∀ i, 0 < G.degX i) (d : ℤ) :
    (relationsInGrade G Λ ρ d).Finite := by
  obtain ⟨L, hL⟩ := G.bddBelow_stdDeg ρ (fun a => (hX a).le) Set.univ
  have hmin (b : Std) : L ≤ G.stdDeg ρ b := hL ⟨b, Set.mem_univ _, rfl⟩
  have hcyc (i : Seq ν) : 0 ≤ cycEltDegree G Λ ν i := by
    unfold cycEltDegree
    split_ifs <;> first | exact nsmul_nonneg (hX _).le _ | exact le_rfl
  let U := ⋃ n ∈ Set.Icc L (d-L), {b : Std | G.stdDeg ρ b = n}
  have hU : U.Finite := (Set.finite_Icc _ _).biUnion fun n _ => G.finite_stdDeg_eq ρ hX n
  refine Set.Finite.image _ ((hU.prod (Set.finite_univ.prod hU)).subset ?_)
  rintro ⟨x, i, y⟩ h
  change G.stdDeg ρ x + cycEltDegree G Λ ν i + G.stdDeg ρ y = d at h
  have encode (b : Std) (hb : G.stdDeg ρ b ≤ d-L) : b ∈ U :=
    Set.mem_iUnion₂.mpr ⟨G.stdDeg ρ b, ⟨hmin b, hb⟩, rfl⟩
  exact ⟨encode x (by linarith [hcyc i, hmin y]), Set.mem_univ _, encode y (by linarith [hcyc i, hmin x])⟩

include hρ in
/-- The dimension of the undeformed cyclotomic quotient in degree `d` is the number
of affine standard diagrams of degree `d` minus the rank of the finite family
`relationsInGrade`. The products and their rank are taken before quotienting. -/
theorem finrank_grade_eq_card_sub_rank (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i) (d : ℤ) :
    Module.finrank k (grade G Λ ν d) = Nat.card {b : Std | G.stdDeg ρ b = d} -
      Module.finrank k (Submodule.span k (relationsInGrade G Λ ρ d)) := by
  let := G.hasGdim_grade (ν := ν) hsym ρ hρ hX
  have h := finrank_map_add_finrank_inf_ker (mk k Q aΛ ν).toLinearMap (G.grade ν d)
  rw [grade_inf_ker_mk G Λ ρ hρ, G.finrank_grade hsym ρ hρ hX] at h
  change Module.finrank k ((G.grade ν d).map (mk k Q aΛ ν).toLinearMap) = _
  omega

section Corners

/-- Projection onto the affine sequence corner, before taking the cyclotomic quotient. -/
noncomputable def cutToCorner (j i : Seq ν) : R →ₗ[k] R :=
  (LinearMap.mulLeft k (e j)).comp (LinearMap.mulRight k (e i))

private theorem cutToCorner_mem_grade (j i : Seq ν) {d : ℤ} {x : R} (hx : x ∈ G.grade ν d) :
    cutToCorner j i x ∈ G.grade ν d := by
  have h := SetLike.GradedMul.mul_mem (G.e_mem_grade j) (SetLike.GradedMul.mul_mem hx (G.e_mem_grade i))
  change e j * (x * e i) ∈ G.grade ν d
  simpa only [zero_add, add_zero] using h

private theorem cutToCorner_eq_self (j i : Seq ν) {x : R} (hx : x ∈ KLRAlgebra.corner j i) :
    cutToCorner j i x = x :=
  (mul_assoc _ _ _).symm.trans (mem_corner_iff.mp hx)

private theorem map_cornerGrade (j i : Seq ν) (d : ℤ) :
    (G.cornerGrade j i d).map (mk k Q aΛ ν).toLinearMap =
      grade G Λ ν d ⊓ corner k Q aΛ j i := by
  let π := mk k Q aΛ ν
  let E := fun u : Seq ν => π (e u)
  have hE (u : Seq ν) : E u * E u = E u := by
    change π (e u) * π (e u) = π (e u)
    rw [← map_mul, e_mul_self]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxi⟩, rfl⟩
    refine ⟨Graded.mem_map_of_mem _ _ hx, ⟨π x, ?_⟩⟩
    change E j * (π x * E i) = π x
    have he : e j * (x * e i) = x := cutToCorner_eq_self j i hxi
    simpa only [E, map_mul] using congrArg π he
  · rintro ⟨⟨x, hx, rfl⟩, ⟨z, hz⟩⟩
    refine ⟨cutToCorner j i x, ⟨cutToCorner_mem_grade G j i hx, ⟨x, rfl⟩⟩, ?_⟩
    change E j * (z * E i) = π x at hz
    change π (e j * (x * e i)) = π x
    rw [map_mul, map_mul]
    change E j * (π x * E i) = π x
    rw [← hz]
    simp only [← mul_assoc, hE]
    rw [mul_assoc _ (E i), hE]

include hρ in
private theorem cornerGrade_inf_ker_mk (j i : Seq ν) (d : ℤ) :
    G.cornerGrade j i d ⊓ LinearMap.ker (mk k Q aΛ ν).toLinearMap =
      Submodule.span k (cutToCorner (Q := Q) j i '' relationsInGrade G Λ ρ d) := by
  rw [Submodule.span_image, ← grade_inf_ker_mk G Λ ρ hρ]
  ext x
  constructor
  · rintro ⟨⟨hx, hxi⟩, h0⟩
    exact ⟨x, ⟨hx, h0⟩, cutToCorner_eq_self j i hxi⟩
  · rintro ⟨y, ⟨hy, h0⟩, rfl⟩
    refine ⟨⟨cutToCorner_mem_grade G j i hy, ⟨y, rfl⟩⟩, ?_⟩
    change mk k Q aΛ ν y = 0 at h0
    change mk k Q aΛ ν (e j * (y * e i)) = 0
    simp [h0]

include hρ in
/-- The dimensions of all sequence corners of the cyclotomic quotient. Restricting the
affine PBW basis to the specified endpoints gives the first term; the correction is the
rank in the affine algebra of the finite list of cyclotomic relations at those endpoints. -/
theorem finrank_cornerGrade_eq_card_sub_rank (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i)
    (j i : Seq ν) (d : ℤ) :
    Module.finrank k (grade G Λ ν d ⊓ corner k Q aΛ j i : Submodule k (CycKLR k Q aΛ ν)) =
      Nat.card {b : Std | (b.1 = i ∧ b.2.1 • i = j) ∧ G.stdDeg ρ b = d} -
        Module.finrank k (Submodule.span k (cutToCorner (Q := Q) j i '' relationsInGrade G Λ ρ d)) := by
  let := G.hasGdim_cornerGrade hsym ρ hρ hX j i
  have h := finrank_map_add_finrank_inf_ker (mk k Q aΛ ν).toLinearMap (G.cornerGrade j i d)
  rw [map_cornerGrade, cornerGrade_inf_ker_mk G Λ ρ hρ] at h
  let F := ({i} : Finset (Seq ν)) ×ˢ Finset.univ.filter (fun w : Perm (Fin (Multiset.card ν)) => w • i = j)
  have hnum := finrank_inf_span (G.grade ν) (G.stdDeg ρ)
    (basisOfSymm hsym ρ hρ).linearIndependent (G.basis_mem_grade hsym ρ hρ)
    {b : Std | (b.1, b.2.1) ∈ F} d ((G.finite_stdDeg_eq ρ hX d).subset fun _ hb => hb.2)
  change Module.finrank k (G.grade ν d ⊓ GradingDatum.spanF hsym ρ hρ F : Submodule k R) = _ at hnum
  rw [GradingDatum.spanF_corner hsym ρ hρ] at hnum
  change Module.finrank k (G.cornerGrade j i d) = _ at hnum
  simp only [F, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_singleton, Finset.mem_filter,
    Finset.mem_univ, true_and] at hnum
  omega

end Corners

end Categorification.KLR.CycKLR
