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
colours. Selecting a minimal spanning family modulo these affine relations yields a
homogeneous basis consisting of quotient images of PBW diagrams. This calculation uses the undeformed cyclotomic polynomial `X ^ Λ i`.
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

section Selection

variable {A M J : Type*} [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M]

/-- A finite PBW selection can be checked entirely in the affine algebra. Every
candidate lies in the span of the selected terms and the relations, and each selected
term is indispensable after adjoining the relations. -/
def IsPBWSelection (v : J → A) (C : Set J) (W : Submodule k A) (s : Finset J) : Prop :=
  (s : Set J) ⊆ C ∧
  (∀ j ∈ C, v j ∈ Submodule.span k (v '' (s : Set J)) ⊔ W) ∧
  ∀ j ∈ s, v j ∉ Submodule.span k (v '' ((s : Set J) \ {j})) ⊔ W

/-- Delete redundant affine PBW diagrams until every remaining diagram is
indispensable modulo the relation span. Each deletion strictly decreases the
candidate count. The choice of a redundant diagram can change the basis. -/
noncomputable def selectPBW (v : J → A) (W : Submodule k A) (S : Finset J) :
    {s : Finset J // IsPBWSelection v (S : Set J) W s} := by
  classical
  by_cases h : ∃ j ∈ S, v j ∈ Submodule.span k (v '' ((S : Set J) \ {j})) ⊔ W
  · let j := h.choose
    have hj : j ∈ S := h.choose_spec.1
    let B := selectPBW v W (S.erase j)
    refine ⟨B.1, B.2.1.trans (by exact Finset.erase_subset j S), ?_, B.2.2.2⟩
    intro i hi
    by_cases he : i = j
    · subst i
      have hspan : Submodule.span k (v '' ((S.erase j : Finset J) : Set J)) ≤
          Submodule.span k (v '' (B.1 : Set J)) ⊔ W :=
        Submodule.span_le.mpr (by rintro _ ⟨u, hu, rfl⟩; exact B.2.2.1 u hu)
      have hm : v j ∈ Submodule.span k (v '' ((S.erase j : Finset J) : Set J)) ⊔ W := by
        rw [Finset.coe_erase]
        exact h.choose_spec.2
      exact (sup_le hspan le_sup_right) hm
    · exact B.2.2.1 i (Finset.mem_erase.mpr ⟨he, hi⟩)
  · refine ⟨S, Set.Subset.rfl, fun i hi => ?_, fun j hj hmem => h ⟨j, hj, hmem⟩⟩
    exact (le_sup_left : Submodule.span k (v '' (S : Set J)) ≤ _) (Submodule.subset_span ⟨i, hi, rfl⟩)
termination_by S.card
decreasing_by
  classical
  exact Finset.card_erase_lt_of_mem hj

private theorem map_mem_span_iff (f : A →ₗ[k] M) (v : J → A) {C T : Set J}
    (hTC : T ⊆ C) {i : J} (hi : i ∈ C) :
    (f ∘ v) i ∈ Submodule.span k ((f ∘ v) '' T) ↔
      v i ∈ Submodule.span k (v '' T) ⊔ (Submodule.span k (v '' C) ⊓ LinearMap.ker f) := by
  let U := Submodule.span k (v '' T)
  let P := Submodule.span k (v '' C)
  have hU : U ≤ P := Submodule.span_mono (Set.image_mono hTC)
  have hv : v i ∈ P := Submodule.subset_span ⟨i, hi, rfl⟩
  rw [Set.image_comp, Submodule.span_image]
  constructor
  · rintro ⟨x, hx, hfx⟩
    refine Submodule.mem_sup.mpr ⟨x, hx, v i - x, ⟨P.sub_mem hv (hU hx), ?_⟩, by abel⟩
    change f (v i - x) = 0
    change f x = f (v i) at hfx
    rw [map_sub, hfx, sub_self]
  · intro h
    obtain ⟨x, hx, y, ⟨_, hy⟩, he⟩ := Submodule.mem_sup.mp h
    refine ⟨x, hx, ?_⟩
    change f y = 0 at hy
    change f x = f (v i)
    rw [← he, map_add, hy, add_zero]

/-- An affine PBW selection is equivalent to choosing an independent subfamily
whose images span all the quotient images of the candidates. -/
theorem isPBWSelection_iff (f : A →ₗ[k] M) (v : J → A) (C : Set J)
    (W : Submodule k A) (hW : Submodule.span k (v '' C) ⊓ LinearMap.ker f = W)
    (s : Finset J) :
    IsPBWSelection v C W s ↔
      (s : Set J) ⊆ C ∧ (f ∘ v) '' C ⊆ Submodule.span k ((f ∘ v) '' (s : Set J)) ∧
        LinearIndepOn k (f ∘ v) (s : Set J) := by
  rw [← hW, linearIndepOn_iff_notMem_span]
  constructor
  · rintro ⟨hs, hsp, hind⟩
    refine ⟨hs, ?_, ?_⟩
    · rintro _ ⟨j, hj, rfl⟩
      exact (map_mem_span_iff f v hs hj).2 (hsp j hj)
    · intro j hj h
      exact hind j hj ((map_mem_span_iff f v (Set.sdiff_subset.trans hs) (hs hj)).1 h)
  · rintro ⟨hs, hsp, hind⟩
    refine ⟨hs, fun j hj => (map_mem_span_iff f v hs hj).1 (hsp ⟨j, hj, rfl⟩), ?_⟩
    intro j hj h
    exact hind j hj ((map_mem_span_iff f v (Set.sdiff_subset.trans hs) (hs hj)).2 h)

/-- Any selection passing the affine span tests gives a basis of the specified
image space with exactly those representatives. -/
theorem IsPBWSelection.exists_basis {v : J → A} {C : Set J} {W : Submodule k A} {s : Finset J}
    (hsel : IsPBWSelection v C W s) (f : A →ₗ[k] M) (P : Submodule k M)
    (hW : Submodule.span k (v '' C) ⊓ LinearMap.ker f = W)
    (hP : (Submodule.span k (v '' C)).map f = P) :
    ∃ B : Module.Basis s k P, ∀ b, (B b : M) = f (v b) := by
  obtain ⟨hT, hsp, hind⟩ := (isPBWSelection_iff f v C W hW s).1 hsel
  have hspan : Submodule.span k ((f ∘ v) '' (s : Set J)) = P := by
    rw [← hP, Submodule.map_span, ← Set.image_comp]
    exact le_antisymm (Submodule.span_mono (Set.image_mono hT)) (Submodule.span_le.2 hsp)
  have hli : LinearIndependent k (fun b : s => f (v b)) := hind
  have he : Submodule.span k (Set.range fun b : s => f (v b)) = P := by
    change Submodule.span k (Set.range ((s : Set J).domRestrict (f ∘ v))) = P
    rw [Set.range_domRestrict, hspan]
  refine ⟨(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ he), fun b => ?_⟩
  simp only [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]

private theorem exists_selection_basis (f : A →ₗ[k] M) (v : J → A) (C : Set J)
    (hC : C.Finite) (W : Submodule k A) (P : Submodule k M)
    (hW : Submodule.span k (v '' C) ⊓ LinearMap.ker f = W)
    (hP : (Submodule.span k (v '' C)).map f = P) :
    ∃ s : Finset J, IsPBWSelection v C W s ∧
      ∃ B : Module.Basis s k P, ∀ b, (B b : M) = f (v b) := by
  classical
  let S := selectPBW v W hC.toFinset
  have hsel : IsPBWSelection v C W S.1 :=
    (congrArg (fun D => IsPBWSelection v D W S.1) hC.coe_toFinset).mp S.2
  exact ⟨S.1, hsel, hsel.exists_basis f P hW hP⟩

end Selection

include hρ in
/-- For the monomial quotient of Kang–Kashiwara, arXiv:1102.4677v4, Definition
4.1, degreewise elimination in the affine PBW basis of Khovanov–Lauda I,
arXiv:0803.4121v2, Theorem 2.5, selects homogeneous diagrams whose images form
a basis. Both the candidates and the relations in the selection test are finite. -/
theorem exists_gradePBWBasis (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i) (d : ℤ) :
    ∃ s : Finset Std, IsPBWSelection (stdElt ρ : Std → R) {b | G.stdDeg ρ b = d}
        (Submodule.span k (relationsInGrade G Λ ρ d)) s ∧
      ∃ B : Module.Basis s k (grade G Λ ν d),
        ∀ b, (B b : CycKLR k Q aΛ ν) = mk k Q aΛ ν (stdElt ρ b) := by
  have hgrade := G.grade_eq_span hsym ρ hρ d
  have hb : (⇑(basisOfSymm hsym ρ hρ) : Std → R) = stdElt ρ :=
    funext fun b => basisOfSymm_apply hsym ρ hρ b
  rw [hb] at hgrade
  apply exists_selection_basis (mk k Q aΛ ν).toLinearMap _ _ (G.finite_stdDeg_eq ρ hX d)
  · rw [← hgrade, grade_inf_ker_mk G Λ ρ hρ]
  · rw [← hgrade]
    rfl

include hρ in
/-- Degreewise PBW-image bases with prescribed source and target sequences in
the monomial quotient (Kang–Kashiwara, arXiv:1102.4677v4, Definition 4.1).
The selection uses the corner restrictions of the affine cyclotomic relations. -/
theorem exists_cornerGradePBWBasis (hsym : KLRSymm Q) (hX : ∀ l, 0 < G.degX l)
    (j i : Seq ν) (d : ℤ) :
    ∃ s : Finset Std, IsPBWSelection (stdElt ρ : Std → R)
        {b | (b.1 = i ∧ b.2.1 • i = j) ∧ G.stdDeg ρ b = d}
        (Submodule.span k (cutToCorner (Q := Q) j i '' relationsInGrade G Λ ρ d)) s ∧
      ∃ B : Module.Basis s k (grade G Λ ν d ⊓ corner k Q aΛ j i : Submodule k (CycKLR k Q aΛ ν)),
        ∀ b, (B b : CycKLR k Q aΛ ν) = mk k Q aΛ ν (stdElt ρ b) := by
  let F := ({i} : Finset (Seq ν)) ×ˢ Finset.univ.filter (fun w : Perm (Fin (Multiset.card ν)) => w • i = j)
  have hc := inf_span_eq (G.grade ν) (G.stdDeg ρ) (G.basis_mem_grade hsym ρ hρ)
    {b : Std | (b.1, b.2.1) ∈ F} d
  change G.grade ν d ⊓ GradingDatum.spanF hsym ρ hρ F = _ at hc
  rw [GradingDatum.spanF_corner hsym ρ hρ] at hc
  have hb : (⇑(basisOfSymm hsym ρ hρ) : Std → R) = stdElt ρ :=
    funext fun b => basisOfSymm_apply hsym ρ hρ b
  simp only [hb, F, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_filter, Finset.mem_univ, true_and] at hc
  apply exists_selection_basis (mk k Q aΛ ν).toLinearMap
  · exact (G.finite_stdDeg_eq ρ hX d).subset fun _ h => h.2
  · rw [← hc]
    exact cornerGrade_inf_ker_mk G Λ ρ hρ j i d
  · rw [← hc]
    exact map_cornerGrade G Λ j i d

include hρ in
/-- Collecting these degreewise selections gives a homogeneous PBW-image basis of
the entire cyclotomic algebra of Kang–Kashiwara, arXiv:1102.4677v4, Definition 4.1.
The PBW labels in each degree satisfy the affine relation-span tests. -/
theorem exists_homogeneousPBWBasis (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i) :
    ∃ s : ℤ → Finset Std,
      (∀ d, IsPBWSelection (stdElt ρ : Std → R) {b | G.stdDeg ρ b = d}
        (Submodule.span k (relationsInGrade G Λ ρ d)) (s d)) ∧
      ∃ B : Module.Basis (Σ d, ↥(s d)) k (CycKLR k Q aΛ ν),
        ∀ b, B b = mk k Q aΛ ν (stdElt ρ b.2) := by
  choose s hs Bs hBs using exists_gradePBWBasis G Λ ρ hρ hsym hX
  refine ⟨s, hs, (DirectSum.Decomposition.isInternal (grade G Λ ν)).collectedBasis Bs, ?_⟩
  intro b
  rw [DirectSum.IsInternal.collectedBasis_coe]
  exact hBs b.1 b.2

private theorem hasGdim_image {A M : Type*} [AddCommGroup A] [Module k A]
    [AddCommGroup M] [Module k M] (f : A →ₗ[k] M) (P : ℤ → Submodule k A) [HasGdim P] :
    HasGdim (fun d => (P d).map f) where
  finiteDimensional _ := inferInstance
  bddBelow := by
    obtain ⟨L, hL⟩ := HasGdim.bddBelow (ℳ := P)
    refine ⟨L, fun d hd => hL ?_⟩
    intro h
    apply hd
    rw [h, Submodule.map_bot]

include hρ in
/-- Coefficient of the Laurent series graded dimension of the monomial cyclotomic
algebra (Kang–Kashiwara, arXiv:1102.4677v4, Definition 4.1), computed from the
degreewise affine PBW count and the affine cyclotomic relation rank. -/
theorem coeff_gdim_grade_eq_card_sub_rank (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i) (d : ℤ) :
    (gdim (grade G Λ ν)).coeff d =
      ((Nat.card {b : Std | G.stdDeg ρ b = d} -
        Module.finrank k (Submodule.span k (relationsInGrade G Λ ρ d)) : ℕ) : ℤ) := by
  let := G.hasGdim_grade (ν := ν) hsym ρ hρ hX
  let : HasGdim (grade G Λ ν) := hasGdim_image (mk k Q aΛ ν).toLinearMap (G.grade ν)
  rw [coeff_gdim, finrank_grade_eq_card_sub_rank G Λ ρ hρ hsym hX]

include hρ in
/-- The Laurent series coefficient in a prescribed sequence corner, using the rank
of the relations projected onto those endpoints (Kang–Kashiwara, arXiv:1102.4677v4,
Definition 4.1 and Khovanov–Lauda I, arXiv:0803.4121v2, Theorem 2.5). -/
theorem coeff_gdim_cornerGrade_eq_card_sub_rank (hsym : KLRSymm Q) (hX : ∀ l, 0 < G.degX l)
    (j i : Seq ν) (d : ℤ) :
    (gdim (fun t => grade G Λ ν t ⊓ corner k Q aΛ j i : ℤ → Submodule k (CycKLR k Q aΛ ν))).coeff d =
      ((Nat.card {b : Std | (b.1 = i ∧ b.2.1 • i = j) ∧ G.stdDeg ρ b = d} -
        Module.finrank k (Submodule.span k (cutToCorner (Q := Q) j i '' relationsInGrade G Λ ρ d)) : ℕ) : ℤ) := by
  let := G.hasGdim_cornerGrade hsym ρ hρ hX j i
  have h := hasGdim_image (mk k Q aΛ ν).toLinearMap (G.cornerGrade j i)
  simp_rw [map_cornerGrade] at h
  let := h
  rw [coeff_gdim]
  exact_mod_cast finrank_cornerGrade_eq_card_sub_rank G Λ ρ hρ hsym hX j i d

end Categorification.KLR.CycKLR
