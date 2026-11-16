/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GalleryRep
import Categorification.WeightedKLR.Gallery
import Categorification.WeightedKLR.Standing
import Categorification.Algebra.CoactionGrading
import Categorification.KLR.PolyRep.Graded

/-!
# The grading of the gallery algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.1 (the degree
function stated before Definition 2.4).

Webster grades weighted KLR diagrams by giving a dot on an `i`-strand degree `⟨α_i, α_i⟩`, a
crossing of two strands of colours `i, j` degree `-δ_{ij} ⟨α_i, α_i⟩`, and a crossing of a strand
with a ghost degree `-½ ⟨α_i, α_j⟩ (1 - δ_{ij})`. We work with abstract grading data
(`GradingDatum`): integers `dot i` (a dot on an `i`-strand), `wall e` (a step across a wall of the
edge `e`, in either direction) and `cross i` (a step across a diagonal of colour `i`), subject to

* `Q_e` is weighted homogeneous of degree `2 wall e` for the weights `(dot (head e), dot (tail e))`
  (homogeneity of the ghost bigon, relation (2));
* `cross i = -dot i` if there is no loop of weight `0` at `i` (the nilHecke relations (1));
* the loop polynomial `P_i` is weighted homogeneous of degree `cross i` for the weights
  `(dot i, dot i)` if there is such a loop (the bigon `ψ² = 2 P_i ψ`, relation (3)).

Every defining relation of `GalleryAlgebra` is then homogeneous (`GradingDatum.liftF_rel`),
including the triple-point corrections (4a)–(4c). Idempotents and relabellings have degree `0`.

## Normalization and comparison with the printed degrees

Under Webster's standing hypothesis (`WeightedGraph.Standing`: `Q_e` is homogeneous for weights
`(d_{h(e)}, d_{t(e)})` of degree `d_{h(e)} c_e`, and `(u - v) P_i` of degree `d_i c_i`), the
grading datum `WeightedGraph.Standing.gradingDatum` uses the *doubled* normalization:

* a dot on an `i`-strand has degree `2 d_i`;
* a step across a wall of the edge `e` has degree `d_{h(e)} c_e`, so that `Q_e(y_a, y_b)` has
  degree `2 d_{h(e)} c_e`, twice its degree in the standing hypothesis;
* a step across a diagonal of colour `i` has degree `-2 d_i` without a loop of weight `0` at `i`,
  and `2 d_i (c_i - 1)` (the degree of `P_i`) with one.

These are twice the degrees obtained by reading Webster's pairing as `⟨α_i, α_i⟩ = d_i` and
`⟨α_i, α_j⟩ = -d_{h(e)} c_e`, the reading under which his printed degrees agree with the standing
hypothesis (a dot of degree `d_i`, so `Q_e` of degree `d_{h(e)} c_e`, and two ghost crossings of
total degree `-⟨α_i, α_j⟩ = d_{h(e)} c_e`); with that reading the ghost crossings can have
half-integral degree, which the doubling avoids. With the usual reading `⟨α_i, α_i⟩ = 2 d_i` the
printed dot and strand-crossing degrees are ours, but the printed ghost crossings have degree
`½ d_{h(e)} c_e`, half the degree the ghost bigon (relation (2)) requires. Beyond this
normalization, the printed function does not make every relation homogeneous in general:

* with several edges between `i` and `j`, each ghost crossing must carry the degree of its own
  edge, not a total `⟨α_i, α_j⟩`;
* for a loop of nonzero weight at `i`, the factor `1 - δ_{ij}` gives the crossing of an `i`-strand
  with an `i`-ghost degree `0`, while relation (2) multiplies by `Q_e`, of positive degree;
* for a loop of weight `0` at `i`, relation (3) forces the crossing of two `i`-strands to have the
  degree of `P_i`, not `-⟨α_i, α_i⟩`.

The grading data here assign the degrees that make every relation homogeneous.

The grading is constructed with a coaction `GalleryAlgebra k Γ ν → GalleryAlgebra k Γ ν [ℤ]`
(`Categorification.Algebra.CoactionGrading`), as for the KLR algebras (`KLR/Grading.lean`).

## Main definitions and results

* `WeightedKLR.GradingDatum Γ` : grading data compatible with `Γ`.
* `GradingDatum.coaction`, `GradingDatum.grade` and the `GradedAlgebra (G.grade ν)`
  structure `GradingDatum.gradedAlgebra`.
* `GradingDatum.e_mem_grade`, `GradingDatum.poly_mem_grade`, `GradingDatum.t_mem_grade`,
  `GradingDatum.r_mem_grade`, `GradingDatum.galList_mem_grade` : degrees of the generators and of
  galleries; `GradingDatum.r_mul_galList_mul_poly_mem_grade` : the elements of the basis of
  Webster's Theorem 2.8 are homogeneous.
* `WeightedGraph.Standing.gradingDatum` : the grading datum of Webster's standing hypothesis.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv AddMonoidAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-! ### Weighted homogeneous polynomials as singles -/

section Single

variable {σ R : Type*} [CommRing R] (w : σ → ℤ)

/-- The substitution `X s ↦ single (w s) (X s)` sends a monomial of weight `d` to `single d`. -/
theorem aeval_single_monomial (m : σ →₀ ℕ) (c : R) :
    aeval (fun s => (single (w s) (X s) : AddMonoidAlgebra (MvPolynomial σ R) ℤ))
      (monomial m c) = single (Finsupp.weight w m) (monomial m c) := by
  rw [aeval_monomial]
  simp only [single_pow, finsuppProd_single, coe_algebraMap, Function.comp_apply,
    single_mul_single, zero_add, algebraMap_eq]
  rw [monomial_eq, Finsupp.weight_apply]

/-- The substitution `X s ↦ single (w s) (X s)` sends a weighted homogeneous polynomial `f` of
degree `d` to `single d f`. -/
theorem aeval_single_of_isWeightedHomogeneous {f : MvPolynomial σ R} {d : ℤ}
    (hf : f.IsWeightedHomogeneous w d) :
    aeval (fun s => (single (w s) (X s) : AddMonoidAlgebra (MvPolynomial σ R) ℤ)) f =
      single d f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, show (single d (∑ v ∈ f.support, monomial v (f.coeff v)) :
      AddMonoidAlgebra (MvPolynomial σ R) ℤ) = ∑ v ∈ f.support, single d (monomial v (f.coeff v))
    from map_sum (singleAddHom d) _ _]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_single_monomial, hf (mem_support_iff.1 hm)]

end Single

/-! ### Grading data -/

variable (Γ) in
/-- Grading data for the gallery algebra of `Γ`: the degree `dot i` of a dot on an `i`-strand, the
degree `wall e` of a step across a wall of the edge `e` (in either direction) and the degree
`cross i` of a step across a diagonal of colour `i`. -/
structure GradingDatum where
  /-- The degree of a dot on a strand of colour `i`. -/
  dot : I → ℤ
  /-- The degree of a step across a wall of the edge `e`. -/
  wall : Γ.E → ℤ
  /-- The degree of a step across a diagonal of colour `i`. -/
  cross : I → ℤ
  isWeightedHomogeneous_Q : ∀ e,
    (Γ.Q e).IsWeightedHomogeneous ![dot (Γ.head e), dot (Γ.tail e)] (2 * wall e)
  cross_of_loop_none : ∀ i, Γ.loop i = none → cross i = -dot i
  isWeightedHomogeneous_loop : ∀ i P, Γ.loop i = some P →
    P.IsWeightedHomogeneous ![dot i, dot i] (cross i)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.left_fst (C : FullChamber Γ ν) (d : Diag ν) : (d.left C).1 = d.fst.1 := by
  unfold Diag.left; split_ifs
  · rfl
  · exact d.2.1.symm

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.right_fst (C : FullChamber Γ ν) (d : Diag ν) : (d.right C).1 = d.fst.1 := by
  unfold Diag.right; split_ifs
  · exact d.2.1.symm
  · rfl

omit [DecidableEq I] in
theorem Diag.Joins.fst_eq {d : Diag ν} {a b : Strand ν} (h : d.Joins a b) :
    d.fst.1 = a.1 ∧ b.1 = a.1 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by rw [h1], by rw [← h1, ← h2]; exact d.2.1.symm⟩
  · exact ⟨by rw [← h2]; exact d.2.1, by rw [← h1, ← h2]; exact d.2.1⟩

namespace GradingDatum

variable (G : GradingDatum Γ)

/-- The weight of the variable `y_s`: the degree of a dot on the strand `s`. -/
def wt (s : Strand ν) : ℤ := G.dot s.1

/-- The degree of a step across the hyperplane `h`. -/
def hypDeg : Hyp Γ ν → ℤ
  | .inl w => G.wall w.edge
  | .inr d => G.cross d.fst.1

open Classical in
/-- The degree of the step from `C` to `C'`: that of the hyperplane separating them if they are
adjacent, and `0` otherwise (the step is then zero). -/
noncomputable def stepDeg (C C' : FullChamber Γ ν) : ℤ :=
  if h : ∃ h, C.Adjacent C' h then G.hypDeg h.choose else 0

omit [IsStrictOrderedRing 𝕜] in
theorem stepDeg_of_adjacent {C C' : FullChamber Γ ν} {h : Hyp Γ ν} (hC : C.Adjacent C' h) :
    G.stepDeg C C' = G.hypDeg h := by
  have hex : ∃ h, C.Adjacent C' h := ⟨h, hC⟩
  rw [stepDeg, dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg G.hypDeg (hex.choose_spec.unique hC)

omit [IsStrictOrderedRing 𝕜] in
theorem stepDeg_of_not_adjacent {C C' : FullChamber Γ ν} (hC : ¬∃ h, C.Adjacent C' h) :
    G.stepDeg C C' = 0 := by
  rw [stepDeg, dite_eq_right_of_eq_false (eq_false hC)]

omit [IsStrictOrderedRing 𝕜] in
theorem stepDeg_symm (C C' : FullChamber Γ ν) : G.stepDeg C' C = G.stepDeg C C' := by
  by_cases hC : ∃ h, C.Adjacent C' h
  · obtain ⟨h, hC⟩ := hC
    rw [G.stepDeg_of_adjacent hC, G.stepDeg_of_adjacent hC.symm]
  · have hC' : ¬∃ h, C'.Adjacent C h := fun ⟨h, hh⟩ => hC ⟨h, hh.symm⟩
    rw [G.stepDeg_of_not_adjacent hC, G.stepDeg_of_not_adjacent hC']

omit [DecidableEq I] in
theorem diag_comap_fst (g : ColPerm ν) (d : Diag ν) : (d.comap g).1.fst.1 = d.fst.1 := by
  rcases Diag.comap_spec g d with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> rw [h, ColPerm.inv_apply_fst]
  exact d.2.1.symm

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem hypDeg_comap (g : ColPerm ν) (h : Hyp Γ ν) : G.hypDeg (h.comap g) = G.hypDeg h := by
  rcases h with w | d
  · rfl
  · exact congrArg (fun x : ν.support => G.cross (x : I)) (diag_comap_fst g d)

theorem stepDeg_smul (g : ColPerm ν) (C C' : FullChamber Γ ν) :
    G.stepDeg (g • C) (g • C') = G.stepDeg C C' := by
  by_cases hC : ∃ h, (g • C).Adjacent (g • C') h
  · obtain ⟨h, hh⟩ := hC
    rw [G.stepDeg_of_adjacent hh, G.stepDeg_of_adjacent (hh.of_smul g), hypDeg_comap]
  · have hC' : ¬∃ h, C.Adjacent C' h := fun ⟨h, hh⟩ => hC ⟨_, hh.smul g⟩
    rw [G.stepDeg_of_not_adjacent hC, G.stepDeg_of_not_adjacent hC']

/-! ### Homogeneity of the polynomials in the relations -/

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem isWeightedHomogeneous_factor (w : Wall Γ ν) :
    (w.factor (k := k)).IsWeightedHomogeneous G.wt (2 * G.wall w.edge) := by
  rw [w.factor_eq_rename]
  refine isWeightedHomogeneous_rename _ (fun j => ?_) (G.isWeightedHomogeneous_Q w.edge)
  fin_cases j
  · exact congrArg G.dot w.2.1
  · exact congrArg G.dot w.2.2.1

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem isWeightedHomogeneous_loopFactor {i : I} {P : MvPolynomial (Fin 2) k}
    (hP : Γ.loop i = some P) {a b : Strand ν} (ha : a.1 = i) (hb : b.1 = i) :
    (loopFactor P a b).IsWeightedHomogeneous G.wt (G.cross i) := by
  rw [loopFactor_eq_rename]
  refine isWeightedHomogeneous_rename _ (fun j => ?_) (G.isWeightedHomogeneous_loop i P hP)
  fin_cases j
  · exact congrArg G.dot ha
  · exact congrArg G.dot hb

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A diagonal step operator `Δ_{l r}` shifts the degree by `cross i`. -/
theorem isWeightedHomogeneous_stepFactor {l r : Strand ν} (hlr : l ≠ r) (hc : l.1 = r.1)
    {f : PolyRing ν k} {D : ℤ} (hf : f.IsWeightedHomogeneous G.wt D) :
    (stepFactor Γ l r f).IsWeightedHomogeneous G.wt (D + G.cross l.1) := by
  unfold stepFactor
  split
  · next h =>
    rw [G.cross_of_loop_none _ h, ← sub_eq_add_neg]
    exact isWeightedHomogeneous_ddiff hlr (congrArg (fun x : ν.support => G.dot (x : I)) hc) hf
  · next P h =>
    rw [add_comm]
    refine (G.isWeightedHomogeneous_loopFactor h rfl (congrArg Subtype.val hc.symm)).mul
      (hf.sub ?_)
    exact isWeightedHomogeneous_rename _ (fun s => by
      rcases eq_or_ne s l with rfl | h1
      · rw [swap_apply_left]; exact congrArg (fun x : ν.support => G.dot (x : I)) hc.symm
      rcases eq_or_ne s r with rfl | h2
      · rw [swap_apply_right]; exact congrArg (fun x : ν.support => G.dot (x : I)) hc
      · rw [swap_apply_of_ne_of_ne h1 h2]) hf

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem stepFactor_add (l r : Strand ν) (f g : PolyRing ν k) :
    stepFactor Γ l r (f + g) = stepFactor Γ l r f + stepFactor Γ l r g := by
  unfold stepFactor
  split
  · exact map_add _ f g
  · rw [map_add]; ring

/-! ### The coaction on the free algebra -/

open GalleryAlgebra

local notation "Fr" => FreeAlgebra k (Gen k Γ ν)
local notation "mkF" => GalleryAlgebra.mk k Γ ν

/-- Polynomials, with each monomial placed in its degree. -/
noncomputable def polyCo : PolyRing ν k →ₐ[k] AddMonoidAlgebra (GalleryAlgebra k Γ ν) ℤ :=
  (mapAlgHom ℤ (polyHom k Γ ν)).comp (aeval fun s => single (G.wt s) (X s))

theorem polyCo_of_isWeightedHomogeneous {f : PolyRing ν k} {D : ℤ}
    (hf : f.IsWeightedHomogeneous G.wt D) : G.polyCo f = single D (poly f) := by
  rw [polyCo, AlgHom.comp_apply, aeval_single_of_isWeightedHomogeneous G.wt hf,
    mapAlgHom_single]
  rfl

/-- Images of the generators under the coaction. -/
noncomputable def genImage : Gen k Γ ν → AddMonoidAlgebra (GalleryAlgebra k Γ ν) ℤ
  | .idem C => single 0 (e C)
  | .poly f => G.polyCo f
  | .step C C' => single (G.stepDeg C C') (t C C')
  | .relabel g C => single 0 (r g C)

/-- The coaction on the free algebra. -/
noncomputable def liftF : Fr →ₐ[k] AddMonoidAlgebra (GalleryAlgebra k Γ ν) ℤ :=
  FreeAlgebra.lift k G.genImage

@[simp] theorem liftF_fe (C : FullChamber Γ ν) : G.liftF (fe k Γ ν C) = single 0 (e C) := by
  simp [liftF, genImage]

@[simp] theorem liftF_fp (f : PolyRing ν k) : G.liftF (fp k Γ ν f) = G.polyCo f := by
  simp [liftF, genImage]

@[simp] theorem liftF_ft (C C' : FullChamber Γ ν) :
    G.liftF (ft k Γ ν C C') = single (G.stepDeg C C') (t C C') := by
  simp [liftF, genImage]

@[simp] theorem liftF_fr (g : ColPerm ν) (C : FullChamber Γ ν) :
    G.liftF (fr k Γ ν g C) = single 0 (r g C) := by
  simp [liftF, genImage]

/-- `u` is sent by the coaction to its image placed in degree `D`. -/
def IsHom (D : ℤ) (u : Fr) : Prop := G.liftF u = single D (mkF u)

variable {G} in
theorem IsHom.congr {D D' : ℤ} {u : Fr} (hu : G.IsHom D u) (h : D = D') : G.IsHom D' u :=
  h ▸ hu

theorem isHom_zero (D : ℤ) : G.IsHom D (0 : Fr) := by
  rw [IsHom, map_zero, map_zero, single_zero]

theorem isHom_one : G.IsHom 0 (1 : Fr) := by
  rw [IsHom, map_one, map_one]; rfl

variable {G} in
theorem IsHom.mul {D D' : ℤ} {u v : Fr} (hu : G.IsHom D u) (hv : G.IsHom D' v) :
    G.IsHom (D + D') (u * v) := by
  rw [IsHom, map_mul, hu, hv, single_mul_single, map_mul]

variable {G} in
theorem IsHom.add {D : ℤ} {u v : Fr} (hu : G.IsHom D u) (hv : G.IsHom D v) :
    G.IsHom D (u + v) := by
  rw [IsHom, map_add, hu, hv, ← single_add, map_add]

variable {G} in
theorem IsHom.neg {D : ℤ} {u : Fr} (hu : G.IsHom D u) : G.IsHom D (-u) := by
  rw [IsHom, map_neg, hu, ← single_neg, map_neg]

variable {G} in
theorem IsHom.sub {D : ℤ} {u v : Fr} (hu : G.IsHom D u) (hv : G.IsHom D v) :
    G.IsHom D (u - v) := by
  rw [sub_eq_add_neg]; exact hu.add hv.neg

theorem isHom_sum {ι : Type*} (s : Finset ι) {D : ℤ} {u : ι → Fr}
    (hu : ∀ i ∈ s, G.IsHom D (u i)) : G.IsHom D (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact G.isHom_zero D
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hu a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

theorem isHom_fe (C : FullChamber Γ ν) : G.IsHom 0 (fe k Γ ν C) := by
  rw [IsHom, liftF_fe]; rfl

theorem isHom_ft (C C' : FullChamber Γ ν) : G.IsHom (G.stepDeg C C') (ft k Γ ν C C') := by
  rw [IsHom, liftF_ft]; rfl

theorem isHom_fr (g : ColPerm ν) (C : FullChamber Γ ν) : G.IsHom 0 (fr k Γ ν g C) := by
  rw [IsHom, liftF_fr]; rfl

theorem isHom_fp {f : PolyRing ν k} {D : ℤ} (hf : f.IsWeightedHomogeneous G.wt D) :
    G.IsHom D (fp k Γ ν f) := by
  rw [IsHom, liftF_fp, G.polyCo_of_isWeightedHomogeneous hf]; rfl

theorem isHom_fp_monomial (m : Strand ν →₀ ℕ) (c : k) :
    G.IsHom (Finsupp.weight G.wt m) (fp k Γ ν (monomial m c)) :=
  G.isHom_fp (isWeightedHomogeneous_monomial _ _ _ rfl)

theorem isHom_ft_of_adjacent {C C' : FullChamber Γ ν} {h : Hyp Γ ν} (hC : C.Adjacent C' h) :
    G.IsHom (G.hypDeg h) (ft k Γ ν C C') :=
  (G.isHom_ft C C').congr (G.stepDeg_of_adjacent hC)

/-- A relation between two elements of the same degree is respected by the coaction. -/
theorem liftF_eq_of_rel {a b : Fr} (hr : Rel k Γ ν a b) {D D' : ℤ} (ha : G.IsHom D a)
    (hb : G.IsHom D' b) (hD : D = D') : G.liftF a = G.liftF b := by
  rw [ha, hb, GalleryAlgebra.rel hr, hD]

theorem isHom_gal₁ (H : Hexagon Γ ν) :
    G.IsHom (G.hypDeg H.h₃ + G.hypDeg H.h₂ + G.hypDeg H.h₁) (H.gal₁ k Γ ν) :=
  ((G.isHom_ft_of_adjacent H.adj₂₃).mul (G.isHom_ft_of_adjacent H.adj₁₂)).mul
    (G.isHom_ft_of_adjacent H.adj₀₁)

theorem isHom_gal₂ (H : Hexagon Γ ν) :
    G.IsHom (G.hypDeg H.h₃ + G.hypDeg H.h₂ + G.hypDeg H.h₁) (H.gal₂ k Γ ν) :=
  (((G.isHom_ft_of_adjacent H.adj₄₃).mul (G.isHom_ft_of_adjacent H.adj₅₄)).mul
    (G.isHom_ft_of_adjacent H.adj₀₅)).congr (by ring)

/-! ### Homogeneity of the defining relations -/

theorem isHom_hex_mid_diag_correction (H : Hexagon Γ ν) (w : Wall Γ ν) (d : Diag ν) :
    G.IsHom (2 * G.wall w.edge + G.cross d.fst.1 + 0)
      (fp k Γ ν (stepFactor Γ (d.left H.A₁) (d.right H.A₁) w.factor) * fr k Γ ν d.refl H.A₀) := by
  refine (G.isHom_fp ?_).mul (G.isHom_fr _ _)
  have := G.isWeightedHomogeneous_stepFactor (Diag.left_ne_right H.A₁ d)
    ((Diag.left_fst H.A₁ d).trans (Diag.right_fst H.A₁ d).symm) (G.isWeightedHomogeneous_factor w)
  rwa [Diag.left_fst] at this

theorem isHom_loopCorrection (H : Hexagon Γ ν) (d₁ d₂ d₃ : Diag ν) (u v w : Strand ν)
    (h₁ : H.h₁ = .inr d₁) (h₃ : H.h₃ = .inr d₃) (j₁ : d₁.Joins u v) (j₂ : d₂.Joins u w)
    (j₃ : d₃.Joins v w) {P : MvPolynomial (Fin 2) k} (hP : Γ.loop u.1 = some P) :
    G.IsHom (G.cross u.1 + G.cross u.1 + 0 + G.cross u.1)
      (H.loopCorrection k Γ ν d₁ d₂ d₃ u v w P) := by
  have hv := (Diag.Joins.fst_eq j₁).2
  have hw := (Diag.Joins.fst_eq j₂).2
  have hv' := congrArg Subtype.val hv
  have hw' := congrArg Subtype.val hw
  have Puv := G.isWeightedHomogeneous_loopFactor (ν := ν) (a := u) (b := v) hP rfl hv'
  have Puw := G.isWeightedHomogeneous_loopFactor (ν := ν) (a := u) (b := w) hP rfl hw'
  have Pvw := G.isWeightedHomogeneous_loopFactor (ν := ν) (a := v) (b := w) hP hv' hw'
  have e₁ : G.hypDeg H.h₁ = G.cross u.1 := by rw [h₁, hypDeg, (Diag.Joins.fst_eq j₁).1]
  have e₃ : G.hypDeg H.h₃ = G.cross u.1 := by rw [h₃, hypDeg, (Diag.Joins.fst_eq j₃).1, hv]
  unfold Hexagon.loopCorrection
  refine IsHom.add ?_ ?_
  · refine ((G.isHom_fp ?_).mul (G.isHom_fr _ _)).mul
      ((G.isHom_ft_of_adjacent H.adj₀₁).congr e₁)
    exact ((Puv.mul Puw).sub (Pvw.mul Puw) |>.sub (Pvw.mul Puv)).neg
  · refine ((G.isHom_fp ?_).mul (G.isHom_fr _ _)).mul
      ((G.isHom_ft_of_adjacent H.adj₀₅).congr e₃)
    exact ((Puv.mul Puw).add (Puv.mul Pvw) |>.sub (Puw.mul Pvw)).neg

/-- The coaction respects the defining relations: every relation of Webster's Definition 2.4,
read for labelled strands, is homogeneous. -/
theorem liftF_rel {a b : Fr} (h : Rel k Γ ν a b) : G.liftF a = G.liftF b := by
  induction h with
  | idem_mul C D =>
    refine G.liftF_eq_of_rel (.idem_mul C D) ((G.isHom_fe C).mul (G.isHom_fe D)) (D' := 0)
      ?_ (add_zero 0)
    split_ifs
    · exact G.isHom_fe C
    · exact G.isHom_zero 0
  | idem_sum =>
    exact G.liftF_eq_of_rel .idem_sum (G.isHom_sum _ fun C _ => G.isHom_fe C) G.isHom_one rfl
  | poly_add f g => rw [map_add, liftF_fp, liftF_fp, liftF_fp, map_add]
  | poly_mul f g => rw [map_mul, liftF_fp, liftF_fp, liftF_fp, map_mul]
  | poly_C c => rw [liftF_fp, AlgHom.commutes, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  | poly_idem f C =>
    induction f using MvPolynomial.induction_on' with
    | monomial m c =>
      exact G.liftF_eq_of_rel (.poly_idem _ C) ((G.isHom_fp_monomial m c).mul (G.isHom_fe C))
        ((G.isHom_fe C).mul (G.isHom_fp_monomial m c)) (add_comm _ _)
    | add f g hf hg =>
      simp only [map_mul, liftF_fp, map_add, add_mul, mul_add] at hf hg ⊢
      rw [hf, hg]
  | step_idem C C' =>
    exact G.liftF_eq_of_rel (.step_idem C C') (G.isHom_ft C C')
      (((G.isHom_fe C').mul (G.isHom_ft C C')).mul (G.isHom_fe C)) (by ring)
  | step_zero C C' h =>
    exact G.liftF_eq_of_rel (.step_zero C C' h) (G.isHom_ft C C') (G.isHom_zero _) rfl
  | relabel_idem g C =>
    exact G.liftF_eq_of_rel (.relabel_idem g C) (G.isHom_fr g C)
      (((G.isHom_fe _).mul (G.isHom_fr g C)).mul (G.isHom_fe C)) (by ring)
  | relabel_one C =>
    exact G.liftF_eq_of_rel (.relabel_one C) (G.isHom_fr 1 C) (G.isHom_fe C) rfl
  | relabel_mul g g' C =>
    exact G.liftF_eq_of_rel (.relabel_mul g g' C) ((G.isHom_fr g _).mul (G.isHom_fr g' C))
      (G.isHom_fr _ C) (add_zero 0)
  | relabel_poly g C f =>
    induction f using MvPolynomial.induction_on' with
    | monomial m c =>
      have hren : (rename g.1 (monomial m c : PolyRing ν k)).IsWeightedHomogeneous G.wt
          (Finsupp.weight G.wt m) :=
        isWeightedHomogeneous_rename (w := G.wt) (w' := G.wt) (⇑g.1)
          (fun s => show G.dot _ = G.dot _ from
            congrArg (fun x : ν.support => G.dot (x : I)) (ColPerm.apply_fst g s))
          (isWeightedHomogeneous_monomial _ _ _ rfl)
      exact G.liftF_eq_of_rel (.relabel_poly g C _) ((G.isHom_fr g C).mul
        (G.isHom_fp_monomial m c)) ((G.isHom_fp hren).mul (G.isHom_fr g C)) (by ring)
    | add f f' hf hf' =>
      simp only [map_mul, liftF_fp, map_add, add_mul, mul_add] at hf hf' ⊢
      rw [hf, hf']
  | relabel_step g C C' =>
    exact G.liftF_eq_of_rel (.relabel_step g C C') ((G.isHom_fr g C').mul (G.isHom_ft C C'))
      ((G.isHom_ft _ _).mul (G.isHom_fr g C)) (by rw [stepDeg_smul]; ring)
  | wall_bigon C C' w h =>
    refine G.liftF_eq_of_rel (.wall_bigon C C' w h)
      ((G.isHom_ft_of_adjacent h.symm).mul (G.isHom_ft_of_adjacent h))
      ((G.isHom_fp (G.isWeightedHomogeneous_factor w)).mul (G.isHom_fe C)) ?_
    simp only [hypDeg]; ring
  | diag_bigon C C' d h =>
    refine G.liftF_eq_of_rel (.diag_bigon C C' d h)
      ((G.isHom_ft_of_adjacent h.symm).mul (G.isHom_ft_of_adjacent h))
      (D' := G.cross d.fst.1 + 0 + G.cross d.fst.1) ?_ (by simp only [hypDeg]; ring)
    split
    · exact G.isHom_zero _
    · next P hP =>
      refine ((G.isHom_fp ?_).mul (G.isHom_fr _ _)).mul (G.isHom_ft_of_adjacent h)
      have := (isWeightedHomogeneous_C G.wt (-2 : k)).mul
        (G.isWeightedHomogeneous_loopFactor hP (congrArg Subtype.val (Diag.left_fst C d))
          (congrArg Subtype.val (Diag.right_fst C d)))
      rwa [map_neg, map_ofNat, zero_add] at this
  | wall_poly C C' w h f =>
    induction f using MvPolynomial.induction_on' with
    | monomial m c =>
      exact G.liftF_eq_of_rel (.wall_poly C C' w h _) ((G.isHom_ft C C').mul
        (G.isHom_fp_monomial m c)) ((G.isHom_fp_monomial m c).mul (G.isHom_ft C C'))
        (add_comm _ _)
    | add f g hf hg =>
      simp only [map_mul, liftF_fp, map_add, add_mul, mul_add] at hf hg ⊢
      rw [hf, hg]
  | diag_poly C C' d h f =>
    induction f using MvPolynomial.induction_on' with
    | monomial m c =>
      have hs := G.isWeightedHomogeneous_stepFactor (Diag.left_ne_right C d)
        ((Diag.left_fst C d).trans (Diag.right_fst C d).symm)
        (isWeightedHomogeneous_monomial (R := k) G.wt m c rfl)
      exact G.liftF_eq_of_rel (.diag_poly C C' d h _)
        (((G.isHom_ft C C').mul (G.isHom_fp_monomial m c)).sub
          (((G.isHom_fp_monomial m c).mul (G.isHom_ft C C')).congr (add_comm _ _)))
        ((G.isHom_fp hs).mul (G.isHom_fr _ _))
        (by rw [G.stepDeg_of_adjacent h, Diag.left_fst, hypDeg]; ring)
    | add f g hf hg =>
      simp only [map_sub, map_mul, liftF_fp, map_add, stepFactor_add, add_mul,
        mul_add] at hf hg ⊢
      rw [← hf, ← hg]
      abel
  | square C B B' D h₁ h₂ hne hi a₁ a₂ a₃ a₄ =>
    exact G.liftF_eq_of_rel (.square C B B' D h₁ h₂ hne hi a₁ a₂ a₃ a₄)
      ((G.isHom_ft_of_adjacent a₂).mul (G.isHom_ft_of_adjacent a₁))
      ((G.isHom_ft_of_adjacent a₄).mul (G.isHom_ft_of_adjacent a₃)) (add_comm _ _)
  | hex_walls H h₁ h₂ h₃ =>
    exact G.liftF_eq_of_rel (.hex_walls H h₁ h₂ h₃) (G.isHom_gal₁ H) (G.isHom_gal₂ H) rfl
  | hex_mid_diag H w d h₁ h₂ h₃ hσ hA =>
    refine G.liftF_eq_of_rel (.hex_mid_diag H w d h₁ h₂ h₃ hσ hA)
      ((G.isHom_gal₁ H).sub (G.isHom_gal₂ H)) (G.isHom_hex_mid_diag_correction H w d) ?_
    rw [h₁, h₂, h₃]
    simp only [hypDeg]
    rw [show (w.comap d.refl).edge = w.edge from rfl]
    ring
  | hex_end_diag H w d h₂ hd hσ =>
    exact G.liftF_eq_of_rel (.hex_end_diag H w d h₂ hd hσ) (G.isHom_gal₁ H) (G.isHom_gal₂ H) rfl
  | hex_diags H d₁ d₂ d₃ u v w h₁ h₂ h₃ j₁ j₂ j₃ hA =>
    refine G.liftF_eq_of_rel (.hex_diags H d₁ d₂ d₃ u v w h₁ h₂ h₃ j₁ j₂ j₃ hA)
      ((G.isHom_gal₁ H).sub (G.isHom_gal₂ H))
      (D' := G.cross u.1 + G.cross u.1 + 0 + G.cross u.1) ?_ ?_
    · split
      · exact G.isHom_zero _
      · next P hP => exact G.isHom_loopCorrection H d₁ d₂ d₃ u v w h₁ h₃ j₁ j₂ j₃ hP
    · rw [h₁, h₂, h₃]
      simp only [hypDeg]
      rw [(Diag.Joins.fst_eq j₁).1, (Diag.Joins.fst_eq j₂).1, (Diag.Joins.fst_eq j₃).1,
        (Diag.Joins.fst_eq j₁).2]
      ring

/-! ### The coaction and the grading of the gallery algebra -/

/-- The coaction `A → A[ℤ]` defining the grading: `e_C ↦ single 0 e_C`, a weighted homogeneous
polynomial of degree `D` goes to `single D`, a step `t C C'` to `single (stepDeg C C')` and a
relabelling to `single 0`. -/
noncomputable def coaction : GalleryAlgebra k Γ ν →ₐ[k] AddMonoidAlgebra (GalleryAlgebra k Γ ν) ℤ :=
  RingQuot.liftAlgHom k ⟨G.liftF, fun _ _ h => G.liftF_rel h⟩

theorem coaction_mk (u : Fr) : G.coaction (mkF u) = G.liftF u :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

variable (ν) in
/-- The grading of the gallery algebra: the degree `d` part is `{a | coaction a = single d a}`. -/
noncomputable def grade : ℤ → Submodule k (GalleryAlgebra k Γ ν) :=
  CoactionGrading.grade (G.coaction (ν := ν))

theorem mem_grade {d : ℤ} {a : GalleryAlgebra k Γ ν} :
    a ∈ G.grade ν d ↔ G.coaction a = single d a := Iff.rfl

theorem IsHom.mk_mem_grade {D : ℤ} {u : Fr} (h : G.IsHom D u) : mkF u ∈ G.grade ν D := by
  rw [mem_grade, coaction_mk]; exact h

/-- The idempotents `e_C` have degree `0`. -/
theorem e_mem_grade (C : FullChamber Γ ν) : (e C : GalleryAlgebra k Γ ν) ∈ G.grade ν 0 :=
  (G.isHom_fe C).mk_mem_grade

/-- A polynomial in the dots which is weighted homogeneous of degree `D` (dot on a strand of
label `i` in degree `dot i`) has degree `D`. -/
theorem poly_mem_grade {f : PolyRing ν k} {D : ℤ} (hf : f.IsWeightedHomogeneous G.wt D) :
    (poly f : GalleryAlgebra k Γ ν) ∈ G.grade ν D :=
  (G.isHom_fp hf).mk_mem_grade

/-- The monomial `x^m` has degree `∑_s m_s · dot (label s)`. -/
theorem poly_monomial_mem_grade (m : Strand ν →₀ ℕ) (c : k) :
    (poly (monomial m c) : GalleryAlgebra k Γ ν) ∈ G.grade ν (Finsupp.weight G.wt m) :=
  G.poly_mem_grade (isWeightedHomogeneous_monomial _ _ _ rfl)

/-- A step `t C C'` has degree `stepDeg C C'`: the degree of the crossed hyperplane when `C` and
`C'` are adjacent. -/
theorem t_mem_grade (C C' : FullChamber Γ ν) :
    (t C C' : GalleryAlgebra k Γ ν) ∈ G.grade ν (G.stepDeg C C') :=
  (G.isHom_ft C C').mk_mem_grade

/-- The relabellings `r g C` have degree `0`. -/
theorem r_mem_grade (g : ColPerm ν) (C : FullChamber Γ ν) :
    (r g C : GalleryAlgebra k Γ ν) ∈ G.grade ν 0 :=
  (G.isHom_fr g C).mk_mem_grade

/-- The degree of the gallery `galList C w`: the sum of the degrees of its steps. -/
noncomputable def galDeg : FullChamber Γ ν → List (Hyp Γ ν) → ℤ
  | _, [] => 0
  | C, h :: w => galDeg (C.flipH h) w + G.stepDeg C (C.flipH h)

/-- The gallery `galList C w` is homogeneous of degree `galDeg C w`. -/
theorem galList_mem_grade (C : FullChamber Γ ν) (w : List (Hyp Γ ν)) :
    galList k C w ∈ G.grade ν (G.galDeg C w) := by
  induction w generalizing C with
  | nil => exact G.e_mem_grade C
  | cons h w ih =>
    exact CoactionGrading.mul_mem_grade _ (ih _) (G.t_mem_grade _ _)

/-- `r g E · galList C w · x^m` is homogeneous of degree `galDeg C w + ∑_s m_s · dot (label s)`.
These are the elements of the basis of Webster's Theorem 2.8. -/
theorem r_mul_galList_mul_poly_mem_grade (g : ColPerm ν) (E C : FullChamber Γ ν)
    (w : List (Hyp Γ ν)) (m : Strand ν →₀ ℕ) :
    r g E * galList k C w * poly (monomial m 1) ∈
      G.grade ν (G.galDeg C w + Finsupp.weight G.wt m) := by
  have := CoactionGrading.mul_mem_grade _
    (CoactionGrading.mul_mem_grade _ (G.r_mem_grade g E) (G.galList_mem_grade C w))
    (G.poly_monomial_mem_grade m 1)
  rwa [zero_add] at this

/-- Every element of the gallery algebra is a sum of homogeneous elements. -/
theorem mem_homogeneousSubalgebra (a : GalleryAlgebra k Γ ν) :
    a ∈ CoactionGrading.homogeneousSubalgebra G.coaction := by
  obtain ⟨u, rfl⟩ := mk_surjective a
  induction u using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ c
  | grade1 x =>
    cases x with
    | idem C =>
      exact CoactionGrading.mem_homogeneousSubalgebra_of_mem_grade _ (G.e_mem_grade C)
    | poly f =>
      change poly f ∈ _
      rw [show (poly f : GalleryAlgebra k Γ ν) = polyHom k Γ ν f from rfl, f.as_sum, map_sum]
      exact Subalgebra.sum_mem _ fun m _ =>
        CoactionGrading.mem_homogeneousSubalgebra_of_mem_grade _
          (G.poly_monomial_mem_grade m (f.coeff m))
    | step C C' =>
      exact CoactionGrading.mem_homogeneousSubalgebra_of_mem_grade _ (G.t_mem_grade C C')
    | relabel g C =>
      exact CoactionGrading.mem_homogeneousSubalgebra_of_mem_grade _ (G.r_mem_grade g C)
  | mul u v hu hv => rw [map_mul]; exact Subalgebra.mul_mem _ hu hv
  | add u v hu hv => rw [map_add]; exact Subalgebra.add_mem _ hu hv

theorem counit : CoactionGrading.Counit (G.coaction (ν := ν)) :=
  CoactionGrading.counit_of_forall_mem _ G.mem_homogeneousSubalgebra

theorem coassoc : CoactionGrading.Coassoc (G.coaction (ν := ν)) :=
  CoactionGrading.coassoc_of_forall_mem _ G.mem_homogeneousSubalgebra

/-- The `ℤ`-grading of the gallery algebra defined by the grading datum `G` (Webster §2.1). -/
noncomputable instance gradedAlgebra : GradedAlgebra (G.grade ν) :=
  CoactionGrading.gradedAlgebra G.counit G.coassoc

/-- The degree `d` component of `a` is the coefficient of `single d` in `coaction a`. -/
theorem decompose_apply (a : GalleryAlgebra k Γ ν) (d : ℤ) :
    (DirectSum.decompose (G.grade ν) a d : GalleryAlgebra k Γ ν) = (G.coaction a).coeff d :=
  CoactionGrading.decompose_apply G.counit G.coassoc a d

end GradingDatum


/-! ### The grading datum of the standing hypothesis -/

section Weighted

variable {σ R : Type*} [CommRing R] {w : σ → ℤ}

/-- Multiplying by a weighted homogeneous polynomial of degree `a` shifts weighted homogeneous
components by `a`. -/
theorem weightedHomogeneousComponent_mul_of_isWeightedHomogeneous {φ : MvPolynomial σ R} {a : ℤ}
    (hφ : φ.IsWeightedHomogeneous w a) (m : ℤ) (P : MvPolynomial σ R) :
    weightedHomogeneousComponent w (a + m) (φ * P) = φ * weightedHomogeneousComponent w m P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    have hd : (monomial d c : MvPolynomial σ R).IsWeightedHomogeneous w (Finsupp.weight w d) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : Finsupp.weight w d = m
    · subst h
      rw [(hφ.mul hd).weightedHomogeneousComponent_same, hd.weightedHomogeneousComponent_same]
    · rw [(hφ.mul hd).weightedHomogeneousComponent_ne _ (by omega),
        hd.weightedHomogeneousComponent_ne _ (Ne.symm h), mul_zero]
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, mul_add]

/-- If `φ` is weighted homogeneous of degree `a` and a non-zero-divisor, and `φ P` is weighted
homogeneous of degree `n`, then `P` is weighted homogeneous of degree `n - a`. -/
theorem isWeightedHomogeneous_of_mul_left {φ P : MvPolynomial σ R} {a n : ℤ}
    (hφ : φ.IsWeightedHomogeneous w a) (hreg : IsRegular φ)
    (h : (φ * P).IsWeightedHomogeneous w n) : P.IsWeightedHomogeneous w (n - a) := by
  have hz : ∀ m, m ≠ n - a → weightedHomogeneousComponent w m P = 0 := fun m hm =>
    hreg.left (by
      change φ * _ = φ * 0
      rw [mul_zero, ← weightedHomogeneousComponent_mul_of_isWeightedHomogeneous hφ,
        h.weightedHomogeneousComponent_ne _ (by omega)])
  have hP : P = weightedHomogeneousComponent w (n - a) P := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent w P]
    exact finsum_eq_single _ _ hz
  rw [hP]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- Scaling natural weights and the degree by the same integer preserves weighted homogeneity. -/
theorem isWeightedHomogeneous_intCast_mul {w : σ → ℕ} {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsWeightedHomogeneous w n) (c : ℤ) :
    p.IsWeightedHomogeneous (fun j => c * (w j : ℤ)) (c * n) := by
  intro d hd
  rw [← hp hd, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
    Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
  ring

end Weighted

namespace WeightedGraph

/-- `u - v` is weighted homogeneous of degree `a` for the weights `(a, a)`. -/
theorem isWeightedHomogeneous_X_sub_X (a : ℤ) :
    (X 0 - X 1 : MvPolynomial (Fin 2) k).IsWeightedHomogeneous ![a, a] a := by
  have h0 := isWeightedHomogeneous_X k ![a, a] (0 : Fin 2)
  have h1 := isWeightedHomogeneous_X k ![a, a] (1 : Fin 2)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact h0.sub h1

theorem two_mul_vecCons_two (a b : ℕ) :
    (fun j => (2 : ℤ) * ((![a, b] : Fin 2 → ℕ) j : ℤ)) = ![2 * (a : ℤ), 2 * b] := by
  funext j; fin_cases j <;> rfl

namespace Standing

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

variable (h : Γ.Standing)
include h

/-- The symmetrizer `d` of the standing hypothesis. -/
noncomputable def symm (i : I) : ℕ := h.choose i

/-- The multiplicity `c_e` of the edge `e` in the standing hypothesis. -/
noncomputable def edgeMult (e : Γ.E) : ℕ := (h.choose_spec.2.1 e).choose

theorem isUnitHomogeneous_Q (e : Γ.E) :
    ∃ c', IsUnitHomogeneous (h.symm (Γ.head e)) (h.symm (Γ.tail e)) (h.edgeMult e) c' (Γ.Q e) :=
  (h.choose_spec.2.1 e).choose_spec

theorem exists_loopMult (i : I) : ∃ c : ℕ, ∀ P, Γ.loop i = some P →
    ∃ c', IsUnitHomogeneous (h.symm i) (h.symm i) c c' ((X 0 - X 1) * P) := by
  cases hl : Γ.loop i with
  | none => exact ⟨0, fun P hP => absurd hP (by simp)⟩
  | some Q =>
    obtain ⟨-, c, c', hc⟩ := h.choose_spec.2.2 i Q hl
    exact ⟨c, fun P hP => ⟨c', by rwa [← Option.some_injective _ hP]⟩⟩

/-- The multiplicity `c_i` of the loop of weight `0` at `i`: `(u - v) P_i` has degree
`d_i c_i`. -/
noncomputable def loopMult (i : I) : ℕ := (h.exists_loopMult i).choose

theorem isUnitHomogeneous_loop {i : I} {P : MvPolynomial (Fin 2) k} (hP : Γ.loop i = some P) :
    ∃ c', IsUnitHomogeneous (h.symm i) (h.symm i) (h.loopMult i) c' ((X 0 - X 1) * P) :=
  (h.exists_loopMult i).choose_spec P hP

open Classical in
/-- **The grading of Webster's standing hypothesis** (arXiv:1209.2463v4, §2.1), in the doubled
normalization of the module docstring: a dot on an `i`-strand has degree `2 d_i`, a wall of the
edge `e` degree `d_{h(e)} c_e`, and a crossing of two `i`-strands degree `-2 d_i`, or
`2 d_i (c_i - 1)` if there is a loop of weight `0` at `i`. -/
noncomputable def gradingDatum : GradingDatum Γ where
  dot i := 2 * h.symm i
  wall e := h.symm (Γ.head e) * h.edgeMult e
  cross i := if Γ.loop i = none then -(2 * h.symm i) else 2 * h.symm i * ((h.loopMult i : ℤ) - 1)
  isWeightedHomogeneous_Q e := by
    obtain ⟨c', -, hQ, -⟩ := h.isUnitHomogeneous_Q e
    have := isWeightedHomogeneous_intCast_mul hQ 2
    rw [two_mul_vecCons_two] at this
    convert this using 1
    push_cast; ring
  cross_of_loop_none i hi := by simp [hi]
  isWeightedHomogeneous_loop i P hP := by
    simp only [hP, reduceCtorEq, ↓reduceIte]
    obtain ⟨c', -, hQ, -⟩ := h.isUnitHomogeneous_loop hP
    have hQ' := isWeightedHomogeneous_intCast_mul hQ 2
    rw [two_mul_vecCons_two] at hQ'
    have := isWeightedHomogeneous_of_mul_left (isWeightedHomogeneous_X_sub_X (k := k) _)
      (isRegular_X_sub_X (by decide : (0 : Fin 2) ≠ 1)) hQ'
    convert this using 1
    push_cast; ring

@[simp] theorem gradingDatum_dot (i : I) : h.gradingDatum.dot i = 2 * h.symm i := rfl

@[simp] theorem gradingDatum_wall (e : Γ.E) :
    h.gradingDatum.wall e = h.symm (Γ.head e) * h.edgeMult e := rfl

theorem gradingDatum_cross_of_none {i : I} (hi : Γ.loop i = none) :
    h.gradingDatum.cross i = -(2 * h.symm i) := by simp [gradingDatum, hi]

theorem gradingDatum_cross_of_some {i : I} {P : MvPolynomial (Fin 2) k} (hP : Γ.loop i = some P) :
    h.gradingDatum.cross i = 2 * h.symm i * ((h.loopMult i : ℤ) - 1) := by
  simp [gradingDatum, hP]

end Standing

end WeightedGraph

end Categorification.WeightedKLR
