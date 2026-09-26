/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DividedDifference
import Categorification.Diagrams.NilHecke.Relations
import StringDiagrams.LocalInterpretation

/-!
# The polynomial representation of the nilHecke category

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.2, Example 3 (the nilHecke ring acting on polynomials) and §2.3 (the
action of `R(ν)` on `Pol_ν`, Proposition 2.3), specialised to a single colour.

The nilHecke category acts on polynomials: every object is sent to the polynomial ring
`MvPolynomial ℕ k` in the variables `X 0, X 1, …`, a dot with `i` strands to its left acts by
multiplication by `X i`, and a crossing with `i` strands to its left acts by the divided
difference operator `Categorification.ddiff i (i + 1)`. The endomorphisms of `n` strands only
involve the first `n` variables; the comparison with the nilHecke ring
`Categorification.NilHecke.nilHecke k n ⊆ End_k(k[x_0, …, x_{n-1}])` is in
`Categorification.Diagrams.NilHecke.Comparison`, where this representation is shown to be
faithful on `n` strands.

The representation is built with `StringDiagrams.LocalInterpretation.uniform` (a single module
for all objects); soundness is checked by linear evaluation (`LocalInterpretation.respects_of`),
the interchange law by the commutation of generators at disjoint positions (`genOp_comm`,
`LocalInterpretation.evalW_interchange_eq_zero_of_comm`).

## Main declarations

* `genOp k g i`: the operator of the generator `g` with `i` strands to its left.
* `polyLocal k`, `polyFunctor k`: the interpretation of the free 2-category, and its functor.
* `polyFunctor_respects`: every whiskered defining relation and every whiskered instance of the
  interchange law is sent to zero.
* `polyRep k : NH k ⥤ ModuleCat k`, a `k`-linear functor.
* `realize k n : End ((pres k).obj (strands n)) →ₐ[k] Module.End k (MvPolynomial ℕ k)`, the
  induced algebra map, with `realize_x` and `realize_ψ`.
* `x_ne_zero`, `ψ_ne_zero`: over a nontrivial ring, dots and crossings are nonzero, so the
  presentation does not collapse.
-/

noncomputable section

namespace Categorification.NilHecke.Diagram

open CategoryTheory StringDiagrams MvPolynomial Equiv

universe u

variable (k : Type u) [CommRing k]

/-! ## Operators of generators and layers -/

/-- The operator of a generator with `i` strands to its left: multiplication by `X i` for a
dot, the divided difference `∂_{i, i+1}` for a crossing. -/
def genOp : Gen → ℕ → Module.End k (MvPolynomial ℕ k)
  | .dot, i => LinearMap.mulLeft k (X i)
  | .cross, i => ddiff i (i + 1)

@[simp] theorem genOp_dot (i : ℕ) : genOp k .dot i = LinearMap.mulLeft k (X i) := rfl

@[simp] theorem genOp_cross (i : ℕ) : genOp k .cross i = ddiff i (i + 1) := rfl

/-- The operator of a layer: its generator, acting at the position given by the number of
strands to its left. -/
def layerOp (L : Layer sig) : Module.End k (MvPolynomial ℕ k) :=
  genOp k L.gen L.left.length

private theorem ne_succ (i : ℕ) : i ≠ i + 1 := by omega

/-- Generators at positions `i` and `j`, with `g` entirely to the left of `h`, act by
commuting operators. -/
theorem genOp_comm (g h : Gen) {i j : ℕ} (hij : i + g.arity ≤ j) :
    genOp k h j ∘ₗ genOp k g i = genOp k g i ∘ₗ genOp k h j := by
  refine LinearMap.ext fun f => ?_
  cases g <;> cases h <;> simp only [Gen.arity] at hij <;>
    simp only [genOp, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  · ring
  · exact ddiff_mul_of_rename_eq (ne_succ j)
      (by rw [rename_X, swap_apply_of_ne_of_ne (by omega) (by omega)]) f
  · exact (ddiff_mul_of_rename_eq (ne_succ i)
      (by rw [rename_X, swap_apply_of_ne_of_ne (by omega) (by omega)]) f).symm
  · exact ddiff_ddiff_comm (ne_succ j) (ne_succ i) (by omega) (by omega) (by omega) (by omega) f

/-! ## The interpretation -/

/-- The polynomial ring `MvPolynomial ℕ k` as an object of `ModuleCat k`. -/
abbrev polyModule : ModuleCat.{u} k := ModuleCat.of k (MvPolynomial ℕ k)

/-- The polynomial interpretation by local operators, with a single module for all objects. -/
def polyLocal :
    LocalInterpretation sig k (MvPolynomial ℕ k) (fun _ : Unit => MvPolynomial ℕ k) :=
  LocalInterpretation.uniform (layerOp k)

/-- The functor from the free 2-category determined by `polyLocal`. -/
def polyFunctor : Obj sig ⥤ ModuleCat.{u} k := (polyLocal k).functor

/-! ## Soundness hypotheses -/

section Respects

variable {k}

open LinDiagram LocalInterpretation

private theorem layerOp_whisker (L : Layer sig) (u : Obj sig) (v : List sig.Colour) :
    layerOp k (L.whisker u v) = genOp k L.gen (u.word.length + L.left.length) := by
  simp [layerOp, Layer.whisker]

/-- Evaluation of a whiskered relation as a combination of composites of operators, applied
to a polynomial. -/
local macro "eval_relation" : tactic => `(tactic| (
  simp only [pres, relation, evalW_sub, polyLocal, uniform_evalW_of, Diagram.layers_comp,
    Diagram.layers_id, layers_dlay, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, uniform_opList_cons, opList_nil, layerOp_whisker, lay, List.length_replicate,
    add_zero, genOp_cross, genOp_dot]))

/-- Pointwise form of an evaluated relation. -/
local macro "eval_apply" : tactic => `(tactic| simp only [LinearMap.sub_apply,
  LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply, LinearMap.mulLeft_apply])

theorem polyLocal_rel (r : (pres k).Rel) (u : Obj sig) (v : List sig.Colour) :
    (polyLocal k).evalW () () u v ((pres k).rel r) = 0 := by
  cases r
  · eval_relation
    refine LinearMap.ext fun f => ?_
    eval_apply
    exact ddiff_ddiff (ne_succ _) f
  · eval_relation
    refine LinearMap.ext fun f => ?_
    eval_apply
    rw [ddiff_braid (ne_succ _) (ne_succ _) (by omega) f, sub_self]
  · eval_relation
    refine LinearMap.ext fun f => ?_
    eval_apply
    rw [ddiff_mul (ne_succ _), ddiff_X_right (ne_succ _), rename_X, swap_apply_right]
    ring
  · eval_relation
    refine LinearMap.ext fun f => ?_
    eval_apply
    rw [ddiff_mul (ne_succ _), ddiff_X_left (ne_succ _), rename_X, swap_apply_left]
    ring

theorem polyLocal_interchange (d : InterchangeData sig) (hd : d.Valid) (u : Obj sig)
    (v : List sig.Colour) :
    (polyLocal k).evalW () () u v (InterchangeData.rel k hd) = 0 := by
  refine (polyLocal k).evalW_interchange_eq_zero_of_comm (fun s l m r g g' => ?_) d hd u v
  have hs : (((⟨s, g, m, g'⟩ : InterchangeData sig).sign : ℤ) : k) = 1 := by
    simp [InterchangeData.sign, sig]
  have hc : (sig.cod g).length = (sig.dom g).length := rfl
  simp only [polyLocal, uniform_op, layerOp, List.length_append, hs, one_smul, hc]
  exact genOp_comm k g g' (by simp)

/-- `polyFunctor` respects the nilHecke presentation: every whiskered defining relation and
every whiskered instance of the interchange law is sent to zero. -/
theorem polyFunctor_respects : (pres k).Respects (polyFunctor k) :=
  (polyLocal k).respects_of (pres k) (fun r u v _ => polyLocal_rel r u v)
    (fun d hd u v _ => polyLocal_interchange d hd u v)

end Respects

/-! ## The polynomial representation -/

/-- The polynomial representation of the nilHecke category. -/
def polyRep : NH k ⥤ ModuleCat.{u} k := (pres k).lift (polyFunctor_respects (k := k))

instance : (polyRep k).Additive := Presentation.lift_additive _

instance : (polyRep k).Linear k := Presentation.lift_linear _

/-- The class of a diagram acts by the composite of the operators of its layers. -/
theorem polyRep_map_diag {a b : Obj sig} (f : a ⟶ b) :
    ((polyRep k).map ((pres k).diag f)).hom = (polyLocal k).opList (Diagram.layers f) :=
  (congrArg ModuleCat.Hom.hom (Presentation.lift_diag _ f)).trans
    (LocalInterpretation.uniform_functor_map_hom _ f)

/-- The polynomial representation on `n` strands, as an algebra map. -/
def realize (n : ℕ) :
    End ((pres k).obj (strands n)) →ₐ[k] Module.End k (MvPolynomial ℕ k) where
  toFun f := ((polyRep k).map f).hom
  map_one' := by rw [End.one_def, (polyRep k).map_id]; rfl
  map_mul' f g := by rw [End.mul_def, (polyRep k).map_comp]; rfl
  map_zero' := by rw [(polyRep k).map_zero]; rfl
  map_add' f g := by rw [(polyRep k).map_add]; rfl
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, End.one_def,
      (polyRep k).map_smul, (polyRep k).map_id]
    rfl

theorem realize_apply (n : ℕ) (f : End ((pres k).obj (strands n))) :
    realize k n f = ((polyRep k).map f).hom := rfl

/-- A dot on strand `i` acts by multiplication by `X i`. -/
theorem realize_x {n i : ℕ} (h : i < n) : realize k n (x k n i) = LinearMap.mulLeft k (X i) := by
  rw [realize_apply, x_def k h, polyRep_map_diag, layers_dlay]
  refine LinearMap.ext fun f => ?_
  simp [polyLocal, layerOp, lay]

/-- The crossing of strands `i` and `i + 1` acts by the divided difference `∂_{i, i+1}`. -/
theorem realize_ψ {n i : ℕ} (h : i + 1 < n) : realize k n (ψ k n i) = ddiff i (i + 1) := by
  rw [realize_apply, ψ_def k h, polyRep_map_diag, layers_dlay]
  refine LinearMap.ext fun f => ?_
  simp [polyLocal, layerOp, lay]

/-! ## Nonvanishing -/

/-- Over a nontrivial ring, a dot on any strand is nonzero. -/
theorem x_ne_zero [Nontrivial k] {n i : ℕ} (h : i < n) : x k n i ≠ 0 := by
  intro h0
  have h1 := LinearMap.congr_fun ((realize_x k h).symm.trans (by rw [h0, map_zero])) 1
  rw [LinearMap.mulLeft_apply, mul_one, LinearMap.zero_apply] at h1
  exact X_ne_zero i h1

/-- Over a nontrivial ring, a crossing of adjacent strands is nonzero. -/
theorem ψ_ne_zero [Nontrivial k] {n i : ℕ} (h : i + 1 < n) : ψ k n i ≠ 0 := by
  intro h0
  have h1 := LinearMap.congr_fun ((realize_ψ k h).symm.trans (by rw [h0, map_zero])) (X i)
  rw [ddiff_X_left (ne_succ i), LinearMap.zero_apply] at h1
  exact one_ne_zero h1

end Categorification.NilHecke.Diagram

end
