/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.Presentation

/-!
# Rescaling generators of a presented linear 2-category

This file contains the generic machinery behind the rescaling isomorphisms between the
2-categories `U_Q(g)` of Cautis–Lauda for different choices of scalars
(`Categorification.Diagrams.CL.Rescale`).

## Rescaling diagrams

Let `S` be a signature, `k` a commutative ring and `χ : S.Gen → kˣ` a unit for every generator.
The *weight* of a diagram is the product of `χ` over its layers (`weight`). Multiplying every
diagram by its weight is a `k`-linear functor of the free linear 2-category (`scL χ`, the linear
extension of `scObj χ`), which commutes with whiskering (`scL_whisker`) and multiplies the
interchange law by the unit `χ g χ h` (`scL_interchange`).

Hence, for presentations `P` and `P'` on `S`, if the rescaled relations of `P` hold in `P'`
(`h : ∀ i, P'.lin (scL χ (P.rel i)) = 0`), then rescaling descends to a `k`-linear functor
`functor χ h : P.Presented ⥤ P'.Presented` (`Presentation.lift`), which is the identity on
objects, sends the class of a diagram `d` to `weight χ d • d` (`functor_diag`), commutes with
whiskering (`functor_whisk`; so it is a strict 2-functor between the presented 2-categories,
which are the identity on objects and on 1-morphisms) and preserves degrees
(`functor_homDeg`). If moreover the rescaled relations of `P'` for `χ⁻¹` hold in `P`, the two
functors are mutually inverse (`functor_inv_functor`, `functor_comp_functor_inv`), giving an
isomorphism of categories `equiv`.

## Rescaling polynomials

For the KLR relations the dots enter through polynomials `ncEval y p`. If each variable is
rescaled, `y t ↦ u t • y t`, then `ncEval (u • y) p = ncEval y (scaleP u p)` where
`scaleP u p = p(u₀ x₀, u₁ x₁, …)` (`ncEval_smul`), and the divided difference satisfies
`Q̄(u x₀, v x₁, u x₂) · u = ` the divided difference of `Q(u x₀, v x₁)` (`qbar_scaleP`). The
recursion `grassInv` defining fake bubbles is compatible with rescaling the `a`-th term by `t^a`
(`grassInv_smul`).
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL.Rescale

open CategoryTheory StringDiagrams MvPolynomial

universe w v u₀ u₁ u₂

/-! ## The weight of a diagram -/

section Generic

variable {S : Signature.{u₀, u₁, u₂}} {k : Type w} [CommRing k] (χ : S.Gen → kˣ)

/-- The weight of a list of layers: the product of the units of their generators. -/
def weight (ls : List (Layer S)) : kˣ := (ls.map fun L => χ L.gen).prod

@[simp] theorem weight_nil : weight χ [] = 1 := rfl

@[simp] theorem weight_cons (L : Layer S) (ls : List (Layer S)) :
    weight χ (L :: ls) = χ L.gen * weight χ ls := by
  simp [weight]

theorem weight_append (ls ms : List (Layer S)) :
    weight χ (ls ++ ms) = weight χ ls * weight χ ms := by
  simp [weight]

theorem weight_map_whisker (ls : List (Layer S)) (u : Obj S) (v : List S.Colour) :
    weight χ (ls.map (·.whisker u v)) = weight χ ls := by
  simp only [weight, List.map_map, Function.comp_def]
  rfl

/-- Rescaling on the free 2-category: every diagram times its weight. -/
def scObj : Obj S ⥤ Free k (Obj S) where
  obj a := a
  map d := ((weight χ (Diagram.layers d) : kˣ) : k) • LinDiagram.of d
  map_id a := by
    show ((weight χ (Diagram.layers (𝟙 a)) : kˣ) : k) • LinDiagram.of (𝟙 a) = _
    rw [Diagram.layers_id, weight_nil, Units.val_one, one_smul]
    rfl
  map_comp f g := by
    show ((weight χ (Diagram.layers (f ≫ g)) : kˣ) : k) • LinDiagram.of (f ≫ g) = _
    rw [Diagram.layers_comp, weight_append, LinDiagram.of_comp, Units.val_mul, mul_smul]
    rw [Linear.smul_comp, Linear.comp_smul, smul_comm]

/-- Rescaling of linear combinations of diagrams. -/
abbrev scL {a b : Obj S} (f : LinDiagram k a b) : LinDiagram k a b :=
  (freeLift k (scObj χ)).map f

variable {χ}

theorem scL_single {a b : Obj S} (d : a ⟶ b) (r : k) :
    scL χ (Finsupp.single d r : LinDiagram k a b) =
      r • ((weight χ (Diagram.layers d) : kˣ) : k) • LinDiagram.of d :=
  freeLift_map_single _ d r

theorem scL_of {a b : Obj S} (d : a ⟶ b) :
    scL χ (LinDiagram.of d) = ((weight χ (Diagram.layers d) : kˣ) : k) • LinDiagram.of d :=
  freeLift_map_of _ d

theorem scL_of_id (a : Obj S) :
    scL χ (LinDiagram.of (𝟙 a) : LinDiagram k a a) = LinDiagram.of (𝟙 a) := by
  rw [scL_of, Diagram.layers_id, weight_nil, Units.val_one, one_smul]

theorem scL_add {a b : Obj S} (f g : LinDiagram k a b) : scL χ (f + g) = scL χ f + scL χ g :=
  Functor.map_add _

theorem scL_sub {a b : Obj S} (f g : LinDiagram k a b) : scL χ (f - g) = scL χ f - scL χ g :=
  Functor.map_sub _

theorem scL_neg {a b : Obj S} (f : LinDiagram k a b) : scL χ (-f) = -scL χ f :=
  Functor.map_neg _

theorem scL_zero {a b : Obj S} : scL χ (0 : LinDiagram k a b) = 0 :=
  Functor.map_zero _ _ _

theorem scL_smul {a b : Obj S} (r : k) (f : LinDiagram k a b) : scL χ (r • f) = r • scL χ f :=
  Functor.map_smul _ _ _

theorem scL_comp {a b c : Obj S} (f : LinDiagram k a b) (g : LinDiagram k b c) :
    scL χ (f ≫ g) = scL χ f ≫ scL χ g :=
  Functor.map_comp _ _ _

theorem scL_id (a : Obj S) : scL χ (𝟙 (Free.of k a)) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

theorem scL_sum {a b : Obj S} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    scL χ (∑ x ∈ s, f x) = ∑ x ∈ s, scL χ (f x) :=
  Functor.map_sum _ _ _

variable (χ) in
/-- Rescaling as a `k`-algebra homomorphism on endomorphism algebras. -/
def scEnd (a : Obj S) : End (Free.of k a) →ₐ[k] End (Free.of k a) where
  toFun := scL χ
  map_one' := scL_id a
  map_mul' f g := scL_comp g f
  map_zero' := scL_zero
  map_add' := scL_add
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [scL_smul]
    exact congrArg (r • ·) (scL_id a)

theorem scEnd_apply (a : Obj S) (f : End (Free.of k a)) : scEnd χ a f = scL χ f := rfl

theorem scL_whisker {a b : Obj S} (f : LinDiagram k a b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) :
    scL χ (LinDiagram.whisker f u v hw) = LinDiagram.whisker (scL χ f) u v hw := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [show LinDiagram.whisker (0 : LinDiagram k a b) u v hw = 0 from Finsupp.mapDomain_zero,
      scL_zero, scL_zero, show LinDiagram.whisker (0 : LinDiagram k a b) u v hw = 0 from
        Finsupp.mapDomain_zero]
  | add f g hf hg => rw [LinDiagram.whisker_add, scL_add, hf, hg, scL_add, LinDiagram.whisker_add]
  | single d r =>
    rw [LinDiagram.whisker_single, scL_single, scL_single, Diagram.layers_whisker,
      weight_map_whisker, LinDiagram.whisker_smul, LinDiagram.whisker_smul, LinDiagram.whisker_of]

theorem scL_whisk {a b : Obj S} (f : LinDiagram k a b) (u : Obj S) (v : List S.Colour) :
    scL χ (LinDiagram.whisk f u v) = LinDiagram.whisk (scL χ f) u v := by
  by_cases h : a.WhiskerOK u v
  · rw [LinDiagram.whisk_of_ok _ h, LinDiagram.whisk_of_ok _ h, scL_whisker]
  · rw [LinDiagram.whisk_of_not_ok _ h, LinDiagram.whisk_of_not_ok _ h, scL_zero]

theorem scL_cast {a b a' b' : Obj S} (f : LinDiagram k a b) (ha : a = a') (hb : b = b') :
    scL χ (LinDiagram.cast f ha hb) = LinDiagram.cast (scL χ f) ha hb := by
  subst ha hb
  rw [LinDiagram.cast_rfl, LinDiagram.cast_rfl]

/-- The interchange law is multiplied by the unit `χ g χ h`. -/
theorem scL_interchange (x : InterchangeData S) (hx : x.Valid) :
    scL χ (InterchangeData.rel k hx) =
      ((χ x.g * χ x.h : kˣ) : k) • InterchangeData.rel k hx := by
  rw [InterchangeData.rel, scL_sub, scL_smul, scL_of, scL_of, smul_sub, smul_comm _ (_ : k)]
  congr 3
  · simp [InterchangeData.ghDiagram, InterchangeData.gh₁, InterchangeData.gh₂]
  · simp [InterchangeData.hgDiagram, InterchangeData.hg₁, InterchangeData.hg₂, mul_comm]

/-- If `χ' χ = 1`, rescaling by `χ'` undoes rescaling by `χ`. -/
theorem scL_scL {χ' : S.Gen → kˣ} (hχ : ∀ g, χ' g * χ g = 1) {a b : Obj S}
    (f : LinDiagram k a b) : scL χ' (scL χ f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [scL_zero, scL_zero]
  | add f g hf hg => rw [scL_add, scL_add, hf, hg]
  | single d r =>
    have : weight χ' (Diagram.layers d) * weight χ (Diagram.layers d) = 1 := by
      simp only [weight, ← List.prod_map_mul, hχ, List.map_const', List.prod_replicate, one_pow]
    rw [scL_single, scL_smul, scL_smul, scL_of, smul_smul, smul_smul, mul_assoc, ← Units.val_mul,
      mul_comm (weight χ _), this, Units.val_one, mul_one, Finsupp.smul_single_one]

/-- Rescaling preserves the degree of homogeneous linear combinations of diagrams. -/
theorem scL_mem_homDeg {A : Type*} [AddCommMonoid A] {deg : S.Gen → A} {a b : Obj S}
    {f : LinDiagram k a b} {d : A} (hf : f ∈ LinDiagram.homDeg k deg a b d) :
    scL χ f ∈ LinDiagram.homDeg k deg a b d := by
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [scL_single]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (LinDiagram.of_mem_homDeg' hg))
  | zero => rw [scL_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [show scL χ (x + y : LinDiagram k a b) = scL χ x + scL χ y from scL_add x y]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [scL_smul]; exact Submodule.smul_mem _ r hx

/-! ## Descent to presented categories -/

variable {P P' : Presentation.{w, v} S k}

variable (χ P') in
/-- Rescaling followed by the quotient functor of `P'`. -/
def scP : Obj S ⥤ P'.Presented := scObj χ ⋙ P'.linFunctor

theorem freeLift_scP {a b : Obj S} (f : LinDiagram k a b) :
    (freeLift k (scP χ P')).map f = P'.lin (scL χ f) := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Functor.map_zero, scL_zero, Presentation.lin_zero]
  | add f g hf hg => rw [Functor.map_add, hf, hg, scL_add, Presentation.lin_add]
  | single d r =>
    rw [freeLift_map_single, scL_single, Presentation.lin_smul, Presentation.lin_smul]
    rfl

/-- **Soundness of rescaling**: if the rescaled relations of `P` hold in `P'`, rescaling
respects the relations of `P` (whiskered) and the interchange law. -/
theorem respects (h : ∀ i, P'.lin (scL χ (P.rel i)) = 0) : P.Respects (scP χ P') where
  rel i u v hw := by
    rw [freeLift_scP, scL_whisker, ← LinDiagram.whisk_of_ok _ hw, ← Presentation.whisk_lin, h,
      Presentation.whisk_zero]
  interchange x hx u v hw := by
    rw [freeLift_scP, scL_whisker, scL_interchange, LinDiagram.whisker_smul,
      Presentation.lin_smul, Presentation.lin_interchange, smul_zero]

variable (χ) in
/-- **The rescaling functor** `P.Presented ⥤ P'.Presented`: the identity on objects, the class
of a diagram `d` goes to `weight χ d • d`. -/
def functor (h : ∀ i, P'.lin (scL χ (P.rel i)) = 0) : P.Presented ⥤ P'.Presented :=
  P.lift (respects h)

variable (h : ∀ i, P'.lin (scL χ (P.rel i)) = 0)

instance : (functor χ h).Additive := by unfold functor; infer_instance

instance : (functor χ h).Linear k := by unfold functor; infer_instance

@[simp] theorem functor_obj (a : Obj S) : (functor χ h).obj (P.obj a) = P'.obj a := rfl

theorem functor_lin {a b : Obj S} (f : LinDiagram k a b) :
    (functor χ h).map (P.lin f) = P'.lin (scL χ f) := by
  unfold functor; rw [Presentation.lift_lin, freeLift_scP]

theorem functor_diag {a b : Obj S} (d : a ⟶ b) :
    (functor χ h).map (P.diag d) = ((weight χ (Diagram.layers d) : kˣ) : k) • P'.diag d := by
  rw [Presentation.diag, functor_lin, scL_of, Presentation.lin_smul]
  rfl

/-- **Rescaling commutes with whiskering** (it is a strict 2-functor which is the identity on
objects and 1-morphisms). -/
theorem functor_whisk {a b : Obj S} (f : P.obj a ⟶ P.obj b) (u : Obj S) (v : List S.Colour) :
    (functor χ h).map (P.whisk f u v) = P'.whisk ((functor χ h).map f) u v := by
  obtain ⟨g, rfl⟩ := P.lin_surjective f
  rw [Presentation.whisk_lin, functor_lin, functor_lin, Presentation.whisk_lin, scL_whisk]

/-- **Rescaling preserves degrees.** -/
theorem functor_homDeg {A : Type*} [AddCommMonoid A] {deg : S.Gen → A} {a b : Obj S}
    {f : P.obj a ⟶ P.obj b} {d : A} (hf : f ∈ P.homDeg deg a b d) :
    (functor χ h).map f ∈ P'.homDeg deg a b d := by
  obtain ⟨g, hg, rfl⟩ := Presentation.mem_homDeg_iff.1 hf
  rw [functor_lin]
  exact Presentation.lin_mem_homDeg (scL_mem_homDeg hg)

variable {χ' : S.Gen → kˣ} (h' : ∀ i, P.lin (scL χ' (P'.rel i)) = 0)

/-- If `χ' χ = 1`, the rescaling functors for `χ` and `χ'` are inverse. -/
theorem functor_inv_functor (hχ : ∀ g, χ' g * χ g = 1) {a b : Obj S} (f : P.obj a ⟶ P.obj b) :
    (functor χ' h').map ((functor χ h).map f) = f := by
  obtain ⟨g, rfl⟩ := P.lin_surjective f
  rw [functor_lin, functor_lin, scL_scL hχ]

theorem functor_comp_functor_inv (hχ : ∀ g, χ' g * χ g = 1) :
    functor χ h ⋙ functor χ' h' = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by
    simp only [Functor.comp_map, Functor.id_map, eqToHom_refl, Category.id_comp,
      Category.comp_id]
    exact functor_inv_functor h h' hχ (a := X.as) (b := Y.as) f

variable (χ χ') in
/-- **The rescaling isomorphism** of presented categories, for mutually inverse rescalings
(an isomorphism of categories: `functor_comp_functor_inv` and its converse). -/
def equiv (hχ : ∀ g, χ' g * χ g = 1) : P.Presented ≌ P'.Presented :=
  CategoryTheory.Equivalence.mk (functor χ h) (functor χ' h')
    (eqToIso (functor_comp_functor_inv h h' hχ).symm)
    (eqToIso (functor_comp_functor_inv h' h fun g => by rw [mul_comm, hχ]))

@[simp] theorem equiv_functor (hχ : ∀ g, χ' g * χ g = 1) :
    (equiv χ h χ' h' hχ).functor = functor χ h := rfl

@[simp] theorem equiv_inverse (hχ : ∀ g, χ' g * χ g = 1) :
    (equiv χ h χ' h' hχ).inverse = functor χ' h' := rfl

end Generic

/-! ## Rescaling polynomials -/

section Poly

variable {k : Type w} [CommRing k]

/-- `scaleP u p = p(u₀ x₀, u₁ x₁, …)`. -/
def scaleP {n : ℕ} (u : Fin n → k) : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k :=
  aeval fun t => C (u t) * X t

theorem scaleP_X {n : ℕ} (u : Fin n → k) (t : Fin n) : scaleP u (X t) = C (u t) * X t :=
  aeval_X _ _

theorem scaleP_C {n : ℕ} (u : Fin n → k) (c : k) : scaleP u (C c) = C c :=
  aeval_C _ _

theorem scaleP_monomial {n : ℕ} (u : Fin n → k) (s : Fin n →₀ ℕ) (c : k) :
    scaleP u (monomial s c) = monomial s (c * ∏ t, u t ^ s t) := by
  rw [scaleP, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_mul, map_prod]
  simp only [algebraMap_eq, mul_pow, Finset.prod_mul_distrib, ← map_pow, mul_assoc]

section ncEval

variable {A : Type*} [Ring A] [Algebra k A]

theorem ncEval_add {n : ℕ} (y : Fin n → A) (p q : MvPolynomial (Fin n) k) :
    KLR.ncEval y (p + q) = KLR.ncEval y p + KLR.ncEval y q :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

theorem ncEval_monomial {n : ℕ} (y : Fin n → A) (s : Fin n →₀ ℕ) (c : k) :
    KLR.ncEval y (monomial s c) = algebraMap k A c * (List.ofFn fun a => y a ^ s a).prod :=
  Finsupp.sum_single_index (by simp)

theorem prod_ofFn_algebraMap_mul {n : ℕ} (f : Fin n → k) (g : Fin n → A) :
    (List.ofFn fun a => algebraMap k A (f a) * g a).prod =
      algebraMap k A (∏ a, f a) * (List.ofFn g).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons,
      map_mul, mul_assoc, mul_assoc, ← mul_assoc (g 0), ← Algebra.commutes, mul_assoc]

/-- **Rescaling the variables of `ncEval`**: `ncEval (u • y) p = ncEval y (p(u₀ x₀, …))`. -/
theorem ncEval_smul {n : ℕ} (u : Fin n → k) (y : Fin n → A) (p : MvPolynomial (Fin n) k) :
    KLR.ncEval (fun t => u t • y t) p = KLR.ncEval y (scaleP u p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [scaleP_monomial, ncEval_monomial, ncEval_monomial, map_mul, mul_assoc]
    congr 1
    simp only [Algebra.smul_def, ← prod_ofFn_algebraMap_mul]
    congr 1
    refine List.ofFn_inj.2 (funext fun a => ?_)
    rw [map_pow, Commute.mul_pow (Algebra.commutes (u a) (y a))]
  | add p q hp hq => rw [ncEval_add, hp, hq, map_add, ncEval_add]

end ncEval

theorem qbar_zero' : KLR.qbar (0 : MvPolynomial (Fin 2) k) = 0 := by
  unfold KLR.qbar; exact Finsupp.sum_zero_index

/-- **The divided difference of a rescaled polynomial**:
`Q̄[Q(u x₀, v x₁)] = u · Q̄[Q](u x₀, v x₁, u x₂)`. -/
theorem qbar_scaleP (u v : k) (Q : MvPolynomial (Fin 2) k) :
    KLR.qbar (scaleP ![u, v] Q) = C u * scaleP ![u, v, u] (KLR.qbar Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [scaleP_monomial, KLR.qbar_monomial, KLR.qbar_monomial, Fin.prod_univ_two]
    simp only [map_mul, map_pow, scaleP_C, scaleP_X, map_sum, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, mul_pow,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨e, he⟩ : ∃ e, s 0 = t + 1 + e :=
      ⟨s 0 - 1 - t, by have := Finset.mem_range.mp ht; omega⟩
    rw [show s 0 - 1 - t = e by omega, he]
    ring
  | add p q hp hq => rw [map_add, KLR.qbar_add, hp, hq, KLR.qbar_add, map_add, mul_add]

end Poly

/-! ## Rescaling the infinite Grassmannian recursion -/

theorem grassInv_map_ringHom {A B : Type*} [Ring A] [Ring B] (φ : A →+* B) (c : ℕ → A) (n : ℕ) :
    φ (grassInv c n) = grassInv (fun a => φ (c a)) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [grassInv_zero, grassInv_zero, map_one]
    | succ n =>
      rw [grassInv_succ, grassInv_succ, map_neg, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, ih (n - a.1) (by omega)]

theorem grassInv_smul {k A : Type*} [CommRing k] [Ring A] [Algebra k A] (t : k) (c : ℕ → A)
    (n : ℕ) : grassInv (fun a => t ^ a • c a) n = t ^ n • grassInv c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [grassInv_zero, grassInv_zero, pow_zero, one_smul]
    | succ n =>
      rw [grassInv_succ, grassInv_succ, smul_neg, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ih (n - a.1) (by omega), smul_mul_smul_comm, ← pow_add]
      congr 2
      have := a.2
      omega

end Categorification.KL3.Diagram.CL.Rescale
