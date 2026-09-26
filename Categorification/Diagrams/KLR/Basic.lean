/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Interpretation
import StringDiagrams.Whisker
import Categorification.KLR.Basic

/-!
# KLR diagrams as a presented linear monoidal category

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.1, relations (2.3)–(2.8), and *II*, arXiv:0804.2080v1, §3.

The signature has one region, strand colours `I`, and two families of even generators:

* `dot c` : a dot on a strand of colour `c` (bottom and top boundary `[c]`);
* `cross c d` : a crossing with bottom boundary `[c, d]` and top boundary `[d, c]`.

For a family of polynomials `Q : I → I → k[u, v]` the defining relations (besides the
interchange law, which gives all the isotopy relations) are, with `x₀`, `x₁`, `x₂` dots on
the strands of a two- or three-strand diagram and diagrams read bottom to top:

* `sqEq c`: `ψ ≫ ψ = 0` on `[c, c]`;
* `sqNe c d` (`c ≠ d`): `ψ ≫ ψ = Q_{cd}(x₀, x₁)` on `[c, d]`;
* `slideLEq c` / `slideLNe c d`: `ψ ≫ x₀ - x₁ ≫ ψ = [c = d]` (KLR `x_k ψ_k - ψ_k x_{k+1}`);
* `slideREq c` / `slideRNe c d`: `x₀ ≫ ψ - ψ ≫ x₁ = [c = d]` (KLR `ψ_k x_k - x_{k+1} ψ_k`);
* `braid c d e` (unless `c = e ≠ d`): `ψ₀ ≫ ψ₁ ≫ ψ₀ = ψ₁ ≫ ψ₀ ≫ ψ₁`;
* `braidQ c d` (`c ≠ d`): `ψ₀ ≫ ψ₁ ≫ ψ₀ - ψ₁ ≫ ψ₀ ≫ ψ₁ = Q̄_{cd}(x₀, x₁, x₂)` on `[c, d, c]`.

These are exactly the relations `Categorification.KLR.Rel` of `KLRAlgebra k Q ν`, split
according to the case distinctions made there. Polynomials in dots are written with
`ncEval` in the endomorphism algebra of an object of the free linear category, so that
their monomials are composites of dot diagrams.

## Main definitions

* `sig I`, `pres k Q`: the signature and the presentation; `ob l`: the object with strand
  colours `l`; `lay l g r`, `dl l g r`: the layer `l ⊗ g ⊗ r` and its diagram.
* `linAlg`, `whiskerAlg`: the algebra homomorphisms on endomorphism algebras given by the
  quotient functor and by whiskering.
* The relations whiskered to an arbitrary position (`sqEq_at`, `sqNe_at`, `slideLEq_at`,
  `slideLNe_at`, `slideREq_at`, `slideRNe_at`, `braid_at`, `braidQ_at`), stated for
  diagrams with prescribed lists of layers, and the interchange law `interchange_at`.
* The same relations in positional form (`sqEq_pos`, …, `braidQ_pos`, `interchange_pos`):
  each layer is only described by its generator and the number of strands to its left.
* `ncEval_of_mul`: evaluating a polynomial through a non-unital multiplicative linear map.
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory StringDiagrams

universe u

variable {I : Type u}

/-! ## The signature -/

/-- The generators: a dot on a strand of colour `c`, and a crossing of a strand of colour
`c` (bottom left) with a strand of colour `d` (bottom right). -/
inductive Gen (I : Type u) : Type u
  | dot (c : I)
  | cross (c d : I)

namespace Gen

/-- Bottom boundary of a generator. -/
def dom : Gen I → List I
  | dot c => [c]
  | cross c d => [c, d]

/-- Top boundary of a generator. -/
def cod : Gen I → List I
  | dot c => [c]
  | cross c d => [d, c]

/-- Number of strands of a generator. -/
def arity : Gen I → ℕ
  | dot _ => 1
  | cross _ _ => 2

@[simp] theorem dom_dot (c : I) : (dot c).dom = [c] := rfl
@[simp] theorem dom_cross (c d : I) : (cross c d).dom = [c, d] := rfl
@[simp] theorem cod_dot (c : I) : (dot c).cod = [c] := rfl
@[simp] theorem cod_cross (c d : I) : (cross c d).cod = [d, c] := rfl

@[simp] theorem dom_length (g : Gen I) : g.dom.length = g.arity := by cases g <;> rfl
@[simp] theorem cod_length (g : Gen I) : g.cod.length = g.arity := by cases g <;> rfl

end Gen

variable (I) in
/-- The KLR signature: one region, strands coloured by `I`, even dots and crossings. -/
abbrev sig : Signature where
  Region := Unit
  Colour := I
  colourSrc _ := ()
  colourTgt _ := ()
  Gen := Gen I
  dom := Gen.dom
  cod := Gen.cod
  left _ := ()
  right _ := ()

instance : Subsingleton (sig I).Region := inferInstanceAs (Subsingleton Unit)

@[simp] theorem sig_dom (g : Gen I) : (sig I).dom g = g.dom := rfl
@[simp] theorem sig_cod (g : Gen I) : (sig I).cod g = g.cod := rfl
@[simp] theorem sig_odd (g : Gen I) : (sig I).odd g = false := rfl

/-- The object with strand colours `l`. -/
def ob (l : List I) : Obj (sig I) := ⟨(), l⟩

@[simp] theorem ob_word (l : List I) : (ob l).word = l := rfl
@[simp] theorem ob_start (l : List I) : (ob l).start = () := rfl

theorem obj_ext {a b : Obj (sig I)} (h : a.word = b.word) : a = b :=
  Obj.ext (Subsingleton.elim (α := Unit) _ _) h

theorem layer_ext {L₁ L₂ : Layer (sig I)} (hl : L₁.left = L₂.left) (hg : L₁.gen = L₂.gen)
    (hr : L₁.right = L₂.right) : L₁ = L₂ :=
  Layer.ext (Subsingleton.elim (α := Unit) _ _) hl hg hr

/-- The layer `l ⊗ g ⊗ r`. -/
def lay (l : List I) (g : Gen I) (r : List I) : Layer (sig I) := ⟨(), l, g, r⟩

@[simp] theorem lay_left (l : List I) (g : Gen I) (r : List I) : (lay l g r).left = l := rfl
@[simp] theorem lay_gen (l : List I) (g : Gen I) (r : List I) : (lay l g r).gen = g := rfl
@[simp] theorem lay_right (l : List I) (g : Gen I) (r : List I) : (lay l g r).right = r := rfl

theorem lay_valid (l : List I) (g : Gen I) (r : List I) : (lay l g r).Valid :=
  Layer.valid_of_subsingleton _

theorem lay_eq_iff {l l' : List I} {g g' : Gen I} {r r' : List I} :
    lay l g r = lay l' g' r' ↔ l = l' ∧ g = g' ∧ r = r' := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem Layer.eq_lay (L : Layer (sig I)) : L = lay L.left L.gen L.right := rfl

@[simp] theorem Layer.whisker_lay (l : List I) (g : Gen I) (r : List I) (u v : List I) :
    (lay l g r).whisker (ob u) v = lay (u ++ l) g (r ++ v) := rfl

/-- The layer `l ⊗ g ⊗ r` as a diagram between objects with the right words. -/
def dl (l : List I) (g : Gen I) (r : List I) {a b : Obj (sig I)}
    (ha : l ++ g.dom ++ r = a.word) (hb : l ++ g.cod ++ r = b.word) : a ⟶ b :=
  Diagram.layer (lay l g r) (lay_valid l g r) (obj_ext ha) (obj_ext hb)

@[simp] theorem layers_dl (l : List I) (g : Gen I) (r : List I) {a b : Obj (sig I)}
    (ha : l ++ g.dom ++ r = a.word) (hb : l ++ g.cod ++ r = b.word) :
    Diagram.layers (dl l g r ha hb) = [lay l g r] := rfl

/-! ## The presentation -/

/-- Index type of the defining relations (see the module docstring). -/
inductive Rel (I : Type u) : Type u
  | sqEq (c : I)
  | sqNe (c d : I) (h : c ≠ d)
  | slideLEq (c : I)
  | slideLNe (c d : I) (h : c ≠ d)
  | slideREq (c : I)
  | slideRNe (c d : I) (h : c ≠ d)
  | braid (c d e : I) (h : ¬ (c = e ∧ c ≠ d))
  | braidQ (c d : I) (h : c ≠ d)

/-- Bottom boundary of a relation. -/
def Rel.dom : Rel I → Obj (sig I)
  | .sqEq c => ob [c, c]
  | .sqNe c d _ => ob [c, d]
  | .slideLEq c => ob [c, c]
  | .slideLNe c d _ => ob [c, d]
  | .slideREq c => ob [c, c]
  | .slideRNe c d _ => ob [c, d]
  | .braid c d e _ => ob [c, d, e]
  | .braidQ c d _ => ob [c, d, c]

/-- Top boundary of a relation. -/
def Rel.cod : Rel I → Obj (sig I)
  | .sqEq c => ob [c, c]
  | .sqNe c d _ => ob [c, d]
  | .slideLEq c => ob [c, c]
  | .slideLNe c d _ => ob [d, c]
  | .slideREq c => ob [c, c]
  | .slideRNe c d _ => ob [d, c]
  | .braid c d e _ => ob [e, d, c]
  | .braidQ c d _ => ob [c, d, c]

/-- The crossing on `[c, d]`. -/
abbrev X2 (c d : I) : ob [c, d] ⟶ ob [d, c] := dl [] (.cross c d) [] rfl rfl
/-- The dot on the left strand of `[c, d]`. -/
abbrev D0 (c d : I) : ob [c, d] ⟶ ob [c, d] := dl [] (.dot c) [d] rfl rfl
/-- The dot on the right strand of `[c, d]`. -/
abbrev D1 (c d : I) : ob [c, d] ⟶ ob [c, d] := dl [c] (.dot d) [] rfl rfl
/-- The crossing of the left two strands of `[c, d, e]`. -/
abbrev XL (c d e : I) : ob [c, d, e] ⟶ ob [d, c, e] := dl [] (.cross c d) [e] rfl rfl
/-- The crossing of the right two strands of `[c, d, e]`. -/
abbrev XR (c d e : I) : ob [c, d, e] ⟶ ob [c, e, d] := dl [c] (.cross d e) [] rfl rfl
/-- The dots on the three strands of `[c, d, e]`. -/
abbrev E0 (c d e : I) : ob [c, d, e] ⟶ ob [c, d, e] := dl [] (.dot c) [d, e] rfl rfl
abbrev E1 (c d e : I) : ob [c, d, e] ⟶ ob [c, d, e] := dl [c] (.dot d) [e] rfl rfl
abbrev E2 (c d e : I) : ob [c, d, e] ⟶ ob [c, d, e] := dl [c, d] (.dot e) [] rfl rfl

/-- The left-hand side `ψ₀ ψ₁ ψ₀` of the braid relation (bottom to top: `ψ₀`, `ψ₁`, `ψ₀`). -/
abbrev braidL (c d e : I) : ob [c, d, e] ⟶ ob [e, d, c] := XL c d e ≫ XR d c e ≫ XL d e c
/-- The right-hand side `ψ₁ ψ₀ ψ₁` of the braid relation. -/
abbrev braidR (c d e : I) : ob [c, d, e] ⟶ ob [e, d, c] := XR c d e ≫ XL c e d ≫ XR e c d

variable (k : Type*) [CommRing k]

/-- A polynomial in commuting variables, evaluated on the given endomorphisms of an object of
the free linear category (see `Categorification.KLR.ncEval`). -/
abbrev lpoly {w : Obj (sig I)} {n : ℕ} (y : Fin n → (w ⟶ w)) (p : MvPolynomial (Fin n) k) :
    LinDiagram k w w :=
  ncEval (A := End (Free.of k w)) (fun a => LinDiagram.of (y a)) p

open LinDiagram in
/-- The defining relations, as linear combinations of diagrams that are set to zero. -/
def relation (Q : I → I → MvPolynomial (Fin 2) k) : (r : Rel I) → LinDiagram k r.dom r.cod
  | .sqEq c => of (X2 c c ≫ X2 c c)
  | .sqNe c d _ => of (X2 c d ≫ X2 d c) - lpoly k ![D0 c d, D1 c d] (Q c d)
  | .slideLEq c => of (X2 c c ≫ D0 c c) - of (D1 c c ≫ X2 c c) - of (𝟙 _)
  | .slideLNe c d _ => of (X2 c d ≫ D0 d c) - of (D1 c d ≫ X2 c d)
  | .slideREq c => of (D0 c c ≫ X2 c c) - of (X2 c c ≫ D1 c c) - of (𝟙 _)
  | .slideRNe c d _ => of (D0 c d ≫ X2 c d) - of (X2 c d ≫ D1 d c)
  | .braid c d e _ => of (braidL c d e) - of (braidR c d e)
  | .braidQ c d _ => of (braidL c d c) - of (braidR c d c) -
      lpoly k ![E0 c d c, E1 c d c, E2 c d c] (qbar (Q c d))

/-- The KLR presentation over `k` for the polynomials `Q`. -/
def pres (Q : I → I → MvPolynomial (Fin 2) k) : Presentation (sig I) k where
  Rel := Rel I
  dom := Rel.dom
  cod := Rel.cod
  rel := relation k Q

/-! ## Polynomials in noncommuting variables -/

section ncEval

variable {k} {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]

theorem _root_.AlgHom.map_ncEval (φ : A →ₐ[k] B) {n : ℕ} (y : Fin n → A)
    (p : MvPolynomial (Fin n) k) : φ (ncEval y p) = ncEval (fun a => φ (y a)) p := by
  simp only [ncEval, Finsupp.sum, map_sum, map_mul, AlgHom.commutes, map_list_prod,
    List.map_ofFn, Function.comp_def, map_pow]

/-- A multiplicative `k`-linear map `φ` with `φ 1 = e` (not necessarily unital) sends
`ncEval y p` to `ncEval z p * e`, provided `φ (y a) = z a * e` and each `z a` commutes
with `e`. -/
theorem ncEval_of_mul (φ : A →ₗ[k] B) (hmul : ∀ a b, φ (a * b) = φ a * φ b) {e : B}
    (he : φ 1 = e) {n : ℕ} (y : Fin n → A) (z : Fin n → B) (hy : ∀ a, φ (y a) = z a * e)
    (hz : ∀ a, Commute (z a) e) (p : MvPolynomial (Fin n) k) :
    φ (ncEval y p) = ncEval z p * e := by
  have hee : e * e = e := by rw [← he, ← hmul, one_mul]
  have hpow : ∀ (a : Fin n) (t : ℕ), φ (y a ^ t) = z a ^ t * e := by
    intro a t
    induction t with
    | zero => simp [he]
    | succ t ih =>
      rw [pow_succ, hmul, ih, hy, pow_succ, mul_assoc, ← mul_assoc e, ← (hz a).eq, mul_assoc,
        hee, mul_assoc]
  have hlist : ∀ (l : List (Fin n)) (s : Fin n →₀ ℕ),
      φ (l.map fun a => y a ^ s a).prod = (l.map fun a => z a ^ s a).prod * e := by
    intro l s
    induction l with
    | nil => simp [he]
    | cons a l ih =>
      have hc : Commute e (l.map fun a => z a ^ s a).prod :=
        Commute.list_prod_right _ _ fun w hw => by
          obtain ⟨b, -, rfl⟩ := List.mem_map.1 hw
          exact ((hz b).pow_left _).symm
      rw [List.map_cons, List.prod_cons, hmul, ih, hpow, List.map_cons, List.prod_cons,
        mul_assoc, ← mul_assoc e, hc.eq, mul_assoc, hee, mul_assoc]
  simp only [ncEval, Finsupp.sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Algebra.smul_def, map_smul, List.ofFn_eq_map, hlist, ← List.ofFn_eq_map,
    Algebra.smul_def, mul_assoc]

end ncEval

/-! ## Algebra homomorphisms on endomorphism algebras -/

section Alg

variable {k} {S : Signature} (P : Presentation S k)

/-- The quotient functor of a presentation on endomorphism algebras. -/
def linAlg (a : Obj S) : End (Free.of k a) →ₐ[k] End (P.obj a) where
  toFun := P.lin
  map_one' := P.lin_id a
  map_mul' f g := P.lin_comp g f
  map_zero' := P.lin_zero
  map_add' := P.lin_add
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [P.lin_smul]
    exact congrArg (r • ·) (P.lin_id a)

@[simp] theorem linAlg_apply (a : Obj S) (f : End (Free.of k a)) : linAlg P a f = P.lin f :=
  rfl

variable (k) in
/-- Whiskering on endomorphism algebras of the free linear category. -/
def whiskerAlg (w u : Obj S) (v : List S.Colour) (hw : w.WhiskerOK u v) :
    End (Free.of k w) →ₐ[k] End (Free.of k (w.whisker u v)) where
  toFun f := LinDiagram.whisker f u v hw
  map_one' := LinDiagram.whisker_single _ _ _ _ _
  map_mul' f g := LinDiagram.whisker_comp g f u v hw hw
  map_zero' := Finsupp.mapDomain_zero
  map_add' f g := LinDiagram.whisker_add f g u v hw
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [LinDiagram.whisker_smul]
    exact congrArg (r • ·) (LinDiagram.whisker_single _ _ _ _ _)

@[simp] theorem whiskerAlg_apply (w u : Obj S) (v : List S.Colour) (hw : w.WhiskerOK u v)
    (f : End (Free.of k w)) : whiskerAlg k w u v hw f = LinDiagram.whisker f u v hw := rfl

end Alg

/-! ## Boundaries of diagrams given by their layers -/

theorem Chain.target_append_singleton {S : Signature} (a : Obj S) (ls : List (Layer S))
    (L : Layer S) : Chain.target a (ls ++ [L]) = L.cod := by
  induction ls generalizing a with
  | nil => rfl
  | cons L' ls ih => exact ih _

theorem dom_eq_of_layers {S : Signature} {a b : Obj S} (f : a ⟶ b) {L : Layer S}
    {ls : List (Layer S)} (h : Diagram.layers f = L :: ls) : a = L.dom := by
  have := Diagram.chain f
  rw [h] at this
  exact this.2.1.symm

theorem cod_eq_of_layers {S : Signature} {a b : Obj S} (f : a ⟶ b) {L : Layer S}
    {ls : List (Layer S)} (h : Diagram.layers f = ls ++ [L]) : b = L.cod := by
  have := (Diagram.chain f).target_eq
  rw [h, Chain.target_append_singleton] at this
  exact this.symm

/-! ## The relations at an arbitrary position

Each defining relation, whiskered by `u` on the left and `v` on the right, is stated for
diagrams `f`, `g`, … with prescribed lists of layers; the boundary objects are arbitrary
(they are determined by the layers). -/

section Relations

variable {k} (Q : I → I → MvPolynomial (Fin 2) k)

local notation "P" => pres k Q

theorem rel_at (r : Rel I) (u v : List I) :
    (P).lin (LinDiagram.whisker (relation k Q r) (ob u) v
      (Obj.whiskerOK_of_subsingleton _ _ _)) = 0 :=
  (P).lin_rel r (ob u) v _

theorem diag_whisker_id (a u : Obj (sig I)) (v : List I) (hw : a.WhiskerOK u v) :
    (P).diag (Diagram.whisker (𝟙 a) u v hw) = 𝟙 _ := by
  rw [Diagram.whisker_id]; exact (P).diag_id _

/-- `ψ ≫ ψ = 0` on `[c, c]`, at any position. -/
theorem sqEq_at {u v : List I} {c : I} {a b : Obj (sig I)} (f : a ⟶ b)
    (hf : Diagram.layers f = [lay u (.cross c c) v, lay u (.cross c c) v]) :
    (P).diag f = 0 := by
  obtain rfl : a = (ob [c, c]).whisker (ob u) v :=
    (dom_eq_of_layers f hf).trans (obj_ext (by simp [lay]))
  obtain rfl : b = (ob [c, c]).whisker (ob u) v :=
    (cod_eq_of_layers f (ls := [lay u (.cross c c) v]) hf).trans (obj_ext (by simp [lay]))
  have key := rel_at Q (.sqEq c) u v
  simp only [relation, LinDiagram.whisker_of, Presentation.lin_of] at key
  rw [← key]
  exact (P).diag_eq_of_layers_eq (by simp [hf])

/-- `ψ ≫ ψ = Q_{cd}(x₀, x₁)` on `[c, d]` for `c ≠ d`, at any position. -/
theorem sqNe_at {u v : List I} {c d : I} (hcd : c ≠ d) {a : Obj (sig I)} (f y₀ y₁ : a ⟶ a)
    (hf : Diagram.layers f = [lay u (.cross c d) v, lay u (.cross d c) v])
    (h₀ : Diagram.layers y₀ = [lay u (.dot c) (d :: v)])
    (h₁ : Diagram.layers y₁ = [lay (u ++ [c]) (.dot d) v]) :
    (P).diag f = ncEval (A := End ((P).obj a)) ![(P).diag y₀, (P).diag y₁] (Q c d) := by
  obtain rfl : a = (ob [c, d]).whisker (ob u) v :=
    (dom_eq_of_layers f hf).trans (obj_ext (by simp [lay]))
  have key := rel_at Q (.sqNe c d hcd) u v
  simp only [relation] at key
  rw [LinDiagram.whisker_sub, LinDiagram.whisker_of, Presentation.lin_sub, Presentation.lin_of,
    sub_eq_zero] at key
  rw [show ∀ w : End (Free.of k (ob [c, d])), (P).lin (LinDiagram.whisker w (ob u) v
      (Obj.whiskerOK_of_subsingleton _ _ _)) =
      linAlg P _ (whiskerAlg k _ (ob u) v (Obj.whiskerOK_of_subsingleton _ _ _) w)
      from fun _ => rfl, AlgHom.map_ncEval, AlgHom.map_ncEval] at key
  refine ((P).diag_eq_of_layers_eq ?_).trans (key.trans ?_)
  · simp [hf]
  · congr 1; funext t; fin_cases t <;>
      simp only [linAlg_apply, whiskerAlg_apply, LinDiagram.whisker_of, Presentation.lin_of,
        Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;>
      exact (P).diag_eq_of_layers_eq (by simp [h₀, h₁])

/-- `ψ ≫ x₀ - x₁ ≫ ψ = 1` on `[c, c]`, at any position. -/
theorem slideLEq_at {u v : List I} {c : I} {a : Obj (sig I)} (f g : a ⟶ a)
    (hf : Diagram.layers f = [lay u (.cross c c) v, lay u (.dot c) (c :: v)])
    (hg : Diagram.layers g = [lay (u ++ [c]) (.dot c) v, lay u (.cross c c) v]) :
    (P).diag f - (P).diag g = 𝟙 _ := by
  obtain rfl : a = (ob [c, c]).whisker (ob u) v :=
    (dom_eq_of_layers f hf).trans (obj_ext (by simp [lay]))
  have key := rel_at Q (.slideLEq c) u v
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, Presentation.lin_sub,
    Presentation.lin_of, diag_whisker_id, sub_eq_zero] at key
  refine Eq.trans ?_ key
  congr 1 <;> exact (P).diag_eq_of_layers_eq (by simp [hf, hg])

/-- `ψ ≫ x₀ = x₁ ≫ ψ` on `[c, d]` for `c ≠ d`, at any position. -/
theorem slideLNe_at {u v : List I} {c d : I} (hcd : c ≠ d) {a b : Obj (sig I)} (f g : a ⟶ b)
    (hf : Diagram.layers f = [lay u (.cross c d) v, lay u (.dot d) (c :: v)])
    (hg : Diagram.layers g = [lay (u ++ [c]) (.dot d) v, lay u (.cross c d) v]) :
    (P).diag f = (P).diag g := by
  obtain rfl : a = (ob [c, d]).whisker (ob u) v :=
    (dom_eq_of_layers f hf).trans (obj_ext (by simp [lay]))
  obtain rfl : b = (ob [d, c]).whisker (ob u) v :=
    (cod_eq_of_layers f (ls := [lay u (.cross c d) v]) hf).trans (obj_ext (by simp [lay]))
  have key := rel_at Q (.slideLNe c d hcd) u v
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, Presentation.lin_sub,
    Presentation.lin_of, sub_eq_zero] at key
  refine Eq.trans ?_ (key.trans ?_) <;> exact (P).diag_eq_of_layers_eq (by simp [hf, hg])

/-- `x₀ ≫ ψ - ψ ≫ x₁ = 1` on `[c, c]`, at any position. -/
theorem slideREq_at {u v : List I} {c : I} {a : Obj (sig I)} (f g : a ⟶ a)
    (hf : Diagram.layers f = [lay u (.dot c) (c :: v), lay u (.cross c c) v])
    (hg : Diagram.layers g = [lay u (.cross c c) v, lay (u ++ [c]) (.dot c) v]) :
    (P).diag f - (P).diag g = 𝟙 _ := by
  obtain rfl : a = (ob [c, c]).whisker (ob u) v :=
    (dom_eq_of_layers f hf).trans (obj_ext (by simp [lay]))
  have key := rel_at Q (.slideREq c) u v
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, Presentation.lin_sub,
    Presentation.lin_of, diag_whisker_id, sub_eq_zero] at key
  refine Eq.trans ?_ key
  congr 1 <;> exact (P).diag_eq_of_layers_eq (by simp [hf, hg])

/-- `x₀ ≫ ψ = ψ ≫ x₁` on `[c, d]` for `c ≠ d`, at any position. -/
theorem slideRNe_at {u v : List I} {c d : I} (hcd : c ≠ d) {a b : Obj (sig I)} (f g : a ⟶ b)
    (hf : Diagram.layers f = [lay u (.dot c) (d :: v), lay u (.cross c d) v])
    (hg : Diagram.layers g = [lay u (.cross c d) v, lay (u ++ [d]) (.dot c) v]) :
    (P).diag f = (P).diag g := by
  obtain rfl : a = (ob [c, d]).whisker (ob u) v :=
    (dom_eq_of_layers f hf).trans (obj_ext (by simp [lay]))
  obtain rfl : b = (ob [d, c]).whisker (ob u) v :=
    (cod_eq_of_layers f (ls := [lay u (.dot c) (d :: v)]) hf).trans (obj_ext (by simp [lay]))
  have key := rel_at Q (.slideRNe c d hcd) u v
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, Presentation.lin_sub,
    Presentation.lin_of, sub_eq_zero] at key
  refine Eq.trans ?_ (key.trans ?_) <;> exact (P).diag_eq_of_layers_eq (by simp [hf, hg])

/-- The braid relation on `[c, d, e]` unless `c = e ≠ d`, at any position. -/
theorem braid_at {u v : List I} {c d e : I} (h : ¬ (c = e ∧ c ≠ d)) {a b : Obj (sig I)}
    (f g : a ⟶ b)
    (hf : Diagram.layers f = [lay u (.cross c d) (e :: v), lay (u ++ [d]) (.cross c e) v,
      lay u (.cross d e) (c :: v)])
    (hg : Diagram.layers g = [lay (u ++ [c]) (.cross d e) v, lay u (.cross c e) (d :: v),
      lay (u ++ [e]) (.cross c d) v]) :
    (P).diag f = (P).diag g := by
  obtain rfl : a = (ob [c, d, e]).whisker (ob u) v :=
    (dom_eq_of_layers f hf).trans (obj_ext (by simp [lay]))
  obtain rfl : b = (ob [e, d, c]).whisker (ob u) v :=
    (cod_eq_of_layers f (ls := [lay u (.cross c d) (e :: v), lay (u ++ [d]) (.cross c e) v])
      hf).trans (obj_ext (by simp [lay]))
  have key := rel_at Q (.braid c d e h) u v
  simp only [relation, LinDiagram.whisker_sub, LinDiagram.whisker_of, Presentation.lin_sub,
    Presentation.lin_of, sub_eq_zero] at key
  refine Eq.trans ?_ (key.trans ?_) <;> exact (P).diag_eq_of_layers_eq (by simp [hf, hg])

/-- The braid relation with correction `Q̄_{cd}(x₀, x₁, x₂)` on `[c, d, c]` for `c ≠ d`, at
any position. -/
theorem braidQ_at {u v : List I} {c d : I} (hcd : c ≠ d) {a : Obj (sig I)}
    (f g y₀ y₁ y₂ : a ⟶ a)
    (hf : Diagram.layers f = [lay u (.cross c d) (c :: v), lay (u ++ [d]) (.cross c c) v,
      lay u (.cross d c) (c :: v)])
    (hg : Diagram.layers g = [lay (u ++ [c]) (.cross d c) v, lay u (.cross c c) (d :: v),
      lay (u ++ [c]) (.cross c d) v])
    (h₀ : Diagram.layers y₀ = [lay u (.dot c) (d :: c :: v)])
    (h₁ : Diagram.layers y₁ = [lay (u ++ [c]) (.dot d) (c :: v)])
    (h₂ : Diagram.layers y₂ = [lay (u ++ [c, d]) (.dot c) v]) :
    (P).diag f - (P).diag g =
      ncEval (A := End ((P).obj a)) ![(P).diag y₀, (P).diag y₁, (P).diag y₂]
        (qbar (Q c d)) := by
  obtain rfl : a = (ob [c, d, c]).whisker (ob u) v :=
    (dom_eq_of_layers f hf).trans (obj_ext (by simp [lay]))
  have key := rel_at Q (.braidQ c d hcd) u v
  simp only [relation] at key
  rw [LinDiagram.whisker_sub, LinDiagram.whisker_sub, LinDiagram.whisker_of,
    LinDiagram.whisker_of, Presentation.lin_sub, Presentation.lin_sub, Presentation.lin_of,
    Presentation.lin_of, sub_eq_zero] at key
  rw [show ∀ w : End (Free.of k (ob [c, d, c])), (P).lin (LinDiagram.whisker w (ob u) v
      (Obj.whiskerOK_of_subsingleton _ _ _)) =
      linAlg P _ (whiskerAlg k _ (ob u) v (Obj.whiskerOK_of_subsingleton _ _ _) w)
      from fun _ => rfl, AlgHom.map_ncEval, AlgHom.map_ncEval] at key
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1 <;> exact (P).diag_eq_of_layers_eq (by simp [hf, hg])
  · congr 1; funext t; fin_cases t <;>
      simp only [linAlg_apply, whiskerAlg_apply, LinDiagram.whisker_of, Presentation.lin_of,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      exact (P).diag_eq_of_layers_eq (by simp [h₀, h₁, h₂])

/-- The interchange law: generators `g` and `h` on disjoint strands (`g` to the left of `h`)
can be applied in either order. -/
theorem interchange_at (l m r : List I) (g h : Gen I) {a b : Obj (sig I)} (f₁ f₂ : a ⟶ b)
    (h₁ : Diagram.layers f₁ = [lay l g (m ++ h.dom ++ r), lay (l ++ g.cod ++ m) h r])
    (h₂ : Diagram.layers f₂ = [lay (l ++ g.dom ++ m) h r, lay l g (m ++ h.cod ++ r)]) :
    (P).diag f₁ = (P).diag f₂ := by
  let x : InterchangeData (sig I) := ⟨(), g, m, h⟩
  have hx : x.Valid := InterchangeData.valid_of_subsingleton x
  have ha : x.dom.whisker (ob l) r = a :=
    ((dom_eq_of_layers f₁ h₁).trans (obj_ext (by simp [x, InterchangeData.dom, lay]))).symm
  have hb : x.cod.whisker (ob l) r = b :=
    ((cod_eq_of_layers f₁ (ls := [lay l g (m ++ h.dom ++ r)]) h₁).trans
      (obj_ext (by simp [x, InterchangeData.cod, lay]))).symm
  have key := (P).diag_interchange x hx (ob l) r (Obj.whiskerOK_of_subsingleton _ _ _) ha hb
  have hs : ((x.sign : ℤ) : k) = 1 := by simp [x, InterchangeData.sign]
  rw [hs, one_smul] at key
  refine Eq.trans ?_ (key.trans ?_) <;> refine (P).diag_eq_of_layers_eq ?_
  · simp [h₁, x, InterchangeData.ghDiagram, InterchangeData.gh₁, InterchangeData.gh₂, lay,
      Layer.whisker]
  · simp [h₂, x, InterchangeData.hgDiagram, InterchangeData.hg₁, InterchangeData.hg₂, lay,
      Layer.whisker]

end Relations

/-! ## The relations in positional form

The same relations, for diagrams whose layers are only described by the number of strands to
the left of their generator and by the generator; the words of the layers are determined by
the boundary objects. -/

theorem append_three_inj {α : Type*} {l₁ w₁ r₁ l₂ w₂ r₂ : List α}
    (h : l₁ ++ w₁ ++ r₁ = l₂ ++ w₂ ++ r₂) (hl : l₁.length = l₂.length)
    (hw : w₁.length = w₂.length) : l₁ = l₂ ∧ w₁ = w₂ ∧ r₁ = r₂ := by
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨rfl, h'⟩ := List.append_inj h hl
  obtain ⟨rfl, rfl⟩ := List.append_inj h' hw
  exact ⟨rfl, rfl, rfl⟩

@[simp] theorem Layer.dom_word' (L : Layer (sig I)) :
    L.dom.word = L.left ++ L.gen.dom ++ L.right := rfl
@[simp] theorem Layer.cod_word' (L : Layer (sig I)) :
    L.cod.word = L.left ++ L.gen.cod ++ L.right := rfl

/-- A layer is determined by its bottom word, the number of strands to the left of its
generator, and its generator. -/
theorem eq_lay_of_dom (L : Layer (sig I)) {u v : List I} {g : Gen I}
    (hd : L.dom.word = u ++ g.dom ++ v) (hl : L.left.length = u.length) (hg : L.gen = g) :
    L = lay u g v := by
  obtain ⟨⟨⟩, l, g', r⟩ := L
  simp only at hl hg
  subst hg
  obtain ⟨rfl, -, rfl⟩ := append_three_inj hd hl rfl
  rfl

theorem chain_one {S : Signature} {a b : Obj S} (f : a ⟶ b) {L : Layer S}
    (h : Diagram.layers f = [L]) : L.dom = a ∧ L.cod = b := by
  have := Diagram.chain f
  rw [h] at this
  exact ⟨this.2.1, this.2.2⟩

theorem chain_two {S : Signature} {a b : Obj S} (f : a ⟶ b) {L₁ L₂ : Layer S}
    (h : Diagram.layers f = [L₁, L₂]) : L₁.dom = a ∧ L₂.dom = L₁.cod ∧ L₂.cod = b := by
  have := Diagram.chain f
  rw [h] at this
  exact ⟨this.2.1, this.2.2.2.1, this.2.2.2.2⟩

theorem chain_three {S : Signature} {a b : Obj S} (f : a ⟶ b) {L₁ L₂ L₃ : Layer S}
    (h : Diagram.layers f = [L₁, L₂, L₃]) :
    L₁.dom = a ∧ L₂.dom = L₁.cod ∧ L₃.dom = L₂.cod ∧ L₃.cod = b := by
  have := Diagram.chain f
  rw [h] at this
  exact ⟨this.2.1, this.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2⟩

section Positional

variable {k} (Q : I → I → MvPolynomial (Fin 2) k)

local notation "P" => pres k Q

theorem sqEq_pos {c : I} {p : ℕ} {a b : Obj (sig I)} (f : a ⟶ b) {L₁ L₂ : Layer (sig I)}
    (hf : Diagram.layers f = [L₁, L₂]) (h₁ : L₁.left.length = p) (g₁ : L₁.gen = .cross c c)
    (h₂ : L₂.left.length = p) (g₂ : L₂.gen = .cross c c) : (P).diag f = 0 := by
  obtain ⟨-, e₂, -⟩ := chain_two f hf
  obtain ⟨⟨⟩, u, g', v⟩ := L₁
  simp only at h₁ g₁; subst g₁ h₁
  obtain rfl := eq_lay_of_dom L₂ (u := u) (v := v) (by rw [e₂]; rfl) h₂ g₂
  exact sqEq_at Q f hf

theorem sqNe_pos {c d : I} (hcd : c ≠ d) {p : ℕ} {a : Obj (sig I)} (f y₀ y₁ : a ⟶ a)
    {L₁ L₂ M₀ M₁ : Layer (sig I)}
    (hf : Diagram.layers f = [L₁, L₂]) (h₁ : L₁.left.length = p) (g₁ : L₁.gen = .cross c d)
    (h₂ : L₂.left.length = p) (g₂ : L₂.gen = .cross d c)
    (hy₀ : Diagram.layers y₀ = [M₀]) (h₀' : M₀.left.length = p) (g₀' : M₀.gen = .dot c)
    (hy₁ : Diagram.layers y₁ = [M₁]) (h₁' : M₁.left.length = p + 1) (g₁' : M₁.gen = .dot d) :
    (P).diag f = ncEval (A := End ((P).obj a)) ![(P).diag y₀, (P).diag y₁] (Q c d) := by
  obtain ⟨e₁, e₂, -⟩ := chain_two f hf
  have em₀ := (chain_one y₀ hy₀).1
  have em₁ := (chain_one y₁ hy₁).1
  obtain ⟨⟨⟩, u, g', v⟩ := L₁
  simp only at h₁ g₁; subst g₁ h₁ e₁
  obtain rfl := eq_lay_of_dom L₂ (u := u) (v := v) (by rw [e₂]; rfl) h₂ g₂
  obtain rfl := eq_lay_of_dom M₀ (u := u) (v := d :: v) (by rw [em₀]; simp) h₀' g₀'
  obtain rfl := eq_lay_of_dom M₁ (u := u ++ [c]) (v := v) (by rw [em₁]; simp) (by simpa using h₁')
    g₁'
  exact sqNe_at Q hcd f y₀ y₁ hf hy₀ hy₁

theorem slideLEq_pos {c : I} {p : ℕ} {a : Obj (sig I)} (f g : a ⟶ a)
    {L₁ L₂ M₁ M₂ : Layer (sig I)}
    (hf : Diagram.layers f = [L₁, L₂]) (h₁ : L₁.left.length = p) (g₁ : L₁.gen = .cross c c)
    (h₂ : L₂.left.length = p) (g₂ : L₂.gen = .dot c)
    (hg : Diagram.layers g = [M₁, M₂]) (h₁' : M₁.left.length = p + 1) (g₁' : M₁.gen = .dot c)
    (h₂' : M₂.left.length = p) (g₂' : M₂.gen = .cross c c) :
    (P).diag f - (P).diag g = 𝟙 _ := by
  obtain ⟨e₁, e₂, -⟩ := chain_two f hf
  obtain ⟨e₁', e₂', -⟩ := chain_two g hg
  obtain ⟨⟨⟩, u, g', v⟩ := L₁
  simp only at h₁ g₁; subst g₁ h₁ e₁
  obtain rfl := eq_lay_of_dom L₂ (u := u) (v := c :: v) (by rw [e₂]; simp) h₂ g₂
  obtain rfl := eq_lay_of_dom M₁ (u := u ++ [c]) (v := v) (by rw [e₁']; simp)
    (by simpa using h₁') g₁'
  obtain rfl := eq_lay_of_dom M₂ (u := u) (v := v) (by rw [e₂']; simp) h₂' g₂'
  exact slideLEq_at Q f g hf hg

theorem slideLNe_pos {c d : I} (hcd : c ≠ d) {p : ℕ} {a b : Obj (sig I)} (f g : a ⟶ b)
    {L₁ L₂ M₁ M₂ : Layer (sig I)}
    (hf : Diagram.layers f = [L₁, L₂]) (h₁ : L₁.left.length = p) (g₁ : L₁.gen = .cross c d)
    (h₂ : L₂.left.length = p) (g₂ : L₂.gen = .dot d)
    (hg : Diagram.layers g = [M₁, M₂]) (h₁' : M₁.left.length = p + 1) (g₁' : M₁.gen = .dot d)
    (h₂' : M₂.left.length = p) (g₂' : M₂.gen = .cross c d) :
    (P).diag f = (P).diag g := by
  obtain ⟨e₁, e₂, -⟩ := chain_two f hf
  obtain ⟨e₁', e₂', -⟩ := chain_two g hg
  obtain ⟨⟨⟩, u, g', v⟩ := L₁
  simp only at h₁ g₁; subst g₁ h₁ e₁
  obtain rfl := eq_lay_of_dom L₂ (u := u) (v := c :: v) (by rw [e₂]; simp) h₂ g₂
  obtain rfl := eq_lay_of_dom M₁ (u := u ++ [c]) (v := v) (by rw [e₁']; simp)
    (by simpa using h₁') g₁'
  obtain rfl := eq_lay_of_dom M₂ (u := u) (v := v) (by rw [e₂']; simp) h₂' g₂'
  exact slideLNe_at Q hcd f g hf hg

theorem slideREq_pos {c : I} {p : ℕ} {a : Obj (sig I)} (f g : a ⟶ a)
    {L₁ L₂ M₁ M₂ : Layer (sig I)}
    (hf : Diagram.layers f = [L₁, L₂]) (h₁ : L₁.left.length = p) (g₁ : L₁.gen = .dot c)
    (h₂ : L₂.left.length = p) (g₂ : L₂.gen = .cross c c)
    (hg : Diagram.layers g = [M₁, M₂]) (h₁' : M₁.left.length = p) (g₁' : M₁.gen = .cross c c)
    (h₂' : M₂.left.length = p + 1) (g₂' : M₂.gen = .dot c) :
    (P).diag f - (P).diag g = 𝟙 _ := by
  obtain ⟨e₁, e₂, -⟩ := chain_two f hf
  obtain ⟨e₁', e₂', -⟩ := chain_two g hg
  obtain ⟨⟨⟩, u, g', w⟩ := M₁
  simp only at h₁' g₁'; subst g₁' h₁' e₁'
  obtain rfl := eq_lay_of_dom L₁ (u := u) (v := c :: w) (by rw [e₁]; simp) h₁ g₁
  obtain rfl := eq_lay_of_dom L₂ (u := u) (v := w) (by rw [e₂]; simp) h₂ g₂
  obtain rfl := eq_lay_of_dom M₂ (u := u ++ [c]) (v := w) (by rw [e₂']; simp)
    (by simpa using h₂') g₂'
  exact slideREq_at Q f g hf hg

theorem slideRNe_pos {c d : I} (hcd : c ≠ d) {p : ℕ} {a b : Obj (sig I)} (f g : a ⟶ b)
    {L₁ L₂ M₁ M₂ : Layer (sig I)}
    (hf : Diagram.layers f = [L₁, L₂]) (h₁ : L₁.left.length = p) (g₁ : L₁.gen = .dot c)
    (h₂ : L₂.left.length = p) (g₂ : L₂.gen = .cross c d)
    (hg : Diagram.layers g = [M₁, M₂]) (h₁' : M₁.left.length = p) (g₁' : M₁.gen = .cross c d)
    (h₂' : M₂.left.length = p + 1) (g₂' : M₂.gen = .dot c) :
    (P).diag f = (P).diag g := by
  obtain ⟨e₁, e₂, -⟩ := chain_two f hf
  obtain ⟨e₁', e₂', -⟩ := chain_two g hg
  obtain ⟨⟨⟩, u, g', w⟩ := M₁
  simp only at h₁' g₁'; subst g₁' h₁' e₁'
  obtain rfl := eq_lay_of_dom L₁ (u := u) (v := d :: w) (by rw [e₁]; simp) h₁ g₁
  obtain rfl := eq_lay_of_dom L₂ (u := u) (v := w) (by rw [e₂]; simp) h₂ g₂
  obtain rfl := eq_lay_of_dom M₂ (u := u ++ [d]) (v := w) (by rw [e₂']; simp)
    (by simpa using h₂') g₂'
  exact slideRNe_at Q hcd f g hf hg

theorem braid_pos {c d e : I} (h : ¬ (c = e ∧ c ≠ d)) {p : ℕ} {a b : Obj (sig I)}
    (f g : a ⟶ b) {L₁ L₂ L₃ M₁ M₂ M₃ : Layer (sig I)}
    (hf : Diagram.layers f = [L₁, L₂, L₃]) (h₁ : L₁.left.length = p) (g₁ : L₁.gen = .cross c d)
    (h₂ : L₂.left.length = p + 1) (g₂ : L₂.gen = .cross c e)
    (h₃ : L₃.left.length = p) (g₃ : L₃.gen = .cross d e)
    (hg : Diagram.layers g = [M₁, M₂, M₃]) (h₁' : M₁.left.length = p + 1)
    (g₁' : M₁.gen = .cross d e) (h₂' : M₂.left.length = p) (g₂' : M₂.gen = .cross c e)
    (h₃' : M₃.left.length = p + 1) (g₃' : M₃.gen = .cross c d) :
    (P).diag f = (P).diag g := by
  obtain ⟨e₁, e₂, e₃, -⟩ := chain_three f hf
  obtain ⟨e₁', e₂', e₃', -⟩ := chain_three g hg
  obtain ⟨⟨⟩, u, g', w⟩ := L₁
  simp only at h₁ g₁; subst g₁ h₁ e₁
  obtain ⟨⟨⟩, u₂, g'', v⟩ := L₂
  simp only at h₂ g₂; subst g₂
  obtain ⟨rfl, -, rfl⟩ := append_three_inj (l₁ := u₂) (w₁ := [c]) (r₁ := e :: v)
    (l₂ := u ++ [d]) (w₂ := [c]) (r₂ := w) (by simpa using congrArg Obj.word e₂)
    (by simpa using h₂) rfl
  obtain rfl := eq_lay_of_dom L₃ (u := u) (v := c :: v) (by rw [e₃]; simp) h₃ g₃
  obtain rfl := eq_lay_of_dom M₁ (u := u ++ [c]) (v := v) (by rw [e₁']; simp)
    (by simpa using h₁') g₁'
  obtain rfl := eq_lay_of_dom M₂ (u := u) (v := d :: v) (by rw [e₂']; simp) h₂' g₂'
  obtain rfl := eq_lay_of_dom M₃ (u := u ++ [e]) (v := v) (by rw [e₃']; simp)
    (by simpa using h₃') g₃'
  exact braid_at Q h f g hf hg

theorem braidQ_pos {c d : I} (hcd : c ≠ d) {p : ℕ} {a : Obj (sig I)}
    (f g y₀ y₁ y₂ : a ⟶ a) {L₁ L₂ L₃ M₁ M₂ M₃ N₀ N₁ N₂ : Layer (sig I)}
    (hf : Diagram.layers f = [L₁, L₂, L₃]) (h₁ : L₁.left.length = p) (g₁ : L₁.gen = .cross c d)
    (h₂ : L₂.left.length = p + 1) (g₂ : L₂.gen = .cross c c)
    (h₃ : L₃.left.length = p) (g₃ : L₃.gen = .cross d c)
    (hg : Diagram.layers g = [M₁, M₂, M₃]) (h₁' : M₁.left.length = p + 1)
    (g₁' : M₁.gen = .cross d c) (h₂' : M₂.left.length = p) (g₂' : M₂.gen = .cross c c)
    (h₃' : M₃.left.length = p + 1) (g₃' : M₃.gen = .cross c d)
    (hy₀ : Diagram.layers y₀ = [N₀]) (k₀ : N₀.left.length = p) (l₀ : N₀.gen = .dot c)
    (hy₁ : Diagram.layers y₁ = [N₁]) (k₁ : N₁.left.length = p + 1) (l₁ : N₁.gen = .dot d)
    (hy₂ : Diagram.layers y₂ = [N₂]) (k₂ : N₂.left.length = p + 2) (l₂ : N₂.gen = .dot c) :
    (P).diag f - (P).diag g =
      ncEval (A := End ((P).obj a)) ![(P).diag y₀, (P).diag y₁, (P).diag y₂]
        (qbar (Q c d)) := by
  obtain ⟨e₁, e₂, e₃, -⟩ := chain_three f hf
  obtain ⟨e₁', e₂', e₃', -⟩ := chain_three g hg
  have en₀ := (chain_one y₀ hy₀).1
  have en₁ := (chain_one y₁ hy₁).1
  have en₂ := (chain_one y₂ hy₂).1
  obtain ⟨⟨⟩, u, g', w⟩ := L₁
  simp only at h₁ g₁; subst g₁ h₁ e₁
  obtain ⟨⟨⟩, u₂, g'', v⟩ := L₂
  simp only at h₂ g₂; subst g₂
  obtain ⟨rfl, -, rfl⟩ := append_three_inj (l₁ := u₂) (w₁ := [c]) (r₁ := c :: v)
    (l₂ := u ++ [d]) (w₂ := [c]) (r₂ := w) (by simpa using congrArg Obj.word e₂)
    (by simpa using h₂) rfl
  obtain rfl := eq_lay_of_dom L₃ (u := u) (v := c :: v) (by rw [e₃]; simp) h₃ g₃
  obtain rfl := eq_lay_of_dom M₁ (u := u ++ [c]) (v := v) (by rw [e₁']; simp)
    (by simpa using h₁') g₁'
  obtain rfl := eq_lay_of_dom M₂ (u := u) (v := d :: v) (by rw [e₂']; simp) h₂' g₂'
  obtain rfl := eq_lay_of_dom M₃ (u := u ++ [c]) (v := v) (by rw [e₃']; simp)
    (by simpa using h₃') g₃'
  obtain rfl := eq_lay_of_dom N₀ (u := u) (v := d :: c :: v) (by rw [en₀]; simp) k₀ l₀
  obtain rfl := eq_lay_of_dom N₁ (u := u ++ [c]) (v := c :: v) (by rw [en₁]; simp)
    (by simpa using k₁) l₁
  obtain rfl := eq_lay_of_dom N₂ (u := u ++ [c, d]) (v := v) (by rw [en₂]; simp)
    (by simpa using k₂) l₂
  exact braidQ_at Q hcd f g y₀ y₁ y₂ hf hg hy₀ hy₁ hy₂

/-- The interchange law in positional form: a generator `g` at position `p` and a generator
`h` at position `q ≥ p + arity g` can be applied in either order. -/
theorem interchange_pos {g h : Gen I} {p q : ℕ} (hpq : p + g.arity ≤ q) {a b : Obj (sig I)}
    (f₁ f₂ : a ⟶ b) {L₁ L₂ L₃ L₄ : Layer (sig I)}
    (hf₁ : Diagram.layers f₁ = [L₁, L₂]) (hf₂ : Diagram.layers f₂ = [L₃, L₄])
    (h₁ : L₁.left.length = p) (g₁ : L₁.gen = g) (h₂ : L₂.left.length = q) (g₂ : L₂.gen = h)
    (h₃ : L₃.left.length = q) (g₃ : L₃.gen = h) (h₄ : L₄.left.length = p) (g₄ : L₄.gen = g) :
    (P).diag f₁ = (P).diag f₂ := by
  obtain ⟨e₁, e₂, -⟩ := chain_two f₁ hf₁
  obtain ⟨e₃, e₄, -⟩ := chain_two f₂ hf₂
  obtain ⟨⟨⟩, u, g', v⟩ := L₁
  simp only at h₁ g₁; subst g' h₁ e₁
  obtain ⟨⟨⟩, u₃, h', v₃⟩ := L₃
  simp only at h₃ g₃; subst h' h₃
  have hw : u₃ ++ h.dom ++ v₃ = (u ++ g.dom) ++ v := by
    simpa using congrArg Obj.word e₃
  have hlen : (u ++ g.dom).length ≤ u₃.length := by simpa using hpq
  obtain ⟨n, hn⟩ : ∃ n, u₃.length = (u ++ g.dom).length + n :=
    ⟨_, (Nat.add_sub_cancel' hlen).symm⟩
  obtain ⟨mid, hu₃, hv⟩ : ∃ mid, u₃ = u ++ g.dom ++ mid ∧ v = mid ++ h.dom ++ v₃ := by
    refine ⟨v.take n, ?_, ?_⟩
    · have := congrArg (List.take u₃.length) hw
      rw [List.append_assoc u₃, List.take_left, hn, List.take_append] at this
      exact this
    · have := congrArg (List.drop u₃.length) hw
      rw [List.append_assoc u₃, List.drop_left, hn, List.drop_append] at this
      conv_lhs => rw [← List.take_append_drop n v]
      rw [← this, List.append_assoc]
  subst hu₃ hv
  obtain rfl := eq_lay_of_dom L₂ (u := u ++ g.cod ++ mid) (v := v₃) (by rw [e₂]; simp)
    (by simp [h₂]) g₂
  obtain rfl := eq_lay_of_dom L₄ (u := u) (v := mid ++ h.cod ++ v₃) (by rw [e₄]; simp) h₄ g₄
  exact interchange_at Q u mid v₃ g h f₁ f₂ hf₁ hf₂

end Positional

end Categorification.KLR.Diagram

end
