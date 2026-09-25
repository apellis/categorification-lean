/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Basic

/-!
# KLR algebras

The Khovanov–Lauda–Rouquier algebra `R(ν)` attached to a family of polynomials
`Q i j ∈ k[u, v]` (indexed by a type `I` of vertices) and a weight `ν ∈ ℕ[I]`,
following

* M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum
  groups I*, arXiv:0803.4121v2, §2.1 (simply-laced case), and
* M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum
  groups II*, arXiv:0804.2080v1, §3 (arbitrary Cartan data).

Weights are multisets `ν : Multiset I`, and `m = card ν` is the number of strands.
`Seq ν` is the finite set of sequences `i = i₁ ⋯ i_m` of weight `ν`.

## Presentation

We use the standard presentation of the diagrammatic algebra by generators and
relations. A braid-like diagram read from bottom to top is a product (right to left)
of the generators

* `e i` — the identity diagram `1_i` with bottom and top sequence `i`;
* `x a` — a dot on the `a`-th strand (`x a * e i` is `x_{a,i}` in the paper);
* `ψ k` — a crossing of the strands at positions `k, k + 1`
  (`ψ k * e i` is `δ_{k,i}` in the paper).

The planar isotopies of the paper become the relations that dots and crossings far
apart commute; the local relations (2.3)–(2.8) of KL I (and their KL II
generalisation) become

* `ψ_k² e_i = 0` if `i_k = i_{k+1}`, and `ψ_k² e_i = Q_{i_k i_{k+1}}(x_k, x_{k+1}) e_i`
  otherwise;
* `(x_k ψ_k - ψ_k x_{k+1}) e_i = (ψ_k x_k - x_{k+1} ψ_k) e_i = [i_k = i_{k+1}] e_i`;
* `(ψ_k ψ_{k+1} ψ_k - ψ_{k+1} ψ_k ψ_{k+1}) e_i = Q̄_{i_k i_{k+1}}(x_k, x_{k+1}, x_{k+2}) e_i`
  if `i_k = i_{k+2} ≠ i_{k+1}` and `0` otherwise, where
  `Q̄(a, b, c) = (Q(a, b) - Q(c, b)) / (a - c)`.

For the simply-laced data of KL I (`Q_{ij} = u + v` when `i`, `j` are joined by an
edge and `Q_{ij} = 1` otherwise, see `klQ`) these are literally the relations of
KL I §2.1; the correspondence is recorded in `Categorification.KLR.KL1`.

Positions are zero-indexed: the paper's `x_{k}` is `x ⟨k - 1, _⟩` here, and the
paper's `δ_k` is `ψ (k - 1)`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA

variable {I : Type*}

/-! ### Sequences -/

/-- Sequences of weight `ν`: maps `Fin (card ν) → I` taking each value `i` exactly
`ν.count i` times. -/
def Seq (ν : Multiset I) : Type _ :=
  {i : Fin (Multiset.card ν) → I // (Finset.univ.val.map i) = ν}

namespace Seq

variable {ν : Multiset I}

instance [DecidableEq I] : DecidableEq (Seq ν) :=
  inferInstanceAs (DecidableEq {f : Fin (Multiset.card ν) → I // Finset.univ.val.map f = ν})

theorem mem (i : Seq ν) (a : Fin (Multiset.card ν)) : i.1 a ∈ ν := by
  have h : i.1 a ∈ Finset.univ.val.map i.1 := Multiset.mem_map_of_mem _ (Finset.mem_univ _)
  rwa [i.2] at h

instance : Finite (Seq ν) := by
  classical
  refine Finite.of_injective
    (fun i : Seq ν => fun a => (⟨i.1 a, Multiset.mem_toFinset.2 (i.mem a)⟩ : ν.toFinset)) ?_
  intro i j h
  apply Subtype.ext
  funext a
  have := congrArg (fun f => (f a).1) h
  simpa using this

noncomputable instance : Fintype (Seq ν) := Fintype.ofFinite _

/-- The label `i_a` at position `a`. -/
abbrev lbl (i : Seq ν) (a : Fin (Multiset.card ν)) : I := i.1 a

/-- `S_m` acts on sequences by permuting positions: `(w • i)_{w a} = i_a`. -/
instance : MulAction (Perm (Fin (Multiset.card ν))) (Seq ν) where
  smul w i := ⟨i.1 ∘ w.symm, by
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
    exact i.2⟩
  one_smul i := rfl
  mul_smul w₁ w₂ i := rfl

@[simp] theorem smul_apply (w : Perm (Fin (Multiset.card ν))) (i : Seq ν)
    (a : Fin (Multiset.card ν)) : (w • i).1 a = i.1 (w.symm a) := rfl

end Seq

/-! ### Noncommutative evaluation of polynomials -/

section ncEval

variable {k : Type*} [CommRing k] {A : Type*} [Ring A] [Algebra k A]

/-- Evaluate a polynomial at a tuple of elements of a (possibly noncommutative)
algebra, ordering each monomial as `x₀^{s₀} x₁^{s₁} ⋯`. This is only used to write
down relations; for pairwise commuting arguments it agrees with `MvPolynomial.aeval`. -/
noncomputable def ncEval {n : ℕ} (x : Fin n → A) (p : MvPolynomial (Fin n) k) : A :=
  p.sum fun s c => algebraMap k A c * (List.ofFn fun a => x a ^ s a).prod

end ncEval

/-! ### The divided difference `Q̄` -/

section qbar

variable {k : Type*} [CommRing k]

/-- `Q̄(a, b, c) = (Q(a, b) - Q(c, b)) / (a - c)`, computed monomialwise:
`a^p b^q ↦ (∑_{t < p} a^t c^{p-1-t}) b^q`. See `qbar_spec`. -/
noncomputable def qbar (Q : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 3) k :=
  Q.sum fun s c => C c * X 1 ^ s 1 *
    ∑ t ∈ Finset.range (s 0), X 0 ^ t * X 2 ^ (s 0 - 1 - t)

theorem qbar_add (p q : MvPolynomial (Fin 2) k) : qbar (p + q) = qbar p + qbar q := by
  unfold qbar
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

theorem qbar_monomial (s : Fin 2 →₀ ℕ) (c : k) :
    qbar (monomial s c) = C c * X 1 ^ s 1 *
      ∑ t ∈ Finset.range (s 0), X 0 ^ t * X 2 ^ (s 0 - 1 - t) := by
  unfold qbar
  exact Finsupp.sum_single_index (by simp)

theorem qbar_spec (Q : MvPolynomial (Fin 2) k) :
    (X 0 - X 2) * qbar Q = rename ![0, 1] Q - rename ![2, 1] Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [qbar_monomial, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_two]
    simp only [map_mul, map_pow, rename_C, rename_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    have := geom_sum₂_mul (X 0 : MvPolynomial (Fin 3) k) (X 2) (s 0)
    linear_combination (C c * X 1 ^ s 1) * this
  | add p q hp hq =>
    rw [qbar_add, mul_add, hp, hq, map_add, map_add]; ring

end qbar

/-! ### Generators and relations -/

/-- Generators of the KLR algebra `R(ν)`. Crossings are indexed by `ℕ`; the crossing
`cross k` with `k + 1 ≥ card ν` is set to zero by a relation. -/
inductive Gen (ν : Multiset I) : Type _
  | idem : Seq ν → Gen ν
  | dot : Fin (Multiset.card ν) → Gen ν
  | cross : ℕ → Gen ν

variable {k : Type*} [CommRing k] [DecidableEq I]

section Rel

variable (k) (Q : I → I → MvPolynomial (Fin 2) k) (ν : Multiset I)

local notation "m" => Multiset.card ν
local notation "Fr" => FreeAlgebra k (Gen ν)

/-- Idempotent generator in the free algebra. -/
noncomputable abbrev fe (i : Seq ν) : Fr := FreeAlgebra.ι k (Gen.idem i)
/-- Dot generator in the free algebra. -/
noncomputable abbrev fx (a : Fin m) : Fr := FreeAlgebra.ι k (Gen.dot a)
/-- Crossing generator in the free algebra. -/
noncomputable abbrev fψ (j : ℕ) : Fr := FreeAlgebra.ι k (Gen.cross j)

/-- The defining relations of `R(ν)`. -/
inductive Rel : Fr → Fr → Prop
  /-- `e_i e_j = δ_{ij} e_i`. -/
  | idem_mul (i j : Seq ν) : Rel (fe k ν i * fe k ν j) (if i = j then fe k ν i else 0)
  /-- `∑_i e_i = 1`. -/
  | idem_sum : Rel (∑ i, fe k ν i) 1
  /-- Dots preserve sequences. -/
  | dot_idem (a : Fin m) (i : Seq ν) : Rel (fx k ν a * fe k ν i) (fe k ν i * fx k ν a)
  /-- A crossing `ψ_k` takes sequence `i` to `s_k i`. -/
  | cross_idem (j : ℕ) (i : Seq ν) :
      Rel (fψ k ν j * fe k ν i) (fe k ν (sadj m j • i) * fψ k ν j)
  /-- Out-of-range crossings vanish. -/
  | cross_zero (j : ℕ) (h : m ≤ j + 1) : Rel (fψ k ν j) 0
  /-- Dots commute (isotopy). -/
  | dot_dot (a b : Fin m) : Rel (fx k ν a * fx k ν b) (fx k ν b * fx k ν a)
  /-- Distant crossings commute (isotopy). -/
  | cross_cross (j l : ℕ) (h : j + 1 < l) : Rel (fψ k ν j * fψ k ν l) (fψ k ν l * fψ k ν j)
  /-- Dots slide through crossings of other strands (isotopy). -/
  | dot_cross (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
      Rel (fx k ν a * fψ k ν j) (fψ k ν j * fx k ν a)
  /-- KL I (2.4)/(2.5): `(x_k ψ_k - ψ_k x_{k+1}) e_i = [i_k = i_{k+1}] e_i`. -/
  | dot_cross_left (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
      Rel ((fx k ν ⟨j, by omega⟩ * fψ k ν j - fψ k ν j * fx k ν ⟨j + 1, h⟩) * fe k ν i)
        (if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then fe k ν i else 0)
  /-- KL I (2.4)/(2.6): `(ψ_k x_k - x_{k+1} ψ_k) e_i = [i_k = i_{k+1}] e_i`. -/
  | dot_cross_right (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
      Rel ((fψ k ν j * fx k ν ⟨j, by omega⟩ - fx k ν ⟨j + 1, h⟩ * fψ k ν j) * fe k ν i)
        (if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then fe k ν i else 0)
  /-- KL I (2.3): `ψ_k² e_i = 0` if `i_k = i_{k+1}`, else `Q_{i_k i_{k+1}}(x_k, x_{k+1}) e_i`. -/
  | cross_sq (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
      Rel (fψ k ν j * fψ k ν j * fe k ν i)
        (if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then 0 else
          ncEval ![fx k ν ⟨j, by omega⟩, fx k ν ⟨j + 1, h⟩]
            (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩)) * fe k ν i)
  /-- KL I (2.7)/(2.8): the braid relation with correction term. -/
  | braid (j : ℕ) (h : j + 2 < m) (i : Seq ν) :
      Rel ((fψ k ν j * fψ k ν (j + 1) * fψ k ν j
          - fψ k ν (j + 1) * fψ k ν j * fψ k ν (j + 1)) * fe k ν i)
        (if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩ ∧
            i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, by omega⟩ then
          ncEval ![fx k ν ⟨j, by omega⟩, fx k ν ⟨j + 1, by omega⟩, fx k ν ⟨j + 2, h⟩]
            (qbar (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩))) * fe k ν i
        else 0)

end Rel

/-- The KLR algebra `R(ν)` over `k` for the data `Q`. -/
def KLRAlgebra (k : Type*) [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
    (ν : Multiset I) : Type _ :=
  RingQuot (Rel k Q ν)

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

noncomputable instance : Ring (KLRAlgebra k Q ν) := inferInstanceAs (Ring (RingQuot _))
noncomputable instance : Algebra k (KLRAlgebra k Q ν) :=
  inferInstanceAs (Algebra k (RingQuot _))

variable (k Q ν) in
/-- The quotient map from the free algebra. -/
noncomputable def mk : FreeAlgebra k (Gen ν) →ₐ[k] KLRAlgebra k Q ν :=
  RingQuot.mkAlgHom k (Rel k Q ν)

theorem mk_surjective : Function.Surjective (mk k Q ν) :=
  RingQuot.mkAlgHom_surjective _ _

/-- The idempotent `1_i`. -/
noncomputable def e (i : Seq ν) : KLRAlgebra k Q ν := mk k Q ν (fe k ν i)
/-- The dot on the `a`-th strand. -/
noncomputable def x (a : Fin (Multiset.card ν)) : KLRAlgebra k Q ν := mk k Q ν (fx k ν a)
/-- The crossing of strands `j` and `j + 1` (zero if out of range). -/
noncomputable def ψ (j : ℕ) : KLRAlgebra k Q ν := mk k Q ν (fψ k ν j)

/-- The element `ψ_{ρ₀} ψ_{ρ₁} ⋯` attached to a word `ρ`. -/
noncomputable def ψw (ρ : List ℕ) : KLRAlgebra k Q ν := (ρ.map ψ).prod

theorem rel {a b : FreeAlgebra k (Gen ν)} (h : Rel k Q ν a b) : mk k Q ν a = mk k Q ν b :=
  RingQuot.mkAlgHom_rel k h

local notation "m" => Multiset.card ν

theorem e_mul_e (i j : Seq ν) :
    (e i * e j : KLRAlgebra k Q ν) = if i = j then e i else 0 := by
  have := rel (Q := Q) (Rel.idem_mul i j)
  simp only [map_mul] at this
  rw [e, e, this]; split_ifs <;> simp [e]

theorem e_mul_self (i : Seq ν) : (e i * e i : KLRAlgebra k Q ν) = e i := by
  simp [e_mul_e]

theorem sum_e : (∑ i, e i : KLRAlgebra k Q ν) = 1 := by
  have := rel (Q := Q) (Rel.idem_sum (k := k) (ν := ν))
  simpa [map_sum] using this

theorem x_mul_e (a : Fin m) (i : Seq ν) :
    (x a * e i : KLRAlgebra k Q ν) = e i * x a := by
  simpa using rel (Q := Q) (Rel.dot_idem a i)

theorem ψ_mul_e (j : ℕ) (i : Seq ν) :
    (ψ j * e i : KLRAlgebra k Q ν) = e (sadj m j • i) * ψ j := by
  simpa using rel (Q := Q) (Rel.cross_idem j i)

theorem ψ_eq_zero (j : ℕ) (h : m ≤ j + 1) : (ψ j : KLRAlgebra k Q ν) = 0 := by
  simpa using rel (Q := Q) (Rel.cross_zero j h)

theorem x_mul_x (a b : Fin m) : (x a * x b : KLRAlgebra k Q ν) = x b * x a := by
  simpa using rel (Q := Q) (Rel.dot_dot a b)

theorem ψ_mul_ψ (j l : ℕ) (h : j + 1 < l) :
    (ψ j * ψ l : KLRAlgebra k Q ν) = ψ l * ψ j := by
  simpa using rel (Q := Q) (Rel.cross_cross (k := k) (ν := ν) j l h)

theorem x_mul_ψ (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    (x a * ψ j : KLRAlgebra k Q ν) = ψ j * x a := by
  simpa using rel (Q := Q) (Rel.dot_cross a j h₁ h₂)

theorem dot_cross_left (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    ((x ⟨j, by omega⟩ * ψ j - ψ j * x ⟨j + 1, h⟩) * e i : KLRAlgebra k Q ν) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then e i else 0 := by
  have := rel (Q := Q) (Rel.dot_cross_left j h i)
  simp only [map_mul, map_sub] at this
  rw [x, x, ψ, e, this]; split_ifs <;> simp [e]

theorem dot_cross_right (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    ((ψ j * x ⟨j, by omega⟩ - x ⟨j + 1, h⟩ * ψ j) * e i : KLRAlgebra k Q ν) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then e i else 0 := by
  have := rel (Q := Q) (Rel.dot_cross_right j h i)
  simp only [map_mul, map_sub] at this
  rw [x, x, ψ, e, this]; split_ifs <;> simp [e]

theorem mk_ncEval {n : ℕ} (y : Fin n → FreeAlgebra k (Gen ν)) (p : MvPolynomial (Fin n) k) :
    mk k Q ν (ncEval y p) = ncEval (fun a => mk k Q ν (y a)) p := by
  simp only [ncEval, Finsupp.sum, map_sum, map_mul, AlgHom.commutes, map_list_prod,
    List.map_ofFn, Function.comp_def, map_pow]

theorem ψ_sq (j : ℕ) (h : j + 1 < m) (i : Seq ν) :
    (ψ j * ψ j * e i : KLRAlgebra k Q ν) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then 0 else
        ncEval ![x ⟨j, by omega⟩, x ⟨j + 1, h⟩]
          (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩)) * e i := by
  have := rel (Q := Q) (Rel.cross_sq j h i)
  simp only [map_mul] at this
  rw [ψ, e, this]
  split_ifs
  · simp
  · rw [map_mul, mk_ncEval]
    congr 2
    funext a; fin_cases a <;> rfl

theorem braid (j : ℕ) (h : j + 2 < m) (i : Seq ν) :
    ((ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) * e i : KLRAlgebra k Q ν) =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩ ∧
          i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, by omega⟩ then
        ncEval ![x ⟨j, by omega⟩, x ⟨j + 1, by omega⟩, x ⟨j + 2, h⟩]
          (qbar (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩))) * e i
      else 0 := by
  have := rel (Q := Q) (Rel.braid j h i)
  simp only [map_mul, map_sub] at this
  rw [ψ, ψ, e, this]
  split_ifs
  · rw [map_mul, mk_ncEval]
    congr 2
    funext a; fin_cases a <;> rfl
  · simp

/-! ### The polynomial subalgebra -/

theorem x_commute (a b : Fin m) : Commute (x a : KLRAlgebra k Q ν) (x b) := x_mul_x a b

/-- The subalgebra generated by the dots; it is commutative. -/
noncomputable def dotSubalgebra : Subalgebra k (KLRAlgebra k Q ν) :=
  Algebra.adjoin k (Set.range x)

theorem dotSubalgebra_comm (p q : dotSubalgebra (k := k) (Q := Q) (ν := ν)) : p * q = q * p := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  apply Subtype.ext
  show p * q = q * p
  have key : ∀ a ∈ Algebra.adjoin k (Set.range (x (k := k) (Q := Q) (ν := ν))),
      ∀ b ∈ Set.range (x (k := k) (Q := Q) (ν := ν)), a * b = b * a := by
    intro a ha b hb
    induction ha using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy; obtain ⟨b, rfl⟩ := hb; exact x_mul_x a b
    | algebraMap r => exact Algebra.commutes r b
    | add y z _ _ hy hz => rw [add_mul, mul_add, hy, hz]
    | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]
  induction hq using Algebra.adjoin_induction with
  | mem y hy => exact key p hp y hy
  | algebraMap r => exact (Algebra.commutes r p).symm
  | add y z _ _ hy hz => rw [add_mul, mul_add, hy, hz]
  | mul y z _ _ hy hz => rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]

noncomputable instance : CommRing (dotSubalgebra (k := k) (Q := Q) (ν := ν)) :=
  { (dotSubalgebra (k := k) (Q := Q) (ν := ν)).toRing with mul_comm := dotSubalgebra_comm }

/-- The polynomial ring `k[x_1, …, x_m]` maps to `R(ν)` by sending `X a` to the dot `x a`.
(Its image in `e_i R(ν) e_i`, i.e. `pol p * e i`, is the paper's `Pol(ν, i)`.) -/
noncomputable def pol : MvPolynomial (Fin m) k →ₐ[k] KLRAlgebra k Q ν :=
  (dotSubalgebra (k := k) (Q := Q) (ν := ν)).val.comp
    (MvPolynomial.aeval fun a => ⟨x a, Algebra.subset_adjoin ⟨a, rfl⟩⟩)

@[simp] theorem pol_X (a : Fin m) : pol (MvPolynomial.X a) = (x a : KLRAlgebra k Q ν) := by
  simp [pol]

theorem pol_mem_dotSubalgebra (p : MvPolynomial (Fin m) k) :
    pol p ∈ dotSubalgebra (k := k) (Q := Q) (ν := ν) := by
  simp only [pol, AlgHom.comp_apply, Subalgebra.coe_val]; exact Subtype.property _

theorem ncEval_eq_pol {n : ℕ} (f : Fin n → Fin m) (p : MvPolynomial (Fin n) k) :
    ncEval (fun a => (x (f a) : KLRAlgebra k Q ν)) p = pol (rename f p) := by
  conv_rhs => rw [p.as_sum]
  simp only [ncEval, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rename_monomial, monomial_eq, Finsupp.prod_mapDomain_index
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_fintype _ _
    (fun _ => pow_zero _), ← List.prod_ofFn, map_mul, algHom_C, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, map_pow, pol_X]
  rfl

theorem e_commute_pol (i : Seq ν) (p : MvPolynomial (Fin m) k) :
    Commute (e i : KLRAlgebra k Q ν) (pol p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [algHom_C]; exact Algebra.commute_algebraMap_right _ _
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | mul_X p a hp => rw [map_mul, pol_X]; exact hp.mul_right (x_mul_e a i).symm


end KLRAlgebra

end Categorification.KLR
