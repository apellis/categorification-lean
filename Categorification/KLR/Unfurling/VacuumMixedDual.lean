/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumMixed
import Categorification.TwoRep.Coop

/-!
# Counterclockwise bubbles on the generating object with labels of both signs

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`: the case of a positive weight `h = n > 0` for the colour `i`.
Rouquier's inverse (Brundan (1.8)) gives a cup `ν : V → R E V` and caps `Dᵗ ≫ d : R E V → V`
with `ν ≫ Dᵗ ≫ d = δ_{t, n-1}` for `t < n`, and `ν ≫ σ = 0` for the rightward crossing
`σ : R E V → E R V`. The bubble `ν ≫ Dᵏ ≫ d` is the counterclockwise bubble with `k` dots.
This is the statement of `VacuumMixed` in the opposite category: the lowest weight labels now
decompose the caps, and the chains of the highest weight labels map out of `E R V`.

## Main results

* `ev_comp_eq_lwSeq_dual`: `ev (ν ≫ Dᵏ ≫ d) = [t^{k+1-n}] ∏_b (1 - z_b t)^{Λ_b}
  ∏ₐ (1 - zₐ t)^{-hₐ}`.
-/

namespace Categorification.KLR.Unfurling

open CategoryTheory CategoryTheory.Limits PowerSeries Opposite

variable {L : Type*} [Field L] {C : Type*} [Category C] [Preadditive C] [Linear L C]

/-- An endomorphism of `X`, as an endomorphism of `op X`. -/
def endOp {X : C} (e : End X) : End (op X) := e.op

omit [Preadditive C] in
@[simp] theorem unop_endOp {X : C} (e : End X) : (endOp e).unop = e := rfl

omit [Preadditive C] in
/-- Powers in `End (op X)` are opposite to powers in `End X`. -/
theorem unop_pow_op {X : C} (e : End X) (n : ℕ) : (endOp e ^ n).unop = e ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, End.mul_def, unop_comp, ih, unop_endOp, pow_succ', End.mul_def]

/-- Scalars in `End (op X)` are opposite to scalars in `End X`. -/
theorem unop_algebraMap_op {X : C} (r : L) :
    (algebraMap L (End (op X)) r).unop = algebraMap L (End X) r := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TwoRep.unop_smul']
  rfl

/-- An `L`-algebra map from `End V` to a commutative ring, read on `End (op V)`. -/
def evOp {R : Type*} [CommRing R] [Algebra L R] {V : C} (ev : End V →ₐ[L] R) :
    End (op V) →ₐ[L] R where
  toFun f := ev f.unop
  map_one' := ev.map_one
  map_mul' f g := by
    change ev (f.unop ≫ g.unop) = _
    rw [← End.mul_def, map_mul, mul_comm]
  map_zero' := ev.map_zero
  map_add' f g := ev.map_add f.unop g.unop
  commutes' r := by
    rw [unop_algebraMap_op, ev.commutes]

/-- **The counterclockwise bubbles on the generating object, labels of both signs** (Webster,
arXiv:1603.06311v3, proof of the theorem with label `nondegenerate`). Let `V` be an object with a
cup `ν : V → Q` and caps `Dᵗ ≫ d : Q → V` dual to it in degrees `t < n`.

* Over the lowest weight labels `a`: `Q = ⊕ₐ Wₐ` (`∑ ι a ≫ π a = 1`), the cap with `n` dots is
  `(zₐ + yₐ)ⁿ ≫ νₐ` on the summand `a`, and `yₐ^m ≫ νₐ = 0` for `m ≥ hₐ`.
* Over the highest weight labels `b`: `w_b` is a two-sided inverse of `D - z_b`, and
  `c_{b,0}, …, c_{b,Λ_b-1} : P → V` satisfy `(D' - z_b) ≫ c_{b,m} = ∑_{j<m} β_{b,m,j} c_{b,j}`
  with `β_{b,m+1,m} ≠ 0`, and `κ ≫ c_{b,m} = δ_{m,0}`.
* `σ : Q → P` satisfies the dot slide `D ≫ σ - σ ≫ D' = d ≫ κ`, and `ν ≫ σ = 0` if `n > 0`,
  `ν ≫ σ = κ` if `n = 0` (for `n = 0`, `σ` is invertible and `ν = κ ≫ σ⁻¹`).
* `∑ₐ hₐ = n + ∑_b Λ_b > 0`.

Then `ev (ν ≫ Dᵏ ≫ d) = [t^{k+1-n}] ∏_b (1 - z_b t)^{Λ_b} ∏ₐ (1 - zₐ t)^{-hₐ}`. This is
`ev_comp_eq_lwSeq` in the opposite category. -/
theorem ev_comp_eq_lwSeq_dual {R : Type*} [CommRing R] [Algebra L R] {V Q P : C}
    (ev : End V →ₐ[L] R)
    {A : Type*} [Fintype A] {Wa : A → C} (π : ∀ a, Wa a ⟶ Q) (ι : ∀ a, Q ⟶ Wa a)
    (νa : ∀ a, Wa a ⟶ V) (y : ∀ a, End (Wa a)) (za : A → L) (hp : A → ℕ)
    (ν : V ⟶ Q) (d : Q ⟶ V) (D : End Q) (hπι : ∑ a, ι a ≫ π a = 𝟙 Q)
    (hc : ∀ n a, π a ≫ (D ^ n : End Q) ≫ d =
      ((algebraMap L (End (Wa a)) (za a) + y a) ^ n : End (Wa a)) ≫ νa a)
    (hν : ∀ a m, hp a ≤ m → (y a ^ m : End (Wa a)) ≫ νa a = 0)
    {B : Type*} [Fintype B] [DecidableEq B] (zb : B → L) (hzb : Function.Injective zb)
    (Λ : B → ℕ) (w : B → End Q) (hw₁ : ∀ b, (D - algebraMap L (End Q) (zb b)) * w b = 1)
    (hw₂ : ∀ b, w b * (D - algebraMap L (End Q) (zb b)) = 1)
    (σ : Q ⟶ P) (κ : V ⟶ P) (D' : End P) (hrel : D ≫ σ - σ ≫ D' = d ≫ κ)
    (c : B → ℕ → (P ⟶ V)) (β : B → ℕ → ℕ → L)
    (hcN : ∀ b m, m < Λ b → (D' - algebraMap L (End P) (zb b) : End P) ≫ c b m =
      ∑ j ∈ Finset.range m, β b m j • c b j)
    (hβ : ∀ b m, m + 1 < Λ b → β b (m + 1) m ≠ 0)
    (hcκ : ∀ b m, m < Λ b → κ ≫ c b m = if m = 0 then 𝟙 V else 0)
    (n : ℕ) (hN : ∑ a, hp a = n + ∑ b, Λ b) (hNpos : 0 < ∑ a, hp a)
    (hσd : ν ≫ σ = if n = 0 then κ else 0)
    (hd : ∀ t < n, ev (ν ≫ (D ^ t : End Q) ≫ d) = if t + 1 = n then 1 else 0) (k : ℕ) :
    ev (ν ≫ (D ^ k : End Q) ≫ d) = algebraMap L R (lwSeq n
      ((∏ b, (1 - PowerSeries.C (zb b) * X) ^ Λ b) *
        ((∏ a, oneSubUnit (za a) ^ (-(hp a : ℤ)) : (PowerSeries L)ˣ) : PowerSeries L)) k) := by
  have hb : ∀ t, ev (ν ≫ (D ^ t : End Q) ≫ d) =
      evOp ev (d.op ≫ (endOp D ^ t : End (op Q)) ≫ ν.op) := fun t => by
    change _ = ev ((d.op ≫ (endOp D ^ t : End (op Q)) ≫ ν.op).unop)
    rw [unop_comp, unop_comp, unop_pow_op, Category.assoc]
    rfl
  have hsc : ∀ {X : C} (r : L) (e : End X),
      ((algebraMap L (End (op X)) r - endOp e : End (op X))).unop =
        (algebraMap L (End X) r - e : End X) := fun r e => by
    rw [unop_sub, unop_algebraMap_op]; rfl
  have hsc' : ∀ {X : C} (r : L) (e : End X),
      ((endOp e - algebraMap L (End (op X)) r : End (op X))).unop =
        (e - algebraMap L (End X) r : End X) := fun r e => by
    rw [unop_sub, unop_algebraMap_op]; rfl
  have hsa : ∀ {X : C} (r : L) (e : End X),
      ((algebraMap L (End (op X)) r + endOp e : End (op X))) =
        endOp (algebraMap L (End X) r + e : End X) := fun r e => by
    apply Quiver.Hom.unop_inj
    rw [unop_add, unop_algebraMap_op]; rfl
  rw [hb]
  refine ev_comp_eq_lwSeq (evOp ev) (fun a => (π a).op) (fun a => (ι a).op) (fun a => (νa a).op)
    (fun a => endOp (y a)) za hp d.op ν.op (endOp D) ?_ ?_ ?_ zb hzb Λ (fun b => endOp (w b)) ?_ ?_
    σ.op κ.op (endOp D') ?_ (fun b m => (c b m).op) β ?_ hβ ?_ n hN hNpos ?_ ?_ k
  · apply Quiver.Hom.unop_inj
    rw [unop_sum]
    simpa using hπι
  · intro m a
    apply Quiver.Hom.unop_inj
    rw [hsa, unop_comp, unop_comp, unop_comp, unop_pow_op, unop_pow_op]
    simp only [Quiver.Hom.unop_op]
    exact hc m a
  · intro a m hm
    apply Quiver.Hom.unop_inj
    rw [unop_comp, unop_pow_op, unop_zero]
    exact hν a m hm
  · intro b
    apply Quiver.Hom.unop_inj
    rw [End.mul_def, unop_comp, hsc' (zb b) D]
    exact (End.mul_def _ _).symm.trans (hw₂ b)
  · intro b
    apply Quiver.Hom.unop_inj
    rw [End.mul_def, unop_comp, hsc' (zb b) D]
    exact (End.mul_def _ _).symm.trans (hw₁ b)
  · apply Quiver.Hom.unop_inj
    rw [unop_sub, unop_comp, unop_comp, unop_comp]
    exact hrel
  · intro b m hm
    apply Quiver.Hom.unop_inj
    rw [unop_comp, hsc' (zb b) D', unop_sum]
    simp only [TwoRep.unop_smul', Quiver.Hom.unop_op]
    exact hcN b m hm
  · intro b m hm
    apply Quiver.Hom.unop_inj
    rw [unop_comp]
    simp only [Quiver.Hom.unop_op]
    rw [hcκ b m hm]
    split_ifs <;> rfl
  · apply Quiver.Hom.unop_inj
    rw [unop_comp]
    simp only [Quiver.Hom.unop_op]
    rw [hσd]
    split_ifs <;> rfl
  · intro t ht
    rw [← hb]
    exact hd t ht

end Categorification.KLR.Unfurling
