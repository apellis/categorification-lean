/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.TopDividedPower
import Categorification.Algebra.NilHeckeModuleRecognition

/-!
# Simple subobjects of divided powers of a lowest-weight simple object

Chuang–Rouquier, arXiv:math/0407205v2, Proposition 5.20 (b), socle part: let `U` be a simple
object of a weak `𝔰𝔩₂`-categorification with nilHecke actions on `E` and `F`, with `F U = 0`,
and let `N = h₊([U])`. For `i ≤ N` and every simple `S`, `dim Hom(S, E^{(i)} U) ≤ 1`.

The argument is that of Chuang–Rouquier, with the nilHecke ring in place of the affine Hecke
algebra. Write `N = i + m` and `T = E^{(N)} U`, which is simple
(`WeakSl2.simple_divObj_top_of_F_eq_zero`). The space `R = Hom(T, E^N U)` is a representation of
`NH_N` of dimension `N!` (since `E^N U ≅ T^{⊕ N!}`) on which the dots act nilpotently. A
nonzero map `φ : S → E^{(i)} U ⊆ E^i U` gives `E^m φ : E^m S → E^N U`, and composing with a
nonzero map `z : T → E^m S` killed by the dots of `E^m` gives a vector of `R` fixed by the
idempotent `e_i` of `NH_i ⊆ NH_N` and killed by the dots `x_b`, `b ≥ i`. These vectors lie on a
line (`NilHecke.exists_forall_mem_span_of_idemNHAt`), and `φ ↦ z ≫ E^m(φ)` is injective.

The local nilpotence of the dot (Chuang–Rouquier, §5.2.1, with eigenvalue `0`) is the
hypothesis `hX`, and the condition `End(S) = k` for simple `S` (Chuang–Rouquier, §5.1.1) is the
hypothesis `hEnd`. The functor `E` is `k`-linear.

## Main results

* `WeakSl2.finrank_hom_divObj_le_one`: **Chuang–Rouquier, Proposition 5.20 (b)**, socle part,
  for `E`: `dim Hom(S, E^{(i)} U) ≤ 1`.
-/

namespace Categorification.Sl2

open CategoryTheory Limits Module

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Lifting maps through powers of `E` -/

section LiftMap

variable {E : C ⥤ C}

/-- For `g : M ⟶ Eⁱ U`, the map `E^m(g) : E^m M ⟶ E^{i+m} U`. -/
def liftMap {M U : C} {i : ℕ} (g : M ⟶ (Epow E i).obj U) :
    (m : ℕ) → ((Epow E m).obj M ⟶ (Epow E (i + m)).obj U)
  | 0 => g
  | m + 1 => E.map (liftMap g m)

@[simp] theorem liftMap_zero {M U : C} {i : ℕ} (g : M ⟶ (Epow E i).obj U) :
    liftMap g 0 = g := rfl

theorem liftMap_succ {M U : C} {i : ℕ} (g : M ⟶ (Epow E i).obj U) (m : ℕ) :
    liftMap g (m + 1) = E.map (liftMap g m) := rfl

theorem mono_liftMap [E.PreservesMonomorphisms] {M U : C} {i : ℕ} (g : M ⟶ (Epow E i).obj U)
    [Mono g] : ∀ m, Mono (liftMap g m)
  | 0 => inferInstanceAs (Mono g)
  | m + 1 => by
    have := mono_liftMap g m
    rw [liftMap_succ]
    exact E.map_mono _

theorem liftMap_comp {M M' U : C} {i : ℕ} (f : M' ⟶ M) (g : M ⟶ (Epow E i).obj U) :
    ∀ m, liftMap (f ≫ g) m = (Epow E m).map f ≫ liftMap g m
  | 0 => rfl
  | m + 1 => by
    rw [liftMap_succ, liftMap_comp f g m, Functor.map_comp, liftMap_succ]
    rfl

theorem liftMap_add [Preadditive C] [E.Additive] {M U : C} {i : ℕ} (g g' : M ⟶ (Epow E i).obj U) :
    ∀ m, liftMap (g + g') m = liftMap g m + liftMap g' m
  | 0 => rfl
  | m + 1 => by rw [liftMap_succ, liftMap_add g g' m, Functor.map_add]; rfl

theorem liftMap_smul {k : Type*} [CommRing k] [Preadditive C] [Linear k C] [E.Linear k] {M U : C} {i : ℕ} (c : k) (g : M ⟶ (Epow E i).obj U) :
    ∀ m, liftMap (c • g) m = c • liftMap g m
  | 0 => rfl
  | m + 1 => by rw [liftMap_succ, liftMap_smul c g m, Functor.map_smul]; rfl

end LiftMap

namespace NilHeckeData

variable [Preadditive C] {E : C ⥤ C} (D : NilHeckeData E)

/-- `E^m(g)` intertwines a dot on an inner strand. -/
theorem liftMap_xE_of_lt {M U : C} {i a : ℕ} (ha : a < i) (g : M ⟶ (Epow E i).obj U) :
    ∀ m, liftMap g m ≫ (D.xE (i + m) a).app U = liftMap (g ≫ (D.xE i a).app U) m
  | 0 => rfl
  | m + 1 => by
    rw [show D.xE (i + (m + 1)) a = sR (i + m) (D.xE (i + m) a) from
      D.xE_succ_of_lt (n := i + m) (by omega), liftMap_succ, liftMap_succ, ← liftMap_xE_of_lt ha g m,
      Functor.map_comp]
    rfl

/-- `E^m(g)` intertwines a crossing of inner strands. -/
theorem liftMap_τE_of_lt {M U : C} {i j : ℕ} (hj : j + 1 < i) (g : M ⟶ (Epow E i).obj U) :
    ∀ m, liftMap g m ≫ (D.τE (i + m) j).app U = liftMap (g ≫ (D.τE i j).app U) m
  | 0 => rfl
  | m + 1 => by
    rw [show D.τE (i + (m + 1)) j = sR (i + m) (D.τE (i + m) j) from
      D.τE_succ_of_lt (n := i + m) (by omega), liftMap_succ, liftMap_succ, ← liftMap_τE_of_lt hj g m,
      Functor.map_comp]
    rfl

/-- `E^m(g)` intertwines a dot on an outer strand. -/
theorem liftMap_xE_outer {M U : C} {i : ℕ} (g : M ⟶ (Epow E i).obj U) :
    ∀ m c, c < m → liftMap g m ≫ (D.xE (i + m) (i + c)).app U =
      (D.xE m c).app M ≫ liftMap g m
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, c, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · rw [show D.xE (i + (m + 1)) (i + c) = sR (i + m) (D.xE (i + m) (i + c)) from
        D.xE_succ_of_lt (n := i + m) (by omega), D.xE_succ_of_lt h, liftMap_succ]
      change E.map _ ≫ E.map _ = E.map _ ≫ E.map _
      rw [← Functor.map_comp, ← Functor.map_comp, liftMap_xE_outer g m c h]
    · rw [show D.xE (i + (c + 1)) (i + c) = sL (i + c) D.X from D.xE_succ_self _,
        D.xE_succ_self, liftMap_succ]
      exact D.X.naturality (liftMap g c)

/-- `α' ∈ End(E^{i+m})` restricts to `α ∈ End(Eⁱ)` along `E^m(-)` at `U`. -/
def Lifts (U : C) (i m : ℕ) (α' : End (Epow E (i + m))) (α : End (Epow E i)) : Prop :=
  ∀ (M : C) (g : M ⟶ (Epow E i).obj U), liftMap g m ≫ α'.app U = liftMap (g ≫ α.app U) m

omit [Preadditive C] in
theorem lifts_one (U : C) (i m : ℕ) : Lifts (E := E) U i m 1 1 := fun M g => by
  change liftMap g m ≫ 𝟙 _ = liftMap (g ≫ 𝟙 _) m
  simp

omit [Preadditive C] in
theorem Lifts.mul {U : C} {i m : ℕ} {α' β' : End (Epow E (i + m))} {α β : End (Epow E i)}
    (h : Lifts U i m α' α) (h' : Lifts U i m β' β) : Lifts U i m (α' * β') (α * β) :=
  fun M g => by
    change liftMap g m ≫ β'.app U ≫ α'.app U = liftMap (g ≫ β.app U ≫ α.app U) m
    rw [← Category.assoc, h', h, Category.assoc]

theorem lifts_xE {U : C} {i a : ℕ} (ha : a < i) (m : ℕ) :
    Lifts U i m (D.xE (i + m) a) (D.xE i a) := fun _ g => D.liftMap_xE_of_lt ha g m

theorem lifts_τE {U : C} {i j : ℕ} (hj : j + 1 < i) (m : ℕ) :
    Lifts U i m (D.τE (i + m) j) (D.τE i j) := fun _ g => D.liftMap_τE_of_lt hj g m

/-! ### The idempotent of `NH_i` inside `NH_{i+m}` -/

section Gamma

variable [E.Additive] {k : Type*} [Field k] [Linear k C]

open NilHecke MvPolynomial

/-- Multiplication by polynomials, as an algebra map into `NH_n`. -/
noncomputable def polyNH (k : Type*) [Field k] (n : ℕ) :
    MvPolynomial (Fin n) k →ₐ[k] nilHecke k n :=
  (mulPoly k n).codRestrict (nilHecke k n) mulPoly_mem

theorem lifts_polyNH_xDelta (U : C) (i m : ℕ) :
    Lifts U i m (D.γ (k := k) (i + m) (polyNH k (i + m) (xDelta i)))
      (D.γ (k := k) i (polyNH k i (xDelta i))) := by
  let P : MvPolynomial (Fin i) k → Prop := fun q =>
    Lifts U i m (D.γ (k := k) (i + m)
      (polyNH k (i + m) (rename (Fin.castLE (Nat.le_add_right i m)) q)))
      (D.γ (k := k) i (polyNH k i q))
  have hmul : ∀ q r, P q → P r → P (q * r) := fun q r hq hr => by
    simp only [P, map_mul]
    exact hq.mul hr
  have hone : P 1 := by
    simp only [P, map_one]
    exact lifts_one U i m
  have hX : ∀ a : Fin i, P (MvPolynomial.X a) := fun a => by
    simp only [P, rename_X]
    have h1 : polyNH k (i + m) (MvPolynomial.X (Fin.castLE (Nat.le_add_right i m) a)) =
        ⟨mulX k (i + m) (Fin.castLE (Nat.le_add_right i m) a), mulX_mem _⟩ := rfl
    have h2 : polyNH k i (MvPolynomial.X a) = ⟨mulX k i a, mulX_mem a⟩ := rfl
    rw [h1, h2, D.γ_mulX, D.γ_mulX]
    exact D.lifts_xE a.isLt m
  have hpow : ∀ (a : Fin i) (e : ℕ), P (MvPolynomial.X a ^ e) := fun a e => by
    induction e with
    | zero => rw [pow_zero]; exact hone
    | succ e ih => rw [pow_succ]; exact hmul _ _ ih (hX a)
  have hP : P (∏ a : Fin i, MvPolynomial.X a ^ (i - 1 - a)) :=
    Finset.prod_induction _ P hmul hone fun a _ => hpow a _
  simp only [P] at hP
  rw [← xDelta_eq_rename (Nat.le_add_right i m)] at hP
  exact hP

theorem lifts_ddw (U : C) {i : ℕ} (m : ℕ) :
    ∀ ρ : List ℕ, (∀ j ∈ ρ, j + 1 < i) →
      Lifts U i m (D.γ (k := k) (i + m) ⟨ddw ρ, ddw_mem ρ⟩) (D.γ (k := k) i ⟨ddw ρ, ddw_mem ρ⟩)
  | [], _ => by
    have h1 : ∀ n, (⟨ddw [], ddw_mem []⟩ : nilHecke k n) = 1 := fun n => Subtype.ext ddw_nil
    rw [h1, h1, map_one, map_one]
    exact lifts_one U i m
  | j :: ρ, h => by
    have h1 : ∀ n, (⟨ddw (j :: ρ), ddw_mem _⟩ : nilHecke k n) =
        ⟨dd k n j, dd_mem j⟩ * ⟨ddw ρ, ddw_mem ρ⟩ := fun n => Subtype.ext (ddw_cons j ρ)
    rw [h1, h1, map_mul, map_mul, D.γ_dd, D.γ_dd]
    exact (D.lifts_τE (h j (by simp)) m).mul
      (lifts_ddw U m ρ fun l hl => h l (by simp [hl]))

/-- The idempotent `e_i ∈ NH_i ⊆ NH_{i+m}` restricts to `e_i ∈ NH_i` along `E^m(-)`. -/
theorem lifts_idemNHAt (U : C) (i m : ℕ) :
    Lifts U i m (D.γ (k := k) (i + m) (idemNHAt k (i + m) i))
      (D.γ (k := k) i ⟨idemNH k i, idemNH_mem⟩) := by
  have h1 : idemNHAt k (i + m) i = polyNH k (i + m) (xDelta i) * ⟨ddw (w0Word i), ddw_mem _⟩ :=
    rfl
  have h2 : (⟨idemNH k i, idemNH_mem⟩ : nilHecke k i) =
      polyNH k i (xDelta i) * ⟨ddw (w0Word i), ddw_mem _⟩ := rfl
  rw [h1, h2, map_mul, map_mul]
  exact (D.lifts_polyNH_xDelta U i m).mul
    (D.lifts_ddw U m _ fun j hj => lt_of_mem_w0Word hj)

end Gamma

end NilHeckeData

end Categorification.Sl2
