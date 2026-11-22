/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.Examples.NilHecke
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The nilHecke action on powers of an endofunctor

Chuang and Rouquier (*Derived equivalences for symmetric groups and `sl₂`-categorification*,
arXiv:math/0407205v2, §5.2.1) let an endofunctor `E` carry endomorphisms `X ∈ End(E)` and
`T ∈ End(E²)` satisfying the defining relations of the (degenerate) affine Hecke algebra, and
obtain an action of that algebra on `Eⁿ`. In the nilHecke version used for `𝔰𝔩₂`
2-representations (Rouquier; Khovanov–Lauda), `X` and `T` satisfy the nilHecke relations and
`Eⁿ` carries an action of the nilHecke algebra `NH_n`. This file constructs that action.

`Eⁿ` is `Epow E n`, with `Epow E (n + 1) = Epow E n ⋙ E`: strand `0` is the innermost copy of
`E`. Strand `a < n` of `Eⁿ⁺¹` carries `x_a ▷ E`, the new strand `n` carries `Eⁿ ◁ X`; the
crossing `τ_j` of strands `j, j + 1` is `τ_j ▷ E` for `j + 1 < n` and `Eⁿ⁻¹ ◁ T` for `j = n - 1`.

## Main definitions

* `Sl2.NilHeckeData E`: `X : E ⟶ E` and `T : E ⋙ E ⟶ E ⋙ E` with `T² = 0`, the braid relation
  and the two nilHecke commutation relations.
* `Sl2.Epow E n`, `Sl2.NilHeckeData.xE`, `Sl2.NilHeckeData.τE`.
* `Sl2.NilHeckeData.isNilHeckeFamily`: the `xE n a`, `τE n j` satisfy the relations of `NH_n`.
* `Sl2.NilHeckeData.γ`: the resulting algebra map `NH_n → End(Eⁿ)`.
-/

namespace Categorification.Sl2

open CategoryTheory CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C]

/-- The powers `Eⁿ` of an endofunctor, with `E⁰ = 𝟭` and `Eⁿ⁺¹ = Eⁿ ⋙ E`. -/
def Epow (E : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => Epow E n ⋙ E

@[simp] theorem Epow_zero (E : C ⥤ C) : Epow E 0 = 𝟭 C := rfl

theorem Epow_succ (E : C ⥤ C) (n : ℕ) : Epow E (n + 1) = Epow E n ⋙ E := rfl

/-! ### Whiskering as ring maps -/

section Whisker

/-- Right whiskering of an endomorphism, as an element of `End (F ⋙ E)`. -/
def wR {F : C ⥤ C} (a : End F) (E : C ⥤ C) : End (F ⋙ E) := whiskerRight a E

/-- Left whiskering of an endomorphism, as an element of `End (F ⋙ G)`. -/
def wL (F : C ⥤ C) {G : C ⥤ C} (b : End G) : End (F ⋙ G) := whiskerLeft F b

/-- Left whiskering by `F` of an endomorphism of `G ⋙ H`, as an element of
`End ((F ⋙ G) ⋙ H)`. -/
def wL₂ (F : C ⥤ C) {G H : C ⥤ C} (b : End (G ⋙ H)) : End ((F ⋙ G) ⋙ H) := whiskerLeft F b

end Whisker

/-! ### Whiskering into powers -/

section Pow

variable {E : C ⥤ C}

/-- `a ↦ a ▷ E : End(Eⁿ) → End(Eⁿ⁺¹)`. -/
def sR (n : ℕ) (a : End (Epow E n)) : End (Epow E (n + 1)) := whiskerRight a E

/-- `a ↦ a ▷ E² : End(Eⁿ) → End(Eⁿ⁺²)`. -/
def sR₂ (n : ℕ) (a : End (Epow E n)) : End (Epow E (n + 2)) := whiskerRight a (E ⋙ E)

/-- `b ↦ Eⁿ ◁ b : End(E) → End(Eⁿ⁺¹)`. -/
def sL (n : ℕ) (b : End E) : End (Epow E (n + 1)) := whiskerLeft (Epow E n) b

/-- `b ↦ Eⁿ ◁ b : End(E²) → End(Eⁿ⁺²)`. -/
def sL₂ (n : ℕ) (b : End (E ⋙ E)) : End (Epow E (n + 2)) := whiskerLeft (Epow E n) b

/-- `b ↦ Eⁿ ◁ b : End(E³) → End(Eⁿ⁺³)`. -/
def sL₃ (n : ℕ) (b : End ((E ⋙ E) ⋙ E)) : End (Epow E (n + 3)) := whiskerLeft (Epow E n) b

theorem sR_mul (n : ℕ) (a b : End (Epow E n)) : sR n (a * b) = sR n a * sR n b :=
  whiskerRight_comp b a E

theorem sR_one (n : ℕ) : sR n (1 : End (Epow E n)) = 1 := whiskerRight_id' E

theorem sL₂_mul (n : ℕ) (a b : End (E ⋙ E)) : sL₂ n (a * b) = sL₂ n a * sL₂ n b :=
  whiskerLeft_comp _ b a

theorem sL₂_one (n : ℕ) : sL₂ n (1 : End (E ⋙ E)) = 1 := whiskerLeft_id' _

theorem sL₃_mul (n : ℕ) (a b : End ((E ⋙ E) ⋙ E)) : sL₃ n (a * b) = sL₃ n a * sL₃ n b :=
  whiskerLeft_comp _ b a

theorem sR_mul_sL (n : ℕ) (a : End (Epow E n)) (b : End E) : sR n a * sL n b = sL n b * sR n a := by
  simp only [sR, sL]
  exact whiskerLeft_comp_whiskerRight a b

theorem sR₂_mul_sL₂ (n : ℕ) (a : End (Epow E n)) (b : End (E ⋙ E)) :
    sR₂ n a * sL₂ n b = sL₂ n b * sR₂ n a := by
  simp only [sR₂, sL₂]
  exact whiskerLeft_comp_whiskerRight a b

theorem sR_sR (n : ℕ) (a : End (Epow E n)) : sR (n + 1) (sR n a) = sR₂ n a := rfl

theorem sR_sL (n : ℕ) (b : End E) : sR (n + 1) (sL n b) = sL₂ n (wR b E) := rfl

theorem sL_succ (n : ℕ) (b : End E) : sL (n + 1) b = sL₂ n (wL E b) := rfl

theorem sL₂_succ (n : ℕ) (b : End (E ⋙ E)) : sL₂ (n + 1) b = sL₃ n (wL₂ E b) := rfl

theorem sR_sL₂ (n : ℕ) (b : End (E ⋙ E)) : sR (n + 2) (sL₂ n b) = sL₃ n (wR b E) := rfl

section Additive

variable [Preadditive C]

theorem sL₂_sub (n : ℕ) (a b : End (E ⋙ E)) : sL₂ n (a - b) = sL₂ n a - sL₂ n b := by
  refine NatTrans.ext (funext fun M => ?_)
  change (a - b).app ((Epow E n).obj M) = (sL₂ n a - sL₂ n b).app M
  rw [NatTrans.app_sub, NatTrans.app_sub]; rfl

theorem sL₂_zero (n : ℕ) : sL₂ n (0 : End (E ⋙ E)) = 0 := by
  refine NatTrans.ext (funext fun M => ?_)
  exact NatTrans.app_zero ((Epow E n).obj M)

theorem sR_sub [E.Additive] (n : ℕ) (a b : End (Epow E n)) : sR n (a - b) = sR n a - sR n b := by
  refine NatTrans.ext (funext fun M => ?_)
  change E.map ((a - b).app M) = (sR n a - sR n b).app M
  rw [NatTrans.app_sub, NatTrans.app_sub, E.map_sub]; rfl

theorem sR_zero [E.Additive] (n : ℕ) : sR n (0 : End (Epow E n)) = 0 := by
  refine NatTrans.ext (funext fun M => ?_)
  change E.map ((0 : End (Epow E n)).app M) = (0 : End (Epow E (n + 1))).app M
  rw [NatTrans.app_zero, NatTrans.app_zero, E.map_zero]; rfl

end Additive

end Pow

/-! ### NilHecke data -/

variable [Preadditive C]

/-- Endomorphisms `X` of `E` and `T` of `E²` satisfying the nilHecke relations (Rouquier;
Khovanov–Lauda; the nilHecke form of Chuang–Rouquier §5.2.1). Products are those of the
endomorphism rings (`End.mul_def`: `a * b = b ≫ a`). With `x₀ = X ▷ E` (inner strand) and
`x₁ = E ◁ X`, the relations are `T² = 0`, the braid relation on `E³`, `x₀ T - T x₁ = 1` and
`T x₀ - x₁ T = 1`. -/
structure NilHeckeData (E : C ⥤ C) where
  /-- The dot. -/
  X : End E
  /-- The crossing. -/
  T : End (E ⋙ E)
  T_mul_T : T * T = 0
  braid : wR T E * wL₂ E T * wR T E = wL₂ E T * wR T E * wL₂ E T
  x_T_sub : wR X E * T - T * wL E X = 1
  T_x_sub : T * wR X E - wL E X * T = 1

namespace NilHeckeData

variable {E : C ⥤ C} (D : NilHeckeData E)

/-- The dot on strand `a` of `Eⁿ` (zero if `a ≥ n`). -/
def xE : (n : ℕ) → ℕ → End (Epow E n)
  | 0, _ => 0
  | n + 1, a => if a < n then sR n (xE n a) else if a = n then sL n D.X else 0

/-- The crossing of strands `j, j + 1` of `Eⁿ` (zero if `j + 1 ≥ n`). -/
def τE : (n : ℕ) → ℕ → End (Epow E n)
  | 0, _ => 0
  | 1, _ => 0
  | n + 2, j => if j < n then sR (n + 1) (τE (n + 1) j) else if j = n then sL₂ n D.T else 0

theorem xE_zero (a : ℕ) : D.xE 0 a = 0 := rfl

theorem xE_succ_of_lt {n a : ℕ} (h : a < n) : D.xE (n + 1) a = sR n (D.xE n a) := by
  simp [xE, h]

theorem xE_succ_self (n : ℕ) : D.xE (n + 1) n = sL n D.X := by
  simp [xE]

theorem xE_of_le {n a : ℕ} (h : n ≤ a) : D.xE n a = 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [xE, show ¬ a < n by omega, show a ≠ n by omega]

theorem τE_succ_succ_of_lt {n j : ℕ} (h : j < n) :
    D.τE (n + 2) j = sR (n + 1) (D.τE (n + 1) j) := by
  simp [τE, h]

theorem τE_succ_succ_self (n : ℕ) : D.τE (n + 2) n = sL₂ n D.T := by
  simp [τE]

theorem τE_of_le {n j : ℕ} (h : n ≤ j + 1) : D.τE n j = 0 := by
  match n, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, h => simp [τE, show ¬ j < n by omega, show j ≠ n by omega]

theorem xE_succ_succ_penult (n : ℕ) : D.xE (n + 2) n = sL₂ n (wR D.X E) := by
  rw [xE_succ_of_lt D (by omega), xE_succ_self, sR_sL]

theorem xE_succ_succ_last (n : ℕ) : D.xE (n + 2) (n + 1) = sL₂ n (wL E D.X) := by
  rw [xE_succ_self, sL_succ]

theorem xE_succ_succ_of_lt {n a : ℕ} (h : a < n) : D.xE (n + 2) a = sR₂ n (D.xE n a) := by
  rw [xE_succ_of_lt D (by omega), xE_succ_of_lt D h, sR_sR]

theorem τE_succ_of_lt {n j : ℕ} (h : j + 1 < n) : D.τE (n + 1) j = sR n (D.τE n j) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact D.τE_succ_succ_of_lt (by omega)

theorem τE_succ_succ_of_lt' {n j : ℕ} (h : j + 1 < n) : D.τE (n + 2) j = sR₂ n (D.τE n j) := by
  rw [D.τE_succ_succ_of_lt (by omega), D.τE_succ_of_lt h, sR_sR]

/-! ### The nilHecke relations -/

theorem xE_comm (n a b : ℕ) : D.xE n a * D.xE n b = D.xE n b * D.xE n a := by
  induction n generalizing a b with
  | zero => simp [xE_zero]
  | succ n ih =>
    have key : ∀ a, a < n →
        D.xE (n + 1) a * D.xE (n + 1) n = D.xE (n + 1) n * D.xE (n + 1) a := by
      intro a ha
      rw [D.xE_succ_of_lt ha, D.xE_succ_self]
      exact sR_mul_sL _ _ _
    rcases lt_trichotomy a n with ha | rfl | ha
    · rcases lt_trichotomy b n with hb | rfl | hb
      · rw [D.xE_succ_of_lt ha, D.xE_succ_of_lt hb, ← sR_mul, ← sR_mul, ih]
      · exact key a ha
      · simp [D.xE_of_le (show n + 1 ≤ b by omega)]
    · rcases lt_trichotomy b a with hb | rfl | hb
      · exact (key b hb).symm
      · rfl
      · simp [D.xE_of_le (show a + 1 ≤ b by omega)]
    · simp [D.xE_of_le (show n + 1 ≤ a by omega)]

theorem τE_xE_comm (n j a : ℕ) (h₁ : a ≠ j) (h₂ : a ≠ j + 1) :
    D.τE n j * D.xE n a = D.xE n a * D.τE n j := by
  induction n generalizing j a with
  | zero => simp [τE, xE_zero]
  | succ m ih =>
    match m, ih with
    | 0, _ => simp [τE]
    | n + 1, ih =>
      rcases lt_trichotomy j n with hj | rfl | hj
      · rw [D.τE_succ_succ_of_lt hj]
        rcases lt_trichotomy a (n + 1) with ha | rfl | ha
        · rw [D.xE_succ_of_lt ha, ← sR_mul, ← sR_mul, ih j a h₁ h₂]
        · rw [D.xE_succ_self]
          exact sR_mul_sL _ _ _
        · simp [D.xE_of_le (show n + 2 ≤ a by omega)]
      · rw [D.τE_succ_succ_self]
        rcases lt_trichotomy a j with ha | rfl | ha
        · rw [D.xE_succ_succ_of_lt ha]
          exact (sR₂_mul_sL₂ _ _ _).symm
        · exact absurd rfl h₁
        · rw [D.xE_of_le (show j + 2 ≤ a by omega)]; simp
      · simp [D.τE_of_le (show n + 2 ≤ j + 1 by omega)]

theorem τE_comm (n j l : ℕ) (h : j + 1 < l) :
    D.τE n j * D.τE n l = D.τE n l * D.τE n j := by
  induction n generalizing j l with
  | zero => simp [τE]
  | succ m ih =>
    match m, ih with
    | 0, _ => simp [τE]
    | n + 1, ih =>
      rcases lt_trichotomy l n with hl | rfl | hl
      · rw [D.τE_succ_succ_of_lt hl, D.τE_succ_succ_of_lt (show j < n by omega),
          ← sR_mul, ← sR_mul, ih j l h]
      · rw [D.τE_succ_succ_self, D.τE_succ_succ_of_lt' h]
        exact sR₂_mul_sL₂ _ _ _
      · simp [D.τE_of_le (show n + 2 ≤ l + 1 by omega)]

variable [E.Additive]

theorem τE_mul_self (n j : ℕ) : D.τE n j * D.τE n j = 0 := by
  induction n generalizing j with
  | zero => exact zero_mul _
  | succ m ih =>
    match m, ih with
    | 0, _ => simp [τE]
    | n + 1, ih =>
      rcases lt_trichotomy j n with hj | rfl | hj
      · rw [D.τE_succ_succ_of_lt hj, ← sR_mul, ih, sR_zero]
      · rw [D.τE_succ_succ_self, ← sL₂_mul, D.T_mul_T, sL₂_zero]
      · simp [D.τE_of_le (show n + 2 ≤ j + 1 by omega)]

omit [E.Additive] in
theorem τE_braid (n j : ℕ) :
    D.τE n j * D.τE n (j + 1) * D.τE n j = D.τE n (j + 1) * D.τE n j * D.τE n (j + 1) := by
  induction n generalizing j with
  | zero => simp [τE]
  | succ m ih =>
    match m, ih with
    | 0, _ => simp [τE]
    | n + 1, ih =>
      rcases lt_trichotomy (j + 1) n with hj | hj | hj
      · rw [D.τE_succ_succ_of_lt hj, D.τE_succ_succ_of_lt (show j < n by omega),
          ← sR_mul, ← sR_mul, ← sR_mul, ← sR_mul, ih]
      · subst hj
        rw [D.τE_succ_succ_self, D.τE_succ_succ_of_lt (show j < j + 1 by omega),
          D.τE_succ_succ_self, sL₂_succ, sR_sL₂, ← sL₃_mul, ← sL₃_mul, ← sL₃_mul,
          ← sL₃_mul, D.braid]
      · simp [D.τE_of_le (show n + 2 ≤ j + 1 + 1 by omega)]

theorem xE_τE_sub (n j : ℕ) (h : j + 1 < n) :
    D.xE n j * D.τE n j - D.τE n j * D.xE n (j + 1) = 1 := by
  induction n generalizing j with
  | zero => omega
  | succ m ih =>
    match m, ih with
    | 0, _ => omega
    | n + 1, ih =>
      rcases lt_trichotomy j n with hj | rfl | hj
      · rw [D.τE_succ_succ_of_lt hj, D.xE_succ_of_lt (show j < n + 1 by omega),
          D.xE_succ_of_lt (show j + 1 < n + 1 by omega), ← sR_mul, ← sR_mul, ← sR_sub,
          ih j (by omega), sR_one]
      · rw [D.τE_succ_succ_self, xE_succ_succ_penult, xE_succ_succ_last, ← sL₂_mul, ← sL₂_mul,
          ← sL₂_sub, D.x_T_sub, sL₂_one]
      · omega

theorem τE_xE_sub (n j : ℕ) (h : j + 1 < n) :
    D.τE n j * D.xE n j - D.xE n (j + 1) * D.τE n j = 1 := by
  induction n generalizing j with
  | zero => omega
  | succ m ih =>
    match m, ih with
    | 0, _ => omega
    | n + 1, ih =>
      rcases lt_trichotomy j n with hj | rfl | hj
      · rw [D.τE_succ_succ_of_lt hj, D.xE_succ_of_lt (show j < n + 1 by omega),
          D.xE_succ_of_lt (show j + 1 < n + 1 by omega), ← sR_mul, ← sR_mul, ← sR_sub,
          ih j (by omega), sR_one]
      · rw [D.τE_succ_succ_self, xE_succ_succ_penult, xE_succ_succ_last, ← sL₂_mul, ← sL₂_mul,
          ← sL₂_sub, D.T_x_sub, sL₂_one]
      · omega

/-! ### The action of `NH_n` -/


/-- The dots and crossings on `Eⁿ` satisfy the defining relations of `NH_n`. -/
theorem isNilHeckeFamily (n : ℕ) :
    KLR.NilHecke.IsNilHeckeFamily (B := End (Epow E n)) n (fun a => D.xE n a.val)
      (D.τE n) where
  x_comm a b := D.xE_comm n a b
  d_x_comm j a h₁ h₂ := D.τE_xE_comm n j a h₁ h₂
  d_comm j l h := D.τE_comm n j l h
  d_sq j := D.τE_mul_self n j
  braid j := D.τE_braid n j
  x_d_sub j h := D.xE_τE_sub n j h
  d_x_sub j h := D.τE_xE_sub n j h
  d_zero _ h := D.τE_of_le h

variable {k : Type*} [CommRing k] [IsDomain k] [Linear k C]

/-- **The nilHecke action on `Eⁿ`** (the nilHecke form of Chuang–Rouquier §5.2.1): the algebra
map `NH_n → End(Eⁿ)` sending `x_a` to the dot on strand `a` and `∂_j` to the crossing of strands
`j, j + 1`. -/
noncomputable def γ (n : ℕ) : NilHecke.nilHecke k n →ₐ[k] End (Epow E n) :=
  KLR.NilHecke.lift (D.isNilHeckeFamily n)

theorem γ_mulX (n : ℕ) (a : Fin n) :
    γ (k := k) D n ⟨NilHecke.mulX k n a, NilHecke.mulX_mem a⟩ = D.xE n a :=
  KLR.NilHecke.lift_mulX _ a

theorem γ_dd (n j : ℕ) : γ (k := k) D n ⟨NilHecke.dd k n j, NilHecke.dd_mem j⟩ = D.τE n j :=
  KLR.NilHecke.lift_dd _ j

end NilHeckeData

end Categorification.Sl2
