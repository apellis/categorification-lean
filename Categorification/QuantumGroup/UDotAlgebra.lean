/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotBlock

/-!
# `U̇` as an idempotented algebra

Khovanov–Lauda III, arXiv:0807.3250v1, §2.1.3: `U̇` is obtained from `U` by adjoining
orthogonal idempotents `1_λ`, `λ ∈ X`, and `U̇ = ⊕_{λ, λ'} 1_{λ'} U̇ 1_λ`.

We realise `U̇ = ⊕_λ U̇ 1_λ` (`UDot.UD RD q`) as the direct sum of the blocks
`U̇ 1_λ = UDot.U1 RD q λ` of `Categorification.QuantumGroup.UDotBlock`, with the product
`(x 1_μ)(y 1_λ) = x · 1_μ y 1_λ` (`UDot.mulU`): for signed sequences,
`(E_s 1_μ)(E_t 1_λ) = E_{st} 1_λ` if `μ = λ + t_X` and `0` otherwise (KL III eq. (2.40)).

## Main results

* `UDot.mulU_assoc`, `UDot.mul_assoc'` — associativity;
* `UDot.instNonUnitalRing`, `UDot.instIsScalarTower`, `UDot.instSMulCommClass` — `U̇` is a
  non-unital associative `K`-algebra;
* `UDot.one_mul_one` — the `1_λ` are orthogonal idempotents (KL III eq. (2.2));
* `UDot.one_mul_one_ew` — `1_{λ'} E_t 1_λ = δ_{λ', λ + t_X} E_t 1_λ` (KL III eq. (2.3));
* `UDot.idem_eq` — `1_{λ₁} x 1_{λ₂}` is the `oneL`-projection of the `λ₂` component of `x`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K]
variable {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (q : Kˣ)

/-! ### The product of blocks -/

/-- `P_μ = 1_μ ·` on `'U 1_λ`. -/
def projF (lam μ : X) : Free K I →ₗ[K] Free K I := diagX RD fun ν => if lam + ν = μ then 1 else 0

theorem projF_ew (lam μ : X) (t : List (Bool × I)) :
    projF RD lam μ (ew t : Free K I) = if lam + RD.wX t = μ then ew t else 0 := by
  rw [projF, diagX_ew]; split_ifs <;> simp

theorem mul_mem_Lrel_left (ℓ : I → ℤ) (x : Free K I) {z : Free K I} (hz : z ∈ Lrel C q ℓ) :
    x * z ∈ Lrel C q ℓ := by
  induction x using Free.induction with
  | zero => simp
  | add x y hx hy => rw [add_mul]; exact add_mem hx hy
  | smul_ew w r =>
    rw [smul_mul_assoc]
    refine Submodule.smul_mem _ _ ?_
    induction w with
    | nil => simpa using hz
    | cons l w ih =>
      rw [ew_cons, mul_assoc]
      exact mulLeft_Lrel q ℓ l ih

theorem commRel_shift (mu lam : X) (b t : List (Bool × I)) (h : lam + RD.wX t = mu) (i j : I) :
    commRel C q (RD.ellOf mu) b i j = (commRel C q (RD.ellOf lam) (b ++ t) i j : Free K I) := by
  simp only [commRel, RD.wl_ellOf, RD.wX_append, ← h]
  congr 4
  abel_nf

theorem mul_ew_mem_Lrel (mu lam : X) {x : Free K I} (hx : x ∈ Lrel C q (RD.ellOf mu))
    (t : List (Bool × I)) (h : lam + RD.wX t = mu) : x * ew t ∈ Lrel C q (RD.ellOf lam) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    refine Submodule.subset_span ?_
    rcases hz with ⟨a, b, i, j, rfl⟩ | ⟨a, b, i, j, hij, rfl | rfl⟩
    · exact Or.inl ⟨a, b ++ t, i, j, by rw [commRel_shift RD q mu lam b t h, ew_append, mul_assoc]⟩
    · exact Or.inr ⟨a, b ++ t, i, j, hij, Or.inl (by rw [ew_append, mul_assoc])⟩
    · exact Or.inr ⟨a, b ++ t, i, j, hij, Or.inr (by rw [ew_append, mul_assoc])⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

theorem mul_projF_mem_Lrel (mu lam : X) {x : Free K I} (hx : x ∈ Lrel C q (RD.ellOf mu))
    (y : Free K I) : x * projF RD lam mu y ∈ Lrel C q (RD.ellOf lam) := by
  induction y using Free.induction with
  | zero => simp
  | add y y' hy hy' => rw [map_add, mul_add]; exact add_mem hy hy'
  | smul_ew t r =>
    rw [map_smul, mul_smul_comm, projF_ew]
    refine Submodule.smul_mem _ _ ?_
    split_ifs with h
    · exact mul_ew_mem_Lrel RD q mu lam hx t h
    · simp

/-- The product `U̇ 1_μ × U̇ 1_λ → U̇ 1_λ`, `(x, y) ↦ x · 1_μ y`. -/
def mulU (mu lam : X) : U1 RD q mu →ₗ[K] U1 RD q lam →ₗ[K] U1 RD q lam :=
  (Lrel C q (RD.ellOf mu)).liftQ
    ((Lrel C q (RD.ellOf lam)).liftQ
      ((LinearMap.mul K (Free K I)).compl₂ (projF RD lam mu) |>.compr₂ (mk RD q lam)).flip
      (fun y hy => LinearMap.ext fun x => by
        simp only [LinearMap.flip_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
          LinearMap.mul_apply', LinearMap.zero_apply]
        exact mk_eq_zero RD q lam (mul_mem_Lrel_left q _ x (diagX_Lrel RD q lam _ hy)))).flip
    (fun x hx => LinearMap.ext fun y => by
      obtain ⟨y, rfl⟩ := mk_surjective RD q lam y
      exact mk_eq_zero RD q lam (mul_projF_mem_Lrel RD q mu lam hx y))

theorem mulU_mk (mu lam : X) (x y : Free K I) :
    mulU RD q mu lam (mk RD q mu x) (mk RD q lam y) = mk RD q lam (x * projF RD lam mu y) := rfl

theorem mulU_mk_ew (mu lam : X) (s t : List (Bool × I)) :
    mulU RD q mu lam (mk RD q mu (ew s)) (mk RD q lam (ew t)) =
      if lam + RD.wX t = mu then mk RD q lam (ew (s ++ t)) else 0 := by
  rw [mulU_mk, projF_ew]
  split_ifs <;> simp [ew_append]

theorem projF_mul_projF (nu mu lam : X) (y z : Free K I) :
    projF RD lam nu (y * projF RD lam mu z) = projF RD mu nu y * projF RD lam mu z := by
  induction y using Free.induction with
  | zero => simp
  | add y y' hy hy' => rw [add_mul, map_add, hy, hy', map_add, add_mul]
  | smul_ew s r =>
    rw [smul_mul_assoc, map_smul, map_smul, smul_mul_assoc]
    congr 1
    induction z using Free.induction with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, mul_add, hz, hz']
    | smul_ew t r' =>
      simp only [map_smul, mul_smul_comm, projF_ew]
      congr 1
      by_cases h : lam + RD.wX t = mu
      · simp only [if_pos h]
        rw [← ew_append, projF_ew, RD.wX_append, ← h]
        have e : (lam + (RD.wX s + RD.wX t) = nu) ↔ (lam + RD.wX t + RD.wX s = nu) := by
          constructor <;> intro h' <;> rw [← h'] <;> abel
        by_cases h2 : lam + RD.wX t + RD.wX s = nu
        · simp [h2, e.2 h2, ew_append]
        · simp [h2, mt e.1 h2]
      · simp [h]

/-- Associativity of the product of blocks. -/
theorem mulU_assoc (nu mu lam : X) (x : U1 RD q nu) (y : U1 RD q mu) (z : U1 RD q lam) :
    mulU RD q mu lam (mulU RD q nu mu x y) z = mulU RD q nu lam x (mulU RD q mu lam y z) := by
  obtain ⟨x, rfl⟩ := mk_surjective RD q nu x
  obtain ⟨y, rfl⟩ := mk_surjective RD q mu y
  obtain ⟨z, rfl⟩ := mk_surjective RD q lam z
  rw [mulU_mk, mulU_mk, mulU_mk, mulU_mk, projF_mul_projF, mul_assoc]

/-! ### `U̇ = ⊕_λ U̇ 1_λ` -/

/-- `U̇ = ⊕_{λ ∈ X} U̇ 1_λ` (KL III §2.1.3). -/
abbrev UD := DirectSum X fun lam => U1 RD q lam

/-- The inclusion of the block `U̇ 1_λ` into `U̇`. -/
def ofB (lam : X) : U1 RD q lam →ₗ[K] UD RD q := DirectSum.lof K X (fun lam => U1 RD q lam) lam

/-- The product of `U̇` (a bilinear map). -/
def mulUD : UD RD q →ₗ[K] UD RD q →ₗ[K] UD RD q :=
  DirectSum.toModule K X _ fun mu =>
    ((DFinsupp.lsum K).toLinearMap : (∀ lam, U1 RD q lam →ₗ[K] UD RD q) →ₗ[K] _) ∘ₗ
      LinearMap.pi fun lam => (mulU RD q mu lam).compr₂ (ofB RD q lam)

theorem mulUD_ofB (mu lam : X) (x : U1 RD q mu) (y : U1 RD q lam) :
    mulUD RD q (ofB RD q mu x) (ofB RD q lam y) = ofB RD q lam (mulU RD q mu lam x y) := by
  simp only [mulUD, ofB, DirectSum.toModule_lof, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact DFinsupp.lsum_single K _ lam y

instance instMulUD : Mul (UD RD q) := ⟨fun x y => mulUD RD q x y⟩

theorem mul_def (x y : UD RD q) : x * y = mulUD RD q x y := rfl

theorem ofB_mul_ofB (mu lam : X) (x : U1 RD q mu) (y : U1 RD q lam) :
    ofB RD q mu x * ofB RD q lam y = ofB RD q lam (mulU RD q mu lam x y) := mulUD_ofB RD q _ _ _ _

theorem UD_induction {motive : UD RD q → Prop} (x : UD RD q) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (ofB : ∀ lam (z : U1 RD q lam), motive (ofB RD q lam z)) : motive x :=
  DirectSum.induction_on x zero (fun lam z => ofB lam z) add

theorem mul_assoc' (x y z : UD RD q) : x * y * z = x * (y * z) := by
  induction x using UD_induction with
  | zero => simp [mul_def]
  | add x x' hx hx' => simp only [mul_def, map_add, LinearMap.add_apply] at hx hx' ⊢; rw [hx, hx']
  | ofB nu x =>
    induction y using UD_induction with
    | zero => simp [mul_def]
    | add y y' hy hy' => simp only [mul_def, map_add, LinearMap.add_apply] at hy hy' ⊢; rw [hy, hy']
    | ofB mu y =>
      induction z using UD_induction with
      | zero => simp [mul_def]
      | add z z' hz hz' => simp only [mul_def, map_add, LinearMap.add_apply] at hz hz' ⊢; rw [hz, hz']
      | ofB lam z => rw [ofB_mul_ofB, ofB_mul_ofB, ofB_mul_ofB, ofB_mul_ofB, mulU_assoc]

/-- `U̇` is a non-unital associative ring. -/
instance instNonUnitalRing : NonUnitalRing (UD RD q) where
  __ := (inferInstance : AddCommGroup (UD RD q))
  mul := (· * ·)
  left_distrib x y z := by simp [mul_def]
  right_distrib x y z := by simp [mul_def]
  zero_mul x := by simp [mul_def]
  mul_zero x := by simp [mul_def]
  mul_assoc := mul_assoc' RD q

instance instIsScalarTower : IsScalarTower K (UD RD q) (UD RD q) :=
  ⟨fun r x y => by simp only [smul_eq_mul, mul_def, map_smul, LinearMap.smul_apply]⟩

instance instSMulCommClass : SMulCommClass K (UD RD q) (UD RD q) :=
  ⟨fun r x y => by simp only [smul_eq_mul, mul_def, map_smul]⟩

/-! ### The idempotents `1_λ` -/

/-- The idempotent `1_λ ∈ U̇`. -/
def one (lam : X) : UD RD q := ofB RD q lam (mk RD q lam 1)

/-- The element `E_t 1_λ ∈ U̇` for a signed sequence `t`. -/
def E1 (t : List (Bool × I)) (lam : X) : UD RD q := ofB RD q lam (mk RD q lam (ew t))

theorem one_eq_E1 (lam : X) : one RD q lam = E1 RD q [] lam := rfl

/-- **KL III eq. (2.40)**: `(E_s 1_μ)(E_t 1_λ) = δ_{μ, λ + t_X} E_{st} 1_λ`. -/
theorem E1_mul_E1 (s t : List (Bool × I)) (mu lam : X) :
    E1 RD q s mu * E1 RD q t lam = if lam + RD.wX t = mu then E1 RD q (s ++ t) lam else 0 := by
  rw [E1, E1, ofB_mul_ofB, mulU_mk_ew]
  split_ifs <;> simp [E1]

/-- **KL III eq. (2.2)**: the `1_λ` are orthogonal idempotents. -/
theorem one_mul_one (lam lam' : X) :
    one RD q lam * one RD q lam' = if lam' = lam then one RD q lam else 0 := by
  rw [one_eq_E1, one_eq_E1, E1_mul_E1]
  split_ifs with h h' h'
  · subst h'; rfl
  · exact absurd (by simpa using h) h'
  · exact absurd (by simpa using h') h
  · rfl

/-- **KL III eq. (2.3)**: `1_{λ'} (E_t 1_λ) = δ_{λ', λ + t_X} E_t 1_λ`. -/
theorem one_mul_E1 (t : List (Bool × I)) (lam lam' : X) :
    one RD q lam' * E1 RD q t lam = if lam + RD.wX t = lam' then E1 RD q t lam else 0 := by
  rw [one_eq_E1, E1_mul_E1, List.nil_append]

/-- `(E_t 1_λ) 1_{λ'} = δ_{λ, λ'} E_t 1_λ`. -/
theorem E1_mul_one (t : List (Bool × I)) (lam lam' : X) :
    E1 RD q t lam' * one RD q lam = if lam = lam' then E1 RD q t lam else 0 := by
  rw [one_eq_E1, E1_mul_E1, List.append_nil]
  simp

/-- `E_s E_t 1_λ = (E_s 1_{λ + t_X})(E_t 1_λ)`. -/
theorem E1_append (s t : List (Bool × I)) (lam : X) :
    E1 RD q (s ++ t) lam = E1 RD q s (lam + RD.wX t) * E1 RD q t lam := by
  rw [E1_mul_E1, if_pos rfl]

/-- The elements `E_t 1_λ` span `U̇`. -/
theorem E1_induction {motive : UD RD q → Prop} (x : UD RD q) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul_E1 : ∀ (r : K) t lam, motive (r • E1 RD q t lam)) : motive x := by
  induction x using UD_induction with
  | zero => exact zero
  | add x y hx hy => exact add x y hx hy
  | ofB lam z =>
    obtain ⟨z, rfl⟩ := mk_surjective RD q lam z
    induction z using Free.induction with
    | zero => simpa using zero
    | add x y hx hy => rw [map_add, map_add]; exact add _ _ hx hy
    | smul_ew w r => rw [map_smul, map_smul]; exact smul_E1 r w lam

/-- The component map `U̇ → U̇ 1_λ`. -/
def compB (lam : X) : UD RD q →ₗ[K] U1 RD q lam := DirectSum.component K X _ lam

/-- `1_{λ₁} x 1_{λ₂}`, computed blockwise: the `oneL λ₁`-projection of the `λ₂`-component. -/
def idem (lam1 lam2 : X) : UD RD q →ₗ[K] UD RD q :=
  ofB RD q lam2 ∘ₗ oneL RD q lam2 lam1 ∘ₗ compB RD q lam2

theorem compB_ofB_self (lam : X) (z : U1 RD q lam) : compB RD q lam (ofB RD q lam z) = z :=
  DirectSum.component.lof_self K lam z

theorem compB_ofB_ne {lam lam' : X} (h : lam' ≠ lam) (z : U1 RD q lam') :
    compB RD q lam (ofB RD q lam' z) = 0 := by
  rw [compB, ofB, DirectSum.component.of, dif_neg h]

theorem idem_E1 (lam1 lam2 : X) (t : List (Bool × I)) (lam : X) :
    idem RD q lam1 lam2 (E1 RD q t lam) =
      if lam = lam2 ∧ lam + RD.wX t = lam1 then E1 RD q t lam else 0 := by
  rw [idem, LinearMap.comp_apply, LinearMap.comp_apply, E1]
  by_cases h : lam = lam2
  · subst h
    rw [compB_ofB_self, oneL_mk_ew]
    simp only [true_and]
    split_ifs <;> simp
  · rw [compB_ofB_ne RD q h, map_zero, map_zero, if_neg (fun h' => h h'.1)]

/-- **`1_{λ₁} x 1_{λ₂}` via the algebra structure** equals `idem λ₁ λ₂ x`. -/
theorem idem_eq (lam1 lam2 : X) (x : UD RD q) :
    idem RD q lam1 lam2 x = one RD q lam1 * x * one RD q lam2 := by
  induction x using E1_induction with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, mul_add, add_mul]
  | smul_E1 r t lam =>
    rw [map_smul, idem_E1, mul_smul_comm, smul_mul_assoc, one_mul_E1]
    split_ifs with h1 h2 h2
    · rw [E1_mul_one, if_pos h1.1.symm, h1.1]
    · exact absurd h1.2 h2
    · rw [E1_mul_one, if_neg (fun h => h1 ⟨h.symm, h2⟩)]
    · simp

end UDot

end Categorification.QuantumGroup

end
