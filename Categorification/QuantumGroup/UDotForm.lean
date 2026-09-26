/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotModel

/-!
# The bilinear form on `'U 1_λ`

Khovanov–Lauda III, arXiv:0807.3250v1, §2.1.3, Proposition 2.2, and §2.2 (proof of
Theorem 2.7). We construct the bilinear form `( , )` on the free version `'U 1_λ` of
`U̇ 1_λ` (for a fixed right weight `λ`, with `ℓ = ⟨-, λ⟩`) and prove its main properties;
the passage to `U̇` (Serre relations, quotient) is in `Categorification.QuantumGroup.UDotSerre`
and `Categorification.QuantumGroup.UDotPairing`.

## Conventions

KL III's form on `'f` is `(θ_i, θ_i) = (1 - q_i²)⁻¹` with the twisted multiplication
`(x₁ ⊗ x₂)(x₁' ⊗ x₂') = q^{-|x₂|·|x₁'|} x₁x₁' ⊗ x₂x₂'`; this is the repository's
`PreF.form C.dot v c` for Lusztig's `v = q⁻¹` (`UDot.fF`), with `c` arbitrary here
(KL III's normalisation is `c = lusztigC C.dot q⁻¹`).

The anti-involution `ρ̄ = ψρψ` of KL III §2.1.2 satisfies `ρ̄(E_{εi}) = q_i^{-1} K̃_{-εi} E_{-εi}`,
so on `E_t 1_λ` (left weight `μ = λ + t_X`) left multiplication by `ρ̄(E_{εi})` is
`E_t 1_λ ↦ q_i^{1 - ε⟨i, μ⟩} E_{-εi} E_t 1_λ` (`UDot.rhoE`). Property (iii) of Prop. 2.2,
`(ux, y) = (x, ρ̄(u) y)`, then determines the form from the functional
`φ(y) = (1_λ, y)`, and `φ(F_{c^{rev}} E_b 1_λ) = q^{κ}(b, c)` (KL III eq. (2.25) together with
property (iii)).

## Construction

* `UDot.φ ℓ = ε ∘ NF`, where `NF` is the normal form of `Categorification.QuantumGroup.UDotModel`
  and `ε (c, b) = q^{Kx ℓ |c|} (b, c)`;
* `UDot.B ℓ (E_s 1_λ) (E_t 1_λ) = q^{rcx (wl t) s} φ(E_{ρW(s) t} 1_λ)`, which is
  `φ(ρ̄(E_s 1_λ) E_t 1_λ)`.

## Main results

* `UDot.B_rhoE` — property (iii) in the first argument (for the generators `E_{±i}`);
* `UDot.B_comm_right`, `UDot.B_comm_left` — `B` respects the commutation relations
  (KL III eq. (2.4)) in both arguments;
* `UDot.B_eq_zero_of_not_balanced` — property (ii) (weights);
* `UDot.B_symm` — property (v) (symmetry), via normal ordering (`UDot.normal_induction`,
  as in the proof of KL III Theorem 2.7, Lemmas 2.10–2.12);
* `UDot.B_posF_posF` — property (iv): `(x⁺ 1_λ, x'⁺ 1_λ) = (x, x')`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K] (C : CartanDatum I) (q : Kˣ) (c : I → K)

/-! ### Powers of `q` -/

/-- `qp q e = q^e ∈ K`. -/
def qp (e : ℤ) : K := ((q ^ e : Kˣ) : K)

variable {q} in
theorem qp_add (a b : ℤ) : qp q (a + b) = qp q a * qp q b := by
  rw [qp, zpow_add, Units.val_mul]; rfl

variable {q} in
@[simp] theorem qp_zero : qp q 0 = (1 : K) := by simp [qp]

/-! ### The form on `'f` and the functional `ε` -/

/-- KL III's bilinear form on `'f`: `PreF.form` with Lusztig's `v = q⁻¹` (KL III §2.1.1). -/
def fF : PreF K I →ₗ[K] PreF K I →ₗ[K] K := PreF.form C.dot q⁻¹ c

variable {C q c} in
theorem fF_symm (x y : PreF K I) : fF C q c x y = fF C q c y x := form_symm C.symm x y

/-- `S1 m ν = Σ_{j ∈ ν} (j·j/2) m j`. -/
def S1 (m : I → ℤ) (ν : Multiset I) : ℤ := (ν.map fun j => di C j * m j).sum

/-- `|ν|²/2 = (ν·ν)/2` (an integer). -/
def hsq (ν : Multiset I) : ℤ := wdot C.dot ν ν / 2

/-- The exponent `κ` with `ρ̄(F_{c^{rev}}) 1_λ = q^κ E_c 1_λ`:
`Kx ℓ ν = Σ_{j ∈ ν} (j·j/2)⟨j, λ⟩ + (ν·ν)/2`. -/
def Kx (ℓ : I → ℤ) (ν : Multiset I) : ℤ := S1 C ℓ ν + hsq C ν

variable {C} in
theorem wdot_self_even (ν : Multiset I) : Even (wdot C.dot ν ν) := by
  induction ν using Multiset.induction_on with
  | empty => simp
  | cons a ν ih =>
    rw [wdot_cons_left, wdot_cons_right, wdot_cons_right, wdot_singleton,
      wdot_singleton_comm C.dot C.symm a ν]
    have h1 := C.dot_self_even a
    have : wdot C.dot ν {a} + (wdot C.dot ν {a} + wdot C.dot ν ν) =
        2 * wdot C.dot ν {a} + wdot C.dot ν ν := by ring
    rw [add_assoc, this]
    exact h1.add ((even_two_mul _).add ih)

theorem two_mul_hsq (ν : Multiset I) : 2 * hsq C ν = wdot C.dot ν ν := by
  obtain ⟨k, hk⟩ := wdot_self_even (C := C) ν
  unfold hsq; omega

@[simp] theorem S1_zero (m : I → ℤ) : S1 C m 0 = 0 := by simp [S1]

@[simp] theorem S1_cons (m : I → ℤ) (a : I) (ν : Multiset I) :
    S1 C m (a ::ₘ ν) = di C a * m a + S1 C m ν := by simp [S1]

theorem di_mul_msA (a : I) (μ : Multiset I) : di C a * msA C a μ = wdot C.dot {a} μ := by
  induction μ using Multiset.induction_on with
  | empty => simp
  | cons b μ ihμ => rw [msA_cons, mul_add, ihμ, wdot_cons_right, wdot_singleton, di_mul_A]

theorem S1_add_msA (m : I → ℤ) (ν μ : Multiset I) :
    S1 C (fun k => m k + msA C k μ) ν = S1 C m ν + wdot C.dot ν μ := by
  induction ν using Multiset.induction_on with
  | empty => simp
  | cons a ν ih =>
    rw [S1_cons, S1_cons, ih, wdot_cons_left, mul_add, di_mul_msA]
    ring

theorem S1_sub_msA (m : I → ℤ) (ν μ : Multiset I) :
    S1 C (fun k => m k - msA C k μ) ν = S1 C m ν - wdot C.dot ν μ := by
  have h := S1_add_msA C (fun k => m k - msA C k μ) ν μ
  simp only [sub_add_cancel] at h
  linarith

/-- `ε : M → K`, `ε (c, b) = q^{Kx ℓ |c|} (b, c)`: the value `(1_λ, F_{c^{rev}} E_b 1_λ)`. -/
def ε (ℓ : I → ℤ) : M K I →ₗ[K] K :=
  Finsupp.linearCombination K fun p => qp q (Kx C ℓ (wt p.1)) * fF C q c (word p.2) (word p.1)

variable {C q c}

theorem ε_tm_word (ℓ : I → ℤ) (u w : FreeMonoid I) :
    ε C q c ℓ (tm (word u) (word w)) = qp q (Kx C ℓ (wt u)) * fF C q c (word w) (word u) := by
  rw [tm_word_word, ε, Finsupp.linearCombination_single, one_smul]

theorem ε_tm_of_mem_grade (ℓ : I → ℤ) {ν : Multiset I} {x : PreF K I} (hx : x ∈ grade K ν)
    (w : FreeMonoid I) :
    ε C q c ℓ (tm x (word w)) = qp q (Kx C ℓ ν) * fF C q c (word w) x := by
  refine eqOn_supp ((ε C q c ℓ) ∘ₗ tm.flip (word w))
    ((qp q (Kx C ℓ ν)) • (fF C q c (word w))) ?_ x hx
  intro u hu
  simp only [Set.mem_setOf_eq] at hu
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, LinearMap.smul_apply,
    smul_eq_mul, ε_tm_word, hu]

/-! ### The functional `φ = (1_λ, -)` -/

variable (C q c) in
/-- `φ ℓ y = (1_λ, y)`, computed as `ε (NF y)`. -/
def φ (ℓ : I → ℤ) : Free K I →ₗ[K] K := ε C q c ℓ ∘ₗ NF C q ℓ

theorem φ_apply (ℓ : I → ℤ) (x : Free K I) : φ C q c ℓ x = ε C q c ℓ (NF C q ℓ x) := rfl

/-- `φ` vanishes on `E_w 1_λ` unless `w` has weight zero. -/
theorem φ_eq_zero (ℓ : I → ℤ) {w : List (Bool × I)} (hw : posMS w ≠ negMS w) :
    φ C q c ℓ (ew w) = 0 := by
  rw [φ_apply]
  refine Msupp_induction (motive := fun v => ε C q c ℓ v = 0) (NF_mem_Msupp ℓ w) (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, add_zero])
    (fun r x hx => by beta_reduce at hx ⊢; rw [map_smul, hx, smul_zero]) fun u w' h => ?_
  beta_reduce
  rw [ε_tm_word, fF, form_eq_zero_of_wt_ne, mul_zero]
  intro h'
  rw [h'] at h
  exact hw (add_left_cancel h).symm

theorem φ_comm (ℓ : I → ℤ) (a b : List (Bool × I)) (i j : I) :
    φ C q c ℓ (ew (a ++ (true, i) :: (false, j) :: b)) =
      φ C q c ℓ (ew (a ++ (false, j) :: (true, i) :: b)) +
        if j = i then qbr (qi C q i) (wl C ℓ b i) * φ C q c ℓ (ew (a ++ b)) else 0 := by
  rw [φ_apply, NF_comm, map_add, φ_apply, φ_apply]
  split_ifs <;> simp

theorem φ_negW_posW (ℓ : I → ℤ) (c' b : List I) :
    φ C q c ℓ (ew (negW c' ++ posW b)) =
      qp q (Kx C ℓ c') * fF C q c (word (FreeMonoid.ofList b)) (word (FreeMonoid.ofList c'.reverse)) := by
  rw [φ_apply, NF_negW_posW, ε_tm_word]
  congr 3
  simp [wt]

/-! ### `ρ̄` acting on `'U 1_λ` -/

variable (C q) in
/-- Left multiplication by `ρ̄(E_{εi}) = q_i^{-1} K̃_{-εi} E_{-εi}` on `'U 1_λ`:
`E_t 1_λ ↦ q_i^{1 - ε⟨i, λ + t_X⟩} E_{(-εi) t} 1_λ`. -/
def rhoE (ℓ : I → ℤ) (l : Bool × I) : Free K I →ₗ[K] Free K I :=
  linLift fun t => qp q (di C l.2 * (1 - sgn l.1 * wl C ℓ t.toList l.2)) • ew ((!l.1, l.2) :: t.toList)

theorem rhoE_ew (ℓ : I → ℤ) (l : Bool × I) (t : List (Bool × I)) :
    rhoE C q ℓ l (ew t) = qp q (di C l.2 * (1 - sgn l.1 * wl C ℓ t l.2)) • ew ((!l.1, l.2) :: t) := by
  rw [rhoE, ew, linLift_word, FreeMonoid.toList_ofList]

/-! ### The form `B` -/

variable (C) in
/-- The exponent in `ρ̄(E_s) E_t 1_λ = q^{rcx (wl ℓ t) s} E_{ρW(s) t} 1_λ` (for `ρ̄(E_s)` acting by
left multiplication, `ρ̄(E_{l s}) = ρ̄(E_s) ρ̄(E_l)`). -/
def rcx : (I → ℤ) → List (Bool × I) → ℤ
  | _, [] => 0
  | m, (b, i) :: s => di C i * (1 - sgn b * m i) + rcx (fun k => m k - sgn b * A C k i) s

variable (C q c) in
/-- **The bilinear form on `'U 1_λ`** (KL III Prop. 2.2):
`B (E_s 1_λ) (E_t 1_λ) = q^{rcx (wl t) s} φ(E_{ρW(s) t} 1_λ) = (1_λ, ρ̄(E_s 1_λ) E_t 1_λ)`. -/
def B (ℓ : I → ℤ) : Free K I →ₗ[K] Free K I →ₗ[K] K :=
  linLift fun s => linLift fun t =>
    qp q (rcx C (wl C ℓ t.toList) s.toList) * φ C q c ℓ (ew (ρW s.toList ++ t.toList))

theorem B_ew_ew (ℓ : I → ℤ) (s t : List (Bool × I)) :
    B C q c ℓ (ew s) (ew t) = qp q (rcx C (wl C ℓ t) s) * φ C q c ℓ (ew (ρW s ++ t)) := by
  rw [B, ew, linLift_word, ew, linLift_word, FreeMonoid.toList_ofList, FreeMonoid.toList_ofList]

theorem wl_nil (ℓ : I → ℤ) : wl C ℓ [] = ℓ := by funext i; simp [wl]

theorem B_one_left (ℓ : I → ℤ) (y : Free K I) : B C q c ℓ 1 y = φ C q c ℓ y := by
  have : B C q c ℓ 1 = φ C q c ℓ := by
    refine Free.lhom_ext fun t => ?_
    rw [← ew_nil, B_ew_ew]
    simp [rcx]
  rw [this]

theorem wl_cons_rho (ℓ : I → ℤ) (b : Bool) (i : I) (t : List (Bool × I)) :
    wl C ℓ ((!b, i) :: t) = fun k => wl C ℓ t k - sgn b * A C k i := by
  rw [wl_cons]; funext k; simp; ring

/-- **Property (iii)** of KL III Prop. 2.2 for the generators, in the first argument:
`(E_{εi} x, y) = (x, ρ̄(E_{εi}) y)`. -/
theorem B_rhoE (ℓ : I → ℤ) (l : Bool × I) (s : List (Bool × I)) (y : Free K I) :
    B C q c ℓ (ew (l :: s)) y = B C q c ℓ (ew s) (rhoE C q ℓ l y) := by
  have : B C q c ℓ (ew (l :: s)) = B C q c ℓ (ew s) ∘ₗ rhoE C q ℓ l := by
    refine Free.lhom_ext fun t => ?_
    obtain ⟨b, i⟩ := l
    rw [LinearMap.comp_apply, rhoE_ew, map_smul, B_ew_ew, B_ew_ew, smul_eq_mul, ρW_cons,
      List.append_assoc, List.singleton_append, rcx, wl_cons_rho, qp_add, mul_assoc]
  rw [this, LinearMap.comp_apply]

/-! ### Weights -/

theorem balanced_of_φ_ne_zero (ℓ : I → ℤ) {s t : List (Bool × I)}
    (h : φ C q c ℓ (ew (ρW s ++ t)) ≠ 0) : Balanced s t := by
  by_contra hb
  refine h (φ_eq_zero ℓ fun he => hb ?_)
  simp only [posMS_append, posMS_ρW, negMS_append, negMS_ρW] at he
  unfold Balanced
  rw [← he, add_comm]

/-- **Property (ii)** (weights): `(E_s 1_λ, E_t 1_λ) = 0` unless `s` and `t` have the same
weight in `ℤ[I]` (in particular the same left weight). -/
theorem B_eq_zero_of_not_balanced (ℓ : I → ℤ) {s t : List (Bool × I)} (h : ¬ Balanced s t) :
    B C q c ℓ (ew s) (ew t) = 0 := by
  rw [B_ew_ew]
  by_contra h'
  exact h (balanced_of_φ_ne_zero ℓ (right_ne_zero_of_mul h'))

theorem wl_eq_of_balanced (ℓ : I → ℤ) {s t : List (Bool × I)} (h : Balanced s t) :
    wl C ℓ s = wl C ℓ t := by
  funext i; simp [wl, aS_eq_of_balanced C h]

/-! ### The commutation relations -/

theorem aS_swap (i : I) (a b : List (Bool × I)) (l l' : Bool × I) :
    aS C i (a ++ l :: l' :: b) = aS C i (a ++ l' :: l :: b) := by
  simp; ring

theorem wl_swap (ℓ : I → ℤ) (a b : List (Bool × I)) (l l' : Bool × I) :
    wl C ℓ (a ++ l :: l' :: b) = wl C ℓ (a ++ l' :: l :: b) := by
  funext i; simp only [wl, aS_swap]

theorem wl_cancel (ℓ : I → ℤ) (a b : List (Bool × I)) (i : I) :
    wl C ℓ (a ++ (false, i) :: (true, i) :: b) = wl C ℓ (a ++ b) := by
  funext k; simp [wl]

/-- `B` respects the commutation relations (KL III eq. (2.4)) in the second argument. -/
theorem B_comm_right (ℓ : I → ℤ) (x : Free K I) (a b : List (Bool × I)) (i j : I) :
    B C q c ℓ x (ew (a ++ (true, i) :: (false, j) :: b)) =
      B C q c ℓ x (ew (a ++ (false, j) :: (true, i) :: b)) +
        if j = i then qbr (qi C q i) (wl C ℓ b i) * B C q c ℓ x (ew (a ++ b)) else 0 := by
  induction x using Free.induction with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]
    split_ifs <;> ring
  | smul_ew s r =>
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, B_ew_ew]
    rw [← List.append_assoc, φ_comm, List.append_assoc, List.append_assoc, wl_swap]
    split_ifs with h
    · subst h
      rw [wl_cancel]; ring
    · ring

variable (C q) in
/-- `R ℓ s = ρ̄(E_s)` acting on `'U 1_λ`: `R (l :: s) = R s ∘ ρ̄(E_l)`. -/
def R (ℓ : I → ℤ) : List (Bool × I) → (Free K I →ₗ[K] Free K I)
  | [] => LinearMap.id
  | l :: s => R ℓ s ∘ₗ rhoE C q ℓ l

theorem B_append (ℓ : I → ℤ) (s s' : List (Bool × I)) (y : Free K I) :
    B C q c ℓ (ew (s ++ s')) y = B C q c ℓ (ew s') (R C q ℓ s y) := by
  induction s generalizing y with
  | nil => rfl
  | cons l s ih => rw [List.cons_append, B_rhoE, ih]; rfl

theorem rhoE_rhoE_sub (ℓ : I → ℤ) (i j : I) (t : List (Bool × I)) :
    rhoE C q ℓ (false, j) (rhoE C q ℓ (true, i) (ew t)) -
        rhoE C q ℓ (true, i) (rhoE C q ℓ (false, j) (ew t)) =
      qp q (di C i * (1 - wl C ℓ t i) + di C j * (1 + wl C ℓ t j) - C.dot i j) •
        (ew ((true, j) :: (false, i) :: t) - ew ((false, i) :: (true, j) :: t)) := by
  simp only [rhoE_ew, map_smul, smul_smul, ← qp_add, smul_sub]
  simp only [Bool.not_true, Bool.not_false, sgn_true, sgn_false, wl_cons, one_mul]
  congr 2
  · rw [← di_mul_A, di_mul_A_comm]; ring_nf
  · rw [← di_mul_A]; ring_nf

/-- `B` respects the commutation relations (KL III eq. (2.4)) in the first argument. -/
theorem B_comm_left (ℓ : I → ℤ) (a b : List (Bool × I)) (i j : I) (y : Free K I) :
    B C q c ℓ (ew (a ++ (true, i) :: (false, j) :: b)) y =
      B C q c ℓ (ew (a ++ (false, j) :: (true, i) :: b)) y +
        if j = i then qbr (qi C q i) (wl C ℓ b i) * B C q c ℓ (ew (a ++ b)) y else 0 := by
  rw [B_append, B_append, B_append]
  generalize R C q ℓ a y = z
  induction z using Free.induction with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    split_ifs <;> ring
  | smul_ew t r =>
    simp only [map_smul, smul_eq_mul, B_rhoE]
    have key : B C q c ℓ (ew b) (rhoE C q ℓ (false, j) (rhoE C q ℓ (true, i) (ew t))) =
        B C q c ℓ (ew b) (rhoE C q ℓ (true, i) (rhoE C q ℓ (false, j) (ew t))) +
          if j = i then qbr (qi C q i) (wl C ℓ b i) * B C q c ℓ (ew b) (ew t) else 0 := by
      rw [← sub_eq_iff_eq_add', ← map_sub, rhoE_rhoE_sub, map_smul, map_sub, smul_eq_mul]
      have h := B_comm_right (C := C) (q := q) (c := c) ℓ (ew b) [] t j i
      simp only [List.nil_append] at h
      rw [h, add_sub_cancel_left]
      split_ifs with hji hij hij
      · subst hji
        by_cases hB : B C q c ℓ (ew b) (ew t) = 0
        · simp [hB]
        · have hbal := wl_eq_of_balanced (C := C) ℓ (by_contra fun h => hB
            (B_eq_zero_of_not_balanced ℓ h))
          rw [hbal]
          have : di C i * (1 - wl C ℓ t i) + di C i * (1 + wl C ℓ t i) - C.dot i i = 0 := by
            rw [← two_mul_di]; ring
          rw [this, qp_zero]; ring
      · exact absurd hji.symm hij
      · exact absurd hij.symm hji
      · simp
    rw [key]
    split_ifs <;> ring

end UDot

end Categorification.QuantumGroup

end
