/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.Bar
import Categorification.QuantumGroup.SerreDivided

/-!
# Signed sequences and the free idempotented algebra behind `U̇`

Khovanov–Lauda III, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §2.1.4:
write `E_{+i} = E_i` and `E_{-i} = F_i`; a *signed sequence* `i = (ε₁i₁, …, εₘiₘ)` gives
`E_i 1_λ = E_{ε₁i₁} ⋯ E_{εₘiₘ} 1_λ ∈ U̇` (eq. (2.10)), whose left weight is `λ + i_X`
(eq. (2.11)).

For a fixed right weight `λ`, the elements `E_i 1_λ` (over all signed sequences `i`) span
`U̇ 1_λ`, and they form a basis of the free version `'U 1_λ` of KL III eq. (2.40)
(the algebra with basis `{E_i 1_λ}` and concatenation product). We realise `'U 1_λ` as the
free algebra `Free K I = 'f` on the signed letters `Bool × I` (`true = +`, `false = -`), with
basis vectors `ew w` for lists `w` of signed letters. The weight `λ` enters only through the
integers `⟨i, λ⟩`, recorded as a function `ℓ : I → ℤ`; the weight functional of `E_w 1_λ`
is `wl C ℓ w : i ↦ ⟨i, λ + w_X⟩` (`wl`).

## Main definitions

* `UDot.A C i j = 2 (i·j)/(i·i) = ⟨i, j_X⟩`, `UDot.di C i = (i·i)/2` (so `q_i = q^{di i}`);
* `UDot.qbr t n = (tⁿ - t⁻ⁿ)/(t - t⁻¹)`, the quantum integer `[n]` (for `n ∈ ℤ`);
* `UDot.posMS w`, `UDot.negMS w` — the multisets of positively/negatively signed labels; the
  signed weight of `w` in `ℤ[I]` is `posMS w - negMS w`;
* `UDot.aS C i w = ⟨i, w_X⟩` and `UDot.wl C ℓ w`;
* `UDot.ρW w` — reverse the sequence and flip all signs (the sequence of `ρ̄(E_w 1_λ)`);
* `UDot.posF`, `UDot.negF : 'f →ₐ Free` — `θ_i ↦ E_{+i}`, resp. `θ_i ↦ E_{-i}`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical

namespace UDot

variable {I : Type*}

/-! ### Signs -/

/-- The integer `±1` attached to a sign (`true = +`, `false = -`). -/
def sgn : Bool → ℤ
  | true => 1
  | false => -1

@[simp] theorem sgn_true : sgn true = 1 := rfl

@[simp] theorem sgn_false : sgn false = -1 := rfl

@[simp] theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> rfl

@[simp] theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> rfl

/-! ### Cartan integers -/

variable (C : CartanDatum I)

/-- The Cartan integer `⟨i, j_X⟩ = 2 (i·j)/(i·i)` of a root datum of type `(I, ·)`
(KL III §2.1.1). -/
def A (i j : I) : ℤ := 2 * C.dot i j / C.dot i i

/-- `(i·i)/2`, so that `q_i = q^{(i·i)/2} = q^{di i}` (KL III §2.1.1). -/
def di (i : I) : ℤ := C.dot i i / 2

theorem two_mul_di (i : I) : 2 * di C i = C.dot i i := by
  obtain ⟨k, hk⟩ := C.dot_self_even i
  unfold di; omega

theorem di_pos (i : I) : 0 < di C i := by
  have := two_mul_di C i
  have := C.dot_self_pos i
  omega

theorem di_mul_A (i j : I) : di C i * A C i j = C.dot i j := by
  obtain ⟨q, hq⟩ := C.dvd_two_mul i j
  have hpos := C.dot_self_pos i
  have hA : A C i j = q := by
    unfold A; rw [hq, Int.mul_ediv_cancel_left _ hpos.ne']
  rw [hA]
  have h2 := two_mul_di C i
  have : 2 * (di C i * q) = 2 * C.dot i j := by rw [hq, ← h2]; ring
  omega

theorem A_self (i : I) : A C i i = 2 := by
  unfold A
  rw [mul_comm, Int.mul_ediv_cancel_left _ (C.dot_self_pos i).ne']

theorem di_mul_A_comm (i j : I) : di C i * A C i j = di C j * A C j i := by
  rw [di_mul_A, di_mul_A, C.symm]

/-- `⟨i, ν_X⟩ = Σ_{j ∈ ν} ⟨i, j_X⟩` for a multiset `ν` of labels. -/
def msA (i : I) (ν : Multiset I) : ℤ := (ν.map (A C i)).sum

@[simp] theorem msA_zero (i : I) : msA C i 0 = 0 := by simp [msA]

@[simp] theorem msA_cons (i j : I) (ν : Multiset I) :
    msA C i (j ::ₘ ν) = A C i j + msA C i ν := by simp [msA]

@[simp] theorem msA_add (i : I) (ν μ : Multiset I) :
    msA C i (ν + μ) = msA C i ν + msA C i μ := by simp [msA]

theorem msA_singleton (i j : I) : msA C i {j} = A C i j := by simp [msA]

/-! ### Quantum integers -/

/-- The quantum integer `[n]_t = (tⁿ - t⁻ⁿ)/(t - t⁻¹)` for `n ∈ ℤ`. -/
def qbr {K : Type*} [Field K] (t : Kˣ) (n : ℤ) : K :=
  (((t ^ n : Kˣ) : K) - ((t ^ (-n) : Kˣ) : K)) / ((t : K) - ((t⁻¹ : Kˣ) : K))

/-- `q_i = q^{(i·i)/2}`. -/
def qi {K : Type*} [Field K] (q : Kˣ) (i : I) : Kˣ := q ^ di C i

/-! ### Signed sequences -/

/-- The multiset of labels carrying a `+` sign. -/
def posMS (w : List (Bool × I)) : Multiset I := ((w.filter fun l => l.1).map Prod.snd : List I)

/-- The multiset of labels carrying a `-` sign. -/
def negMS (w : List (Bool × I)) : Multiset I := ((w.filter fun l => !l.1).map Prod.snd : List I)

@[simp] theorem posMS_nil : posMS ([] : List (Bool × I)) = 0 := rfl

@[simp] theorem negMS_nil : negMS ([] : List (Bool × I)) = 0 := rfl

@[simp] theorem posMS_cons_true (i : I) (w : List (Bool × I)) :
    posMS ((true, i) :: w) = i ::ₘ posMS w := by simp [posMS]

@[simp] theorem posMS_cons_false (i : I) (w : List (Bool × I)) :
    posMS ((false, i) :: w) = posMS w := by simp [posMS]

@[simp] theorem negMS_cons_true (i : I) (w : List (Bool × I)) :
    negMS ((true, i) :: w) = negMS w := by simp [negMS]

@[simp] theorem negMS_cons_false (i : I) (w : List (Bool × I)) :
    negMS ((false, i) :: w) = i ::ₘ negMS w := by simp [negMS]

@[simp] theorem posMS_append (w w' : List (Bool × I)) :
    posMS (w ++ w') = posMS w + posMS w' := by simp [posMS, List.filter_append]

@[simp] theorem negMS_append (w w' : List (Bool × I)) :
    negMS (w ++ w') = negMS w + negMS w' := by simp [negMS, List.filter_append]

/-- `⟨i, w_X⟩` for a signed sequence `w`: `Σ_k ε_k ⟨i, (i_k)_X⟩`. -/
def aS (i : I) (w : List (Bool × I)) : ℤ := (w.map fun l => sgn l.1 * A C i l.2).sum

@[simp] theorem aS_nil (i : I) : aS C i [] = 0 := rfl

@[simp] theorem aS_cons (i : I) (l : Bool × I) (w : List (Bool × I)) :
    aS C i (l :: w) = sgn l.1 * A C i l.2 + aS C i w := by simp [aS]

@[simp] theorem aS_append (i : I) (w w' : List (Bool × I)) :
    aS C i (w ++ w') = aS C i w + aS C i w' := by simp [aS]

theorem aS_eq (i : I) (w : List (Bool × I)) :
    aS C i w = msA C i (posMS w) - msA C i (negMS w) := by
  induction w with
  | nil => simp
  | cons l w ih =>
    obtain ⟨b, j⟩ := l
    cases b <;> simp [ih] <;> ring

/-- Two signed sequences are *balanced* if they have the same weight in `ℤ[I]`. -/
def Balanced (s t : List (Bool × I)) : Prop := posMS s + negMS t = posMS t + negMS s

theorem aS_eq_of_balanced {s t : List (Bool × I)} (h : Balanced s t) (i : I) :
    aS C i s = aS C i t := by
  rw [aS_eq, aS_eq]
  have := congrArg (msA C i) h
  simp only [msA_add] at this
  linarith

/-- The weight functional `i ↦ ⟨i, λ + w_X⟩` of `E_w 1_λ`, where `ℓ i = ⟨i, λ⟩`. -/
def wl (ℓ : I → ℤ) (w : List (Bool × I)) : I → ℤ := fun i => ℓ i + aS C i w

theorem wl_cons (ℓ : I → ℤ) (l : Bool × I) (w : List (Bool × I)) :
    wl C ℓ (l :: w) = fun i => wl C ℓ w i + sgn l.1 * A C i l.2 := by
  funext i; simp [wl]; ring

/-- The negative sequence `(-c₁, …, -cₘ)`. -/
def negW (c : List I) : List (Bool × I) := c.map fun i => (false, i)

/-- The positive sequence `(+b₁, …, +bₘ)`. -/
def posW (b : List I) : List (Bool × I) := b.map fun i => (true, i)

@[simp] theorem negW_nil : negW ([] : List I) = [] := rfl
@[simp] theorem posW_nil : posW ([] : List I) = [] := rfl
@[simp] theorem negW_cons (i : I) (c : List I) : negW (i :: c) = (false, i) :: negW c := rfl
@[simp] theorem posW_cons (i : I) (c : List I) : posW (i :: c) = (true, i) :: posW c := rfl
@[simp] theorem negW_append (c c' : List I) : negW (c ++ c') = negW c ++ negW c' := by
  simp [negW]
@[simp] theorem posW_append (c c' : List I) : posW (c ++ c') = posW c ++ posW c' := by
  simp [posW]

@[simp] theorem posMS_posW (b : List I) : posMS (posW b) = (b : Multiset I) := by
  induction b with
  | nil => rfl
  | cons i b ih => simp [ih]

@[simp] theorem negMS_posW (b : List I) : negMS (posW b) = 0 := by
  induction b with
  | nil => rfl
  | cons i b ih => simp [ih]

@[simp] theorem posMS_negW (b : List I) : posMS (negW b) = 0 := by
  induction b with
  | nil => rfl
  | cons i b ih => simp [ih]

@[simp] theorem negMS_negW (b : List I) : negMS (negW b) = (b : Multiset I) := by
  induction b with
  | nil => rfl
  | cons i b ih => simp [ih]

/-- The signed sequence of `ρ̄(E_w 1_λ)`: reverse `w` and flip every sign. -/
def ρW (w : List (Bool × I)) : List (Bool × I) := (w.map fun l => (!l.1, l.2)).reverse

@[simp] theorem ρW_nil : ρW ([] : List (Bool × I)) = [] := rfl

theorem ρW_cons (l : Bool × I) (w : List (Bool × I)) : ρW (l :: w) = ρW w ++ [(!l.1, l.2)] := by
  simp [ρW]

theorem ρW_append (w w' : List (Bool × I)) : ρW (w ++ w') = ρW w' ++ ρW w := by
  simp [ρW]

theorem ρW_ρW (w : List (Bool × I)) : ρW (ρW w) = w := by
  simp [ρW, List.map_reverse, Function.comp_def]

@[simp] theorem posMS_ρW (w : List (Bool × I)) : posMS (ρW w) = negMS w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨b, j⟩ := l
    cases b <;> simp [ρW_cons, ih, add_comm]

@[simp] theorem negMS_ρW (w : List (Bool × I)) : negMS (ρW w) = posMS w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨b, j⟩ := l
    cases b <;> simp [ρW_cons, ih, add_comm]

theorem aS_ρW (i : I) (w : List (Bool × I)) : aS C i (ρW w) = -aS C i w := by
  rw [aS_eq, aS_eq, posMS_ρW, negMS_ρW]; ring

theorem ρW_negW (c : List I) : ρW (negW c) = posW c.reverse := by
  simp [ρW, negW, posW, List.map_reverse]

theorem ρW_posW (c : List I) : ρW (posW c) = negW c.reverse := by
  simp [ρW, negW, posW, List.map_reverse]

/-! ### The free algebra on signed letters -/

variable (K : Type*) [Field K]

/-- The free algebra on the signed letters `E_{±i}`; for a fixed right weight `λ` it is the
free version `'U 1_λ` of `U̇ 1_λ` (KL III eq. (2.40)). -/
abbrev Free (I : Type*) := PreF K (Bool × I)

variable {K}

/-- The basis vector `E_w 1_λ` of `'U 1_λ` for a signed sequence `w` (KL III eq. (2.10)). -/
def ew (w : List (Bool × I)) : Free K I := PreF.word (FreeMonoid.ofList w)

@[simp] theorem ew_nil : (ew [] : Free K I) = 1 := rfl

theorem ew_append (w w' : List (Bool × I)) : (ew (w ++ w') : Free K I) = ew w * ew w' := by
  rw [ew, FreeMonoid.ofList_append, PreF.word_mul]; rfl

theorem ew_cons (l : Bool × I) (w : List (Bool × I)) :
    (ew (l :: w) : Free K I) = ew [l] * ew w := by
  rw [← ew_append]; rfl

theorem word_eq_ew (w : FreeMonoid (Bool × I)) : (PreF.word w : Free K I) = ew w.toList := rfl

/-- Linear-combination induction on `Free` in terms of the basis `ew`. -/
@[elab_as_elim]
theorem Free.induction {motive : Free K I → Prop} (x : Free K I) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul_ew : ∀ w (r : K), motive (r • ew w)) : motive x :=
  PreF.induction_linear x zero add fun w r => smul_ew w.toList r

/-- Two linear maps out of `Free` agreeing on the basis `ew` are equal. -/
theorem Free.lhom_ext {N : Type*} [AddCommMonoid N] [Module K N] ⦃φ ψ : Free K I →ₗ[K] N⦄
    (h : ∀ w, φ (ew w) = ψ (ew w)) : φ = ψ :=
  PreF.lhom_ext fun w => h w.toList

/-- The embedding `θ_i ↦ E_{+i}` of `'f` into `Free` (`x ↦ x⁺`). -/
def posF : PreF K I →ₐ[K] Free K I :=
  MonoidAlgebra.mapDomainAlgHom K K (FreeMonoid.map fun i => (true, i))

/-- The embedding `θ_i ↦ E_{-i}` of `'f` into `Free` (`x ↦ x⁻`). -/
def negF : PreF K I →ₐ[K] Free K I :=
  MonoidAlgebra.mapDomainAlgHom K K (FreeMonoid.map fun i => (false, i))

theorem posF_word (u : FreeMonoid I) : posF (PreF.word u : PreF K I) = ew (posW u.toList) := by
  simp [posF, PreF.word, ew, MonoidAlgebra.mapDomain_single, posW]
  rfl

theorem negF_word (u : FreeMonoid I) : negF (PreF.word u : PreF K I) = ew (negW u.toList) := by
  simp [negF, PreF.word, ew, MonoidAlgebra.mapDomain_single, negW]
  rfl

end UDot

end Categorification.QuantumGroup

end
