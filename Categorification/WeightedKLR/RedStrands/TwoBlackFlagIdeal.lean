/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ExitPolynomialMatrix

/-!
# Polynomial ideals for two equal black strands

In Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21), a
rightward crossing past a red of pairing `d` acts by a black-dot power.
For the two-black flag polynomial quotient, the first and second black
strands have cumulative red pairings `m ≤ n`. Increasing the second pairing
by `d` and multiplying by its dot to power `d` gives an injective map.
-/

noncomputable section
namespace Categorification.Stendhal.TwoBlackFlag

open MvPolynomial Equiv
variable {k σ : Type*} [CommRing k]
local notation "P" => MvPolynomial σ k

/-- The complete homogeneous polynomial of degree `n−1` in two variables,
with value zero at `n=0`. -/
def complete {R : Type*} [CommRing R] (x y : R) : ℕ → R
  | 0 => 0
  | n+1 => y*complete x y n + x^n

theorem sub_mul_complete {R : Type*} [CommRing R] (x y : R) (n : ℕ) :
    (x-y)*complete x y n=x^n-y^n := by
  induction n with
  | zero => simp [complete]
  | succ n ih =>
    calc
      _ = y*((x-y)*complete x y n)+(x-y)*x^n := by rw [complete]; ring
      _ = _ := by rw [ih,pow_succ,pow_succ]; ring

/-- The two-variable generator is the divided difference of a single power. -/
theorem ddiff_X_pow {a b : σ} (hab : a≠b) (n : ℕ) :
    ddiff a b ((X a : P)^n)=complete (X a) (X b) n := by
  classical
  apply ddiff_eq_of_mul hab
  rw [map_pow,rename_X,swap_apply_left,sub_mul_complete]

/-- A divided power relation for the first black, and its divided difference
for the second black, with separate bounds for the two positions. -/
def ideal (a b : σ) (m n : ℕ) : Ideal P :=
  Ideal.span {(X a)^m, complete (X a) (X b) n}

private theorem complete_add {R : Type*} [CommRing R] (x y : R) (n d : ℕ) :
    ∃ u : R, complete x y (n+d)=y^d*complete x y n+x^n*u := by
  induction d with
  | zero => exact ⟨0,by simp⟩
  | succ d ih =>
    obtain ⟨u,hu⟩ := ih
    exact ⟨y*u+x^d,by rw [Nat.add_succ,complete,hu,pow_succ,pow_add]; ring⟩

/-- Increasing the second bound multiplies the second ideal generator by
its dot power modulo the first generator. -/
theorem ideal_add_right (a b : σ) {m n : ℕ} (hm : m≤n) (d : ℕ) :
    ideal (k := k) a b m (n+d) =
      Ideal.span {(X a)^m,(X b)^d*complete (X a) (X b) n} := by
  obtain ⟨u,hu⟩ := complete_add (X a : P) (X b) n d
  obtain ⟨l,hl⟩ := Nat.exists_eq_add_of_le hm
  have repl : complete (X a : P) (X b) (n+d) =
      (X b)^d*complete (X a) (X b) n + (X a)^m*((X a)^l*u) := by
    rw [hu,show (X a : P)^n=(X a)^m*(X a)^l by rw [hl,pow_add],mul_assoc]
  rw [ideal,repl,Ideal.span_pair_add_left_mul]

/-- Exact reflection of ideal membership for a rightward power of the
second black dot. This holds over any commutative ring. -/
theorem mul_second_pow_mem_iff {a b : σ} (hab : a≠b) {m n : ℕ} (hm : m≤n)
    (d : ℕ) (f : P) :
    f*(X b)^d ∈ ideal a b m (n+d) ↔ f ∈ ideal a b m n := by
  rw [ideal_add_right a b hm d,ideal,Ideal.mem_span_pair,Ideal.mem_span_pair]
  let x : P := X a
  let y : P := X b
  let H := complete x y n
  constructor
  · rintro ⟨u,v,hu⟩
    change u*x^m+v*(y^d*H)=f*y^d at hu
    have hdiv : x^m ∣ (f-v*H)*y^d := ⟨u,by linear_combination -hu⟩
    obtain ⟨w,hw⟩ := KLR.KLRAlgebra.X_pow_dvd_of_dvd_mul_other_pow hab m d hdiv
    exact ⟨w,v,by change w*x^m+v*H=f; linear_combination -hw⟩
  · rintro ⟨u,v,h⟩
    exact ⟨u*y^d,v,by rw [← h]; change u*y^d*x^m+v*(y^d*H)=(u*x^m+v*H)*y^d; ring⟩

/-- Renaming both black positions transports flag relations. -/
theorem rename_mem {τ : Type*} (r : σ → τ) {a b : σ} {m n : ℕ} {f : P}
    (hf : f ∈ ideal a b m n) : rename r f ∈ ideal (r a) (r b) m n := by
  have h (j : ℕ) : rename r (complete (X a : P) (X b) j)=complete (X (r a)) (X (r b)) j := by
    induction j with
    | zero => simp [complete]
    | succ j ih => simp only [complete,map_add,map_mul,map_pow,rename_X,ih]
  obtain ⟨u,v,rfl⟩ := Ideal.mem_span_pair.1 hf
  exact Ideal.mem_span_pair.2 ⟨rename r u,rename r v,by rw [map_add,map_mul,map_mul,map_pow,rename_X,h]⟩

/-- Moving a red right of the first black restricts its dot relation. -/
theorem restrict_first {a b : σ} {m n d : ℕ} {f : P}
    (hf : f ∈ ideal a b (m+d) n) : f ∈ ideal a b m n := by
  obtain ⟨u,v,rfl⟩ := Ideal.mem_span_pair.1 hf
  exact Ideal.mem_span_pair.2 ⟨u*(X a)^d,v,by rw [pow_add]; ring⟩

/-- Moving the first black right over a red multiplies by its dot power. -/
theorem push_first {a b : σ} {m n : ℕ} (d : ℕ) {f : P}
    (hf : f ∈ ideal a b m n) : f*(X a)^d ∈ ideal a b (m+d) n := by
  obtain ⟨u,v,rfl⟩ := Ideal.mem_span_pair.1 hf
  exact Ideal.mem_span_pair.2 ⟨u,v*(X a)^d,by rw [pow_add]; ring⟩

/-- Moving a red right of the second black restricts the second relation. -/
theorem restrict_second {a b : σ} {m n d : ℕ} (hm : m≤n) {f : P}
    (hf : f ∈ ideal a b m (n+d)) : f ∈ ideal a b m n := by
  rw [ideal_add_right a b hm d] at hf
  obtain ⟨u,v,rfl⟩ := Ideal.mem_span_pair.1 hf
  exact Ideal.mem_span_pair.2 ⟨u,v*(X b)^d,by ring⟩

/-- At equal cumulative bounds the black crossing preserves the flag ideal. -/
theorem ddiff_mem_ideal {a b : σ} (hab : a≠b) {m : ℕ} {f : P}
    (hf : f ∈ ideal a b m m) : ddiff a b f ∈ ideal a b m m := by
  classical
  obtain ⟨u,v,rfl⟩ := Ideal.mem_span_pair.1 hf
  rw [map_add,ddiff_mul hab,ddiff_mul hab,← ddiff_X_pow hab m,ddiff_ddiff hab, mul_zero,add_zero]
  exact Ideal.mem_span_pair.2 ⟨ddiff a b u,rename (swap a b) u+ddiff a b v,by rw [ddiff_X_pow hab]; ring⟩

end Categorification.Stendhal.TwoBlackFlag
