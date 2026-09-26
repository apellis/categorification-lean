/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.BubbleSlidesAll
import Categorification.Diagrams.KL3.Grading

/-!
# The ring `Π_λ` of bubble monomials and `END_U(1_λ)`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.1
("Endomorphisms of `1_λ`"; TeX `\subsubsection{Endomorphisms of $\onel$}`, eq. (3.24), label
`eq_bub_rules`, Proposition 3.6, label `prop_bubbles_same_orient`, eq. (3.25), label
`homo_Pi_Uone`).

KL III define `Π_λ` as the graded commutative ring freely generated, over all `i ∈ I` and
`α > 0`, by the clockwise bubble with label `⟨i,λ⟩ - 1 + α` if `⟨i,λ⟩ ≥ 0`, and by the
counterclockwise bubble with label `-⟨i,λ⟩ - 1 + α` if `⟨i,λ⟩ < 0`, the generator of index
`(i, α)` having degree `α · (i·i)`. All these generators are real bubbles (their labels are
nonnegative).

## Conventions

* `PiLam I k = MvPolynomial (I × ℕ) k`: the variable `(i, n)` is KL III's generator with
  `α = n + 1`. As a ring it does not depend on `λ`; its interpretation does.
* `EndOne RD k λ` is the endomorphism ring of the identity 1-morphism `1_λ` of `U` (the empty
  word with region `λ`), with the commutative ring structure given by the interchange law
  (Eckmann–Hilton, `endEmpty_comm`). Its multiplication is `f * g = g ≫ f`, as for `End`.
* `bubMap RD k λ : PiLam I k →ₐ[k] EndOne RD k λ` is the homomorphism (3.25), and `IsBub RD k λ x`
  says that `x` lies in its image (a linear combination of bubble monomials).

`Π_λ` is graded by the weights `wPi` (`(n+1) (i·i)` for the variable `(i, n)`).

## Main results

* `EndOne`'s `CommRing` instance: `END_U(1_λ)` is commutative (`endEmpty_comm`).
* `bubMap RD k λ : PiLam I k →ₐ[k] EndOne RD k λ`: KL III's homomorphism (3.25).
* `cwU_isBub`, `ccwU_isBub`: every real or fake dotted bubble, of either orientation and any
  colour, with outer region `λ`, lies in the image of `Π_λ` (KL III's last sentence of the proof
  of Proposition 3.6: "Using the Grassmannian relations (3.7) all dotted bubbles with the same
  label `i` can be made to have the same orientation given by (3.24)").

The gradedness of `bubMap` and Corollary 3.7 are in `Categorification.Diagrams.KL3.EndOneGraded`;
the spanning results (Proposition 3.6 for crossingless diagrams) in
`Categorification.Diagrams.KL3.Spanning`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## `END_U(1_λ)` as a commutative algebra -/

/-- The endomorphism ring of the identity 1-morphism `1_λ` of `U` (KL III's `HOM_U(1_λ, 1_λ)`,
before splitting into degrees), with its commutative ring structure. -/
def EndOne (lam : X) : Type _ := End ((pres RD k).obj (ob RD lam []))

variable (lam : X)

/-- **`END_U(1_λ)` is commutative** (interchange law / Eckmann–Hilton, `endEmpty_comm`). -/
instance : CommRing (EndOne RD k lam) :=
  { (inferInstance : Ring (End ((pres RD k).obj (ob RD lam [])))) with
    mul_comm := fun a b => endEmpty_comm RD k lam b a }

instance : Algebra k (EndOne RD k lam) :=
  inferInstanceAs (Algebra k (End ((pres RD k).obj (ob RD lam []))))

namespace EndOne

variable {RD k lam}

/-- View an endomorphism of `1_λ` as an element of `EndOne`. -/
def of (x : End ((pres RD k).obj (ob RD lam []))) : EndOne RD k lam := x

/-- The underlying endomorphism. -/
def val (x : EndOne RD k lam) : End ((pres RD k).obj (ob RD lam [])) := x

@[simp] theorem val_of (x : End ((pres RD k).obj (ob RD lam []))) : (of x).val = x := rfl

@[simp] theorem of_val (x : EndOne RD k lam) : of x.val = x := rfl

theorem val_mul (x y : EndOne RD k lam) : (x * y).val = y.val ≫ x.val := rfl

theorem val_mul' (x y : EndOne RD k lam) : (x * y).val = x.val ≫ y.val :=
  (endEmpty_comm RD k lam y.val x.val)

@[simp] theorem val_one : (1 : EndOne RD k lam).val = 𝟙 _ := rfl

@[simp] theorem val_zero : (0 : EndOne RD k lam).val = 0 := rfl

@[simp] theorem val_add (x y : EndOne RD k lam) : (x + y).val = x.val + y.val := rfl

@[simp] theorem val_neg (x : EndOne RD k lam) : (-x).val = -x.val := rfl

@[simp] theorem val_sub (x y : EndOne RD k lam) : (x - y).val = x.val - y.val := rfl

@[simp] theorem val_smul (r : k) (x : EndOne RD k lam) : (r • x).val = r • x.val := rfl

theorem val_injective : Function.Injective (val : EndOne RD k lam → _) := fun _ _ h => h

theorem of_comp (x y : End ((pres RD k).obj (ob RD lam []))) : of (x ≫ y) = of x * of y :=
  (endEmpty_comm RD k lam x y).trans rfl

@[simp] theorem of_id : of (𝟙 ((pres RD k).obj (ob RD lam []))) = 1 := rfl

@[simp] theorem of_zero : of (0 : End ((pres RD k).obj (ob RD lam []))) = 0 := rfl

theorem of_add (x y : End ((pres RD k).obj (ob RD lam []))) : of (x + y) = of x + of y := rfl

theorem of_neg (x : End ((pres RD k).obj (ob RD lam []))) : of (-x) = -of x := rfl

theorem of_sub (x y : End ((pres RD k).obj (ob RD lam []))) : of (x - y) = of x - of y := rfl

theorem of_smul (r : k) (x : End ((pres RD k).obj (ob RD lam []))) : of (r • x) = r • of x := rfl

theorem of_sum {ι : Type*} (s : Finset ι) (f : ι → End ((pres RD k).obj (ob RD lam []))) :
    of (∑ j ∈ s, f j) = ∑ j ∈ s, of (f j) := rfl

theorem val_algebraMap (r : k) : (algebraMap k (EndOne RD k lam) r).val = r • 𝟙 _ := by
  rw [Algebra.algebraMap_eq_smul_one]; rfl

end EndOne

/-! ## The ring `Π_λ` and the homomorphism (3.25) -/

/-- KL III's `Π_λ` (eq. (3.24)): the polynomial ring over `k` in the variables `(i, n)`,
`i ∈ I`, `n ∈ ℕ` (KL III's generator of index `(i, α)` with `α = n + 1`). -/
abbrev PiLam (I : Type u) (k : Type w) [CommRing k] : Type _ := MvPolynomial (I × ℕ) k

/-- The weight `α · (i·i)` of the generator `(i, n)`, `α = n + 1` (KL III: "of degree
`α i·i`"). -/
def wPi (C : CartanDatum I) (p : I × ℕ) : ℤ := ((p.2 : ℤ) + 1) * C.dot p.1 p.1

theorem wPi_pos (p : I × ℕ) : 0 < wPi C p :=
  mul_pos (by omega) (C.dot_self_pos p.1)

/-- The bubble of colour `i` and degree index `α` of the orientation of eq. (3.24): the clockwise
bubble with label `⟨i,λ⟩ - 1 + α` if `⟨i,λ⟩ ≥ 0`, the counterclockwise bubble with label
`-⟨i,λ⟩ - 1 + α` if `⟨i,λ⟩ < 0`. For `α = 0` it is `1`, for `α > 0` a real bubble. -/
def bubGen (i : I) (α : ℕ) : End ((pres RD k).obj (ob RD lam [])) :=
  if 0 ≤ ip RD i lam then cwU RD k lam i (ip RD i lam - 1 + α)
  else ccwU RD k lam i (-ip RD i lam - 1 + α)

/-- **KL III eq. (3.25)**: the homomorphism `Π_λ → HOM_U(1_λ, 1_λ)` interpreting the variable
`(i, n)` as the bubble `bubGen λ i (n + 1)`. -/
def bubMap : PiLam I k →ₐ[k] EndOne RD k lam :=
  MvPolynomial.aeval (R := k) (S₁ := EndOne RD k lam) fun p => EndOne.of (bubGen RD k lam p.1 (p.2 + 1))

/-- `x` is a linear combination of bubble monomials: it lies in the image of `Π_λ`. -/
def IsBub (x : End ((pres RD k).obj (ob RD lam []))) : Prop :=
  EndOne.of x ∈ (bubMap RD k lam).range

variable {RD k lam}

theorem IsBub.zero : IsBub RD k lam 0 := Subalgebra.zero_mem _

theorem IsBub.id : IsBub RD k lam (𝟙 _) := Subalgebra.one_mem _

theorem IsBub.add {x y : End ((pres RD k).obj (ob RD lam []))} (hx : IsBub RD k lam x)
    (hy : IsBub RD k lam y) : IsBub RD k lam (x + y) := Subalgebra.add_mem _ hx hy

theorem IsBub.neg {x : End ((pres RD k).obj (ob RD lam []))} (hx : IsBub RD k lam x) :
    IsBub RD k lam (-x) := Subalgebra.neg_mem _ hx

theorem IsBub.sub {x y : End ((pres RD k).obj (ob RD lam []))} (hx : IsBub RD k lam x)
    (hy : IsBub RD k lam y) : IsBub RD k lam (x - y) := Subalgebra.sub_mem _ hx hy

theorem IsBub.smul {x : End ((pres RD k).obj (ob RD lam []))} (r : k) (hx : IsBub RD k lam x) :
    IsBub RD k lam (r • x) := Subalgebra.smul_mem _ hx r

theorem IsBub.zsmul {x : End ((pres RD k).obj (ob RD lam []))} (r : ℤ) (hx : IsBub RD k lam x) :
    IsBub RD k lam (r • x) := Subalgebra.zsmul_mem _ hx r

theorem IsBub.comp {x y : End ((pres RD k).obj (ob RD lam []))} (hx : IsBub RD k lam x)
    (hy : IsBub RD k lam y) : IsBub RD k lam (x ≫ y) := by
  unfold IsBub; rw [EndOne.of_comp]; exact Subalgebra.mul_mem _ hx hy

theorem IsBub.sum {ι : Type*} (s : Finset ι) {f : ι → End ((pres RD k).obj (ob RD lam []))}
    (h : ∀ j ∈ s, IsBub RD k lam (f j)) : IsBub RD k lam (∑ j ∈ s, f j) := by
  unfold IsBub; rw [EndOne.of_sum]; exact Subalgebra.sum_mem _ h

theorem isBub_bubGen (i : I) (α : ℕ) : IsBub RD k lam (bubGen RD k lam i α) := by
  rcases α with _ | n
  · unfold bubGen
    split_ifs
    · rw [Nat.cast_zero, add_zero, cwU_deg0]; exact IsBub.id
    · rw [Nat.cast_zero, add_zero, ccwU_deg0]; exact IsBub.id
  · exact ⟨MvPolynomial.X (i, n), by simp [bubMap]⟩

variable (RD k lam)

/-- The span of `IsBub` as a submodule of `End`. -/
def bubSubmodule : Submodule k (End ((pres RD k).obj (ob RD lam []))) where
  carrier := {x | IsBub RD k lam x}
  add_mem' := IsBub.add
  zero_mem' := IsBub.zero
  smul_mem' r _ hx := IsBub.smul r hx

variable {RD k lam}

theorem isBub_iff_mem_bubSubmodule (x : End ((pres RD k).obj (ob RD lam []))) :
    IsBub RD k lam x ↔ x ∈ bubSubmodule RD k lam := Iff.rfl

/-! ## All bubbles lie in the image of `Π_λ` -/

theorem isBub_cw_ccw (i : I) :
    (∀ m : ℤ, IsBub RD k lam (cwU RD k lam i m)) ∧ ∀ m : ℤ, IsBub RD k lam (ccwU RD k lam i m) := by
  have G := grassmannian_all RD k lam i
  by_cases h0 : 0 ≤ ip RD i lam
  · -- the clockwise bubbles are the generators
    have hcw : ∀ m : ℤ, IsBub RD k lam (cwU RD k lam i m) := by
      intro m
      by_cases h1 : m + 1 - ip RD i lam < 0
      · rw [cwU_eq_zero RD k lam i m h1]; exact IsBub.zero
      · have := isBub_bubGen (RD := RD) (k := k) (lam := lam) i (m + 1 - ip RD i lam).toNat
        unfold bubGen at this
        rw [if_pos h0, show ip RD i lam - 1 + (((m + 1 - ip RD i lam).toNat : ℕ) : ℤ) = m by omega] at this
        exact this
    refine ⟨hcw, fun m => ?_⟩
    by_cases h1 : m + 1 + ip RD i lam < 0
    · rw [ccwU_eq_zero RD k lam i m h1]; exact IsBub.zero
    · obtain ⟨a, ha⟩ : ∃ a : ℕ, m = -ip RD i lam - 1 + a := ⟨(m + 1 + ip RD i lam).toNat, by omega⟩
      subst ha
      induction a using Nat.strong_induction_on with
      | _ a ih =>
        rcases a with _ | a
        · rw [Nat.cast_zero, add_zero, ccwU_deg0]; exact IsBub.id
        · have Ga := G (a + 1)
          rw [if_neg (by omega), Finset.sum_range_succ, sub_self, add_zero, cwU_deg0,
            Category.comp_id] at Ga
          rw [eq_neg_of_add_eq_zero_right Ga]
          refine IsBub.neg (IsBub.sum _ fun j hj => ?_)
          have := Finset.mem_range.1 hj
          exact IsBub.comp (ih j (by omega) (by omega)) (hcw _)
  · -- the counterclockwise bubbles are the generators
    have hccw : ∀ m : ℤ, IsBub RD k lam (ccwU RD k lam i m) := by
      intro m
      by_cases h1 : m + 1 + ip RD i lam < 0
      · rw [ccwU_eq_zero RD k lam i m h1]; exact IsBub.zero
      · have := isBub_bubGen (RD := RD) (k := k) (lam := lam) i (m + 1 + ip RD i lam).toNat
        unfold bubGen at this
        rw [if_neg h0, show -ip RD i lam - 1 + (((m + 1 + ip RD i lam).toNat : ℕ) : ℤ) = m by omega] at this
        exact this
    refine ⟨fun m => ?_, hccw⟩
    by_cases h1 : m + 1 - ip RD i lam < 0
    · rw [cwU_eq_zero RD k lam i m h1]; exact IsBub.zero
    · obtain ⟨b, hb⟩ : ∃ b : ℕ, m = ip RD i lam - 1 + b := ⟨(m + 1 - ip RD i lam).toNat, by omega⟩
      subst hb
      induction b using Nat.strong_induction_on with
      | _ b ih =>
        rcases b with _ | b
        · rw [Nat.cast_zero, add_zero, cwU_deg0]; exact IsBub.id
        · have Gb := G (b + 1)
          rw [if_neg (by omega), Finset.sum_range_succ', Nat.cast_zero, add_zero, ccwU_deg0,
            Category.id_comp, sub_zero] at Gb
          rw [eq_neg_of_add_eq_zero_right Gb]
          refine IsBub.neg (IsBub.sum _ fun j hj => ?_)
          have := Finset.mem_range.1 hj
          refine IsBub.comp (hccw _) ?_
          have e : ip RD i lam - 1 + (((b + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) = ip RD i lam - 1 + ((b - j : ℕ) : ℤ) := by
            push_cast [Nat.cast_sub (by omega : j ≤ b)]; ring
          rw [e]
          exact ih (b - j) (by omega) (by omega)

/-- Every clockwise bubble (real or fake, any label) with outer region `λ` lies in the image of
`Π_λ`. -/
theorem cwU_isBub (i : I) (m : ℤ) : IsBub RD k lam (cwU RD k lam i m) := (isBub_cw_ccw i).1 m

/-- Every counterclockwise bubble (real or fake, any label) with outer region `λ` lies in the
image of `Π_λ`. -/
theorem ccwU_isBub (i : I) (m : ℤ) : IsBub RD k lam (ccwU RD k lam i m) := (isBub_cw_ccw i).2 m

theorem dg_cwLs_isBub (i : I) (m : ℕ) : IsBub RD k lam (dg RD k lam [] [] (cwLs i m)) := by
  rw [← cwU_of_nonneg]; exact cwU_isBub i m

theorem dg_ccwLs_isBub (i : I) (m : ℕ) : IsBub RD k lam (dg RD k lam [] [] (ccwLs i m)) := by
  rw [← ccwU_of_nonneg]; exact ccwU_isBub i m

end Categorification.KL3.Diagram
