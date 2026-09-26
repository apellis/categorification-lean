/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotWords

/-!
# The normal-ordering model of `'U̇ 1_λ`

Khovanov–Lauda III (arXiv:0807.3250v1, §2.1.3, eq. (2.4) and §2.2, proof of Theorem 2.7)
compute with `U̇ 1_λ` by moving `F`'s to the left of `E`'s using
`(E_iF_j - F_jE_i) 1_μ = δ_{ij} [⟨i, μ⟩]_i 1_μ`. We make this precise with an explicit
representation of the free algebra `Free = 'U 1_λ` on the space
`M = 'f ⊗ 'f` (with basis the pairs of words `(c, b)`), where `(c, b)` stands for the
normal-ordered monomial `F_{c^{rev}} E_b 1_λ` (`F_{cₘ} ⋯ F_{c₁} E_{b₁} ⋯ E_{bₖ} 1_λ`):

* `F_j` acts by `(c, b) ↦ (c θ_j, b)` (`UDot.Fop`);
* `E_i` acts by `(c, b) ↦ (c, θ_i b) + (D_i^{(n)} c, b)` with `n = ⟨i, λ + |b|⟩`
  (`UDot.Eop`), where the *quantum derivation* `D_i^{(n)}` (`UDot.D`) is
  `D_i^{(n)}(c₁ ⋯ cₘ) = Σ_{p : c_p = i} [n - ⟨i, (c₁ + ⋯ + c_{p-1})_X⟩]_i c₁ ⋯ ĉ_p ⋯ cₘ`.

This is the formula `E_i F_a E_b 1_λ = F_a E_{ib} 1_λ + [E_i, F_a] E_b 1_λ` expanded with the
commutation relation. The action is `UDot.act ℓ : Free →ₐ End M`, and
`UDot.NF ℓ x = x · (1 ⊗ 1)` is the normal form of `x`.

## Main results

* `UDot.NF_mem_Msupp` — `NF (E_w)` lies in the weight space of `w`;
* `UDot.Eop_Fop_sub` — on a weight space, `E_iF_j - F_jE_i` acts by `δ_{ij} [⟨i, μ⟩]_i`;
* `UDot.NF_comm` — hence `NF` kills the commutation relators (KL III eq. (2.4)):
  `NF(E_{a (+i)(-j) b}) = NF(E_{a (-j)(+i) b}) + δ_{ij} [⟨i, λ + b_X⟩]_i NF(E_{ab})`;
* `UDot.NF_negW_posW` — `NF(F_{c₁} ⋯ F_{cₘ} E_b 1_λ) = (c^{rev}, b)`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K] (C : CartanDatum I) (q : Kˣ)

/-! ### The quantum derivations `D_i^{(n)}` -/

/-- `D_i^{(n)}` on a word, by recursion on its first letter. -/
def DW (i : I) : List I → ℤ → PreF K I
  | [], _ => 0
  | j :: u, n => (if j = i then qbr (qi C q i) n • word (FreeMonoid.ofList u) else 0) +
      θ j * DW i u (n - A C i j)

/-- The quantum derivation `D_i^{(n)}(c₁ ⋯ cₘ) = Σ_{p : c_p = i} [n - ⟨i, (c_{<p})_X⟩]_i c₁ ⋯ ĉ_p ⋯ cₘ`,
which computes the commutator `[E_i, F_{c^{rev}}]` against a right weight with `⟨i, -⟩ = n`. -/
def D (i : I) (n : ℤ) : PreF K I →ₗ[K] PreF K I :=
  linLift fun w => DW C q i (FreeMonoid.toList w) n

variable {C q}

@[simp] theorem D_one (i : I) (n : ℤ) : D C q i n (1 : PreF K I) = 0 := by
  rw [← word_one, D, linLift_word]; rfl

theorem D_word_of_mul (i j : I) (n : ℤ) (u : FreeMonoid I) :
    D C q i n (word (FreeMonoid.of j * u) : PreF K I) =
      (if j = i then qbr (qi C q i) n • word u else 0) + θ j * D C q i (n - A C i j) (word u) := by
  simp only [D, linLift_word, FreeMonoid.toList_of_mul, DW, FreeMonoid.ofList_toList]

theorem D_θ_mul (i j : I) (n : ℤ) (y : PreF K I) :
    D C q i n (θ j * y) =
      (if j = i then qbr (qi C q i) n • y else 0) + θ j * D C q i (n - A C i j) y := by
  induction y using induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [mul_add, map_add, hx, hy, map_add, mul_add]
    simp only [smul_add]
    split_ifs <;> abel
  | smul_word w c =>
    rw [mul_smul_comm, map_smul, ← word_of_mul, D_word_of_mul, map_smul, mul_smul_comm,
      smul_add]
    split_ifs <;> simp [smul_comm c]

theorem D_θ (i j : I) (n : ℤ) :
    D C q i n (θ j : PreF K I) = if j = i then qbr (qi C q i) n • 1 else 0 := by
  have := D_θ_mul (C := C) (q := q) i j n 1
  rw [mul_one, D_one, mul_zero, add_zero] at this
  exact this

/-- The twisted Leibniz rule for `D_i^{(n)}` with a word as left factor:
`D^{(n)}(u y) = D^{(n)}(u) y + u D^{(n - ⟨i, |u|⟩)}(y)`. -/
theorem D_word_mul (i : I) (n : ℤ) (u : FreeMonoid I) (y : PreF K I) :
    D C q i n (word u * y) = D C q i n (word u) * y + word u * D C q i (n - msA C i (wt u)) y := by
  induction u using FreeMonoid.inductionOn' generalizing n with
  | one => simp
  | mul_of j u ih =>
    rw [word_of_mul, mul_assoc, D_θ_mul, ih, D_θ_mul, wt_of_mul, msA_cons, ← sub_sub]
    split_ifs
    · simp only [mul_add, add_mul, smul_mul_assoc, mul_assoc, add_assoc]
    · simp only [zero_add, mul_add, add_mul, mul_assoc]

/-- The Leibniz rule with a homogeneous left factor. -/
theorem D_mul_of_mem_grade (i : I) (n : ℤ) {ν : Multiset I} {x : PreF K I} (hx : x ∈ grade K ν)
    (y : PreF K I) :
    D C q i n (x * y) = D C q i n x * y + x * D C q i (n - msA C i ν) y := by
  refine eqOn_supp ((D C q i n) ∘ₗ LinearMap.mulRight K y)
    (LinearMap.mulRight K y ∘ₗ D C q i n + LinearMap.mulRight K (D C q i (n - msA C i ν) y))
      ?_ x hx
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
    LinearMap.add_apply, D_word_mul, hw]

theorem D_word_mul_θ (i j : I) (n : ℤ) (c : FreeMonoid I) :
    D C q i n (word c * θ j : PreF K I) = D C q i n (word c) * θ j +
      (if j = i then qbr (qi C q i) (n - msA C i (wt c)) • word c else 0) := by
  rw [D_word_mul, D_θ]
  split_ifs <;> simp

/-- `D_i^{(n)}` removes one letter `i`. -/
theorem D_word_mem_supp (i : I) (n : ℤ) (c : FreeMonoid I) :
    D C q i n (word c : PreF K I) ∈ (supp {w | i ::ₘ wt w = wt c} : Submodule K (PreF K I)) := by
  induction c using FreeMonoid.inductionOn' generalizing n with
  | one => simp
  | mul_of j c ih =>
    rw [D_word_of_mul]
    refine Submodule.add_mem _ ?_ ?_
    · split_ifs with h
      · exact Submodule.smul_mem _ _ (word_mem_supp (by simp [wt_of_mul, h]))
      · exact Submodule.zero_mem _
    · refine map_supp_le (LinearMap.mulLeft K (θ j)) ?_ _ (ih (n - A C i j))
      intro w hw
      simp only [LinearMap.mulLeft_apply, ← word_of_mul]
      refine word_mem_supp ?_
      simp only [Set.mem_setOf_eq, wt_of_mul] at hw ⊢
      rw [Multiset.cons_swap, hw]

/-! ### The space `M = 'f ⊗ 'f` -/

/-- The model space `M`, with basis the pairs of words `(c, b)`, standing for
`F_{c^{rev}} E_b 1_λ`. -/
abbrev M (K I : Type*) [Semiring K] := (FreeMonoid I × FreeMonoid I) →₀ K

/-- The bilinear map `(x, y) ↦ x ⊗ y ∈ M`. -/
def tm : PreF K I →ₗ[K] PreF K I →ₗ[K] M K I :=
  linLift fun u => linLift fun w => Finsupp.single (u, w) 1

@[simp] theorem tm_word_word (u w : FreeMonoid I) :
    tm (word u : PreF K I) (word w) = Finsupp.single (u, w) 1 := by
  simp [tm, linLift_word]

theorem single_eq_tm (p : FreeMonoid I × FreeMonoid I) :
    (Finsupp.single p 1 : M K I) = tm (word p.1) (word p.2) := by simp

/-- A linear map out of `M` is determined by its values on `tm (word u) (word w)`. -/
theorem M_lhom_ext {N : Type*} [AddCommMonoid N] [Module K N] ⦃φ ψ : M K I →ₗ[K] N⦄
    (h : ∀ u w, φ (tm (word u) (word w)) = ψ (tm (word u) (word w))) : φ = ψ :=
  Finsupp.lhom_ext' fun p => LinearMap.ext_ring (by
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [single_eq_tm]; exact h p.1 p.2)

/-- `x ⊗ y` for `x` supported on `S` is supported on `S × {w}` when `y = word w`. -/
theorem tm_mem_supported {S : Set (FreeMonoid I)} {x : PreF K I}
    (hx : x ∈ (supp S : Submodule K (PreF K I))) (w : FreeMonoid I) :
    tm x (word w) ∈ Finsupp.supported K K {p : FreeMonoid I × FreeMonoid I | p.1 ∈ S ∧ p.2 = w} := by
  refine eqOn_supp (S := S) ((Finsupp.supported K K _).mkQ ∘ₗ (tm.flip (word w))) 0 ?_ x hx |>
    fun h => (Submodule.Quotient.mk_eq_zero _).1 (by simpa using h)
  intro u hu
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, tm_word_word,
    LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Finsupp.single_mem_supported K _ ⟨hu, rfl⟩

/-! ### The generators acting on `M` -/

/-- `F_j` acting on `M`: `(c, b) ↦ (c θ_j, b)`. -/
def Fop (j : I) : Module.End K (M K I) :=
  Finsupp.linearCombination K fun p => tm (word p.1 * θ j) (word p.2)

variable (C q) in
/-- `E_i` acting on `M` for the right weight `ℓ = ⟨-, λ⟩`:
`(c, b) ↦ (c, θ_i b) + (D_i^{(⟨i, λ + |b|⟩)} c, b)`. -/
def Eop (ℓ : I → ℤ) (i : I) : Module.End K (M K I) :=
  Finsupp.linearCombination K fun p =>
    tm (word p.1) (θ i * word p.2) + tm (D C q i (ℓ i + msA C i (wt p.2)) (word p.1)) (word p.2)

theorem Fop_tm (j : I) (x y : PreF K I) : Fop j (tm x y) = tm (x * θ j) y := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [map_add, LinearMap.add_apply, map_add, hx, hx', add_mul, map_add,
      LinearMap.add_apply]
  | smul_word u r =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add]
    | smul_word w s =>
      simp only [map_smul, LinearMap.smul_apply, tm_word_word, Fop, smul_mul_assoc]
      rw [Finsupp.linearCombination_single, one_smul]

theorem Eop_tm_word (ℓ : I → ℤ) (i : I) (x : PreF K I) (w : FreeMonoid I) :
    Eop C q ℓ i (tm x (word w)) =
      tm x (θ i * word w) + tm (D C q i (ℓ i + msA C i (wt w)) x) (word w) := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [map_add, LinearMap.add_apply, map_add, hx, hx', map_add, map_add,
      LinearMap.add_apply, LinearMap.add_apply]; abel
  | smul_word u r =>
    simp only [map_smul, LinearMap.smul_apply, tm_word_word, Eop, smul_add]
    rw [Finsupp.linearCombination_single]
    simp

variable (C q) in
/-- The generator `E_{εi}` acting on `M`. -/
def gen (ℓ : I → ℤ) : Bool × I → Module.End K (M K I)
  | (true, i) => Eop C q ℓ i
  | (false, i) => Fop i

variable (C q) in
/-- The action of the free algebra `Free = 'U 1_λ` on `M`. -/
def act (ℓ : I → ℤ) : Free K I →ₐ[K] Module.End K (M K I) :=
  MonoidAlgebra.lift K (FreeMonoid (Bool × I)) (Module.End K (M K I)) (FreeMonoid.lift (gen C q ℓ))

theorem act_ew (ℓ : I → ℤ) (w : List (Bool × I)) :
    act C q ℓ (ew w) = (w.map (gen C q ℓ)).prod := by
  rw [act, ew, word, MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_apply]
  rfl

theorem act_ew_cons (ℓ : I → ℤ) (l : Bool × I) (w : List (Bool × I)) :
    act C q ℓ (ew (l :: w)) = gen C q ℓ l * act C q ℓ (ew w) := by
  rw [act_ew, act_ew, List.map_cons, List.prod_cons]

theorem act_ew_append (ℓ : I → ℤ) (w w' : List (Bool × I)) :
    act C q ℓ (ew (w ++ w')) = act C q ℓ (ew w) * act C q ℓ (ew w') := by
  rw [ew_append, map_mul]

/-- The vacuum `1 ⊗ 1`, i.e. `1_λ`. -/
def vac : M K I := Finsupp.single (1, 1) 1

variable (C q) in
/-- The normal form `NF x = x · (1 ⊗ 1)` of `x ∈ 'U 1_λ`. -/
def NF (ℓ : I → ℤ) : Free K I →ₗ[K] M K I :=
  LinearMap.applyₗ (vac (K := K) (I := I)) ∘ₗ (act C q ℓ).toLinearMap

theorem NF_apply (ℓ : I → ℤ) (x : Free K I) : NF C q ℓ x = act C q ℓ x vac := rfl

theorem NF_mul (ℓ : I → ℤ) (x y : Free K I) : NF C q ℓ (x * y) = act C q ℓ x (NF C q ℓ y) := by
  simp [NF_apply, Module.End.mul_apply]

theorem NF_ew_cons (ℓ : I → ℤ) (l : Bool × I) (w : List (Bool × I)) :
    NF C q ℓ (ew (l :: w)) = gen C q ℓ l (NF C q ℓ (ew w)) := by
  rw [NF_apply, act_ew_cons, Module.End.mul_apply]; rfl

theorem NF_ew_append (ℓ : I → ℤ) (w w' : List (Bool × I)) :
    NF C q ℓ (ew (w ++ w')) = act C q ℓ (ew w) (NF C q ℓ (ew w')) := by
  rw [ew_append, NF_mul]

theorem vac_eq : (vac : M K I) = tm 1 1 := by
  rw [vac, ← word_one, tm_word_word]

theorem NF_posW (ℓ : I → ℤ) (b : List I) :
    NF C q ℓ (ew (posW b)) = tm (1 : PreF K I) (word (FreeMonoid.ofList b)) := by
  induction b with
  | nil => rw [posW_nil, ew_nil, NF_apply, map_one, Module.End.one_apply, vac_eq]; rfl
  | cons i b ih =>
    rw [posW_cons, NF_ew_cons, ih]
    change Eop C q ℓ i _ = _
    rw [Eop_tm_word, D_one, map_zero, LinearMap.zero_apply, add_zero, FreeMonoid.ofList_cons,
      word_of_mul]

theorem act_negW_tm (ℓ : I → ℤ) (c : List I) (x y : PreF K I) :
    act C q ℓ (ew (negW c)) (tm x y) = tm (x * word (FreeMonoid.ofList c.reverse)) y := by
  induction c generalizing x with
  | nil => simp [ew_nil]
  | cons i c ih =>
    rw [negW_cons, act_ew_cons, Module.End.mul_apply, ih]
    change Fop i _ = _
    rw [Fop_tm, List.reverse_cons, FreeMonoid.ofList_append, word_mul, mul_assoc]
    rfl

/-- `NF(F_{c₁} ⋯ F_{cₘ} E_{b₁} ⋯ E_{bₖ} 1_λ) = (c^{rev}, b)`. -/
theorem NF_negW_posW (ℓ : I → ℤ) (c b : List I) :
    NF C q ℓ (ew (negW c ++ posW b)) =
      tm (word (FreeMonoid.ofList c.reverse) : PreF K I) (word (FreeMonoid.ofList b)) := by
  rw [NF_ew_append, NF_posW, act_negW_tm, one_mul]

/-! ### Weight spaces of `M` -/

/-- The weight space of `M` of signed weight `P - N ∈ ℤ[I]`: pairs `(c, b)` with
`|b| - |c| = P - N`. -/
def Msupp (P N : Multiset I) : Submodule K (M K I) :=
  Finsupp.supported K K {p : FreeMonoid I × FreeMonoid I | wt p.2 + N = wt p.1 + P}

theorem Msupp_induction {P N : Multiset I} {motive : M K I → Prop} {v : M K I}
    (hv : v ∈ Msupp P N) (zero : motive 0) (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul : ∀ (r : K) x, motive x → motive (r • x))
    (basis : ∀ u w : FreeMonoid I, wt w + N = wt u + P → motive (tm (word u) (word w))) :
    motive v := by
  rw [Msupp, Finsupp.supported_eq_span_single] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    show motive (Finsupp.single p 1)
    rw [single_eq_tm]
    exact basis p.1 p.2 hp
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul r x _ hx => exact smul r x hx

theorem tm_mem_Msupp {P N : Multiset I} {u w : FreeMonoid I} (h : wt w + N = wt u + P) :
    tm (word u : PreF K I) (word w) ∈ Msupp P N := by
  rw [tm_word_word]
  exact Finsupp.single_mem_supported K _ h

theorem Fop_mem_Msupp (j : I) {P N : Multiset I} {v : M K I} (hv : v ∈ Msupp P N) :
    Fop j v ∈ Msupp P (j ::ₘ N) := by
  refine Msupp_induction (motive := fun v => Fop j v ∈ Msupp P (j ::ₘ N)) hv (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
    (fun r x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ _ hx)
    fun u w h => ?_
  beta_reduce
  rw [Fop_tm, θ, ← word_mul]
  refine tm_mem_Msupp ?_
  rw [wt_mul, wt_of, ← Multiset.singleton_add, add_left_comm, h]
  abel

theorem Eop_mem_Msupp (ℓ : I → ℤ) (i : I) {P N : Multiset I} {v : M K I} (hv : v ∈ Msupp P N) :
    Eop C q ℓ i v ∈ Msupp (i ::ₘ P) N := by
  refine Msupp_induction (motive := fun v => Eop C q ℓ i v ∈ Msupp (i ::ₘ P) N) hv (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
    (fun r x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ _ hx)
    fun u w h => ?_
  beta_reduce
  rw [Eop_tm_word]
  refine add_mem ?_ ?_
  · rw [θ, ← word_mul]
    refine tm_mem_Msupp ?_
    rw [wt_mul, wt_of, ← Multiset.singleton_add, add_assoc, h]
    abel
  · have h1 := tm_mem_supported (D_word_mem_supp (C := C) (q := q) i (ℓ i + msA C i (wt w)) u) w
    refine Finsupp.supported_mono ?_ h1
    rintro ⟨u', w'⟩ ⟨hu', rfl⟩
    simp only [Set.mem_setOf_eq] at hu' ⊢
    rw [h, ← hu', Multiset.cons_add, Multiset.add_cons]

/-- `NF(E_w 1_λ)` lies in the weight space of `w`. -/
theorem NF_mem_Msupp (ℓ : I → ℤ) (w : List (Bool × I)) :
    NF C q ℓ (ew w) ∈ Msupp (posMS w) (negMS w) := by
  induction w with
  | nil =>
    rw [ew_nil, NF_apply, map_one, Module.End.one_apply, vac_eq, ← word_one]
    exact tm_mem_Msupp (by simp)
  | cons l w ih =>
    obtain ⟨b, i⟩ := l
    rw [NF_ew_cons]
    cases b
    · simpa using Fop_mem_Msupp i ih
    · simpa using Eop_mem_Msupp ℓ i ih

/-- On the weight space of signed weight `P - N`, `E_iF_j - F_jE_i` acts by
`δ_{ij} [⟨i, λ + P - N⟩]_i`. -/
theorem Eop_Fop_sub (ℓ : I → ℤ) (i j : I) {P N : Multiset I} {v : M K I} (hv : v ∈ Msupp P N) :
    Eop C q ℓ i (Fop j v) - Fop j (Eop C q ℓ i v) =
      if j = i then qbr (qi C q i) (ℓ i + msA C i P - msA C i N) • v else 0 := by
  refine Msupp_induction (motive := fun v => Eop C q ℓ i (Fop j v) - Fop j (Eop C q ℓ i v) =
      if j = i then qbr (qi C q i) (ℓ i + msA C i P - msA C i N) • v else 0) hv (by simp)
    (fun x y hx hy => by
      beta_reduce at hx hy ⊢
      rw [map_add, map_add, map_add, map_add, add_sub_add_comm, hx, hy]
      split_ifs <;> simp [smul_add])
    (fun r x hx => by
      beta_reduce at hx ⊢
      rw [map_smul, map_smul, map_smul, map_smul, ← smul_sub, hx]
      split_ifs <;> simp [smul_comm r])
    fun u w h => ?_
  beta_reduce
  rw [Fop_tm, Eop_tm_word, Eop_tm_word, map_add, Fop_tm, Fop_tm, D_word_mul_θ, map_add,
    LinearMap.add_apply]
  have hw : msA C i (wt w) - msA C i (wt u) = msA C i P - msA C i N := by
    have := congrArg (msA C i) h
    simp only [msA_add] at this
    linarith
  split_ifs with hji
  · rw [map_smul, LinearMap.smul_apply]
    have e : ℓ i + msA C i (wt w) - msA C i (wt u) = ℓ i + msA C i P - msA C i N := by
      linarith
    rw [e]; abel
  · simp

/-- **`NF` kills the commutation relators** (KL III eq. (2.4)):
`NF(E_{a (+i)(-j) b}) = NF(E_{a (-j)(+i) b}) + δ_{ij} [⟨i, λ + b_X⟩]_i NF(E_{ab})`. -/
theorem NF_comm (ℓ : I → ℤ) (a b : List (Bool × I)) (i j : I) :
    NF C q ℓ (ew (a ++ (true, i) :: (false, j) :: b)) =
      NF C q ℓ (ew (a ++ (false, j) :: (true, i) :: b)) +
        if j = i then qbr (qi C q i) (wl C ℓ b i) • NF C q ℓ (ew (a ++ b)) else 0 := by
  rw [NF_ew_append, NF_ew_append, NF_ew_append, NF_ew_cons, NF_ew_cons, NF_ew_cons,
    NF_ew_cons]
  change act C q ℓ (ew a) (Eop C q ℓ i (Fop j _)) =
    act C q ℓ (ew a) (Fop j (Eop C q ℓ i _)) + _
  rw [← sub_eq_iff_eq_add', ← map_sub, Eop_Fop_sub ℓ i j (NF_mem_Msupp ℓ b), wl, aS_eq,
    ← add_sub_assoc]
  split_ifs <;> simp

end UDot

end Categorification.QuantumGroup

end
