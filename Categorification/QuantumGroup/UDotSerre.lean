/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotSerreF

/-!
# The form on `'U 1_λ` kills the defining relations of `U̇ 1_λ`

Khovanov–Lauda III, arXiv:0807.3250v1, §2.1.3: `U̇ 1_λ` is the quotient of `'U 1_λ = Free` by
the subspace `UDot.Lrel C q ℓ` spanned by the elements `E_a · r · E_b 1_λ`, where `r` is one of
the defining relators of `U̇` inserted at the weight `λ + b_X`:

* `E_iF_j - F_jE_i - δ_{ij} [⟨i, λ + b_X⟩]_i` (KL III eq. (2.4); `UDot.commRel`),
* `Σ_{a+b=N} (-1)^a E_i^{(a)} E_j E_i^{(b)}` and `Σ_{a+b=N} (-1)^a F_i^{(a)} F_j F_i^{(b)}`
  (`i ≠ j`, `N = 1 - ⟨i, j_X⟩`; KL III §2.1.1 (v)).

(The relations (2.2), (2.3) involving the idempotents are built into the weight bookkeeping.)
We show that the form `UDot.B` of `Categorification.QuantumGroup.UDotForm` vanishes on
`Lrel` in either argument (`UDot.B_Lrel_right`, `UDot.B_Lrel_left`):

* the commutation relators by `UDot.B_comm_right`;
* the `F`-Serre relators because the normal form of `E_a F_S E_b 1_λ` lies in `(ℐ_S ⊗ 'f)`
  for the Serre ideal `ℐ_S = UDot.Jf`, which is stable under the operators of the model and is
  killed by `ε` (it lies in the radical of the form on `'f`);
* the `E`-Serre relators by symmetry and property (iii), which turn `E_S` into `F_S`
  (`ρ̄(E_S 1_μ)` is a multiple of `F_{S^{rev}} 1_{μ+…}`).

Throughout, `q` is not a root of unity.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF Finset

namespace UDot

variable {I : Type*} {K : Type*} [Field K] {C : CartanDatum I} {q : Kˣ} {c : I → K}

/-! ### The Serre subspace of the model -/

variable (C q) in
/-- The subspace `ℐ_S ⊗ 'f` of `M`. -/
def Wsub : Submodule K (M K I) :=
  Submodule.span K {v | ∃ x ∈ Jf C q, ∃ b : FreeMonoid I, v = tm x (word b)}

theorem tm_mem_Wsub {x : PreF K I} (hx : x ∈ Jf C q) (y : PreF K I) : tm x y ∈ Wsub C q := by
  induction y using induction_linear with
  | zero => simp
  | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'
  | smul_word b r => rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, b, rfl⟩)

theorem Wsub_induction {motive : M K I → Prop} {v : M K I} (hv : v ∈ Wsub C q) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y)) (smul : ∀ (r : K) x, motive x → motive (r • x))
    (gen : ∀ x ∈ Jf C q, ∀ b : FreeMonoid I, motive (tm x (word b))) : motive v := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨x, hx, b, rfl⟩ := hv; exact gen x hx b
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul r x _ hx => exact smul r x hx

theorem Fop_mem_Wsub (j : I) {v : M K I} (hv : v ∈ Wsub C q) : Fop j v ∈ Wsub C q := by
  refine Wsub_induction (motive := fun v => Fop j v ∈ Wsub C q) hv (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
    (fun r x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ _ hx)
    fun x hx b => ?_
  beta_reduce
  rw [Fop_tm]
  exact tm_mem_Wsub (Jf_mul_right hx _) _

theorem Eop_mem_Wsub (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) (i : I) {v : M K I}
    (hv : v ∈ Wsub C q) : Eop C q ℓ i v ∈ Wsub C q := by
  refine Wsub_induction (motive := fun v => Eop C q ℓ i v ∈ Wsub C q) hv (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
    (fun r x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ _ hx)
    fun x hx b => ?_
  beta_reduce
  rw [Eop_tm_word]
  exact add_mem (tm_mem_Wsub hx _) (tm_mem_Wsub (D_mem_Jf hq i _ hx) _)

theorem act_ew_mem_Wsub (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) (w : List (Bool × I))
    {v : M K I} (hv : v ∈ Wsub C q) : act C q ℓ (ew w) v ∈ Wsub C q := by
  induction w with
  | nil => simpa using hv
  | cons l w ih =>
    rw [act_ew_cons, Module.End.mul_apply]
    obtain ⟨b, i⟩ := l
    cases b
    · exact Fop_mem_Wsub i ih
    · exact Eop_mem_Wsub hq ℓ i ih

theorem act_mem_Wsub (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) (x : Free K I)
    {v : M K I} (hv : v ∈ Wsub C q) : act C q ℓ x v ∈ Wsub C q := by
  induction x using Free.induction with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply]; exact add_mem hx hy
  | smul_ew w r =>
    rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ (act_ew_mem_Wsub hq ℓ w hv)

theorem ε_eq_zero_of_mem_Wsub (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) {v : M K I}
    (hv : v ∈ Wsub C q) : ε C q c ℓ v = 0 := by
  refine Wsub_induction (motive := fun v => ε C q c ℓ v = 0) hv (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, add_zero])
    (fun r x hx => by beta_reduce at hx ⊢; rw [map_smul, hx, smul_zero]) fun x hx b => ?_
  beta_reduce
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, a', i, j, hij, rfl⟩ := hz
    have hg : word a * serreDiv C.dot q i j (C.serreN i j) * word a' ∈
        grade K (wt a + (j ::ₘ Multiset.replicate (C.serreN i j) i) + wt a') :=
      SetLike.mul_mem_graded (SetLike.mul_mem_graded (word_mem_grade a)
        (serreDiv_mem_grade C q i j _)) (word_mem_grade a')
    rw [ε_tm_of_mem_grade ℓ hg, fF, (mem_radical_iff' C.symm).1
      (Jf_le_radical hq c (mul_serreDiv_mul_mem_Jf hij _ _)), mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, LinearMap.smul_apply, map_smul, hx, smul_zero]

theorem act_negF_tm (ℓ : I → ℤ) (T x y : PreF K I) :
    act C q ℓ (negF T) (tm x y) = tm (x * rev T) y := by
  induction T using induction_linear with
  | zero => simp
  | add T T' hT hT' => rw [map_add, map_add, LinearMap.add_apply, hT, hT', map_add, mul_add,
      map_add, LinearMap.add_apply]
  | smul_word u r =>
    rw [map_smul, map_smul, LinearMap.smul_apply, negF_word, act_negW_tm, map_smul, mul_smul_comm,
      map_smul, LinearMap.smul_apply, rev_word]
    rfl

theorem act_negF_mem_Wsub (ℓ : I → ℤ) {T : PreF K I} (hT : rev T ∈ Jf C q) (v : M K I) :
    act C q ℓ (negF T) v ∈ Wsub C q := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | single p r =>
    rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, single_eq_tm, act_negF_tm]
    exact Submodule.smul_mem _ _ (tm_mem_Wsub (Jf_mul_left hT _) _)

/-- `φ` kills `x F_T y` whenever `T^{rev}` lies in the Serre ideal. -/
theorem φ_negF_eq_zero (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) {T : PreF K I}
    (hT : rev T ∈ Jf C q) (x y : Free K I) : φ C q c ℓ (x * negF T * y) = 0 := by
  rw [φ_apply, mul_assoc, NF_mul, NF_mul]
  exact ε_eq_zero_of_mem_Wsub hq ℓ (act_mem_Wsub hq ℓ x (act_negF_mem_Wsub ℓ hT _))

/-! ### Graded pieces of `Free` -/

variable (I K) in
/-- The span of the `E_w` with `posMS w = P` and `negMS w = N` (signed weight `P - N`). -/
def Fg (P N : Multiset I) : Submodule K (Free K I) :=
  supp {w : FreeMonoid (Bool × I) | posMS w.toList = P ∧ negMS w.toList = N}

theorem ew_mem_Fg (t : List (Bool × I)) : (ew t : Free K I) ∈ Fg I K (posMS t) (negMS t) :=
  word_mem_supp (by simp)

/-- A bilinear-style closure lemma: products of supported elements. -/
theorem supp_mul_mem {S T U : Set (FreeMonoid (Bool × I))}
    (h : ∀ u ∈ S, ∀ w ∈ T, u * w ∈ U) {x y : Free K I}
    (hx : x ∈ (supp S : Submodule K (Free K I))) (hy : y ∈ (supp T : Submodule K (Free K I))) :
    x * y ∈ (supp U : Submodule K (Free K I)) := by
  have h1 : ∀ u ∈ S, (word u : Free K I) * y ∈ (supp U : Submodule K (Free K I)) := by
    intro u hu
    refine map_supp_le (LinearMap.mulLeft K (word u)) (fun w hw => ?_) y hy
    rw [LinearMap.mulLeft_apply, ← word_mul]
    exact word_mem_supp (h u hu w hw)
  have := map_supp_le (T := U) (LinearMap.mulRight K y) (fun u hu => by
    rw [LinearMap.mulRight_apply]; exact h1 u hu)
  exact this x hx

theorem Fg_mul {P N P' N' : Multiset I} {x y : Free K I} (hx : x ∈ Fg I K P N)
    (hy : y ∈ Fg I K P' N') : x * y ∈ Fg I K (P + P') (N + N') := by
  refine supp_mul_mem (fun u hu w hw => ?_) hx hy
  simp only [Set.mem_setOf_eq, FreeMonoid.toList_mul, posMS_append, negMS_append] at hu hw ⊢
  rw [hu.1, hu.2, hw.1, hw.2]; exact ⟨rfl, rfl⟩

/-- A linear map out of `'f` sending the words of `S` into a submodule `T` sends `supp S` into
`T`. -/
theorem map_supp_le' {N : Type*} [AddCommGroup N] [Module K N] (φ : PreF K I →ₗ[K] N)
    {S : Set (FreeMonoid I)} {T : Submodule K N} (h : ∀ w ∈ S, φ (word w) ∈ T) :
    ∀ x ∈ (supp S : Submodule K (PreF K I)), φ x ∈ T := by
  intro x hx
  have : supp S ≤ T.comap φ := by
    rw [supp_eq_span, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  exact this hx

theorem negF_mem_Fg {ν : Multiset I} {x : PreF K I} (hx : x ∈ grade K ν) :
    negF x ∈ Fg I K 0 ν := by
  refine map_supp_le' negF.toLinearMap (fun u hu => ?_) x hx
  simp only [Set.mem_setOf_eq] at hu
  rw [AlgHom.toLinearMap_apply, negF_word]
  refine word_mem_supp ?_
  simp [← hu, wt]

theorem posF_mem_Fg {ν : Multiset I} {x : PreF K I} (hx : x ∈ grade K ν) :
    posF x ∈ Fg I K ν 0 := by
  refine map_supp_le' posF.toLinearMap (fun u hu => ?_) x hx
  simp only [Set.mem_setOf_eq] at hu
  rw [AlgHom.toLinearMap_apply, posF_word]
  refine word_mem_supp ?_
  simp [← hu, wt]

/-! ### `ρ̄` on graded pieces -/

theorem rhoE_of_mem_Fg (ℓ : I → ℤ) (b : Bool) (i : I) {P N : Multiset I} {y : Free K I}
    (hy : y ∈ Fg I K P N) :
    rhoE C q ℓ (b, i) y =
      qp q (di C i * (1 - sgn b * (ℓ i + msA C i P - msA C i N))) • (ew [(!b, i)] * y) := by
  refine eqOn_supp (rhoE C q ℓ (b, i))
    (qp q (di C i * (1 - sgn b * (ℓ i + msA C i P - msA C i N))) •
      LinearMap.mulLeft K (ew [(!b, i)])) (fun w hw => ?_) y hy
  simp only [Set.mem_setOf_eq] at hw
  rw [word_eq_ew, rhoE_ew, LinearMap.smul_apply, LinearMap.mulLeft_apply, ← ew_cons, wl, aS_eq,
    hw.1, hw.2, add_sub_assoc]

theorem R_of_mem_Fg (ℓ : I → ℤ) (s : List (Bool × I)) {P N : Multiset I} {y : Free K I}
    (hy : y ∈ Fg I K P N) :
    R C q ℓ s y = qp q (rcx C (fun k => ℓ k + msA C k P - msA C k N) s) • (ew (ρW s) * y) := by
  induction s generalizing P N y with
  | nil => simp [R, rcx]
  | cons l s ih =>
    obtain ⟨b, i⟩ := l
    have hy' := Fg_mul (ew_mem_Fg [(!b, i)]) hy
    simp only [R, LinearMap.comp_apply]
    rw [rhoE_of_mem_Fg ℓ b i hy, map_smul, ih hy', smul_smul, ← qp_add, rcx, ρW_cons, ew_append,
      mul_assoc]
    congr 3
    congr 1
    funext k
    cases b <;> simp [msA_singleton] <;> ring

theorem B_eq_φ_R (ℓ : I → ℤ) (s : List (Bool × I)) (y : Free K I) :
    B C q c ℓ (ew s) y = φ C q c ℓ (R C q ℓ s y) := by
  have h := B_append (C := C) (q := q) (c := c) ℓ s [] y
  rw [List.append_nil, ew_nil, B_one_left] at h
  exact h

theorem B_ew_mul_left (ℓ : I → ℤ) (a : List (Bool × I)) (Y z : Free K I) :
    B C q c ℓ (ew a * Y) z = B C q c ℓ Y (R C q ℓ a z) := by
  induction Y using Free.induction with
  | zero => simp
  | add Y Y' hY hY' => rw [mul_add, map_add, LinearMap.add_apply, hY, hY', map_add,
      LinearMap.add_apply]
  | smul_ew s r => rw [mul_smul_comm, map_smul, LinearMap.smul_apply, ← ew_append, B_append,
      map_smul, LinearMap.smul_apply]

/-! ### The Serre relators -/

/-- `F`-Serre relators are killed in the second argument. -/
theorem B_negF_right (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) (x : Free K I)
    {T : PreF K I} {ν : Multiset I} (hTg : T ∈ grade K ν) (hT : rev T ∈ Jf C q)
    (a b : List (Bool × I)) : B C q c ℓ x (ew a * negF T * ew b) = 0 := by
  induction x using Free.induction with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | smul_ew s r =>
    rw [map_smul, LinearMap.smul_apply, B_eq_φ_R,
      R_of_mem_Fg ℓ s (Fg_mul (Fg_mul (ew_mem_Fg a) (negF_mem_Fg hTg)) (ew_mem_Fg b)), map_smul,
      ← mul_assoc, ← mul_assoc, φ_negF_eq_zero hq ℓ hT, smul_zero, smul_zero]

variable (C) in
/-- The exponent `rcx m (+ν)` for a multiset `ν` (it only depends on `ν`). -/
def rcxP (m : I → ℤ) (ν : Multiset I) : ℤ := rcx C m (posW ν.toList)

theorem rcx_posW_eq (m : I → ℤ) (u : List I) : rcx C m (posW u) = rcxP C m u := by
  have h1 := rcx_posW C m u
  have h2 := rcx_posW C m (u : Multiset I).toList
  rw [Multiset.coe_toList] at h2
  unfold rcxP
  omega

theorem R_posW_ew (ℓ : I → ℤ) (u : FreeMonoid I) (t : List (Bool × I)) :
    R C q ℓ (posW u.toList) (ew t) =
      qp q (rcxP C (wl C ℓ t) (wt u)) • (negF (rev (word u : PreF K I)) * ew t) := by
  have hw : wl C ℓ t = fun k => ℓ k + msA C k (posMS t) - msA C k (negMS t) := by
    funext k; rw [wl, aS_eq, add_sub_assoc]
  rw [R_of_mem_Fg ℓ _ (ew_mem_Fg t), rcx_posW_eq, rev_word, negF_word, ρW_posW, hw]
  rfl

/-- `E`-Serre relators are killed in the first argument (after moving the prefix). -/
theorem B_posF_left (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) {T : PreF K I}
    {ν : Multiset I} (hTg : T ∈ grade K ν) (hT : T ∈ Jf C q) (b : List (Bool × I))
    (z : Free K I) : B C q c ℓ (posF T * ew b) z = 0 := by
  induction z using Free.induction with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, add_zero]
  | smul_ew t r =>
    rw [map_smul]
    have key : ∀ T' ∈ grade K ν, B C q c ℓ (posF T' * ew b) (ew t) =
        qp q (rcxP C (wl C ℓ t) ν) * B C q c ℓ (ew b) (negF (rev T') * ew t) := by
      intro T' hT'
      refine eqOn_supp ((B C q c ℓ).flip (ew t) ∘ₗ LinearMap.mulRight K (ew b) ∘ₗ
          posF.toLinearMap)
        (qp q (rcxP C (wl C ℓ t) ν) • (B C q c ℓ (ew b) ∘ₗ LinearMap.mulRight K (ew t) ∘ₗ
          negF.toLinearMap ∘ₗ rev)) (fun u hu => ?_) T' hT'
      simp only [Set.mem_setOf_eq] at hu
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
        LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [posF_word, ← ew_append, B_append, R_posW_ew, map_smul, smul_eq_mul, hu]
    rw [key T hTg]
    have h := B_negF_right (c := c) hq ℓ (ew b) (rev_mem_supp (P := (· = ν)) hTg)
      (by rw [rev_rev]; exact hT) [] t
    rw [ew_nil, one_mul] at h
    rw [h, mul_zero, smul_zero]

/-- `E`-Serre relators are killed in the second argument. -/
theorem B_posF_right (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) (x : Free K I)
    {T : PreF K I} {ν : Multiset I} (hTg : T ∈ grade K ν) (hT : T ∈ Jf C q)
    (a b : List (Bool × I)) : B C q c ℓ x (ew a * posF T * ew b) = 0 := by
  rw [B_symm, mul_assoc, B_ew_mul_left, B_posF_left hq ℓ hTg hT]

theorem serreKL_mem_grade (i j : I) :
    serreKL C q i j ∈ grade K (j ::ₘ Multiset.replicate (C.serreN i j) i) := by
  rw [serreKL_eq]; exact Submodule.smul_mem _ _ (serreDiv_mem_grade C q i j _)

theorem serreKL_mem_Jf {i j : I} (hij : i ≠ j) : serreKL C q i j ∈ Jf C q := by
  rw [serreKL_eq]
  refine Submodule.smul_mem _ _ ?_
  have := mul_serreDiv_mul_mem_Jf (C := C) (q := q) hij 1 1
  rwa [one_mul, mul_one] at this

theorem rev_serreKL_mem_Jf {i j : I} (hij : i ≠ j) : rev (serreKL C q i j) ∈ Jf C q := by
  rw [rev_serreKL]
  have := mul_serreDiv_mul_mem_Jf (C := C) (q := q) hij 1 1
  rwa [one_mul, mul_one] at this

/-! ### The relators of `U̇ 1_λ` -/

variable (C q) in
/-- The commutation relator `E_iF_j - F_jE_i - δ_{ij} [⟨i, λ + b_X⟩]_i` (KL III eq. (2.4)), to be
inserted in front of `E_b 1_λ`. -/
def commRel (ℓ : I → ℤ) (b : List (Bool × I)) (i j : I) : Free K I :=
  ew [(true, i), (false, j)] - ew [(false, j), (true, i)] -
    (if j = i then qbr (qi C q i) (wl C ℓ b i) else 0) • 1

variable (C q) in
/-- The generators `E_a · r · E_b 1_λ` of the relations of `U̇ 1_λ` (KL III §2.1.1 and
eq. (2.4)). -/
def relSet (ℓ : I → ℤ) : Set (Free K I) :=
  {z | ∃ a b i j, z = ew a * commRel C q ℓ b i j * ew b} ∪
    {z | ∃ a b i j, i ≠ j ∧
      (z = ew a * posF (serreKL C q i j) * ew b ∨ z = ew a * negF (serreKL C q i j) * ew b)}

variable (C q) in
/-- The relations of `U̇ 1_λ`: `U̇ 1_λ = 'U 1_λ / Lrel`. -/
def Lrel (ℓ : I → ℤ) : Submodule K (Free K I) := Submodule.span K (relSet C q ℓ)

theorem ew_mul_commRel_mul (ℓ : I → ℤ) (a b : List (Bool × I)) (i j : I) :
    ew a * commRel C q ℓ b i j * ew b =
      ew (a ++ (true, i) :: (false, j) :: b) - ew (a ++ (false, j) :: (true, i) :: b) -
        (if j = i then qbr (qi C q i) (wl C ℓ b i) else 0) • ew (a ++ b) := by
  simp only [commRel, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, ← ew_append,
    List.append_assoc, List.cons_append, List.nil_append]

/-- **The form kills the relations of `U̇ 1_λ`** (second argument). -/
theorem B_Lrel_right (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) (x : Free K I) {y : Free K I}
    (hy : y ∈ Lrel C q ℓ) : B C q c ℓ x y = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨a, b, i, j, rfl⟩ | ⟨a, b, i, j, hij, rfl | rfl⟩
    · rw [ew_mul_commRel_mul, map_sub, map_sub, map_smul, B_comm_right]
      split_ifs <;> simp
    · exact B_posF_right hq ℓ x (serreKL_mem_grade i j) (serreKL_mem_Jf hij) a b
    · exact B_negF_right hq ℓ x (serreKL_mem_grade i j) (rev_serreKL_mem_Jf hij) a b
  | zero => simp
  | add y y' _ _ hy hy' => rw [map_add, hy, hy', add_zero]
  | smul r y _ hy => rw [map_smul, hy, smul_zero]

/-- **The form kills the relations of `U̇ 1_λ`** (first argument). -/
theorem B_Lrel_left (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) {x : Free K I}
    (hx : x ∈ Lrel C q ℓ) (y : Free K I) : B C q c ℓ x y = 0 := by
  rw [B_symm]; exact B_Lrel_right hq ℓ y hx

end UDot

end Categorification.QuantumGroup

end
