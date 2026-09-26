/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotNondegForm
import Categorification.QuantumGroup.UDotFormNondeg
import Categorification.QuantumGroup.SerreDivided

/-!
# KL III Proposition 2.5: nondegeneracy of the forms on `U̇`

Khovanov–Lauda III, arXiv:0807.3250v1, §2.1.3, Proposition 2.5 (`prop_nondeg`): *the bilinear
form `( , )` and the semilinear form `⟨ , ⟩` are both nondegenerate on `U̇`.* KL III's proof is
a pointer to Lusztig, *Introduction to quantum groups*, Ch. 26 (Theorem 26.3.1, almost
orthonormality of the canonical basis of `U̇`). We give a direct proof, avoiding canonical
bases.

## Setting and the Gabber–Kac hypothesis

In this library `U̇ 1_λ` is *presented* (KL III §2.1.1–2.1.3): it is the free algebra `'U 1_λ`
on the signed letters modulo the commutation relations (2.4) and the quantum Serre relations
(`UDot.Lrel`), and `f` enters only through the Serre ideal `UDot.Jf ⊆ 'f`. Nondegeneracy of
`( , )` on the presented `U̇` forces every element `x` of the radical `ℐ` of the form on `'f` to
vanish in `U̇ 1_λ` as `x⁺ 1_λ` (indeed `(x⁺ 1_λ, -) = 0`, see `UDot.B_posF_radical`); with the
triangular decomposition of the presented algebra this is the quantum Gabber–Kac theorem
(Lusztig 33.1.3) `ℐ = Jf`. Gabber–Kac is not proved in this library, so the inclusion
`ℐ ⊆ Jf` is an explicit hypothesis `hGK` of the main theorems (the inclusion `Jf ⊆ ℐ` is
`UDot.Jf_le_radical`). No other hypothesis is used besides `q` not a root of unity and KL III's
normalisation `(θ_i, θ_i) = (1 - q_i²)⁻¹` (`hc`); the Cartan datum is arbitrary.

## Proof

1. (`Categorification.QuantumGroup.UDotNondegModel`, `…UDotNondegForm`) The *limit action* of
   `'U 1_λ` on `M = 'f ⊗ 'f`, from Lusztig's construction of `( , )` via
   `ᵚM(λ') ⊗ M(λ'')`, `λ', λ'' → ∞`, kills the commutation relators, and
   `(z, w) = ndP (ndNF z, ndNF w)` where `ndP` is the tensor square of the form on `'f`
   (`UDot.B_eq_ndP`). This is proved by the uniqueness argument of KL III Prop. 2.2 at the level
   of the free algebra.
2. (`UDot.ndT_sub_mem_Mlow`, `UDot.ndNF_surjective`) On the normal-ordered monomials
   `F_x E_y 1_λ` (`UDot.Nmap`), `ndNF` is unitriangular: `ndNF (F_x E_y 1_λ) = x ⊗ y + (terms with
   a shorter first factor)`. In particular `ndNF` is onto.
3. (`UDot.mem_Wof_radical_of_ndP`) The left radical of `ndP` is `ℐ ⊗ 'f + 'f ⊗ ℐ`
   (linear algebra over a field).
4. (`UDot.mem_Wof_of_ndT`) If `z = Σ F_x E_y 1_λ` (normal ordered, `z = Nmap m`) lies in the
   radical of `( , )` then, by induction on the length of the first factor using 2 and 3,
   `m ∈ ℐ ⊗ 'f + 'f ⊗ ℐ ⊆ Jf ⊗ 'f + 'f ⊗ Jf` (using `hGK`), so `z` lies in the span of the Serre
   relators. Together with normal ordering this shows that the radical of `( , )` on `'U 1_λ`
   is exactly `Lrel` (`UDot.mem_Lrel_of_B`).

## Main results

* **`UDot.mem_Lrel_of_B`** — the left radical of `( , )` on `'U 1_λ` is `Lrel`;
* **`UDot.formU_nondegenerate`** — `( , )` is nondegenerate on each block `U̇ 1_λ`;
* **`UDot.nondegenerate_formUD`** — KL III Prop. 2.5 for `( , )` on `U̇`;
* **`UDot.nondegenerate_hform`**, `UDot.hform_block_nondegenerate` — KL III Prop. 2.5 for
  `⟨ , ⟩` on `U̇` (and blockwise);
* **`UDot.KL3.formNondeg`**, **`UDot.KL3.prop_2_5`** — the statement
  `UDot.KL3.FormNondeg RD` of `Categorification.QuantumGroup.UDotFormNondeg` (and the
  `⟨ , ⟩` half) over `ℚ(q)` in KL III's normalisation, for every root datum, from `ℐ ⊆ Jf`;
* `UDot.radK_le_Jf_of_gabberKac`, **`UDot.KL3.formNondeg_of_gabberKac`** — for simply-laced
  data (in particular `sl_n`) the hypothesis follows from the library's `PreF.GabberKac`;
* `UDot.B_posF_radical` — the Gabber–Kac hypothesis cannot be dropped from the presented `U̇`:
  `(x⁺ 1_λ, -) = 0` for `x ∈ ℐ`.

In rank one (`U̇(sl₂)`) the hypothesis holds and Prop. 2.5 is proved unconditionally in
`Categorification.QuantumGroup.UDotNondegRankOne`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K] {C : CartanDatum I} {q : Kˣ} {c : I → K}

/-! ### Subspaces `S ⊗ 'f + 'f ⊗ S` of the model -/

/-- `S ⊗ 'f + 'f ⊗ S ⊆ M`. -/
def Wof (S : Submodule K (PreF K I)) : Submodule K (M K I) :=
  Submodule.span K {v | ∃ x y, (x ∈ S ∨ y ∈ S) ∧ v = tm x y}

theorem tm_mem_Wof_left {S : Submodule K (PreF K I)} {x : PreF K I} (hx : x ∈ S) (y : PreF K I) :
    tm x y ∈ Wof S := Submodule.subset_span ⟨x, y, Or.inl hx, rfl⟩

theorem tm_mem_Wof_right {S : Submodule K (PreF K I)} (x : PreF K I) {y : PreF K I} (hy : y ∈ S) :
    tm x y ∈ Wof S := Submodule.subset_span ⟨x, y, Or.inr hy, rfl⟩

theorem Wof_mono {S T : Submodule K (PreF K I)} (h : S ≤ T) : Wof S ≤ Wof T := by
  refine Submodule.span_mono ?_
  rintro _ ⟨x, y, hxy, rfl⟩
  exact ⟨x, y, hxy.imp (fun hx => h hx) (fun hy => h hy), rfl⟩

variable (C q c) in
/-- The radical `ℐ` of the form on `'f`, as a `K`-subspace. -/
abbrev radK : Submodule K (PreF K I) := (radical C.dot q⁻¹ c).restrictScalars K

theorem mem_radK {x : PreF K I} : x ∈ radK C q c ↔ ∀ y, fF C q c x y = 0 := Iff.rfl

/-! ### The left radical of `ndP` -/

/-- Linear algebra: if `Σ_{i ∈ s} (X_i, a) Y_i ∈ ℐ` for every `a`, then
`Σ_{i ∈ s} X_i ⊗ Y_i ∈ ℐ ⊗ 'f + 'f ⊗ ℐ`. -/
theorem sum_tm_mem_Wof {ι : Type*} (s : Finset ι) (X Y : ι → PreF K I)
    (h : ∀ a : PreF K I, ∑ i ∈ s, fF C q c (X i) a • Y i ∈ radK C q c) :
    ∑ i ∈ s, tm (X i) (Y i) ∈ Wof (radK C q c) := by
  induction s using Finset.strongInduction generalizing X with
  | H s ih =>
  by_cases hdep : ∃ g : ι → K, ∑ i ∈ s, g i • Y i ∈ radK C q c ∧ ∃ i ∈ s, g i ≠ 0
  · obtain ⟨g, hg, i0, hi0, hgi0⟩ := hdep
    set s' := s.erase i0
    set ρ : PreF K I := ∑ i ∈ s, (g i / g i0) • Y i
    have hρ : ρ ∈ radK C q c := by
      have : ρ = (g i0)⁻¹ • ∑ i ∈ s, g i • Y i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, div_eq_inv_mul]
      rw [this]
      exact Submodule.smul_mem _ _ hg
    have hρs : ρ = Y i0 + ∑ j ∈ s', (g j / g i0) • Y j := by
      have := (Finset.add_sum_erase s (fun i => (g i / g i0) • Y i) hi0).symm
      rw [div_self hgi0, one_smul] at this
      exact this
    have hY0 : Y i0 = ρ - ∑ j ∈ s', (g j / g i0) • Y j := by rw [hρs]; abel
    set X' : ι → PreF K I := fun j => X j - (g j / g i0) • X i0
    have h1 : ∑ i ∈ s, tm (X i) (Y i) = tm (X i0) (Y i0) + ∑ j ∈ s', tm (X j) (Y j) :=
      (Finset.add_sum_erase s (fun i => tm (X i) (Y i)) hi0).symm
    have h2 : tm (X i0) (Y i0) = tm (X i0) ρ - ∑ j ∈ s', (g j / g i0) • tm (X i0) (Y j) := by
      rw [hY0, map_sub]
      congr 1
      rw [map_sum]
      simp only [map_smul]
    have h3 : ∑ j ∈ s', tm (X' j) (Y j) =
        ∑ j ∈ s', tm (X j) (Y j) - ∑ j ∈ s', (g j / g i0) • tm (X i0) (Y j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [X', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
    have hsum : ∑ i ∈ s, tm (X i) (Y i) = tm (X i0) ρ + ∑ j ∈ s', tm (X' j) (Y j) := by
      rw [h1, h2, h3]; abel
    rw [hsum]
    refine add_mem (tm_mem_Wof_right _ hρ) (ih s' (Finset.erase_ssubset hi0) X' fun a => ?_)
    have e1 : ∑ i ∈ s, fF C q c (X i) a • Y i =
        fF C q c (X i0) a • Y i0 + ∑ j ∈ s', fF C q c (X j) a • Y j :=
      (Finset.add_sum_erase s (fun i => fF C q c (X i) a • Y i) hi0).symm
    have e2 : ∑ j ∈ s', fF C q c (X' j) a • Y j =
        ∑ j ∈ s', fF C q c (X j) a • Y j -
          fF C q c (X i0) a • ∑ j ∈ s', (g j / g i0) • Y j := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [X', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        sub_smul, smul_smul]
      rw [mul_comm]
    have e : ∑ j ∈ s', fF C q c (X' j) a • Y j =
        ∑ i ∈ s, fF C q c (X i) a • Y i - fF C q c (X i0) a • ρ := by
      rw [e2, e1, hρs, smul_add]; abel
    rw [e]
    exact sub_mem (h a) (Submodule.smul_mem _ _ hρ)
  · push_neg at hdep
    refine Submodule.sum_mem _ fun i hi => tm_mem_Wof_left ?_ _
    rw [mem_radK]
    intro a
    exact hdep (fun i => fF C q c (X i) a) (h a) i hi

/-- **The left radical of `ndP` is `ℐ ⊗ 'f + 'f ⊗ ℐ`.** -/
theorem mem_Wof_radical_of_ndP {m : M K I} (h : ∀ v, ndP C q c m v = 0) :
    m ∈ Wof (radK C q c) := by
  have hm : m = ∑ p ∈ m.support, tm (m p • word p.1 : PreF K I) (word p.2) := by
    have h0 : m = ∑ p ∈ m.support, Finsupp.single p (m p) := (Finsupp.sum_single m).symm
    conv_lhs => rw [h0]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, LinearMap.smul_apply, tm_word_word, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hm]
  refine sum_tm_mem_Wof _ _ _ fun a => ?_
  rw [mem_radK]
  intro b
  have := h (tm a b)
  rw [hm, map_sum, LinearMap.sum_apply] at this
  simp only [ndP_tm] at this
  rw [map_sum, LinearMap.sum_apply]
  simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using this

/-! ### Normal-ordered monomials -/

/-- `x ⊗ y ↦ F_x E_y 1_λ` (for words `x = x₁ ⋯ xₘ`, `F_x = F_{x₁} ⋯ F_{xₘ}`). -/
def Nmap : M K I →ₗ[K] Free K I :=
  Finsupp.linearCombination K fun p =>
    ew (negW (FreeMonoid.toList p.1) ++ posW (FreeMonoid.toList p.2))

theorem Nmap_tm_word (u w : FreeMonoid I) :
    Nmap (tm (word u) (word w) : M K I) = negF (word u) * posF (word w) := by
  rw [tm_word_word, Nmap, Finsupp.linearCombination_single, one_smul, negF_word, posF_word,
    ew_append]

theorem Nmap_tm (x y : PreF K I) : Nmap (tm x y) = negF x * posF y := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [map_add, LinearMap.add_apply, map_add, hx, hx', map_add, add_mul]
  | smul_word u r =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, mul_add]
    | smul_word w s =>
      simp only [map_smul, LinearMap.smul_apply, Nmap_tm_word]
      rw [smul_mul_smul_comm, smul_smul, mul_comm s r]

/-- Normal ordering: every `z ∈ 'U 1_λ` is a combination of `F_x E_y 1_λ` modulo the
commutation relators. -/
theorem exists_Nmap (ℓ : I → ℤ) (z : Free K I) : ∃ m, z - Nmap m ∈ Lrel C q ℓ := by
  induction z using Free.induction with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨m', hm'⟩ := hy
    exact ⟨m + m', by rw [map_add]; convert add_mem hm hm' using 1; abel⟩
  | smul_ew w r =>
    suffices h : ∃ m, ew w - Nmap m ∈ Lrel C q ℓ by
      obtain ⟨m, hm⟩ := h
      exact ⟨r • m, by rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ hm⟩
    induction w using normal_induction with
    | hN c' b =>
      refine ⟨tm (word (FreeMonoid.ofList c')) (word (FreeMonoid.ofList b)), ?_⟩
      rw [tm_word_word, Nmap, Finsupp.linearCombination_single, one_smul,
        FreeMonoid.toList_ofList, FreeMonoid.toList_ofList, sub_self]
      exact Submodule.zero_mem _
    | hS a i j b h1 h2 =>
      obtain ⟨m1, hm1⟩ := h1
      obtain ⟨m2, hm2⟩ := h2
      set κ : K := if j = i then qbr (qi C q i) (wl C ℓ b i) else 0
      refine ⟨m1 + κ • m2, ?_⟩
      have hrel : ew a * commRel C q ℓ b i j * ew b ∈ Lrel C q ℓ :=
        Submodule.subset_span (Or.inl ⟨a, b, i, j, rfl⟩)
      rw [ew_mul_commRel_mul] at hrel
      have := add_mem (add_mem hrel hm1) (Submodule.smul_mem _ κ hm2)
      convert this using 1
      rw [map_add, map_smul, smul_sub]
      abel

/-- The Serre relators, with arbitrary left and right factors, lie in `Lrel`. -/
theorem mul_negF_serreKL_mul_mem (ℓ : I → ℤ) {i j : I} (hij : i ≠ j) (x y : Free K I) :
    x * negF (serreKL C q i j) * y ∈ Lrel C q ℓ := by
  induction x using Free.induction with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, add_mul]; exact add_mem hx hx'
  | smul_ew a r =>
    rw [smul_mul_assoc, smul_mul_assoc]
    refine Submodule.smul_mem _ _ ?_
    induction y using Free.induction with
    | zero => simp
    | add y y' hy hy' => rw [mul_add]; exact add_mem hy hy'
    | smul_ew b s =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨a, b, i, j, hij, Or.inr rfl⟩))

theorem mul_posF_serreKL_mul_mem (ℓ : I → ℤ) {i j : I} (hij : i ≠ j) (x y : Free K I) :
    x * posF (serreKL C q i j) * y ∈ Lrel C q ℓ := by
  induction x using Free.induction with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, add_mul]; exact add_mem hx hx'
  | smul_ew a r =>
    rw [smul_mul_assoc, smul_mul_assoc]
    refine Submodule.smul_mem _ _ ?_
    induction y using Free.induction with
    | zero => simp
    | add y y' hy hy' => rw [mul_add]; exact add_mem hy hy'
    | smul_ew b s =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨a, b, i, j, hij, Or.inl rfl⟩))

theorem serreDiv_eq_smul_serreKL (i j : I) :
    serreDiv C.dot q i j (C.serreN i j) = ((-1 : K) ^ C.serreN i j) • serreKL C q i j := by
  rw [serreKL_eq, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- `Nmap (Jf ⊗ 'f + 'f ⊗ Jf) ⊆ Lrel`. -/
theorem Nmap_Wof_Jf (ℓ : I → ℤ) {m : M K I} (hm : m ∈ Wof (Jf C q)) : Nmap m ∈ Lrel C q ℓ := by
  induction hm using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, y, hxy | hxy, rfl⟩ := hv
    · rw [Nmap_tm]
      induction hxy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, b, i, j, hij, rfl⟩ := hz
        rw [map_mul, map_mul, serreDiv_eq_smul_serreKL, map_smul]
        have e : negF (word a) * ((-1 : K) ^ C.serreN i j • negF (serreKL C q i j)) *
            negF (word b) * posF y = ((-1 : K) ^ C.serreN i j) •
              (negF (word a) * negF (serreKL C q i j) * (negF (word b) * posF y)) := by
          simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
        rw [e]
        exact Submodule.smul_mem _ _ (mul_negF_serreKL_mul_mem ℓ hij _ _)
      | zero => simp
      | add x x' _ _ hx hx' => rw [map_add, add_mul]; exact add_mem hx hx'
      | smul r x _ hx => rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
    · rw [Nmap_tm]
      induction hxy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, b, i, j, hij, rfl⟩ := hz
        rw [map_mul, map_mul, serreDiv_eq_smul_serreKL, map_smul]
        have e : negF x * (posF (word a) * ((-1 : K) ^ C.serreN i j • posF (serreKL C q i j)) *
            posF (word b)) = ((-1 : K) ^ C.serreN i j) •
              (negF x * posF (word a) * posF (serreKL C q i j) * posF (word b)) := by
          simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
        rw [e]
        exact Submodule.smul_mem _ _ (mul_posF_serreKL_mul_mem ℓ hij _ _)
      | zero => simp
      | add y y' _ _ hy hy' => rw [map_add, mul_add]; exact add_mem hy hy'
      | smul r y _ hy => rw [map_smul, mul_smul_comm]; exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-! ### Triangularity of the model normal form on normal-ordered monomials -/

theorem M_supported_induction {S : Set (FreeMonoid I × FreeMonoid I)} {motive : M K I → Prop}
    {v : M K I} (hv : v ∈ Finsupp.supported K K S) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul : ∀ (r : K) x, motive x → motive (r • x))
    (basis : ∀ u w : FreeMonoid I, (u, w) ∈ S → motive (tm (word u) (word w))) : motive v := by
  rw [Finsupp.supported_eq_span_single] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    show motive (Finsupp.single p 1)
    rw [single_eq_tm]
    exact basis p.1 p.2 hp
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul r x _ hx => exact smul r x hx

theorem Mlow_mono {k k' : ℕ} (h : k ≤ k') : (Mlow k : Submodule K (M K I)) ≤ Mlow k' :=
  Finsupp.supported_mono fun _ hp => lt_of_lt_of_le hp h

variable (C q) in
/-- `m ↦ ndNF (Nmap m)`: the model normal form of the normal-ordered element `Nmap m`. -/
def ndT (ℓ : I → ℤ) : M K I →ₗ[K] M K I := ndNF C q ℓ ∘ₗ Nmap

theorem ndT_tm_sub (ℓ : I → ℤ) (u w : FreeMonoid I) :
    ndT C q ℓ (tm (word u) (word w)) - tm (word u) (word w) ∈
      (Mlow (Multiset.card (wt u)) : Submodule K (M K I)) := by
  have h := ndAct_negW_tm (C := C) (q := q) ℓ (FreeMonoid.toList u) 1 w
  rw [ndT, LinearMap.comp_apply, tm_word_word, Nmap, Finsupp.linearCombination_single, one_smul,
    ndNF_ew_append, ndNF_posW, FreeMonoid.ofList_toList, ← word_one, ← tm_word_word]
  simpa [wt] using h

theorem ndT_sub_mem_Mlow (ℓ : I → ℤ) {k : ℕ} {m : M K I}
    (hm : m ∈ Finsupp.supported K K {p : FreeMonoid I × FreeMonoid I | Multiset.card (wt p.1) ≤ k}) :
    ndT C q ℓ m - m ∈ (Mlow k : Submodule K (M K I)) := by
  refine M_supported_induction (motive := fun m => ndT C q ℓ m - m ∈ (Mlow k : Submodule K (M K I)))
    hm (by simp) (fun x y hx hy => ?_) (fun r x hx => ?_) fun u w h => ?_
  · beta_reduce at *
    rw [map_add, add_sub_add_comm]; exact add_mem hx hy
  · beta_reduce at *
    rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ hx
  · beta_reduce at *
    exact Mlow_mono h (ndT_tm_sub ℓ u w)

theorem ndT_mem_Mlow (ℓ : I → ℤ) {k : ℕ} {m : M K I} (hm : m ∈ (Mlow k : Submodule K (M K I))) :
    ndT C q ℓ m ∈ (Mlow k : Submodule K (M K I)) := by
  refine Mlow_induction (motive := fun m => ndT C q ℓ m ∈ (Mlow k : Submodule K (M K I)))
    hm (by simp) (fun x y hx hy => ?_) (fun r x hx => ?_) fun u w h => ?_
  · beta_reduce at *
    rw [map_add]; exact add_mem hx hy
  · beta_reduce at *
    rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · beta_reduce at *
    have := add_mem (Mlow_mono h.le (ndT_tm_sub (C := C) (q := q) ℓ u w)) (tm_mem_Mlow h (word w))
    rwa [sub_add_cancel] at this

theorem ndP_Mlow_eq_zero {k : ℕ} {v : M K I} (hv : v ∈ (Mlow k : Submodule K (M K I)))
    {a : FreeMonoid I} (ha : Multiset.card (wt a) = k) (y : PreF K I) :
    ndP C q c v (tm (word a) y) = 0 := by
  refine Mlow_induction (motive := fun v => ndP C q c v (tm (word a) y) = 0) hv (by simp)
    (fun x y hx hy => ?_) (fun r x hx => ?_) fun u w h => ?_
  · beta_reduce at *
    rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  · beta_reduce at *
    rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  · beta_reduce at *
    rw [ndP_tm, fF_word_eq_zero (fun he => by rw [he] at h; omega), zero_mul]

theorem ndP_eq_zero_of_supported {k : ℕ} {v : M K I}
    (hv : v ∈ Finsupp.supported K K {p : FreeMonoid I × FreeMonoid I | Multiset.card (wt p.1) = k})
    {a : FreeMonoid I} (ha : Multiset.card (wt a) ≠ k) (y : PreF K I) :
    ndP C q c v (tm (word a) y) = 0 := by
  refine M_supported_induction (motive := fun v => ndP C q c v (tm (word a) y) = 0) hv (by simp)
    (fun x y hx hy => ?_) (fun r x hx => ?_) fun u w h => ?_
  · beta_reduce at *
    rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  · beta_reduce at *
    rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  · beta_reduce at *
    simp only [Set.mem_setOf_eq] at h
    rw [ndP_tm, fF_word_eq_zero (fun he => ha (by rw [← he, h])), zero_mul]

/-- **The model normal form is onto.** -/
theorem ndNF_surjective (ℓ : I → ℤ) : Function.Surjective (ndNF C q ℓ : Free K I → M K I) := by
  have key : ∀ n (u w : FreeMonoid I), Multiset.card (wt u) = n →
      tm (word u) (word w) ∈ LinearMap.range (ndNF C q ℓ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro u w hu
    have hlow : (Mlow n : Submodule K (M K I)) ≤ LinearMap.range (ndNF C q ℓ) := by
      intro v hv
      refine Mlow_induction (motive := fun v => v ∈ LinearMap.range (ndNF C q ℓ)) hv
        (Submodule.zero_mem _) (fun x y hx hy => add_mem hx hy)
        (fun r x hx => Submodule.smul_mem _ r hx) fun u' w' h => ih _ h u' w' rfl
    have h1 : ndT C q ℓ (tm (word u) (word w)) ∈ LinearMap.range (ndNF C q ℓ) :=
      ⟨_, rfl⟩
    have h2 := hlow (hu ▸ ndT_tm_sub (C := C) (q := q) ℓ u w)
    have := sub_mem h1 h2
    rwa [sub_sub_cancel] at this
  intro v
  refine M_induction (motive := fun v => ∃ z, ndNF C q ℓ z = v) v ⟨0, map_zero _⟩
    (fun x y ⟨z, hz⟩ ⟨z', hz'⟩ => ⟨z + z', by rw [map_add, hz, hz']⟩)
    (fun r x ⟨z, hz⟩ => ⟨r • z, by rw [map_smul, hz]⟩) fun u w => key _ u w rfl

/-! ### The radical -/

variable (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (hc : ∀ i, c i = (1 - ((qi C q i : Kˣ) : K) ^ 2)⁻¹)

include hq hc in
theorem ndP_ndT_Wof_Jf (ℓ : I → ℤ) {m : M K I} (hm : m ∈ Wof (Jf C q)) (v : M K I) :
    ndP C q c (ndT C q ℓ m) v = 0 := by
  obtain ⟨w, rfl⟩ := ndNF_surjective (C := C) (q := q) ℓ v
  rw [ndT, LinearMap.comp_apply, ← B_eq_ndP hc hq]
  exact B_Lrel_left hq ℓ (Nmap_Wof_Jf ℓ hm) w

include hq hc in
/-- **The key step.** If `ndP (ndNF (Nmap m), -) = 0` then `m ∈ Jf ⊗ 'f + 'f ⊗ Jf`, assuming the
Gabber–Kac inclusion `ℐ ⊆ Jf`. Induction on the length of the first tensor factor. -/
theorem mem_Wof_of_ndT (hGK : radK C q c ≤ Jf C q) (ℓ : I → ℤ) :
    ∀ (k : ℕ) (m : M K I), m ∈ (Mlow k : Submodule K (M K I)) →
      (∀ v, ndP C q c (ndT C q ℓ m) v = 0) → m ∈ Wof (Jf C q) := by
  intro k
  induction k with
  | zero =>
    intro m hm _
    have : m = 0 := by
      ext p
      by_contra hp
      have := (Finsupp.mem_supported K m).1 hm (Finsupp.mem_support_iff.2 hp)
      simp at this
    rw [this]; exact Submodule.zero_mem _
  | succ k ih =>
    intro m hm hT
    set mt := m.filter fun p => Multiset.card (wt p.1) = k
    set mr := m.filter fun p => ¬ Multiset.card (wt p.1) = k
    have hsplit : mt + mr = m := Finsupp.filter_pos_add_filter_neg _ _
    have hmt : mt ∈ Finsupp.supported K K
        {p : FreeMonoid I × FreeMonoid I | Multiset.card (wt p.1) = k} := by
      rw [Finsupp.mem_supported, Finsupp.support_filter]
      intro p hp
      exact (Finset.mem_filter.1 hp).2
    have hmt' : mt ∈ Finsupp.supported K K
        {p : FreeMonoid I × FreeMonoid I | Multiset.card (wt p.1) ≤ k} :=
      Finsupp.supported_mono (fun p (hp : p ∈ {p : FreeMonoid I × FreeMonoid I |
        Multiset.card (wt p.1) = k}) => show Multiset.card (wt p.1) ≤ k from le_of_eq hp) hmt
    have hmr : mr ∈ (Mlow k : Submodule K (M K I)) := by
      rw [Mlow, Finsupp.mem_supported, Finsupp.support_filter]
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      have := (Finsupp.mem_supported K m).1 hm hp1
      simp only [Set.mem_setOf_eq] at this ⊢
      omega
    -- the top part lies in the radical of `ndP`
    have htop : ∀ v, ndP C q c mt v = 0 := by
      intro v
      refine M_induction (motive := fun v => ndP C q c mt v = 0) v (by simp)
        (fun x y hx hy => by beta_reduce at *; rw [map_add, hx, hy, add_zero])
        (fun r x hx => by beta_reduce at *; rw [map_smul, hx, smul_zero]) fun a b => ?_
      beta_reduce
      by_cases ha : Multiset.card (wt a) = k
      · have h0 := hT (tm (word a) (word b))
        have e : ndT C q ℓ m = mt + (ndT C q ℓ mt - mt) + ndT C q ℓ mr := by
          rw [← hsplit, map_add]; abel
        rw [e, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
          ndP_Mlow_eq_zero (ndT_sub_mem_Mlow ℓ hmt') ha, ndP_Mlow_eq_zero (ndT_mem_Mlow ℓ hmr) ha,
          add_zero, add_zero] at h0
        exact h0
      · exact ndP_eq_zero_of_supported hmt ha _
    have hmtW : mt ∈ Wof (Jf C q) := Wof_mono hGK (mem_Wof_radical_of_ndP htop)
    have hmrW : mr ∈ Wof (Jf C q) := by
      refine ih mr hmr fun v => ?_
      have h1 := hT v
      rw [← hsplit, map_add, map_add, LinearMap.add_apply,
        ndP_ndT_Wof_Jf hq hc ℓ hmtW, zero_add] at h1
      exact h1
    rw [← hsplit]
    exact add_mem hmtW hmrW

theorem mem_Mlow_sup (m : M K I) :
    m ∈ (Mlow (m.support.sup (fun p => Multiset.card (wt p.1)) + 1) : Submodule K (M K I)) := by
  rw [Mlow, Finsupp.mem_supported]
  intro p hp
  simp only [Set.mem_setOf_eq]
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun p : FreeMonoid I × FreeMonoid I =>
    Multiset.card (wt p.1)) hp)

include hq hc in
/-- **The radical of `( , )` on `'U 1_λ` is exactly the span of the relations of `U̇ 1_λ`**
(for an arbitrary Cartan datum, `q` not a root of unity, KL III's normalisation of the form on
`'f`, and the Gabber–Kac inclusion `ℐ ⊆ Jf`). -/
theorem mem_Lrel_of_B (hGK : radK C q c ≤ Jf C q) (ℓ : I → ℤ) {z : Free K I}
    (hz : ∀ w, B C q c ℓ z w = 0) : z ∈ Lrel C q ℓ := by
  obtain ⟨m, hm⟩ := exists_Nmap (C := C) (q := q) ℓ z
  have hB : ∀ w, B C q c ℓ (Nmap m) w = 0 := by
    intro w
    have := B_Lrel_left (c := c) hq ℓ hm w
    rw [map_sub, LinearMap.sub_apply, hz, zero_sub, neg_eq_zero] at this
    exact this
  have hT : ∀ v, ndP C q c (ndT C q ℓ m) v = 0 := by
    intro v
    obtain ⟨w, rfl⟩ := ndNF_surjective (C := C) (q := q) ℓ v
    rw [ndT, LinearMap.comp_apply, ← B_eq_ndP hc hq]
    exact hB w
  have hW := mem_Wof_of_ndT hq hc hGK ℓ _ m (mem_Mlow_sup m) hT
  have := add_mem hm (Nmap_Wof_Jf ℓ hW)
  rwa [sub_add_cancel] at this

include hq hc in
/-- The Gabber–Kac hypothesis cannot be dropped: for `x` in the radical `ℐ` of the form on `'f`,
`x⁺ 1_λ` lies in the radical of `( , )`. -/
theorem B_posF_radical (ℓ : I → ℤ) {x : PreF K I} (hx : x ∈ radK C q c) (w : Free K I) :
    B C q c ℓ (posF x) w = 0 := by
  rw [B_eq_ndP hc hq, ndNF_posF]
  refine M_induction (motive := fun v => ndP C q c (tm (1 : PreF K I) x) v = 0) _ (by simp)
    (fun a b ha hb => by beta_reduce at *; rw [map_add, ha, hb, add_zero])
    (fun r a ha => by beta_reduce at *; rw [map_smul, ha, smul_zero]) fun a b => ?_
  beta_reduce
  rw [ndP_tm, (mem_radK.1 hx) (word b), mul_zero]

/-! ### KL III Proposition 2.5 -/

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : RootDatum C X Y)

include hc in
/-- **KL III Prop. 2.5 for `( , )`, blockwise**: the form is nondegenerate on each `U̇ 1_λ`. -/
theorem formU_nondegenerate (hGK : radK C q c ≤ Jf C q) (lam : X) (x : U1 RD q lam)
    (hx : ∀ y, formU RD q c hq lam x y = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := mk_surjective RD q lam x
  refine mk_eq_zero RD q lam (mem_Lrel_of_B hq hc hGK _ fun w => ?_)
  rw [← formU_mk RD q c hq]
  exact hx _

include hc in
/-- **KL III Proposition 2.5 for `( , )`**: the bilinear form is nondegenerate on `U̇`. -/
theorem nondegenerate_formUD (hGK : radK C q c ≤ Jf C q) : Nondegenerate (formUD RD q c hq) :=
  (nondegenerate_formUD_iff RD q c hq).2 fun _ _ hz => mem_Lrel_of_B hq hc hGK _ hz

include hc in
/-- **KL III Proposition 2.5 for `⟨ , ⟩`**: the semilinear form `⟨x, y⟩ = (ψ(x), y)` is
nondegenerate on `U̇` (for `σ` an involution of `K` with `σ q = q⁻¹`, e.g. `q ↦ q⁻¹` on
`ℚ(q)`). -/
theorem nondegenerate_hform (hGK : radK C q c ≤ Jf C q) (σ : K →+* K)
    (hσ : σ (q : K) = ((q⁻¹ : Kˣ) : K)) (hσσ : ∀ a, σ (σ a) = a) (x : UD RD q)
    (hx : ∀ y, hform RD q c σ hσ hq x y = 0) : x = 0 :=
  nondegenerate_hform_of_formUD RD q c hq σ hσ hσσ (nondegenerate_formUD hq hc RD hGK) x hx

include hc in
/-- **KL III Proposition 2.5 for `⟨ , ⟩`, blockwise**: if `⟨x 1_λ, y 1_λ⟩ = 0` for all
`y ∈ U̇ 1_λ` then `x 1_λ = 0`. -/
theorem hform_block_nondegenerate (hGK : radK C q c ≤ Jf C q) (σ : K →+* K)
    (hσ : σ (q : K) = ((q⁻¹ : Kˣ) : K)) (hσσ : ∀ a, σ (σ a) = a) (lam : X) (x : U1 RD q lam)
    (hx : ∀ y : U1 RD q lam, hform RD q c σ hσ hq (ofB RD q lam x) (ofB RD q lam y) = 0) :
    x = 0 := by
  have h0 : ofB RD q lam x = 0 := by
    refine nondegenerate_hform hq hc RD hGK σ hσ hσσ _ fun y => ?_
    have := hx (compB RD q lam y)
    rw [hform, Upsi_ofB, formUD_ofB] at this ⊢
    rwa [compB_ofB_self] at this
  have := congrArg (compB RD q lam) h0
  rwa [compB_ofB_self, map_zero] at this

/-! ### The Gabber–Kac hypothesis in the simply-laced case -/

include hq in
/-- For a simply-laced Cartan datum, the library's statement `PreF.GabberKac` of the quantum
Gabber–Kac theorem (at Lusztig's `v = q⁻¹`) implies the inclusion `ℐ ⊆ Jf` used above. -/
theorem radK_le_Jf_of_gabberKac (hsl : ∀ i, C.dot i i = 2)
    (hGK : PreF.GabberKac C.dot q⁻¹ c) : radK C q c ≤ Jf C q := by
  intro x hx
  have hx' : x ∈ radical C.dot q⁻¹ c := hx
  rw [hGK, TwoSidedIdeal.mem_asIdeal] at hx'
  clear hx
  have hqf : ∀ i N, qfact (vi C.dot q⁻¹ i) N ≠ 0 := fun i N => by
    rw [vi, inv_zpow', zpow_neg, qfact_inv]
    exact qfact_vi_ne_zero C q hq i _
  have hS : ∀ {i j : I} (hij : i ≠ j) (N : ℕ), C.serreN i j = N →
      serreSeq C.dot q⁻¹ i j N ∈ Jf C q := by
    intro i j hij N hN
    rw [serreSeq_eq_qfact_smul_serreDiv C.symm i j (C.dot_self_even i)
      (by rw [← hN]; exact C.two_mul_dot_eq hij) (hqf i N), serreDiv_inv, ← hN]
    refine Submodule.smul_mem _ _ ?_
    simpa using mul_serreDiv_mul_mem_Jf (C := C) (q := q) hij 1 1
  induction hx' using TwoSidedIdeal.span_induction with
  | mem x h =>
    rcases h with ⟨i, j, hij, h0, rfl⟩ | ⟨i, j, hij, h1, rfl⟩
    · rw [← serreSeq_one (dot := C.dot) (v := q⁻¹) i j (by rw [C.symm]; exact h0)]
      exact hS hij 1 (by simp [CartanDatum.serreN, h0])
    · rw [← serreSeq_two (dot := C.dot) (v := q⁻¹) i j (hsl i) (by rw [C.symm]; exact h1)]
      exact hS hij 2 (by simp [CartanDatum.serreN, h1, hsl i])
  | zero => exact Submodule.zero_mem _
  | add x y _ _ ha hb => exact add_mem ha hb
  | neg x _ ha => exact neg_mem ha
  | left_absorb a x _ ha => exact Jf_mul_left ha a
  | right_absorb b x _ ha => exact Jf_mul_right ha b

namespace KL3

/-- **Khovanov–Lauda III, Proposition 2.5 for `( , )`** over `ℚ(q)` (KL III's normalisation),
for an arbitrary Cartan datum, **assuming the quantum Gabber–Kac inclusion** `ℐ ⊆ Jf` (the
radical of the form on `'f` lies in the ideal generated by the quantum Serre elements; Lusztig
33.1.3). This is the hypothesis `UDot.KL3.FormNondeg RD` of KL III Theorem 1.2. -/
theorem formNondeg (hGK : radK C qK (cK C) ≤ Jf C qK) : FormNondeg RD :=
  nondegenerate_formUD hqK (fun _ => rfl) RD hGK

/-- **KL III Proposition 2.5** over `ℚ(q)`: both `( , )` and `⟨ , ⟩` are nondegenerate on `U̇`,
assuming `ℐ ⊆ Jf`. -/
theorem prop_2_5 (hGK : radK C qK (cK C) ≤ Jf C qK) :
    FormNondeg RD ∧ ∀ x, (∀ y, sform RD x y = 0) → x = 0 :=
  ⟨formNondeg RD hGK, sform_nondeg (formNondeg RD hGK)⟩

/-- KL III Proposition 2.5 for a simply-laced Cartan datum (e.g. `sl_n`), from the library's
statement `PreF.GabberKac` of the quantum Gabber–Kac theorem at `v = q⁻¹`. -/
theorem formNondeg_of_gabberKac (hsl : ∀ i, C.dot i i = 2)
    (hGK : PreF.GabberKac C.dot qK⁻¹ (cK C)) : FormNondeg RD :=
  formNondeg RD (radK_le_Jf_of_gabberKac hqK hsl hGK)

end KL3

end UDot

end Categorification.QuantumGroup

end
