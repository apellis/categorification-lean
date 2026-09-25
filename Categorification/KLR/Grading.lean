/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL1
import Categorification.Algebra.CoactionGrading

/-!
# The grading of KLR algebras

KL I (arXiv:0803.4121v2, §2.1) grades `R(ν)` by `deg (x_{a,i}) = 2` and
`deg (δ_{k,i}) = - i_k · i_{k+1}` (Cartan form of a simply-laced graph); KL II
(arXiv:0804.2080v1, §3.1) by `deg (x_{a,i}) = i_a · i_a` and `deg (δ_{k,i}) = - i_k · i_{k+1}`.

We work with abstract grading data (`GradingDatum`): integers `degX a` (the degree of a
dot on an `a`-strand) and `degΨ a b` (the degree of a crossing whose lower-left strand is
labelled `a` and lower-right strand `b`), subject to

* `degΨ a a = - degX a` (needed for the nil-Hecke relations `x ψ - ψ x = e`);
* for `a ≠ b`, `Q a b` is weighted homogeneous of degree `degΨ a b + degΨ b a` for the
  weights `(degX a, degX b)` (needed for `ψ² e_i = Q(x, x') e_i`).

The braid relation then imposes no further condition: `qbar` shifts weighted degree by
`- degX a` (`qbar_isWeightedHomogeneous`), which matches `degΨ a a = - degX a`.

The grading is constructed with a coaction `R(ν) → R(ν)[ℤ]` (see
`Categorification.Algebra.CoactionGrading`): on generators,
`e_i ↦ single 0 e_i`, `x_a ↦ ∑_i single (deg x_{a,i}) (x_a e_i)`,
`ψ_j ↦ ∑_i single (deg ψ_{j,i}) (ψ_j e_i)`. That this respects the defining relations is
exactly the homogeneity of the relations.

## Main definitions and results

* `KLR.GradingDatum Q` : grading data compatible with `Q`.
* `GradingDatum.coaction`, `GradingDatum.grade` and the `GradedAlgebra (G.grade ν)` instance.
* `GradingDatum.e_mem_grade`, `GradingDatum.x_mul_e_mem_grade`,
  `GradingDatum.ψ_mul_e_mem_grade`, `GradingDatum.pol_monomial_mul_e_mem_grade`,
  `GradingDatum.ψw_mul_pol_mul_e_mem_grade` : degrees of the standard elements.
* `KLR.cartan`, `KLR.klGradingDatum` : the KL I grading of the simply-laced data.
-/

namespace Categorification.KLR

open MvPolynomial TypeA AddMonoidAlgebra Equiv

variable {I : Type*} {k : Type*} [CommRing k]

/-! ### Weighted homogeneity of `Q̄` -/

/-- `Q̄(a, b, c) = (Q(a, b) - Q(c, b)) / (a - c)` has weighted degree `deg Q - w₀` for the
weights `(w₀, w₁, w₀)`. -/
theorem qbar_isWeightedHomogeneous {Q : MvPolynomial (Fin 2) k} {w₀ w₁ D : ℤ}
    (hQ : Q.IsWeightedHomogeneous ![w₀, w₁] D) :
    (qbar Q).IsWeightedHomogeneous ![w₀, w₁, w₀] (D - w₀) := by
  unfold qbar
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  have hsD : (s 0 : ℤ) * w₀ + s 1 * w₁ = D := by
    have := hQ (mem_support_iff.1 hs)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [Fin.sum_univ_two] using this
  beta_reduce
  rw [Finset.mul_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  convert ((isWeightedHomogeneous_C ![w₀, w₁, w₀] _).mul
    ((isWeightedHomogeneous_X k ![w₀, w₁, w₀] 1).pow (s 1))).mul
    (((isWeightedHomogeneous_X k ![w₀, w₁, w₀] 0).pow t).mul
      ((isWeightedHomogeneous_X k ![w₀, w₁, w₀] 2).pow (s 0 - 1 - t))) using 1
  have h1 : ((s 0 - 1 - t : ℕ) : ℤ) = s 0 - 1 - t := by omega
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, nsmul_eq_mul, h1]
  linear_combination -hsD

/-! ### Grading data -/

/-- Grading data for the KLR algebras with parameters `Q`: the degree `degX a` of a dot on an
`a`-strand and the degree `degΨ a b` of a crossing with bottom labels `a b`. -/
structure GradingDatum (Q : I → I → MvPolynomial (Fin 2) k) where
  /-- The degree of a dot on a strand labelled `a`. -/
  degX : I → ℤ
  /-- The degree of a crossing whose bottom endpoints are labelled `a`, `b` (left to right). -/
  degΨ : I → I → ℤ
  degΨ_self : ∀ a, degΨ a a = -degX a
  isWeightedHomogeneous : ∀ a b, a ≠ b →
    (Q a b).IsWeightedHomogeneous ![degX a, degX b] (degΨ a b + degΨ b a)

namespace GradingDatum

variable {Q : I → I → MvPolynomial (Fin 2) k} (G : GradingDatum Q)

/-- The weighted homogeneity of `Q̄` required by the braid relation. -/
theorem qbar_isWeightedHomogeneous {a b : I} (h : a ≠ b) :
    (qbar (Q a b)).IsWeightedHomogeneous ![G.degX a, G.degX b, G.degX a]
      (G.degΨ a b + G.degΨ a a + G.degΨ b a) := by
  convert KLR.qbar_isWeightedHomogeneous (G.isWeightedHomogeneous a b h) using 1
  rw [G.degΨ_self]; ring

variable {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- The degree of `x_a e_i`. -/
def dx (a : Fin m) (i : Seq ν) : ℤ := G.degX (i.lbl a)

/-- The degree of `ψ_j e_i` (zero for an out-of-range crossing, which vanishes). -/
def dψ (j : ℕ) (i : Seq ν) : ℤ :=
  if h : j + 1 < m then G.degΨ (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩) else 0

theorem dψ_of_lt {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    G.dψ j i = G.degΨ (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩) := dif_pos h

/-- The degree of `ψ_ρ e_i = ψ_{ρ₀} ψ_{ρ₁} ⋯ e_i`, computed along the word. -/
def degW : List ℕ → Seq ν → ℤ
  | [], _ => 0
  | j :: ρ, i => G.dψ j (wordProd m ρ • i) + degW ρ i

theorem lbl_sadj_smul (j : ℕ) (i : Seq ν) (a : Fin m) :
    (sadj m j • i).lbl a = i.lbl (sadj m j a) := by
  simp only [Seq.lbl, Seq.smul_apply, ← Perm.inv_def, sadj_inv]

/-! ### The coaction on the free algebra -/

variable [DecidableEq I]

open KLRAlgebra

local notation "mkF" => KLRAlgebra.mk k Q ν

/-- Images of the generators under the coaction. -/
noncomputable def genImage : Gen ν → AddMonoidAlgebra (KLRAlgebra k Q ν) ℤ
  | .idem i => single 0 (e i)
  | .dot a => ∑ i, single (G.dx a i) (x a * e i)
  | .cross j => ∑ i, single (G.dψ j i) (ψ j * e i)

/-- The coaction on the free algebra. -/
noncomputable def liftF : FreeAlgebra k (Gen ν) →ₐ[k] AddMonoidAlgebra (KLRAlgebra k Q ν) ℤ :=
  FreeAlgebra.lift k G.genImage

@[simp] theorem liftF_fe (i : Seq ν) : G.liftF (fe k ν i) = single 0 (e i) := by
  simp [liftF, genImage]

@[simp] theorem liftF_fx (a : Fin m) :
    G.liftF (fx k ν a) = ∑ i, single (G.dx a i) (x a * e i) := by
  simp [liftF, genImage]

@[simp] theorem liftF_fψ (j : ℕ) :
    G.liftF (fψ k ν j) = ∑ i, single (G.dψ j i) (ψ j * e i) := by
  simp [liftF, genImage]

/-- Elements `u` of the free algebra such that `liftF u = single d (mk u)` and whose image
starts (on top) at the sequence `l`, i.e. `e_l * mk u = mk u`. -/
def homAt (l : Seq ν) (d : ℤ) : Submodule k (FreeAlgebra k (Gen ν)) where
  carrier := {u | G.liftF u = single d (mkF u) ∧ e l * mkF u = mkF u}
  zero_mem' := by simp
  add_mem' {u v} hu hv := by
    refine ⟨?_, ?_⟩
    · rw [map_add, map_add, hu.1, hv.1, single_add]
    · rw [map_add, mul_add, hu.2, hv.2]
  smul_mem' c u hu := by
    refine ⟨?_, ?_⟩
    · rw [map_smul, map_smul, hu.1, smul_single]
    · rw [map_smul, mul_smul_comm, hu.2]

theorem mem_homAt {u : FreeAlgebra k (Gen ν)} {l : Seq ν} {d : ℤ} :
    u ∈ G.homAt l d ↔ G.liftF u = single d (mkF u) ∧ e l * mkF u = mkF u := Iff.rfl

theorem homAt_of_eq {u : FreeAlgebra k (Gen ν)} {l : Seq ν} {d d' : ℤ} (hu : u ∈ G.homAt l d)
    (h : d = d') : u ∈ G.homAt l d' := h ▸ hu

theorem sum_single_mul (f : Seq ν → ℤ) (y : KLRAlgebra k Q ν) (l : Seq ν) (d : ℤ)
    (w : KLRAlgebra k Q ν) :
    (∑ i, single (f i) (y * e i)) * single d (e l * w) = single (f l + d) (y * e l * w) := by
  rw [Finset.sum_mul, Finset.sum_eq_single l]
  · rw [single_mul_single, mul_assoc y, ← mul_assoc (e l), e_mul_self, mul_assoc]
  · intro i _ hi
    rw [single_mul_single, mul_assoc y, ← mul_assoc (e i), e_mul_e, if_neg hi]
    simp
  · simp

theorem homAt_fe (i : Seq ν) : fe k ν i ∈ G.homAt i 0 :=
  G.mem_homAt.2 ⟨by rw [liftF_fe]; rfl, e_mul_self i⟩

theorem homAt_fe_mul (i : Seq ν) {u : FreeAlgebra k (Gen ν)} {l : Seq ν} {d : ℤ}
    (hu : u ∈ G.homAt l d) : fe k ν i * u ∈ G.homAt l d := by
  rw [mem_homAt] at *
  refine ⟨?_, ?_⟩
  · rw [map_mul, liftF_fe, hu.1, single_mul_single, zero_add, map_mul]; rfl
  · rw [map_mul, ← mul_assoc]
    change e l * e i * mkF u = e i * mkF u
    conv_rhs => rw [← hu.2, ← mul_assoc]
    rw [e_mul_e, e_mul_e]
    by_cases h : i = l
    · subst h; rfl
    · rw [if_neg (Ne.symm h), if_neg h]

theorem homAt_fx_mul (a : Fin m) {u : FreeAlgebra k (Gen ν)} {l : Seq ν} {d : ℤ}
    (hu : u ∈ G.homAt l d) : fx k ν a * u ∈ G.homAt l (G.dx a l + d) := by
  rw [mem_homAt] at *
  refine ⟨?_, ?_⟩
  · rw [map_mul, liftF_fx, hu.1, ← hu.2, sum_single_mul, map_mul, mul_assoc, hu.2]; rfl
  · rw [map_mul]
    change e l * (x a * _) = x a * _
    rw [← mul_assoc, ← x_mul_e, mul_assoc, hu.2]

theorem homAt_fψ_mul (j : ℕ) {u : FreeAlgebra k (Gen ν)} {l : Seq ν} {d : ℤ}
    (hu : u ∈ G.homAt l d) : fψ k ν j * u ∈ G.homAt (sadj m j • l) (G.dψ j l + d) := by
  rw [mem_homAt] at *
  refine ⟨?_, ?_⟩
  · rw [map_mul, liftF_fψ, hu.1, ← hu.2, sum_single_mul, map_mul, mul_assoc, hu.2]; rfl
  · rw [map_mul]
    change e (sadj m j • l) * (ψ j * _) = ψ j * _
    have h1 : ψ j * mkF u = e (sadj m j • l) * (ψ j * mkF u) := by
      conv_lhs => rw [← hu.2, ← mul_assoc, ψ_mul_e, mul_assoc]
    rw [h1, ← mul_assoc, e_mul_self]

theorem homAt_fx_pow_mul (a : Fin m) {u : FreeAlgebra k (Gen ν)} {l : Seq ν} {d : ℤ}
    (hu : u ∈ G.homAt l d) (n : ℕ) : fx k ν a ^ n * u ∈ G.homAt l (n • G.dx a l + d) := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    exact G.homAt_of_eq (G.homAt_fx_mul a ih) (by rw [succ_nsmul]; ring)

theorem homAt_prod_mul {u : FreeAlgebra k (Gen ν)} {l : Seq ν} {d : ℤ} (hu : u ∈ G.homAt l d) :
    ∀ {n : ℕ} (f : Fin n → Fin m) (s : Fin n → ℕ),
      (List.ofFn fun a => fx k ν (f a) ^ s a).prod * u ∈
        G.homAt l ((∑ a, s a • G.dx (f a) l) + d)
  | 0, f, s => by simpa using hu
  | n + 1, f, s => by
    rw [List.ofFn_succ, List.prod_cons, mul_assoc]
    refine G.homAt_of_eq (G.homAt_fx_pow_mul (f 0) (homAt_prod_mul hu _ _) (s 0)) ?_
    rw [Fin.sum_univ_succ]; ring

theorem homAt_ncEval {n : ℕ} (f : Fin n → Fin m) (p : MvPolynomial (Fin n) k) {D : ℤ}
    {u : FreeAlgebra k (Gen ν)} {l : Seq ν} {d : ℤ}
    (hp : p.IsWeightedHomogeneous (fun a => G.dx (f a) l) D) (hu : u ∈ G.homAt l d) :
    ncEval (fun a => fx k ν (f a)) p * u ∈ G.homAt l (D + d) := by
  unfold ncEval
  rw [Finsupp.sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [← Algebra.smul_def, smul_mul_assoc]
  refine Submodule.smul_mem _ _ (G.homAt_of_eq (G.homAt_prod_mul hu f s) ?_)
  have := hp (mem_support_iff.1 hs)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at this
  rw [this]

/-! ### The relations are homogeneous -/

theorem sum_single_e :
    (∑ l, single (0 : ℤ) (e l) : AddMonoidAlgebra (KLRAlgebra k Q ν) ℤ) = 1 := by
  have : (∑ l, single (0 : ℤ) (e l) : AddMonoidAlgebra (KLRAlgebra k Q ν) ℤ) =
      single 0 (∑ l, e l) := (Finsupp.single_finset_sum _ _ _).symm
  rw [this, sum_e, AddMonoidAlgebra.one_def]

theorem liftF_eq_sum (u : FreeAlgebra k (Gen ν)) :
    G.liftF u = ∑ l, G.liftF (u * fe k ν l) := by
  simp only [map_mul, liftF_fe, ← Finset.mul_sum]
  rw [sum_single_e, mul_one]

theorem liftF_eq_of_homAt {L R : FreeAlgebra k (Gen ν)} {l l' : Seq ν} {d : ℤ}
    (hL : L ∈ G.homAt l d) (hR : R ∈ G.homAt l' d) (h : mkF L = mkF R) :
    G.liftF L = G.liftF R := by
  rw [(G.mem_homAt.1 hL).1, (G.mem_homAt.1 hR).1, h]

theorem liftF_sub_of_homAt {A B : FreeAlgebra k (Gen ν)} {l l' : Seq ν} {d : ℤ}
    (hA : A ∈ G.homAt l d) (hB : B ∈ G.homAt l' d) :
    G.liftF (A - B) = single d (mkF (A - B)) := by
  rw [map_sub, map_sub, (G.mem_homAt.1 hA).1, (G.mem_homAt.1 hB).1]
  exact (Finsupp.single_sub _ _ _).symm

theorem liftF_eq_of_forall {L R : FreeAlgebra k (Gen ν)}
    (h : ∀ l, ∃ l₁ l₂ d, L * fe k ν l ∈ G.homAt l₁ d ∧ R * fe k ν l ∈ G.homAt l₂ d)
    (hmk : mkF L = mkF R) : G.liftF L = G.liftF R := by
  rw [G.liftF_eq_sum L, G.liftF_eq_sum R]
  refine Finset.sum_congr rfl fun l _ => ?_
  obtain ⟨l₁, l₂, d, h₁, h₂⟩ := h l
  exact G.liftF_eq_of_homAt h₁ h₂ (by rw [map_mul, map_mul, hmk])

theorem liftF_rel {a b : FreeAlgebra k (Gen ν)} (h : Rel k Q ν a b) : G.liftF a = G.liftF b := by
  have hmk : mkF a = mkF b := KLRAlgebra.rel h
  cases h with
  | idem_mul i j =>
    rw [map_mul, liftF_fe, liftF_fe, single_mul_single, add_zero]
    split_ifs with hij
    · subst hij; rw [liftF_fe, e_mul_self]
    · rw [map_zero]
      change single 0 (e i * e j) = 0
      rw [e_mul_e, if_neg hij, single_zero]
  | idem_sum =>
    rw [map_sum, map_one]
    simp only [liftF_fe]
    exact sum_single_e
  | dot_idem a i =>
    refine G.liftF_eq_of_forall (fun l => ⟨l, l, G.dx a l + 0, ?_, ?_⟩) hmk
    · rw [mul_assoc]; exact G.homAt_fx_mul a (G.homAt_fe_mul i (G.homAt_fe l))
    · rw [mul_assoc]; exact G.homAt_fe_mul i (G.homAt_fx_mul a (G.homAt_fe l))
  | cross_idem j i =>
    refine G.liftF_eq_of_forall (fun l => ⟨sadj m j • l, sadj m j • l, G.dψ j l + 0, ?_, ?_⟩) hmk
    · rw [mul_assoc]; exact G.homAt_fψ_mul j (G.homAt_fe_mul i (G.homAt_fe l))
    · rw [mul_assoc]; exact G.homAt_fe_mul _ (G.homAt_fψ_mul j (G.homAt_fe l))
  | cross_zero j hj =>
    rw [map_zero, liftF_fψ]
    simp [ψ_eq_zero j hj]
  | dot_dot a c =>
    refine G.liftF_eq_of_forall (fun l => ⟨l, l, G.dx a l + (G.dx c l + 0), ?_, ?_⟩) hmk
    · rw [mul_assoc]; exact G.homAt_fx_mul a (G.homAt_fx_mul c (G.homAt_fe l))
    · rw [mul_assoc]
      exact G.homAt_of_eq (G.homAt_fx_mul c (G.homAt_fx_mul a (G.homAt_fe l))) (by ring)
  | cross_cross j l hjl =>
    refine G.liftF_eq_of_forall (fun t => ⟨sadj m j • sadj m l • t, sadj m l • sadj m j • t,
      G.dψ j (sadj m l • t) + (G.dψ l t + 0),
      ?_, ?_⟩) hmk
    · rw [mul_assoc]; exact G.homAt_fψ_mul j (G.homAt_fψ_mul l (G.homAt_fe t))
    · rw [mul_assoc]
      refine G.homAt_of_eq (G.homAt_fψ_mul l (G.homAt_fψ_mul j (G.homAt_fe t))) ?_
      have h1 : G.dψ j (sadj m l • t) = G.dψ j t := by
        unfold dψ
        split_ifs with hj
        · rw [lbl_sadj_smul, lbl_sadj_smul, sadj_apply_of_ne _ (by simp; omega) (by simp; omega),
            sadj_apply_of_ne _ (by simp; omega) (by simp; omega)]
        · rfl
      have h2 : G.dψ l (sadj m j • t) = G.dψ l t := by
        unfold dψ
        split_ifs with hl
        · rw [lbl_sadj_smul, lbl_sadj_smul, sadj_apply_of_ne _ (by simp; omega) (by simp; omega),
            sadj_apply_of_ne _ (by simp; omega) (by simp; omega)]
        · rfl
      rw [h1, h2]; ring
  | dot_cross a j h₁ h₂ =>
    refine G.liftF_eq_of_forall (fun t => ⟨sadj m j • t, sadj m j • t,
      G.dx a (sadj m j • t) + (G.dψ j t + 0),
      ?_, ?_⟩) hmk
    · rw [mul_assoc]; exact G.homAt_fx_mul a (G.homAt_fψ_mul j (G.homAt_fe t))
    · rw [mul_assoc]
      refine G.homAt_of_eq (G.homAt_fψ_mul j (G.homAt_fx_mul a (G.homAt_fe t))) ?_
      rw [dx, dx, lbl_sadj_smul, sadj_apply_of_ne _ h₁ h₂]; ring
  | dot_cross_left j hj i =>
    have hL : G.liftF ((fx k ν ⟨j, by omega⟩ * fψ k ν j - fψ k ν j * fx k ν ⟨j + 1, hj⟩) *
        fe k ν i) = single (G.dψ j i + (G.dx ⟨j + 1, hj⟩ i + 0))
          (mkF ((fx k ν ⟨j, by omega⟩ * fψ k ν j - fψ k ν j * fx k ν ⟨j + 1, hj⟩) *
            fe k ν i)) := by
      rw [sub_mul, mul_assoc, mul_assoc]
      refine G.liftF_sub_of_homAt (G.homAt_of_eq (G.homAt_fx_mul _ (G.homAt_fψ_mul j
        (G.homAt_fe i))) ?_) (G.homAt_fψ_mul j (G.homAt_fx_mul _ (G.homAt_fe i)))
      simp only [dx, lbl_sadj_smul, sadj_apply_left hj]; ring
    rw [hL, hmk]
    split_ifs with hc
    · rw [(G.mem_homAt.1 (G.homAt_fe i)).1]
      congr 1
      rw [dx, G.dψ_of_lt hj, ← hc, G.degΨ_self]; simp
    · simp
  | dot_cross_right j hj i =>
    have hL : G.liftF ((fψ k ν j * fx k ν ⟨j, by omega⟩ - fx k ν ⟨j + 1, hj⟩ * fψ k ν j) *
        fe k ν i) = single (G.dψ j i + (G.dx ⟨j, by omega⟩ i + 0))
          (mkF ((fψ k ν j * fx k ν ⟨j, by omega⟩ - fx k ν ⟨j + 1, hj⟩ * fψ k ν j) *
            fe k ν i)) := by
      rw [sub_mul, mul_assoc, mul_assoc]
      refine G.liftF_sub_of_homAt (G.homAt_fψ_mul j (G.homAt_fx_mul _ (G.homAt_fe i)))
        (G.homAt_of_eq (G.homAt_fx_mul _ (G.homAt_fψ_mul j (G.homAt_fe i))) ?_)
      simp only [dx, lbl_sadj_smul, sadj_apply_right hj]; ring
    rw [hL, hmk]
    split_ifs with hc
    · rw [(G.mem_homAt.1 (G.homAt_fe i)).1]
      congr 1
      rw [dx, G.dψ_of_lt hj, ← hc, G.degΨ_self]; simp
    · simp
  | cross_sq j hj i =>
    have hL := G.homAt_fψ_mul j (G.homAt_fψ_mul j (G.homAt_fe i))
    rw [← mul_assoc] at hL
    rw [(G.mem_homAt.1 hL).1, hmk]
    split_ifs with hc
    · simp
    · have hv : ![fx k ν ⟨j, by omega⟩, fx k ν ⟨j + 1, hj⟩] =
          fun t => fx k ν (![⟨j, by omega⟩, ⟨j + 1, hj⟩] t : Fin m) := by
        funext t; fin_cases t <;> rfl
      have hw : (fun t => G.dx (![⟨j, by omega⟩, ⟨j + 1, hj⟩] t : Fin m) i) =
          ![G.degX (i.lbl ⟨j, by omega⟩), G.degX (i.lbl ⟨j + 1, hj⟩)] := by
        funext t; fin_cases t <;> rfl
      have hR := G.homAt_ncEval _ _ (hw ▸ G.isWeightedHomogeneous _ _ hc) (G.homAt_fe i)
      rw [← hv] at hR
      rw [(G.mem_homAt.1 hR).1]
      congr 1
      simp only [dx, G.dψ_of_lt hj, lbl_sadj_smul, sadj_apply_left hj, sadj_apply_right hj]
      ring
  | braid j hj i =>
    have h1 : j + 1 < m := by omega
    have h2 : j + 1 + 1 < m := hj
    have e1 : sadj m j ⟨j, by omega⟩ = ⟨j + 1, h1⟩ := sadj_apply_left h1
    have e2 : sadj m j ⟨j + 1, h1⟩ = ⟨j, by omega⟩ := sadj_apply_right h1
    have e3 : sadj m j ⟨j + 1 + 1, h2⟩ = ⟨j + 1 + 1, h2⟩ :=
      sadj_apply_of_ne _ (by rw [Fin.val_mk]; omega) (by rw [Fin.val_mk]; omega)
    have e4 : sadj m (j + 1) ⟨j + 1, h1⟩ = ⟨j + 1 + 1, h2⟩ := sadj_apply_left h2
    have e5 : sadj m (j + 1) ⟨j + 1 + 1, h2⟩ = ⟨j + 1, h1⟩ := sadj_apply_right h2
    have e6 : sadj m (j + 1) ⟨j, by omega⟩ = ⟨j, by omega⟩ :=
      sadj_apply_of_ne _ (by rw [Fin.val_mk]; omega) (by rw [Fin.val_mk]; omega)
    have hL : G.liftF ((fψ k ν j * fψ k ν (j + 1) * fψ k ν j -
        fψ k ν (j + 1) * fψ k ν j * fψ k ν (j + 1)) * fe k ν i) =
        single (G.degΨ (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h1⟩) +
          G.degΨ (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1 + 1, h2⟩) +
          G.degΨ (i.lbl ⟨j + 1, h1⟩) (i.lbl ⟨j + 1 + 1, h2⟩))
          (mkF ((fψ k ν j * fψ k ν (j + 1) * fψ k ν j -
            fψ k ν (j + 1) * fψ k ν j * fψ k ν (j + 1)) * fe k ν i)) := by
      rw [sub_mul, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
      refine G.liftF_sub_of_homAt
        (G.homAt_of_eq (G.homAt_fψ_mul _ (G.homAt_fψ_mul _ (G.homAt_fψ_mul _ (G.homAt_fe i)))) ?_)
        (G.homAt_of_eq (G.homAt_fψ_mul _ (G.homAt_fψ_mul _ (G.homAt_fψ_mul _ (G.homAt_fe i)))) ?_)
      · simp only [G.dψ_of_lt h1, G.dψ_of_lt h2, lbl_sadj_smul, e1, e2, e3, e4, e5, e6]; ring
      · simp only [G.dψ_of_lt h1, G.dψ_of_lt h2, lbl_sadj_smul, e1, e2, e3, e4, e5, e6]; ring
    rw [hL, hmk]
    split_ifs with hc
    · have hv : ![fx k ν ⟨j, by omega⟩, fx k ν ⟨j + 1, h1⟩, fx k ν ⟨j + 2, hj⟩] =
          fun t => fx k ν (![⟨j, by omega⟩, ⟨j + 1, h1⟩, ⟨j + 2, hj⟩] t : Fin m) := by
        funext t; fin_cases t <;> rfl
      have hw : (fun t => G.dx (![⟨j, by omega⟩, ⟨j + 1, h1⟩, ⟨j + 2, hj⟩] t : Fin m) i) =
          ![G.degX (i.lbl ⟨j, by omega⟩), G.degX (i.lbl ⟨j + 1, h1⟩),
            G.degX (i.lbl ⟨j, by omega⟩)] := by
        funext t; fin_cases t
        · rfl
        · rfl
        · exact congrArg G.degX hc.1.symm
      have hR := G.homAt_ncEval _ _ (hw ▸ G.qbar_isWeightedHomogeneous hc.2) (G.homAt_fe i)
      rw [← hv] at hR
      rw [(G.mem_homAt.1 hR).1]
      congr 1
      have hc1 : i.lbl ⟨j + 1 + 1, h2⟩ = i.lbl ⟨j, by omega⟩ := hc.1.symm
      rw [hc1]; ring
    · simp

/-! ### The coaction and the grading of `R(ν)` -/

/-- The coaction `R(ν) → R(ν)[ℤ]` defining the grading:
`e_i ↦ single 0 e_i`, `x_a ↦ ∑_i single (deg x_{a,i}) (x_a e_i)`,
`ψ_j ↦ ∑_i single (deg ψ_{j,i}) (ψ_j e_i)`. -/
noncomputable def coaction : KLRAlgebra k Q ν →ₐ[k] AddMonoidAlgebra (KLRAlgebra k Q ν) ℤ :=
  RingQuot.liftAlgHom k ⟨G.liftF, fun _ _ h => G.liftF_rel h⟩

theorem coaction_mk (u : FreeAlgebra k (Gen ν)) : G.coaction (mkF u) = G.liftF u :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem coaction_e (i : Seq ν) : G.coaction (e i) = single 0 (e i) := by
  rw [e, coaction_mk, liftF_fe]; rfl

@[simp] theorem coaction_x (a : Fin m) :
    G.coaction (x a) = ∑ i, single (G.dx a i) (x a * e i) := by
  rw [x, coaction_mk, liftF_fx]; rfl

@[simp] theorem coaction_ψ (j : ℕ) :
    G.coaction (ψ j : KLRAlgebra k Q ν) = ∑ i, single (G.dψ j i) (ψ j * e i) := by
  rw [ψ, coaction_mk, liftF_fψ]; rfl

variable (ν) in
/-- The grading of `R(ν)`: the degree `d` part is `{a | coaction a = single d a}`. -/
noncomputable def grade : ℤ → Submodule k (KLRAlgebra k Q ν) :=
  CoactionGrading.grade (G.coaction (ν := ν))

theorem mem_grade {d : ℤ} {a : KLRAlgebra k Q ν} :
    a ∈ G.grade ν d ↔ G.coaction a = single d a := Iff.rfl

theorem mk_mem_grade_of_homAt {u : FreeAlgebra k (Gen ν)} {l : Seq ν} {d : ℤ}
    (hu : u ∈ G.homAt l d) : mkF u ∈ G.grade ν d := by
  rw [mem_grade, coaction_mk]; exact (G.mem_homAt.1 hu).1

/-- The idempotents `e_i` have degree `0`. -/
theorem e_mem_grade (i : Seq ν) : (e i : KLRAlgebra k Q ν) ∈ G.grade ν 0 :=
  G.mk_mem_grade_of_homAt (G.homAt_fe i)

/-- `x_a e_i` has degree `degX i_a`. -/
theorem x_mul_e_mem_grade (a : Fin m) (i : Seq ν) :
    (x a * e i : KLRAlgebra k Q ν) ∈ G.grade ν (G.degX (i.lbl a)) := by
  have h := G.mk_mem_grade_of_homAt (G.homAt_fx_mul a (G.homAt_fe i))
  rwa [map_mul, add_zero] at h

theorem ψ_mul_e_mem_grade' (j : ℕ) (i : Seq ν) :
    (ψ j * e i : KLRAlgebra k Q ν) ∈ G.grade ν (G.dψ j i) := by
  have h := G.mk_mem_grade_of_homAt (G.homAt_fψ_mul j (G.homAt_fe i))
  rwa [map_mul, add_zero] at h

/-- `ψ_j e_i` has degree `degΨ i_j i_{j+1}`. -/
theorem ψ_mul_e_mem_grade {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    (ψ j * e i : KLRAlgebra k Q ν) ∈
      G.grade ν (G.degΨ (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩)) := by
  rw [← G.dψ_of_lt h]; exact G.ψ_mul_e_mem_grade' j i

theorem mk_ncEval_mul_fe (p : MvPolynomial (Fin m) k) (i : Seq ν) :
    mkF (ncEval (fun a => fx k ν (id a)) p * fe k ν i) = pol p * e i := by
  rw [map_mul, mk_ncEval]
  change ncEval (fun a => (x (id a) : KLRAlgebra k Q ν)) p * e i = _
  rw [ncEval_eq_pol, rename_id_apply]

/-- `p(x) e_i` has degree `D` if `p` is weighted homogeneous of degree `D` for the weights
`deg x_a = degX i_a`. -/
theorem pol_mul_e_mem_grade (i : Seq ν) {p : MvPolynomial (Fin m) k} {D : ℤ}
    (hp : p.IsWeightedHomogeneous (fun a => G.degX (i.lbl a)) D) :
    (pol p * e i : KLRAlgebra k Q ν) ∈ G.grade ν D := by
  have h := G.mk_mem_grade_of_homAt (G.homAt_ncEval (l := i) id p hp (G.homAt_fe i))
  rwa [mk_ncEval_mul_fe, add_zero] at h

/-- `x^u e_i` has degree `∑_a u_a · degX i_a`. -/
theorem pol_monomial_mul_e_mem_grade (u : Fin m →₀ ℕ) (i : Seq ν) :
    (pol (monomial u 1) * e i : KLRAlgebra k Q ν) ∈
      G.grade ν (Finsupp.weight (fun a => G.degX (i.lbl a)) u) :=
  G.pol_mul_e_mem_grade i (isWeightedHomogeneous_monomial _ _ _ rfl)

theorem homAt_fψw_mul (ρ : List ℕ) {u : FreeAlgebra k (Gen ν)} {l : Seq ν} {d : ℤ}
    (hu : u ∈ G.homAt l d) :
    (ρ.map (fψ k ν)).prod * u ∈ G.homAt (wordProd m ρ • l) (G.degW ρ l + d) := by
  induction ρ with
  | nil => simpa [degW] using hu
  | cons j ρ ih =>
    rw [List.map_cons, List.prod_cons, mul_assoc, wordProd_cons, mul_smul]
    exact G.homAt_of_eq (G.homAt_fψ_mul j ih) (by rw [degW, add_assoc])

theorem mk_fψw (ρ : List ℕ) : mkF (ρ.map (fψ k ν)).prod = ψw ρ := by
  rw [map_list_prod, List.map_map]; rfl

/-- `ψ_ρ p(x) e_i` has degree `degW ρ i + D` if `p` is weighted homogeneous of degree `D`. -/
theorem ψw_mul_pol_mul_e_mem_grade (ρ : List ℕ) (i : Seq ν) {p : MvPolynomial (Fin m) k}
    {D : ℤ} (hp : p.IsWeightedHomogeneous (fun a => G.degX (i.lbl a)) D) :
    (ψw ρ * pol p * e i : KLRAlgebra k Q ν) ∈ G.grade ν (G.degW ρ i + D) := by
  have h := G.mk_mem_grade_of_homAt
    (G.homAt_fψw_mul ρ (G.homAt_ncEval (l := i) id p hp (G.homAt_fe i)))
  rwa [map_mul, mk_ncEval_mul_fe, mk_fψw, add_zero, ← mul_assoc] at h

/-- `ψ_ρ x^u e_i` is homogeneous of degree `degW ρ i + ∑_a u_a · degX i_a`. -/
theorem ψw_mul_pol_monomial_mul_e_mem_grade (ρ : List ℕ) (u : Fin m →₀ ℕ) (i : Seq ν) :
    (ψw ρ * pol (monomial u 1) * e i : KLRAlgebra k Q ν) ∈
      G.grade ν (G.degW ρ i + Finsupp.weight (fun a => G.degX (i.lbl a)) u) :=
  G.ψw_mul_pol_mul_e_mem_grade ρ i (isWeightedHomogeneous_monomial _ _ _ rfl)

/-- Every element of `R(ν)` is a sum of homogeneous elements. -/
theorem mem_homogeneousSubalgebra (a : KLRAlgebra k Q ν) :
    a ∈ CoactionGrading.homogeneousSubalgebra G.coaction := by
  obtain ⟨u, rfl⟩ := mk_surjective a
  induction u using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
  | grade1 g =>
    cases g with
    | idem i =>
      exact CoactionGrading.mem_homogeneousSubalgebra_of_mem_grade _ (G.e_mem_grade i)
    | dot a =>
      change x a ∈ _
      rw [← mul_one (x a), ← sum_e, Finset.mul_sum]
      exact Subalgebra.sum_mem _ fun i _ =>
        CoactionGrading.mem_homogeneousSubalgebra_of_mem_grade _ (G.x_mul_e_mem_grade a i)
    | cross j =>
      change ψ j ∈ _
      rw [← mul_one (ψ j), ← sum_e, Finset.mul_sum]
      exact Subalgebra.sum_mem _ fun i _ =>
        CoactionGrading.mem_homogeneousSubalgebra_of_mem_grade _ (G.ψ_mul_e_mem_grade' j i)
  | mul u v hu hv => rw [map_mul]; exact Subalgebra.mul_mem _ hu hv
  | add u v hu hv => rw [map_add]; exact Subalgebra.add_mem _ hu hv

theorem counit : CoactionGrading.Counit (G.coaction (ν := ν)) :=
  CoactionGrading.counit_of_forall_mem _ G.mem_homogeneousSubalgebra

theorem coassoc : CoactionGrading.Coassoc (G.coaction (ν := ν)) :=
  CoactionGrading.coassoc_of_forall_mem _ G.mem_homogeneousSubalgebra

/-- The `ℤ`-grading of the KLR algebra `R(ν)` defined by the grading datum `G`. -/
noncomputable instance gradedAlgebra : GradedAlgebra (G.grade ν) :=
  CoactionGrading.gradedAlgebra G.counit G.coassoc

/-- The degree `d` component of `a` is the coefficient of `single d` in `coaction a`. -/
theorem decompose_apply (a : KLRAlgebra k Q ν) (d : ℤ) :
    (DirectSum.decompose (G.grade ν) a d : KLRAlgebra k Q ν) = G.coaction a d :=
  CoactionGrading.decompose_apply G.counit G.coassoc a d

end GradingDatum

/-! ### The KL I grading of simply-laced data -/

section KL1

variable [DecidableEq I] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

/-- The Cartan form of a simply-laced graph `Γ`: `a · a = 2`, `a · b = -1` if `a` and `b`
are joined by an edge, and `a · b = 0` otherwise. -/
def cartan (a b : I) : ℤ := if a = b then 2 else if Γ.Adj a b then -1 else 0

theorem cartan_self (a : I) : cartan Γ a a = 2 := if_pos rfl

theorem cartan_symm (a b : I) : cartan Γ a b = cartan Γ b a := by
  unfold cartan
  by_cases h : a = b
  · subst h; rfl
  · simp only [if_neg h, if_neg (Ne.symm h), Γ.adj_comm]

variable (k)

/-- The KL I grading: `deg x_{a,i} = 2 = i_a · i_a` and `deg ψ_{k,i} = - i_k · i_{k+1}`. -/
noncomputable def klGradingDatum : GradingDatum (klQ (k := k) Γ) where
  degX _ := 2
  degΨ a b := -cartan Γ a b
  degΨ_self a := by rw [cartan_self]
  isWeightedHomogeneous a b hab := by
    simp only [klQ, cartan, if_neg hab, if_neg (Ne.symm hab), Γ.adj_comm b a]
    split_ifs
    · have h0 : (X 0 : MvPolynomial (Fin 2) k).IsWeightedHomogeneous ![(2 : ℤ), 2] 2 :=
        isWeightedHomogeneous_X k _ 0
      have h1 : (X 1 : MvPolynomial (Fin 2) k).IsWeightedHomogeneous ![(2 : ℤ), 2] 2 :=
        isWeightedHomogeneous_X k _ 1
      simpa using h0.add h1
    · simpa using isWeightedHomogeneous_one k ![(2 : ℤ), 2]

variable {k} {Γ} {ν : Multiset I}

/-- KL I: `x_a e_i` has degree `2`. -/
theorem kl_x_mul_e_mem_grade (a : Fin (Multiset.card ν)) (i : Seq ν) :
    (KLRAlgebra.x a * KLRAlgebra.e i : KLRAlgebra k (klQ (k := k) Γ) ν) ∈
      (klGradingDatum k Γ).grade ν 2 :=
  (klGradingDatum k Γ).x_mul_e_mem_grade a i

/-- KL I: `ψ_j e_i` has degree `- i_j · i_{j+1}`. -/
theorem kl_ψ_mul_e_mem_grade {j : ℕ} (h : j + 1 < Multiset.card ν) (i : Seq ν) :
    (KLRAlgebra.ψ j * KLRAlgebra.e i : KLRAlgebra k (klQ (k := k) Γ) ν) ∈
      (klGradingDatum k Γ).grade ν (-cartan Γ (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩)) :=
  (klGradingDatum k Γ).ψ_mul_e_mem_grade h i

end KL1

end Categorification.KLR
