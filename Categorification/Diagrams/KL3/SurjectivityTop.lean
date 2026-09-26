/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SurjectivityWidth
import Categorification.Diagrams.KL3.LocalFiltration
import Categorification.Diagrams.KL3.SortedSplit
import Categorification.Diagrams.KL3.IdempotentLift
import Categorification.KLR.KL2.Prop34KL2
import Categorification.KLR.TensorKLRK0

/-!
# The top step of the proof of KL III Theorem 1.1

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.8.4,
(3.100)–(3.106) and the *Proof of Theorem 1.1*.

Fix a sorted sequence `(+i)(-j)`, `i ∈ Seq ν`, `j ∈ Seq ν'`, of length `m = |ν| + |ν'|`, and
`W = E_{+i} E_{-j} 1_λ {n}`. The endomorphisms of `W` factoring through sequences of length
`< m` form a two-sided ideal `T` (KL III's `I_{ν,-ν',λ}`). Given

* the **spanning hypothesis** `SortedSpan` (KL III §3.2.4: every endomorphism of `E_{+i} E_{-j} 1_λ`
  is a linear combination of split diagrams followed by bubble monomials, modulo diagrams
  factoring through shorter sequences; this is the input from the spanning sets `B_{i,j,λ}` of
  Proposition 3.11 used by KL III in the proof of Proposition 3.36), and
* the **Grothendieck group hypothesis** `TobjHyp`: the class of every 1-morphism
  `(E_{+i} E_{-j} 1_λ {n}, α(g))`, `g` a degree-zero idempotent of `R(ν) ⊗ R(ν')` in the corner
  of `(i, j)`, lies in the image of `γ` (KL III: "`[E_{ν,-ν'} 1_λ, e_{r,r'}]` belongs to image of
  `γ`"),

the top step `TopHyp` of `Categorification.Diagrams.KL3.SurjectivityWidth` holds: an
indecomposable summand `Z` of `W` which is not a summand of a shorter sequence satisfies
`[Z] ∈ γ(_𝒜 U̇) + ∑ [lower indecomposables]` (`topHyp_of_sortedSpan`). Consequently `γ` is
surjective (`gammaUA'_surjective_of_sortedSpan`).

The proof follows KL III: decompose `1 = ∑ α(g_r)` with `g_r` indecomposable idempotents of
`R(ν) ⊗ R(ν')` (`Graded.exists_indec_decomp`); `Z` is a summand of some `(W, α(g_r))`; by the
spanning hypothesis, `α(g_r)` is local modulo `T` (`localModT_alpha`, using that the corner of an
indecomposable idempotent is local and that the bubbles of positive degree generate a nilpotent
ideal in degree zero); so the complement of `Z` in `(W, α(g_r))` has only summands factoring
through shorter sequences (`KrullSchmidtCat.of_sub_mem_closure_low`).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams QuantumGroup
  UDot Presentation GradedBicat KrullSchmidtCat KLR
open scoped TensorProduct

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

/-! ## Endomorphisms of `x{t}` in `U̇` -/

section EndVal

variable {ρ lam : X}

/-- The underlying degree-zero 2-morphism of an endomorphism of `x{t}` in `U̇`. -/
def endVal {x : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)} {t : ℤ}
    (φ : (objOf x t : UKar RD k ρ lam) ⟶ objOf x t) : (pres RD k).obj x.obj ⟶ (pres RD k).obj x.obj :=
  ((incl (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam)).preimage φ).1

theorem endVal_mem {x : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)} {t : ℤ}
    (φ : (objOf x t : UKar RD k ρ lam) ⟶ objOf x t) :
    endVal φ ∈ (pres RD k).homDeg (deg RD) x.obj x.obj (t - t) :=
  ((incl (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam)).preimage φ).2

theorem homOf_endVal {x : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)} {t : ℤ}
    (φ : (objOf x t : UKar RD k ρ lam) ⟶ objOf x t) : homOf (endVal φ) (endVal_mem φ) = φ :=
  (incl (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam)).map_preimage φ

theorem endVal_homOf {x : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)} {t : ℤ}
    (f : (pres RD k).obj x.obj ⟶ (pres RD k).obj x.obj)
    (hf : f ∈ (pres RD k).homDeg (deg RD) x.obj x.obj (t - t)) :
    endVal (homOf f hf : (objOf x t : UKar RD k ρ lam) ⟶ objOf x t) = f := by
  unfold endVal
  rw [Functor.preimage_map]

theorem endVal_comp {x : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)} {t : ℤ}
    (φ ψ : (objOf x t : UKar RD k ρ lam) ⟶ objOf x t) : endVal (φ ≫ ψ) = endVal φ ≫ endVal ψ := by
  unfold endVal
  rw [Functor.preimage_comp]
  rfl

theorem endVal_id {x : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)} {t : ℤ} :
    endVal (𝟙 (objOf x t : UKar RD k ρ lam)) = 𝟙 _ := by
  unfold endVal
  rw [Functor.preimage_id]
  rfl

theorem endVal_injective {x : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)} {t : ℤ} :
    Function.Injective (endVal (x := x) (t := t) (RD := RD) (k := k)) := fun φ ψ h => by
  rw [← homOf_endVal φ, ← homOf_endVal ψ]
  exact homOf_congr h _ _

/-- `endVal` as a linear map. -/
def endValL (x : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)) (t : ℤ) :
    ((objOf x t : UKar RD k ρ lam) ⟶ objOf x t) →ₗ[k]
      ((pres RD k).obj x.obj ⟶ (pres RD k).obj x.obj) where
  toFun := endVal
  map_add' φ ψ := by
    have h := homOf_add (endVal φ) (endVal ψ) (endVal_mem φ) (endVal_mem ψ)
    rw [homOf_endVal, homOf_endVal] at h
    rw [← h, endVal_homOf]
  map_smul' r φ := by
    have h := homOf_smul (P := pres RD k) (deg := deg RD) (l := wtObj RD k ρ) (m := wtObj RD k lam)
      r (endVal φ) (endVal_mem φ)
    rw [homOf_endVal] at h
    rw [← h, endVal_homOf]
    rfl

end EndVal

/-! ## The ideal of endomorphisms factoring through shorter sequences -/

section Thru

theorem comp_mem_thru {μ : X} {w : List (Letter I)} {S : Set (List (Letter I))}
    {a t : (pres RD k).obj (ob RD μ w) ⟶ (pres RD k).obj (ob RD μ w)}
    (ha : a ∈ HomD RD k μ w w 0) (ht : t ∈ thru RD k μ w S) : a ≫ t ∈ thru RD k μ w S := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨u, hu, hw, α, a', b', ha', hb', rfl⟩ := ht
    refine Submodule.subset_span ⟨u, hu, hw, α, a ≫ a', b', ?_, hb', by rw [Category.assoc]⟩
    exact mem_homDeg_of_eq (Presentation.comp_mem_homDeg ha ha') (zero_add α)
  | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx

theorem mem_thru_comp {μ : X} {w : List (Letter I)} {S : Set (List (Letter I))}
    {a t : (pres RD k).obj (ob RD μ w) ⟶ (pres RD k).obj (ob RD μ w)}
    (ha : a ∈ HomD RD k μ w w 0) (ht : t ∈ thru RD k μ w S) : t ≫ a ∈ thru RD k μ w S := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨u, hu, hw, α, a', b', ha', hb', rfl⟩ := ht
    refine Submodule.subset_span ⟨u, hu, hw, α, a', b' ≫ a, ha', ?_, by rw [Category.assoc]⟩
    exact mem_homDeg_of_eq (Presentation.comp_mem_homDeg hb' ha) (add_zero _)
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

variable {ρ lam : X} (w : List (Letter I)) (hw : wt RD lam w = ρ) (n : ℤ)

variable (RD k) in
/-- **The ideal `T` of endomorphisms of `E_w 1_λ {n}` factoring through sequences of length
`< m`** (the degree-zero part of KL III's `I_{ν,-ν',λ}`). -/
def thruIdeal (m : ℕ) : Submodule k (nfObj RD k ρ lam w hw n ⟶ nfObj RD k ρ lam w hw n) :=
  (thru RD k lam w {u | u.length < m}).comap (endValL (nfHom RD k ρ lam w hw) n)

theorem mem_thruIdeal {m : ℕ} {φ : nfObj RD k ρ lam w hw n ⟶ nfObj RD k ρ lam w hw n} :
    φ ∈ thruIdeal RD k w hw n m ↔ endVal φ ∈ thru RD k lam w {u | u.length < m} := Iff.rfl

theorem thruIdeal_isIdeal (m : ℕ) : IsIdealEnd (thruIdeal RD k w hw n m) where
  comp_left x t ht := by
    rw [mem_thruIdeal, endVal_comp]
    exact comp_mem_thru (mem_homDeg_of_eq (endVal_mem x) (sub_self n)) ht
  comp_right t x ht := by
    rw [mem_thruIdeal, endVal_comp]
    exact mem_thru_comp (mem_homDeg_of_eq (endVal_mem x) (sub_self n)) ht

variable [DecidableEq I] [Finite I] (hSL : SimplyLaced C)
include hSL

/-- **An indecomposable retract of `E_w 1_λ {n}` whose idempotent factors through sequences of
length `< m` is a retract of some `E_u 1_λ {n'}` with `|u| < m`.** -/
theorem isLow_of_mem_thruIdeal {m : ℕ} {Q : UKar RD k ρ lam} (hQ : IsIndec Q)
    (f : Q ⟶ nfObj RD k ρ lam w hw n) (g : nfObj RD k ρ lam w hw n ⟶ Q) (hfg : f ≫ g = 𝟙 Q)
    (hT : g ≫ f ∈ thruIdeal RD k w hw n m) : IsLow RD k m Q := by
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  rw [mem_thruIdeal] at hT
  obtain ⟨N, c, x, hx⟩ := Submodule.mem_span_set'.1 hT
  have hgen : ∀ i, (x i).1 ∈ thruGen RD k lam w {u | u.length < m} := fun i => (x i).2
  choose u hu hwu α a b ha hb he using hgen
  have hu' : ∀ i, wt RD lam (u i) = ρ := fun i => (hwu i).trans hw
  let V : Fin N → UKar RD k ρ lam := fun i => nfObj RD k ρ lam (u i) (hu' i) (n - α i)
  let A : ∀ i, Q ⟶ V i := fun i =>
    f ≫ homOf (c i • a i) (mem_homDeg_of_eq (Submodule.smul_mem _ _ (ha i)) (by ring))
  let B : ∀ i, V i ⟶ Q := fun i => homOf (b i) (mem_homDeg_of_eq (hb i) (by ring)) ≫ g
  have htot : ∑ i ∈ Finset.univ, A i ≫ B i = 𝟙 Q := by
    have h1 : ∑ i ∈ Finset.univ, A i ≫ B i =
        f ≫ (∑ i ∈ Finset.univ, homOf ((c i • a i) ≫ b i) (mem_homDeg_of_eq
          (Presentation.comp_mem_homDeg (Submodule.smul_mem _ _ (ha i)) (hb i))
          (show α i + -α i = n - n by ring)) :
          nfObj RD k ρ lam w hw n ⟶ nfObj RD k ρ lam w hw n) ≫ g := by
      simp only [A, B, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Category.assoc (homOf _ _) (homOf _ _), homOf_comp]
    rw [h1, sum_homOf]
    have h2 : (∑ i ∈ Finset.univ, (c i • a i) ≫ b i) = endVal (g ≫ f) := by
      rw [← hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [he i, Linear.smul_comp]
    rw [homOf_congr h2 _ (endVal_mem _), homOf_endVal, ← Category.assoc, ← Category.assoc, hfg,
      Category.id_comp, hfg]
  obtain ⟨i, -, f', g', hfg'⟩ := hQ.exists_retract_of_sum k (𝟙 Q) (𝟙 Q) (Category.id_comp _)
    Finset.univ V A B htot
  exact ⟨u i, hu' i, n - α i, hu i, f', g', hfg'⟩

end Thru

/-! ## The spanning hypothesis -/

section Span

variable (RD k)

/-- Split diagrams `E_{+a} E_{-b} 1_μ → E_{+a} E_{-b} 1_μ` followed by bubble monomials on the far
right. -/
def splitBubSpan (μ : X) (a b : List I) :
    Submodule k (End ((pres RD k).obj (ob RD μ (ups a ++ dns b)))) :=
  Submodule.span k {g | ∃ h ∈ SplitSet RD k μ a b a b, ∃ β : End ((pres RD k).obj (ob RD μ [])),
    IsBub RD k μ β ∧ g = h ≫ bubAt RD k μ (ups a ++ dns b) β}

/-- **The spanning hypothesis** (KL III §3.2.3–§3.2.4, Proposition 3.11 and the discussion of
`END_U(E_{ν,-ν'} 1_λ)`): every endomorphism of a sorted `E_{+a} E_{-b} 1_μ` is a linear
combination of split diagrams followed by bubble monomials, modulo composites of homogeneous
2-morphisms through sequences of length `< |a| + |b|`. -/
def SortedSpan : Prop :=
  ∀ (μ : X) (a b : List I) (f : End ((pres RD k).obj (ob RD μ (ups a ++ dns b)))),
    f ∈ splitBubSpan RD k μ a b ⊔
      Submodule.span k (homGen RD k μ (ups a ++ dns b) {u | u.length < a.length + b.length})

end Span

/-- The degree-zero components of composites through `S` lie in `thru`. -/
theorem homogeneousComponent_zero_mem_thru {μ : X} {w : List (Letter I)}
    {S : Set (List (Letter I))} {x : End ((pres RD k).obj (ob RD μ w))}
    (hx : x ∈ Submodule.span k (homGen RD k μ w S)) :
    Presentation.homogeneousComponent (pres_isHomogeneous (RD := RD) (k := k)) 0 x ∈
      thru RD k μ w S := by
  have hP := pres_isHomogeneous (RD := RD) (k := k)
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, hw, α, β, a, b, ha, hb, rfl⟩ := hx
    have hab := Presentation.comp_mem_homDeg ha hb
    by_cases h0 : α + β = 0
    · rw [Presentation.homogeneousComponent_of_mem hP (mem_homDeg_of_eq hab h0)]
      exact Submodule.subset_span ⟨u, hu, hw, α, a, b, ha,
        mem_homDeg_of_eq hb (by omega), rfl⟩
    · rw [Presentation.homogeneousComponent_of_mem_of_ne hP hab h0]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-! ## The filtration by bubble degree -/

section Filt

variable (k C) in
/-- The tensor product grading of `R(ν) ⊗ R(ν')`. -/
abbrev TG (ν ν' : Multiset I) [DecidableEq I] : ℤ → Submodule k (KLR.R2 k C ν ⊗[k] KLR.R2 k C ν') :=
  Graded.tensorGrading ((klGradingDatum2 k C).grade ν) ((klGradingDatum2 k C).grade ν')


variable [DecidableEq I] (lam : X) {ν ν' : Multiset I} (s₀ : KLR.Seq ν) (t₀ : KLR.Seq ν')

open KLR.Diagram (word)

variable (RD k) in
/-- The `(i, j), (i, j)` entry of `α`. -/
abbrev aent (x : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν') :
    End ((pres RD k).obj (ob RD lam (ups (word s₀) ++ dns (word t₀)))) :=
  alpha RD k lam ν ν' x (s₀, t₀) (s₀, t₀)

/-- The idempotent `e_i ⊗ e_j`. -/
abbrev e₀ : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν' := KLRAlgebra.e s₀ ⊗ₜ KLRAlgebra.e t₀

theorem aent_e₀_mul (x : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν') :
    aent RD k lam s₀ t₀ (e₀ (k := k) s₀ t₀ * x) = aent RD k lam s₀ t₀ x := by
  rw [aent, map_mul, alpha_e, KLR.Diagram.MatEnd.mul_apply, Finset.sum_eq_single (s₀, t₀)]
  · rw [KLR.Diagram.MatEnd.single_apply_self, Category.comp_id]
  · intro j _ hj
    rw [KLR.Diagram.MatEnd.single_apply_of_ne _ (fun h => hj h.1), Limits.comp_zero]
  · simp

theorem aent_mul_e₀ (x : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν') :
    aent RD k lam s₀ t₀ (x * e₀ (k := k) s₀ t₀) = aent RD k lam s₀ t₀ x := by
  rw [aent, map_mul, alpha_e, KLR.Diagram.MatEnd.mul_apply, Finset.sum_eq_single (s₀, t₀)]
  · rw [KLR.Diagram.MatEnd.single_apply_self, Category.id_comp]
  · intro j _ hj
    rw [KLR.Diagram.MatEnd.single_apply_of_ne _ (fun h => hj h.2), Limits.zero_comp]
  · simp

theorem aent_mul (x y : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν') :
    aent RD k lam s₀ t₀ (x * (e₀ (k := k) s₀ t₀ * y)) =
      aent RD k lam s₀ t₀ y ≫ aent RD k lam s₀ t₀ x := by
  have h := (alphaData RD k lam ν ν').α_mul (y := x) (z := e₀ (k := k) s₀ t₀ * y) (j := (s₀, t₀))
    (by rw [← mul_assoc, (show (e₀ (k := k) s₀ t₀) * e₀ s₀ t₀ = e₀ s₀ t₀ by
      rw [Algebra.TensorProduct.tmul_mul_tmul, KLRAlgebra.e_mul_self, KLRAlgebra.e_mul_self])])
    (s₀, t₀) (s₀, t₀)
  rw [alphaData_α] at h
  rw [aent, h]
  exact congrArg (· ≫ _) (aent_e₀_mul lam s₀ t₀ y)

theorem e₀_mem : e₀ (k := k) (C := C) s₀ t₀ ∈ TG C k ν ν' 0 := by
  have := Graded.tmul_mem_tensorGrading ((klGradingDatum2 k C).e_mem_grade s₀)
    ((klGradingDatum2 k C).e_mem_grade t₀)
  simpa using this

variable (RD k) in
/-- **The filtration by bubble degree**: the span of the `α(x) ≫ β` with `x` of degree `-e` and
`β ∈ END_U(1_λ)` of degree `e`, `e ≥ K`. -/
def bubFil (K : ℕ) : Submodule k (End ((pres RD k).obj (ob RD lam (ups (word s₀) ++ dns (word t₀))))) :=
  Submodule.span k {g | ∃ (e : ℕ) (x : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν')
    (β : End ((pres RD k).obj (ob RD lam []))), K ≤ e ∧ x ∈ TG C k ν ν' (-(e : ℤ)) ∧
      β ∈ HDe RD k lam e ∧ g = aent RD k lam s₀ t₀ x ≫ bubAt RD k lam (ups (word s₀) ++ dns (word t₀)) β}

theorem bubFil_anti (K : ℕ) : bubFil RD k lam s₀ t₀ (K + 1) ≤ bubFil RD k lam s₀ t₀ K := by
  refine Submodule.span_mono ?_
  rintro _ ⟨e, x, β, hK, hx, hβ, rfl⟩
  exact ⟨e, x, β, by omega, hx, hβ, rfl⟩

theorem bubFil_mul (K L : ℕ) {f g : End ((pres RD k).obj (ob RD lam (ups (word s₀) ++ dns (word t₀))))}
    (hf : f ∈ bubFil RD k lam s₀ t₀ K) (hg : g ∈ bubFil RD k lam s₀ t₀ L) :
    f ≫ g ∈ bubFil RD k lam s₀ t₀ (K + L) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨e, x, β, hK, hx, hβ, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨e', x', β', hL, hx', hβ', rfl⟩ := hg
      refine Submodule.subset_span ⟨e + e', x' * (e₀ s₀ t₀ * x), β ≫ β', by omega, ?_,
        ?_, ?_⟩
      · have := SetLike.mul_mem_graded hx' (SetLike.mul_mem_graded (e₀_mem (k := k) (C := C) s₀ t₀) hx)
        convert this using 2; push_cast; ring
      · exact mem_homDeg_of_eq (Presentation.comp_mem_homDeg hβ hβ') (by push_cast; ring)
      · rw [aent_mul, bubAt_comp]
        have := bubAt_comm RD k lam β (aent RD k lam s₀ t₀ x')
        simp only [Category.assoc]
        rw [← Category.assoc (bubAt RD k lam _ β), this]
        simp only [Category.assoc]
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r ha
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Preadditive.add_comp]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r ha

theorem aent_comp_bubFil {K : ℕ} {x : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν'} (hx : x ∈ TG C k ν ν' 0)
    {g : End ((pres RD k).obj (ob RD lam (ups (word s₀) ++ dns (word t₀))))} (hg : g ∈ bubFil RD k lam s₀ t₀ K) :
    aent RD k lam s₀ t₀ x ≫ g ∈ bubFil RD k lam s₀ t₀ K ∧
      g ≫ aent RD k lam s₀ t₀ x ∈ bubFil RD k lam s₀ t₀ K := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨e, x', β, hK, hx', hβ, rfl⟩ := hg
    constructor
    · refine Submodule.subset_span ⟨e, x' * (e₀ s₀ t₀ * x), β, hK, ?_, hβ, ?_⟩
      · have := SetLike.mul_mem_graded hx' (SetLike.mul_mem_graded (e₀_mem (k := k) (C := C) s₀ t₀) hx)
        convert this using 2; ring
      · rw [aent_mul, Category.assoc]
    · refine Submodule.subset_span ⟨e, x * (e₀ s₀ t₀ * x'), β, hK, ?_, hβ, ?_⟩
      · have := SetLike.mul_mem_graded hx (SetLike.mul_mem_graded (e₀_mem (k := k) (C := C) s₀ t₀) hx')
        convert this using 2; ring
      · rw [aent_mul, Category.assoc, bubAt_comm RD k lam β, Category.assoc]
  | zero => simp
  | add a b _ _ ha hb =>
    exact ⟨by rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha.1 hb.1,
      by rw [Preadditive.add_comp]; exact Submodule.add_mem _ ha.2 hb.2⟩
  | smul r a _ ha =>
    exact ⟨by rw [Linear.comp_smul]; exact Submodule.smul_mem _ r ha.1,
      by rw [Linear.smul_comp]; exact Submodule.smul_mem _ r ha.2⟩

theorem bubFil_eventually_bot : ∃ K₀ : ℕ, bubFil RD k lam s₀ t₀ (K₀ + 1) = ⊥ := by
  obtain ⟨N, hN⟩ := Graded.exists_grade_eq_bot_of_hasGdim (TG C k ν ν')
  refine ⟨(-N).toNat, eq_bot_iff.2 (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨e, x, β, hK, hx, hβ, rfl⟩
  have hlt : -(e : ℤ) < N := by omega
  rw [hN _ hlt, Submodule.mem_bot] at hx
  subst hx
  simp [aent]

theorem bubFil_le_homD (K : ℕ) : bubFil RD k lam s₀ t₀ K ≤ HomD RD k lam (ups (word s₀) ++ dns (word t₀)) (ups (word s₀) ++ dns (word t₀)) 0 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨e, x, β, hK, hx, hβ, rfl⟩
  have h1 := alpha_mem RD k (μ := lam) hx (s₀, t₀) (s₀, t₀)
  have h2 := bubAt_mem (RD := RD) (k := k) lam (ups (word s₀) ++ dns (word t₀)) hβ
  have := Presentation.comp_mem_homDeg h1 h2
  exact mem_homDeg_of_eq this (by ring)

end Filt

/-! ## Degree-zero endomorphisms modulo the ideal -/

section Span0

variable [DecidableEq I] (lam : X) {ν ν' : Multiset I} (s₀ : KLR.Seq ν) (t₀ : KLR.Seq ν')

open KLR.Diagram (word)

variable (RD k) in
/-- `x ↦ α(x)_{(i,j),(i,j)}` as a linear map. -/
def aentL : (KLR.R2 k C ν ⊗[k] KLR.R2 k C ν') →ₗ[k]
    End ((pres RD k).obj (ob RD lam (ups (word s₀) ++ dns (word t₀)))) where
  toFun := aent RD k lam s₀ t₀
  map_add' x y := by simp only [aent, map_add]; rfl
  map_smul' r x := by simp only [aent, map_smul]; rfl

omit [DecidableEq I] in
theorem bubMon_zero (μ : X) : bubMon RD k μ 0 = 𝟙 _ := by
  simp [bubMon]

/-- **Degree-zero endomorphisms of a sorted `E_{+i} E_{-j} 1_λ`, modulo the ideal**: under the
spanning hypothesis, every degree-zero endomorphism is `α(x₀) + n` modulo endomorphisms factoring
through shorter sequences, with `x₀ ∈ (R(ν) ⊗ R(ν'))_0` and `n` in the span of the
`α(x) ≫ β`, `β` bubbles of positive degree. -/
theorem exists_aent_add_bubFil (hspan : SortedSpan RD k)
    {f : End ((pres RD k).obj (ob RD lam (ups (word s₀) ++ dns (word t₀))))}
    (hf : f ∈ HomD RD k lam (ups (word s₀) ++ dns (word t₀)) (ups (word s₀) ++ dns (word t₀)) 0) :
    ∃ x₀ ∈ TG C k ν ν' 0, ∃ n ∈ bubFil RD k lam s₀ t₀ 1,
      f - aent RD k lam s₀ t₀ x₀ - n ∈
        thru RD k lam (ups (word s₀) ++ dns (word t₀)) {u | u.length < (word s₀).length + (word t₀).length} := by
  have hP := pres_isHomogeneous (RD := RD) (k := k)
  set G := (TG C k ν ν' 0).map (aentL RD k lam s₀ t₀) ⊔ bubFil RD k lam s₀ t₀ 1 with hG
  -- the generators
  have hgen : ∀ (h : End ((pres RD k).obj (ob RD lam (ups (word s₀) ++ dns (word t₀)))))
      (β : End ((pres RD k).obj (ob RD lam []))), h ∈ SplitSet RD k lam (word s₀) (word t₀)
        (word s₀) (word t₀) → IsBub RD k lam β →
      Presentation.homogeneousComponent hP 0 (h ≫ bubAt RD k lam _ β) ∈ G := by
    intro h β hh hβ
    obtain ⟨D, U, hD, hU, hDc, hUc, hh'⟩ := hh
    set L := D.map (whL (ups (word s₀)) []) ++ U.map (whL [] (dns (word t₀)))
    have hhd : h ∈ HomD RD k lam _ _ (sdegSum RD lam L) := by rw [hh']; exact dg_mem_homD rfl
    have hsplit : h ∈ SplitSet RD k lam (word s₀) (word t₀) (word s₀) (word t₀) :=
      ⟨D, U, hD, hU, hDc, hUc, hh'⟩
    -- reduce to bubble monomials
    let Φ : End ((pres RD k).obj (ob RD lam [])) →ₗ[k]
        End ((pres RD k).obj (ob RD lam (ups (word s₀) ++ dns (word t₀)))) :=
      (Presentation.homogeneousComponent hP 0).comp
        ((Linear.leftComp k _ h).comp (bubAt RD k lam (ups (word s₀) ++ dns (word t₀))))
    have hΦ : Submodule.span k (Set.range (bubMon RD k lam)) ≤ G.comap Φ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨m, rfl⟩
      show Presentation.homogeneousComponent hP 0 (h ≫ bubAt RD k lam _ (bubMon RD k lam m)) ∈ G
      have hb := bubAt_mem (RD := RD) (k := k) lam (ups (word s₀) ++ dns (word t₀))
        (bubMon_mem (RD := RD) (k := k) lam m)
      have hprod := Presentation.comp_mem_homDeg hhd hb
      by_cases h0 : sdegSum RD lam L + Finsupp.weight (wPi C) m = 0
      · rw [Presentation.homogeneousComponent_of_mem hP (mem_homDeg_of_eq hprod h0)]
        have hwt := weight_wPi_nonneg (C := C) m
        by_cases he : Finsupp.weight (wPi C) m = 0
        · -- degree zero: a split diagram
          rw [weight_wPi_eq_zero he, bubMon_zero, bubAt_id, Category.comp_id]
          obtain ⟨x, hx, hxe⟩ := exists_alpha_eq_split_mem RD k lam ν ν' s₀ s₀ t₀ t₀ (d := 0)
            hsplit (mem_homDeg_of_eq hhd (by omega))
          exact Submodule.mem_sup_left ⟨x, hx, hxe⟩
        · -- positive degree
          set e := Finsupp.weight (wPi C) m with he_def
          have he1 : 1 ≤ e.toNat := by omega
          have hde : sdegSum RD lam L = -((e.toNat : ℕ) : ℤ) := by omega
          obtain ⟨x, hx, hxe⟩ := exists_alpha_eq_split_mem RD k lam ν ν' s₀ s₀ t₀ t₀ hsplit
            (mem_homDeg_of_eq hhd hde)
          refine Submodule.mem_sup_right (Submodule.subset_span ⟨e.toNat,
            x, bubMon RD k lam m, he1, hx, ?_, by rw [← hxe]⟩)
          exact mem_homDeg_of_eq (bubMon_mem (RD := RD) (k := k) lam m) (by omega)
      · rw [Presentation.homogeneousComponent_of_mem_of_ne hP hprod h0]
        exact Submodule.zero_mem _
    exact hΦ (isBub_mem_span hβ)
  -- the sum
  have key : ∀ g ∈ splitBubSpan RD k lam (word s₀) (word t₀),
      Presentation.homogeneousComponent hP 0 g ∈ G := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨h, hh, β, hβ, rfl⟩ := hg
      exact hgen h β hh hβ
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  obtain ⟨g₁, hg₁, g₂, hg₂, hsum⟩ := Submodule.mem_sup.1 (hspan lam (word s₀) (word t₀) f)
  have h1 := key g₁ hg₁
  have h2 := homogeneousComponent_zero_mem_thru hg₂
  obtain ⟨y, hy, n, hn, hyn⟩ := Submodule.mem_sup.1 h1
  obtain ⟨x₀, hx₀, rfl⟩ := hy
  refine ⟨x₀, hx₀, n, hn, ?_⟩
  have hf0 : f = Presentation.homogeneousComponent hP 0 f :=
    (Presentation.homogeneousComponent_of_mem hP hf).symm
  rw [hf0, ← hsum, map_add, ← hyn]
  convert h2 using 1
  change _ = Presentation.homogeneousComponent hP 0 g₂
  simp only [aentL, LinearMap.coe_mk, AddHom.coe_mk]
  have key : ∀ {M : Type _} [AddCommGroup M] (a b c : M), a + b + c - a - b = c := by
    intros; abel
  exact key (M := (pres RD k).obj (ob RD lam (ups (word s₀) ++ dns (word t₀))) ⟶
    (pres RD k).obj (ob RD lam (ups (word s₀) ++ dns (word t₀)))) _ _ _

end Span0

/-! ## Images of idempotents -/

section IdemRetract

variable {ρ lam : X} {x : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)} {t : ℤ}
  {e : (pres RD k).obj x.obj ⟶ (pres RD k).obj x.obj}
  (he : e ∈ (pres RD k).homDeg (deg RD) x.obj x.obj 0) (hee : e ≫ e = e)

/-- The inclusion of the image `(x{t}, e)` into `x{t}`. -/
def idemIncl : (idemObj x t e he hee : UKar RD k ρ lam) ⟶ objOf x t where
  f := (Mat_.embedding (GrObj (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam))).map
    (X := ⟨x, t⟩) (Y := ⟨x, t⟩) ⟨e, mem_homDeg_of_eq he (sub_self t).symm⟩
  comm := by
    show _ = (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp]
    congr 1
    exact Subtype.ext hee.symm

/-- The projection of `x{t}` onto the image `(x{t}, e)`. -/
def idemProj : (objOf x t : UKar RD k ρ lam) ⟶ idemObj x t e he hee where
  f := (Mat_.embedding (GrObj (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam))).map
    (X := ⟨x, t⟩) (Y := ⟨x, t⟩) ⟨e, mem_homDeg_of_eq he (sub_self t).symm⟩
  comm := by
    show _ = 𝟙 _ ≫ (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _
    rw [Category.id_comp, ← Functor.map_comp]
    congr 1
    exact Subtype.ext hee.symm

theorem idemIncl_idemProj : idemIncl (t := t) he hee ≫ idemProj he hee = 𝟙 _ := by
  apply Karoubi.hom_ext
  show (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = (Mat_.embedding _).map _
  rw [← Functor.map_comp]
  congr 1
  exact Subtype.ext hee

theorem idemProj_idemIncl :
    idemProj (t := t) he hee ≫ idemIncl he hee =
      homOf e (mem_homDeg_of_eq he (sub_self t).symm) := by
  apply Karoubi.hom_ext
  show (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = (Mat_.embedding _).map _
  rw [← Functor.map_comp]
  congr 1
  exact Subtype.ext hee

end IdemRetract

/-! ## The transfer data with a prescribed left weight -/

section DataR

variable [DecidableEq I] (lam : X) (ν ν' : Multiset I)

open KLR.Diagram (word)

variable (RD k) in
/-- `alphaData` with the left weight `ρ` of `E_{+i} E_{-j} 1_λ` given by a proof. -/
def alphaDataR (ρ : X) (hρ : rhoS RD lam ν ν' = ρ) :
    TransferData (P := pres RD k) (deg := deg RD) (TG C k ν ν')
      (fun p : KLR.Seq ν × KLR.Seq ν' =>
        nfHom RD k ρ lam (ups (word p.1) ++ dns (word p.2)) ((wt_ZS RD lam ν ν' p).trans hρ))
      (fun p => KLRAlgebra.e p.1 ⊗ₜ KLRAlgebra.e p.2) where
  α := alpha RD k lam ν ν'
  α_e p := alpha_e RD k lam ν ν' p.1 p.2
  α_mem hr i j := alpha_mem RD k hr i j

variable (RD k) in
/-- **The Grothendieck group hypothesis**: the classes of the 1-morphisms
`(E_{+i} E_{-j} 1_λ {t}, α(g))`, `g` a degree-zero idempotent of `R(ν) ⊗ R(ν')` in the corner of
`(i, j)`, lie in the image of `γ` (KL III, end of the proof of Theorem 1.1). -/
def TobjHyp : Prop :=
  ∀ (lam ρ : X) (ν ν' : Multiset I) (hρ : rhoS RD lam ν ν' = ρ) (p : KLR.Seq ν × KLR.Seq ν')
    (F : TCorner (TG C k ν ν') (fun p : KLR.Seq ν × KLR.Seq ν' =>
      (KLRAlgebra.e p.1 ⊗ₜ KLRAlgebra.e p.2 : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν')) p) (t : ℤ),
    K0U.cl (tobj (alphaDataR RD k lam ν ν' ρ hρ) F t) ∈ gammaImg RD k lam ρ

end DataR

/-! ## The local property -/

section Local

variable [DecidableEq I] {lam ρ : X} {ν ν' : Multiset I} (s₀ : KLR.Seq ν) (t₀ : KLR.Seq ν')
  (hw : wt RD lam (ups (KLR.Diagram.word s₀) ++ dns (KLR.Diagram.word t₀)) = ρ) (n : ℤ)

open KLR.Diagram (word)

theorem aent_mem_zero {x : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν'} (hx : x ∈ TG C k ν ν' 0) :
    aent RD k lam s₀ t₀ x ∈ (pres RD k).homDeg (deg RD) (ob RD lam (ups (word s₀) ++ dns (word t₀)))
      (ob RD lam (ups (word s₀) ++ dns (word t₀))) (n - n) :=
  mem_homDeg_of_eq (alpha_mem RD k (μ := lam) hx (s₀, t₀) (s₀, t₀)) (sub_self n).symm

theorem aent_mul' (x y : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν') (hy : e₀ (k := k) (C := C) s₀ t₀ * y = y) :
    aent RD k lam s₀ t₀ (x * y) = aent RD k lam s₀ t₀ y ≫ aent RD k lam s₀ t₀ x := by
  conv_lhs => rw [← hy]
  exact aent_mul lam s₀ t₀ x y

variable [Finite I] (hSL : SimplyLaced C)

omit [Finite I] in
/-- **An indecomposable idempotent `g` of `R(ν) ⊗ R(ν')` acts on `E_{+i} E_{-j} 1_λ {n}` by an
idempotent which is local modulo the ideal of endomorphisms factoring through shorter
sequences** (KL III §3.8.4, from Propositions 3.32 and 3.36; under the spanning hypothesis). -/
theorem localModT_alpha (hspan : SortedSpan RD k) {g : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν'}
    (hg : Graded.IdemLe (𝒜 := TG C k ν ν') g (e₀ (k := k) (C := C) s₀ t₀))
    (hind : (Graded.GProj.ofIdempotent (𝒜 := TG C k ν ν') g hg.idem hg.deg0).IsIndec
      (KLR.R2 k C ν ⊗[k] KLR.R2 k C ν')) :
    LocalModT (thruIdeal RD k (ups (word s₀) ++ dns (word t₀)) hw n
        ((word s₀).length + (word t₀).length))
      (homOf (aent RD k lam s₀ t₀ g) (aent_mem_zero s₀ t₀ n hg.deg0)) := by
  set W := nfObj RD k ρ lam (ups (word s₀) ++ dns (word t₀)) hw n
  set T := thruIdeal RD k (ups (word s₀) ++ dns (word t₀)) hw n ((word s₀).length + (word t₀).length)
  have hT := thruIdeal_isIdeal (RD := RD) (k := k) (ups (word s₀) ++ dns (word t₀)) hw n
    ((word s₀).length + (word t₀).length)
  have hge : e₀ (k := k) (C := C) s₀ t₀ * g = g := hg.left
  have heg : g * e₀ (k := k) (C := C) s₀ t₀ = g := hg.right
  have hcorner : ∀ x : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν', g * x * g = x →
      e₀ (k := k) (C := C) s₀ t₀ * x = x := fun x hx => by
    rw [← hx, ← mul_assoc, ← mul_assoc, hge]
  -- lifting degree-zero endomorphisms
  let lift : ∀ f : End ((pres RD k).obj (ob RD lam (ups (word s₀) ++ dns (word t₀)))),
      f ∈ HomD RD k lam (ups (word s₀) ++ dns (word t₀)) (ups (word s₀) ++ dns (word t₀)) 0 →
      (W ⟶ W) := fun f hf => homOf f (mem_homDeg_of_eq hf (sub_self n).symm)
  have hlift : ∀ f hf, endVal (lift f hf) = f := fun f hf => endVal_homOf _ _
  set ε : W ⟶ W := homOf (aent RD k lam s₀ t₀ g) (aent_mem_zero s₀ t₀ n hg.deg0)
  have hεv : endVal ε = aent RD k lam s₀ t₀ g := endVal_homOf _ _
  let S : Set (W ⟶ W) := {φ | ∃ x ∈ TG C k ν ν' 0, g * x * g = x ∧ endVal φ = aent RD k lam s₀ t₀ x}
  let F : ℕ → Submodule k (W ⟶ W) := fun K =>
    (bubFil RD k lam s₀ t₀ K).comap (endValL (nfHom RD k ρ lam (ups (word s₀) ++ dns (word t₀)) hw) n)
  have hinj := endVal_injective (RD := RD) (k := k) (x := nfHom RD k ρ lam (ups (word s₀) ++ dns (word t₀)) hw) (t := n)
  obtain ⟨K₀, hK₀⟩ := bubFil_eventually_bot (RD := RD) (k := k) lam s₀ t₀
  refine localModT_of_filtration hT ?_ S ⟨g, hg.deg0, by rw [hg.idem.eq, hg.idem.eq], hεv⟩ ?_ ?_ ?_ F K₀
    ?_ ?_ ?_ ?_ ?_
  · -- `ε` is idempotent
    apply hinj
    rw [endVal_comp, hεv, ← aent_mul' s₀ t₀ g g hge, hg.idem.eq]
  · -- `S` lies in the corner
    rintro φ ⟨x, hx, hxc, hφ⟩
    have hxg : x * g = x := by rw [← hxc, mul_assoc, hg.idem.eq]
    have hgx : g * x = x := by rw [← hxc, ← mul_assoc, ← mul_assoc, hg.idem.eq]
    constructor
    · apply hinj
      rw [endVal_comp, hεv, hφ, ← aent_mul' s₀ t₀ x g hge, hxg]
    · apply hinj
      rw [endVal_comp, hεv, hφ, ← aent_mul' s₀ t₀ g x (hcorner x hxc), hgx]
  · -- `S` is closed under composition
    rintro φ ⟨x, hx, hxc, hφ⟩ ψ ⟨x', hx', hxc', hψ⟩
    refine ⟨x' * x, by simpa using SetLike.mul_mem_graded hx' hx, ?_, ?_⟩
    · have hxg : x * g = x := by rw [← hxc, mul_assoc, hg.idem.eq]
      have hgx' : g * x' = x' := by rw [← hxc', ← mul_assoc, ← mul_assoc, hg.idem.eq]
      calc g * (x' * x) * g = (g * x') * (x * g) := by simp only [mul_assoc]
        _ = x' * x := by rw [hgx', hxg]
    · rw [endVal_comp, hφ, hψ, aent_mul' s₀ t₀ x' x (hcorner x hxc)]
  · -- elements of `S` are nilpotent or invertible
    rintro φ ⟨x, hx, hxc, hφ⟩
    have hpow : ∀ j : ℕ, endVal (compPow φ (j + 1)) = aent RD k lam s₀ t₀ (x ^ (j + 1)) := by
      intro j
      induction j with
      | zero => rw [compPow_one, pow_one, hφ]
      | succ j ih =>
        rw [compPow_succ, endVal_comp, ih, hφ, pow_succ' x (j + 1),
          aent_mul' s₀ t₀ x (x ^ (j + 1))]
        rw [pow_succ', ← mul_assoc, hcorner x hxc]
    rcases Graded.isNilpotent_or_isUnit_corner hind hx hxc with ⟨N, hN⟩ | ⟨z, hz, hzc, hxz, hzx⟩
    · left
      refine ⟨N, hinj ?_⟩
      rw [hpow, pow_succ, hN, zero_mul,
        show endVal (0 : W ⟶ W) = 0 from
          (endValL (nfHom RD k ρ lam (ups (word s₀) ++ dns (word t₀)) hw) n).map_zero]
      simp [aent]
    · right
      refine ⟨homOf (aent RD k lam s₀ t₀ z) (aent_mem_zero s₀ t₀ n hz), ⟨z, hz, hzc, endVal_homOf _ _⟩,
        ?_, ?_⟩
      · apply hinj
        rw [endVal_comp, hφ, endVal_homOf, hεv, ← aent_mul' s₀ t₀ z x (hcorner x hxc), hzx]
      · apply hinj
        rw [endVal_comp, hφ, endVal_homOf, hεv, ← aent_mul' s₀ t₀ x z (hcorner z hzc), hxz]
  · -- the filtration vanishes in degree `K₀ + 1`
    refine eq_bot_iff.2 fun φ hφ => ?_
    have : endVal φ = 0 := by
      have h := hφ
      simp only [F, Submodule.mem_comap, hK₀, Submodule.mem_bot] at h
      exact h
    rw [Submodule.mem_bot]
    apply hinj
    rw [this]
    exact ((endValL (nfHom RD k ρ lam (ups (word s₀) ++ dns (word t₀)) hw) n).map_zero).symm
  · intro K; exact Submodule.comap_mono (bubFil_anti lam s₀ t₀ K)
  · intro K L x y hx hy
    simp only [F, Submodule.mem_comap] at hx hy ⊢
    change endVal (x ≫ y) ∈ bubFil RD k lam s₀ t₀ (K + L)
    rw [endVal_comp]
    exact bubFil_mul lam s₀ t₀ K L hx hy
  · rintro φ ⟨x, hx, hxc, hφ⟩ K ψ hψ
    simp only [F, Submodule.mem_comap] at hψ ⊢
    have h := aent_comp_bubFil lam s₀ t₀ hx (g := endVal ψ) hψ
    constructor
    · change endVal (φ ≫ ψ) ∈ bubFil RD k lam s₀ t₀ K
      rw [endVal_comp, hφ]; exact h.1
    · change endVal (ψ ≫ φ) ∈ bubFil RD k lam s₀ t₀ K
      rw [endVal_comp, hφ]; exact h.2
  · -- the spanning statement
    intro y hy
    have hy0 : endVal y ∈ HomD RD k lam (ups (word s₀) ++ dns (word t₀)) (ups (word s₀) ++ dns (word t₀)) 0 :=
      mem_homDeg_of_eq (endVal_mem y) (sub_self n)
    obtain ⟨x₀, hx₀, nb, hnb, hdiff⟩ := exists_aent_add_bubFil lam s₀ t₀ hspan hy0
    have hnb0 := bubFil_le_homD lam s₀ t₀ 1 hnb
    have he₀0 := e₀_mem (k := k) (C := C) s₀ t₀
    set x₁ := e₀ (k := k) (C := C) s₀ t₀ * x₀ * e₀ s₀ t₀ with hx₁def
    have hx₁ : x₁ ∈ TG C k ν ν' 0 := by
      have := SetLike.mul_mem_graded (SetLike.mul_mem_graded he₀0 hx₀) he₀0
      simpa using this
    have hx₁e : aent RD k lam s₀ t₀ x₁ = aent RD k lam s₀ t₀ x₀ := by
      rw [hx₁def, aent_mul_e₀, aent_e₀_mul]
    have he₀e₀ : e₀ (k := k) (C := C) s₀ t₀ * e₀ s₀ t₀ = e₀ s₀ t₀ := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, KLRAlgebra.e_mul_self, KLRAlgebra.e_mul_self]
    have hx₁l : e₀ (k := k) (C := C) s₀ t₀ * x₁ = x₁ := by
      rw [hx₁def, ← mul_assoc, ← mul_assoc, he₀e₀]
    have hs'mem : aent RD k lam s₀ t₀ x₀ ∈
        HomD RD k lam (ups (word s₀) ++ dns (word t₀)) (ups (word s₀) ++ dns (word t₀)) 0 :=
      mem_homDeg_of_eq (alpha_mem RD k (μ := lam) hx₀ (s₀, t₀) (s₀, t₀)) rfl
    set s' := lift (aent RD k lam s₀ t₀ x₀) hs'mem
    set n' := lift nb hnb0
    have hgx₁ : e₀ (k := k) (C := C) s₀ t₀ * (g * x₁) = g * x₁ := by rw [← mul_assoc, hge]
    refine ⟨ε ≫ s' ≫ ε, ⟨g * x₁ * g, ?_, ?_, ?_⟩, ε ≫ n' ≫ ε, ?_, ?_⟩
    · have := SetLike.mul_mem_graded (SetLike.mul_mem_graded hg.deg0 hx₁) hg.deg0
      simpa using this
    · calc g * (g * x₁ * g) * g = (g * g) * x₁ * (g * g) := by simp only [mul_assoc]
        _ = g * x₁ * g := by rw [hg.idem.eq]
    · rw [endVal_comp, endVal_comp, hεv, hlift _ hs'mem, ← hx₁e, ← Category.assoc,
        ← aent_mul' s₀ t₀ x₁ g hge, ← aent_mul' s₀ t₀ g (x₁ * g) (by rw [← mul_assoc, hx₁l])]
      congr 1
      simp only [hx₁def, mul_assoc]
    · simp only [F, Submodule.mem_comap]
      change endVal (ε ≫ n' ≫ ε) ∈ bubFil RD k lam s₀ t₀ 1
      rw [endVal_comp, endVal_comp, hεv, hlift nb hnb0]
      exact (aent_comp_bubFil lam s₀ t₀ hg.deg0
        (aent_comp_bubFil lam s₀ t₀ hg.deg0 hnb).2).1
    · have hmem : y - s' - n' ∈ T := by
        rw [mem_thruIdeal]
        have h1 : endVal (y - s' - n') = endVal y - endVal s' - endVal n' := by
          change endValL (nfHom RD k ρ lam (ups (word s₀) ++ dns (word t₀)) hw) n (y - s' - n') =
            endValL _ n y - endValL _ n s' - endValL _ n n'
          rw [map_sub, map_sub]
        rw [h1, hlift _ hs'mem, hlift nb hnb0]
        exact hdiff
      have e2 : y - ε ≫ s' ≫ ε - ε ≫ n' ≫ ε = ε ≫ (y - s' - n') ≫ ε := by
        rw [Preadditive.sub_comp, Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_sub,
          hy]
      rw [e2]
      exact hT.comp_left _ _ (hT.comp_right _ _ hmem)

end Local

/-! ## The top step and the surjectivity of `γ` -/

section Top

variable [DecidableEq I]

open KLR.Diagram (word)

variable [Finite I] (hSL : SimplyLaced C)
include hSL

/-- **The top step, for sequences.** -/
theorem top_of_seq (hspan : SortedSpan RD k) (htobj : TobjHyp RD k) {ρ lam : X}
    {ν ν' : Multiset I} (s₀ : KLR.Seq ν) (t₀ : KLR.Seq ν')
    (hw : wt RD lam (ups (word s₀) ++ dns (word t₀)) = ρ) (n : ℤ) {Z : UKar RD k ρ lam}
    (hZ : IsIndec Z) (f : Z ⟶ nfObj RD k ρ lam (ups (word s₀) ++ dns (word t₀)) hw n)
    (g : nfObj RD k ρ lam (ups (word s₀) ++ dns (word t₀)) hw n ⟶ Z) (hfg : f ≫ g = 𝟙 Z)
    (hlow : ¬ IsLow RD k ((word s₀).length + (word t₀).length) Z) :
    K0U.cl Z ∈ gammaImg RD k lam ρ ⊔ lowSpanU RD k ρ lam ((word s₀).length + (word t₀).length) := by
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  set m := (word s₀).length + (word t₀).length
  have hρ : rhoS RD lam ν ν' = ρ := (wt_ZS RD lam ν ν' (s₀, t₀)).symm.trans hw
  set D := alphaDataR RD k lam ν ν' ρ hρ
  have he₀0 := e₀_mem (k := k) (C := C) s₀ t₀
  have he₀i : IsIdempotentElem (e₀ (k := k) (C := C) s₀ t₀) := by
    show e₀ (k := k) (C := C) s₀ t₀ * e₀ s₀ t₀ = e₀ s₀ t₀
    rw [Algebra.TensorProduct.tmul_mul_tmul, KLRAlgebra.e_mul_self, KLRAlgebra.e_mul_self]
  obtain ⟨M, gs, hgs, hind, horth, hsum⟩ := Graded.exists_indec_decomp (𝒜 := TG C k ν ν')
    (Module.finrank k (Graded.cornerZero (𝒜 := TG C k ν ν') (e₀ (k := k) (C := C) s₀ t₀)) + 1)
    (e₀ (k := k) (C := C) s₀ t₀) he₀i he₀0 (Nat.lt_succ_self _)
  let F : ∀ j, TCorner (TG C k ν ν') (fun p : KLR.Seq ν × KLR.Seq ν' =>
      (KLRAlgebra.e p.1 ⊗ₜ KLRAlgebra.e p.2 : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν')) (s₀, t₀) :=
    fun j => ⟨gs j, (hgs j).deg0, (hgs j).idem.eq, (hgs j).left⟩
  let E : Fin M → UKar RD k ρ lam := fun j => tobj D (F j) n
  let ι : ∀ j, E j ⟶ nfObj RD k ρ lam (ups (word s₀) ++ dns (word t₀)) hw n := fun j =>
    idemIncl (D.α_mem (F j).deg0 (s₀, t₀) (s₀, t₀)) (F j).α_idem
  let π : ∀ j, nfObj RD k ρ lam (ups (word s₀) ++ dns (word t₀)) hw n ⟶ E j := fun j =>
    idemProj (D.α_mem (F j).deg0 (s₀, t₀) (s₀, t₀)) (F j).α_idem
  -- the idempotents sum to the identity
  have htot : ∑ j ∈ Finset.univ, π j ≫ ι j = 𝟙 _ := by
    simp only [π, ι, idemProj_idemIncl]
    rw [sum_homOf]
    refine homOf_eq_id ?_ _
    have : ∑ j, D.α (gs j) (s₀, t₀) (s₀, t₀) = D.α (e₀ (k := k) (C := C) s₀ t₀) (s₀, t₀) (s₀, t₀) := by
      rw [← hsum, map_sum, KLR.Diagram.MatEnd.sum_apply]
    rw [this]
    erw [D.α_e (s₀, t₀)]
    exact KLR.Diagram.MatEnd.single_apply_self _ _ _
  obtain ⟨j, -, f', g', hfg'⟩ := hZ.exists_retract_of_sum k f g hfg Finset.univ E π ι htot
  have hloc := localModT_alpha (RD := RD) (k := k) (lam := lam) s₀ t₀ hw n hspan (hgs j) (hind j)
  have hclos := of_sub_mem_closure_low (thruIdeal_isIdeal (RD := RD) (k := k)
      (ups (word s₀) ++ dns (word t₀)) hw n m) (IsLow RD k m)
    (fun Q f₁ g₁ h₁ h₂ hQ => isLow_of_mem_thruIdeal (ups (word s₀) ++ dns (word t₀)) hw n hSL hQ
      f₁ g₁ h₁ h₂)
    hloc (ι j) (π j) (idemIncl_idemProj _ _) (idemProj_idemIncl _ _) hZ f' g' hfg' hlow
  have hE : K0U.cl (E j) ∈ gammaImg RD k lam ρ := htobj lam ρ ν ν' hρ (s₀, t₀) (F j) n
  have hlowle : AddSubmonoid.closure {x | ∃ Q : UKar RD k ρ lam, IsIndec Q ∧ IsLow RD k m Q ∧
      x = SplitK0.of Q} ≤ (lowSpanU RD k ρ lam m).toAddSubmonoid := by
    rw [AddSubmonoid.closure_le]
    rintro _ ⟨Q, hQ, hQl, rfl⟩
    exact Submodule.subset_span ⟨Q, hQ, hQl, rfl⟩
  have h2 : SplitK0.of (E j) - K0U.cl Z ∈ lowSpanU RD k ρ lam m := hlowle hclos
  have : K0U.cl Z = K0U.cl (E j) - (SplitK0.of (E j) - K0U.cl Z) := by abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left hE) (Submodule.mem_sup_right h2)

/-- **The top step of KL III's proof of Theorem 1.1**, from the spanning and Grothendieck group
hypotheses. -/
theorem topHyp_of_sortedSpan (hspan : SortedSpan RD k) (htobj : TobjHyp RD k) (ρ lam : X) :
    TopHyp RD k ρ lam := by
  intro a b hab n Z hZ ⟨f, g, hfg⟩ hlow
  have ha := word_seqOfList a
  have hb := word_seqOfList b
  have hl : ups a ++ dns b = ups (word (seqOfList a)) ++ dns (word (seqOfList b)) := by rw [ha, hb]
  have hab' : wt RD lam (ups (word (seqOfList a)) ++ dns (word (seqOfList b))) = ρ := hl ▸ hab
  have hobj : nfObj RD k ρ lam (ups a ++ dns b) hab n =
      nfObj RD k ρ lam (ups (word (seqOfList a)) ++ dns (word (seqOfList b))) hab' n := by
    congr 1
  have hm : (word (seqOfList a)).length + (word (seqOfList b)).length = a.length + b.length := by
    rw [ha, hb]
  have := top_of_seq hSL hspan htobj (seqOfList a) (seqOfList b) hab' n hZ
    (f ≫ eqToHom hobj) (eqToHom hobj.symm ≫ g) (by simp [hfg]) (by rw [hm]; exact hlow)
  rwa [hm] at this

/-- **KL III Theorem 1.1 (surjectivity of `γ : _𝒜 U̇ → K₀(U̇)`), conditional on the spanning
hypothesis `SortedSpan` and the Grothendieck group hypothesis `TobjHyp`** (simply-laced Cartan
data, `I` finite, `k` a field). -/
theorem gammaUA'_surjective_of_sortedSpan (hspan : SortedSpan RD k) (htobj : TobjHyp RD k)
    (lam ρ : X) : Function.Surjective (gammaUA' (RD := RD) (k := k) hSL lam ρ) :=
  gammaUA'_surjective_of_topHyp hSL (topHyp_of_sortedSpan hSL hspan htobj ρ lam)

end Top

end Categorification.KL3.Diagram
