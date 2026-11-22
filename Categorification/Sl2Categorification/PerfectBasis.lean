/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.SimpleHead
import Categorification.Sl2Categorification.TopDividedPowerSimple
import Categorification.Sl2Categorification.WeakCategorificationOp

/-!
# Simple classes form a perfect basis

Berenstein–Kazhdan, *Geometric and unipotent crystals II*, arXiv:math/0601391v3,
Definition 5.30: a weight basis `B` of a locally finite module is *perfect* if for each `i` there
is a partial bijection `ẽᵢ` of `B` with `ẽᵢ b` defined exactly when `eᵢ b ≠ 0`, and then
`eᵢ b ∈ c · ẽᵢ b + V_i^{< ℓᵢ(b) - 1}` for a nonzero scalar `c`. Here `ℓᵢ(v)` is the largest `l`
with `eᵢ^l v ≠ 0` (`hPlus`) and `V_i^{< l} = ker eᵢ^l`. The condition involves one index at a
time; `IsPerfectBasis` is the condition for one endomorphism `e`, over `ℚ`.

For a weak `𝔰𝔩₂`-categorification (Chuang–Rouquier, arXiv:math/0407205v2, §5.1.1) with a
nil-Hecke action, let `ẽ L` be the head of `E L` for `L` simple (`WeakSl2.eTilde`; the head is
simple by Chuang–Rouquier, Proposition 5.20 (b)). The argument of Webster, arXiv:1309.3796v2,
proof of Theorem 5.14, shows that the simple classes form a perfect basis for `[E]`: if
`n = h₊([L])`, then `E^{n-1}(ẽ L)` is a quotient of `E^n L`, whose class is `n!` times the class
of the simple object `E^{(n)} L` (Proposition 5.20 (a)). So `e^{n-1}[ẽ L]` is a nonzero multiple
of `e^n [L]`.

## Main results

* `Sl2.IsPerfectBasis`: Berenstein–Kazhdan, Definition 5.30, for one index.
* `WeakSl2.eTilde_eq_some_iff`: `ẽ L` is the head of `E L`.
* `WeakSl2.isPerfectBasis`: the simple classes form a perfect basis for `e = [E]`, with `ẽ`
  given by heads.
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Sl2

open CategoryTheory Limits Module

universe v u

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

/-- **Berenstein–Kazhdan, arXiv:math/0601391v3, Definition 5.30**, for one index: the basis `B`
is perfect for `e` with the partial map `et` (`none` meaning undefined) if `et` is injective
where defined, `et b` is defined exactly when `e (B b) ≠ 0`, and then
`e (B b) - r • B (et b) ∈ ker e^{ℓ(b) - 1}` for some `r ≠ 0`, where `ℓ(b) = h₊(B b)`.

Berenstein and Kazhdan work over `ℂ` and also ask for a weight basis; for a weak
`𝔰𝔩₂`-categorification the simple classes are weight vectors by definition (`WeakSl2.wt_eq`). -/
structure IsPerfectBasis (B : Module.Basis ι ℚ V) (e : Module.End ℚ V) (et : ι → Option ι) :
    Prop where
  isSome_iff : ∀ b, (et b).isSome ↔ e (B b) ≠ 0
  injective : ∀ b b' c, et b = some c → et b' = some c → b = b'
  exists_smul : ∀ b c, et b = some c →
    ∃ r : ℚ, r ≠ 0 ∧ (e ^ (hPlus e (B b) - 1)) (e (B b) - r • B c) = 0

namespace WeakSl2

variable {C : Type u} [Category.{v} C] [Abelian C] (A : WeakSl2 C ι V)

lemma idx_eq_of_iso {S T : C} (hS : Simple S) (hT : Simple T) (e : S ≅ T) :
    A.idx S hS = A.idx T hT := by
  apply A.B.injective
  rw [← A.cls_simple S hS, ← A.cls_simple T hT]
  exact A.cls_of_iso e

variable [∀ X : C, IsArtinianObject X] [∀ X : C, IsNoetherianObject X]

open Classical in
/-- The Kashiwara operator `ẽ` on simple objects: the index of a simple quotient of `E L`
(the head of `E L`, which is simple by Chuang–Rouquier, Proposition 5.20 (b)), or `none` if
`E L = 0`. -/
noncomputable def eTilde (b : ι) : Option ι :=
  if h : IsZero (A.E.obj (A.simple b)) then none else
    some (A.idx (exists_simple_epi h).choose (exists_simple_epi h).choose_spec.choose)

omit [∀ X : C, IsNoetherianObject X] in
lemma isZero_E_iff (b : ι) : IsZero (A.E.obj (A.simple b)) ↔ A.e (A.B b) = 0 := by
  rw [A.e_basis]
  exact ⟨A.cls_eq_zero_of_isZero, A.isZero_of_cls_eq_zero⟩

lemma eTilde_isSome_iff (b : ι) : (A.eTilde b).isSome ↔ A.e (A.B b) ≠ 0 := by
  rw [← not_iff_not, not_not, ← A.isZero_E_iff]
  unfold eTilde
  split_ifs with h <;> simp [h]

omit [∀ X : C, IsArtinianObject X] in
/-- If `ẽ L = c`, then the simple object of index `c` is a quotient of `E L`. -/
lemma exists_epi_of_eTilde_eq_some {b c : ι} (h : A.eTilde b = some c) :
    ∃ p : A.E.obj (A.simple b) ⟶ A.simple c, Epi p := by
  unfold eTilde at h
  split_ifs at h with h0
  obtain ⟨L, hL, p, hp⟩ := exists_simple_epi h0
  rw [Option.some.injEq] at h
  have hc : A.idx (exists_simple_epi h0).choose (exists_simple_epi h0).choose_spec.choose = c :=
    h
  set L := (exists_simple_epi h0).choose
  have hL : Simple L := (exists_simple_epi h0).choose_spec.choose
  obtain ⟨p, hp⟩ := (exists_simple_epi h0).choose_spec.choose_spec
  rw [← A.idx_simple c] at hc
  obtain ⟨φ⟩ := A.iso_of_idx_eq _ _ _ _ hc
  exact ⟨p ≫ φ.hom, epi_comp _ _⟩

omit [∀ X : C, IsArtinianObject X] in
/-- A simple quotient `S` of `E U`, `U` simple, has `h₊([S]) + 1 = h₊([U])` (Chuang–Rouquier,
Lemma 5.12, in the opposite category). -/
lemma hPlus_add_one_of_epi {U S : C} (hU : Simple U) (hS : Simple S) (p : A.E.obj U ⟶ S)
    [Epi p] : hPlus A.e (A.cls S) + 1 = hPlus A.e (A.cls U) := by
  have : ∀ X : Cᵒᵖ, IsArtinianObject X := fun X ↦ isArtinianObject_op X.unop
  let s : Opposite.op S ⟶ (Epow A.op.E 1).obj (Opposite.op U) := p.op
  have : Mono s := (inferInstance : Mono p.op)
  exact A.op.hPlus_add_of_mono_Epow ((simple_op_iff U).mpr hU) 1 ((simple_op_iff S).mpr hS) s

omit [∀ X : C, IsArtinianObject X] [∀ X : C, IsNoetherianObject X] in
lemma preservesEpimorphisms_Epow : ∀ m, (Epow A.E m).PreservesEpimorphisms
  | 0 => inferInstanceAs (𝟭 C).PreservesEpimorphisms
  | m + 1 => by
    have := preservesEpimorphisms_Epow m
    have : A.E.IsLeftAdjoint := A.adjEF.isLeftAdjoint
    exact inferInstanceAs (Epow A.E m ⋙ A.E).PreservesEpimorphisms

variable [A.E.Additive] [A.F.Additive] (DE : NilHeckeData A.E) (DF : NilHeckeData A.F)
variable (k : Type*) [Field k] [Linear k C] [A.E.Linear k] [A.F.Linear k]

/-- `ẽ L` is the head of `E L`: `ẽ L = c` if and only if the simple object of index `c` is a
quotient of `E L` (Chuang–Rouquier, Proposition 5.20 (b)). -/
theorem eTilde_eq_some_iff
    (hX : ∀ M, IsNilpotent (R := End (A.E.obj M)) (DE.X.app M))
    (hXF : ∀ M, IsNilpotent (R := End (A.F.obj M)) (DF.X.app M))
    (hEnd : ∀ S : C, Simple S → finrank k (S ⟶ S) = 1) (b c : ι) :
    A.eTilde b = some c ↔ ∃ p : A.E.obj (A.simple b) ⟶ A.simple c, Epi p := by
  refine ⟨A.exists_epi_of_eTilde_eq_some, fun ⟨p, hp⟩ ↦ ?_⟩
  have := A.simple_simple c
  have h0 : ¬IsZero (A.E.obj (A.simple b)) := fun h ↦ Simple.not_isZero _ (h.of_epi p)
  unfold eTilde
  simp only [h0, ↓reduceDIte, Option.some.injEq]
  set L := (exists_simple_epi h0).choose
  have hL : Simple L := (exists_simple_epi h0).choose_spec.choose
  obtain ⟨q, hq⟩ := (exists_simple_epi h0).choose_spec.choose_spec
  obtain ⟨φ, -⟩ := A.exists_iso_of_epi_E DE DF k hX hXF hEnd (A.simple_simple b) q p
  rw [A.idx_eq_of_iso _ (A.simple_simple c) φ, A.idx_simple]

/-- `ẽ` is injective where defined: if `E L` and `E L'` have the same simple quotient `S`, then
`L` and `L'` are simple subobjects of `F S`, whose socle is simple (Chuang–Rouquier,
Proposition 5.20 (b)). -/
theorem eTilde_injective
    (hX : ∀ M, IsNilpotent (R := End (A.E.obj M)) (DE.X.app M))
    (hXF : ∀ M, IsNilpotent (R := End (A.F.obj M)) (DF.X.app M))
    (hEnd : ∀ S : C, Simple S → finrank k (S ⟶ S) = 1) (b b' c : ι)
    (h : A.eTilde b = some c) (h' : A.eTilde b' = some c) : b = b' := by
  have := A.simple_simple b
  have := A.simple_simple b'
  have hS := A.simple_simple c
  set S := A.simple c with hSdef
  obtain ⟨p, hp⟩ := A.exists_epi_of_eTilde_eq_some h
  obtain ⟨p', hp'⟩ := A.exists_epi_of_eTilde_eq_some h'
  -- the adjoint maps `L ⟶ F S` are nonzero
  have hne : ∀ {L : C} (q : A.E.obj L ⟶ S) [Epi q], A.adjEF.homEquiv L S q ≠ 0 := by
    intro L q _ hq0
    have hq : q ≠ 0 := fun h0 ↦ Simple.not_isZero S
      ((IsZero.iff_id_eq_zero _).2 ((cancel_epi q).1 (by rw [h0]; simp)))
    apply hq
    apply (A.adjEF.homEquiv L S).injective
    rw [hq0, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  set g := A.adjEF.homEquiv _ S p
  set g' := A.adjEF.homEquiv _ S p'
  have : Mono g := mono_of_nonzero_from_simple (hne p)
  have : Mono g' := mono_of_nonzero_from_simple (hne p')
  -- `1 ≤ h₊` of `[S]` for `f`
  have hclsS : A.cls S = A.B c := by rw [A.cls_simple S hS, A.idx_simple]
  have hi : 1 ≤ hPlus A.swap.e (A.swap.cls S) := by
    change 1 ≤ hPlus A.f (A.cls S)
    rw [hclsS]
    by_contra h0
    have h1 := (A.posBasis.strings c).2.2.2.2
    rw [show hPlus A.f (A.B c) = 0 by omega, zero_add, pow_one] at h1
    have hFS : IsZero (A.F.obj S) := A.isZero_of_cls_eq_zero (by rw [A.cls_F, hclsS, h1])
    exact hne p (hFS.eq_of_tgt _ _)
  let ι₁ := DF.divι k 1 S
  have : IsIso ι₁ := NilHeckeData.isIso_divι_one DF k _
  let φ : A.simple b ⟶ DF.divObj k 1 S := (g : A.simple b ⟶ (Epow A.F 1).obj S) ≫ inv ι₁
  let φ' : A.simple b' ⟶ DF.divObj k 1 S := (g' : A.simple b' ⟶ (Epow A.F 1).obj S) ≫ inv ι₁
  have : Mono φ := mono_comp _ _
  have : Mono φ' := mono_comp _ _
  have hmk := A.swap.subobject_mk_eq_of_simple DF DE k hXF hX hEnd hS hi φ φ'
  rw [← A.idx_simple b, ← A.idx_simple b']
  exact A.idx_eq_of_iso _ _ (Subobject.isoOfMkEqMk φ φ' hmk)

include DE in
/-- If `ẽ L = S`, then `e [L]` and a multiple of `[S]` agree up to the kernel of `e^{h₊ - 1}`:
`E^{h₊([L]) - 1}` applied to the epimorphism `E L ⟶ S` exhibits `e^{h₊ - 1} [S]` as a part of
`[E^{h₊} L] = h₊! [E^{(h₊)} L]`, which is a multiple of a single basis vector (Webster,
arXiv:1309.3796v2, proof of Theorem 5.14; Chuang–Rouquier, Proposition 5.20). -/
theorem eTilde_exists_smul
    (hXF : ∀ M, IsNilpotent (R := End (A.F.obj M)) (DF.X.app M))
    (hEnd : ∀ S : C, Simple S → finrank k (S ⟶ S) = 1) (b c : ι)
    (h : A.eTilde b = some c) :
    ∃ r : ℚ, r ≠ 0 ∧ (A.e ^ (hPlus A.e (A.B b) - 1)) (A.e (A.B b) - r • A.B c) = 0 := by
  have hb := A.simple_simple b
  have hc := A.simple_simple c
  obtain ⟨p, hp⟩ := A.exists_epi_of_eTilde_eq_some h
  let L := A.simple b
  have hclsL : A.cls L = A.B b := by rw [A.cls_simple L hb, A.idx_simple]
  have hclsc : A.cls (A.simple c) = A.B c := by rw [A.cls_simple _ hc, A.idx_simple]
  have hn := A.hPlus_add_one_of_epi hb hc p
  rw [hclsL, hclsc] at hn
  set m := hPlus A.e (A.B c)
  set N := hPlus A.e (A.B b)
  have hD := A.simple_divObj_top DE DF k hXF hEnd hb
  rw [hclsL] at hD
  set d := A.idx _ hD
  -- `e^N [L] = N! • B d`
  have hEN : (A.e ^ N) (A.B b) = (N.factorial : ℚ) • A.B d := by
    rw [← hclsL, ← A.toK0Data.cls_Epow_obj A.cls_E, DE.cls_Epow k A.toK0Data N L,
      A.cls_simple _ hD, Nat.cast_smul_eq_nsmul]
  -- the image of `p` under `E^m`
  have := A.preservesEpimorphisms_Epow m
  let q := (Epow A.E m).map p
  have hq := A.cls_add_of_epi q
  have hsrc : A.cls ((Epow A.E m).obj (A.E.obj L)) = (A.e ^ N) (A.B b) := by
    rw [A.toK0Data.cls_Epow_obj A.cls_E, A.cls_E, hclsL, ← hn, pow_succ,
      Module.End.mul_apply]
  have htgt : A.cls ((Epow A.E m).obj (A.simple c)) = (A.e ^ m) (A.B c) := by
    rw [A.toK0Data.cls_Epow_obj A.cls_E, hclsc]
  rw [hsrc, htgt, hEN] at hq
  set w := (A.e ^ m) (A.B c)
  have hw : w = (A.B.repr w d) • A.B d := by
    refine A.B.ext_elem fun j ↦ ?_
    rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, smul_eq_mul]
    by_cases hj : j = d
    · subst hj; simp
    · rw [Finsupp.single_eq_of_ne hj, mul_zero]
      have h1 := congrArg (fun v ↦ A.B.repr v j) hq
      simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_eq_of_ne hj, smul_zero] at h1
      have h2 := A.cls_mem_cone (kernel q) j
      have h3 : 0 ≤ A.B.repr w j := by rw [← htgt]; exact A.cls_mem_cone _ j
      linarith
  set t := A.B.repr w d
  have hwne : w ≠ 0 := (A.posBasis.strings c).2.1
  have ht : t ≠ 0 := fun h0 ↦ hwne (by rw [hw, h0, zero_smul])
  refine ⟨(N.factorial : ℚ) / t, div_ne_zero (by positivity) ht, ?_⟩
  rw [map_sub, map_smul, ← Module.End.mul_apply, ← pow_succ, show N - 1 + 1 = N by omega,
    show N - 1 = m by omega, hEN]
  change _ - _ • w = 0
  rw [hw, smul_smul, div_mul_cancel₀ _ ht, sub_self]

/-- **Webster, arXiv:1309.3796v2, Theorem 5.14** (in the generality of Chuang–Rouquier's weak
`sl₂`-categorifications with nilpotent dots): the classes of simple objects form a perfect basis
in the sense of Berenstein–Kazhdan (arXiv:math/0601391v3, Definition 5.30), with crystal
operator `ẽ`. -/
theorem isPerfectBasis
    (hX : ∀ M, IsNilpotent (R := End (A.E.obj M)) (DE.X.app M))
    (hXF : ∀ M, IsNilpotent (R := End (A.F.obj M)) (DF.X.app M))
    (hEnd : ∀ S : C, Simple S → finrank k (S ⟶ S) = 1) :
    IsPerfectBasis A.B A.e A.eTilde where
  isSome_iff := A.eTilde_isSome_iff
  injective := A.eTilde_injective DE DF k hX hXF hEnd
  exists_smul := A.eTilde_exists_smul DE DF k hXF hEnd

end WeakSl2

end Categorification.Sl2
