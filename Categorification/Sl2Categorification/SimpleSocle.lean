/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.TopDividedPowerSimple

/-!
# The socle of a divided power of a simple object

Chuang–Rouquier, arXiv:math/0407205v2, Proposition 5.20 (b), socle part, for an arbitrary
simple object: let `U` be simple, `n = h₊([U])` and `i ≤ n`. Then every simple `S` has
`dim Hom(S, E^{(i)} U) ≤ 1` (`WeakSl2.finrank_hom_divObj_le_one_of_simple`), and any two simple
subobjects of `E^{(i)} U` coincide (`WeakSl2.subobject_mk_eq_of_simple`), so the socle of
`E^{(i)} U` is simple.

The proof is that of Chuang–Rouquier. A simple subobject `S` of `E^i U` has
`d(S) = d(U)` (Chuang–Rouquier, Lemma 5.12: `d(S) ≥ d(U)` by Lemma 5.11 and `d(S) ≤ d(U)` by
Lemma 4.3 (1)) and weight `wt U + 2i`, so `h₊([S]) = n - i` and `E^{n-i} S ≠ 0`. A simple
subobject of `E^{n-i} S ⊆ E^n U` is then isomorphic to the simple object `T = E^{(n)} U`
(Proposition 5.20 (a), `WeakSl2.simple_divObj_top`), giving a nonzero map `T ⟶ E^{n-i} S`. The
socle bound follows from `NilHeckeData.finiteDimensional_hom_divObj_of_ne_zero`. For two
simple subobjects `S₁`, `S₂`, the maps `T ⟶ E^{n-i} S_j ⟶ E^n U` killed by the dots lie on one
line (`NilHeckeData.exists_forall_lift_mem_span`); since `E^{n-i}` preserves pullbacks, this
forces `S₁ ∩ S₂ ≠ 0`. This replaces the use of Chuang–Rouquier, Lemma 3.6.

## Main results

* `PosBasis.dOf_le_of_e_pow`: Chuang–Rouquier, Lemma 4.3 (1), for powers of `e`.
* `WeakSl2.hPlus_add_of_mono_Epow`: a simple subobject `S ⊆ E^j U` has
  `h₊([S]) + j = h₊([U])` (Chuang–Rouquier, Lemma 5.12).
* `WeakSl2.finrank_hom_divObj_le_one_of_simple`: **Chuang–Rouquier, Proposition 5.20 (b)**,
  socle bound, for every simple `U`.
* `WeakSl2.subobject_mk_eq_of_simple`: **Chuang–Rouquier, Proposition 5.20 (b)**, the socle of
  `E^{(i)} U` is simple.
-/

namespace Categorification.Sl2

open CategoryTheory Limits Module

universe v u

namespace PosBasis

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]
variable {B : Module.Basis ι ℚ V} {e f : Module.End ℚ V} {wt : ι → ℤ} (P : PosBasis B e f wt)
include P

/-- **Chuang–Rouquier, Lemma 4.3 (1)**, for powers of `e`: if `c` occurs in `e^j b`, then
`d(c) ≤ d(b)`. -/
theorem dOf_le_of_e_pow {i c : ι} :
    ∀ {j : ℕ}, B.repr ((e ^ j) (B i)) c ≠ 0 → dOf e f (B c) ≤ dOf e f (B i)
  | 0, hc => by
    classical
    rw [pow_zero, Module.End.one_apply, Module.Basis.repr_self, Finsupp.single_apply] at hc
    by_cases h : i = c
    · rw [h]
    · exact absurd (by simp [h]) hc
  | j + 1, hc => by
    classical
    rw [pow_succ', Module.End.mul_apply] at hc
    set v := (e ^ j) (B i)
    have hv : e v = (B.repr v).sum fun c' a => a • e (B c') := by
      conv_lhs => rw [← B.linearCombination_repr v, Finsupp.linearCombination_apply]
      rw [map_finsuppSum]
      simp only [map_smul]
    rw [hv, map_finsuppSum, Finsupp.sum_apply] at hc
    obtain ⟨c', hc', hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hne
    have h1 : B.repr v c' ≠ 0 := left_ne_zero_of_mul hne
    have h2 : B.repr (e (B c')) c ≠ 0 := right_ne_zero_of_mul hne
    exact (P.dOf_le_of_e h2).trans (dOf_le_of_e_pow h1)

end PosBasis

variable {C : Type u} [Category.{v} C]

namespace WeakSl2

variable [Abelian C] {ι V : Type*} [AddCommGroup V] [Module ℚ V] (A : WeakSl2 C ι V)
variable [∀ X : C, IsArtinianObject X]

/-- **Chuang–Rouquier, Lemma 5.11**, iterated: every simple subobject of `E^j U`, for `U`
simple, has `d ≥ d(U)`. -/
theorem dS_le_of_mono_Epow {U : C} (hU : Simple U) :
    ∀ (j : ℕ) (S : C) (hS : Simple S) (s : S ⟶ (Epow A.E j).obj U), Mono s →
      A.dS U hU ≤ A.dS S hS
  | 0, S, hS, s, hs => by
    have hs0 : s ≠ 0 := fun h ↦ id_nonzero S ((cancel_mono s).1 (by rw [h, comp_zero, comp_zero]))
    have : Simple ((Epow A.E 0).obj U) := hU
    have : Mono s := hs
    have hiso : IsIso s := isIso_of_mono_of_nonzero hs0
    have hcls : A.B (A.idx S hS) = A.B (A.idx U hU) := by
      rw [← A.cls_simple S hS, ← A.cls_simple U hU]; exact A.cls_of_iso (@asIso _ _ _ _ s hiso)
    unfold dS
    rw [hcls]
  | j + 1, S, hS, s, hs => by
    let t : S ⟶ A.E.obj ((Epow A.E j).obj U) := s
    have : Mono t := hs
    exact A.dOf_le_of_mono_E (fun S' hS' s' hs' ↦ dS_le_of_mono_Epow hU j S' hS' s' hs') hS t

/-- **Chuang–Rouquier, Lemma 5.12**: a simple subobject `S` of `E^j U`, for `U` simple, has
`d(S) = d(U)`, weight `wt U + 2j`, and so `h₊([S]) + j = h₊([U])`. -/
theorem hPlus_add_of_mono_Epow {U : C} (hU : Simple U) (j : ℕ) {S : C} (hS : Simple S)
    (s : S ⟶ (Epow A.E j).obj U) [Mono s] :
    hPlus A.e (A.cls S) + j = hPlus A.e (A.cls U) := by
  have hclsU : A.cls U = A.B (A.idx U hU) := A.cls_simple U hU
  have hclsS : A.cls S = A.B (A.idx S hS) := A.cls_simple S hS
  have hpos := A.repr_cls_pos_of_mono_of_epi (𝟙 _) s
  rw [A.toK0Data.cls_Epow_obj A.cls_E, hclsU] at hpos
  have hd1 : A.dS U hU ≤ A.dS S hS := A.dS_le_of_mono_Epow hU j S hS s inferInstance
  have hd2 : dOf A.e A.f (A.B (A.idx S hS)) ≤ dOf A.e A.f (A.B (A.idx U hU)) :=
    A.posBasis.dOf_le_of_e_pow hpos.ne'
  have hwt : A.wt (A.idx S hS) = A.wt (A.idx U hU) + 2 * j :=
    A.posBasis.wt_eq_of_repr_ne_zero (A.posBasis.hOp_pow_e_basis _ j) hpos.ne'
  have h1 := (A.posBasis.strings (A.idx S hS)).1
  have h2 := (A.posBasis.strings (A.idx U hU)).1
  unfold dS dOf at hd1
  unfold dOf at hd2
  rw [hclsS, hclsU]
  omega

variable [∀ X : C, IsNoetherianObject X]
variable [A.E.Additive] [A.F.Additive] (DE : NilHeckeData A.E) (DF : NilHeckeData A.F)
variable (k : Type*) [Field k] [Linear k C] [A.E.Linear k] [A.F.Linear k]

/-- For `U` simple, `h₊([U]) = i + m` and a simple subobject `S` of `E^{(i)} U`, there is a
nonzero map `E^{(i+m)} U ⟶ E^m S`. -/
theorem exists_divObj_hom_Epow_ne_zero
    (hXF : ∀ M, IsNilpotent (R := End (A.F.obj M)) (DF.X.app M))
    (hEnd : ∀ S : C, Simple S → finrank k (S ⟶ S) = 1)
    {U : C} (hU : Simple U) {i m : ℕ} (hN : hPlus A.e (A.cls U) = i + m)
    {S : C} [hS : Simple S] (φ : S ⟶ DE.divObj k i U) [Mono φ] :
    Simple (DE.divObj k (i + m) U) ∧
      ∃ z₀ : DE.divObj k (i + m) U ⟶ (Epow A.E m).obj S, z₀ ≠ 0 := by
  have : A.E.IsRightAdjoint := A.adjFE.isRightAdjoint
  have hT : Simple (DE.divObj k (i + m) U) := by
    have := A.simple_divObj_top DE DF k hXF hEnd hU
    rwa [hN] at this
  refine ⟨hT, ?_⟩
  -- `h₊([S]) = m`, so `E^m S ≠ 0`
  have hh := A.hPlus_add_of_mono_Epow hU i hS (φ ≫ DE.divι k i U)
  obtain ⟨-, hne, -⟩ := A.posBasis.strings (A.idx S hS)
  have hES : ¬IsZero ((Epow A.E m).obj S) := by
    intro h
    apply hne
    have hm : hPlus A.e (A.B (A.idx S hS)) = m := by
      rw [← A.cls_simple S hS]; omega
    rw [hm, ← A.cls_simple S hS, ← A.toK0Data.cls_Epow_obj A.cls_E]
    exact A.toK0Data.cls_eq_zero_of_isZero h
  -- a simple `S' ⊆ E^m S`, which is isomorphic to `E^{(i+m)} U`
  set s' := simpleSubobjectArrow hES
  set w := s' ≫ liftMap (φ ≫ DE.divι k i U) m
  have : Mono (liftMap (E := A.E) (φ ≫ DE.divι k i U) m) := mono_liftMap _ m
  have hw : w ≠ 0 := fun h ↦ id_nonzero _ ((cancel_mono w).1 (by rw [h, comp_zero, comp_zero]))
  obtain ⟨y, hy⟩ := DE.exists_comp_divπ_ne_zero (k := k) hw
  have : Mono (w ≫ y ≫ DE.divπ k (i + m) U) := mono_of_nonzero_from_simple hy
  have : IsIso (w ≫ y ≫ DE.divπ k (i + m) U) := isIso_of_mono_of_nonzero hy
  have hs' : s' ≠ 0 := fun h ↦ id_nonzero _ ((cancel_mono s').1 (by rw [h, comp_zero, comp_zero]))
  refine ⟨inv (w ≫ y ≫ DE.divπ k (i + m) U) ≫ s', fun h ↦ hs' ?_⟩
  rw [← IsIso.hom_inv_id_assoc (w ≫ y ≫ DE.divπ k (i + m) U) s', h, comp_zero]

/-- **Chuang–Rouquier, Proposition 5.20 (b)**, socle bound, for `E` and every simple `U`: if
`i ≤ h₊([U])`, then `dim Hom(S, E^{(i)} U) ≤ 1` for every simple `S`, and this space is
finite-dimensional.

The hypotheses `hX`, `hXF` are the nilpotence of the dots on `E` and `F` (Chuang–Rouquier,
§5.2.1, eigenvalue `0`), and `hEnd` is the condition `End(S) = k` for simple `S`. -/
theorem finiteDimensional_hom_divObj_of_simple
    (hX : ∀ M, IsNilpotent (R := End (A.E.obj M)) (DE.X.app M))
    (hXF : ∀ M, IsNilpotent (R := End (A.F.obj M)) (DF.X.app M))
    (hEnd : ∀ S : C, Simple S → finrank k (S ⟶ S) = 1)
    {U : C} (hU : Simple U) {i : ℕ} (hi : i ≤ hPlus A.e (A.cls U)) (S : C) [Simple S] :
    FiniteDimensional k (S ⟶ DE.divObj k i U) ∧ finrank k (S ⟶ DE.divObj k i U) ≤ 1 := by
  classical
  have : A.E.IsRightAdjoint := A.adjFE.isRightAdjoint
  obtain ⟨m, hN⟩ := Nat.exists_eq_add_of_le hi
  by_cases h0 : ∀ φ : S ⟶ DE.divObj k i U, φ = 0
  · have : Subsingleton (S ⟶ DE.divObj k i U) := ⟨fun a b => (h0 a).trans (h0 b).symm⟩
    rw [finrank_zero_of_subsingleton]
    exact ⟨inferInstance, zero_le_one⟩
  push Not at h0
  obtain ⟨φ, hφ⟩ := h0
  have : Mono φ := mono_of_nonzero_from_simple hφ
  obtain ⟨hT, z₀, hz₀⟩ := A.exists_divObj_hom_Epow_ne_zero DE DF k hXF hEnd hU hN φ
  exact DE.finiteDimensional_hom_divObj_of_ne_zero hX (hEnd _ hT) hz₀

/-- **Chuang–Rouquier, Proposition 5.20 (b)**, socle bound, for `E` and every simple `U`. -/
theorem finrank_hom_divObj_le_one_of_simple
    (hX : ∀ M, IsNilpotent (R := End (A.E.obj M)) (DE.X.app M))
    (hXF : ∀ M, IsNilpotent (R := End (A.F.obj M)) (DF.X.app M))
    (hEnd : ∀ S : C, Simple S → finrank k (S ⟶ S) = 1)
    {U : C} (hU : Simple U) {i : ℕ} (hi : i ≤ hPlus A.e (A.cls U)) (S : C) [Simple S] :
    finrank k (S ⟶ DE.divObj k i U) ≤ 1 :=
  (A.finiteDimensional_hom_divObj_of_simple DE DF k hX hXF hEnd hU hi S).2

omit [∀ X : C, IsArtinianObject X] [∀ X : C, IsNoetherianObject X] [A.E.Additive]
  [A.F.Additive] [A.E.Linear k] [A.F.Linear k] in
/-- The powers of `E` preserve pullbacks, `E` being a right adjoint. -/
theorem preservesPullbacks_Epow :
    ∀ m, PreservesLimitsOfShape WalkingCospan (Epow A.E m)
  | 0 => inferInstanceAs (PreservesLimitsOfShape WalkingCospan (𝟭 C))
  | m + 1 => by
    have := preservesPullbacks_Epow m
    have : A.E.IsRightAdjoint := A.adjFE.isRightAdjoint
    exact inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Epow A.E m ⋙ A.E))

omit [∀ X : C, IsArtinianObject X] [∀ X : C, IsNoetherianObject X] [A.F.Additive] [A.E.Linear k]
  [A.F.Linear k] in
/-- The powers of `E` are additive. -/
theorem additive_Epow : ∀ m, (Epow A.E m).Additive
  | 0 => inferInstanceAs (𝟭 C).Additive
  | m + 1 => by
    have := additive_Epow m
    exact inferInstanceAs (Epow A.E m ⋙ A.E).Additive

/-- **Chuang–Rouquier, Proposition 5.20 (b)**, socle part, for `E` and every simple `U`: if
`i ≤ h₊([U])`, any two simple subobjects of `E^{(i)} U` are equal, so the socle of `E^{(i)} U`
is simple. -/
theorem subobject_mk_eq_of_simple
    (hX : ∀ M, IsNilpotent (R := End (A.E.obj M)) (DE.X.app M))
    (hXF : ∀ M, IsNilpotent (R := End (A.F.obj M)) (DF.X.app M))
    (hEnd : ∀ S : C, Simple S → finrank k (S ⟶ S) = 1)
    {U : C} (hU : Simple U) {i : ℕ} (hi : i ≤ hPlus A.e (A.cls U))
    {S₁ S₂ : C} [Simple S₁] [Simple S₂] (φ₁ : S₁ ⟶ DE.divObj k i U)
    (φ₂ : S₂ ⟶ DE.divObj k i U) [Mono φ₁] [Mono φ₂] :
    Subobject.mk φ₁ = Subobject.mk φ₂ := by
  have : A.E.IsRightAdjoint := A.adjFE.isRightAdjoint
  obtain ⟨m, hN⟩ := Nat.exists_eq_add_of_le hi
  have := A.preservesPullbacks_Epow m
  have := A.additive_Epow m
  obtain ⟨hT, z₁₀, hz₁₀⟩ := A.exists_divObj_hom_Epow_ne_zero DE DF k hXF hEnd hU hN φ₁
  obtain ⟨-, z₂₀, hz₂₀⟩ := A.exists_divObj_hom_Epow_ne_zero DE DF k hXF hEnd hU hN φ₂
  obtain ⟨z₁, hz₁, hz₁x⟩ := DE.exists_ne_zero_comp_xE_eq_zero hX hz₁₀
  obtain ⟨z₂, hz₂, hz₂x⟩ := DE.exists_ne_zero_comp_xE_eq_zero hX hz₂₀
  obtain ⟨u₀, hu₀⟩ := DE.exists_forall_lift_mem_span hX (hEnd _ hT)
  have : Mono (liftMap (E := A.E) (DE.divι k i U) m) := mono_liftMap _ m
  obtain ⟨a₁, ha₁⟩ := Submodule.mem_span_singleton.1 (hu₀ z₁ hz₁x φ₁)
  obtain ⟨a₂, ha₂⟩ := Submodule.mem_span_singleton.1 (hu₀ z₂ hz₂x φ₂)
  have hM : ∀ {S : C} (z : DE.divObj k (i + m) U ⟶ (Epow A.E m).obj S) (φ : S ⟶ DE.divObj k i U)
      [Mono φ], z ≠ 0 → z ≫ liftMap (φ ≫ DE.divι k i U) m ≠ 0 := by
    intro S z φ _ hz h
    have : Mono (liftMap (E := A.E) (φ ≫ DE.divι k i U) m) := mono_liftMap _ m
    exact hz ((cancel_mono _).1 (by rw [h, zero_comp]))
  have ha₁0 : a₁ ≠ 0 := by
    rintro rfl; exact hM z₁ φ₁ hz₁ (by rw [← ha₁, zero_smul])
  have ha₂0 : a₂ ≠ 0 := by
    rintro rfl; exact hM z₂ φ₂ hz₂ (by rw [← ha₂, zero_smul])
  rw [liftMap_comp] at ha₁ ha₂
  have hw : (a₂ • z₁) ≫ (Epow A.E m).map φ₁ = (a₁ • z₂) ≫ (Epow A.E m).map φ₂ := by
    refine (cancel_mono (liftMap (E := A.E) (DE.divι k i U) m)).1 ?_
    rw [Category.assoc, Category.assoc, Linear.smul_comp, Linear.smul_comp, ← ha₁, ← ha₂,
      smul_smul, smul_smul, mul_comm]
  by_contra hmk
  have hP : IsZero (pullback φ₁ φ₂) := by
    by_contra hP
    have hf : pullback.fst φ₁ φ₂ ≠ 0 := fun h ↦ hP (by
      rw [IsZero.iff_id_eq_zero]
      exact (cancel_mono (pullback.fst φ₁ φ₂)).1 (by rw [h, comp_zero, comp_zero]))
    have : IsIso (pullback.fst φ₁ φ₂) := isIso_of_mono_of_nonzero hf
    set g := inv (pullback.fst φ₁ φ₂) ≫ pullback.snd φ₁ φ₂
    have hg : g ≫ φ₂ = φ₁ := by
      rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
    have : Mono g := mono_of_mono_fac hg
    have hg0 : g ≠ 0 := fun h ↦ id_nonzero S₁ ((cancel_mono φ₁).1 (by
      rw [← hg, h, zero_comp, comp_zero, zero_comp]))
    have : IsIso g := isIso_of_mono_of_nonzero hg0
    exact hmk (Subobject.mk_eq_mk_of_comm φ₁ φ₂ (asIso g) hg)
  have h0 : (Epow A.E m).map (pullback.fst φ₁ φ₂) = 0 := by
    rw [hP.eq_of_src (pullback.fst φ₁ φ₂) 0, (Epow A.E m).map_zero]
  have hs : a₂ • z₁ = 0 := by
    rw [← pullback.lift_fst _ _ hw, ← PreservesPullback.iso_inv_fst (Epow A.E m) φ₁ φ₂, h0,
      comp_zero, comp_zero]
  exact hz₁ ((smul_eq_zero.1 hs).resolve_left ha₂0)

end WeakSl2

end Categorification.Sl2
