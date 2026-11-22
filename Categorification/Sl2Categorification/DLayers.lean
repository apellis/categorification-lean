/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.WeakCategorificationOp

/-!
# The subcategories `A^{≤ r}` and `C_r`

For a weak `𝔰𝔩₂`-categorification `A` (Chuang–Rouquier, arXiv:math/0407205v2, §5.1.3),
`A^{≤ r}` is the Serre subcategory of objects all of whose composition factors `S` have
`d(S) ≤ r` (`WeakSl2.IsLe`), and `C_r` is the full subcategory of `A^{≤ r}` of objects whose
simple subobjects and simple quotients all have `d = r` (`WeakSl2.IsCr`).

## Main results

* `WeakSl2.IsLe.E`, `WeakSl2.IsLe.F`: `A^{≤ r}` is stable under `E` and `F`
  (Chuang–Rouquier, Proposition 5.10, from Lemma 4.3 (1)).
* `WeakSl2.IsCr.E`, `WeakSl2.IsCr.F`: **Chuang–Rouquier, Lemma 5.12**: `C_r` is stable under
  `E` and `F`.
-/

namespace Categorification.Sl2

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

namespace WeakSl2

variable (A : WeakSl2 C ι V)

/-- `M` lies in `A^{≤ r}`: every composition factor `S` of `M` has `d(S) ≤ r`. -/
def IsLe (r : ℕ) (M : C) : Prop :=
  ∀ c, A.B.repr (A.cls M) c ≠ 0 → dOf A.e A.f (A.B c) ≤ r

/-- If every basis vector in the support of `v` has `d ≤ r`, so does every one in the support
of `T v`, for `T` a positive operator not increasing `d` on basis vectors. -/
lemma le_of_apply {T : Module.End ℚ V} (hT : ∀ i c, A.B.repr (T (A.B i)) c ≠ 0 →
    dOf A.e A.f (A.B c) ≤ dOf A.e A.f (A.B i)) {r : ℕ} {v : V}
    (hv : ∀ c, A.B.repr v c ≠ 0 → dOf A.e A.f (A.B c) ≤ r) :
    ∀ c, A.B.repr (T v) c ≠ 0 → dOf A.e A.f (A.B c) ≤ r := by
  intro c hc
  rw [repr_apply_eq_sum] at hc
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hi
  exact (hT i c h2).trans (hv i h1)

variable {A}

/-- `A^{≤ r}` is stable under `E` (Chuang–Rouquier, Proposition 5.10). -/
theorem IsLe.E {r : ℕ} {M : C} (h : A.IsLe r M) : A.IsLe r (A.E.obj M) := by
  intro c hc
  rw [A.cls_E] at hc
  exact A.le_of_apply (fun _ _ ↦ A.posBasis.dOf_le_of_e) h c hc

/-- `A^{≤ r}` is stable under `F` (Chuang–Rouquier, Proposition 5.10). -/
theorem IsLe.F {r : ℕ} {M : C} (h : A.IsLe r M) : A.IsLe r (A.F.obj M) := by
  intro c hc
  rw [A.cls_F] at hc
  exact A.le_of_apply (fun _ _ ↦ A.posBasis.dOf_le_of_f) h c hc

theorem IsLe.dS_le_of_mono {r : ℕ} {M T : C} (h : A.IsLe r M) (hT : Simple T) (t : T ⟶ M)
    [Mono t] : A.dS T hT ≤ r :=
  h _ (A.repr_cls_pos_of_mono_of_epi (𝟙 M) t).ne'

theorem IsLe.dS_le_of_epi {r : ℕ} {M T : C} (h : A.IsLe r M) (hT : Simple T) (q : M ⟶ T)
    [Epi q] : A.dS T hT ≤ r :=
  h _ (A.repr_cls_pos_of_mono_of_epi q (𝟙 T)).ne'

variable (A) in
/-- `M` lies in `C_r`: `M ∈ A^{≤ r}` and every simple subobject or simple quotient `S` of `M`
has `d(S) = r`. -/
structure IsCr (r : ℕ) (M : C) : Prop where
  le : A.IsLe r M
  sub : ∀ (S : C) (hS : Simple S) (s : S ⟶ M), Mono s → A.dS S hS = r
  quot : ∀ (S : C) (hS : Simple S) (q : M ⟶ S), Epi q → A.dS S hS = r

variable [∀ X : C, IsArtinianObject X] [∀ X : C, IsNoetherianObject X]

/-- **Chuang–Rouquier, Lemma 5.12**: `C_r` is stable under `E`. -/
theorem IsCr.E {r : ℕ} {M : C} (h : A.IsCr r M) : A.IsCr r (A.E.obj M) where
  le := h.le.E
  sub _ hS s _ := le_antisymm (h.le.E.dS_le_of_mono hS s)
    (A.dOf_le_of_mono_E (fun S' hS' s' hs' ↦ (h.sub S' hS' s' hs').ge) hS s)
  quot _ hS q _ := le_antisymm (h.le.E.dS_le_of_epi hS q)
    (A.dOf_le_of_epi_E (fun S' hS' q' hq' ↦ (h.quot S' hS' q' hq').ge) hS q)

/-- **Chuang–Rouquier, Lemma 5.12**: `C_r` is stable under `F`. -/
theorem IsCr.F {r : ℕ} {M : C} (h : A.IsCr r M) : A.IsCr r (A.F.obj M) where
  le := h.le.F
  sub _ hS s _ := le_antisymm (h.le.F.dS_le_of_mono hS s)
    (A.dOf_le_of_mono_F (fun S' hS' s' hs' ↦ (h.sub S' hS' s' hs').ge) hS s)
  quot _ hS q _ := le_antisymm (h.le.F.dS_le_of_epi hS q)
    (A.dOf_le_of_epi_F (fun S' hS' q' hq' ↦ (h.quot S' hS' q' hq').ge) hS q)

end WeakSl2

end Categorification.Sl2
