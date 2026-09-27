/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.LemXind

/-!
# CL Corollary 3.13: the map `ζ` is an isomorphism

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Corollary 3.13 (`cor:1`), `n ≥ 0`: the map
`ζ = (up-down crossing) ⊕ ⊕_{k=0}^{n-1} (k dots ∘ cup) : F E 1_n ⊕ ⊕_k 1_n⟨n-1-2k⟩ → E F 1_n`
is an isomorphism. CL's proof: the up-down crossing `F E 1_n → E F 1_n` is the inclusion of the
summand (unique up to scalar by Lemma 3.12) and has zero components in the summands
`1_n⟨n-1-2k⟩`; the matrix of `⊕_k (k dots ∘ cup)` in the summands `1_n⟨n-1-2k⟩` is triangular by
degrees, with diagonal entries isomorphisms by Lemma 3.6.

Here, for a decomposition datum `e` (`DotEntries.lean`), the up-down crossing is `ιFE e` and the
`k`-th map is `cupK e k = (cup ≫ dot^k)⟨-2k⟩ : 1_n⟨n-1-2k⟩ → E F 1_n`
(`cupDots e k` shifted back); its components are computed by `bubble_aux`: zero in `F E 1_n`
(`cupK_comp_πFE`) and in `1_n⟨n-1-2j⟩` for `j > k` (`cupK_comp_π_eq_zero`), an isomorphism for
`j = k` (`isIso_cupK_comp_π_self`, from `DotNondeg e`). The general fact "a triangular matrix with
invertible diagonal is invertible" is `isIso_bsum_of_triangular` (with `isIso_biprod_of_blocks`).

* `zeta e`, `isIso_zeta_of_dotNondeg` (Corollary 3.13 from Lemma 3.6),
  `isIso_zeta_of_adjHyp` (Corollary 3.13 under (3.2) at the weights `≥ n`, via `lemXind_of_adjHyp`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits

/-! ## Maps out of `bsum`, and triangular matrices -/

section BSumDesc

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

/-- The map out of `bsum f n` with components `φ j : f j ⟶ Y`. -/
def bsumDesc (f : ℕ → C) {Y : C} (φ : ∀ j : ℕ, f j ⟶ Y) : ∀ n : ℕ, bsum f n ⟶ Y
  | 0 => 0
  | n + 1 => biprod.desc (φ n) (bsumDesc f φ n)

theorem bsumι_desc (f : ℕ → C) {Y : C} (φ : ∀ j : ℕ, f j ⟶ Y) :
    ∀ (n j : ℕ), j < n → bsumι f n j ≫ bsumDesc f φ n = φ j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, h => by
    by_cases hj : j = n
    · subst hj
      simp [bsumι, bsumDesc]
    · simp only [bsumι, bsumDesc, dif_neg hj, Category.assoc, biprod.inr_desc]
      exact bsumι_desc f φ n j (by omega)

/-- Maps out of `bsum f n` are determined by their restrictions to the summands. -/
theorem bsum_hom_ext (f : ℕ → C) {Y : C} {n : ℕ} {x y : bsum f n ⟶ Y}
    (h : ∀ j, j < n → bsumι f n j ≫ x = bsumι f n j ≫ y) : x = y := by
  rw [← Category.id_comp x, ← Category.id_comp y, ← bsum_total, Preadditive.sum_comp,
    Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Category.assoc, Category.assoc, h j (Finset.mem_range.1 hj)]

omit [HasZeroObject C] in
/-- A block triangular map `X ⊞ Y ⟶ Z ⊞ W` with invertible diagonal blocks is invertible. -/
theorem isIso_biprod_of_blocks {X Y Z W : C} (φ : X ⊞ Y ⟶ Z ⊞ W)
    [IsIso (biprod.inl ≫ φ ≫ biprod.fst)] [IsIso (biprod.inr ≫ φ ≫ biprod.snd)]
    (h : biprod.inr ≫ φ ≫ biprod.fst = 0) : IsIso φ := by
  set a := biprod.inl ≫ φ ≫ biprod.fst
  set b := biprod.inl ≫ φ ≫ biprod.snd
  set d := biprod.inr ≫ φ ≫ biprod.snd
  have hφ₁ : biprod.inl ≫ φ = a ≫ biprod.inl + b ≫ biprod.inr := by
    apply biprod.hom_ext <;> simp [a, b]
  have hφ₂ : biprod.inr ≫ φ = d ≫ biprod.inr := by
    apply biprod.hom_ext
    · simp [h]
    · simp [d]
  refine ⟨⟨biprod.desc (inv a ≫ biprod.inl - inv a ≫ b ≫ inv d ≫ biprod.inr) (inv d ≫ biprod.inr),
    ?_, ?_⟩⟩
  · apply biprod.hom_ext'
    · rw [← Category.assoc, hφ₁]
      simp [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.comp_sub]
    · rw [← Category.assoc, hφ₂]
      simp
  · apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc, Preadditive.sub_comp, Category.assoc, hφ₁, hφ₂,
        Preadditive.comp_add, Preadditive.comp_sub, IsIso.inv_hom_id_assoc, Category.comp_id]
      abel
    · simp only [biprod.inr_desc_assoc, Category.assoc, hφ₂, IsIso.inv_hom_id_assoc,
        Category.comp_id]

/-- **Triangular matrices are invertible**: a map `φ : bsum f n ⟶ bsum g n` whose entries
`ι_j ≫ φ ≫ π_j'` vanish for `j < j'` and are isomorphisms for `j = j'` is an isomorphism. -/
theorem isIso_bsum_of_triangular (f g : ℕ → C) :
    ∀ (n : ℕ) (φ : bsum f n ⟶ bsum g n),
      (∀ j j', j < j' → j' < n → bsumι f n j ≫ φ ≫ bsumπ g n j' = 0) →
      (∀ j, j < n → IsIso (bsumι f n j ≫ φ ≫ bsumπ g n j)) → IsIso φ
  | 0, φ, _, _ => ⟨⟨0, (isZero_zero C).eq_of_src _ _, (isZero_zero C).eq_of_src _ _⟩⟩
  | n + 1, φ, hzero, hdiag => by
    have hd : IsIso (biprod.inl ≫ φ ≫ biprod.fst) := by
      have := hdiag n (by omega)
      simpa [bsumι, bsumπ] using this
    have hsub : IsIso (biprod.inr ≫ φ ≫ biprod.snd) := by
      refine isIso_bsum_of_triangular f g n (biprod.inr ≫ φ ≫ biprod.snd) ?_ ?_
      · intro j j' hjj' hj'
        have := hzero j j' hjj' (by omega)
        have hj : ¬ j = n := by omega
        have hj'' : ¬ j' = n := by omega
        simpa [bsumι, bsumπ, hj, hj''] using this
      · intro j hj
        have := hdiag j (by omega)
        have hj' : ¬ j = n := by omega
        simpa [bsumι, bsumπ, hj'] using this
    refine isIso_biprod_of_blocks φ ?_
    apply bsum_hom_ext f
    intro j hj
    have := hzero j n hj (by omega)
    have hj' : ¬ j = n := by omega
    simpa [bsumι, bsumπ, hj'] using this

end BSumDesc

/-! ## The map `ζ` -/

namespace StrongSl2

open CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  {S : StrongSl2 k B} {r : ℤ} (e : S.EFDecomp r)

/-- `1_n⟨n-1-2k⟩ ≅ 1_n⟨n-1⟩⟨-2k⟩`. -/
def oneShiftIso (k : ℕ) : S.oneShift r k ≅ (S.oneShift r 0)⟦-((k : ℤ) * 2)⟧ :=
  (shiftFunctorAdd' _ (1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)))
    (-((k : ℤ) * 2)) (1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (k : ℤ)))
    (by push_cast; ring)).app _

/-- **`k` dots on the cup**, as a map `1_n⟨n-1-2k⟩ → E F 1_n`: `cup ≫ dot^k` shifted by `-2k`. -/
def cupK (k : ℕ) : S.oneShift r k ⟶ S.F r ≫ S.E r :=
  (oneShiftIso (S := S) (r := r) k).hom ≫ (cupDots e k)⟦-((k : ℤ) * 2)⟧' ≫
    (shiftFunctorCompIsoId _ ((k : ℤ) * 2) (-((k : ℤ) * 2)) (by ring)).hom.app _

omit [GradedBicategory.IsLinear B k] in
theorem cupK_comp (k : ℕ) {Y : S.obj (r + 1) ⟶ S.obj (r + 1)} (x : S.F r ≫ S.E r ⟶ Y) :
    cupK e k ≫ x = (oneShiftIso (S := S) (r := r) k).hom ≫
      (cupDots e k ≫ x⟦(k : ℤ) * 2⟧')⟦-((k : ℤ) * 2)⟧' ≫
      (shiftFunctorCompIsoId _ ((k : ℤ) * 2) (-((k : ℤ) * 2)) (by ring)).hom.app Y := by
  simp only [cupK, Category.assoc, Functor.map_comp]
  have := (shiftFunctorCompIsoId _ ((k : ℤ) * 2) (-((k : ℤ) * 2)) (by ring)).hom.naturality x
  simp only [Functor.id_map, Functor.comp_map] at this
  rw [← this]

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- The component of `cupK e k` in `F E 1_n` vanishes. -/
theorem cupK_comp_πFE (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r') {k : ℕ}
    (hk : k < (S.wt (r + 1)).toNat) : cupK e k ≫ πFE e = 0 := by
  rw [cupK_comp, cupDots_comp_πFE e hn hyp hk, Functor.map_zero, zero_comp, comp_zero]

/-- The component of `cupK e k` in `1_n⟨n-1-2j⟩` vanishes for `j > k`. -/
theorem cupK_comp_π_eq_zero (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r')
    (hd : DotNondeg e) {k j : ℕ} (hk : k < (S.wt (r + 1)).toNat) (hkj : k < j) :
    cupK e k ≫ π e j = 0 := by
  rw [cupK_comp, (bubble_aux e hn hyp hd k hk).1 j hkj, Functor.map_zero, zero_comp, comp_zero]

/-- The component of `cupK e k` in `1_n⟨n-1-2k⟩` is an isomorphism. -/
theorem isIso_cupK_comp_π_self (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r')
    (hd : DotNondeg e) {k : ℕ} (hk : k < (S.wt (r + 1)).toNat) : IsIso (cupK e k ≫ π e k) := by
  rw [cupK_comp]
  haveI := (bubble_aux e hn hyp hd k hk).2
  infer_instance

/-- **CL's map `ζ`** (eq. `eq:iso1`): the up-down crossing `F E 1_n → E F 1_n` (the inclusion
`ιFE e`) together with the maps `k dots ∘ cup : 1_n⟨n-1-2k⟩ → E F 1_n`. -/
def zeta : (S.E (r + 1) ≫ S.F (r + 1)) ⊞ bsum (S.oneShift r) (S.wt (r + 1)).toNat ⟶
    S.F r ≫ S.E r :=
  biprod.desc (ιFE e) (bsumDesc (S.oneShift r) (cupK e) _)

/-- **Corollary 3.13** (CL `cor:1`), from Lemma 3.6: for `n ≥ 0`, under (3.2) at the weights `> n`
and the nondegeneracy of the dot (`DotNondeg e`), `ζ` is an isomorphism. -/
theorem isIso_zeta_of_dotNondeg (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r')
    (hd : DotNondeg e) : IsIso (zeta e) := by
  -- the entries of `ζ ≫ e.hom`
  have hent : ∀ j j' : ℕ, j < (S.wt (r + 1)).toNat →
      bsumι (S.oneShift r) _ j ≫ (biprod.inr ≫ (zeta e ≫ e.hom) ≫ biprod.snd) ≫
        bsumπ (S.oneShift r) _ j' = cupK e j ≫ π e j' := by
    intro j j' hj
    simp only [zeta, Category.assoc, biprod.inr_desc_assoc]
    rw [← Category.assoc (bsumι _ _ j), bsumι_desc _ _ _ _ hj]
    rfl
  have hentFE : ∀ j : ℕ, j < (S.wt (r + 1)).toNat →
      bsumι (S.oneShift r) _ j ≫ (biprod.inr ≫ (zeta e ≫ e.hom) ≫ biprod.fst) =
        cupK e j ≫ πFE e := by
    intro j hj
    simp only [zeta, Category.assoc, biprod.inr_desc_assoc]
    rw [← Category.assoc (bsumι _ _ j), bsumι_desc _ _ _ _ hj]
    rfl
  have h1e : biprod.inl ≫ (zeta e ≫ e.hom) ≫ biprod.fst = 𝟙 _ := by simp [zeta, ιFE]
  haveI h1 : IsIso (biprod.inl ≫ (zeta e ≫ e.hom) ≫ biprod.fst) := by rw [h1e]; infer_instance
  haveI h2 : IsIso (biprod.inr ≫ (zeta e ≫ e.hom) ≫ biprod.snd) := by
    refine isIso_bsum_of_triangular _ _ _ _ ?_ ?_
    · intro j j' hjj' hj'
      rw [hent j j' (by omega)]
      exact cupK_comp_π_eq_zero e hn hyp hd (by omega) hjj'
    · intro j hj
      rw [hent j j hj]
      exact isIso_cupK_comp_π_self e hn hyp hd hj
  haveI : IsIso (zeta e ≫ e.hom) := by
    refine isIso_biprod_of_blocks _ ?_
    apply bsum_hom_ext
    intro j hj
    rw [hentFE j hj, comp_zero]
    exact cupK_comp_πFE e hn hyp hj
  have : zeta e = (zeta e ≫ e.hom) ≫ e.inv := by simp
  rw [this]
  infer_instance

/-- **Corollary 3.13** (CL `cor:1`) under the adjoint induction hypothesis at `n`: at a weight
`n = wt (r + 1) ≥ 2` with `1_n ≠ 0`, under (3.2) for all weights `≥ n`, `ζ` is an isomorphism. -/
theorem isIso_zeta_of_adjHyp [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {r : ℤ}
    (e : S.EFDecomp (r + 1)) (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 + 1 < r' → S.AdjHyp r')
    (hA : S.AdjHyp (r + 1 + 1)) (h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) : IsIso (zeta e) :=
  isIso_zeta_of_dotNondeg e (by rw [S.wt_add_one]; omega) hyp (lemXind_of_adjHyp hn hyp hA h2 e)

end StrongSl2

end Categorification.TwoRep
