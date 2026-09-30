/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CisBubRight
import Categorification.TwoRep.DotEntriesNeg

/-!
# CL Lemma 3.14 for `n ≤ 0` (eq. `eq:main2`): dots times bubbles on the `1_n` side

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Lemma 3.14 (`lem:main`), the case `n ≤ -1`: "`f ∈ Hom^m(E 1_n, E 1_n)` is of
the form `∑_i (i dots) · (f_i on 1_n)` where `f_i ∈ Hom^{m-2i}(1_n, 1_n)`" (eq. `eq:main2`), "proved
similarly" to the case `n ≥ -1`. This is the mirror of `LemMain.lean`: the bubbles sit on the
`1_n`-side of the strand (`cisBubR`), and the injectivity argument whiskers with `F 1_{n+2}` on the
right and uses the decomposition of `F E 1_n` (`FEDecomp`) and its dot (`DotEntriesNeg.lean`).

* `lemMainNeg_finrank` (**the dimension count**, the mirror of `EndE.lemMain_finrank`): for
  `n = wt (r + 1) ≤ 0` and `m < -2n`, given (3.2) at `n - 2`,
  `dim Hom(E 1_n, E 1_n⟨m⟩) = ∑_{j<-n} dim Hom(1_n, 1_n⟨m-2j⟩)`; this is `lem1Neg_step` plus
  Lemma 3.1 at `n - 2`. Note the range: the count holds for `m < 2|n|`, which for `n ≤ -2` is
  weaker than CL's hypothesis `m < 2|n+2|`; for `n = -1` both read `m < 2`.
* `ΨN`, `lemMainNeg_surjective_of_dotNondeg` (**eq. `eq:main2`, given Lemma 3.6**): under (3.2) at
  the weights `< n`, the nondegeneracy `DotNondegNeg e` of the dot on `F E 1_n` (the bottom-half
  Lemma 3.6, not proved in this development — see `DotEntriesNeg.lean`), and the coherence mixins
  `ShiftInterchange`, `ShiftAssocRight`, the map `ΨN` is surjective for `m < -2n`.

**Differences from the top half.** The top-half theorem `lemMain_surjective` at `n` needs Lemma
3.6 at `n + 2` (available from (3.2) above `n`); the bottom-half theorem at `n` needs Lemma 3.6 at
`n` itself (the decomposition of `F E 1_n` at the same weight), which is why it is stated with the
hypothesis `DotNondegNeg e`. For `n = 0` the statement is `Hom(E 1_0, E 1_0⟨m⟩) = 0` for `m < 0`
(empty sum), with `DotNondegNeg` vacuous. CL's special case "`m = 2` and `n = -1`" (eq. `eq:new`)
is a top-form statement with an index `i = 1 = n + 2` beyond the range of `LemMain.Ψ`, and is not
covered.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] (S : StrongSl2 k B) (r : ℤ)

/-- **The dimension count for `eq:main2`**: for `n = wt (r + 1) ≤ 0`, (3.2) at the weights `< n`
and `m < -2n`, `dim Hom(E 1_n, E 1_n⟨m⟩) = ∑_{j<-n} dim Hom(1_n, 1_n⟨m-2j⟩)`. -/
theorem lemMainNeg_finrank (hn : S.wt (r + 1) ≤ 0) (hyp : ∀ r', r' < r + 1 → S.AdjHyp r')
    {m : ℤ} (hm : m < -2 * S.wt (r + 1)) :
    finrank k (S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) =
      ∑ j ∈ Finset.range (-S.wt (r + 1)).toNat,
        finrank k (𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦m - 2 * (j : ℤ)⟧) := by
  rw [S.lem1Neg_step hn (hyp r (by omega)) m,
    S.lem1Neg_neg (r₁ := r + 1) hn hyp r (by omega) _ (by omega), zero_add]

/-! ## Dots times bubbles on the `1_n` side -/

/-- A dots-times-bubbles endomorphism of `E 1_n`, bottom form (eq. `eq:main2`, one term): the
bubble `g : 1_n → 1_n⟨m-2i⟩` on the `1_n`-side of the strand, then `i` dots. -/
def dotsBubN (m : ℤ) (i : ℕ)
    (g : 𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦m - 2 * (i : ℤ)⟧) :
    S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧ :=
  (cisBubRSh (S.E (r + 1)) g).comp (shPow (S.dot (r + 1)) i) (by ring)

/-- `dotsBubN m i` as a `k`-linear map. -/
def dotsBubNLin (m : ℤ) (i : ℕ) :
    (𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦m - 2 * (i : ℤ)⟧) →ₗ[k]
      (S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) where
  toFun := S.dotsBubN r m i
  map_add' g g' := by
    simp only [dotsBubN, cisBubRSh, cisBubR_add]
    exact ShiftedHom.add_comp _ _ _ _
  map_smul' c g := by
    simp only [dotsBubN, cisBubRSh, cisBubR_smul, RingHom.id_apply]
    exact ShiftedHom.smul_comp' _ _ _ _

/-- **CL's map for `eq:main2`**: `⊕_{i<-n} Hom(1_n, 1_n⟨m-2i⟩) → Hom(E 1_n, E 1_n⟨m⟩)`,
`(f_i) ↦ ∑_i (bubble f_i on the 1_n side) ∘ (i dots)`. -/
def ΨN (m : ℤ) :
    (∀ i : Fin (-S.wt (r + 1)).toNat,
      (𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦m - 2 * ((i : ℕ) : ℤ)⟧)) →ₗ[k]
      (S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) :=
  ∑ i : Fin (-S.wt (r + 1)).toNat, (S.dotsBubNLin r m i).comp (LinearMap.proj i)

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem ΨN_apply (m : ℤ)
    (f : ∀ i : Fin (-S.wt (r + 1)).toNat,
      (𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦m - 2 * ((i : ℕ) : ℤ)⟧)) :
    S.ΨN r m f = ∑ i : Fin (-S.wt (r + 1)).toNat, S.dotsBubN r m i (f i) := by
  simp [ΨN, LinearMap.sum_apply, dotsBubNLin]

/-! ## Coefficients along the cup and the summands of `F E 1_n` -/

variable {S r} (e : S.FEDecomp r)

/-- The coefficient of `φ : E 1_n → E 1_n⟨m⟩` in the summand `1_n⟨-n-1-2j⟩`:
`cup ≫ (φ ▷ F) ≫ π_j`. -/
def coefShN (j : ℕ) {m : ℤ} (φ : S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) :
    ShiftedHom (S.oneShiftNeg r 0) (S.oneShiftNeg r j) m :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl (ιN e 0)).comp
    ((shWhiskerRight (φ : ShiftedHom (S.E (r + 1)) (S.E (r + 1)) m) (S.F (r + 1))).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl (πN e j)) (zero_add m)) (add_zero m)

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem coefShN_add (j : ℕ) {m : ℤ} (φ φ' : S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) :
    coefShN e j (φ + φ') = coefShN e j φ + coefShN e j φ' := by
  simp only [coefShN, shWhiskerRight, ShiftedHom.map, ShiftedHom.comp, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

/-- The coefficient map as an additive homomorphism. -/
def coefHomN (j : ℕ) (m : ℤ) :
    (S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) →+
      ShiftedHom (S.oneShiftNeg r 0) (S.oneShiftNeg r j) m :=
  AddMonoidHom.mk' (coefShN e j) (coefShN_add e j)

/-- `cup ≫ dot^i ≫ π_j` as a shifted 2-morphism of degree `2i`. -/
def CijN (i j : ℕ) : ShiftedHom (S.oneShiftNeg r 0) (S.oneShiftNeg r j) ((i : ℤ) * 2) :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl (ιN e 0)).comp
    ((shPow (S.dotFE r) i).comp (ShiftedHom.mk₀ (0 : ℤ) rfl (πN e j)) (zero_add _))
    (add_zero _)

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem CijN_eq (i j : ℕ) :
    (CijN e i j : S.oneShiftNeg r 0 ⟶ (S.oneShiftNeg r j)⟦(i : ℤ) * 2⟧) =
      cupDotsN e i ≫ (πN e j)⟦(i : ℤ) * 2⟧' := by
  rw [CijN, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  simp only [cupDotsN, Category.assoc]

variable [GradedBicategory.ShiftInterchange B] [GradedBicategory.ShiftAssocRight B]

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The coefficient of a dots-times-bubbles term: `(g shifted) ∘ (cup ≫ dot^i ≫ π_j)`. -/
theorem coefShN_dotsBubN (j : ℕ) (m : ℤ) (i : ℕ)
    (g : 𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦m - 2 * (i : ℤ)⟧) :
    coefShN e j (S.dotsBubN r m i g) =
      (cisBubRSh (S.oneShiftNeg r 0) g).comp (CijN e i j) (by ring) := by
  have hnat : (ShiftedHom.mk₀ (0 : ℤ) rfl (ιN e 0)).comp
      (cisBubRSh (S.E (r + 1) ≫ S.F (r + 1)) g) (add_zero _) =
      (cisBubRSh (S.oneShiftNeg r 0) g).comp (ShiftedHom.mk₀ (0 : ℤ) rfl (ιN e 0))
        (zero_add _) := by
    rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
    exact cisBubR_natural (ιN e 0) g
  rw [coefShN, dotsBubN, CijN]
  change (ShiftedHom.mk₀ (0 : ℤ) rfl (ιN e 0)).comp
    ((shWhiskerRight ((cisBubRSh (S.E (r + 1)) g).comp
      (shPow (S.dot (r + 1)) i) (by ring)) (S.F (r + 1))).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl (πN e j)) (zero_add m)) (add_zero m) = _
  rw [shWhiskerRight_comp, shWhiskerRight_cisBubR, shWhiskerRight_shPow,
    ShiftedHom.comp_assoc _ _ _ (by ring : (i : ℤ) * 2 + (m - 2 * (i : ℤ)) = m)
      (by norm_num : (0 : ℤ) + (i : ℤ) * 2 = (i : ℤ) * 2) (by ring),
    ← ShiftedHom.comp_assoc _ _ _ (by ring : m - 2 * (i : ℤ) + 0 = m - 2 * (i : ℤ))
      (by ring : (i : ℤ) * 2 + (m - 2 * (i : ℤ)) = m) (by ring),
    hnat, ShiftedHom.comp_assoc _ _ _ (by ring : (0 : ℤ) + (m - 2 * (i : ℤ)) = m - 2 * (i : ℤ))
      (by ring : (i : ℤ) * 2 + 0 = (i : ℤ) * 2) (by ring)]
  rfl

/-! ## Lemma 3.14, bottom half -/

/-- **CL Lemma 3.14 for `n ≤ 0`** (eq. `eq:main2`), given the bottom-half Lemma 3.6: for
`n = wt (r + 1) ≤ 0`, (3.2) at the weights `< n`, `DotNondegNeg e`, and `m < -2n`, every
`f : E 1_n → E 1_n⟨m⟩` is a sum `∑_i (bubble f_i on the 1_n side) ∘ (i dots)`. -/
theorem lemMainNeg_surjective_of_dotNondeg (hn : S.wt (r + 1) ≤ 0)
    (hyp : ∀ r', r' < r + 1 → S.AdjHyp r') (hd : DotNondegNeg e) {m : ℤ}
    (hm : m < -2 * S.wt (r + 1)) : Function.Surjective (S.ΨN r m) := by
  have hN : (((-S.wt (r + 1)).toNat : ℕ) : ℤ) = -S.wt (r + 1) := Int.toNat_of_nonneg (by omega)
  have hfin : finrank k (∀ i : Fin (-S.wt (r + 1)).toNat,
      (𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦m - 2 * ((i : ℕ) : ℤ)⟧)) =
      finrank k (S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) := by
    rw [Module.finrank_pi_fintype, S.lemMainNeg_finrank r hn hyp hm, Finset.sum_range]
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin]
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  have hcoef : ∀ j : ℕ, ∑ i : Fin (-S.wt (r + 1)).toNat,
      (cisBubRSh (S.oneShiftNeg r 0) (f i)).comp (CijN e i j) (by ring) = 0 := by
    intro j
    have := congrArg (coefHomN e j m) hf
    rw [map_zero, ΨN_apply, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (coefShN_dotsBubN e j m i (f i)).symm
  have key : ∀ i : Fin (-S.wt (r + 1)).toNat, (∀ i' : Fin _, i < i' → f i' = 0) → f i = 0 := by
    intro i hi'
    have h := hcoef i
    rw [Finset.sum_eq_single i] at h
    · have : IsIso (CijN e i i : S.oneShiftNeg r 0 ⟶ (S.oneShiftNeg r i)⟦((i : ℕ) : ℤ) * 2⟧) := by
        rw [CijN_eq]
        exact (bubbleN_aux e hn hyp hd i i.2).2
      have h' : cisBubR (S.oneShiftNeg r 0) (f i) ≫
          ((CijN e i i : S.oneShiftNeg r 0 ⟶ _)⟦m - 2 * ((i : ℕ) : ℤ)⟧' ≫
            (shiftFunctorAdd' _ (((i : ℕ) : ℤ) * 2) (m - 2 * ((i : ℕ) : ℤ)) m
              (by ring)).inv.app _) = 0 := h
      have h'' := congrArg (fun φ => φ ≫ inv ((CijN e i i : S.oneShiftNeg r 0 ⟶ _)⟦m -
        2 * ((i : ℕ) : ℤ)⟧' ≫ (shiftFunctorAdd' _ (((i : ℕ) : ℤ) * 2) (m - 2 * ((i : ℕ) : ℤ)) m
          (by ring)).inv.app _)) h'
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, zero_comp] at h''
      exact eq_zero_of_cisBubR_eq_zero _ _ h''
    · intro i' _ hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hz : CijN e i' i = 0 := by
          rw [CijN_eq]
          exact (bubbleN_aux e hn hyp hd i' i'.2).1 i (Fin.lt_def.1 hlt)
        rw [hz, ShiftedHom.comp_zero]
      · rw [hi' i' hgt, cisBubRSh, cisBubR_zero]
        apply ShiftedHom.zero_comp
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hall : ∀ t : ℕ, ∀ i : Fin (-S.wt (r + 1)).toNat,
      (-S.wt (r + 1)).toNat - 1 - (i : ℕ) ≤ t → f i = 0 := by
    intro t
    induction t with
    | zero =>
      intro i hi
      refine key i fun i' hi' => ?_
      exfalso
      have := i'.2
      have := Fin.lt_def.1 hi'
      omega
    | succ t ih =>
      intro i hi
      refine key i fun i' hi' => ih i' ?_
      have := Fin.lt_def.1 hi'
      omega
  funext i
  exact hall _ i le_rfl

end Categorification.TwoRep.StrongSl2
