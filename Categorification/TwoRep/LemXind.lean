/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.DotEntries
import Categorification.TwoRep.DividedPowerDot
import Categorification.TwoRep.MultShift
import Categorification.TwoRep.StepLemmas

/-!
# CL Lemma 3.6, given the adjoint induction hypothesis at `n`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Lemma 3.6 (`lem:Xind`), in the form `DotNondeg e` of `DotEntries.lean`: for a
decomposition `E F 1_n ≅ F E 1_n ⊕ ⊕_{j<n} 1_n⟨n-1-2j⟩` the `n - 1` subdiagonal scalars of the dot
`E F 1_n → E F 1_n ⟨2⟩` are nonzero. The proof is CL's rank comparison on
`E E F 1_{n-2}` (also S. Cautis, *Rigidity in higher representation theory*, arXiv:1409.0827v1,
Lemma 13.1), made non-circular by assuming (3.2) *at* `n` (Proposition 3.9 at `n`; the theorem is
`lemXind_of_adjHyp`), so that Lemma 3.1 at `n - 2` and the right adjoint of `F 1_{n+2}` are
available, and organised so that no Krull–Schmidt cancellation with rigidity is needed. Only the
numerical shadow `NumAdj` (`WordBounded.lean`) of (3.2) is used, at the weight `n` and above
(`lemXind_of_numAdj`). The Hom-finite hypothesis remains essential when turning vanishing
finranks into zero morphisms. Under (BB_w) and the ambient graded linear and Hom-finite
hypotheses, `BBw.numAdj` (in `WordNumerics.lean`) supplies the shadow at every weight; this does not
construct an actual adjunction.

Indexing: `1_n` at the object `r + 1 + 1`, `E 1_{n-2} = E (r + 1)`, `E 1_{n-4} = E r`,
`F 1_{n-2} = F r`, `E E F 1_{n-2} = F r ≫ (E r ≫ E (r + 1))` (`FW`), `E F 1_n = F (r + 1) ≫ E (r + 1)`
with decomposition `e : EFDecomp (r + 1)`, `E F 1_{n-2} = F r ≫ E r` with `e' : EFDecomp r`.

The map is `Φ₀ = F r ◁ (E r ◁ dot)`, the dot on the outer strand `E 1_{n-2}` of `E E F 1_{n-2}`,
as a map `FW → FW₂ = F r ≫ (E r ≫ E 1_{n-2}⟨2⟩)`. Its "`E 1_{n-2}⟨a_i⟩`-rank" is compared through
the pairing `(g, h) ↦ g ≫ Φ₀ ≫ h` on `Hom(A_i, FW) × Hom(FW₂, A_i)`, `A_i = E 1_{n-2} 1_n⟨a_i⟩`,
`a_i = n - 1 - 2i`:

* **Upper bound** (`pairing_eq_zero_of_entry_eq_zero`): if the subdiagonal entry
  `entry e i (i+1)` vanishes then the pairing is identically zero. `FW` decomposes (through `e'`
  and `e`) into `E 1_{n-2} (E F 1_{n+2})`, the summands `A_j` and the summands
  `B_j = 1_{n-2}⟨b_j⟩ E 1_{n-2}`; `Φ₀` is block diagonal for the first decomposition
  (`ιb_comp_Φ₀`), acts on the `A`-block through the whiskered matrix of the dot on `E F 1_n`
  (`ιa_comp_Φ₀`), and all other contributions vanish by degree (Lemma 3.1 at `n - 2`, Corollary
  3.2 at `n - 2`, and `Hom(E E F 1_{n+2}⟨2⟩, E 1_{n-2}⟨a⟩) = 0` which uses (3.2) at `n`).
* **Lower bound** (`exists_pairing_ne_zero`): the splitting `E E 1_{n-4} ≅ P ⊕ P⟨-2⟩`
  (`P = E^{(2)} 1_{n-4}⟨1⟩`) on which the dot is an isomorphism `P → P⟨-2⟩⟨2⟩`
  (`DividedPowerDot.exists_E2_dot`) gives an isomorphism `F P → F P⟨-2⟩⟨2⟩` as a component of `Φ₀`;
  if `A_i` is a direct summand of `F P` (CL: "`E^{(2)} F 1_{n-2} ≅ F E^{(2)} 1_{n-2} ⊕_{[n-1]}
  E 1_{n-2}`") the pairing takes the value `1_{A_i} ≠ 0`. The summand is produced by counting
  multiplicities of the indecomposable `E 1_{n-2}⟨a⟩` (`MultShift.lean`): `m(a) + m(a+2) =
  mult_{E⟨a⟩}(F E E 1_{n-4})`, whose right-hand side is computed from the decomposition of
  `E E F 1_{n-2}`; descending from `a = n + 1` gives `m(a_i) = mult_E(E) > 0` for `i ≤ n - 2`
  (`mult_FP_eq`). This replaces CL's cancellation of `[2]` in `E E F ≅ [2] E^{(2)} F`, which would
  need the rigidity hypothesis of `cancel_shiftSum`.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite IsIndec mult)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] (S : StrongSl2 k B) (r : ℤ)

/-! ## The objects and the map -/

/-- `E E F 1_{n-2} = F r ≫ (E r ≫ E (r + 1))`. -/
abbrev FW : S.obj (r + 1) ⟶ S.obj (r + 1 + 1) := S.F r ≫ (S.E r ≫ S.E (r + 1))

/-- `E E F 1_{n-2}` with the outer strand shifted by `2`. -/
abbrev FW₂ : S.obj (r + 1) ⟶ S.obj (r + 1 + 1) := S.F r ≫ (S.E r ≫ (S.E (r + 1))⟦(2 : ℤ)⟧)

/-- The dot on the outer strand `E 1_{n-2}` of `E E F 1_{n-2}`. -/
def Φ₀ : S.FW r ⟶ S.FW₂ r :=
  S.F r ◁ (S.E r ◁ (S.dot (r + 1) : S.E (r + 1) ⟶ (S.E (r + 1))⟦(2 : ℤ)⟧))

/-- The summand `A_j = E 1_{n-2} 1_n⟨a_j⟩` of `E F E 1_{n-2} ⊆ E E F 1_{n-2}`. -/
abbrev Asum (j : ℕ) : S.obj (r + 1) ⟶ S.obj (r + 1 + 1) := S.E (r + 1) ≫ S.oneShift (r + 1) j

/-- The summand `A_j` of `FW₂`. -/
abbrev Asum₂ (j : ℕ) : S.obj (r + 1) ⟶ S.obj (r + 1 + 1) :=
  S.E (r + 1) ≫ (S.oneShift (r + 1) j)⟦(2 : ℤ)⟧

/-- The summand `B_j = 1_{n-2}⟨b_j⟩ E 1_{n-2}` of `[n-2] E 1_{n-2} ⊆ E E F 1_{n-2}`. -/
abbrev Bsum (j : ℕ) : S.obj (r + 1) ⟶ S.obj (r + 1 + 1) := S.oneShift r j ≫ S.E (r + 1)

/-- The summand `B_j` of `FW₂`. -/
abbrev Bsum₂ (j : ℕ) : S.obj (r + 1) ⟶ S.obj (r + 1 + 1) := S.oneShift r j ≫ (S.E (r + 1))⟦(2 : ℤ)⟧

/-- The summand `C = E 1_{n-2} (E F 1_{n+2})` of `E E F 1_{n-2}`. -/
abbrev Csum : S.obj (r + 1) ⟶ S.obj (r + 1 + 1) :=
  S.E (r + 1) ≫ (S.E (r + 1 + 1) ≫ S.F (r + 1 + 1))

/-- The summand `C` of `FW₂`. -/
abbrev Csum₂ : S.obj (r + 1) ⟶ S.obj (r + 1 + 1) :=
  S.E (r + 1) ≫ (S.E (r + 1 + 1) ≫ S.F (r + 1 + 1))⟦(2 : ℤ)⟧

variable {S r}

/-! ## Degree vanishing -/

section Vanishing

variable (hyp : ∀ r', r + 1 < r' → S.NumAdj r')

include hyp in
/-- Lemma 3.1 at `n - 2` (under the numerical shadow of (3.2) at the weights `≥ n`): `Hom(E 1_{n-2}⟨a⟩, E 1_{n-2}⟨b⟩) = 0`
for `b < a`. -/
theorem hom_E_shift_eq_zero (hn : 0 ≤ S.wt (r + 1)) {a b : ℤ} (hab : b < a)
    (f : (S.E (r + 1))⟦a⟧ ⟶ (S.E (r + 1))⟦b⟧) : f = 0 := by
  have h0 : finrank k ((S.E (r + 1))⟦a⟧ ⟶ (S.E (r + 1))⟦b⟧) = 0 := by
    rw [finrank_hom_shift_shift k _ _ (c := b - a) (by ring)]
    exact S.lem1_neg_of_numAdj (r₀ := r + 1) hn hyp (r + 1) le_rfl _ (by omega)
  exact eq_zero_of_finrank_eq_zero h0 f

variable (S r) in
/-- `A_j ≅ E 1_{n-2}⟨a_j⟩`. -/
def AsumIso (j : ℕ) : S.Asum r j ≅
    (S.E (r + 1))⟦1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ))⟧ :=
  compIdShiftIso _ _

variable (S r) in
/-- `A_j⟨2⟩ ≅ E 1_{n-2}⟨a_j + 2⟩`. -/
def Asum₂Iso (j : ℕ) : S.Asum₂ r j ≅
    (S.E (r + 1))⟦1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) + 2⟧ :=
  whiskerLeftIso _ ((shiftFunctorAdd' _ _ (2 : ℤ) _ rfl).app (𝟙 _)).symm ≪≫ compIdShiftIso _ _

variable (S r) in
/-- `B_j ≅ E 1_{n-2}⟨b_j⟩`. -/
def BsumIso (j : ℕ) : S.Bsum r j ≅
    (S.E (r + 1))⟦1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ))⟧ :=
  idShiftCompIso _ _

variable (S r) in
/-- `B_j⟨2⟩ ≅ E 1_{n-2}⟨b_j + 2⟩`. -/
def Bsum₂Iso (j : ℕ) : S.Bsum₂ r j ≅
    (S.E (r + 1))⟦(2 : ℤ) + 1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ))⟧ :=
  idShiftCompShiftIso _ rfl

include hyp in
theorem hom_A_A_eq_zero (hn : 0 ≤ S.wt (r + 1)) {i j : ℕ} (hij : i < j)
    (f : S.Asum r i ⟶ S.Asum r j) : f = 0 := by
  have : f = (S.AsumIso r i).hom ≫ ((S.AsumIso r i).inv ≫ f ≫ (S.AsumIso r j).hom) ≫
      (S.AsumIso r j).inv := by simp
  rw [this, hom_E_shift_eq_zero hyp hn (by omega) ((S.AsumIso r i).inv ≫ f ≫ (S.AsumIso r j).hom),
    zero_comp, comp_zero]

include hyp in
theorem hom_A₂_A_eq_zero (hn : 0 ≤ S.wt (r + 1)) {i j : ℕ} (hij : j < i + 1)
    (f : S.Asum₂ r j ⟶ S.Asum r i) : f = 0 := by
  have : f = (S.Asum₂Iso r j).hom ≫ ((S.Asum₂Iso r j).inv ≫ f ≫ (S.AsumIso r i).hom) ≫
      (S.AsumIso r i).inv := by simp
  rw [this, hom_E_shift_eq_zero hyp hn (by omega) ((S.Asum₂Iso r j).inv ≫ f ≫ (S.AsumIso r i).hom),
    zero_comp, comp_zero]

include hyp in
theorem hom_A_B_eq_zero (hn : 0 ≤ S.wt (r + 1)) {i j : ℕ}
    (hij : 1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) <
      1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (i : ℤ)))
    (f : S.Asum r i ⟶ S.Bsum r j) : f = 0 := by
  have : f = (S.AsumIso r i).hom ≫ ((S.AsumIso r i).inv ≫ f ≫ (S.BsumIso r j).hom) ≫
      (S.BsumIso r j).inv := by simp
  rw [this, hom_E_shift_eq_zero hyp hn hij ((S.AsumIso r i).inv ≫ f ≫ (S.BsumIso r j).hom),
    zero_comp, comp_zero]

include hyp in
theorem hom_B₂_A_eq_zero (hn : 0 ≤ S.wt (r + 1)) {i j : ℕ}
    (hij : 1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (i : ℤ)) <
      (2 : ℤ) + 1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)))
    (f : S.Bsum₂ r j ⟶ S.Asum r i) : f = 0 := by
  have : f = (S.Bsum₂Iso r j).hom ≫ ((S.Bsum₂Iso r j).inv ≫ f ≫ (S.AsumIso r i).hom) ≫
      (S.AsumIso r i).inv := by simp
  rw [this, hom_E_shift_eq_zero hyp hn hij ((S.Bsum₂Iso r j).inv ≫ f ≫ (S.AsumIso r i).hom),
    zero_comp, comp_zero]

/-- `Hom(E 1_{n-2}⟨a⟩, E 1_{n-2} E F 1_{n+2}) = 0` for `a > -n + 1` (Corollary 3.2 at `n - 2`). -/
theorem finrank_E_shift_C_eq_zero (hn : 0 ≤ S.wt (r + 1 + 1))
    (hyp : ∀ r', r + 1 + 1 < r' → S.NumAdj r') {a : ℤ} (ha : -S.wt (r + 1 + 1) + 1 < a) :
    finrank k ((S.E (r + 1))⟦a⟧ ⟶ S.Csum r) = 0 := by
  have hw : S.wt (r + 1 + 1) = S.wt (r + 1) + 2 := S.wt_add_one _
  calc finrank k ((S.E (r + 1))⟦a⟧ ⟶ S.Csum r)
      = finrank k (((S.E (r + 1))⟦a⟧)⟦S.wt (r + 1 + 1) + 1⟧ ⟶ (S.Csum r)⟦S.wt (r + 1 + 1) + 1⟧) :=
        (finrank_hom_shift k _ _ _).symm
    _ = finrank k ((S.E (r + 1))⟦a + (S.wt (r + 1 + 1) + 1)⟧ ⟶
          (S.E (r + 1) ≫ S.E (r + 1 + 1)) ≫ (S.F (r + 1 + 1))⟦S.wt (r + 1 + 1) + 1⟧) :=
        finrank_hom_congr k ((shiftFunctorAdd' _ a _ _ rfl).app _).symm
          ((shiftFunctor _ _).mapIso (α_ _ _ _).symm ≪≫ (whiskerLeftShiftIso _ _ _).symm)
    _ = finrank k ((S.E (r + 1))⟦a + (S.wt (r + 1 + 1) + 1)⟧ ≫ S.E (r + 1 + 1) ⟶
          S.E (r + 1) ≫ S.E (r + 1 + 1)) := ((S.dimAdj (r + 1 + 1)).left _ _).symm
    _ = finrank k (S.E (r + 1) ≫ S.E (r + 1 + 1) ⟶
          (S.E (r + 1) ≫ S.E (r + 1 + 1))⟦-(a + (S.wt (r + 1 + 1) + 1))⟧) := by
        rw [finrank_hom_congr_left k (whiskerRightShiftIso _ _ _), finrank_hom_shift_left k _ _
          (b := -(a + (S.wt (r + 1 + 1) + 1))) (by ring)]
    _ = 0 := S.cor0_neg_of_numAdj (r₀ := r + 1 + 1) hn hyp (r + 1) (by omega) _ (by omega)

/-- `Hom(E 1_{n-2} (E F 1_{n+2})⟨2⟩, E 1_{n-2}⟨a⟩) = 0` for `a < n + 1`; this uses
`(F 1_{n+2})_R ≅ E 1_n ⟨-n-1⟩`, i.e. (3.2) at `n`, through its numerical shadow. -/
theorem finrank_C₂_E_shift_eq_zero (hn : 0 ≤ S.wt (r + 1 + 1))
    (hyp : ∀ r', r + 1 + 1 < r' → S.NumAdj r') (hA : S.NumAdj (r + 1 + 1)) {a : ℤ}
    (ha : a < S.wt (r + 1 + 1) + 1) : finrank k (S.Csum₂ r ⟶ (S.E (r + 1))⟦a⟧) = 0 := by
  calc finrank k (S.Csum₂ r ⟶ (S.E (r + 1))⟦a⟧)
      = finrank k ((S.E (r + 1) ≫ S.E (r + 1 + 1)) ≫ S.F (r + 1 + 1) ⟶
          (S.E (r + 1))⟦a - 2⟧) := by
        rw [finrank_hom_congr_left k (whiskerLeftShiftIso _ _ _),
          finrank_hom_shift_shift k _ _ (c := a - 2) (by ring),
          finrank_hom_congr_left k (α_ _ _ _).symm]
    _ = finrank k (S.E (r + 1) ≫ S.E (r + 1 + 1) ⟶
          (S.E (r + 1))⟦a - 2⟧ ≫ (S.E (r + 1 + 1))⟦-(S.wt (r + 1 + 1) + 1)⟧) :=
        hA.left ((WordGen.E _).comp (.E _)) ((WordGen.E _).shift _)
    _ = finrank k (S.E (r + 1) ≫ S.E (r + 1 + 1) ⟶
          (S.E (r + 1) ≫ S.E (r + 1 + 1))⟦a - 2 - (S.wt (r + 1 + 1) + 1)⟧) :=
        finrank_hom_congr_right k _ (shiftCompShiftIso _ _ (by ring))
    _ = 0 := S.cor0_neg_of_numAdj (r₀ := r + 1 + 1) hn hyp (r + 1) (by omega) _ (by omega)

end Vanishing

/-! ## The summand maps of `E E F 1_{n-2}` and the block structure of `Φ₀` -/

section Summands

variable (e' : S.EFDecomp r) (e : S.EFDecomp (r + 1))

/-- The inclusion of `B_j = 1_{n-2}⟨b_j⟩ E 1_{n-2}` into `E E F 1_{n-2}`. -/
def ιb (j : ℕ) : S.Bsum r j ⟶ S.FW r :=
  (ι e' j ▷ S.E (r + 1)) ≫ (α_ (S.F r) (S.E r) (S.E (r + 1))).hom

/-- The projection of `E E F 1_{n-2}` onto `B_j`. -/
def πb (j : ℕ) : S.FW r ⟶ S.Bsum r j :=
  (α_ (S.F r) (S.E r) (S.E (r + 1))).inv ≫ (π e' j ▷ S.E (r + 1))

/-- The inclusion of `B_j⟨2⟩` into `FW₂`. -/
def ιb₂ (j : ℕ) : S.Bsum₂ r j ⟶ S.FW₂ r :=
  (ι e' j ▷ (S.E (r + 1))⟦(2 : ℤ)⟧) ≫ (α_ (S.F r) (S.E r) ((S.E (r + 1))⟦(2 : ℤ)⟧)).hom

/-- The inclusion of `A_j = E 1_{n-2} 1_n⟨a_j⟩` into `E E F 1_{n-2}` (through
`E 1_{n-2} (E F 1_n) = (E F 1_{n-2}) E 1_{n-2}`). -/
def ιa (j : ℕ) : S.Asum r j ⟶ S.FW r :=
  (S.E (r + 1) ◁ ι e j) ≫ (α_ (S.E (r + 1)) (S.F (r + 1)) (S.E (r + 1))).inv ≫
    (ιFE e' ▷ S.E (r + 1)) ≫ (α_ (S.F r) (S.E r) (S.E (r + 1))).hom

/-- The projection of `E E F 1_{n-2}` onto `A_j`. -/
def πa (j : ℕ) : S.FW r ⟶ S.Asum r j :=
  (α_ (S.F r) (S.E r) (S.E (r + 1))).inv ≫ (πFE e' ▷ S.E (r + 1)) ≫
    (α_ (S.E (r + 1)) (S.F (r + 1)) (S.E (r + 1))).hom ≫ (S.E (r + 1) ◁ π e j)

/-- The inclusion of `A_j⟨2⟩` into `FW₂`. -/
def ιa₂ (j : ℕ) : S.Asum₂ r j ⟶ S.FW₂ r :=
  (S.E (r + 1) ◁ ((ι e j)⟦(2 : ℤ)⟧' ≫ (whiskerLeftShiftIso (S.F (r + 1)) (S.E (r + 1)) 2).inv)) ≫
    (α_ (S.E (r + 1)) (S.F (r + 1)) ((S.E (r + 1))⟦(2 : ℤ)⟧)).inv ≫
    (ιFE e' ▷ (S.E (r + 1))⟦(2 : ℤ)⟧) ≫ (α_ (S.F r) (S.E r) ((S.E (r + 1))⟦(2 : ℤ)⟧)).hom

/-- The inclusion of `C = E 1_{n-2} (E F 1_{n+2})` into `E E F 1_{n-2}`. -/
def ιc : S.Csum r ⟶ S.FW r :=
  (S.E (r + 1) ◁ ιFE e) ≫ (α_ (S.E (r + 1)) (S.F (r + 1)) (S.E (r + 1))).inv ≫
    (ιFE e' ▷ S.E (r + 1)) ≫ (α_ (S.F r) (S.E r) (S.E (r + 1))).hom

/-- The projection of `E E F 1_{n-2}` onto `C`. -/
def πc : S.FW r ⟶ S.Csum r :=
  (α_ (S.F r) (S.E r) (S.E (r + 1))).inv ≫ (πFE e' ▷ S.E (r + 1)) ≫
    (α_ (S.E (r + 1)) (S.F (r + 1)) (S.E (r + 1))).hom ≫ (S.E (r + 1) ◁ πFE e)

/-- The inclusion of `C⟨2⟩` into `FW₂`. -/
def ιc₂ : S.Csum₂ r ⟶ S.FW₂ r :=
  (S.E (r + 1) ◁ ((ιFE e)⟦(2 : ℤ)⟧' ≫ (whiskerLeftShiftIso (S.F (r + 1)) (S.E (r + 1)) 2).inv)) ≫
    (α_ (S.E (r + 1)) (S.F (r + 1)) ((S.E (r + 1))⟦(2 : ℤ)⟧)).inv ≫
    (ιFE e' ▷ (S.E (r + 1))⟦(2 : ℤ)⟧) ≫ (α_ (S.F r) (S.E r) ((S.E (r + 1))⟦(2 : ℤ)⟧)).hom

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
theorem whiskerRight_sum' {a b c : B} {f g : a ⟶ b} {ι : Type*} (s : Finset ι) (η : ι → (f ⟶ g))
    (h : b ⟶ c) : (∑ j ∈ s, η j) ▷ h = ∑ j ∈ s, η j ▷ h :=
  (postcomp a h).map_sum η s

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
theorem whiskerLeft_sum' {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} {ι : Type*} (s : Finset ι)
    (θ : ι → (g ⟶ h)) : f ◁ (∑ j ∈ s, θ j) = ∑ j ∈ s, f ◁ θ j :=
  (precomp c f).map_sum θ s

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The decomposition of the identity of `E E F 1_{n-2}`. -/
theorem total_FW :
    ∑ j ∈ Finset.range (S.wt (r + 1)).toNat, πb e' j ≫ ιb e' j +
      (∑ j ∈ Finset.range (S.wt (r + 1 + 1)).toNat, πa e' e j ≫ ιa e' e j + πc e' e ≫ ιc e' e) =
      𝟙 (S.FW r) := by
  have h1 : ∀ j, πa e' e j ≫ ιa e' e j =
      (α_ _ _ _).inv ≫ (πFE e' ▷ S.E (r + 1)) ≫ ((α_ _ _ _).hom ≫
        (S.E (r + 1) ◁ (π e j ≫ ι e j)) ≫ (α_ _ _ _).inv) ≫ (ιFE e' ▷ S.E (r + 1)) ≫
        (α_ _ _ _).hom := by
    intro j
    simp only [πa, ιa, Bicategory.whiskerLeft_comp, Category.assoc]
  have h2 : πc e' e ≫ ιc e' e =
      (α_ _ _ _).inv ≫ (πFE e' ▷ S.E (r + 1)) ≫ ((α_ _ _ _).hom ≫
        (S.E (r + 1) ◁ (πFE e ≫ ιFE e)) ≫ (α_ _ _ _).inv) ≫ (ιFE e' ▷ S.E (r + 1)) ≫
        (α_ _ _ _).hom := by
    simp only [πc, ιc, Bicategory.whiskerLeft_comp, Category.assoc]
  have h3 : ∀ j, πb e' j ≫ ιb e' j =
      (α_ _ _ _).inv ≫ ((π e' j ≫ ι e' j) ▷ S.E (r + 1)) ≫ (α_ _ _ _).hom := by
    intro j
    simp only [πb, ιb, comp_whiskerRight, Category.assoc]
  have hb : ∑ j ∈ Finset.range (S.wt (r + 1)).toNat, πb e' j ≫ ιb e' j =
      (α_ _ _ _).inv ≫ ((∑ j ∈ Finset.range (S.wt (r + 1)).toNat, π e' j ≫ ι e' j) ▷
        S.E (r + 1)) ≫ (α_ _ _ _).hom := by
    simp only [h3, whiskerRight_sum', Preadditive.sum_comp, Preadditive.comp_sum]
  have ha : ∑ j ∈ Finset.range (S.wt (r + 1 + 1)).toNat, πa e' e j ≫ ιa e' e j +
      πc e' e ≫ ιc e' e =
      (α_ _ _ _).inv ≫ (πFE e' ▷ S.E (r + 1)) ≫ ((α_ _ _ _).hom ≫
        (S.E (r + 1) ◁ (∑ j ∈ Finset.range (S.wt (r + 1 + 1)).toNat, π e j ≫ ι e j +
          πFE e ≫ ιFE e)) ≫ (α_ _ _ _).inv) ≫ (ιFE e' ▷ S.E (r + 1)) ≫ (α_ _ _ _).hom := by
    simp only [h1, h2, whiskerLeft_sum', whiskerLeft_add, Preadditive.sum_comp,
      Preadditive.comp_sum, Preadditive.add_comp, Preadditive.comp_add]
  rw [hb, ha, total e, Bicategory.whiskerLeft_id, Category.id_comp, Iso.hom_inv_id,
    Category.id_comp, ← comp_whiskerRight_assoc, ← Preadditive.comp_add, ← Preadditive.add_comp,
    ← add_whiskerRight, total e', Bicategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- `Φ₀` is diagonal on the `B`-summands: `B_j → B_j⟨2⟩` is the dot. -/
theorem ιb_comp_Φ₀ (j : ℕ) :
    ιb e' j ≫ S.Φ₀ r =
      (S.oneShift r j ◁ (S.dot (r + 1) : S.E (r + 1) ⟶ (S.E (r + 1))⟦(2 : ℤ)⟧)) ≫ ιb₂ e' j := by
  simp only [ιb, ιb₂, Φ₀, Category.assoc]
  rw [← associator_naturality_right, ← whisker_exchange_assoc]

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The dot on `E F 1_n` followed by the identification with the shift of `F E`, expanded along the
decomposition. -/
theorem ι_comp_whiskerLeft_dot (j : ℕ) :
    ι e j ≫ (S.F (r + 1) ◁ (S.dot (r + 1) : S.E (r + 1) ⟶ (S.E (r + 1))⟦(2 : ℤ)⟧)) =
      ∑ j' ∈ Finset.range (S.wt (r + 1 + 1)).toNat, entry e j j' ≫
        ((ι e j')⟦(2 : ℤ)⟧' ≫ (whiskerLeftShiftIso (S.F (r + 1)) (S.E (r + 1)) 2).inv) +
      (ι e j ≫ S.dotEF (r + 1) ≫ (πFE e)⟦(2 : ℤ)⟧') ≫
        ((ιFE e)⟦(2 : ℤ)⟧' ≫ (whiskerLeftShiftIso (S.F (r + 1)) (S.E (r + 1)) 2).inv) := by
  have hd : S.F (r + 1) ◁ (S.dot (r + 1) : S.E (r + 1) ⟶ (S.E (r + 1))⟦(2 : ℤ)⟧) =
      S.dotEF (r + 1) ≫ (whiskerLeftShiftIso (S.F (r + 1)) (S.E (r + 1)) 2).inv := by
    rw [dotEF, shWhiskerLeft_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hd, ← Category.assoc, ← Category.comp_id (ι e j ≫ S.dotEF (r + 1)),
    ← CategoryTheory.Functor.map_id (shiftFunctor _ (2 : ℤ)), ← total e, Functor.map_add,
    Functor.map_sum]
  simp only [Preadditive.comp_add, Preadditive.comp_sum, Preadditive.add_comp,
    Preadditive.sum_comp, Functor.map_comp, Category.assoc, entry]

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- `Φ₀` on the `A`-summands acts through the whiskered matrix of the dot on `E F 1_n`. -/
theorem ιa_comp_Φ₀ (j : ℕ) :
    ιa e' e j ≫ S.Φ₀ r =
      ∑ j' ∈ Finset.range (S.wt (r + 1 + 1)).toNat,
        (S.E (r + 1) ◁ entry e j j') ≫ ιa₂ e' e j' +
      (S.E (r + 1) ◁ (ι e j ≫ S.dotEF (r + 1) ≫ (πFE e)⟦(2 : ℤ)⟧')) ≫ ιc₂ e' e := by
  simp only [ιa, ιa₂, ιc₂, Φ₀, Category.assoc]
  rw [← associator_naturality_right, ← whisker_exchange_assoc,
    ← associator_inv_naturality_right_assoc, ← Bicategory.whiskerLeft_comp_assoc,
    ι_comp_whiskerLeft_dot]
  simp only [Bicategory.whiskerLeft_comp, whiskerLeft_add, whiskerLeft_sum', Preadditive.add_comp,
    Preadditive.sum_comp, Category.assoc]

end Summands

/-! ## The upper bound -/

section Upper

variable (e' : S.EFDecomp r) (e : S.EFDecomp (r + 1))

include e' in
/-- **Upper bound**: if the subdiagonal entry `entry e i (i+1)` of the dot vanishes, then the
pairing `(g, h) ↦ g ≫ Φ₀ ≫ h` on `Hom(A_i, E E F 1_{n-2}) × Hom(FW₂, A_i)` is identically zero
(under (3.2) at the weights `≥ n`). -/
theorem pairing_eq_zero_of_entry_eq_zero (hn : 0 ≤ S.wt (r + 1))
    (hyp : ∀ r', r + 1 + 1 < r' → S.NumAdj r') (hA : S.NumAdj (r + 1 + 1)) {i : ℕ}
    (hi : i + 1 < (S.wt (r + 1 + 1)).toNat) (h0 : entry e i (i + 1) = 0)
    (g : S.Asum r i ⟶ S.FW r) (h : S.FW₂ r ⟶ S.Asum r i) : g ≫ S.Φ₀ r ≫ h = 0 := by
  have hw : S.wt (r + 1 + 1) = S.wt (r + 1) + 2 := S.wt_add_one _
  have hN : (((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) = S.wt (r + 1 + 1) := Int.toNat_of_nonneg (by omega)
  have hN' : (((S.wt (r + 1)).toNat : ℕ) : ℤ) = S.wt (r + 1) := Int.toNat_of_nonneg hn
  have hyp' : ∀ r', r + 1 < r' → S.NumAdj r' := fun r' hr' => by
    rcases lt_or_eq_of_le (show r + 1 + 1 ≤ r' by omega) with h' | h'
    · exact hyp r' h'
    · rw [← h']; exact hA
  -- the components of `g` and `h` through `C` vanish by degree
  have hgc : g ≫ πc e' e = 0 := by
    have : g ≫ πc e' e = (S.AsumIso r i).hom ≫ ((S.AsumIso r i).inv ≫ g ≫ πc e' e) := by simp
    rw [this, eq_zero_of_finrank_eq_zero (S.finrank_E_shift_C_eq_zero (by omega) hyp (by omega))
      ((S.AsumIso r i).inv ≫ g ≫ πc e' e), comp_zero]
  have hch : ιc₂ e' e ≫ h = 0 := by
    have : ιc₂ e' e ≫ h = (ιc₂ e' e ≫ h ≫ (S.AsumIso r i).hom) ≫ (S.AsumIso r i).inv := by simp
    rw [this, eq_zero_of_finrank_eq_zero
      (S.finrank_C₂_E_shift_eq_zero (by omega) hyp hA (by omega))
      (ιc₂ e' e ≫ h ≫ (S.AsumIso r i).hom), zero_comp]
  -- the `B`-terms vanish by degree
  have hb : ∀ j ∈ Finset.range (S.wt (r + 1)).toNat,
      g ≫ πb e' j ≫ ιb e' j ≫ S.Φ₀ r ≫ h = 0 := by
    intro j _
    rw [← Category.assoc (ιb e' j), ιb_comp_Φ₀]
    simp only [Category.assoc]
    by_cases hj : 1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) <
        1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (i : ℤ))
    · rw [← Category.assoc g, hom_A_B_eq_zero hyp' hn hj (g ≫ πb e' j), zero_comp]
    · rw [hom_B₂_A_eq_zero hyp' hn (by push Not at hj; omega) (ιb₂ e' j ≫ h), comp_zero,
        comp_zero, comp_zero]
  -- the `A`-terms: only `entry e i (i+1)` could contribute
  have ha : ∀ j ∈ Finset.range (S.wt (r + 1 + 1)).toNat,
      g ≫ πa e' e j ≫ ιa e' e j ≫ S.Φ₀ r ≫ h = 0 := by
    intro j _
    rw [← Category.assoc (ιa e' e j), ιa_comp_Φ₀]
    simp only [Preadditive.add_comp, Preadditive.sum_comp, Preadditive.comp_add,
      Preadditive.comp_sum, Category.assoc]
    rw [hch, comp_zero, comp_zero, comp_zero, add_zero]
    refine Finset.sum_eq_zero fun j' _ => ?_
    by_cases hij : i < j
    · rw [← Category.assoc g, hom_A_A_eq_zero hyp' hn hij (g ≫ πa e' e j), zero_comp]
    · by_cases hj' : j' < i + 1
      · rw [hom_A₂_A_eq_zero hyp' hn hj' (ιa₂ e' e j' ≫ h), comp_zero, comp_zero, comp_zero]
      · by_cases hjj : j + 1 < j'
        · rw [entry_eq_zero e hjj, whiskerLeft_zero', zero_comp, comp_zero, comp_zero]
        · have hj'' : j' = i + 1 := by omega
          have hj0 : j = i := by omega
          subst hj'' hj0
          rw [h0, whiskerLeft_zero', zero_comp, comp_zero, comp_zero]
  calc g ≫ S.Φ₀ r ≫ h = g ≫ (𝟙 _ ≫ S.Φ₀ r) ≫ h := by rw [Category.id_comp]
    _ = ∑ j ∈ Finset.range (S.wt (r + 1)).toNat, g ≫ πb e' j ≫ ιb e' j ≫ S.Φ₀ r ≫ h +
        (∑ j ∈ Finset.range (S.wt (r + 1 + 1)).toNat,
          g ≫ πa e' e j ≫ ιa e' e j ≫ S.Φ₀ r ≫ h +
          g ≫ πc e' e ≫ ιc e' e ≫ S.Φ₀ r ≫ h) := by
        rw [← total_FW e' e]
        simp only [Preadditive.add_comp, Preadditive.sum_comp, Preadditive.comp_add,
          Preadditive.comp_sum, Category.assoc]
    _ = 0 := by
        rw [Finset.sum_eq_zero hb, Finset.sum_eq_zero ha, ← Category.assoc g (πc e' e), hgc,
          zero_comp, add_zero, add_zero]

end Upper

/-! ## The lower bound -/

section Lower

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- **Lower bound**: for the splitting `E E 1_{n-4} ≅ P ⊕ P⟨-2⟩` on which the dot is an
isomorphism `P → P⟨-2⟩⟨2⟩` (`exists_E2_dot`), if `A` is a direct summand of `F P` then the pairing
takes the value `1_A`. -/
theorem exists_pairing_eq_id {P : S.obj r ⟶ S.obj (r + 1 + 1)} (iP : P ⟶ S.E r ≫ S.E (r + 1))
    (p' : S.E r ≫ S.E (r + 1) ⟶ P⟦(-2 : ℤ)⟧)
    (hiso : IsIso (iP ≫ (shWhiskerLeft (S.E r) (S.dot (r + 1)) :
      S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(2 : ℤ)⟧) ≫ p'⟦(2 : ℤ)⟧'))
    {A : S.obj (r + 1) ⟶ S.obj (r + 1 + 1)} (g₀ : A ⟶ S.F r ≫ P) (h₀ : S.F r ≫ P ⟶ A)
    (hg : g₀ ≫ h₀ = 𝟙 A) : ∃ (g : A ⟶ S.FW r) (h : S.FW₂ r ⟶ A), g ≫ S.Φ₀ r ≫ h = 𝟙 A := by
  set Ψ := S.F r ◁ (iP ≫ (shWhiskerLeft (S.E r) (S.dot (r + 1)) :
    S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(2 : ℤ)⟧) ≫ p'⟦(2 : ℤ)⟧') with hΨ
  refine ⟨g₀ ≫ (S.F r ◁ iP), (S.F r ◁ (whiskerLeftShiftIso (S.E r) (S.E (r + 1)) 2).hom) ≫
    (S.F r ◁ p'⟦(2 : ℤ)⟧') ≫ inv Ψ ≫ h₀, ?_⟩
  have hx : iP ≫ (S.E r ◁ (S.dot (r + 1) : S.E (r + 1) ⟶ (S.E (r + 1))⟦(2 : ℤ)⟧)) ≫
      (whiskerLeftShiftIso (S.E r) (S.E (r + 1)) 2).hom ≫ p'⟦(2 : ℤ)⟧' =
      iP ≫ (shWhiskerLeft (S.E r) (S.dot (r + 1)) :
        S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(2 : ℤ)⟧) ≫ p'⟦(2 : ℤ)⟧' := by
    rw [shWhiskerLeft_eq]
    simp only [Category.assoc]
  calc (g₀ ≫ (S.F r ◁ iP)) ≫ S.Φ₀ r ≫ (S.F r ◁ (whiskerLeftShiftIso (S.E r) (S.E (r + 1)) 2).hom) ≫
        (S.F r ◁ p'⟦(2 : ℤ)⟧') ≫ inv Ψ ≫ h₀
      = g₀ ≫ (S.F r ◁ (iP ≫ (S.E r ◁ (S.dot (r + 1) : S.E (r + 1) ⟶ (S.E (r + 1))⟦(2 : ℤ)⟧)) ≫
          (whiskerLeftShiftIso (S.E r) (S.E (r + 1)) 2).hom ≫ p'⟦(2 : ℤ)⟧')) ≫ inv Ψ ≫ h₀ := by
        simp only [Φ₀, Bicategory.whiskerLeft_comp, Category.assoc]
    _ = g₀ ≫ Ψ ≫ inv Ψ ≫ h₀ := by rw [hx]
    _ = 𝟙 A := by rw [IsIso.hom_inv_id_assoc, hg]

end Lower

/-! ## Multiplicities: `A_i` is a direct summand of `F P` -/

section Mult

variable (hn : 0 ≤ S.wt (r + 1)) (hyp' : ∀ r', r + 1 < r' → S.NumAdj r')
  (h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1))))

include hn hyp' h2 in
/-- `E 1_{n-2}` is a brick, hence indecomposable (Lemma 3.1 at `n - 2`, under (3.2) at the
weights `≥ n`). -/
theorem isIndec_E : IsIndec (S.E (r + 1)) :=
  ((isBrick_iff k).2 (S.lem1_zero_of_numAdj hn hyp' le_rfl h2)).1

include hn hyp' h2 in
/-- `E 1_{n-2}⟨a⟩ ≇ E 1_{n-2}⟨b⟩` for `a ≠ b`. -/
theorem not_iso_E_shift {a b : ℤ} (hab : a ≠ b) :
    ¬ Nonempty ((S.E (r + 1))⟦a⟧ ≅ (S.E (r + 1))⟦b⟧) := by
  rintro ⟨φ⟩
  rcases lt_or_gt_of_ne hab with h | h
  · have h0 : φ.inv = 0 := hom_E_shift_eq_zero hyp' hn h φ.inv
    exact (isIndec_shift (isIndec_E hn hyp' h2) b).1
      ((IsZero.iff_id_eq_zero _).2 (by rw [← φ.inv_hom_id, h0, zero_comp]))
  · have h0 : φ.hom = 0 := hom_E_shift_eq_zero hyp' hn h φ.hom
    exact (isIndec_shift (isIndec_E hn hyp' h2) a).1
      ((IsZero.iff_id_eq_zero _).2 (by rw [← φ.hom_inv_id, h0, zero_comp]))

include hn hyp' h2 in
/-- `mult_{E⟨a⟩}(E⟨b⟩) = mult_E(E)` if `a = b` and `0` otherwise. -/
theorem mult_E_shift (a b : ℤ) :
    mult k (isIndec_shift (isIndec_E hn hyp' h2) a) ((S.E (r + 1))⟦b⟧) =
      if a = b then mult k (isIndec_E hn hyp' h2) (S.E (r + 1)) else 0 := by
  split_ifs with hab
  · subst hab
    exact mult_shift k _ a _
  · have := KrullSchmidtCat.multK_of_not_iso k (isIndec_shift (isIndec_E hn hyp' h2) a)
      (isIndec_shift (isIndec_E hn hyp' h2) b) (not_iso_E_shift hn hyp' h2 hab)
    rwa [KrullSchmidtCat.multK_of] at this

include hn hyp' h2 in
/-- The multiplicity of `E 1_{n-2}⟨a⟩` in `E E F 1_{n-2}`, for `a > -n + 1`, from the decomposition
`E E F 1_{n-2} ≅ E 1_{n-2} (E F 1_{n+2}) ⊕ ⊕_j A_j ⊕ ⊕_j B_j`. -/
theorem mult_FW_eq (e' : S.EFDecomp r) (e : S.EFDecomp (r + 1)) {a : ℤ}
    (ha : -S.wt (r + 1 + 1) + 1 < a) :
    mult k (isIndec_shift (isIndec_E hn hyp' h2) a) (S.FW r) =
      ∑ j ∈ Finset.range (S.wt (r + 1 + 1)).toNat,
        (if a = 1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) then
          mult k (isIndec_E hn hyp' h2) (S.E (r + 1)) else 0) +
      ∑ j ∈ Finset.range (S.wt (r + 1)).toNat,
        (if a = 1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) then
          mult k (isIndec_E hn hyp' h2) (S.E (r + 1)) else 0) := by
  have hw : S.wt (r + 1 + 1) = S.wt (r + 1) + 2 := S.wt_add_one _
  have hyp2 : ∀ r', r + 1 + 1 < r' → S.NumAdj r' := fun r' h => hyp' r' (by omega)
  have Ψ : S.FW r ≅ (S.Csum r ⊞ bsum (S.Asum r) (S.wt (r + 1 + 1)).toNat) ⊞
      bsum (S.Bsum r) (S.wt (r + 1)).toNat :=
    (α_ _ _ _).symm ≪≫ whiskerRightIso e' _ ≪≫ whiskerRightBiprodIso _ _ _ ≪≫
      biprod.mapIso (α_ _ _ _ ≪≫ whiskerLeftIso _ e ≪≫ whiskerLeftBiprodIso _ _ _ ≪≫
        biprod.mapIso (Iso.refl _) (whiskerLeftBsumIso _ _ _)) (whiskerRightBsumIso _ _ _)
  rw [KrullSchmidtCat.mult_iso k _ Ψ, KrullSchmidtCat.mult_biprod, KrullSchmidtCat.mult_biprod,
    mult_bsum, mult_bsum, mult_eq_zero_of_finrank_eq_zero k _
      (S.finrank_E_shift_C_eq_zero (by omega) hyp2 ha), zero_add]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [KrullSchmidtCat.mult_iso k _ (S.AsumIso r j), mult_E_shift hn hyp' h2]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [KrullSchmidtCat.mult_iso k _ (S.BsumIso r j), mult_E_shift hn hyp' h2]

include hn hyp' h2 in
/-- **`E 1_{n-2}⟨a_i⟩` occurs in `F P`** (`P = E^{(2)} 1_{n-4}⟨1⟩`) with multiplicity `mult_E(E)`,
for `i ≤ n - 2`: from `m(a) + m(a+2) = mult_{E⟨a⟩}(E E F 1_{n-2})`, descending from `a = n + 1`. -/
theorem mult_FP_eq (e' : S.EFDecomp r) (e : S.EFDecomp (r + 1))
    {P : S.obj r ⟶ S.obj (r + 1 + 1)} (iP : P ⟶ S.E r ≫ S.E (r + 1)) (p : S.E r ≫ S.E (r + 1) ⟶ P)
    (i' : P⟦(-2 : ℤ)⟧ ⟶ S.E r ≫ S.E (r + 1)) (p' : S.E r ≫ S.E (r + 1) ⟶ P⟦(-2 : ℤ)⟧)
    (h1 : iP ≫ p = 𝟙 P) (h2' : i' ≫ p' = 𝟙 _) (h3 : iP ≫ p' = 0) (h4 : i' ≫ p = 0)
    (h5 : p ≫ iP + p' ≫ i' = 𝟙 _) :
    ∀ i : ℕ, i + 1 < (S.wt (r + 1 + 1)).toNat →
      mult k (isIndec_shift (isIndec_E hn hyp' h2)
        (1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (i : ℤ)))) (S.F r ≫ P) =
      mult k (isIndec_E hn hyp' h2) (S.E (r + 1)) := by
  have hw : S.wt (r + 1 + 1) = S.wt (r + 1) + 2 := S.wt_add_one _
  have hN : (((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) = S.wt (r + 1 + 1) := Int.toNat_of_nonneg (by omega)
  have hN' : (((S.wt (r + 1)).toNat : ℕ) : ℤ) = S.wt (r + 1) := Int.toNat_of_nonneg hn
  set hE := isIndec_E hn hyp' h2 with hhE
  set d := mult k hE (S.E (r + 1)) with hd
  -- `m(a) := mult_{E⟨a⟩}(F P)`
  let m : ℤ → ℤ := fun a => mult k (isIndec_shift hE a) (S.F r ≫ P)
  have m_congr : ∀ {a b : ℤ}, a = b → m a = m b := fun h => by subst h; rfl
  have m_nonneg : ∀ a, 0 ≤ m a := fun a => mult_nonneg k _ _
  -- `mult_{E⟨a⟩}(E E F 1_{n-2}) = m(a) + m(a + 2)`
  have hsum : ∀ a : ℤ, mult k (isIndec_shift hE a) (S.FW r) = m a + m (a + 2) := by
    intro a
    have iso1 : S.FW r ≅ (S.F r ≫ P) ⊞ (S.F r ≫ P⟦(-2 : ℤ)⟧) :=
      whiskerLeftIso (S.F r) (KrullSchmidtCat.isoOfData iP p i' p' h1 h2' h3 h4 h5) ≪≫
        whiskerLeftBiprodIso _ _ _
    rw [KrullSchmidtCat.mult_iso k _ iso1, KrullSchmidtCat.mult_biprod]
    congr 1
    have s1 : ((S.F r ≫ P)⟦(-2 : ℤ)⟧)⟦(2 : ℤ)⟧ ≅ S.F r ≫ P :=
      (shiftFunctorCompIsoId _ (-2 : ℤ) 2 (by norm_num)).app _
    rw [KrullSchmidtCat.mult_iso k _ (whiskerLeftShiftIso (S.F r) P (-2)),
      ← mult_shift k (isIndec_shift hE a) 2, KrullSchmidtCat.mult_iso k _ s1,
      mult_congr_left k _ (isIndec_shift hE (a + 2))
        ((shiftFunctorAdd' _ a 2 (a + 2) rfl).app (S.E (r + 1))).symm]
  -- evaluation of the sums in `mult_FW_eq`
  have hFW : ∀ a : ℤ, -S.wt (r + 1 + 1) + 1 < a →
      mult k (isIndec_shift hE a) (S.FW r) =
        ∑ j ∈ Finset.range (S.wt (r + 1 + 1)).toNat,
          (if a = 1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) then d else 0) +
        ∑ j ∈ Finset.range (S.wt (r + 1)).toNat,
          (if a = 1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) then d else 0) :=
    fun a ha => mult_FW_eq hn hyp' h2 e' e ha
  have hS1 : ∀ i : ℕ, i < (S.wt (r + 1 + 1)).toNat →
      ∑ j ∈ Finset.range (S.wt (r + 1 + 1)).toNat,
        (if 1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (i : ℤ)) =
          1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) then d else 0) = d := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl]
    · intro j _ hji
      rw [ite_eq_right]
      intro h
      exact hji (by omega)
    · intro h
      exact absurd (Finset.mem_range.2 hi) h
  have hS1' : ∑ j ∈ Finset.range (S.wt (r + 1 + 1)).toNat,
      (if 1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) + 2 =
        1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) then d else 0) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]
    push_cast
    omega
  have hS2 : ∀ i : ℕ, i + 2 < (S.wt (r + 1 + 1)).toNat →
      ∑ j ∈ Finset.range (S.wt (r + 1)).toNat,
        (if 1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((i + 1 : ℕ) : ℤ)) =
          1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) then d else 0) = d := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left (by push_cast; omega)]
    · intro j _ hji
      rw [ite_eq_right]
      intro h
      exact hji (by push_cast at h; omega)
    · intro h
      rw [Finset.mem_range] at h
      omega
  have hS2₀ : ∀ a : ℤ, 1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1) ≤ a →
      ∑ j ∈ Finset.range (S.wt (r + 1)).toNat,
        (if a = 1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) then d else 0) = 0 := by
    intro a ha
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]
    omega
  -- the recursion
  intro i
  induction i with
  | zero =>
    intro hi
    have e0 := hsum (1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)))
    rw [hFW _ (by push_cast; omega), hS1 0 (by omega), hS2₀ _ (by push_cast; omega), add_zero] at e0
    have e1 := hsum (1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) + 2)
    rw [hFW _ (by push_cast; omega), hS1', hS2₀ _ (by push_cast; omega), add_zero] at e1
    have := m_nonneg (1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) + 2)
    have := m_nonneg (1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) + 2 + 2)
    change m _ = d
    omega
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have e0 := hsum (1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((i + 1 : ℕ) : ℤ)))
    rw [hFW _ (by push_cast; omega), hS1 (i + 1) (by omega), hS2 i (by omega)] at e0
    have hc : m (1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((i + 1 : ℕ) : ℤ)) + 2) =
        m (1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (i : ℤ))) :=
      m_congr (by push_cast; ring)
    change m _ = d at ih' ⊢
    omega

end Mult

/-! ## Lemma 3.6 -/

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- An endomorphism of `1_n⟨a⟩` (through the identification `1_n⟨a-2⟩⟨2⟩ ≅ 1_n⟨a⟩`) which is nonzero
is an isomorphism, since `End(1_n) = k`. -/
theorem isIso_entry_of_ne_zero (h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) {i : ℕ}
    (f : S.oneShift (r + 1) i ⟶ (S.oneShift (r + 1) (i + 1))⟦(2 : ℤ)⟧) (hf : f ≠ 0) : IsIso f := by
  have e₂ : S.oneShift (r + 1) i ≅ (S.oneShift (r + 1) (i + 1))⟦(2 : ℤ)⟧ :=
    (shiftFunctorAdd' _ (1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((i + 1 : ℕ) : ℤ)))
      2 (1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (i : ℤ))) (by push_cast; ring)).app _
  have hne : (𝟙 (S.oneShift (r + 1) i) : _ ⟶ _) ≠ 0 := fun h0 => by
    have hz : IsZero (S.oneShift (r + 1) i) := (IsZero.iff_id_eq_zero _).2 h0
    exact h2 (((shiftFunctor _ (-(1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (i : ℤ))))).map_isZero
      hz).of_iso ((shiftFunctorCompIsoId _ _ _ (by ring)).app _).symm)
  have h1 : finrank k (S.oneShift (r + 1) i ⟶ S.oneShift (r + 1) i) = 1 := by
    rw [oneShift, finrank_hom_shift]
    exact S.hom_zero _ h2
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 h1 (f ≫ e₂.inv)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hf (by rw [← Category.comp_id f, ← e₂.inv_hom_id, ← Category.assoc, ← hc, zero_comp])
  have : f = (c • 𝟙 _) ≫ e₂.hom := by rw [hc, Category.assoc, e₂.inv_hom_id, Category.comp_id]
  rw [this]
  have : IsIso (c • 𝟙 (S.oneShift (r + 1) i)) :=
    ⟨⟨c⁻¹ • 𝟙 _, by simp [smul_smul, hc0], by simp [smul_smul, hc0]⟩⟩
  infer_instance

/-- **CL Lemma 3.6** (`lem:Xind`) from the numerical shadow of (3.2): at a weight
`n = wt (r + 1 + 1)` with `1_n ≠ 0`, `n - 2 ≥ 0`, assuming the numerical shadow `NumAdj` of (3.2)
at all weights `≥ n`, every decomposition datum `e` of `E F 1_n` has nondegenerate subdiagonal:
`DotNondeg e`, i.e. the dot on `E F 1_n` "induces an isomorphism on `n - 1` summands
`1_n⟨k⟩`". The hypothesis at the weight `n` itself enters only through two dimension counts:
Lemma 3.1 at `n - 2` (`hom_E_shift_eq_zero`, `isIndec_E`) and
`Hom(E E F 1_{n+2}⟨2⟩, E 1_{n-2}⟨a⟩) = 0` for `a < n + 1` (`finrank_C₂_E_shift_eq_zero`). -/
theorem lemXind_of_numAdj [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hn : 0 ≤ S.wt (r + 1))
    (hyp' : ∀ r', r + 1 < r' → S.NumAdj r') (h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1))))
    (e : S.EFDecomp (r + 1)) : DotNondeg e := by
  intro i hi
  by_contra hno
  have h0 : entry e i (i + 1) = 0 := by
    by_contra hne
    exact hno (isIso_entry_of_ne_zero h2 _ hne)
  obtain ⟨e'⟩ := S.exists_EFDecomp (r := r) hn
  obtain ⟨P, iP, p, i', p', h1, h2', h3, h4, h5, hiso⟩ := S.exists_E2_dot r
  have hm := mult_FP_eq hn hyp' h2 e' e iP p i' p' h1 h2' h3 h4 h5 i hi
  have hd : 0 < mult k (isIndec_E hn hyp' h2) (S.E (r + 1)) := by
    have := KrullSchmidtCat.multK_self_pos k (isIndec_E hn hyp' h2)
    rwa [KrullSchmidtCat.multK_of] at this
  obtain ⟨f, g', hfg⟩ := exists_retract_of_mult_pos k _ (by rw [hm]; exact hd)
  obtain ⟨g, h, hgh⟩ := S.exists_pairing_eq_id iP p' hiso ((S.AsumIso r i).hom ≫ f)
    (g' ≫ (S.AsumIso r i).inv)
    (by rw [Category.assoc, ← Category.assoc f, hfg, Category.id_comp, Iso.hom_inv_id])
  have hz := pairing_eq_zero_of_entry_eq_zero e' e hn (fun r' h => hyp' r' (by omega))
    (hyp' _ (by omega)) hi h0 g h
  rw [hgh] at hz
  have hzA : IsZero (S.Asum r i) := (IsZero.iff_id_eq_zero _).2 hz
  exact (isIndec_E hn hyp' h2).1 (((shiftFunctor _
    (-(1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (i : ℤ))))).map_isZero
      (hzA.of_iso (S.AsumIso r i).symm)).of_iso
      ((shiftFunctorCompIsoId _ _ _ (by ring)).app _).symm)

/-- **CL Lemma 3.6** (`lem:Xind`) given the adjoint induction hypothesis at `n` (Proposition 3.9
at `n`): at a weight `n = wt (r + 1 + 1)` with `1_n ≠ 0`, `n - 2 ≥ 0`, assuming (3.2) for all
weights `≥ n`, every decomposition datum `e` of `E F 1_n` has nondegenerate subdiagonal:
`DotNondeg e`. -/
theorem lemXind_of_adjHyp [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hn : 0 ≤ S.wt (r + 1))
    (hyp : ∀ r', r + 1 + 1 < r' → S.AdjHyp r')
    (hA : S.AdjHyp (r + 1 + 1)) (h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) (e : S.EFDecomp (r + 1)) :
    DotNondeg e :=
  lemXind_of_numAdj hn (fun r' hr' => by
    rcases lt_or_eq_of_le (show r + 1 + 1 ≤ r' by omega) with h' | h'
    · exact (hyp r' h').numAdj
    · rw [← h']; exact hA.numAdj) h2 e

/-- **Corollary 3.7** (`cor:degz-bubbles`) given the adjoint induction hypothesis at `n`: at a
weight `n = wt (r + 1 + 1) ≥ 2` with `1_n ≠ 0`, under (3.2) for all weights `≥ n`, the degree-zero
bubble with `n - 1` dots (`DotEntries.bubble`) is an isomorphism, i.e. a nonzero multiple of the
identity of `1_n`. -/
theorem cor_degz_bubbles_of_adjHyp [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
    (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 + 1 < r' → S.AdjHyp r')
    (hA : S.AdjHyp (r + 1 + 1)) (h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) (e : S.EFDecomp (r + 1)) :
    IsIso (bubble e) :=
  cor_degz_bubbles_of_dotNondeg e (by rw [S.wt_add_one]; omega) hyp
    (lemXind_of_adjHyp hn hyp hA h2 e)

end Categorification.TwoRep.StrongSl2
