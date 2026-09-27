/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.UpDownCrossing
import Categorification.TwoRep.AdjointInductionNegCor

/-!
# The bottom half (`n ≤ 0`): the dot on `F E 1_n`, Lemma 3.6 as a statement, Corollary 3.7 and
Corollary 3.13

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Lemma 3.6 (`lem:Xind`, the case `n < -1`: "`F E 1_n → F E 1_n ⟨2⟩` [the dot on
the upward strand] induces an isomorphism on `-n-1` summands `1_n⟨k⟩`"), Corollary 3.7
(`cor:degz-bubbles`, `n < 0`) and Corollary 3.13 (`cor:1`, eq. `eq:iso2`, `n ≤ 0`), all "proved in
the same way" as for `n ≥ 0` (Remark 3.11).

This file is the mirror of `DotEntries.lean` and of the `ζ` part of `UpDownCrossing.lean`: fix
`n = wt (r + 1) ≤ 0`, `F E 1_n = E (r + 1) ≫ F (r + 1)`, `E F 1_n = F r ≫ E r`, and the mirror
decomposition `F E 1_n ≅ E F 1_n ⊕ ⊕_{j<-n} 1_n⟨-n-1-2j⟩` (condition (3), `FEDecomp`). The dot is
on the strand `E 1_n` of `F E 1_n` (`dotFE = dot ▷ F`, the mirror of `dotEF = F ◁ dot`).

**What mirrors literally.** The summand combinatorics is identical: the summands are
`1_n⟨N-1-2j⟩` with `N = -n` (`oneShiftNeg`), the entries of the dot have degree `2(i-j+1)`
(`entryN_eq_zero`), CL's cup `1_n → F E 1_n ⟨n+1⟩` (the map `Ucupr` of Remark 3.11, "defined using
the decomposition of `F E 1_n`") is `ιN e 0`, CL's cap `F E 1_n → 1_n ⟨n+1⟩` is `πN e (N-1)`,
the content of Lemma 3.6 is `DotNondegNeg e` (the `-n-1` subdiagonal scalars are nonzero), and
Corollary 3.7 (`cor_degz_bubbles_neg_of_dotNondeg`) and Corollary 3.13
(`isIso_zetaNeg_of_dotNondeg`) follow from it by the same triangularity argument.

**What does not mirror.**

* The vanishing of the component of `cup ≫ dot^m` in the complement `E F 1_n` (the mirror of
  `cupDots_comp_πFE`) is `Hom(1_n⟨-n-1-2m⟩, E 1_{n-2} F 1_n) = 0` for `m < -n`. In the top half the
  corresponding space was computed with the *defining* right adjoint of `E`; here the factor to be
  moved is `E 1_{n-2}` on the right, which needs `(E 1_{n-2})_L`, i.e. **the adjoint induction
  hypothesis (3.2) at `n - 2`** (available in the bottom-half induction, which assumes (3.2) at the
  weights `< n`), together with Lemma 3.1 at `n - 2` (`lem1Neg_neg`). So Corollaries 3.7 and 3.13
  (given Lemma 3.6) need (3.2) at `n - 2`, whereas their top-half versions needed only (3.2) above
  `n`.
* The case `n = 0`: `F E 1_0 ≅ E F 1_0` has no summand `1_0⟨k⟩`, `DotNondegNeg` is vacuous, the
  bubble does not exist (CL state Corollary 3.7 for `n ≠ 0`), and `ζ` is the map `E F 1_0 → F E 1_0`
  alone (the inclusion `ιEF e`, an isomorphism); the statements below cover this with `N = 0`.
* **Lemma 3.6 itself (`DotNondegNeg e` from the induction hypotheses) is not proved here**: CL's
  argument for `n < -1` is *not* the mirror of the one for `n > 1` within Definition 1.2. The
  top-half proof (`LemXind.lean`) uses that the dot on `E E 1_{n-4}` is an isomorphism on the common
  summand `E^{(2)}⟨1⟩` (the nilHecke action on `E`-strands) and whiskers `E F 1_n` by `E 1_{n-2}`,
  where the complement summand `F E 1_n ⊆ E F 1_n` is invisible to the summands `E 1_{n-2}⟨a⟩` by
  degree. Mirrored, one needs the dot on `F E 1_n` restricted to the summand `E F 1_n ⊆ F E 1_n` (no
  longer invisible: `Hom(E 1_{n-2}⟨a⟩, E F E 1_{n-2}) ≠ 0`), or — CL's implicit route — the
  nilHecke action on `F F` (dots and crossings on downward strands, "`F F 1_{n+4} ≅ F^{(2)}⟨1⟩ ⊕
  F^{(2)}⟨-1⟩` with the dot an isomorphism on the common summand"), which is not part of
  Definition 1.2 and would have to be constructed as the mate of the action on `E E` and shown to
  satisfy the nilHecke relations. See the report accompanying this file.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  (S : StrongSl2 k B)

/-! ## Decomposition data (bottom half) -/

/-- The `j`-th summand `1_n⟨-n-1-2j⟩` of `⊕_{[-n]} 1_n` (`n = wt (r + 1) ≤ 0`), in the normal form
of `qsum` with `N = -n`. -/
def oneShiftNeg (r : ℤ) (j : ℕ) : S.obj (r + 1) ⟶ S.obj (r + 1) :=
  (𝟙 (S.obj (r + 1)))⟦1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ))⟧

/-- **A decomposition datum** of `F E 1_n` for `n ≤ 0`: an isomorphism
`F E 1_n ≅ E F 1_n ⊕ ⊕_{j<-n} 1_n⟨-n-1-2j⟩` (condition (3) of Definition 1.2 at the weight `n ≤ 0`). -/
abbrev FEDecomp (r : ℤ) :=
  S.E (r + 1) ≫ S.F (r + 1) ≅ (S.F r ≫ S.E r) ⊞ bsum (S.oneShiftNeg r) (-S.wt (r + 1)).toNat

omit [GradedBicategory.IsLinear B k] in
theorem exists_FEDecomp {r : ℤ} (hn : S.wt (r + 1) ≤ 0) : Nonempty (S.FEDecomp r) := by
  obtain ⟨e⟩ := S.FE r hn
  exact ⟨e ≪≫ biprod.mapIso (Iso.refl _) (bsumIsoQsum 1 (-S.wt (r + 1)).toNat _).symm⟩

variable {S} {r : ℤ} (e : S.FEDecomp r)

/-- The inclusion of the summand `1_n⟨-n-1-2j⟩` into `F E 1_n`. -/
def ιN (j : ℕ) : S.oneShiftNeg r j ⟶ S.E (r + 1) ≫ S.F (r + 1) :=
  bsumι (S.oneShiftNeg r) (-S.wt (r + 1)).toNat j ≫ biprod.inr ≫ e.inv

/-- The projection of `F E 1_n` onto the summand `1_n⟨-n-1-2j⟩`. -/
def πN (j : ℕ) : S.E (r + 1) ≫ S.F (r + 1) ⟶ S.oneShiftNeg r j :=
  e.hom ≫ biprod.snd ≫ bsumπ (S.oneShiftNeg r) (-S.wt (r + 1)).toNat j

/-- The inclusion of the summand `E F 1_n` into `F E 1_n` (CL's up-down crossing for `n ≤ 0`). -/
def ιEF : S.F r ≫ S.E r ⟶ S.E (r + 1) ≫ S.F (r + 1) := biprod.inl ≫ e.inv

/-- The projection of `F E 1_n` onto the summand `E F 1_n`. -/
def πEF : S.E (r + 1) ≫ S.F (r + 1) ⟶ S.F r ≫ S.E r := e.hom ≫ biprod.fst

omit [GradedBicategory.IsLinear B k] in
theorem ιN_πN_self {j : ℕ} (hj : j < (-S.wt (r + 1)).toNat) : ιN e j ≫ πN e j = 𝟙 _ := by
  simp only [ιN, πN, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd_assoc]
  exact bsumι_π_self _ _ _ hj

omit [GradedBicategory.IsLinear B k] in
theorem ιN_πN_ne {j j' : ℕ} (hj : j ≠ j') : ιN e j ≫ πN e j' = 0 := by
  simp only [ιN, πN, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd_assoc]
  exact bsumι_π_ne _ _ _ _ hj

omit [GradedBicategory.IsLinear B k] in
/-- The decomposition of the identity of `F E 1_n`. -/
theorem totalN :
    ∑ j ∈ Finset.range (-S.wt (r + 1)).toNat, πN e j ≫ ιN e j + πEF e ≫ ιEF e = 𝟙 _ := by
  have h1 : ∀ j ∈ Finset.range (-S.wt (r + 1)).toNat, πN e j ≫ ιN e j =
      e.hom ≫ (biprod.snd ≫ (bsumπ (S.oneShiftNeg r) _ j ≫ bsumι (S.oneShiftNeg r) _ j) ≫
        biprod.inr) ≫ e.inv := by
    intro j _
    simp only [πN, ιN, Category.assoc]
  rw [Finset.sum_congr rfl h1, ← Preadditive.comp_sum, ← Preadditive.sum_comp,
    ← Preadditive.comp_sum, ← Preadditive.sum_comp, bsum_total, Category.id_comp]
  have h2 : e.hom ≫ (biprod.snd ≫ biprod.inr + biprod.fst ≫ biprod.inl) ≫ e.inv = 𝟙 _ := by
    rw [add_comm (biprod.snd ≫ biprod.inr), biprod.total, Category.id_comp, Iso.hom_inv_id]
  rw [← h2]
  simp only [πEF, ιEF, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

/-! ## The dot on `F E 1_n` and its matrix entries -/

variable (S) in
/-- **The dot on `F E 1_n`**: the dot on the strand `E 1_n` (Mathlib: `dot r+1 ▷ F (r + 1)`), a map
`F E 1_n → F E 1_n ⟨2⟩` (CL's `sUdown sUupdot`). -/
def dotFE (r : ℤ) : S.E (r + 1) ≫ S.F (r + 1) ⟶ (S.E (r + 1) ≫ S.F (r + 1))⟦(2 : ℤ)⟧ :=
  shWhiskerRight (S.dot (r + 1)) (S.F (r + 1))

/-- The `(i, j)` matrix entry of the dot, of degree `2(i - j + 1)`. -/
def entryN (i j : ℕ) : S.oneShiftNeg r i ⟶ (S.oneShiftNeg r j)⟦(2 : ℤ)⟧ :=
  ιN e i ≫ S.dotFE r ≫ (πN e j)⟦(2 : ℤ)⟧'

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- Degree vanishing: a map `1_n⟨-n-1-2i⟩ → 1_n⟨-n-1-2j⟩⟨d⟩` of negative degree is zero. -/
theorem hom_oneShiftNeg_eq_zero (i j : ℕ) {d : ℤ} (hd : d + 2 * (i : ℤ) - 2 * (j : ℤ) < 0)
    (f : S.oneShiftNeg r i ⟶ (S.oneShiftNeg r j)⟦d⟧) : f = 0 := by
  have s1 : (S.oneShiftNeg r j)⟦d⟧ ≅
      (𝟙 (S.obj (r + 1)))⟦1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) + d⟧ :=
    ((shiftFunctorAdd' _ _ d _ rfl).app (𝟙 (S.obj (r + 1)))).symm
  have h0 : finrank k (S.oneShiftNeg r i ⟶ (S.oneShiftNeg r j)⟦d⟧) = 0 := by
    rw [finrank_hom_congr_right k _ s1, oneShiftNeg,
      finrank_hom_shift_shift k _ _ (c := d + 2 * (i : ℤ) - 2 * (j : ℤ)) (by ring)]
    exact S.hom_neg _ _ hd
  haveI := Module.finrank_zero_iff.1 h0
  exact Subsingleton.elim _ _

/-- The entries above the subdiagonal vanish. -/
theorem entryN_eq_zero {i j : ℕ} (h : i + 1 < j) : entryN e i j = 0 :=
  hom_oneShiftNeg_eq_zero i j (by omega) _

/-- **The content of CL Lemma 3.6 for `n < -1`** ("`rk_{1_n}(dot) = -n-1`"): the `-n-1`
subdiagonal entries of the dot on `F E 1_n` are isomorphisms. Not proved here (see the module
docstring). -/
def DotNondegNeg : Prop := ∀ i : ℕ, i + 1 < (-S.wt (r + 1)).toNat → IsIso (entryN e i (i + 1))

/-! ## Corollary 3.7 for `n < 0` -/

/-- `cup ≫ dot^m : 1_n⟨-n-1⟩ → F E 1_n ⟨2m⟩`. -/
def cupDotsN (m : ℕ) : S.oneShiftNeg r 0 ⟶ (S.E (r + 1) ≫ S.F (r + 1))⟦(m : ℤ) * 2⟧ :=
  ιN e 0 ≫ (shPow (S.dotFE r : ShiftedHom (S.E (r + 1) ≫ S.F (r + 1))
    (S.E (r + 1) ≫ S.F (r + 1)) (2 : ℤ)) m :
    S.E (r + 1) ≫ S.F (r + 1) ⟶ (S.E (r + 1) ≫ S.F (r + 1))⟦(m : ℤ) * 2⟧)

/-- **CL's degree-zero counterclockwise bubble** with `-n-1` dots at the weight `n < 0`: `cup`,
then `-n-1` dots, then `cap`, as a map `1_n⟨-n-1⟩ → 1_n⟨n+1⟩⟨2(-n-1)⟩`. -/
def bubbleN : S.oneShiftNeg r 0 ⟶
    (S.oneShiftNeg r ((-S.wt (r + 1)).toNat - 1))⟦(((-S.wt (r + 1)).toNat - 1 : ℕ) : ℤ) * 2⟧ :=
  cupDotsN e _ ≫ (πN e _)⟦_⟧'

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cupDotsN_zero_comp (j : ℕ) :
    cupDotsN e 0 ≫ (πN e j)⟦((0 : ℕ) : ℤ) * 2⟧' =
      (ιN e 0 ≫ πN e j) ≫ (shiftFunctorZero' _ (((0 : ℕ) : ℤ) * 2) (by simp)).inv.app _ := by
  simp only [cupDotsN, shPow, ShiftedHom.mk₀, Category.id_comp, Category.assoc]
  have := (shiftFunctorZero' _ (((0 : ℕ) : ℤ) * 2) (by simp)).inv.naturality (πN e j)
  simp only [Functor.id_map] at this
  rw [← this]
  try rfl

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cupDotsN_succ_comp (m j : ℕ) :
    cupDotsN e (m + 1) ≫ (πN e j)⟦((m + 1 : ℕ) : ℤ) * 2⟧' =
      (cupDotsN e m ≫ (S.dotFE r ≫ (πN e j)⟦(2 : ℤ)⟧')⟦(m : ℤ) * 2⟧') ≫
        (shiftFunctorAdd' _ 2 ((m : ℤ) * 2) (((m + 1 : ℕ) : ℤ) * 2) (by push_cast; ring)).inv.app _ := by
  simp only [cupDotsN, shPow, ShiftedHom.comp, Category.assoc, Functor.map_comp]
  rw [← (shiftFunctorAdd' _ 2 ((m : ℤ) * 2) (((m + 1 : ℕ) : ℤ) * 2)
    (by push_cast; ring)).inv.naturality (πN e j)]
  try rfl

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem dotFE_comp_πN (j : ℕ) :
    S.dotFE r ≫ (πN e j)⟦(2 : ℤ)⟧' =
      ∑ j' ∈ Finset.range (-S.wt (r + 1)).toNat, πN e j' ≫ entryN e j' j +
        πEF e ≫ (ιEF e ≫ S.dotFE r ≫ (πN e j)⟦(2 : ℤ)⟧') := by
  conv_lhs => rw [← Category.id_comp (S.dotFE r), ← totalN e]
  simp only [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc, entryN]

/-- **The vanishing of the `E F 1_n`-component** of `cup ≫ dot^m` for `m < -n`:
`Hom(1_n⟨-n-1-2m⟩, E 1_{n-2} F 1_n) = 0`. This uses `(E 1_{n-2})_L`, i.e. the adjoint induction
hypothesis (3.2) at the weight `n - 2` (`hyp`), and Lemma 3.1 at `n - 2`. -/
theorem cupDotsN_comp_πEF (hn : S.wt (r + 1) ≤ 0) (hyp : ∀ r', r' < r + 1 → S.AdjHyp r') {m : ℕ}
    (hm : m < (-S.wt (r + 1)).toNat) : cupDotsN e m ≫ (πEF e)⟦(m : ℤ) * 2⟧' = 0 := by
  have hN : (((-S.wt (r + 1)).toNat : ℕ) : ℤ) = -S.wt (r + 1) := Int.toNat_of_nonneg (by omega)
  have hw : S.wt (r + 1) = S.wt r + 2 := S.wt_add_one r
  have h0 : finrank k (S.oneShiftNeg r 0 ⟶ (S.F r ≫ S.E r)⟦(m : ℤ) * 2⟧) = 0 := by
    rw [oneShiftNeg, finrank_hom_shift_shift k _ _
        (c := (m : ℤ) * 2 - 1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)))
        (by ring),
      finrank_hom_shift_right k _ _
        (b := 1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) - (m : ℤ) * 2)
        (by ring),
      ← ((hyp r (by omega)).dimAdj S).left,
      finrank_hom_congr_left k (idShiftCompShiftIso (S.F r) (s := -(S.wt r + 1) +
        (1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) - (m : ℤ) * 2)) rfl),
      finrank_hom_shift_left k _ _ (b := -(-(S.wt r + 1) +
        (1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) - (m : ℤ) * 2))) (by ring),
      S.finrank_F_F_eq]
    refine S.lem1Neg_neg (r₁ := r + 1) hn hyp r (by omega) _ ?_
    push_cast
    omega
  haveI := Module.finrank_zero_iff.1 h0
  exact Subsingleton.elim _ _

/-- The induction behind Corollary 3.7 (bottom half). -/
theorem bubbleN_aux (hn : S.wt (r + 1) ≤ 0) (hyp : ∀ r', r' < r + 1 → S.AdjHyp r')
    (hd : DotNondegNeg e) : ∀ m : ℕ, m < (-S.wt (r + 1)).toNat →
      (∀ j : ℕ, m < j → cupDotsN e m ≫ (πN e j)⟦(m : ℤ) * 2⟧' = 0) ∧
        IsIso (cupDotsN e m ≫ (πN e m)⟦(m : ℤ) * 2⟧') := by
  intro m
  induction m with
  | zero =>
    intro hm
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [cupDotsN_zero_comp, ιN_πN_ne e (by omega), zero_comp]
    · rw [cupDotsN_zero_comp, ιN_πN_self e hm, Category.id_comp]
      infer_instance
  | succ m ih =>
    intro hm
    obtain ⟨iha, ihb⟩ := ih (by omega)
    have key : ∀ j : ℕ, cupDotsN e (m + 1) ≫ (πN e j)⟦((m + 1 : ℕ) : ℤ) * 2⟧' =
        (∑ j' ∈ Finset.range (-S.wt (r + 1)).toNat,
          (cupDotsN e m ≫ (πN e j')⟦(m : ℤ) * 2⟧') ≫ (entryN e j' j)⟦(m : ℤ) * 2⟧') ≫
          (shiftFunctorAdd' _ 2 ((m : ℤ) * 2) (((m + 1 : ℕ) : ℤ) * 2)
            (by push_cast; ring)).inv.app _ := by
      intro j
      rw [cupDotsN_succ_comp, dotFE_comp_πN, Functor.map_add, Functor.map_sum,
        Preadditive.comp_add, Preadditive.comp_sum]
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc (cupDotsN e m) ((πEF e)⟦(m : ℤ) * 2⟧'),
        cupDotsN_comp_πEF e hn hyp (by omega), zero_comp, add_zero]
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [key, Finset.sum_eq_zero, zero_comp]
      intro j' _
      by_cases hj' : m < j'
      · rw [iha j' hj', zero_comp]
      · rw [entryN_eq_zero e (by omega), Functor.map_zero, comp_zero]
    · rw [key, Finset.sum_eq_single m]
      · haveI := hd m hm
        infer_instance
      · intro j' _ hj'
        rcases lt_or_gt_of_ne hj' with h | h
        · rw [entryN_eq_zero e (by omega), Functor.map_zero, comp_zero]
        · rw [iha j' h, zero_comp]
      · intro h
        rw [Finset.mem_range] at h
        omega

/-- **Corollary 3.7 for `n < 0`** (CL `cor:degz-bubbles`), conditionally on Lemma 3.6: at a weight
`n < 0`, assuming (3.2) for the weights `< n` and `DotNondegNeg e`, the degree-zero
counterclockwise bubble with `-n-1` dots is an isomorphism (a nonzero multiple of `1_{1_n}`). -/
theorem cor_degz_bubbles_neg_of_dotNondeg (hn : S.wt (r + 1) < 0)
    (hyp : ∀ r', r' < r + 1 → S.AdjHyp r') (hd : DotNondegNeg e) : IsIso (bubbleN e) :=
  (bubbleN_aux e hn.le hyp hd ((-S.wt (r + 1)).toNat - 1) (by omega)).2

/-! ## Corollary 3.13 for `n ≤ 0` (eq. `eq:iso2`) -/

/-- `1_n⟨-n-1-2k⟩ ≅ 1_n⟨-n-1⟩⟨-2k⟩`. -/
def oneShiftNegIso (k : ℕ) : S.oneShiftNeg r k ≅ (S.oneShiftNeg r 0)⟦-((k : ℤ) * 2)⟧ :=
  (shiftFunctorAdd' _ (1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)))
    (-((k : ℤ) * 2)) (1 * ((((-S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (k : ℤ)))
    (by push_cast; ring)).app _

/-- `k` dots on the cup, as a map `1_n⟨-n-1-2k⟩ → F E 1_n`. -/
def cupKN (k : ℕ) : S.oneShiftNeg r k ⟶ S.E (r + 1) ≫ S.F (r + 1) :=
  (oneShiftNegIso (S := S) (r := r) k).hom ≫ (cupDotsN e k)⟦-((k : ℤ) * 2)⟧' ≫
    (shiftFunctorCompIsoId _ ((k : ℤ) * 2) (-((k : ℤ) * 2)) (by ring)).hom.app _

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cupKN_comp (k : ℕ) {Y : S.obj (r + 1) ⟶ S.obj (r + 1)}
    (x : S.E (r + 1) ≫ S.F (r + 1) ⟶ Y) :
    cupKN e k ≫ x = (oneShiftNegIso (S := S) (r := r) k).hom ≫
      (cupDotsN e k ≫ x⟦(k : ℤ) * 2⟧')⟦-((k : ℤ) * 2)⟧' ≫
      (shiftFunctorCompIsoId _ ((k : ℤ) * 2) (-((k : ℤ) * 2)) (by ring)).hom.app Y := by
  simp only [cupKN, Category.assoc, Functor.map_comp]
  have := (shiftFunctorCompIsoId _ ((k : ℤ) * 2) (-((k : ℤ) * 2)) (by ring)).hom.naturality x
  simp only [Functor.id_map, Functor.comp_map] at this
  rw [← this]

/-- **CL's map `ζ` for `n ≤ 0`** (eq. `eq:iso2`): the up-down crossing `E F 1_n → F E 1_n`
(the inclusion `ιEF e`) together with `k dots ∘ cup : 1_n⟨-n-1-2k⟩ → F E 1_n`. -/
def zetaNeg : (S.F r ≫ S.E r) ⊞ bsum (S.oneShiftNeg r) (-S.wt (r + 1)).toNat ⟶
    S.E (r + 1) ≫ S.F (r + 1) :=
  biprod.desc (ιEF e) (bsumDesc (S.oneShiftNeg r) (cupKN e) _)

/-- **Corollary 3.13 for `n ≤ 0`** (CL `cor:1`, eq. `eq:iso2`), from Lemma 3.6: under (3.2) at the
weights `< n` and `DotNondegNeg e`, `ζ` is an isomorphism. (For `n = 0` this is the isomorphism
`ιEF e`.) -/
theorem isIso_zetaNeg_of_dotNondeg (hn : S.wt (r + 1) ≤ 0)
    (hyp : ∀ r', r' < r + 1 → S.AdjHyp r') (hd : DotNondegNeg e) : IsIso (zetaNeg e) := by
  have hent : ∀ j j' : ℕ, j < (-S.wt (r + 1)).toNat →
      bsumι (S.oneShiftNeg r) _ j ≫ (biprod.inr ≫ (zetaNeg e ≫ e.hom) ≫ biprod.snd) ≫
        bsumπ (S.oneShiftNeg r) _ j' = cupKN e j ≫ πN e j' := by
    intro j j' hj
    simp only [zetaNeg, Category.assoc, biprod.inr_desc_assoc]
    rw [← Category.assoc (bsumι _ _ j), bsumι_desc _ _ _ _ hj]
    rfl
  have hentEF : ∀ j : ℕ, j < (-S.wt (r + 1)).toNat →
      bsumι (S.oneShiftNeg r) _ j ≫ (biprod.inr ≫ (zetaNeg e ≫ e.hom) ≫ biprod.fst) =
        cupKN e j ≫ πEF e := by
    intro j hj
    simp only [zetaNeg, Category.assoc, biprod.inr_desc_assoc]
    rw [← Category.assoc (bsumι _ _ j), bsumι_desc _ _ _ _ hj]
    rfl
  have h1e : biprod.inl ≫ (zetaNeg e ≫ e.hom) ≫ biprod.fst = 𝟙 _ := by simp [zetaNeg, ιEF]
  haveI h1 : IsIso (biprod.inl ≫ (zetaNeg e ≫ e.hom) ≫ biprod.fst) := by rw [h1e]; infer_instance
  haveI h2 : IsIso (biprod.inr ≫ (zetaNeg e ≫ e.hom) ≫ biprod.snd) := by
    refine isIso_bsum_of_triangular _ _ _ _ ?_ ?_
    · intro j j' hjj' hj'
      rw [hent j j' (by omega), cupKN_comp, (bubbleN_aux e hn hyp hd j (by omega)).1 j' hjj',
        Functor.map_zero, zero_comp, comp_zero]
    · intro j hj
      rw [hent j j hj, cupKN_comp]
      haveI := (bubbleN_aux e hn hyp hd j hj).2
      infer_instance
  haveI : IsIso (zetaNeg e ≫ e.hom) := by
    refine isIso_biprod_of_blocks _ ?_
    apply bsum_hom_ext
    intro j hj
    rw [hentEF j hj, comp_zero, cupKN_comp, cupDotsN_comp_πEF e hn hyp hj, Functor.map_zero,
      zero_comp, comp_zero]
  have : zetaNeg e = (zetaNeg e ≫ e.hom) ≫ e.inv := by simp
  rw [this]
  infer_instance

end Categorification.TwoRep.StrongSl2
