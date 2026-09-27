/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BSum
import Categorification.TwoRep.Biadjoint

/-!
# The dot on `E F 1_n` in a decomposition `E F 1_n ≅ F E 1_n ⊕ ⊕_{[n]} 1_n`: Lemma 3.6 as a
statement, and Corollary 3.7

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3.3 Lemma 3.6 (`lem:Xind`) and §3.4 Corollary 3.7 (`cor:degz-bubbles`).

Fix `n = wt (r + 1) ≥ 0`, so `E F 1_n = F r ≫ E r` and `F E 1_n = E (r + 1) ≫ F (r + 1)`.

* `EFDecomp r`: a **decomposition datum**, an isomorphism `E F 1_n ≅ F E 1_n ⊕ ⊕_{j<n} 1_n⟨n-1-2j⟩`
  (condition (3), in the `bsum` form of `BSum.lean`; `exists_EFDecomp`). It gives the summand
  inclusions and projections `ι e j : 1_n⟨n-1-2j⟩ → E F 1_n`, `π e j`, `ιFE e`, `πFE e`
  (`ι_π_self`, `ι_π_ne`, `total`). CL's "cup" `1_n⟨n-1⟩ → E F 1_n` ("the inclusion of `1_n` into
  the lowest degree summand", §3.4) is `ι e 0`, and CL's "cap" `E F 1_n → 1_n⟨-n+1⟩` ("the
  projection out of the top degree summand") is `π e (n-1)`.
* `dotEF r : E F 1_n → E F 1_n ⟨2⟩`, the dot on the strand `E 1_{n-2}` (`F r ◁ dot r`), and its
  **matrix entries** `entry e i j : 1_n⟨n-1-2i⟩ → 1_n⟨n-1-2j⟩⟨2⟩` in the decomposition; the entry
  has degree `2(i - j + 1)`, so it vanishes for `j > i + 1` (`entry_eq_zero`), and for `j = i + 1`
  it is a degree-zero map between copies of `1_n`, i.e. a scalar.
* `DotNondeg e`: **the content of Lemma 3.6**: the `n - 1` subdiagonal scalars
  `entry e i (i + 1)`, `i = 0, …, n - 2`, are nonzero (isomorphisms). CL state Lemma 3.6 as
  "`rk_{1_n}(dot) = n - 1`"; by the degree analysis above (see the module docstring of
  `StepLemmas.lean` for the gap in CL's proof) the total `1_n`-rank of the dot is exactly the
  number of nonzero subdiagonal scalars, so this is CL's statement. It is proved from (3.2) at `n`
  in `Categorification.TwoRep.LemXind` (`lemXind_of_adjHyp`); everything below takes it as a
  hypothesis.
* `bubble e : 1_n⟨n-1⟩ → 1_n⟨-n+1⟩⟨2(n-1)⟩`, CL's degree-zero bubble with `n - 1` dots
  (`cup`, then `n - 1` dots, then `cap`), and **Corollary 3.7**
  (`cor_degz_bubbles_of_dotNondeg`): if `DotNondeg e` then the bubble is an isomorphism (a nonzero
  multiple of the identity). Proof: `cup ≫ dot^m` has zero component in the summands
  `1_n⟨n-1-2j⟩`, `j > m`, and an isomorphism as component in the `m`-th summand, by induction on
  `m` (`bubble_aux`): the component in `F E 1_n ⟨2m⟩` vanishes since
  `Hom(1_n⟨n-1-2m⟩, F E 1_n) = 0` for `m < n` (Lemma 3.1), and only the subdiagonal entries
  of the dot contribute to the next step, by degrees. This needs the adjoint induction
  hypothesis only at the weights `> n`.
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

/-! ## Decomposition data -/

/-- The `j`-th summand `1_n⟨n-1-2j⟩` of `⊕_{[n]} 1_n` (`n = wt (r + 1)`), in the normal form of
`qsum`. -/
def oneShift (r : ℤ) (j : ℕ) : S.obj (r + 1) ⟶ S.obj (r + 1) :=
  (𝟙 (S.obj (r + 1)))⟦1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ))⟧

/-- **A decomposition datum** of `E F 1_n`: an isomorphism `E F 1_n ≅ F E 1_n ⊕ ⊕_{j<n} 1_n⟨n-1-2j⟩`
(condition (3) of Definition 1.2 at the weight `n ≥ 0`, with a chosen isomorphism). -/
abbrev EFDecomp (r : ℤ) :=
  S.F r ≫ S.E r ≅ (S.E (r + 1) ≫ S.F (r + 1)) ⊞ bsum (S.oneShift r) (S.wt (r + 1)).toNat

omit [GradedBicategory.IsLinear B k] in
theorem exists_EFDecomp {r : ℤ} (hn : 0 ≤ S.wt (r + 1)) : Nonempty (S.EFDecomp r) := by
  obtain ⟨e⟩ := S.EF r (by rw [← wt]; exact hn)
  exact ⟨e ≪≫ biprod.mapIso (Iso.refl _) (bsumIsoQsum 1 (S.wt (r + 1)).toNat _).symm⟩

variable {S} {r : ℤ} (e : S.EFDecomp r)

/-- The inclusion of the summand `1_n⟨n-1-2j⟩` into `E F 1_n`. -/
def ι (j : ℕ) : S.oneShift r j ⟶ S.F r ≫ S.E r :=
  bsumι (S.oneShift r) (S.wt (r + 1)).toNat j ≫ biprod.inr ≫ e.inv

/-- The projection of `E F 1_n` onto the summand `1_n⟨n-1-2j⟩`. -/
def π (j : ℕ) : S.F r ≫ S.E r ⟶ S.oneShift r j :=
  e.hom ≫ biprod.snd ≫ bsumπ (S.oneShift r) (S.wt (r + 1)).toNat j

/-- The inclusion of the summand `F E 1_n` into `E F 1_n`. -/
def ιFE : S.E (r + 1) ≫ S.F (r + 1) ⟶ S.F r ≫ S.E r := biprod.inl ≫ e.inv

/-- The projection of `E F 1_n` onto the summand `F E 1_n`. -/
def πFE : S.F r ≫ S.E r ⟶ S.E (r + 1) ≫ S.F (r + 1) := e.hom ≫ biprod.fst

omit [GradedBicategory.IsLinear B k] in
theorem ι_π_self {j : ℕ} (hj : j < (S.wt (r + 1)).toNat) : ι e j ≫ π e j = 𝟙 _ := by
  simp only [ι, π, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd_assoc]
  exact bsumι_π_self _ _ _ hj

omit [GradedBicategory.IsLinear B k] in
theorem ι_π_ne {j j' : ℕ} (hj : j ≠ j') : ι e j ≫ π e j' = 0 := by
  simp only [ι, π, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd_assoc]
  exact bsumι_π_ne _ _ _ _ hj

omit [GradedBicategory.IsLinear B k] in
/-- The decomposition of the identity of `E F 1_n`. -/
theorem total :
    ∑ j ∈ Finset.range (S.wt (r + 1)).toNat, π e j ≫ ι e j + πFE e ≫ ιFE e = 𝟙 _ := by
  have h1 : ∀ j ∈ Finset.range (S.wt (r + 1)).toNat, π e j ≫ ι e j =
      e.hom ≫ (biprod.snd ≫ (bsumπ (S.oneShift r) _ j ≫ bsumι (S.oneShift r) _ j) ≫ biprod.inr) ≫
        e.inv := by
    intro j _
    simp only [π, ι, Category.assoc]
  rw [Finset.sum_congr rfl h1, ← Preadditive.comp_sum, ← Preadditive.sum_comp,
    ← Preadditive.comp_sum, ← Preadditive.sum_comp, bsum_total, Category.id_comp]
  have h2 : e.hom ≫ (biprod.snd ≫ biprod.inr + biprod.fst ≫ biprod.inl) ≫ e.inv = 𝟙 _ := by
    rw [add_comm (biprod.snd ≫ biprod.inr), biprod.total, Category.id_comp, Iso.hom_inv_id]
  rw [← h2]
  simp only [πFE, ιFE, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

/-! ## The dot and its matrix entries -/

variable (S) in
/-- **The dot on `E F 1_n`**: the dot on the strand `E 1_{n-2}` (Mathlib: `F r ◁ dot r`), a map
`E F 1_n → E F 1_n ⟨2⟩`. -/
def dotEF (r : ℤ) : S.F r ≫ S.E r ⟶ (S.F r ≫ S.E r)⟦(2 : ℤ)⟧ :=
  shWhiskerLeft (S.F r) (S.dot r)

/-- The `(i, j)` matrix entry of the dot in the decomposition:
`1_n⟨n-1-2i⟩ → E F 1_n → E F 1_n ⟨2⟩ → 1_n⟨n-1-2j⟩⟨2⟩`, of degree `2(i - j + 1)`. -/
def entry (i j : ℕ) : S.oneShift r i ⟶ (S.oneShift r j)⟦(2 : ℤ)⟧ :=
  ι e i ≫ S.dotEF r ≫ (π e j)⟦(2 : ℤ)⟧'

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- Degree vanishing: a map `1_n⟨n-1-2i⟩ → 1_n⟨n-1-2j⟩⟨d⟩` of negative degree `d - 2(j - i)` is
zero. -/
theorem hom_oneShift_eq_zero (i j : ℕ) {d : ℤ} (hd : d + 2 * (i : ℤ) - 2 * (j : ℤ) < 0)
    (f : S.oneShift r i ⟶ (S.oneShift r j)⟦d⟧) : f = 0 := by
  have s1 : (S.oneShift r j)⟦d⟧ ≅
      (𝟙 (S.obj (r + 1)))⟦1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)) + d⟧ :=
    ((shiftFunctorAdd' _ _ d _ rfl).app (𝟙 (S.obj (r + 1)))).symm
  have h0 : finrank k (S.oneShift r i ⟶ (S.oneShift r j)⟦d⟧) = 0 := by
    rw [finrank_hom_congr_right k _ s1, oneShift,
      finrank_hom_shift_shift k _ _ (c := d + 2 * (i : ℤ) - 2 * (j : ℤ)) (by ring)]
    exact S.hom_neg _ _ hd
  haveI := Module.finrank_zero_iff.1 h0
  exact Subsingleton.elim _ _

/-- The entries of the dot above the subdiagonal vanish: `entry e i j = 0` for `j > i + 1`. -/
theorem entry_eq_zero {i j : ℕ} (h : i + 1 < j) : entry e i j = 0 :=
  hom_oneShift_eq_zero i j (by omega) _

/-- **The content of CL Lemma 3.6** (`lem:Xind`, "`rk_{1_n}(dot) = n - 1`"): the `n - 1`
subdiagonal entries `entry e i (i + 1) : 1_n⟨n-1-2i⟩ → 1_n⟨n-3-2i⟩⟨2⟩` (`i + 1 < n`) of the dot are
isomorphisms (nonzero scalars). -/
def DotNondeg : Prop := ∀ i : ℕ, i + 1 < (S.wt (r + 1)).toNat → IsIso (entry e i (i + 1))

/-! ## Corollary 3.7: the degree-zero bubble -/

/-- `cup ≫ dot^m : 1_n⟨n-1⟩ → E F 1_n ⟨2m⟩`. -/
def cupDots (m : ℕ) : S.oneShift r 0 ⟶ (S.F r ≫ S.E r)⟦(m : ℤ) * 2⟧ :=
  ι e 0 ≫ (shPow (S.dotEF r : ShiftedHom (S.F r ≫ S.E r) (S.F r ≫ S.E r) (2 : ℤ)) m :
    S.F r ≫ S.E r ⟶ (S.F r ≫ S.E r)⟦(m : ℤ) * 2⟧)

/-- **CL's degree-zero bubble** with `n - 1` dots at the weight `n`: `cup`, then `n - 1` dots, then
`cap`, as a map `1_n⟨n-1⟩ → 1_n⟨-n+1⟩⟨2(n-1)⟩` (the source and target are isomorphic to `1_n`). -/
def bubble : S.oneShift r 0 ⟶
    (S.oneShift r ((S.wt (r + 1)).toNat - 1))⟦(((S.wt (r + 1)).toNat - 1 : ℕ) : ℤ) * 2⟧ :=
  cupDots e _ ≫ (π e _)⟦_⟧'

omit [GradedBicategory.IsLinear B k] in
omit [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cupDots_zero_comp (j : ℕ) :
    cupDots e 0 ≫ (π e j)⟦((0 : ℕ) : ℤ) * 2⟧' =
      (ι e 0 ≫ π e j) ≫ (shiftFunctorZero' _ (((0 : ℕ) : ℤ) * 2) (by simp)).inv.app _ := by
  simp only [cupDots, shPow, ShiftedHom.mk₀, Category.id_comp, Category.assoc]
  have := (shiftFunctorZero' _ (((0 : ℕ) : ℤ) * 2) (by simp)).inv.naturality (π e j)
  simp only [Functor.id_map] at this
  rw [← this]
  try rfl

omit [GradedBicategory.IsLinear B k] in
omit [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- One more dot: `cup ≫ dot^{m+1}`, projected to the `j`-th summand, is
`cup ≫ dot^m` followed by (the shift of) `dot` projected to the `j`-th summand. -/
theorem cupDots_succ_comp (m j : ℕ) :
    cupDots e (m + 1) ≫ (π e j)⟦((m + 1 : ℕ) : ℤ) * 2⟧' =
      (cupDots e m ≫ (S.dotEF r ≫ (π e j)⟦(2 : ℤ)⟧')⟦(m : ℤ) * 2⟧') ≫
        (shiftFunctorAdd' _ 2 ((m : ℤ) * 2) (((m + 1 : ℕ) : ℤ) * 2) (by push_cast; ring)).inv.app _ := by
  simp only [cupDots, shPow, ShiftedHom.comp, Category.assoc, Functor.map_comp]
  rw [← (shiftFunctorAdd' _ 2 ((m : ℤ) * 2) (((m + 1 : ℕ) : ℤ) * 2)
    (by push_cast; ring)).inv.naturality (π e j)]
  try rfl

omit [GradedBicategory.IsLinear B k] in
omit [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The dot followed by the projection to the `j`-th summand, expanded along the decomposition of
the identity of `E F 1_n`. -/
theorem dotEF_comp_π (j : ℕ) :
    S.dotEF r ≫ (π e j)⟦(2 : ℤ)⟧' =
      ∑ j' ∈ Finset.range (S.wt (r + 1)).toNat, π e j' ≫ entry e j' j +
        πFE e ≫ (ιFE e ≫ S.dotEF r ≫ (π e j)⟦(2 : ℤ)⟧') := by
  conv_lhs => rw [← Category.id_comp (S.dotEF r), ← total e]
  simp only [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc, entry]

/-- The component of `cup ≫ dot^m` in `F E 1_n ⟨2m⟩` vanishes for `m < n`:
`Hom(1_n⟨n-1-2m⟩, F E 1_n) = 0` by Lemma 3.1 (under (3.2) for the weights `> n`). -/
theorem cupDots_comp_πFE (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r') {m : ℕ}
    (hm : m < (S.wt (r + 1)).toNat) : cupDots e m ≫ (πFE e)⟦(m : ℤ) * 2⟧' = 0 := by
  have hN : (((S.wt (r + 1)).toNat : ℕ) : ℤ) = S.wt (r + 1) := Int.toNat_of_nonneg hn
  have h0 : finrank k (S.oneShift r 0 ⟶ (S.E (r + 1) ≫ S.F (r + 1))⟦(m : ℤ) * 2⟧) = 0 := by
    rw [oneShift, finrank_hom_shift_shift k _ _
        (c := (m : ℤ) * 2 - 1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)))
        (by ring),
      finrank_hom_shift_right k _ _
        (b := 1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) - (m : ℤ) * 2)
        (by ring),
      S.finrank_one_FE, S.lem1_neg (r₀ := r + 1) hn hyp (r + 1) le_rfl]
    push_cast
    omega
  haveI := Module.finrank_zero_iff.1 h0
  exact Subsingleton.elim _ _

/-- The induction behind Corollary 3.7: for `m < n`, `cup ≫ dot^m` has zero component in the
summands `1_n⟨n-1-2j⟩` with `j > m`, and an isomorphism as component in the `m`-th summand. -/
theorem bubble_aux (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r')
    (hd : DotNondeg e) : ∀ m : ℕ, m < (S.wt (r + 1)).toNat →
      (∀ j : ℕ, m < j → cupDots e m ≫ (π e j)⟦(m : ℤ) * 2⟧' = 0) ∧
        IsIso (cupDots e m ≫ (π e m)⟦(m : ℤ) * 2⟧') := by
  intro m
  induction m with
  | zero =>
    intro hm
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [cupDots_zero_comp, ι_π_ne e (by omega), zero_comp]
    · rw [cupDots_zero_comp, ι_π_self e hm, Category.id_comp]
      infer_instance
  | succ m ih =>
    intro hm
    obtain ⟨iha, ihb⟩ := ih (by omega)
    -- expand one more dot along the decomposition
    have key : ∀ j : ℕ, cupDots e (m + 1) ≫ (π e j)⟦((m + 1 : ℕ) : ℤ) * 2⟧' =
        (∑ j' ∈ Finset.range (S.wt (r + 1)).toNat,
          (cupDots e m ≫ (π e j')⟦(m : ℤ) * 2⟧') ≫ (entry e j' j)⟦(m : ℤ) * 2⟧') ≫
          (shiftFunctorAdd' _ 2 ((m : ℤ) * 2) (((m + 1 : ℕ) : ℤ) * 2)
            (by push_cast; ring)).inv.app _ := by
      intro j
      rw [cupDots_succ_comp, dotEF_comp_π, Functor.map_add, Functor.map_sum, Preadditive.comp_add,
        Preadditive.comp_sum]
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc (cupDots e m) ((πFE e)⟦(m : ℤ) * 2⟧'),
        cupDots_comp_πFE e hn hyp (by omega), zero_comp, add_zero]
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [key, Finset.sum_eq_zero, zero_comp]
      intro j' _
      by_cases hj' : m < j'
      · rw [iha j' hj', zero_comp]
      · rw [entry_eq_zero e (by omega), Functor.map_zero, comp_zero]
    · rw [key, Finset.sum_eq_single m]
      · haveI := hd m hm
        infer_instance
      · intro j' _ hj'
        rcases lt_or_gt_of_ne hj' with h | h
        · rw [entry_eq_zero e (by omega), Functor.map_zero, comp_zero]
        · rw [iha j' h, zero_comp]
      · intro h
        rw [Finset.mem_range] at h
        omega

/-- **Corollary 3.7** (CL `cor:degz-bubbles`), conditionally on Lemma 3.6: at a weight `n > 0`,
assuming the adjoint induction hypothesis (3.2) for the weights `> n` and the nondegeneracy of the
subdiagonal of the dot (`DotNondeg e`, the content of Lemma 3.6), the degree-zero bubble with
`n - 1` dots is an isomorphism, i.e. a nonzero multiple of the identity of `1_n`. -/
theorem cor_degz_bubbles_of_dotNondeg (hn : 0 < S.wt (r + 1))
    (hyp : ∀ r', r + 1 < r' → S.AdjHyp r') (hd : DotNondeg e) : IsIso (bubble e) :=
  (bubble_aux e hn.le hyp hd ((S.wt (r + 1)).toNat - 1) (by omega)).2

end Categorification.TwoRep.StrongSl2
