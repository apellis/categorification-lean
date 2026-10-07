/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Duality
import Categorification.TwoRep.WordNumerics
import Categorification.TwoRep.AdjointWeightNegOne

/-!
# The lower half of Lemma 3.6 under (BB_w), by duality

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Lemma 3.6 (`lem:Xind`) for `n < -1`: the dot on the upward strand of
`F E 1_n` induces an isomorphism on `-n-1` of the summands `1_n⟨k⟩` of `F E 1_n`.

In the notation of `DotEntriesNeg.lean`, this is `DotNondegNeg e` for a decomposition datum
`e : F E 1_n ≅ E F 1_n ⊕ ⊕_{j<-n} 1_n⟨-n-1-2j⟩`. We prove it under (BB_w) by applying the upper
half (`BBw.dotNondeg`, for `n ≥ 2`) to the dual `D(K)` (`StrongSl2.dual`, in the bidual `Bᶜᵒᵒᵖ`):

* `F E 1_n` in `K` is `E' F' 1_{-n}` in `D(K)`, and the dot on its `E`-strand is the dot of `D(K)`
  on the strand `E' 1_{-n-2}` (the whiskerings are exchanged by the duality);
* a decomposition datum `e` of `F E 1_n` in `K` gives a decomposition datum `e'` of
  `E' F' 1_{-n}` in `D(K)` (`StrongSl2.dualEFDecomp`): the summand inclusions of `e'` are the
  opposites of the summand projections of `e`, and the summand `1⟨-n-1-2j⟩` of `e'` is the
  summand `1⟨-n-1-2(-n-1-j)⟩` of `e` (the grading shift of the bidual is inverted);
* the subdiagonal entry `i → i + 1` of the dot in `e'` is, up to identifications of the
  summands, the opposite of the subdiagonal entry `-n-2-i → -n-1-i` of the dot in `e`
  (`StrongSl2.entry_dualEFDecomp`).

Since `E F 1_n` has the same indices as `D(K)` only up to the identities `-(-r) = r`, the comparison
is made with the data of `K` written with free indices (`StrongSl2.Ec`, `Fc`, `dotc`), and
transported back to the usual indexing by `StrongSl2.dotNondegNeg_of_c`.

## Main declarations

* `bsumLift`, `isoOfComponents`: a biproduct decomposition `X ≅ A ⊞ ⊕_j f j` from its components;
* `BDecomp.ιs`, `πs`, `ιA`, `πA` and their relations, for any `X ≅ A ⊞ bsum f n`;
* `StrongSl2.dualEFDecomp`, `StrongSl2.entry_dualEFDecomp`;
* `StrongSl2.BBw.dotNondegNeg`: **CL Lemma 3.6 for `n < -1` under (BB_w)**;
* `StrongSl2.BBw.isIso_bubbleN`: **CL Corollary 3.7 for `n < 0` under (BB_w)** (the
  counter-clockwise degree-zero bubble is an isomorphism);
* `StrongSl2.BBw.isIso_zetaNeg`: CL Corollary 3.13 for `n ≤ 0` under (BB_w).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module Opposite
open KrullSchmidtCat (HomFinite)

universe w v u

/-! ## Biproduct decompositions and their components -/

section Components

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

/-- The map into `bsum f n` with components `φ j : Y ⟶ f j`. -/
def bsumLift (f : ℕ → C) {Y : C} (φ : ∀ j : ℕ, Y ⟶ f j) : ∀ n : ℕ, Y ⟶ bsum f n
  | 0 => 0
  | n + 1 => biprod.lift (φ n) (bsumLift f φ n)

theorem bsumLift_π (f : ℕ → C) {Y : C} (φ : ∀ j : ℕ, Y ⟶ f j) :
    ∀ (n j : ℕ), j < n → bsumLift f φ n ≫ bsumπ f n j = φ j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, h => by
    by_cases hj : j = n
    · subst hj
      simp [bsumLift, bsumπ]
    · simp only [bsumLift, bsumπ, dite_eq_right hj, biprod.lift_snd_assoc]
      exact bsumLift_π f φ n j (by omega)

theorem bsumLift_desc (f : ℕ → C) {Y Z : C} (φ : ∀ j : ℕ, Y ⟶ f j) (ψ : ∀ j : ℕ, f j ⟶ Z) :
    ∀ n : ℕ, bsumLift f φ n ≫ bsumDesc f ψ n = ∑ j ∈ Finset.range n, φ j ≫ ψ j
  | 0 => by simp [bsumLift]
  | n + 1 => by
    rw [Finset.sum_range_succ, ← bsumLift_desc f φ ψ n]
    simp only [bsumLift, bsumDesc, biprod.lift_desc]
    exact add_comm _ _

/-- Maps into `bsum f n` are determined by their components. -/
theorem bsum_hom_ext' (f : ℕ → C) {Y : C} {n : ℕ} {x y : Y ⟶ bsum f n}
    (h : ∀ j, j < n → x ≫ bsumπ f n j = y ≫ bsumπ f n j) : x = y := by
  rw [← Category.comp_id x, ← Category.comp_id y, ← bsum_total, Preadditive.comp_sum,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Category.assoc, ← Category.assoc, h j (Finset.mem_range.1 hj)]

variable {X A : C} {f : ℕ → C} {n : ℕ}

/-- **A biproduct decomposition from its components**: maps `ιA, πA` and `ι j, π j` (`j < n`)
satisfying the biproduct identities give an isomorphism `X ≅ A ⊞ bsum f n` whose components are
the given maps (`isoOfComponents_ι`, `isoOfComponents_π`, `isoOfComponents_ιA`,
`isoOfComponents_πA`). -/
def isoOfComponents (ιA : A ⟶ X) (πA : X ⟶ A) (ι : ∀ j, f j ⟶ X) (π : ∀ j, X ⟶ f j)
    (hA : ιA ≫ πA = 𝟙 A) (hAπ : ∀ j, j < n → ιA ≫ π j = 0)
    (hιA : ∀ j, j < n → ι j ≫ πA = 0) (hself : ∀ j, j < n → ι j ≫ π j = 𝟙 (f j))
    (hne : ∀ j j', j < n → j' < n → j ≠ j' → ι j ≫ π j' = 0)
    (htot : ∑ j ∈ Finset.range n, π j ≫ ι j + πA ≫ ιA = 𝟙 X) : X ≅ A ⊞ bsum f n where
  hom := biprod.lift πA (bsumLift f π n)
  inv := biprod.desc ιA (bsumDesc f ι n)
  hom_inv_id := by rw [biprod.lift_desc, bsumLift_desc, add_comm]; exact htot
  inv_hom_id := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, biprod.inl_fst, hA]
      · rw [Category.assoc, biprod.lift_snd, biprod.inl_snd]
        exact bsum_hom_ext' f fun j hj => by
          rw [Category.assoc, bsumLift_π f π n j hj, hAπ j hj, zero_comp]
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, biprod.inr_fst]
        exact bsum_hom_ext f fun j hj => by
          rw [← Category.assoc, bsumι_desc f ι n j hj, hιA j hj, comp_zero]
      · rw [Category.assoc, biprod.lift_snd, biprod.inr_snd]
        refine bsum_hom_ext f fun j hj => bsum_hom_ext' f fun j' hj' => ?_
        rw [Category.assoc, Category.assoc, bsumLift_π f π n j' hj', ← Category.assoc,
          bsumι_desc f ι n j hj, Category.comp_id]
        by_cases hjj : j = j'
        · subst hjj
          rw [hself j hj, bsumι_π_self f n j hj]
        · rw [hne j j' hj hj' hjj, bsumι_π_ne f n j j' hjj]

section

variable (ιA : A ⟶ X) (πA : X ⟶ A) (ι : ∀ j, f j ⟶ X) (π : ∀ j, X ⟶ f j)
  (hA : ιA ≫ πA = 𝟙 A) (hAπ : ∀ j, j < n → ιA ≫ π j = 0)
  (hιA : ∀ j, j < n → ι j ≫ πA = 0) (hself : ∀ j, j < n → ι j ≫ π j = 𝟙 (f j))
  (hne : ∀ j j', j < n → j' < n → j ≠ j' → ι j ≫ π j' = 0)
  (htot : ∑ j ∈ Finset.range n, π j ≫ ι j + πA ≫ ιA = 𝟙 X)

theorem isoOfComponents_ι {j : ℕ} (hj : j < n) :
    bsumι f n j ≫ biprod.inr ≫ (isoOfComponents ιA πA ι π hA hAπ hιA hself hne htot).inv =
      ι j := by
  change bsumι f n j ≫ biprod.inr ≫ biprod.desc ιA (bsumDesc f ι n) = ι j
  rw [biprod.inr_desc, bsumι_desc f ι n j hj]

theorem isoOfComponents_π {j : ℕ} (hj : j < n) :
    (isoOfComponents ιA πA ι π hA hAπ hιA hself hne htot).hom ≫ biprod.snd ≫ bsumπ f n j =
      π j := by
  change biprod.lift πA (bsumLift f π n) ≫ biprod.snd ≫ bsumπ f n j = π j
  rw [biprod.lift_snd_assoc, bsumLift_π f π n j hj]

theorem isoOfComponents_ιA :
    biprod.inl ≫ (isoOfComponents ιA πA ι π hA hAπ hιA hself hne htot).inv = ιA :=
  biprod.inl_desc _ _

theorem isoOfComponents_πA :
    (isoOfComponents ιA πA ι π hA hAπ hιA hself hne htot).hom ≫ biprod.fst = πA :=
  biprod.lift_fst _ _

end

namespace BDecomp

variable (e : X ≅ A ⊞ bsum f n)

/-- The inclusion of the summand `f j` of a decomposition `X ≅ A ⊞ bsum f n`. -/
def ιs (j : ℕ) : f j ⟶ X := bsumι f n j ≫ biprod.inr ≫ e.inv

/-- The projection onto the summand `f j` of a decomposition `X ≅ A ⊞ bsum f n`. -/
def πs (j : ℕ) : X ⟶ f j := e.hom ≫ biprod.snd ≫ bsumπ f n j

/-- The inclusion of the summand `A` of a decomposition `X ≅ A ⊞ bsum f n`. -/
def ιA : A ⟶ X := biprod.inl ≫ e.inv

/-- The projection onto the summand `A` of a decomposition `X ≅ A ⊞ bsum f n`. -/
def πA : X ⟶ A := e.hom ≫ biprod.fst

theorem ιA_πA : ιA e ≫ πA e = 𝟙 A := by
  simp only [ιA, πA, Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_fst]

theorem ιA_πs (j : ℕ) : ιA e ≫ πs e j = 0 := by
  simp only [ιA, πs, Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_snd_assoc, zero_comp]

theorem ιs_πA (j : ℕ) : ιs e j ≫ πA e = 0 := by
  simp only [ιs, πA, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_fst, comp_zero]

theorem ιs_πs_self {j : ℕ} (hj : j < n) : ιs e j ≫ πs e j = 𝟙 (f j) := by
  simp only [ιs, πs, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd_assoc]
  exact bsumι_π_self _ _ _ hj

theorem ιs_πs_ne {j j' : ℕ} (h : j ≠ j') : ιs e j ≫ πs e j' = 0 := by
  simp only [ιs, πs, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd_assoc]
  exact bsumι_π_ne _ _ _ _ h

/-- The decomposition of the identity of `X`. -/
theorem total : ∑ j ∈ Finset.range n, πs e j ≫ ιs e j + πA e ≫ ιA e = 𝟙 X := by
  have h1 : ∀ j ∈ Finset.range n, πs e j ≫ ιs e j =
      e.hom ≫ (biprod.snd ≫ (bsumπ f n j ≫ bsumι f n j) ≫ biprod.inr) ≫ e.inv := by
    intro j _
    simp only [πs, ιs, Category.assoc]
  rw [Finset.sum_congr rfl h1, ← Preadditive.comp_sum, ← Preadditive.sum_comp,
    ← Preadditive.comp_sum, ← Preadditive.sum_comp, bsum_total, Category.id_comp]
  have h2 : e.hom ≫ (biprod.snd ≫ biprod.inr + biprod.fst ≫ biprod.inl) ≫ e.inv = 𝟙 _ := by
    rw [add_comm (biprod.snd ≫ biprod.inr), biprod.total, Category.id_comp, Iso.hom_inv_id]
  rw [← h2]
  simp only [πA, ιA, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

end BDecomp

/-! ### The opposite decomposition, with the summands in reverse order -/

section OpDecomp

open Opposite

variable (e : X ≅ A ⊞ bsum f n) {g : ℕ → C} (hg : ∀ j, j < n → f (n - 1 - j) = g j)

/-- The summand inclusions of the opposite decomposition (`opDecomp`). -/
def opι (j : ℕ) : op (g j) ⟶ op X :=
  if hj : j < n then (BDecomp.πs e (n - 1 - j) ≫ eqToHom (hg j hj)).op else 0

/-- The summand projections of the opposite decomposition (`opDecomp`). -/
def opπ (j : ℕ) : op X ⟶ op (g j) :=
  if hj : j < n then (eqToHom (hg j hj).symm ≫ BDecomp.ιs e (n - 1 - j)).op else 0

theorem opι_of_lt {j : ℕ} (hj : j < n) :
    opι e hg j = (BDecomp.πs e (n - 1 - j) ≫ eqToHom (hg j hj)).op :=
  dite_eq_left hj

theorem opπ_of_lt {j : ℕ} (hj : j < n) :
    opπ e hg j = (eqToHom (hg j hj).symm ≫ BDecomp.ιs e (n - 1 - j)).op :=
  dite_eq_left hj

/-- **The opposite of a decomposition `X ≅ A ⊞ ⊕_{j<n} f j`**, in `Cᵒᵖ`, with the summands
listed in reverse order (`g j = f (n - 1 - j)`) and indexed up to `n' = n`. -/
def opDecomp (n' : ℕ) (hn : n' = n) : op X ≅ op A ⊞ bsum (fun j => op (g j)) n' :=
  isoOfComponents (BDecomp.πA e).op (BDecomp.ιA e).op (opι e hg) (opπ e hg)
    (Quiver.Hom.unop_inj (by simp [BDecomp.ιA_πA]))
    (fun j hj => Quiver.Hom.unop_inj (by
      rw [unop_comp, opπ_of_lt e hg (hn ▸ hj), Quiver.Hom.unop_op, Quiver.Hom.unop_op,
        Category.assoc, BDecomp.ιs_πA, comp_zero, unop_zero]))
    (fun j hj => Quiver.Hom.unop_inj (by
      rw [unop_comp, opι_of_lt e hg (hn ▸ hj), Quiver.Hom.unop_op, Quiver.Hom.unop_op,
        ← Category.assoc, BDecomp.ιA_πs, zero_comp, unop_zero]))
    (fun j hj => Quiver.Hom.unop_inj (by
      rw [unop_comp, opι_of_lt e hg (hn ▸ hj), opπ_of_lt e hg (hn ▸ hj), Quiver.Hom.unop_op,
        Quiver.Hom.unop_op, Category.assoc, ← Category.assoc (BDecomp.ιs e _),
        BDecomp.ιs_πs_self e (by omega), Category.id_comp, eqToHom_trans, eqToHom_refl,
        unop_id]))
    (fun j j' hj hj' hjj => Quiver.Hom.unop_inj (by
      rw [unop_comp, opι_of_lt e hg (hn ▸ hj), opπ_of_lt e hg (hn ▸ hj'), Quiver.Hom.unop_op,
        Quiver.Hom.unop_op, Category.assoc, ← Category.assoc (BDecomp.ιs e _),
        BDecomp.ιs_πs_ne e (by omega), zero_comp, comp_zero, unop_zero]))
    (Quiver.Hom.unop_inj (by
      rw [unop_add, unop_sum, unop_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op, unop_id, hn]
      have h1 : ∀ j ∈ Finset.range n, (opπ e hg j ≫ opι e hg j).unop =
          BDecomp.πs e (n - 1 - j) ≫ BDecomp.ιs e (n - 1 - j) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [unop_comp, opι_of_lt e hg hj, opπ_of_lt e hg hj, Quiver.Hom.unop_op,
          Quiver.Hom.unop_op, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
      rw [Finset.sum_congr rfl h1,
        Finset.sum_range_reflect (fun j => BDecomp.πs e j ≫ BDecomp.ιs e j)]
      exact BDecomp.total e))

theorem opDecomp_ι (n' : ℕ) (hn : n' = n) {j : ℕ} (hj : j < n) :
    bsumι _ n' j ≫ biprod.inr ≫ (opDecomp e hg n' hn).inv =
      (BDecomp.πs e (n - 1 - j) ≫ eqToHom (hg j hj)).op := by
  rw [opDecomp, isoOfComponents_ι _ _ _ _ _ _ _ _ _ _ (hn ▸ hj), opι_of_lt e hg hj]

theorem opDecomp_π (n' : ℕ) (hn : n' = n) {j : ℕ} (hj : j < n) :
    (opDecomp e hg n' hn).hom ≫ biprod.snd ≫ bsumπ _ n' j =
      (eqToHom (hg j hj).symm ≫ BDecomp.ιs e (n - 1 - j)).op := by
  rw [opDecomp, isoOfComponents_π _ _ _ _ _ _ _ _ _ _ (hn ▸ hj), opπ_of_lt e hg hj]

end OpDecomp

end Components

/-! ## Shifted opposites detect isomorphisms -/

section ShOpIso

open Pretriangulated.Opposite in
/-- If the opposite `opEquiv G : op Y ⟶ (op X)⟨n⟩` of a shifted morphism `G : X ⟶ Y⟨n⟩` is an
isomorphism, so is `G`. -/
theorem isIso_of_isIso_opEquiv {C : Type*} [Category C] [HasShift C ℤ] {X Y : C} {n : ℤ}
    (G : ShiftedHom X Y n)
    (h : IsIso (ShiftedHom.opEquiv n G : Opposite.op Y ⟶ (Opposite.op X)⟦n⟧)) :
    IsIso (G : X ⟶ Y⟦n⟧) := by
  rw [← (ShiftedHom.opEquiv n).symm_apply_apply G, ShiftedHom.opEquiv_symm_apply]
  infer_instance

end ShOpIso

/-! ## The data of `K` with free indices -/

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]

namespace StrongSl2

variable (S : StrongSl2 k B)

/-- The summand `1⟨-n-1-2j⟩` of `⊕_{[-n]} 1_n` at the object `s` (`n = wt s`): `oneShiftNeg`
with a free index. -/
def oneShiftC (s : ℤ) (j : ℕ) : S.obj s ⟶ S.obj s :=
  (𝟙 (S.obj s))⟦1 * ((((-S.wt s).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ))⟧

/-- A decomposition datum `F E 1_n ≅ E F 1_n ⊕ ⊕_{j<-n} 1_n⟨-n-1-2j⟩` (`FEDecomp`) with free
indices. -/
abbrev FEDecompC (s' s t : ℤ) (h' : s' + 1 = s) (h : s + 1 = t) :=
  S.Ec s t h ≫ S.Fc s t h ≅ (S.Fc s' s h' ≫ S.Ec s' s h') ⊞ bsum (S.oneShiftC s) (-S.wt s).toNat

/-- The dot on `F E 1_n` (`dotFE`) with free indices. -/
def dotFEc (s t : ℤ) (h : s + 1 = t) :
    ShiftedHom (S.Ec s t h ≫ S.Fc s t h) (S.Ec s t h ≫ S.Fc s t h) (2 : ℤ) :=
  shWhiskerRight (S.dotc s t h) (S.Fc s t h)

variable {S}

/-- The matrix entries of the dot on `F E 1_n` (`entryN`) with free indices. -/
def entryNc {s' s t : ℤ} {h' : s' + 1 = s} {h : s + 1 = t} (ec : S.FEDecompC s' s t h' h)
    (i j : ℕ) : S.oneShiftC s i ⟶ (S.oneShiftC s j)⟦(2 : ℤ)⟧ :=
  BDecomp.ιs ec i ≫ (S.dotFEc s t h : _ ⟶ _) ≫ (BDecomp.πs ec j)⟦(2 : ℤ)⟧'

variable (S)

/-- The lower half of Lemma 3.6 with free indices gives `DotNondegNeg`. -/
theorem dotNondegNeg_of_c {s₀ s' s t : ℤ} (h₀ : s₀ = s') (h' : s' + 1 = s) (h : s + 1 = t)
    (H : ∀ ec : S.FEDecompC s' s t h' h, ∀ i : ℕ, i + 1 < (-S.wt s).toNat →
      IsIso (entryNc ec i (i + 1)))
    (e : S.FEDecomp s₀) : DotNondegNeg e := by
  subst h₀ h' h
  exact H e

/-! ## The decomposition datum of the dual -/

variable [GradedBicategory.IsLinear B k]

variable {S} {q : ℤ}

theorem dual_wt_toNat (q : ℤ) :
    (S.dual.wt (q + 1 + 1)).toNat = (-S.wt (-(q + 1 + 1))).toNat := by
  rw [dual_wt]

variable (S) in
/-- The summand `1⟨-(N-1-2j)⟩` of the dual decomposition at the weight `-n` (`N = -n`), as a
1-morphism of `K` (the grading shift of the bidual is inverted). -/
def dualSummand (q : ℤ) (j : ℕ) : S.obj (-(q + 1 + 1)) ⟶ S.obj (-(q + 1 + 1)) :=
  (𝟙 (S.obj (-(q + 1 + 1))))⟦-(1 * ((((S.dual.wt (q + 1 + 1)).toNat : ℕ) : ℤ) - 1 -
    2 * (j : ℤ)))⟧

/-- The summand `1⟨-n-1-2(N-1-j)⟩` of `e` is the summand `j` of the dual. -/
theorem oneShiftC_eq_dualSummand {j : ℕ} (hj : j < (-S.wt (-(q + 1 + 1))).toNat) :
    S.oneShiftC (-(q + 1 + 1)) ((-S.wt (-(q + 1 + 1))).toNat - 1 - j) = S.dualSummand q j := by
  have hN := dual_wt_toNat (S := S) q
  have hs : 1 * ((((-S.wt (-(q + 1 + 1))).toNat : ℕ) : ℤ) - 1 - 2 *
      (((-S.wt (-(q + 1 + 1))).toNat - 1 - j : ℕ) : ℤ)) =
        -(1 * ((((S.dual.wt (q + 1 + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ))) := by
    rw [hN]
    omega
  exact congrArg (fun m : ℤ => (𝟙 (S.obj (-(q + 1 + 1))))⟦m⟧) hs

variable (ec : S.FEDecompC (-(q + 1 + 1 + 1)) (-(q + 1 + 1)) (-(q + 1)) (by omega) (by omega))

/-- **The decomposition datum of `E' F' 1_{-n}` in the dual** obtained from a decomposition
datum `ec` of `F E 1_n` in `K`: the opposite of `ec`, with the summands `1_n⟨k⟩` in reverse
order. -/
def dualEFDecomp : S.dual.EFDecomp (q + 1) :=
  opDecomp ec (g := S.dualSummand q) (fun _ hj => oneShiftC_eq_dualSummand hj) _
    (dual_wt_toNat (S := S) q)

theorem ι_dualEFDecomp {j : ℕ} (hj : j < (-S.wt (-(q + 1 + 1))).toNat) :
    ι (dualEFDecomp ec) j =
      (BDecomp.πs ec ((-S.wt (-(q + 1 + 1))).toNat - 1 - j) ≫
        eqToHom (oneShiftC_eq_dualSummand hj)).op :=
  opDecomp_ι ec _ _ _ hj

theorem π_dualEFDecomp {j : ℕ} (hj : j < (-S.wt (-(q + 1 + 1))).toNat) :
    π (dualEFDecomp ec) j =
      (eqToHom (oneShiftC_eq_dualSummand hj).symm ≫
        BDecomp.ιs ec ((-S.wt (-(q + 1 + 1))).toNat - 1 - j)).op :=
  opDecomp_π ec _ _ _ hj

/-- The dot of the dual on `E' F' 1_{-n}` is the opposite of the dot of `K` on `F E 1_n`. -/
theorem dual_dotEF :
    S.dual.dotEF (q + 1) = Coop.shOp (S.dotFEc (-(q + 1 + 1)) (-(q + 1)) (by omega)) :=
  (Coop.shOp_shWhiskerRight _ _).symm

/-- **The subdiagonal entries of the dot in the dual decomposition**: if the entry `i → i + 1`
of `dualEFDecomp ec` is an isomorphism, so is the entry `N-2-i → N-1-i` of `ec` (`N = -n`). -/
theorem isIso_entryNc_of_dual {i : ℕ} (hi : i + 1 < (-S.wt (-(q + 1 + 1))).toNat)
    (hI : IsIso (entry (dualEFDecomp ec) i (i + 1))) :
    IsIso (entryNc ec ((-S.wt (-(q + 1 + 1))).toNat - 1 - (i + 1))
      ((-S.wt (-(q + 1 + 1))).toNat - 1 - i)) := by
  have hi0 : i < (-S.wt (-(q + 1 + 1))).toNat := by omega
  let x : S.dualSummand q (i + 1) ⟶ S.Ec (-(q + 1 + 1)) (-(q + 1)) (by omega) ≫
      S.Fc (-(q + 1 + 1)) (-(q + 1)) (by omega) :=
    eqToHom (oneShiftC_eq_dualSummand hi).symm ≫
      BDecomp.ιs ec ((-S.wt (-(q + 1 + 1))).toNat - 1 - (i + 1))
  let y : S.Ec (-(q + 1 + 1)) (-(q + 1)) (by omega) ≫ S.Fc (-(q + 1 + 1)) (-(q + 1)) (by omega) ⟶
      S.dualSummand q i :=
    BDecomp.πs ec ((-S.wt (-(q + 1 + 1))).toNat - 1 - i) ≫ eqToHom (oneShiftC_eq_dualSummand hi0)
  let G : ShiftedHom (S.dualSummand q (i + 1)) (S.dualSummand q i) (2 : ℤ) :=
    (ShiftedHom.mk₀ (0 : ℤ) rfl x).comp
      ((S.dotFEc (-(q + 1 + 1)) (-(q + 1)) (by omega)).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl y) (zero_add 2)) (add_zero 2)
  have hE : entry (dualEFDecomp ec) i (i + 1) = Coop.shOp G := by
    simp only [G]
    rw [Coop.shOp_comp _ _ (add_zero 2) (zero_add 2),
      Coop.shOp_comp _ _ (zero_add 2) (add_zero 2), Coop.shOp_mk₀, Coop.shOp_mk₀,
      ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ← dual_dotEF]
    rw [entry, ι_dualEFDecomp ec hi0, π_dualEFDecomp ec hi]
    exact (Category.assoc _ _ _).symm
  rw [hE] at hI
  have hG := isIso_of_isIso_opEquiv G hI
  have hG' : (G : _ ⟶ _) = eqToHom (oneShiftC_eq_dualSummand hi).symm ≫
      (entryNc ec ((-S.wt (-(q + 1 + 1))).toNat - 1 - (i + 1))
        ((-S.wt (-(q + 1 + 1))).toNat - 1 - i) ≫
      (eqToHom (oneShiftC_eq_dualSummand hi0))⟦(2 : ℤ)⟧') := by
    simp only [G, x, y]
    rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
    simp only [entryNc, Category.assoc, Functor.map_comp]
  rw [hG'] at hG
  have h3 : IsIso (entryNc ec ((-S.wt (-(q + 1 + 1))).toNat - 1 - (i + 1))
      ((-S.wt (-(q + 1 + 1))).toNat - 1 - i) ≫
      (eqToHom (oneShiftC_eq_dualSummand hi0))⟦(2 : ℤ)⟧') :=
    IsIso.of_isIso_comp_left (eqToHom (oneShiftC_eq_dualSummand hi).symm) _
  exact IsIso.of_isIso_comp_right _ ((eqToHom (oneShiftC_eq_dualSummand hi0))⟦(2 : ℤ)⟧')

omit [GradedBicategory.IsLinear B k] in
theorem isIso_of_isZero_obj {s : ℤ} (hz : IsZero (𝟙 (S.obj s)))
    {a b : ℤ} (f : (𝟙 (S.obj s))⟦a⟧ ⟶ ((𝟙 (S.obj s))⟦b⟧)⟦(2 : ℤ)⟧) : IsIso f := by
  have h1 : IsZero ((𝟙 (S.obj s))⟦a⟧) := (shiftFunctor _ a).map_isZero hz
  have h2 : IsZero (((𝟙 (S.obj s))⟦b⟧)⟦(2 : ℤ)⟧) :=
    (shiftFunctor _ (2 : ℤ)).map_isZero ((shiftFunctor _ b).map_isZero hz)
  exact ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- **The lower half of CL Lemma 3.6 under (BB_w), with free indices**: from the upper half
(`BBw.dotNondeg`) for the dual. -/
theorem BBw.dotNondegNegC_of_dual [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw) :
    ∀ i : ℕ, i + 1 < (-S.wt (-(q + 1 + 1))).toNat → IsIso (entryNc ec i (i + 1)) := by
  intro a ha
  by_cases hz : IsZero (𝟙 (S.obj (-(q + 1 + 1))))
  · exact isIso_of_isZero_obj hz _
  have hn : 0 ≤ S.dual.wt (q + 1) := by
    rw [dual_wt]
    have : S.wt (-(q + 1)) = S.wt (-(q + 1 + 1)) + 2 := by simp only [wt]; ring
    omega
  have h2 : ¬ IsZero (𝟙 (S.dual.obj (q + 1 + 1))) := by
    rwa [isZero_dual_id_iff]
  set N := (-S.wt (-(q + 1 + 1))).toNat with hN
  have hD := BBw.dotNondeg hS.dual hn h2 (dualEFDecomp ec) (N - 2 - a)
    (by rw [dual_wt_toNat]; omega)
  have hG := isIso_entryNc_of_dual ec (i := N - 2 - a) (by omega) hD
  have e1 : N - 1 - (N - 2 - a + 1) = a := by omega
  have e2 : N - 1 - (N - 2 - a) = a + 1 := by omega
  rw [e1, e2] at hG
  exact hG

/-- **CL Lemma 3.6 for `n < -1` under (BB_w)**: every decomposition datum of `F E 1_n`
(`n ≤ 0`) has nondegenerate subdiagonal dot entries. -/
theorem BBw.dotNondegNeg [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw) {r : ℤ}
    (e : S.FEDecomp r) : DotNondegNeg e :=
  S.dotNondegNeg_of_c (s₀ := r) (s' := -(-(r + 3) + 1 + 1 + 1)) (s := -(-(r + 3) + 1 + 1))
    (t := -(-(r + 3) + 1)) (by omega) (by omega) (by omega)
    (fun ec => BBw.dotNondegNegC_of_dual (q := -(r + 3)) ec hS) e

variable [GradedBicategory.ShiftCoherence B] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]

/-- **CL Corollary 3.7 for `n < 0` under (BB_w)**: the counter-clockwise degree-zero bubble with
`-n-1` dots is an isomorphism. -/
theorem BBw.isIso_bubbleN (hS : S.BBw) {r : ℤ} (e : S.FEDecomp r) (hn : S.wt (r + 1) < 0) :
    IsIso (bubbleN e) :=
  cor_degz_bubbles_neg_of_dotNondeg e hn (fun r' _ => hS.adjHyp r') (hS.dotNondegNeg e)

/-- **CL Corollary 3.13 for `n ≤ 0` under (BB_w)**: `ζ : E F 1_n ⊕ ⊕_{[-n]} 1_n → F E 1_n` is an
isomorphism. -/
theorem BBw.isIso_zetaNeg (hS : S.BBw) {r : ℤ} (e : S.FEDecomp r) (hn : S.wt (r + 1) ≤ 0) :
    IsIso (zetaNeg e) :=
  isIso_zetaNeg_of_dotNondeg e hn (fun r' _ => hS.adjHyp r') (hS.dotNondegNeg e)

end StrongSl2

end Categorification.TwoRep
