/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingMixed
import Categorification.TwoRep.FurlingZero
import Categorification.TwoRep.SumInvBiprod
import Categorification.TwoRep.RouqLocTransport

/-!
# Furling: assembling the inverses of Rouquier's maps from blocks

For the furled action `g` of a Rouquier family `g̃` (B. Webster, *Unfurling
Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2.3, Lemma with label `lem:g-action`),
the inverses of Rouquier's maps (J. Brundan, *On the definition of Kac–Moody 2-category*,
arXiv:1501.00350v1, (1.8) and (1.9)) are the hypotheses `invPos`, `invNeg` of
`Furling.rouqFamilyOf`. We reduce them to the *shift-zero* blocks.

On a block `δ`, `(F_i E_i N)_δ` and `(E_i F_i N)_δ` split as biproducts of shift-zero summands
(`E_a F_a`, `F_c E_c`) and mixed summands (`srcIso`, `tgtIso`). In these decompositions the
rightward crossing `σ` is block diagonal (`sM_sigma_rZ'`, `sZ_sigma_rM'`), its mixed block is
invertible (`isIso_mixed`), and the dotted caps and cups of Rouquier's maps vanish on the mixed
summands (`sM_pow_counit`, `unit_pow_rM'`). Hence a sum inverse of the shift-zero block gives one
of `σ` on the block (`blockPos`, `blockNeg`), and these globalize over objects and blocks
(`invPosOf`, `invNegOf`).

## Main definitions

* `Furling.blockPos`, `Furling.blockNeg`: Brundan (1.8), (1.9) on a block, from the shift-zero
  block.
* `Furling.invPosOf`, `Furling.invNegOf`: the hypotheses `invPos`, `invNeg` of
  `Furling.rouqFamilyOf`, from the shift-zero blocks.
* `Furling.rouqFamilyOfBlocks`: the Rouquier family of `g`, given the shift-zero block inverses
  and the mixed inversion hypothesis `hmix`.
* `Furling.rouqFamilyOfPairing`: constructs those inverses from the spectral coproduct
  theorem and a pairing identity on nonzero blocks; its concrete cyclotomic-cover
  consumer is `KLR.Unfurling.coverRouqFamily`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe wk v₁ u₁ u₂ u₃ u₄

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-! ## Block-diagonal maps between binary biproducts -/

section Generic

variable {D' : Type*} [Category D'] [Preadditive D'] [HasBinaryBiproducts D']
  {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
  {Y : ι → D'} {Z : κ → D'} {Y' : ι' → D'} {Z' : κ' → D'} [HasBiproduct Y] [HasBiproduct Z]
  [HasBiproduct Y'] [HasBiproduct Z'] {A B T : D'}

omit [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'] in
/-- A map between decomposed objects with vanishing off-diagonal blocks is the direct sum of
its diagonal blocks. -/
theorem desc_comp_lift_eq_map (s : ∀ i, Y i ⟶ A) (s' : ∀ j, Z j ⟶ A) (σ : A ⟶ B)
    (r : ∀ i, B ⟶ Y' i) (r' : ∀ j, B ⟶ Z' j) (h₁ : ∀ j i, s' j ≫ σ ≫ r i = 0)
    (h₂ : ∀ i j, s i ≫ σ ≫ r' j = 0) :
    biprod.desc (biproduct.desc s) (biproduct.desc s') ≫ σ ≫
        biprod.lift (biproduct.lift r) (biproduct.lift r') =
      biprod.map (biproduct.desc s ≫ σ ≫ biproduct.lift r)
        (matrixW fun j j' => s' j ≫ σ ≫ r' j') := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext
  · simp
  · apply biproduct.hom_ext'; intro i; apply biproduct.hom_ext; intro j
    simp [h₂]
  · apply biproduct.hom_ext'; intro j; apply biproduct.hom_ext; intro i
    simp [h₁]
  · apply biproduct.hom_ext'; intro j; apply biproduct.hom_ext; intro j'
    simp [matrixW]

omit [Fintype ι] [Fintype κ] in
/-- A map out of a decomposed object vanishing on the second summands factors through the
first projection. -/
theorem desc_comp_eq_fst (s : ∀ i, Y i ⟶ A) (s' : ∀ j, Z j ⟶ A) (c : A ⟶ T)
    (h : ∀ j, s' j ≫ c = 0) :
    biprod.desc (biproduct.desc s) (biproduct.desc s') ≫ c =
      biprod.fst ≫ biproduct.desc s ≫ c := by
  apply biprod.hom_ext'
  · simp
  · apply biproduct.hom_ext'; intro j
    simp [h]

omit [Fintype ι] [Fintype κ] in
/-- A map into a decomposed object vanishing on the second summands factors through the first
inclusion. -/
theorem comp_lift_eq_inl (c : T ⟶ A) (r : ∀ i, A ⟶ Y i) (r' : ∀ j, A ⟶ Z j)
    (h : ∀ j, c ≫ r' j = 0) :
    c ≫ biprod.lift (biproduct.lift r) (biproduct.lift r') =
      (c ≫ biproduct.lift r) ≫ biprod.inl := by
  apply biprod.hom_ext
  · simp
  · apply biproduct.hom_ext; intro j
    simp [h]

omit [HasBinaryBiproducts D'] [Preadditive D'] in
/-- Conjugating back: `σ = e ≫ m ≫ e'⁻¹` from `e⁻¹ ≫ σ ≫ e' = m`. -/
theorem eq_hom_comp_inv {A' B' : D'} (e : A ≅ A') (e' : B ≅ B') (σ : A ⟶ B) (m : A' ⟶ B')
    (h : e.inv ≫ σ ≫ e'.hom = m) : σ = e.hom ≫ m ≫ e'.symm.hom := by
  rw [← h]; simp

omit [HasBinaryBiproducts D'] [Preadditive D'] in
/-- Conjugating back a map out of `A`: `c = e ≫ m ≫ 𝟙` from `e⁻¹ ≫ c = m`. -/
theorem eq_hom_comp_id {A' : D'} (e : A ≅ A') (c : A ⟶ T) (m : A' ⟶ T) (h : e.inv ≫ c = m) :
    c = e.hom ≫ m ≫ 𝟙 T := by
  rw [← h]; simp

omit [HasBinaryBiproducts D'] [Preadditive D'] in
/-- Conjugating back a map into `A`: `c = 𝟙 ≫ m ≫ e⁻¹` from `c ≫ e = m`. -/
theorem eq_id_comp_inv {A' : D'} (e : A ≅ A') (c : T ⟶ A) (m : T ⟶ A') (h : c ≫ e.hom = m) :
    c = 𝟙 T ≫ m ≫ e.symm.hom := by
  rw [← h]; simp

end Generic

namespace Furling

variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc} {RD : QuantumGroup.UDot.WeightDatum C X Y}
  {Φ : Furling RDc RD}
  {S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc}
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {P : I → I → MvPolynomial (Fin 2) k}

/-! ## Rouquier's maps on a block -/

section Block

variable (D : KLR.Unfurling.UnfurlingDatum k P J)
  {i : I} {l l' l'' : X} (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')
  (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (δ : Φ.Blk l')
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))

/-- In the decompositions `srcIso`, `tgtIso` of a block, `σ` is the direct sum of its
shift-zero block and its mixed block. -/
theorem sigma_eq_conj :
    (sigma Φ S D h₁ h₂).hom.app N δ = (srcIso h₁ N δ hzero).hom ≫
      biprod.map (biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
          biproduct.lift (rZ' h₂ N δ))
        (matrixW fun x y => sM h₁ N δ x ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫ rM' h₂ N δ y) ≫
      (tgtIso h₂ N δ hzero).symm.hom :=
  eq_hom_comp_inv _ _ _ _
    (desc_comp_lift_eq_map _ _ _ _ _ (sM_sigma_rZ' D h₁ h₂ N δ) (sZ_sigma_rM' D h₁ h₂ N δ))

/-- In the decomposition `srcIso` of a block, the dotted caps of Rouquier's map (1.8) factor
through the shift-zero summands. -/
theorem caps_eq_conj (m : ℕ) :
    (F Φ S i h₁ ◁ powComp ((rouqData Φ S D).dot i h₁) m ≫ (adj Φ S i h₁).counit).hom.app N δ =
      (srcIso h₁ N δ hzero).hom ≫ (biprod.fst ≫ biproduct.desc (sZ h₁ N δ) ≫
        (F Φ S i h₁ ◁ powComp ((rouqData Φ S D).dot i h₁) m ≫
          (adj Φ S i h₁).counit).hom.app N δ) ≫ 𝟙 _ :=
  eq_hom_comp_id _ _ _ (desc_comp_eq_fst _ _ _ fun x => sM_pow_counit D h₁ N δ x m)

/-- In the decomposition `tgtIso` of a block, the dotted cups of Rouquier's map (1.9) factor
through the shift-zero summands. -/
theorem cups_eq_conj (m : ℕ) :
    ((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) m ▷ F Φ S i h₂).hom.app N δ =
      𝟙 _ ≫ ((((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) m ▷
          F Φ S i h₂).hom.app N δ ≫ biproduct.lift (rZ' h₂ N δ)) ≫ biprod.inl) ≫
        (tgtIso h₂ N δ hzero).symm.hom :=
  eq_id_comp_inv _ _ _ (comp_lift_eq_inl _ _ _ fun y => unit_pow_rM' D h₂ N δ y m)

variable (hmix : ∀ (j : I) (a b : J), a ≠ b → Φ.π a = j → Φ.π b = j → ∀ {x y y' z : Xc}
    (e₁ : x + RDc.iX a = y) (e₂ : y + RDc.iX b = z) (e₃ : x + RDc.iX b = y')
    (e₄ : y' + RDc.iX a = z) (M : (S.obj y' : Type u₂)),
    IsIso ((S.adj b e₂).unit.hom.app ((S.E a e₁).obj.obj ((S.F b e₃).obj.obj M)) ≫
      (S.F b e₂).obj.map ((swapCell S D (j = j) e₁ e₂ e₃ e₄).hom.app ((S.F b e₃).obj.obj M) ≫
        (S.E a e₄).obj.map ((S.adj b e₃).counit.hom.app M))))

/-- **Brundan (1.8) on a block, from the shift-zero block.** Given a sum inverse `Z0` of the
shift-zero block of `σ` (between the summands `E_a F_a` and `F_c E_c`) together with the
dotted caps restricted to the shift-zero summands, a sum inverse of `σ` with the dotted caps on
the block `δ`. Hypotheses: the 1-morphisms of irrelevant edges vanish (`hzero`); the mixed
sideways crossings of the cover are invertible (`hmix`, see `isIso_mixed`). -/
def blockPos {n : ℕ}
    (Z0 : SumInvTo (biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
        biproduct.lift (rZ' h₂ N δ))
      (fun m => biproduct.desc (sZ h₁ N δ) ≫ (F Φ S i h₁ ◁
        powComp ((rouqData Φ S D).dot i h₁) m ≫ (adj Φ S i h₁).counit).hom.app N δ) n) :
    SumInvTo ((sigma Φ S D h₁ h₂).hom.app N δ)
      (fun m => (F Φ S i h₁ ◁ powComp ((rouqData Φ S D).dot i h₁) m ≫
        (adj Φ S i h₁).counit).hom.app N δ) n :=
  haveI := isIso_mixed D h₁ h₂ N δ hzero hmix
  (Z0.biprodMap _).conj (srcIso h₁ N δ hzero) (tgtIso h₂ N δ hzero).symm (Iso.refl _)
    (sigma_eq_conj D h₁ h₂ N δ hzero) (caps_eq_conj D h₁ N δ hzero)

/-- **Brundan (1.9) on a block, from the shift-zero block.** Given a sum inverse `Z0` of the
shift-zero block of `σ` (between the summands `E_a F_a` and `F_c E_c`) together with the
dotted cups projected to the shift-zero summands, a sum inverse of `σ` with the dotted cups on
the block `δ`. Hypotheses: as for `blockPos`. -/
def blockNeg {n : ℕ}
    (Z0 : SumInvFrom (biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
        biproduct.lift (rZ' h₂ N δ))
      (fun m => ((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) m ▷
        F Φ S i h₂).hom.app N δ ≫ biproduct.lift (rZ' h₂ N δ)) n) :
    SumInvFrom ((sigma Φ S D h₁ h₂).hom.app N δ)
      (fun m => ((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) m ▷
        F Φ S i h₂).hom.app N δ) n :=
  haveI := isIso_mixed D h₁ h₂ N δ hzero hmix
  (Z0.biprodMap _).conj (tgtIso h₂ N δ hzero).symm (srcIso h₁ N δ hzero) (Iso.refl _)
    (sigma_eq_conj D h₁ h₂ N δ hzero) (cups_eq_conj D h₂ N δ hzero)

end Block

/-! ## Globalization -/

section Global

variable {D : KLR.Unfurling.UnfurlingDatum k P J}
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
  (hmix : ∀ (j : I) (a b : J), a ≠ b → Φ.π a = j → Φ.π b = j → ∀ {x y y' z : Xc}
    (e₁ : x + RDc.iX a = y) (e₂ : y + RDc.iX b = z) (e₃ : x + RDc.iX b = y')
    (e₄ : y' + RDc.iX a = z) (M : (S.obj y' : Type u₂)),
    IsIso ((S.adj b e₂).unit.hom.app ((S.E a e₁).obj.obj ((S.F b e₃).obj.obj M)) ≫
      (S.F b e₂).obj.map ((swapCell S D (j = j) e₁ e₂ e₃ e₄).hom.app ((S.F b e₃).obj.obj M) ≫
        (S.E a e₄).obj.map ((S.adj b e₃).counit.hom.app M))))

/-- **Brundan (1.8) for `g`, from the shift-zero blocks**: the hypothesis `invPos` of
`Furling.rouqFamilyOf`, given, for each weight `λ = l'` with `⟨h_i, λ⟩ ≥ 0`, each object `N`
and each block `δ`, a sum inverse `Z0pos` of the shift-zero block of `σ` with the dotted caps
restricted to the shift-zero summands (`blockPos`). Hypotheses: `hzero`, `hmix` as for
`blockPos`. -/
def invPosOf
    (Z0pos : ∀ (i : I) {l l' l'' : X} (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')
      (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (δ : Φ.Blk l'), 0 ≤ RD.pair (RD.iY i) l' →
      SumInvTo (biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
          biproduct.lift (rZ' h₂ N δ))
        (fun m => biproduct.desc (sZ h₁ N δ) ≫ (F Φ S i h₁ ◁
          powComp ((rouqData Φ S D).dot i h₁) m ≫ (adj Φ S i h₁).counit).hom.app N δ)
        (RD.pair (RD.iY i) l').toNat)
    (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    (hpos : 0 ≤ RD.pair (RD.iY i) b) :
    SumInvTo (RightwardCrossing.sigma (adj Φ S i h₂).unit
        ((rouqData Φ S D).cross i i h₁ h₂ h₁ h₂) (adj Φ S i h₁).counit)
      (fun n => F Φ S i h₁ ◁ powComp ((rouqData Φ S D).dot i h₁) n ≫ (adj Φ S i h₁).counit)
      (RD.pair (RD.iY i) b).toNat :=
  SumInvTo.ofFullyFaithful (LinearCat.homForget _ _)
    (SumInvTo.ofApp fun N => SumInvTo.pi fun δ =>
      blockPos D h₁ h₂ N δ hzero hmix (Z0pos i h₁ h₂ N δ hpos))

/-- **Brundan (1.9) for `g`, from the shift-zero blocks**: the hypothesis `invNeg` of
`Furling.rouqFamilyOf`, given, for each weight `λ = l'` with `⟨h_i, λ⟩ ≤ 0`, each object `N`
and each block `δ`, a sum inverse `Z0neg` of the shift-zero block of `σ` with the dotted cups
projected to the shift-zero summands (`blockNeg`). Hypotheses: `hzero`, `hmix` as for
`blockNeg`. -/
def invNegOf
    (Z0neg : ∀ (i : I) {l l' l'' : X} (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')
      (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (δ : Φ.Blk l'), RD.pair (RD.iY i) l' ≤ 0 →
      SumInvFrom (biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
          biproduct.lift (rZ' h₂ N δ))
        (fun m => ((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) m ▷
          F Φ S i h₂).hom.app N δ ≫ biproduct.lift (rZ' h₂ N δ))
        (-RD.pair (RD.iY i) l').toNat)
    (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c)
    (hneg : RD.pair (RD.iY i) b ≤ 0) :
    SumInvFrom (RightwardCrossing.sigma (adj Φ S i h₂).unit
        ((rouqData Φ S D).cross i i h₁ h₂ h₁ h₂) (adj Φ S i h₁).counit)
      (fun n => (adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) n ▷ F Φ S i h₂)
      (-RD.pair (RD.iY i) b).toNat :=
  SumInvFrom.ofFullyFaithful (LinearCat.homForget _ _)
    (SumInvFrom.ofApp fun N => SumInvFrom.pi fun δ =>
      blockNeg D h₁ h₂ N δ hzero hmix (Z0neg i h₁ h₂ N δ hneg))

variable (hπ : ∀ a, Φ.π a = D.π a)
  (H : RouqUpKLR S (KLR.Unfurling.unfQ (k := k) D.arrows))
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
  {Q : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))

/-- **The Rouquier family of `g`, from the shift-zero blocks** (Webster, arXiv:1603.06311v3,
§2.3, `lem:g-action`): `Furling.rouqFamilyOf` with `invPos := invPosOf hzero hmix Z0pos` and
`invNeg := invNegOf hzero hmix Z0neg`. Besides the hypotheses of the cover (`hπ`, `H`, `hnil`,
`hzero`, `hPQ`), the only remaining inputs are the shift-zero block sum inverses `Z0pos`,
`Z0neg` (to be supplied from the coproduct theorem, `th:coproduct`, on each block) and `hmix`
(Brundan's inversion of the mixed sideways crossings `E_a F_b → F_b E_a`, `a ≠ b`, for the
cover). -/
def rouqFamilyOfBlocks
    (Z0pos : ∀ (i : I) {l l' l'' : X} (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')
      (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (δ : Φ.Blk l'), 0 ≤ RD.pair (RD.iY i) l' →
      SumInvTo (biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
          biproduct.lift (rZ' h₂ N δ))
        (fun m => biproduct.desc (sZ h₁ N δ) ≫ (F Φ S i h₁ ◁
          powComp ((rouqData Φ S D).dot i h₁) m ≫ (adj Φ S i h₁).counit).hom.app N δ)
        (RD.pair (RD.iY i) l').toNat)
    (Z0neg : ∀ (i : I) {l l' l'' : X} (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')
      (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (δ : Φ.Blk l'), RD.pair (RD.iY i) l' ≤ 0 →
      SumInvFrom (biproduct.desc (sZ h₁ N δ) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
          biproduct.lift (rZ' h₂ N δ))
        (fun m => ((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) m ▷
          F Φ S i h₂).hom.app N δ ≫ biproduct.lift (rZ' h₂ N δ))
        (-RD.pair (RD.iY i) l').toNat) :
    RouqFamily (B := LinearCat.{wk, max u₁ v₁, max u₁ u₂} k) RD :=
  rouqFamilyOf hπ H hnil hzero hPQ (invPosOf hzero hmix Z0pos) (invNegOf hzero hmix Z0neg)

theorem rouqFamilyOfBlocks_toRouqData (Z0pos Z0neg) :
    (rouqFamilyOfBlocks hzero hmix hπ H hnil hPQ Z0pos Z0neg).toRouqData = rouqData Φ S D :=
  rfl

variable (hpairOrZero : ∀ (i : I) (β : J →₀ ℤ),
    RD.pair (RD.iY i) (Φ.wtG β) =
      ∑ t : Fin (nLbl Φ i β), RDc.pair (RDc.iY (lab Φ i β t)) (Φ.wtT β) ∨
    ∀ M : blkCat Φ S β, IsZero M)

/-- Positive shift-zero inverse when the pairing identity is needed only on nonzero blocks. -/
def zeroPosOfPairing (i : I) {l l' l'' : X} (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')
    (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (δ : Φ.Blk l') (hp : 0 ≤ RD.pair (RD.iY i) l') := by
  classical
  exact if hc : RD.pair (RD.iY i) (Φ.wtG δ.1) =
      ∑ t : Fin (nLbl Φ i δ.1), RDc.pair (RDc.iY (lab Φ i δ.1 t)) (Φ.wtT δ.1) then
    zeroPos (S := S) (D := D) (h₁ := h₁) (h₂ := h₂) (N := N) (hzero := hzero)
      (hnil := hnil) (funext hπ) δ ((congrArg (RD.pair (RD.iY i)) δ.2).symm.trans hc) hp
  else zeroPosOfIsZero (S := S) (D := D) (h₁ := h₁) (h₂ := h₂) (N := N) δ
    ((hpairOrZero i δ.1).resolve_left hc (N δ)) _

/-- Negative shift-zero inverse when the pairing identity is needed only on nonzero blocks. -/
def zeroNegOfPairing (i : I) {l l' l'' : X} (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')
    (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (δ : Φ.Blk l') (hp : RD.pair (RD.iY i) l' ≤ 0) := by
  classical
  exact if hc : RD.pair (RD.iY i) (Φ.wtG δ.1) =
      ∑ t : Fin (nLbl Φ i δ.1), RDc.pair (RDc.iY (lab Φ i δ.1 t)) (Φ.wtT δ.1) then
    zeroNeg (S := S) (D := D) (h₁ := h₁) (h₂ := h₂) (N := N) (hzero := hzero)
      (hnil := hnil) (funext hπ) δ ((congrArg (RD.pair (RD.iY i)) δ.2).symm.trans hc) hp
  else zeroNegOfIsZero (S := S) (D := D) (h₁ := h₁) (h₂ := h₂) (N := N) δ
    ((hpairOrZero i δ.1).resolve_left hc (N δ)) _

/-- Construct the furled family from the pairing on nonzero blocks, not assumed block inverses. -/
def rouqFamilyOfPairing : RouqFamily (B := LinearCat.{wk, max u₁ v₁, max u₁ u₂} k) RD :=
  rouqFamilyOfBlocks hzero hmix hπ H hnil hPQ
    (zeroPosOfPairing hzero hπ hnil hpairOrZero) (zeroNegOfPairing hzero hπ hnil hpairOrZero)


end Global

end Furling

end Categorification.TwoRep
