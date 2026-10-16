/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingMixedBlocks
import Categorification.TwoRep.FurlingFamily
import Categorification.TwoRep.SumInvPointwise

/-!
# Mixed inversion for the furled action

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
Lemma `lem:g-action`, and Brundan, arXiv:1501.00350v1, Definition 1.1, (1.6)–(1.7).

For distinct base colours, the matrix of the right-adjunction mate is monomial
on the matching of relevant paths. Its matched entries are the cover mixed
crossings with invertible bent `P°` coefficients (`isIso_mate_swapCell_app`);
its discarded source and target summands vanish by cover mixed inversion.
Conjugating this matrix by the biproduct decompositions gives the mixed inversion
relation for `g`, without assuming that relation for `g`.

`MixedBlocks.isIso_mixed` is independent of the same-colour Rouquier inverse
data. `brundanMixedInversion_rouqFamilyOf` packages it for the family constructor;
the latter's `invPos`/`invNeg` inputs concern (1.8)/(1.9), not mixed inversion.
The distinct-cover-label **same-base-colour** input of the KM3 assembly is instead
supplied by `sameColour_mixedInversion`, proved in `FurlingMixedInversion`.
-/

noncomputable section
namespace Categorification.TwoRep.Furling.MixedBlocks
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
universe wk v₁ u₁ u₂ u₃ u₄
private theorem decomp_matrix {C : Type*} [Category C] [Preadditive C]
    {A B : Type*} [Fintype A] [Fintype B] {Y : A → C} {Z : B → C}
    [HasBiproduct Y] [HasBiproduct Z] {U V : C}
    (s : ∀ a, Y a ⟶ U) (r : ∀ b, V ⟶ Z b) (σ : U ⟶ V) :
    biproduct.desc s ≫ σ ≫ biproduct.lift r = matrixW (fun a b => s a ≫ σ ≫ r b) := by
  apply biproduct.hom_ext'
  intro a
  apply biproduct.hom_ext
  intro b
  simp [matrixW]

private theorem conjugate_back {C : Type*} [Category C] {U V U' V' : C}
    (e : U ≅ U') (e' : V ≅ V') (σ : U ⟶ V) (m : U' ⟶ V')
    (h : e.inv ≫ σ ≫ e'.hom = m) : σ = e.hom ≫ m ≫ e'.inv := by
  rw [← h]
  simp
variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc]
  {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc}
  {RD : QuantumGroup.UDot.WeightDatum C X Y}
  {Φ : Furling RDc RD}
  {S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc}
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {P : I → I → MvPolynomial (Fin 2) k} (D : KLR.Unfurling.UnfurlingDatum k P J)
  {i j : I} {l m n t : X}
  (h₁ : l + RD.iX j = m) (h₂ : m + RD.iX i = t)
  (h₃ : l + RD.iX i = n) (h₄ : n + RD.iX j = t)
  (N : ∀ γ : Φ.Blk n, blkCat Φ S γ.1) (δ : Φ.Blk m)

abbrev entry (x : Src (i := i) h₁ δ) (y : Tgt h₂ h₄ δ) :=
  srcIn h₁ h₃ N δ x ≫ (MixedEntry.mixed Φ S D h₁ h₂ h₃ h₄).hom.app N δ ≫ tgtOut h₂ h₄ N δ y

theorem entry_off_graph (hij : i ≠ j) (x : Src (i := i) h₁ δ) (hx : liveSrc h₁ δ x)
    (y : Tgt h₂ h₄ δ) (hne : y ≠ graphY h₁ h₂ h₃ h₄ δ x hx) :
    entry D h₁ h₂ h₃ h₄ N δ x y = 0 := by
  have hlabels : y.1.1.lbl = x.2.1.lbl → y.2.1.lbl ≠ x.1.1.lbl :=
    fun e₁ e₂ => hne (graphY_eq h₁ h₂ h₃ h₄ δ x hx y e₁ e₂).symm
  obtain ⟨⟨p, hp⟩, ⟨⟨⟨qs, b⟩, hb, hrb⟩, hq⟩⟩ := x
  subst hp
  change qs = p.src at hq
  subst qs
  obtain ⟨⟨⟨⟨rs, c⟩, hc, hrc⟩, hr⟩, s⟩ := y
  change rs = p.tgt h₁ at hr
  subst rs
  by_cases hcb : c = b
  · subst hcb
    exact chain_swap_zero (Fa Φ S h₂ (Edge.next h₁ p c hb hrc) _ rfl) _ _ _ _ _ _ _ _
      (MixedEntry.gen_mixed_projF_swap Φ S D h₁ h₂ h₃ h₄ hij N p c hb hrb hrc hx.2)
      (genE_projEb_ne S h₄ N fun h => hlabels rfl (congrArg (fun e => e.1.lbl) h).symm)
  · exact chain_zero _ _ _ _
      (MixedEntry.gen_mixed_projF_ne Φ S D h₁ h₂ h₃ h₄ hij N p b hb hrb c hc hrc (Ne.symm hcb))

variable (H : RouqUpKLR S (KLR.Unfurling.unfQ (k := k) D.arrows))
  (hcover : BrundanMixedInversion S)
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
  (hπ : ∀ a, Φ.π a = D.π a)

include H hcover hnil hπ in
theorem isIso_entry (hij : i ≠ j) (x : Src (i := i) h₁ δ) (hx : liveSrc h₁ δ x) :
    IsIso (entry D h₁ h₂ h₃ h₄ N δ x (graphY h₁ h₂ h₃ h₄ δ x hx)) := by
  obtain ⟨⟨p, hp⟩, ⟨⟨⟨qs, b⟩, hb, hrb⟩, hq⟩⟩ := x
  subst hp
  change qs = p.src at hq
  subst qs
  have hab : p.lbl ≠ b := fun e => hij (hb.symm.trans ((congrArg Φ.π e).symm.trans p.π_lbl))
  have hd : D.π p.lbl ≠ D.π b := fun e =>
    hij (hb.symm.trans (((hπ b).trans (e.symm.trans (hπ p.lbl).symm)).trans p.π_lbl))
  refine isIso_of_eq_hom (chain_swap_id (Fa Φ S h₂ (Edge.next h₁ p b hb hx.1) _ rfl) _ _ _ _ _ _ _ _
    (MixedEntry.gen_mixed_projF_swap Φ S D h₁ h₂ h₃ h₄ hij N p b hb hrb hx.1 hx.2)
    (genE_projEb S h₄ N _)) ?_
  exact isIso_mate_swapCell_app S D H hcover hnil (i = j)
    ⟨fun h => (hij h).elim, fun h => (hd h).elim⟩ hab
    (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p b hb hx.1) rfl)
    (wt_tgt h₃ (swapFst Φ p b hb hrb) rfl)
    (wt_tgt h₄ (swapSnd Φ h₃ p b hb hrb hx.2)
      (swapSnd_tgt Φ h₁ h₂ h₃ h₄ p b hb hx.1 hrb hx.2 rfl))
    (N ((swapFst Φ p b hb hrb).tgt h₃))

variable (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
include H hcover hnil hπ hzero in
theorem isIso_matrix (hij : i ≠ j) : IsIso (matrixW (entry D h₁ h₂ h₃ h₄ N δ)) :=
  isIso_matrix_of_monomial _ (graphEquiv h₁ h₂ h₃ h₄ δ)
    (fun x y hx _ hne => entry_off_graph D h₁ h₂ h₃ h₄ N δ hij x hx y hne.symm)
    (fun x hx => isIso_entry D h₁ h₂ h₃ h₄ N δ H hcover hnil hπ hij x hx)
    (fun x hx => isZero_src h₁ h₃ N δ hcover hzero hij x hx)
    (fun y hy => isZero_tgt h₂ h₄ N δ hcover hzero hij y hy)

include H hcover hnil hπ hzero in
theorem isIso_mixed_app (hij : i ≠ j) :
    IsIso ((MixedEntry.mixed Φ S D h₁ h₂ h₃ h₄).hom.app N δ) := by
  let := isIso_matrix D h₁ h₂ h₃ h₄ N δ H hcover hnil hπ hzero hij
  have hm : (srcIso h₁ h₃ N δ).inv ≫ (MixedEntry.mixed Φ S D h₁ h₂ h₃ h₄).hom.app N δ ≫
      (tgtIso h₂ h₄ N δ).hom = matrixW (entry D h₁ h₂ h₃ h₄ N δ) := decomp_matrix _ _ _
  exact isIso_of_eq_hom (conjugate_back _ _ _ _ hm) (inferInstance)

include H hcover hnil hπ hzero in
/-- Brundan (1.7) for the furled adjunctions (Webster, arXiv:1603.06311v3,
`lem:g-action`): invertibility is proved by the relevant-path matrix, not assumed. -/
theorem isIso_mixed (hij : i ≠ j) : IsIso (MixedEntry.mixed Φ S D h₁ h₂ h₃ h₄) := by
  suffices IsIso ((LinearCat.homForget _ _).map (MixedEntry.mixed Φ S D h₁ h₂ h₃ h₄))
    from isIso_of_fully_faithful (LinearCat.homForget _ _) _
  rw [LinearCat.homForget_map]
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro N
  apply (isIso_pi_iff _).2
  intro δ
  exact isIso_mixed_app D h₁ h₂ h₃ h₄ N δ H hcover hnil hπ hzero hij

end Categorification.TwoRep.Furling.MixedBlocks

namespace Categorification.TwoRep.Furling
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc} {RD : QuantumGroup.UDot.WeightDatum C X Y}
  {Φ : Furling RDc RD}
  {S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc}
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {P : I → I → MvPolynomial (Fin 2) k} {D : KLR.Unfurling.UnfurlingDatum k P J}
  (hπ : ∀ a, Φ.π a = D.π a)
  (H : RouqUpKLR S (KLR.Unfurling.unfQ (k := k) D.arrows))
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
  {Q : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))

variable
  (invPos : ∀ (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c),
    0 ≤ RD.pair (RD.iY i) b →
    SumInvTo (RightwardCrossing.sigma (adj Φ S i h₂).unit
        ((rouqData Φ S D).cross i i h₁ h₂ h₁ h₂) (adj Φ S i h₁).counit)
      (fun n => F Φ S i h₁ ◁ powComp ((rouqData Φ S D).dot i h₁) n ≫ (adj Φ S i h₁).counit)
      (RD.pair (RD.iY i) b).toNat)
  (invNeg : ∀ (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c),
    RD.pair (RD.iY i) b ≤ 0 →
    SumInvFrom (RightwardCrossing.sigma (adj Φ S i h₂).unit
        ((rouqData Φ S D).cross i i h₁ h₂ h₁ h₂) (adj Φ S i h₁).counit)
      (fun n => (adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) n ▷ F Φ S i h₂)
      (-RD.pair (RD.iY i) b).toNat)
variable (hcover : BrundanMixedInversion S)

include hcover in
/-- Brundan, arXiv:1501.00350v1, (1.7), for the furled family in Webster,
arXiv:1603.06311v3, `lem:g-action`; the same-colour
Rouquier inverses in the family constructor are independent of this mixed relation. -/
theorem brundanMixedInversion_rouqFamilyOf :
    BrundanMixedInversion (rouqFamilyOf hπ H hnil hzero hPQ invPos invNeg) := by
  intro i j hij a b c d hj hi' hi hj'
  exact MixedBlocks.isIso_mixed D hj hi' hi hj' H hcover hnil hπ hzero hij
end Categorification.TwoRep.Furling
