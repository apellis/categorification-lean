/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverVanishing
import Categorification.KLR.Unfurling.BranchedCover
import Categorification.TwoRep.Furling

/-!
# The furling data of the unfurled product family

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2.3, Lemma with
label `lem:g-action`, and the proof of the theorem with label `nondegenerate`. The representation
of `g̃` used there is the product `coverProduct` of a lowest weight cyclotomic family on the labels
`Ĩ₋` and a highest weight one on the labels `Ĩ₊`, with no arrows between the two parts. The
generators of `g` act on it by the sums `E_i = ⊕_{a over i} E_a` of `TwoRep.Furling`. This file
supplies the inputs of that construction for an unfurling datum `D` on `Jm ⊕ Jp` (the labels
`Ĩ₋`, `Ĩ₊`) without arrows between the two parts:

* the furling datum `coverFurling`: base weights `x̃₀ = (-Λm, Λp)` (each with zero root-lattice
  degree) and `μ`, and the relevant edges `coverRel`: at a block `β`, a label is relevant if it
  carries weight, occurs in the cyclotomic block of `β` (`β_a > 0` on `Jm`, `β_a < -1` on `Jp`),
  or is joined by an arrow to another label of the support of `β`. Only finitely many labels over
  a colour are adjacent to a given label (`finite_adjacent`: the arrows are root multiplicities
  of a nonzero polynomial), so the relevant labels are finite in number;
* `coverFurling_isZero`: `E_a` and `F_a` vanish on irrelevant edges;
* `coverFurling_isZero_obj`: the blocks outside `CoverAdm` (`β ≥ 0` on `Jm`, `β ≤ 0` on `Jp`)
  are zero categories, since a cyclotomic weight space without blocks is zero;
* `coverFurling_pair`: at an admissible block, the pairing of the colour `i` with the weight of
  `g` is the sum over the relevant labels over `i` of the pairings with the weight of `g̃`. This is
  the count of the identity summands in Rouquier's isomorphism for `g`. It holds under the
  branched-cover identity `hcover` (`UnfurlingDatum.ofClosure_finsum_arrows_eq_dij`) and the
  base identity `hμ`;
* `coverProduct_upKLR_unfQ`: the product family satisfies the upward relations for the
  parameters `unfQ D.arrows` of the whole unfurled graph.
-/

open CategoryTheory CategoryTheory.Limits MvPolynomial

noncomputable section

namespace Categorification.KLR.Unfurling

open QuantumGroup QuantumGroup.UDot TwoRep CyclotomicAction

universe u v w u₄

/-! ## Finitely many neighbours -/

namespace UnfurlingDatum

variable {I : Type*} {J : Type*} {L : Type*} [Field L] {P : I → I → MvPolynomial (Fin 2) L}
  (D : UnfurlingDatum L P J)

private theorem mem_roots_of_rootMultiplicity_ne_zero {p : Polynomial L} {x : L}
    (h : p.rootMultiplicity x ≠ 0) : x ∈ p.roots := by
  classical
  rw [← Polynomial.count_roots] at h
  exact Multiset.count_ne_zero.1 h

/-- **A label has finitely many neighbours over each vertex** (Webster, arXiv:1603.06311v3, §2,
definition with label `def:tilde-I`: the arrows count the roots of a nonzero polynomial; the
statement is implicit there). -/
theorem finite_adjacent (c : J) (i : I) :
    {a | D.π a = i ∧ (D.arrows a c ≠ 0 ∨ D.arrows c a ≠ 0)}.Finite := by
  classical
  by_cases hi : i = D.π c
  · refine Set.Finite.subset Set.finite_empty fun a ⟨ha, h⟩ => ?_
    rcases h with h | h
    · exact h (D.arrows_of_eq a c (ha.trans hi))
    · exact h (D.arrows_of_eq c a (hi.symm.trans ha.symm))
  let w := (D.pw c).coeff 0
  let S : Finset L := (aeval ![Polynomial.X, Polynomial.C w] (P (D.π c) i)).roots.toFinset ∪
    (aeval ![Polynomial.C w, Polynomial.X] (P i (D.π c))).roots.toFinset
  let g : {a // D.π a = i} → L := fun a => (D.pw a.1).coeff 0
  have hg : Function.Injective g := fun a a' h =>
    Subtype.ext (D.pw_coeff_zero_inj _ _ (a.2.trans a'.2.symm) h)
  have hfin : (g ⁻¹' (S : Set L)).Finite := S.finite_toSet.preimage hg.injOn
  refine (hfin.image Subtype.val).subset fun a ⟨ha, h⟩ => ⟨⟨a, ha⟩, ?_, rfl⟩
  simp only [Set.mem_preimage, Finset.coe_union, Set.mem_union, Finset.mem_coe,
    Multiset.mem_toFinset, S, g]
  have hne : D.π a ≠ D.π c := ha ▸ hi
  rcases h with h | h
  · left
    rw [D.arrows_eq_rootMultiplicity_fst hne, ha] at h
    exact mem_roots_of_rootMultiplicity_ne_zero h
  · right
    rw [D.arrows_eq_rootMultiplicity_snd (Ne.symm hne), ha] at h
    exact mem_roots_of_rootMultiplicity_ne_zero h

end UnfurlingDatum

/-! ## The two parts of the labels -/

variable {I : Type*} {L : Type v} [Field L] {P : I → I → MvPolynomial (Fin 2) L}
  {Jm Jp : Type u} [DecidableEq Jm] [DecidableEq Jp] (D : UnfurlingDatum L P (Jm ⊕ Jp))

/-- The arrows among the labels of `Jm`. -/
def arrowsNeg (a b : Jm) : ℕ := D.arrows (.inl a) (.inl b)

/-- The arrows among the labels of `Jp`. -/
def arrowsPos (a b : Jp) : ℕ := D.arrows (.inr a) (.inr b)

/-- There are no arrows between the two parts `Jm` and `Jp`. -/
def NoCrossArrows : Prop := ∀ (a : Jm) (b : Jp), D.arrows (.inl a) (.inr b) = 0 ∧
  D.arrows (.inr b) (.inl a) = 0

/-- The weight datum of the product family. -/
abbrev coverProdWeight :=
  (coverWeight (arrowsNeg D)).prod (coverWeight (arrowsPos D))

/-- The pairing of the coweight of a label with the root of a label: `2` on the diagonal and
`-(n_{ab} + n_{ba})` off it. -/
def coverDot (a c : Jm ⊕ Jp) : ℤ := if a = c then 2 else -((D.arrows a c + D.arrows c a : ℕ) : ℤ)

variable {D}

theorem coverProdWeight_pair_iY_iX (hD : NoCrossArrows D) (a c : Jm ⊕ Jp) :
    (coverProdWeight D).pair ((coverProdWeight D).iY a) ((coverProdWeight D).iX c) =
      coverDot D a c := by
  rcases a with a | a <;> rcases c with c | c <;>
    simp only [WeightDatum.prod_pair, WeightDatum.prod_iY_inl, WeightDatum.prod_iY_inr,
      WeightDatum.prod_iX_inl, WeightDatum.prod_iX_inr, coverWeight_pair_iY, coverWeight_iX,
      map_zero, AddMonoidHom.zero_apply, add_zero, zero_add]
  · by_cases h : a = c
    · subst h
      simp [coverDot]
    · rw [coverCartan_dot_of_ne _ h]
      simp [coverDot, h, arrowsNeg]
  · simp [coverDot, (hD a c).1, (hD a c).2]
  · simp [coverDot, (hD c a).1, (hD c a).2]
  · by_cases h : a = c
    · subst h
      simp [coverDot]
    · rw [coverCartan_dot_of_ne _ h]
      simp [coverDot, h, arrowsPos]

/-- The pairing with a weight `x̃₀ + ∑ β_c α̃_c`. -/
theorem coverProdWeight_pair_add_sum (hD : NoCrossArrows D) (a : Jm ⊕ Jp)
    (x : ((Jm → ℤ) × (Jm →₀ ℤ)) × ((Jp → ℤ) × (Jp →₀ ℤ))) (β : Jm ⊕ Jp →₀ ℤ) :
    (coverProdWeight D).pair ((coverProdWeight D).iY a)
        (x + β.sum fun c n => n • (coverProdWeight D).iX c) =
      (coverProdWeight D).pair ((coverProdWeight D).iY a) x +
        β.sum fun c n => n * coverDot D a c := by
  rw [map_add, map_finsuppSum]
  congr 1
  refine Finsupp.sum_congr fun c _ => ?_
  rw [map_zsmul, coverProdWeight_pair_iY_iX hD, smul_eq_mul]

/-! ## The furling datum -/

variable (D) (Λm : Jm → ℕ) (Λp : Jp → ℕ)

/-- A label is adjacent to the support of `β`: an arrow joins it to another label `c` with
`β_c ≠ 0`. -/
def CoverAdj (β : Jm ⊕ Jp →₀ ℤ) (a : Jm ⊕ Jp) : Prop :=
  ∃ c ∈ β.support, c ≠ a ∧ (D.arrows a c ≠ 0 ∨ D.arrows c a ≠ 0)

/-- **The relevant edges** `β → β + a` of the product family: the label `a` carries weight, lies
in the cyclotomic block of `β` (`β_a > 0` on `Jm`; on `Jp` the block of the target, `β_a < -1`),
or is adjacent to the support of `β`. -/
def coverRel (β : Jm ⊕ Jp →₀ ℤ) : Jm ⊕ Jp → Prop
  | .inl a => Λm a ≠ 0 ∨ 0 < β (.inl a) ∨ CoverAdj D β (.inl a)
  | .inr b => Λp b ≠ 0 ∨ β (.inr b) < -1 ∨ CoverAdj D β (.inr b)

/-- The admissible blocks: those whose cyclotomic weight spaces can be nonempty, `β ≥ 0` on
`Jm` and `β ≤ 0` on `Jp`. -/
def CoverAdm (β : Jm ⊕ Jp →₀ ℤ) : Prop :=
  (∀ a : Jm, 0 ≤ β (.inl a)) ∧ ∀ b : Jp, β (.inr b) ≤ 0

/-- The base weight `x̃₀ = (-Λm, Λp)` of the product family. -/
def coverBase : ((Jm → ℤ) × (Jm →₀ ℤ)) × ((Jp → ℤ) × (Jp →₀ ℤ)) :=
  ((fun a => -(Λm a : ℤ), 0), (fun b => (Λp b : ℤ), 0))

/-- The value of the base weight at a label: `-Λm` on `Jm`, `Λp` on `Jp`. -/
def coverBaseVal : Jm ⊕ Jp → ℤ
  | .inl a => -(Λm a : ℤ)
  | .inr b => (Λp b : ℤ)

theorem coverProdWeight_pair_base (a : Jm ⊕ Jp) :
    (coverProdWeight D).pair ((coverProdWeight D).iY a) (coverBase Λm Λp) =
      coverBaseVal Λm Λp a := by
  rcases a with a | a <;>
    simp [coverBase, coverBaseVal, coverWeight, coverPair_single]

variable {D Λm Λp}

omit [DecidableEq Jm] [DecidableEq Jp] in
/-- The labels over `i` that carry weight, lie in the support of `β`, or are adjacent to it. -/
private theorem coverRel_finite_aux (hΛm : ∀ i, ({a | D.π (.inl a) = i ∧ Λm a ≠ 0} : Set Jm).Finite)
    (hΛp : ∀ i, ({a | D.π (.inr a) = i ∧ Λp a ≠ 0} : Set Jp).Finite) (β : Jm ⊕ Jp →₀ ℤ) (i : I) :
    ({a | D.π a = i ∧ (coverBaseVal Λm Λp a ≠ 0 ∨ a ∈ β.support ∨ CoverAdj D β a)} :
      Set (Jm ⊕ Jp)).Finite := by
  have h₁ : (Sum.inl '' {a | D.π (.inl a) = i ∧ Λm a ≠ 0} ∪
      Sum.inr '' {a | D.π (.inr a) = i ∧ Λp a ≠ 0} ∪
      (β.support : Set (Jm ⊕ Jp)) ∪
      ⋃ c ∈ (β.support : Set (Jm ⊕ Jp)),
        {a | D.π a = i ∧ (D.arrows a c ≠ 0 ∨ D.arrows c a ≠ 0)}).Finite :=
    ((((hΛm i).image _).union ((hΛp i).image _)).union β.support.finite_toSet).union
      (β.support.finite_toSet.biUnion fun c _ => D.finite_adjacent c i)
  refine h₁.subset fun a ⟨ha, h⟩ => ?_
  rcases h with h | h | ⟨c, hc, -, hac⟩
  · rcases a with a | a
    · exact Or.inl (Or.inl (Or.inl ⟨a, ⟨ha, fun h0 => h (by simp [coverBaseVal, h0])⟩, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨a, ⟨ha, fun h0 => h (by simp [coverBaseVal, h0])⟩, rfl⟩))
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Set.mem_biUnion hc ⟨ha, hac⟩)

omit [DecidableEq Jm] [DecidableEq Jp] in
theorem coverRel_imp (β : Jm ⊕ Jp →₀ ℤ) (a : Jm ⊕ Jp) (h : coverRel D Λm Λp β a) :
    coverBaseVal Λm Λp a ≠ 0 ∨ a ∈ β.support ∨ CoverAdj D β a := by
  rcases a with a | a
  · rcases h with h | h | h
    · exact Or.inl (by simpa [coverBaseVal] using h)
    · exact Or.inr (Or.inl (Finsupp.mem_support_iff.2 h.ne'))
    · exact Or.inr (Or.inr h)
  · rcases h with h | h | h
    · exact Or.inl (by simpa [coverBaseVal] using h)
    · exact Or.inr (Or.inl (Finsupp.mem_support_iff.2 (by omega)))
    · exact Or.inr (Or.inr h)

omit [DecidableEq Jm] [DecidableEq Jp] in
theorem coverRel_sub_imp (γ : Jm ⊕ Jp →₀ ℤ) (a : Jm ⊕ Jp)
    (h : coverRel D Λm Λp (γ - Finsupp.single a 1) a) :
    coverBaseVal Λm Λp a ≠ 0 ∨ a ∈ γ.support ∨ CoverAdj D γ a := by
  have hadj : CoverAdj D (γ - Finsupp.single a 1) a → CoverAdj D γ a := by
    rintro ⟨c, hc, hca, h⟩
    refine ⟨c, ?_, hca, h⟩
    rw [Finsupp.mem_support_iff] at hc ⊢
    simpa [Finsupp.single_apply, Ne.symm hca] using hc
  rcases a with a | a
  · rcases h with h | h | h
    · exact Or.inl (by simpa [coverBaseVal] using h)
    · refine Or.inr (Or.inl (Finsupp.mem_support_iff.2 ?_))
      simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same] at h
      omega
    · exact Or.inr (Or.inr (hadj h))
  · rcases h with h | h | h
    · exact Or.inl (by simpa [coverBaseVal] using h)
    · refine Or.inr (Or.inl (Finsupp.mem_support_iff.2 ?_))
      simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same] at h
      omega
    · exact Or.inr (Or.inr (hadj h))

variable (D Λm Λp)
variable {C : CartanDatum I} {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (μ : X)

/-- **The furling datum of the unfurled product family** (Webster, arXiv:1603.06311v3, §2.3,
Lemma with label `lem:g-action`): the cover `π` of the labels, the base weights `x̃₀ = (-Λm, Λp)`
of `g̃` and `μ` of `g`, and the relevant edges `coverRel`. Only finite support within
each base-colour fibre is required; the colour set and global weight support may be infinite. -/
def coverFurling (hΛm : ∀ i, ({a | D.π (.inl a) = i ∧ Λm a ≠ 0} : Set Jm).Finite) (hΛp : ∀ i, ({a | D.π (.inr a) = i ∧ Λp a ≠ 0} : Set Jp).Finite) :
    TwoRep.Furling (coverProdWeight D) RD where
  π := D.π
  base := coverBase Λm Λp
  baseG := μ
  rel := coverRel D Λm Λp
  finite_out β i := (coverRel_finite_aux hΛm hΛp β i).subset fun a ⟨ha, h⟩ =>
    ⟨ha, coverRel_imp β a h⟩
  finite_in γ i := (coverRel_finite_aux hΛm hΛp γ i).subset fun a ⟨ha, h⟩ =>
    ⟨ha, coverRel_sub_imp γ a h⟩

variable (hΛm : ∀ i, ({a | D.π (.inl a) = i ∧ Λm a ≠ 0} : Set Jm).Finite) (hΛp : ∀ i, ({a | D.π (.inr a) = i ∧ Λp a ≠ 0} : Set Jp).Finite)

@[simp] theorem coverFurling_π : (coverFurling D Λm Λp RD μ hΛm hΛp).π = D.π := rfl

@[simp] theorem coverFurling_baseG : (coverFurling D Λm Λp RD μ hΛm hΛp).baseG = μ := rfl

@[simp] theorem coverFurling_rel :
    (coverFurling D Λm Λp RD μ hΛm hΛp).rel = coverRel D Λm Λp := rfl

theorem coverFurling_wtT (β : Jm ⊕ Jp →₀ ℤ) :
    (coverFurling D Λm Λp RD μ hΛm hΛp).wtT β =
      coverBase Λm Λp + β.sum fun c n => n • (coverProdWeight D).iX c := rfl

/-! ## The root-lattice degrees of a block -/

/-- The root-lattice degree on `Jm` of the weight of a block is `β` restricted to `Jm`. -/
theorem wtT_fst_snd (β : Jm ⊕ Jp →₀ ℤ) (c : Jm) :
    ((coverFurling D Λm Λp RD μ hΛm hΛp).wtT β).1.2 c = β (.inl c) := by
  let φ : (((Jm → ℤ) × (Jm →₀ ℤ)) × ((Jp → ℤ) × (Jp →₀ ℤ))) →+ ℤ :=
    (Finsupp.applyAddHom c).comp
      ((AddMonoidHom.snd _ _).comp (AddMonoidHom.fst _ _))
  have hφ : ((coverFurling D Λm Λp RD μ hΛm hΛp).wtT β).1.2 c =
      φ ((coverFurling D Λm Λp RD μ hΛm hΛp).wtT β) := rfl
  rw [hφ]
  rw [coverFurling_wtT, map_add, map_finsuppSum]
  have : ∀ a : Jm ⊕ Jp, φ ((coverProdWeight D).iX a) = if a = .inl c then 1 else 0 := by
    rintro (a | a) <;> simp [φ, Finsupp.single_apply, eq_comm]
  simp only [map_zsmul, this, smul_eq_mul, mul_ite, mul_one, mul_zero, Finsupp.sum_ite_eq',
    Finsupp.mem_support_iff, ne_eq, ite_not]
  simp only [φ, coverBase, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_fst,
    AddMonoidHom.coe_snd, Finsupp.applyAddHom_apply, Finsupp.coe_zero, Pi.zero_apply, zero_add]
  split_ifs with h <;> simp [h]

/-- The root-lattice degree on `Jp` of the weight of a block is `β` restricted to `Jp`. -/
theorem wtT_snd_snd (β : Jm ⊕ Jp →₀ ℤ) (c : Jp) :
    ((coverFurling D Λm Λp RD μ hΛm hΛp).wtT β).2.2 c = β (.inr c) := by
  let φ : (((Jm → ℤ) × (Jm →₀ ℤ)) × ((Jp → ℤ) × (Jp →₀ ℤ))) →+ ℤ :=
    (Finsupp.applyAddHom c).comp
      ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))
  have hφ : ((coverFurling D Λm Λp RD μ hΛm hΛp).wtT β).2.2 c =
      φ ((coverFurling D Λm Λp RD μ hΛm hΛp).wtT β) := rfl
  rw [hφ]
  rw [coverFurling_wtT, map_add, map_finsuppSum]
  have : ∀ a : Jm ⊕ Jp, φ ((coverProdWeight D).iX a) = if a = .inr c then 1 else 0 := by
    rintro (a | a) <;> simp [φ, Finsupp.single_apply, eq_comm]
  simp only [map_zsmul, this, smul_eq_mul, mul_ite, mul_one, mul_zero, Finsupp.sum_ite_eq',
    Finsupp.mem_support_iff, ne_eq, ite_not]
  simp only [φ, coverBase, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_snd,
    Finsupp.applyAddHom_apply, Finsupp.coe_zero, Pi.zero_apply, zero_add]
  split_ifs with h <;> simp [h]

/-- The multiplicities of the cyclotomic block of `W` at a weight `x₁` are the root-lattice
degrees of `x₁`. -/
theorem count_of_blockWeight {J : Type u} [DecidableEq J] (n : J → J → ℕ) (Λ : J → ℕ)
    {x : (J → ℤ) × (J →₀ ℤ)} (m : WeightBlocks (coverWeight n) ((fun j => (Λ j : ℤ)), 0) x)
    (c : J) : (m.1.count c : ℤ) = x.2 c := by
  have := congrArg (fun x => x.2 c) m.2
  simp only [blockWeight, Prod.snd_sub, sub_zero] at this
  rw [← this, coverWeight_sum_snd_apply]

/-! ## Labels acting by zero -/

/-- **Irrelevant edges act by zero** (Webster, arXiv:1603.06311v3, §2.3, proof of the Lemma with
label `lem:g-action`): if the label `a` carries no weight, is not in the cyclotomic block of `β`
and is not adjacent to its support, then `E_a` and `F_a` out of the block `β` vanish. -/
theorem coverFurling_isZero (β : Jm ⊕ Jp →₀ ℤ) (a : Jm ⊕ Jp) {y}
    (h : (coverFurling D Λm Λp RD μ hΛm hΛp).wtT β + (coverProdWeight D).iX a = y)
    (hr : ¬ coverRel D Λm Λp β a) :
    IsZero ((coverProduct.{u, v, w} (arrowsNeg D) (L := L) Λm (arrowsPos D) Λp).E a h) ∧
      IsZero ((coverProduct.{u, v, w} (arrowsNeg D) (L := L) Λm (arrowsPos D) Λp).F a h) := by
  rcases a with a | b
  · simp only [coverRel, not_or, not_lt, ne_eq, not_not] at hr
    obtain ⟨hΛ, hβ, hadj⟩ := hr
    refine coverProduct_isZero_inl _ _ _ _ a h (fun m => ?_) hΛ
    have hcount : ∀ c, (m.1.count c : ℤ) = β (.inl c) := fun c =>
      (count_of_blockWeight _ Λm m c).trans (wtT_fst_snd D Λm Λp RD μ hΛm hΛp β c)
    have ha : a ∉ m.1 := fun hm => by
      have h₁ := hcount a
      have h₂ := Multiset.count_pos.2 hm
      omega
    refine ⟨ha, fun c hc => ?_⟩
    have hc0 : β (.inl c) ≠ 0 := by
      have h₁ := hcount c
      have h₂ := Multiset.count_pos.2 hc
      omega
    have hca : (Sum.inl c : Jm ⊕ Jp) ≠ .inl a := fun e => ha (Sum.inl_injective e ▸ hc)
    by_contra hne
    exact hadj ⟨.inl c, Finsupp.mem_support_iff.2 hc0, hca, by
      simpa only [arrowsNeg, not_and_or, ne_eq] using hne⟩
  · simp only [coverRel, not_or, not_lt, ne_eq, not_not] at hr
    obtain ⟨hΛ, hβ, hadj⟩ := hr
    refine coverProduct_isZero_inr _ _ _ _ b h (fun m => ?_) hΛ
    have hy : ∀ c, (-y.2).2 c = -β (.inr c) - if c = b then 1 else 0 := by
      intro c
      subst h
      by_cases hcb : c = b
      · subst hcb
        simp [wtT_snd_snd]
        ring
      · simp [wtT_snd_snd, hcb]
    have hcount : ∀ c, (m.1.count c : ℤ) = -β (.inr c) - if c = b then 1 else 0 := fun c =>
      (count_of_blockWeight _ Λp m c).trans (hy c)
    have hb : b ∉ m.1 := fun hm => by
      have h₁ := hcount b
      have h₂ := Multiset.count_pos.2 hm
      simp only [↓reduceIte] at h₁
      omega
    refine ⟨hb, fun c hc => ?_⟩
    have hcb : c ≠ b := fun e => hb (e ▸ hc)
    have hc0 : β (.inr c) ≠ 0 := by
      have h₁ := hcount c
      have h₂ := Multiset.count_pos.2 hc
      simp only [hcb, ↓reduceIte] at h₁
      omega
    have hca : (Sum.inr c : Jm ⊕ Jp) ≠ .inr b := fun e => hcb (Sum.inr_injective e)
    by_contra hne
    exact hadj ⟨.inr c, Finsupp.mem_support_iff.2 hc0, hca, by
      simpa only [arrowsPos, not_and_or, ne_eq] using hne⟩

/-- **The blocks outside `CoverAdm` are zero** (Webster, arXiv:1603.06311v3, §2.3): if `β_a < 0`
for a label of `Jm`, the cyclotomic weight space of `W` has no blocks; if `β_b > 0` for a label
of `Jp`, that of `T` has none. -/
theorem coverFurling_isZero_obj (β : Jm ⊕ Jp →₀ ℤ) (hβ : ¬ CoverAdm β)
    (M : (coverProduct.{u, v, w} (arrowsNeg D) (L := L) Λm (arrowsPos D) Λp).obj
      ((coverFurling D Λm Λp RD μ hΛm hΛp).wtT β)) : IsZero M := by
  simp only [CoverAdm, not_and_or, not_forall, not_le] at hβ
  rcases hβ with ⟨a, ha⟩ | ⟨b, hb⟩
  · have hz : IsEmpty (WeightBlocks (coverWeight (arrowsNeg D)) ((fun j => (Λm j : ℤ)), 0)
        ((coverFurling D Λm Λp RD μ hΛm hΛp).wtT β).1) := ⟨fun m => by
      have h₁ := (count_of_blockWeight _ Λm m a).trans (wtT_fst_snd D Λm Λp RD μ hΛm hΛp β a)
      omega⟩
    exact isZero_to_weightSpace.{u, v, w} _ _ _ _ hz M
  · have hz : IsEmpty (WeightBlocks (coverWeight (arrowsPos D)) ((fun j => (Λp j : ℤ)), 0)
        (-((coverFurling D Λm Λp RD μ hΛm hΛp).wtT β).2)) := ⟨fun m => by
      have h₁ := count_of_blockWeight _ Λp m b
      have h₂ := wtT_snd_snd D Λm Λp RD μ hΛm hΛp β b
      simp only [Prod.snd_neg, Finsupp.coe_neg, Pi.neg_apply] at h₁
      omega⟩
    exact isZero_from_weightSpace.{u, v, w} _ _ _ _ hz M

/-! ## The pairing at admissible blocks -/

variable {D} in
omit [DecidableEq Jm] [DecidableEq Jp] in
private theorem finsum_fibre_eq {i : I} (A : Finset (Jm ⊕ Jp)) (hA : ∀ a ∈ A, D.π a = i)
    (f : Jm ⊕ Jp → ℤ) (hf : ∀ a, D.π a = i → f a ≠ 0 → a ∈ A) :
    ∑ᶠ a : {a // D.π a = i}, f a.1 = ∑ a ∈ A, f a := by
  classical
  have hsub : Function.support (fun a : {a // D.π a = i} => f a.1) ⊆
      ↑(A.subtype fun a => D.π a = i) := fun a ha => Finset.mem_subtype.2 (hf a.1 a.2 ha)
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_subtype_eq_sum_filter,
    Finset.filter_true_of_mem hA]

/-- **The pairing of a colour with an admissible block** (Webster, arXiv:1603.06311v3, §2.3,
proof of the Lemma with label `lem:g-action`): the weight of `g` at `β` pairs with `i` as the
sum, over any finite set `A` of labels over `i` containing the relevant ones (for `β` and for
the blocks `β - a`), of the pairings of the labels with the weight of `g̃`. The hypotheses are
the base identity `hμ` and the branched-cover identity `hcover`
(`UnfurlingDatum.ofClosure_finsum_arrows_eq_dij`). -/
theorem coverFurling_pair (hD : NoCrossArrows D)
    (hμ : ∀ i, RD.pair (RD.iY i) μ = ∑ᶠ a : {a // D.π a = i}, coverBaseVal Λm Λp a.1)
    (hcover : ∀ (c : Jm ⊕ Jp) (i : I), i ≠ D.π c →
      ∑ᶠ a : {a // D.π a = i}, (((D.arrows a.1 c + D.arrows c a.1 : ℕ)) : ℤ) =
        -RD.pair (RD.iY i) (RD.iX (D.π c)))
    (β : Jm ⊕ Jp →₀ ℤ) (hβ : CoverAdm β) (i : I) (A : Finset (Jm ⊕ Jp))
    (hA : ∀ a ∈ A, D.π a = i)
    (hA' : ∀ a, D.π a = i → coverRel D Λm Λp β a ∨
      coverRel D Λm Λp (β - Finsupp.single a 1) a → a ∈ A) :
    RD.pair (RD.iY i) ((coverFurling D Λm Λp RD μ hΛm hΛp).wtG β) =
      ∑ a ∈ A, (coverProdWeight D).pair ((coverProdWeight D).iY a)
        ((coverFurling D Λm Λp RD μ hΛm hΛp).wtT β) := by
  have hrel : ∀ a, CoverAdj D β a → coverRel D Λm Λp β a := by
    rintro (a | a) h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inr h)
  simp only [TwoRep.Furling.wtG, coverFurling_wtT, coverFurling_π, coverFurling_baseG]
  rw [map_add, map_finsuppSum]
  simp only [coverProdWeight_pair_add_sum hD, coverProdWeight_pair_base,
    Finset.sum_add_distrib]
  congr 1
  · rw [hμ i]
    refine finsum_fibre_eq A hA _ fun a ha h => hA' a ha (Or.inl ?_)
    rcases a with a | a
    · exact Or.inl fun h0 => h (by simp [coverBaseVal, h0])
    · exact Or.inl fun h0 => h (by simp [coverBaseVal, h0])
  · simp only [Finsupp.sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [map_zsmul, smul_eq_mul, ← Finset.mul_sum]
    congr 1
    have hc0 := Finsupp.mem_support_iff.1 hc
    by_cases hci : D.π c = i
    · have hcA : c ∈ A := by
        refine hA' c hci ?_
        rcases c with c | c
        · exact Or.inl (Or.inr (Or.inl (lt_of_le_of_ne (hβ.1 c) (Ne.symm hc0))))
        · by_cases hlt : β (.inr c) < -1
          · exact Or.inl (Or.inr (Or.inl hlt))
          · refine Or.inr (Or.inr (Or.inl ?_))
            have := hβ.2 c
            simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same]
            omega
      rw [Finset.sum_eq_single_of_mem c hcA fun a ha hac => ?_, hci, RD.pair_iY_iX_self]
      · simp [coverDot]
      · have hπ : D.π a = D.π c := (hA a ha).trans hci.symm
        simp [coverDot, hac, D.arrows_of_eq a c hπ, D.arrows_of_eq c a hπ.symm]
    · have hf : ∀ a, D.π a = i → (((D.arrows a c + D.arrows c a : ℕ)) : ℤ) ≠ 0 → a ∈ A := by
        intro a ha h
        refine hA' a ha (Or.inl (hrel a ⟨c, hc, fun e => hci (e ▸ ha), ?_⟩))
        by_contra hne
        simp only [not_or, not_not] at hne
        simp [hne.1, hne.2] at h
      rw [← neg_neg (RD.pair _ _), ← hcover c i (Ne.symm hci),
        finsum_fibre_eq A hA (fun a => (((D.arrows a c + D.arrows c a : ℕ)) : ℤ)) hf,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have hac : a ≠ c := fun e => hci (e ▸ hA a ha)
      simp [coverDot, hac]

/-! ## The upward relations -/

variable {D} in
omit [DecidableEq Jm] [DecidableEq Jp] in
/-- Without arrows between `Jm` and `Jp`, the product parameters are those of the whole
unfurled graph. -/
theorem prodQ_unfQ (hD : NoCrossArrows D) :
    RouqFamily.prodQ (unfQ (k := L) (arrowsNeg D)) (unfQ (k := L) (arrowsPos D)) =
      unfQ (k := L) D.arrows := by
  funext a b
  rcases a with a | a <;> rcases b with b | b
  · rfl
  · simp [RouqFamily.prodQ, unfQ, unfP, (hD a b).1, (hD a b).2]
  · simp [RouqFamily.prodQ, unfQ, unfP, (hD b a).1, (hD b a).2]
  · rfl

/-- **The upward KLR relations of the product family** with the parameters `unfQ D.arrows` of
the unfurled graph (Webster, arXiv:1603.06311v3, §2.3). -/
theorem coverProduct_upKLR_unfQ (hD : NoCrossArrows D) :
    RouqUpKLR (coverProduct.{u, v, w} (arrowsNeg D) (L := L) Λm (arrowsPos D) Λp)
      (unfQ (k := L) D.arrows) :=
  prodQ_unfQ hD ▸ coverProduct_upKLR _ _ _ _

end Categorification.KLR.Unfurling
