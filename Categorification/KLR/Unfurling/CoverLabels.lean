/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverFurling
import Categorification.KLR.Unfurling.GenericLabels

/-!
# The labels `Ĩ₋ ⊔ Ĩ₊` of the unfurled product family

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2.3, proof of the
theorem with label `nondegenerate`. The representation of `g̃` used there is built from two
unfurled graphs `Ĩ₋` and `Ĩ₊` with no arrows between them. Over an algebraically closed field
`L`, with the polynomials `P_{ij}` defined over a subfield `K` that is integrally closed in `L`,
we take for `Ĩ₋` the labels `(i, u)` of the full closure `Σ i, L ∖ {0}` with `u ∈ K`, and for
`Ĩ₊` those with `u ∉ K`. Together they are the full closure, so every fibre of the cover is
complete, and the splitting theorem `arrows_eq_zero_of_isIntegrallyClosedIn` gives that there
are no arrows between the two parts.

## Main definitions and results

* `LabelNeg`, `LabelPos`: the two parts of the labels; `coverLabel`: their inclusion into the
  full closure;
* `coverDatum`: the restriction of `ofClosure` to `LabelNeg ⊕ LabelPos`;
* `coverDatum_noCrossArrows`: no arrows between the two parts;
* `coverDatum_finsum_arrows`: the branched-cover identity in the form used by
  `coverFurling_pair`, `∑_{a over i} (n_{ac} + n_{ca}) = -⟨i, α_{π c}⟩` for `i ≠ π c`;
* `coverWeightNeg`, `coverWeightPos`, `coverDatum_finsum_base`: the base weights, one label over
  each vertex in each part, with the base identity of `coverFurling_pair`.
-/

open MvPolynomial

noncomputable section

namespace Categorification.KLR.Unfurling

variable (I : Type*) (K : Type*) (L : Type*) [Field K] [Field L] [Algebra K L]

/-- The labels of `Ĩ₋`: pairs `(i, u)` with `u ≠ 0` in the image of `K`. -/
def LabelNeg := Σ _ : I, {u : L // u ≠ 0 ∧ u ∈ Set.range (algebraMap K L)}

/-- The labels of `Ĩ₊`: pairs `(i, u)` with `u ≠ 0` not in the image of `K`. -/
def LabelPos := Σ _ : I, {u : L // u ≠ 0 ∧ u ∉ Set.range (algebraMap K L)}

instance : DecidableEq (LabelNeg I K L) := Classical.decEq _

instance : DecidableEq (LabelPos I K L) := Classical.decEq _

/-- The inclusion of `Ĩ₋ ⊔ Ĩ₊` into the full closure `Σ i, L ∖ {0}`. -/
def coverLabel : LabelNeg I K L ⊕ LabelPos I K L → Σ _ : I, {u : L // u ≠ 0}
  | .inl a => ⟨a.1, a.2.1, a.2.2.1⟩
  | .inr a => ⟨a.1, a.2.1, a.2.2.1⟩

theorem coverLabel_injective : Function.Injective (coverLabel I K L) := by
  rintro (⟨i, u, hu⟩ | ⟨i, u, hu⟩) (⟨i', u', hu'⟩ | ⟨i', u', hu'⟩) h <;>
    obtain ⟨rfl, h₂⟩ := Sigma.mk.inj h <;>
    have h₃ : u = u' := congrArg Subtype.val (eq_of_heq h₂)
  · subst h₃; rfl
  · exact absurd (h₃ ▸ hu.2) hu'.2
  · exact absurd (h₃ ▸ hu'.2) hu.2
  · subst h₃; rfl

/-- Every label of the full closure is in `Ĩ₋` or in `Ĩ₊`. -/
theorem coverLabel_surjective : Function.Surjective (coverLabel I K L) := by
  rintro ⟨i, u, hu⟩
  by_cases hK : u ∈ Set.range (algebraMap K L)
  · exact ⟨.inl ⟨i, u, hu, hK⟩, rfl⟩
  · exact ⟨.inr ⟨i, u, hu, hK⟩, rfl⟩

variable {I K L} (P₀ : I → I → MvPolynomial (Fin 2) K) (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
  (hd : ∀ i, ((d i : ℕ) : L) ≠ 0)
  (hP : ∀ i j, i ≠ j → MvPolynomial.map (algebraMap K L) (P₀ i j) ≠ 0)
  (hhom : ∀ i j, i ≠ j →
    ∃ D, (MvPolynomial.map (algebraMap K L) (P₀ i j)).IsWeightedHomogeneous ![d j, d i] D)

/-- **The unfurling datum on `Ĩ₋ ⊔ Ĩ₊`** (Webster, arXiv:1603.06311v3, proof of the theorem with
label `nondegenerate`): the restriction of `ofClosure` (series `ϖ_{(i,u)}(x) = u (1 + x)^{d_i}`,
for the base change of `P₀`) to the labels `LabelNeg ⊕ LabelPos`. -/
def coverDatum :
    UnfurlingDatum L (fun i j => MvPolynomial.map (algebraMap K L) (P₀ i j))
      (LabelNeg I K L ⊕ LabelPos I K L) :=
  (UnfurlingDatum.ofClosure d hdpos hd hP hhom).restrict (coverLabel I K L)
    (coverLabel_injective I K L)

@[simp] theorem coverDatum_π (a : LabelNeg I K L ⊕ LabelPos I K L) :
    (coverDatum P₀ d hdpos hd hP hhom).π a = (coverLabel I K L a).1 :=
  rfl

@[simp] theorem coverDatum_pw_coeff_zero (a : LabelNeg I K L ⊕ LabelPos I K L) :
    ((coverDatum P₀ d hdpos hd hP hhom).pw a).coeff 0 = (coverLabel I K L a).2 :=
  UnfurlingDatum.ofClosure_pw_coeff_zero d hdpos hd hP hhom (coverLabel I K L a)

@[simp] theorem coverDatum_arrows (a b : LabelNeg I K L ⊕ LabelPos I K L) :
    (coverDatum P₀ d hdpos hd hP hhom).arrows a b =
      (UnfurlingDatum.ofClosure d hdpos hd hP hhom).arrows (coverLabel I K L a)
        (coverLabel I K L b) :=
  rfl

/-- **No arrows between `Ĩ₋` and `Ĩ₊`** (Webster, arXiv:1603.06311v3, proof of the theorem with
label `nondegenerate`), when `K` is integrally closed in `L`. -/
theorem coverDatum_noCrossArrows [IsIntegrallyClosedIn K L] :
    NoCrossArrows (coverDatum P₀ d hdpos hd hP hhom) := fun a b =>
  UnfurlingDatum.arrows_eq_zero_of_isIntegrallyClosedIn (P₀ := P₀) _
    (by rw [coverDatum_pw_coeff_zero]; exact a.2.2.2)
    (by rw [coverDatum_pw_coeff_zero]; exact b.2.2.2)

/-- The labels over `i` are in bijection with the nonzero scalars. -/
theorem coverLabel_fibre_bijective (i : I) :
    Function.Bijective fun a : {a : LabelNeg I K L ⊕ LabelPos I K L //
        (coverDatum P₀ d hdpos hd hP hhom).π a = i} => (coverLabel I K L a.1).2 := by
  refine ⟨fun a a' h => ?_, fun u => ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨a', ha'⟩ := a'
    refine Subtype.ext (coverLabel_injective I K L (Sigma.ext (ha.trans ha'.symm) ?_))
    exact heq_of_eq h
  · obtain ⟨a, ha⟩ := coverLabel_surjective I K L ⟨i, u⟩
    refine ⟨⟨a, by rw [coverDatum_π, ha]⟩, ?_⟩
    change (coverLabel I K L a).2 = u
    rw [ha]

/-- **The branched-cover identity on `Ĩ₋ ⊔ Ĩ₊`** (Webster, arXiv:1603.06311v3, §2, the
definition with label `def:tilde-I` and the homomorphism with label `eq:furling-homomorphism`;
the statement is implicit there): for a label `c` and a vertex `i ≠ π c`,
`∑_{a over i} (n_{ac} + n_{ca}) = d_{i, π c} = -⟨i, α_{π c}⟩`, in the form of the hypothesis
`hcover` of `coverFurling_pair`. The fibres are complete since `Ĩ₋ ⊔ Ĩ₊` is the full
closure. -/
theorem coverDatum_finsum_arrows [IsAlgClosed L] (C : QuantumGroup.CartanDatum I)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : QuantumGroup.UDot.WeightDatum C X Y)
    (Q : I → I → MvPolynomial (Fin 2) L)
    (hPQ : ∀ a b, a ≠ b → Q a b = MvPolynomial.map (algebraMap K L) (P₀ b a) *
      rename ![1, 0] (MvPolynomial.map (algebraMap K L) (P₀ a b)))
    (hext : ∀ a b, a ≠ b → (Q a b).coeff (Finsupp.single 0 (C.dij a b)) ≠ 0)
    (c : LabelNeg I K L ⊕ LabelPos I K L) (i : I)
    (hi : i ≠ (coverDatum P₀ d hdpos hd hP hhom).π c) :
    ∑ᶠ a : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i},
        ((((coverDatum P₀ d hdpos hd hP hhom).arrows a.1 c +
          (coverDatum P₀ d hdpos hd hP hhom).arrows c a.1 : ℕ)) : ℤ) =
      -RD.pair (RD.iY i) (RD.iX ((coverDatum P₀ d hdpos hd hP hhom).π c)) := by
  set D := UnfurlingDatum.ofClosure (P := fun i j => MvPolynomial.map (algebraMap K L) (P₀ i j))
    d hdpos hd hP hhom
  obtain ⟨hfin, hsum⟩ := UnfurlingDatum.ofClosure_finsum_arrows_eq_dij C d hdpos hd hP hhom Q
    hPQ hext hi (coverLabel I K L c).2
  have hlab : ∀ a : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i},
      coverLabel I K L a.1 = ⟨i, (coverLabel I K L a.1).2⟩ := fun a =>
    Sigma.ext a.2 HEq.rfl
  have hc : coverLabel I K L c = ⟨(coverLabel I K L c).1, (coverLabel I K L c).2⟩ := rfl
  have hfun : ∀ a : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i},
      (coverDatum P₀ d hdpos hd hP hhom).arrows a.1 c +
          (coverDatum P₀ d hdpos hd hP hhom).arrows c a.1 =
        (fun u : {u : L // u ≠ 0} => D.arrows ⟨i, u⟩ ⟨(coverLabel I K L c).1,
          (coverLabel I K L c).2⟩ + D.arrows ⟨(coverLabel I K L c).1, (coverLabel I K L c).2⟩
            ⟨i, u⟩) (coverLabel I K L a.1).2 := fun a => by
    simp only [coverDatum_arrows]
    rw [hlab a, ← hc]
  have hnat := finsum_eq_of_bijective (f := fun a : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i} =>
      (coverDatum P₀ d hdpos hd hP hhom).arrows a.1 c +
        (coverDatum P₀ d hdpos hd hP hhom).arrows c a.1)
    (g := fun u : {u : L // u ≠ 0} => D.arrows ⟨i, u⟩ ⟨(coverLabel I K L c).1,
          (coverLabel I K L c).2⟩ + D.arrows ⟨(coverLabel I K L c).1, (coverLabel I K L c).2⟩
            ⟨i, u⟩) _ (coverLabel_fibre_bijective P₀ d hdpos hd hP hhom i) hfun
  have hcast := (Nat.castAddMonoidHom ℤ).map_finsum_of_injective Nat.cast_injective
    (fun a : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i} =>
      (coverDatum P₀ d hdpos hd hP hhom).arrows a.1 c +
        (coverDatum P₀ d hdpos hd hP hhom).arrows c a.1)
  simp only [Nat.coe_castAddMonoidHom] at hcast
  rw [← hcast, hnat.trans hsum]
  exact (neg_pair_eq_dij C RD hi).symm

/-! ## Base weights -/

variable (zm : I → {u : L // u ≠ 0 ∧ u ∈ Set.range (algebraMap K L)})
  (zp : I → {u : L // u ≠ 0 ∧ u ∉ Set.range (algebraMap K L)}) (nm np : I → ℕ)

open Classical in
/-- The weights `Λ₋` on `Ĩ₋`: `n₋(i)` at the label `(i, zm i)`, zero elsewhere. -/
def coverWeightNeg (a : LabelNeg I K L) : ℕ := if a.2 = zm a.1 then nm a.1 else 0

open Classical in
/-- The weights `Λ₊` on `Ĩ₊`: `n₊(i)` at the label `(i, zp i)`, zero elsewhere. -/
def coverWeightPos (a : LabelPos I K L) : ℕ := if a.2 = zp a.1 then np a.1 else 0

theorem coverWeightNeg_finite (hnm : (Function.support nm).Finite) :
    (Function.support (coverWeightNeg zm nm)).Finite :=
  (hnm.image fun i => (⟨i, zm i⟩ : LabelNeg I K L)).subset fun a ha => by
    classical
    obtain ⟨i, u⟩ := a
    by_cases h : u = zm i
    · subst h
      have ha' : coverWeightNeg zm nm ⟨i, zm i⟩ ≠ 0 := ha
      refine ⟨i, ?_, rfl⟩
      intro h0
      exact ha' (by simp [coverWeightNeg, h0])
    · exact absurd (by simp [coverWeightNeg, h]) ha

theorem coverWeightPos_finite (hnp : (Function.support np).Finite) :
    (Function.support (coverWeightPos zp np)).Finite :=
  (hnp.image fun i => (⟨i, zp i⟩ : LabelPos I K L)).subset fun a ha => by
    classical
    obtain ⟨i, u⟩ := a
    by_cases h : u = zp i
    · subst h
      have ha' : coverWeightPos zp np ⟨i, zp i⟩ ≠ 0 := ha
      refine ⟨i, ?_, rfl⟩
      intro h0
      exact ha' (by simp [coverWeightPos, h0])
    · exact absurd (by simp [coverWeightPos, h]) ha

/-- **The base identity** of `coverFurling_pair`: with one weighted label over each vertex in
each part, `∑_{a over i} x̃₀(a) = n₊(i) - n₋(i)`. -/
theorem coverDatum_finsum_base (i : I) :
    ∑ᶠ a : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i},
        coverBaseVal (coverWeightNeg zm nm) (coverWeightPos zp np) a.1 =
      (np i : ℤ) - nm i := by
  classical
  let am : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i} := ⟨.inl ⟨i, zm i⟩, rfl⟩
  let ap : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i} := ⟨.inr ⟨i, zp i⟩, rfl⟩
  have hne : am ≠ ap := fun h => Sum.inl_ne_inr (congrArg Subtype.val h)
  rw [finsum_eq_sum_of_support_subset (s := {am, ap}) _ ?_, Finset.sum_pair hne]
  · simp [am, ap, coverBaseVal, coverWeightNeg, coverWeightPos]
    ring
  · rintro ⟨⟨i', u⟩ | ⟨i', u⟩, h⟩ hs <;> change i' = i at h <;> subst h <;>
      simp only [Function.mem_support, coverBaseVal, coverWeightNeg, coverWeightPos, ne_eq,
        neg_eq_zero, Nat.cast_eq_zero, ite_eq_right_iff, not_forall] at hs <;>
      obtain ⟨rfl, -⟩ := hs <;>
      first
      | exact Finset.mem_coe.2 (Finset.mem_insert_self _ _)
      | exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

end Categorification.KLR.Unfurling
