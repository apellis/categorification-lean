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
* `coverWeightNeg`, `coverWeightPos`, `coverDatum_finsum_base`: the base weights, finitely many
  weighted labels `(i, zm i q)`, `(i, zp i q)` over each vertex in each part (as in the proof of
  the theorem with label `nondegenerate`, where they are pairwise distinct generic scalars), with
  the base identity of `coverFurling_pair`.
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

section Base

/-- The base value of a sum of weights is the sum of the base values. -/
theorem coverBaseVal_sum {Q : Type*} (s : Finset Q) (Λm : Q → LabelNeg I K L → ℕ)
    (Λp : Q → LabelPos I K L → ℕ) (a : LabelNeg I K L ⊕ LabelPos I K L) :
    coverBaseVal (fun c => ∑ q ∈ s, Λm q c) (fun c => ∑ q ∈ s, Λp q c) a =
      ∑ q ∈ s, coverBaseVal (Λm q) (Λp q) a := by
  rcases a with a | a <;> simp [coverBaseVal]

variable (zm₁ : I → {u : L // u ≠ 0 ∧ u ∈ Set.range (algebraMap K L)})
  (zp₁ : I → {u : L // u ≠ 0 ∧ u ∉ Set.range (algebraMap K L)}) (nm₁ np₁ : I → ℕ)

open Classical in
/-- For one weighted label over each vertex in each part, the labels over `i` with a nonzero
base value are among `(i, zm₁ i)` and `(i, zp₁ i)`. -/
private theorem support_base_single_subset (i : I) :
    Function.support (fun a : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i} =>
        coverBaseVal (fun a : LabelNeg I K L => if a.2 = zm₁ a.1 then nm₁ a.1 else 0)
          (fun a : LabelPos I K L => if a.2 = zp₁ a.1 then np₁ a.1 else 0) a.1) ⊆
      ↑({⟨.inl ⟨i, zm₁ i⟩, rfl⟩, ⟨.inr ⟨i, zp₁ i⟩, rfl⟩} :
        Finset {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i}) := by
  rintro ⟨⟨i', u⟩ | ⟨i', u⟩, h⟩ hs <;> change i' = i at h <;> subst h <;>
    simp only [Function.mem_support, coverBaseVal, ne_eq, neg_eq_zero, Nat.cast_eq_zero,
      ite_eq_right_iff, not_forall] at hs <;>
    obtain ⟨rfl, -⟩ := hs <;>
    first
    | exact Finset.mem_coe.2 (Finset.mem_insert_self _ _)
    | exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

open Classical in
/-- The base identity for one weighted label over each vertex in each part:
`∑_{a over i} x̃₀(a) = n₊(i) - n₋(i)` for the weights `n₋(i)` at `(i, zm₁ i)` and `n₊(i)` at
`(i, zp₁ i)`. -/
private theorem finsum_base_single (i : I) :
    ∑ᶠ a : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i},
        coverBaseVal (fun a : LabelNeg I K L => if a.2 = zm₁ a.1 then nm₁ a.1 else 0)
          (fun a : LabelPos I K L => if a.2 = zp₁ a.1 then np₁ a.1 else 0) a.1 =
      (np₁ i : ℤ) - nm₁ i := by
  have hne : (⟨.inl ⟨i, zm₁ i⟩, rfl⟩ : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i}) ≠
      ⟨.inr ⟨i, zp₁ i⟩, rfl⟩ := fun h => Sum.inl_ne_inr (congrArg Subtype.val h)
  rw [finsum_eq_sum_of_support_subset _ (support_base_single_subset P₀ d hdpos hd hP hhom zm₁ zp₁
    nm₁ np₁ i), Finset.sum_pair hne]
  simp [coverBaseVal]
  ring

end Base

variable {Q : Type*} [Fintype Q]
  (zm : I → Q → {u : L // u ≠ 0 ∧ u ∈ Set.range (algebraMap K L)})
  (zp : I → Q → {u : L // u ≠ 0 ∧ u ∉ Set.range (algebraMap K L)}) (nm np : I → Q → ℕ)

open Classical in
/-- The weights `Λ₋` on `Ĩ₋`: `n₋(i, q)` at the label `(i, zm i q)` for each `q`, zero at the
labels not of this form (the values add up if `zm i` takes a label twice). In the proof of the
theorem with label `nondegenerate` (Webster, arXiv:1603.06311v3), `q` runs over `[1, m]` and the
labels `zm i q` are pairwise distinct generic scalars. -/
def coverWeightNeg (a : LabelNeg I K L) : ℕ := ∑ q, if a.2 = zm a.1 q then nm a.1 q else 0

open Classical in
/-- The weights `Λ₊` on `Ĩ₊`: `n₊(i, q)` at the label `(i, zp i q)` for each `q`, zero at the
labels not of this form. -/
def coverWeightPos (a : LabelPos I K L) : ℕ := ∑ q, if a.2 = zp a.1 q then np a.1 q else 0

/-- At a label `(i, zm i q)` with `zm i` injective, the weight is `n₋(i, q)`. -/
theorem coverWeightNeg_mk {i : I} (hzm : Function.Injective (zm i)) (q : Q) :
    coverWeightNeg zm nm ⟨i, zm i q⟩ = nm i q := by
  classical
  simp [coverWeightNeg, hzm.eq_iff]

/-- At a label `(i, zp i q)` with `zp i` injective, the weight is `n₊(i, q)`. -/
theorem coverWeightPos_mk {i : I} (hzp : Function.Injective (zp i)) (q : Q) :
    coverWeightPos zp np ⟨i, zp i q⟩ = np i q := by
  classical
  simp [coverWeightPos, hzp.eq_iff]

theorem coverWeightNeg_finite (hnm : (Function.support nm).Finite) :
    (Function.support (coverWeightNeg zm nm)).Finite :=
  (hnm.biUnion fun i _ => Set.finite_range fun q => (⟨i, zm i q⟩ : LabelNeg I K L)).subset
    fun a ha => by
      classical
      obtain ⟨i, u⟩ := a
      obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
      obtain ⟨hu, hq⟩ := (ite_ne_right_iff).1 hq
      exact Set.mem_biUnion (x := i) (fun h0 => hq (congrFun h0 q))
        ⟨q, congrArg (Sigma.mk i) hu.symm⟩

theorem coverWeightPos_finite (hnp : (Function.support np).Finite) :
    (Function.support (coverWeightPos zp np)).Finite :=
  (hnp.biUnion fun i _ => Set.finite_range fun q => (⟨i, zp i q⟩ : LabelPos I K L)).subset
    fun a ha => by
      classical
      obtain ⟨i, u⟩ := a
      obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
      obtain ⟨hu, hq⟩ := (ite_ne_right_iff).1 hq
      exact Set.mem_biUnion (x := i) (fun h0 => hq (congrFun h0 q))
        ⟨q, congrArg (Sigma.mk i) hu.symm⟩

/-- Finitely many weighted negative labels over each colour, without finite colour support. -/
theorem coverWeightNeg_finite_fibre (i : I) :
    ({a : LabelNeg I K L | a.1 = i ∧ coverWeightNeg zm nm a ≠ 0} : Set _).Finite := by
  classical
  apply (Set.finite_range fun q => (⟨i, zm i q⟩ : LabelNeg I K L)).subset
  rintro ⟨j, u⟩ ⟨rfl, h⟩
  obtain ⟨q, _, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨hu, _⟩ := (ite_ne_right_iff).1 hq
  exact ⟨q, congrArg (Sigma.mk j) hu.symm⟩

/-- Finitely many weighted positive labels over each colour, without finite colour support. -/
theorem coverWeightPos_finite_fibre (i : I) :
    ({a : LabelPos I K L | a.1 = i ∧ coverWeightPos zp np a ≠ 0} : Set _).Finite := by
  classical
  apply (Set.finite_range fun q => (⟨i, zp i q⟩ : LabelPos I K L)).subset
  rintro ⟨j, u⟩ ⟨rfl, h⟩
  obtain ⟨q, _, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨hu, _⟩ := (ite_ne_right_iff).1 hq
  exact ⟨q, congrArg (Sigma.mk j) hu.symm⟩

/-- **The base identity** of `coverFurling_pair`: with the weights `n₋(i, q)` at the labels
`(i, zm i q)` and `n₊(i, q)` at `(i, zp i q)`,
`∑_{a over i} x̃₀(a) = ∑_q (n₊(i, q) - n₋(i, q))`. -/
theorem coverDatum_finsum_base (i : I) :
    ∑ᶠ a : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i},
        coverBaseVal (coverWeightNeg zm nm) (coverWeightPos zp np) a.1 =
      ∑ q, ((np i q : ℤ) - nm i q) := by
  classical
  have hsum : ∀ a : {a // (coverDatum P₀ d hdpos hd hP hhom).π a = i},
      coverBaseVal (coverWeightNeg zm nm) (coverWeightPos zp np) a.1 =
        ∑ q, coverBaseVal (fun a : LabelNeg I K L => if a.2 = zm a.1 q then nm a.1 q else 0)
          (fun a : LabelPos I K L => if a.2 = zp a.1 q then np a.1 q else 0) a.1 := fun a =>
    coverBaseVal_sum Finset.univ (fun q (a : LabelNeg I K L) => if a.2 = zm a.1 q then nm a.1 q
      else 0) (fun q (a : LabelPos I K L) => if a.2 = zp a.1 q then np a.1 q else 0) a.1
  rw [finsum_congr hsum, finsum_sum_comm]
  · exact Finset.sum_congr rfl fun q _ =>
      finsum_base_single P₀ d hdpos hd hP hhom (zm · q) (zp · q) (nm · q) (np · q) i
  · intro q _
    exact (Finset.finite_toSet _).subset
      (support_base_single_subset P₀ d hdpos hd hP hhom (zm · q) (zp · q) (nm · q) (np · q) i)

end Categorification.KLR.Unfurling
