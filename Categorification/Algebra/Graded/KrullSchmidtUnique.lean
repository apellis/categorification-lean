/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.G0Basis

/-!
# Krull–Schmidt at the level of modules

Khovanov–Lauda I (arXiv:0803.4121v2), §2.5, TeX lines 1513–1556: "the category `R(ν)-mod` is
Krull–Schmidt". `Categorification.Algebra.Graded.KrullSchmidt` proves the existence of
decompositions at the level of `K₀` and that `K₀(A)` is free on the indecomposables. Here we
prove the module-level statements, for any `ℤ`-graded algebra `A` over a field `k` with a graded
dimension (`HasGdim 𝒜`; `R(ν)` is such an algebra).

## Main definitions

* `GProj.zeroObj 𝒜` : the zero object of `A-pmod`.
* `GProj.sumList l` : for a list `l = [(b₁, a₁), …, (bₙ, aₙ)]` of indecomposable classes and
  shifts, the direct sum `P_{b₁}{a₁} ⊕ ⋯ ⊕ P_{bₙ}{aₙ}` of shifted chosen representatives
  `P_b = IndecClass.rep b`.
* `K0.mult x b a` : the coefficient of `q^a [P_b]` in `x ∈ K₀(A)` with respect to the basis
  `K0.indecBasis`.

## Main results

* `GProj.exists_iso_sumList` : **existence**: every `P ∈ A-pmod` is isomorphic (by a
  degree-preserving isomorphism) to some `sumList l`.
* `K0.mult_of_sumList` : the multiplicity of `P_b{a}` in `sumList l` is the number of occurrences
  of `(b, a)` in `l`.
* `GProj.perm_of_iso_sumList` and `GProj.nonempty_iso_sumList_iff` : **uniqueness**:
  `sumList l ≅ sumList l'` iff `l` is a permutation of `l'`; so the multiset of pairs `(b, a)` in a
  decomposition of `P` is determined by `P` (`GProj.perm_of_iso_of_iso`).
* `K0.of_eq_of_iff` : `[P] = [P']` in `K₀(A)` iff `P ≅ P'`.
* `GProj.nonempty_iso_of_prod` : **cancellation**: `P ⊕ Q ≅ P' ⊕ Q` implies `P ≅ P'`.
* `K0.mult_of_nonneg`, `K0.of_mem_closure_rep_shift`, `K0.exists_of_eq_iff` : **positivity**: the
  classes of objects of `A-pmod` are exactly the elements of `K₀(A)` whose coordinates in the basis
  `{[P_b]}` lie in `ℕ[q, q⁻¹]`.
* `K0.homRank_top_shift` : `dim_k HOM(P, S_b{a})_0 = mult [P] b a · dim_k END(S_b)_0`, so
  multiplicities are read off from degree-zero homomorphisms into the graded simple tops
  `S_b = IndecClass.top b` (`K0.mult_eq_div`), and `K0.nonempty_iso_iff_finrank_homGrade` : `P ≅ P'`
  iff `dim_k HOM(P, S)_0 = dim_k HOM(P', S)_0` for all graded simples `S = S_b{a}`.
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum Module Function GProj GProj.IndecClass

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

namespace GProj

/-! ### Structural isomorphisms in `A-pmod` -/

section Structural

/-- `(P ⊕ Q) ⊕ R ≅ P ⊕ (Q ⊕ R)`. -/
def prodAssocIso (P Q R : GProj 𝒜) : ((P.prod Q).prod R).Iso (P.prod (Q.prod R)) where
  toLinearEquiv := LinearEquiv.prodAssoc A P.carrier Q.carrier R.carrier
  map_mem' _ _ h := ⟨h.1.1, h.1.2, h.2⟩
  symm_map_mem' _ _ h := ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- `P ⊕ Q ≅ Q ⊕ P`. -/
def prodCommIso (P Q : GProj 𝒜) : (P.prod Q).Iso (Q.prod P) :=
  GradedEquiv.prodComm P.grading Q.grading

/-- Direct sums of isomorphisms. -/
def prodCongrIso {P P' Q Q' : GProj 𝒜} (e : P.Iso P') (f : Q.Iso Q') :
    (P.prod Q).Iso (P'.prod Q') :=
  GradedEquiv.prodCongr e f

/-- Any two zero objects of `A-pmod` are isomorphic. -/
def isoOfSubsingleton (P Q : GProj 𝒜) [Subsingleton P.carrier] [Subsingleton Q.carrier] :
    P.Iso Q :=
  GradedEquiv.ofLinearMaps (0 : P.carrier →ₗ[A] Q.carrier) (0 : Q.carrier →ₗ[A] P.carrier)
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ => by rw [LinearMap.zero_apply]; exact zero_mem _)
    (fun _ _ _ => by rw [LinearMap.zero_apply]; exact zero_mem _)

/-- `P ⊕ Z ≅ P` for a zero object `Z`. -/
def prodSubsingletonIso (P Z : GProj 𝒜) [Subsingleton Z.carrier] : (P.prod Z).Iso P :=
  GradedEquiv.ofLinearMaps (LinearMap.fst A P.carrier Z.carrier)
    (LinearMap.inl A P.carrier Z.carrier) (fun _ => Prod.ext rfl (Subsingleton.elim _ _))
    (fun _ => rfl) (fun _ _ h => h.1) (fun _ _ h => ⟨h, zero_mem _⟩)

variable [GradedAlgebra 𝒜]

variable (𝒜) in
/-- The zero object of `A-pmod` (realized as the image of the zero endomorphism of `A`). -/
def zeroObj : GProj 𝒜 :=
  (GProj.regular 𝒜).summand (e := 0) IsIdempotentElem.zero
    (fun _ _ _ => by rw [LinearMap.zero_apply]; exact zero_mem _)

instance : Subsingleton (zeroObj 𝒜).carrier :=
  ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    rfl⟩

end Structural

/-! ### Direct sums of shifted indecomposables -/

section SumList

variable [GradedAlgebra 𝒜]

/-- The direct sum `P_{b₁}{a₁} ⊕ (P_{b₂}{a₂} ⊕ ⋯ ⊕ (P_{bₙ}{aₙ} ⊕ 0))` of shifted chosen
indecomposables, for `l = [(b₁, a₁), …, (bₙ, aₙ)]`. -/
def sumList : List (IndecClass 𝒜 × ℤ) → GProj 𝒜
  | [] => zeroObj 𝒜
  | x :: l => (x.1.rep.shift x.2).prod (sumList l)

@[simp] theorem sumList_nil : sumList ([] : List (IndecClass 𝒜 × ℤ)) = zeroObj 𝒜 := rfl

instance : Subsingleton (sumList ([] : List (IndecClass 𝒜 × ℤ))).carrier :=
  inferInstanceAs (Subsingleton (zeroObj 𝒜).carrier)

@[simp] theorem sumList_cons (x : IndecClass 𝒜 × ℤ) (l : List (IndecClass 𝒜 × ℤ)) :
    sumList (x :: l) = (x.1.rep.shift x.2).prod (sumList l) := rfl

/-- `sumList (l₁ ++ l₂) ≅ sumList l₁ ⊕ sumList l₂`. -/
def sumListAppendIso : (l₁ l₂ : List (IndecClass 𝒜 × ℤ)) →
    (sumList (l₁ ++ l₂)).Iso ((sumList l₁).prod (sumList l₂))
  | [], l₂ => ((prodCommIso _ _).trans (prodSubsingletonIso (sumList l₂) (zeroObj 𝒜))).symm
  | x :: l₁, l₂ =>
    (prodCongrIso (GradedEquiv.refl _) (sumListAppendIso l₁ l₂)).trans
      (prodAssocIso (x.1.rep.shift x.2) (sumList l₁) (sumList l₂)).symm

/-- A permutation of the summands gives an isomorphic direct sum. -/
theorem nonempty_iso_sumList_of_perm {l l' : List (IndecClass 𝒜 × ℤ)} (h : l.Perm l') :
    Nonempty ((sumList l).Iso (sumList l')) := by
  induction h with
  | nil => exact ⟨GradedEquiv.refl _⟩
  | cons x _ ih => exact ⟨prodCongrIso (GradedEquiv.refl _) ih.some⟩
  | swap x y l =>
    exact ⟨((prodAssocIso _ _ _).symm.trans
      (prodCongrIso (prodCommIso _ _) (GradedEquiv.refl _))).trans (prodAssocIso _ _ _)⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.some.trans ih₂.some⟩

variable [HasGdim 𝒜]

/-- **Krull–Schmidt decompositions exist at the level of modules** (KL I, §2.5): every finitely
generated graded projective module is isomorphic, by a degree-preserving isomorphism, to a finite
direct sum `⊕ₜ P_{bₜ}{aₜ}` of shifts of the chosen indecomposables. -/
theorem exists_iso_sumList (P : GProj 𝒜) :
    ∃ l : List (IndecClass 𝒜 × ℤ), Nonempty (P.Iso (sumList l)) := by
  induction h : finrank k (endZero A P.grading) using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    by_cases hP : Nontrivial P.carrier
    · by_cases hind : ∀ e ∈ endZero A P.grading, IsIdempotentElem e → e = 0 ∨ e = 1
      · obtain ⟨b, a, ⟨e⟩⟩ := IndecClass.exists_iso_rep_shift (P := P) ⟨hP, hind⟩
        exact ⟨[(b, a)], ⟨e.trans (prodSubsingletonIso _ (zeroObj 𝒜)).symm⟩⟩
      · push_neg at hind
        obtain ⟨e, hpe, he, he0, he1⟩ := hind
        have h1 := P.nontrivial_summand he hpe he0
        have h2 := P.nontrivial_summand he.one_sub (preservesGrading_one_sub hpe)
          (sub_ne_zero.2 (Ne.symm he1))
        have hle := finrank_endZero_add_le (P.summandIso he hpe)
        have hp1 := finrank_endZero_pos (P := P.summand he hpe)
        have hp2 := finrank_endZero_pos
          (P := P.summand he.one_sub (preservesGrading_one_sub hpe))
        obtain ⟨l₁, ⟨e₁⟩⟩ := ih _ (by omega) (P.summand he hpe) rfl
        obtain ⟨l₂, ⟨e₂⟩⟩ := ih _ (by omega) (P.summand he.one_sub (preservesGrading_one_sub hpe))
          rfl
        exact ⟨l₁ ++ l₂, ⟨((P.summandIso he hpe).trans (prodCongrIso e₁ e₂)).trans
          (sumListAppendIso l₁ l₂).symm⟩⟩
    · rw [not_nontrivial_iff_subsingleton] at hP
      exact ⟨[], ⟨isoOfSubsingleton _ _⟩⟩

end SumList

end GProj

/-! ### Multiplicities -/

namespace K0

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

omit [HasGdim 𝒜] in
/-- The class of `sumList l` is `∑_{(b, a) ∈ l} q^a [P_b]`. -/
theorem of_sumList (l : List (IndecClass 𝒜 × ℤ)) :
    of (sumList l) =
      (l.map fun x => (LaurentPolynomial.T x.2 : LaurentPolynomial ℤ) • of x.1.rep).sum := by
  induction l with
  | nil => exact of_eq_zero_of_subsingleton _
  | cons x l ih => rw [sumList_cons, of_prod, ih, ← T_smul_of, List.map_cons, List.sum_cons]

/-- The multiplicity of `q^a [P_b]` in `x ∈ K₀(A)`: the coefficient of `q^a` in the `b`-th
coordinate of `x` in the basis `K0.indecBasis`. -/
def mult (x : K0 𝒜) (b : IndecClass 𝒜) (a : ℤ) : ℤ := (indecBasis 𝒜).repr x b a

theorem mult_add (x y : K0 𝒜) (b : IndecClass 𝒜) (a : ℤ) :
    mult (x + y) b a = mult x b a + mult y b a := by
  rw [mult, mult, mult, map_add, Finsupp.add_apply, Finsupp.add_apply]

theorem mult_zero (b : IndecClass 𝒜) (a : ℤ) : mult (0 : K0 𝒜) b a = 0 := by
  simp [mult]

open scoped Classical in
theorem mult_T_smul_of_rep (c : IndecClass 𝒜) (d : ℤ) (b : IndecClass 𝒜) (a : ℤ) :
    mult ((LaurentPolynomial.T d : LaurentPolynomial ℤ) • of c.rep) b a =
      if (c, d) = (b, a) then 1 else 0 := by
  rw [mult, ← indecBasis_apply, map_smul, Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  by_cases hc : c = b
  · subst hc
    rw [if_pos rfl, smul_eq_mul, mul_one, LaurentPolynomial.T, Finsupp.single_apply]
    by_cases hd : d = a
    · simp [hd]
    · simp [hd]
  · rw [if_neg hc, smul_zero, if_neg (fun h => hc (Prod.ext_iff.1 h).1)]
    rfl

/-- The multiplicity of `P_b{a}` in `sumList l` is the number of occurrences of `(b, a)` in
`l`. -/
theorem mult_of_sumList [DecidableEq (IndecClass 𝒜 × ℤ)] (l : List (IndecClass 𝒜 × ℤ))
    (b : IndecClass 𝒜) (a : ℤ) : mult (of (sumList l)) b a = l.count (b, a) := by
  induction l with
  | nil => rw [of_sumList, List.map_nil, List.sum_nil, mult_zero, List.count_nil, Nat.cast_zero]
  | cons x l ih =>
    rw [sumList_cons, of_prod, mult_add, ← T_smul_of, mult_T_smul_of_rep, ih, List.count_cons]
    by_cases hx : x = (b, a)
    · subst hx
      simp [add_comm]
    · have : ¬ (x == (b, a)) = true := by simpa using hx
      simp [hx, this]

/-- Coordinates of classes of objects of `A-pmod` are nonnegative. -/
theorem mult_of_nonneg (P : GProj 𝒜) (b : IndecClass 𝒜) (a : ℤ) : 0 ≤ mult (of P) b a := by
  classical
  obtain ⟨l, ⟨e⟩⟩ := P.exists_iso_sumList
  rw [of_eq_of_iso e, mult_of_sumList]
  exact Int.natCast_nonneg _

end K0

namespace GProj

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

/-- Equal classes of direct sums of shifted indecomposables force equal multisets of summands. -/
theorem perm_of_of_sumList_eq {l l' : List (IndecClass 𝒜 × ℤ)}
    (h : K0.of (sumList l) = K0.of (sumList l')) : l.Perm l' := by
  classical
  rw [List.perm_iff_count]
  rintro ⟨b, a⟩
  have := congrArg (fun x => K0.mult x b a) h
  simp only [K0.mult_of_sumList] at this
  exact_mod_cast this

/-- **Uniqueness of Krull–Schmidt decompositions**: `sumList l ≅ sumList l'` iff `l` and `l'`
agree up to permutation. -/
theorem nonempty_iso_sumList_iff {l l' : List (IndecClass 𝒜 × ℤ)} :
    Nonempty ((sumList l).Iso (sumList l')) ↔ l.Perm l' :=
  ⟨fun ⟨e⟩ => perm_of_of_sumList_eq (K0.of_eq_of_iso e), nonempty_iso_sumList_of_perm⟩

theorem perm_of_iso_sumList {l l' : List (IndecClass 𝒜 × ℤ)}
    (e : (sumList l).Iso (sumList l')) : l.Perm l' :=
  nonempty_iso_sumList_iff.1 ⟨e⟩

/-- **Krull–Schmidt uniqueness** (KL I, §2.5): the multiset of pairs `(b, a)` in a decomposition
`P ≅ ⊕ₜ P_{bₜ}{aₜ}` is determined by `P`. -/
theorem perm_of_iso_of_iso {P : GProj 𝒜} {l l' : List (IndecClass 𝒜 × ℤ)}
    (e : P.Iso (sumList l)) (e' : P.Iso (sumList l')) : l.Perm l' :=
  perm_of_iso_sumList (e.symm.trans e')

/-- The multiset of pairs `(b, a)` in a Krull–Schmidt decomposition of `P` (well defined by
`perm_of_iso_of_iso`). -/
def decompMultiset (P : GProj 𝒜) : Multiset (IndecClass 𝒜 × ℤ) :=
  (P.exists_iso_sumList.choose : Multiset (IndecClass 𝒜 × ℤ))

theorem decompMultiset_eq_iff {P : GProj 𝒜} {l : List (IndecClass 𝒜 × ℤ)} :
    P.decompMultiset = l ↔ Nonempty (P.Iso (sumList l)) := by
  obtain ⟨e⟩ := P.exists_iso_sumList.choose_spec
  constructor
  · intro h
    exact ⟨e.trans (nonempty_iso_sumList_of_perm (Quotient.exact h)).some⟩
  · rintro ⟨e'⟩
    exact Quotient.sound (perm_of_iso_of_iso e e')

/-- The multiplicity of `P_b{a}` in `P` is the number of occurrences of `(b, a)` in its
decomposition multiset. -/
theorem mult_of_eq_count_decompMultiset [DecidableEq (IndecClass 𝒜 × ℤ)] (P : GProj 𝒜)
    (b : IndecClass 𝒜) (a : ℤ) : K0.mult (K0.of P) b a = P.decompMultiset.count (b, a) := by
  obtain ⟨e⟩ := P.exists_iso_sumList.choose_spec
  rw [K0.of_eq_of_iso e, K0.mult_of_sumList, decompMultiset, Multiset.coe_count]

end GProj

namespace K0

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

/-- **`[P] = [P']` in `K₀(A)` iff `P ≅ P'`** by a degree-preserving isomorphism. -/
theorem of_eq_of_iff {P P' : GProj 𝒜} : of P = of P' ↔ Nonempty (P.Iso P') := by
  refine ⟨fun h => ?_, fun ⟨e⟩ => of_eq_of_iso e⟩
  obtain ⟨l, ⟨e⟩⟩ := P.exists_iso_sumList
  obtain ⟨l', ⟨e'⟩⟩ := P'.exists_iso_sumList
  have hp : l.Perm l' := perm_of_of_sumList_eq (by rw [← of_eq_of_iso e, ← of_eq_of_iso e', h])
  exact ⟨(e.trans (nonempty_iso_sumList_of_perm hp).some).trans e'.symm⟩

/-- The map from isomorphism classes of `A-pmod` to `K₀(A)` is injective. -/
theorem isoClass_eq_of_of_eq {P P' : GProj 𝒜} (h : of P = of P') : isoClass P = isoClass P' :=
  isoClass_eq_iff.2 (of_eq_of_iff.1 h)

/-- The class of `P` lies in the additive submonoid generated by the `[P_b{a}]`: the coordinates
of `[P]` in the basis `{[P_b]}` lie in `ℕ[q, q⁻¹]`. -/
theorem of_mem_closure_rep_shift (P : GProj 𝒜) :
    of P ∈ AddSubmonoid.closure (Set.range fun x : IndecClass 𝒜 × ℤ => of (x.1.rep.shift x.2)) := by
  obtain ⟨l, ⟨e⟩⟩ := P.exists_iso_sumList
  rw [of_eq_of_iso e]
  clear e
  induction l with
  | nil => rw [sumList_nil, of_eq_zero_of_subsingleton]; exact zero_mem _
  | cons x l ih =>
    rw [sumList_cons, of_prod]
    exact add_mem (AddSubmonoid.subset_closure ⟨x, rfl⟩) ih

omit [HasGdim 𝒜] in
/-- Every element of the additive submonoid generated by the `[P_b{a}]` is the class of an object
of `A-pmod`. -/
theorem exists_of_eq_of_mem_closure {x : K0 𝒜}
    (hx : x ∈ AddSubmonoid.closure (Set.range fun y : IndecClass 𝒜 × ℤ => of (y.1.rep.shift y.2))) :
    ∃ P : GProj 𝒜, of P = x := by
  induction hx using AddSubmonoid.closure_induction with
  | mem _ h =>
    obtain ⟨y, rfl⟩ := h
    exact ⟨_, rfl⟩
  | one => exact ⟨zeroObj 𝒜, of_eq_zero_of_subsingleton _⟩
  | mul _ _ _ _ h₁ h₂ =>
    obtain ⟨P, rfl⟩ := h₁
    obtain ⟨Q, rfl⟩ := h₂
    exact ⟨P.prod Q, of_prod P Q⟩

/-- **The positive cone of `K₀(A)`**: an element of `K₀(A)` is the class of an object of `A-pmod`
iff all its coordinates in the basis `{[P_b]}` lie in `ℕ[q, q⁻¹]`. -/
theorem exists_of_eq_iff (x : K0 𝒜) :
    (∃ P : GProj 𝒜, of P = x) ↔ ∀ b a, 0 ≤ mult x b a := by
  refine ⟨fun ⟨P, hP⟩ => hP ▸ mult_of_nonneg P, fun h => exists_of_eq_of_mem_closure ?_⟩
  set C := AddSubmonoid.closure
    (Set.range fun y : IndecClass 𝒜 × ℤ => of (y.1.rep.shift y.2))
  rw [← (indecBasis 𝒜).linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine AddSubmonoid.sum_mem _ fun b _ => ?_
  rw [← Finsupp.sum_single ((indecBasis 𝒜).repr x b), Finsupp.sum, Finset.sum_smul]
  refine AddSubmonoid.sum_mem _ fun a _ => ?_
  rw [LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.smul_eq_C_mul, smul_assoc,
    indecBasis_apply, T_smul_of]
  have ha : 0 ≤ (indecBasis 𝒜).repr x b a := h b a
  rw [← Int.toNat_of_nonneg ha, natCast_zsmul]
  exact nsmul_mem (AddSubmonoid.subset_closure
    (Set.mem_range_self (f := fun y : IndecClass 𝒜 × ℤ => of (y.1.rep.shift y.2)) (b, a))) _

end K0

namespace GProj

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

/-- **Cancellation** in `A-pmod`: `P ⊕ Q ≅ P' ⊕ Q` implies `P ≅ P'`. -/
theorem nonempty_iso_of_prod {P P' Q : GProj 𝒜} (e : (P.prod Q).Iso (P'.prod Q)) :
    Nonempty (P.Iso P') := by
  have h := K0.of_eq_of_iso e
  rw [K0.of_prod, K0.of_prod] at h
  exact K0.of_eq_of_iff.1 (add_right_cancel h)

end GProj

/-! ### Multiplicities via homomorphisms into graded simples -/

namespace K0

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

instance hasGdim_top_shift (b : IndecClass 𝒜) (a : ℤ) : HasGdim (b.top.shift a).grading :=
  inferInstanceAs (HasGdim (Graded.shift b.top.grading a))

theorem finrank_endZero_top_pos (b : IndecClass 𝒜) :
    0 < finrank k (endZero A b.top.grading) := by
  haveI := (isGradedSimple_top b).nontrivial
  haveI : FiniteDimensional k (endZero A b.top.grading) := by
    haveI := Graded.hasGdim_homGrade (A := A) b.rep.grading b.top.grading
    have h := finrank_homGrade_rep_top b b 0
    rw [if_pos ⟨rfl, rfl⟩] at h
    exact FiniteDimensional.of_finrank_pos (by
      rw [← h]
      exact Module.finrank_pos_iff_exists_ne_zero.2
        ⟨⟨b.topMap, mem_homGrade_zero_of_preservesGrading (preservesGrading_topMap b)⟩,
          fun h' => topMap_ne_zero b (congrArg Subtype.val h')⟩)
  rw [Module.finrank_pos_iff_exists_ne_zero]
  exact ⟨1, fun h => one_ne_zero (congrArg Subtype.val h : (1 : Module.End A b.top) = 0)⟩

/-- `dim_k HOM(P_b{a}, S_b{a})_0 = dim_k END(S_b)_0`. -/
theorem homRank_top_shift_rep_shift (b : IndecClass 𝒜) (a : ℤ) :
    homRank (b.top.shift a) (of (b.rep.shift a)) = finrank k (endZero A b.top.grading) := by
  rw [homRank_of]
  have h : homGrade A (b.rep.shift a).grading (b.top.shift a).grading 0 =
      homGrade A b.rep.grading b.top.grading 0 := by
    show homGrade A (Graded.shift b.rep.grading a) (Graded.shift b.top.grading a) 0 = _
    rw [homGrade_shift_left, homGrade_shift_right, add_zero, sub_self]
  have h2 := finrank_homGrade_rep_top b b 0
  rw [if_pos ⟨rfl, rfl⟩] at h2
  rw [h]
  exact congrArg Nat.cast h2

/-- **Multiplicities are dimensions of degree-zero homomorphisms into simples**:
`dim_k HOM(x, S_b{a})_0 = mult x b a · dim_k END(S_b)_0` for all `x ∈ K₀(A)` (here `homRank` is
the additive extension of `[P] ↦ dim_k HOM(P, S)_0`). -/
theorem homRank_top_shift (x : K0 𝒜) (b : IndecClass 𝒜) (a : ℤ) :
    homRank (b.top.shift a) x = mult x b a * finrank k (endZero A b.top.grading) := by
  classical
  rw [← homRank_top_shift_rep_shift b a]
  conv_lhs => rw [← (indecBasis 𝒜).linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, map_finsuppSum]
  simp only [indecBasis_apply]
  simp only [homRank_smul_of_rep (isGradedSimple_top b) (preservesGrading_topMap b)
    (topMap_ne_zero b) a]
  rw [Finsupp.sum, Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · simp [mult, Finsupp.not_mem_support_iff.1 hmem]

/-- `mult [P] b a = dim_k HOM(P, S_b{a})_0 / dim_k END(S_b)_0`. -/
theorem mult_eq_div (P : GProj 𝒜) (b : IndecClass 𝒜) (a : ℤ) :
    mult (of P) b a = (finrank k (homGrade A P.grading (b.top.shift a).grading 0) : ℤ) /
      finrank k (endZero A b.top.grading) := by
  rw [← homRank_of, homRank_top_shift, Int.mul_ediv_cancel]
  exact_mod_cast (finrank_endZero_top_pos b).ne'

/-- **Objects of `A-pmod` are determined by their degree-zero homomorphisms into graded
simples**: `P ≅ P'` iff `dim_k HOM(P, S_b{a})_0 = dim_k HOM(P', S_b{a})_0` for all `b`, `a`. -/
theorem nonempty_iso_iff_finrank_homGrade {P P' : GProj 𝒜} :
    Nonempty (P.Iso P') ↔ ∀ (b : IndecClass 𝒜) (a : ℤ),
      finrank k (homGrade A P.grading (b.top.shift a).grading 0) =
        finrank k (homGrade A P'.grading (b.top.shift a).grading 0) := by
  refine ⟨fun ⟨e⟩ b a => (finrank_homGrade_congr_left e 0).symm, fun h => ?_⟩
  refine of_eq_of_iff.1 ((indecBasis 𝒜).repr.injective (Finsupp.ext fun b => ?_))
  ext a
  change mult (of P) b a = mult (of P') b a
  rw [mult_eq_div, mult_eq_div, h]

end K0

end Categorification.Graded

end
