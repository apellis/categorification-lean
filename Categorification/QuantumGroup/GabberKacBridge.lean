/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.GabberKacStatement
import LieLean.Algebra.QuantumGroup.GabberKac

/-!
# The quantum Gabber–Kac theorem, from `LieLean`

We prove `CartanDatum.QuantumGabberKac C` (Lusztig, *Introduction to quantum groups*,
Theorem 33.1.3(a)) for every Cartan datum `C`, by comparison with `LieLean`'s theorem
`LusztigF.radical_eq_serreIdeal_ratFunc` (finitely many simple roots, over `ℚ(v)`).

The comparison goes through Mathlib's identification `PreF.equivFreeAlgebra` of `'f` with the free
algebra `LusztigF k I = FreeAlgebra k I`:

* `CartanDatum.toLusztig`: the same Cartan datum as a `LusztigCartanDatum`;
* `PreF.d_equiv`: the twisted derivation `PreF.d` is `LieLean`'s `ᵢr` (`LusztigF.lDeriv`);
* `PreF.counit_equiv`, `PreF.form_equiv`: the counits and Lusztig's forms agree, with
  `(θ_i, θ_i) = (1 - v_i^{-2})⁻¹` on both sides;
* `PreF.serreDiv_equiv`: the divided-power Serre elements agree (`PreF.serreDiv`,
  `LusztigF.serreElement`), and `PreF.serreSeq` is a nonzero multiple of them.

Arbitrary index sets reduce to finite ones (`CartanDatum.quantumGabberKac`): an element of `'f`
involves finitely many letters, and both the radical and the Serre ideal are compatible with the
inclusion of the free algebra on a finite subset of `I`.

## Main results

* `CartanDatum.quantumGabberKac_of_finite`: the canonical statement for finite `I`.
* `CartanDatum.quantumGabberKac`: the canonical statement for every Cartan datum.
* `UDot.KL3.formNondeg_unconditional`, `UDot.KL3.prop_2_5_unconditional`: Khovanov–Lauda III,
  Proposition 2.5, for every Cartan datum.

The unconditional forms of Khovanov–Lauda I, Theorems 1.1 and 3.21, and Khovanov–Lauda II,
Theorem 8, are in `Categorification.KLR.GabberKacConsumers`; those of the KL III bijectivity
results in `Categorification.Diagrams.KL3.GabberKacWrappers`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open PreF

/-- A Cartan datum in the sense of `LieLean` (the same data). -/
def CartanDatum.toLusztig {I : Type*} (C : CartanDatum I) : LusztigCartanDatum I where
  dot := C.dot
  dot_comm := C.symm
  dot_self_pos := C.dot_self_pos
  even_dot_self := C.dot_self_even
  dot_nonpos := C.dot_nonpos
  dot_self_dvd := C.dvd_two_mul

namespace PreF

variable {I : Type*} {K : Type*} [Field K]

theorem equivFreeAlgebra_symm_θ (i : I) :
    (equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I).symm (θ i) = LusztigF.θ K i := by
  rw [AlgEquiv.symm_apply_eq, equivFreeAlgebra_ι]

theorem equivFreeAlgebra_symm_word_of_mul (i : I) (w : FreeMonoid I) :
    (equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I).symm (word (FreeMonoid.of i * w)) =
      LusztigF.θ K i * (equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I).symm (word w) := by
  rw [word_of_mul, map_mul, equivFreeAlgebra_symm_θ]

/-- The counits agree. -/
theorem counit_equiv (x : PreF K I) :
    counit x = LusztigF.counit ((equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I).symm x) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul_word w r =>
    rw [map_smul, map_smul, map_smul]
    congr 1
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul i w _ =>
      rw [counit_word, ite_eq_right (by simp), equivFreeAlgebra_symm_word_of_mul, map_mul]
      simp

variable [DecidableEq I] (C : CartanDatum I) (v : Kˣ)

omit [DecidableEq I] in
theorem two_mul_d (i : I) : 2 * (C.toLusztig.d i : ℤ) = C.dot i i :=
  C.toLusztig.two_mul_d i

/-- The twisted derivation `d_i` of `'f` is `LieLean`'s skew derivation `ᵢr`. -/
theorem d_equiv (i : I) (x : PreF K I) :
    (equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I).symm (d C.dot v i x) =
      LusztigF.lDeriv C.toLusztig (v : K) i
        ((equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I).symm x) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  | smul_word w r =>
    rw [map_smul, map_smul, map_smul, map_smul]
    congr 1
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul j w ih =>
      rw [d_word_of_mul, map_add, map_smul, map_mul, equivFreeAlgebra_symm_θ, ih,
        equivFreeAlgebra_symm_word_of_mul, LusztigF.lDeriv_mul, LusztigF.lDeriv_θ,
        LusztigF.twist_θ, Units.val_zpow_eq_zpow_val, smul_mul_assoc]
      congr 1
      · by_cases h : j = i
        · subst h; simp
        · simp [h, Ne.symm h]
      · simp [CartanDatum.toLusztig, C.symm]

omit [DecidableEq I] in
/-- Lusztig's normalisation `(θ_i, θ_i) = (1 - v^{-i·i})⁻¹` is `LieLean`'s `thetaNorm`. -/
theorem lusztigC_eq_thetaNorm (i : I) :
    lusztigC C.dot v i = LusztigF.thetaNorm C.toLusztig (v : K) i := by
  rw [lusztigC, LusztigF.thetaNorm, Units.val_zpow_eq_zpow_val, inv_pow, ← pow_mul, ← zpow_natCast,
    ← zpow_neg]
  congr 3
  have := two_mul_d C i
  push_cast
  omega

/-- Lusztig's forms agree (with `(θ_i, θ_i) = (1 - v^{-i·i})⁻¹`). -/
theorem form_equiv (x y : PreF K I) :
    form C.dot v (lusztigC C.dot v) x y =
      LusztigF.form C.toLusztig (v : K)
        ((equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I).symm x)
        ((equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I).symm y) := by
  induction x using induction_linear generalizing y with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | smul_word w r =>
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    induction w using FreeMonoid.inductionOn' generalizing y with
    | one => rw [word_one, form_one, map_one, LusztigF.form_one_left, counit_equiv]
    | of_mul i w ih =>
      rw [word_of_mul, form_θ_mul, ih, ← word_of_mul, equivFreeAlgebra_symm_word_of_mul,
        LusztigF.form_θ_mul, d_equiv, lusztigC_eq_thetaNorm]

/-- The radicals agree. -/
theorem mem_radical_iff_equiv (x : PreF K I) :
    x ∈ radical C.dot v (lusztigC C.dot v) ↔
      (equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I).symm x ∈
        LusztigF.radical C.toLusztig (v : K) := by
  rw [mem_radical, LusztigF.mem_radical_iff]
  refine ⟨fun h y => ?_, fun h y => ?_⟩
  · have := h ((equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I) y)
    rwa [form_equiv, AlgEquiv.symm_apply_apply] at this
  · rw [form_equiv]; exact h _

/-- `LieLean`'s quantum integers are ours. -/
theorem qInt_eq_qint (t : Kˣ) (n : ℕ) : LieLean.QuantumGroup.qInt (t : K) n = qint t n := by
  rw [LieLean.QuantumGroup.qInt, qint_eq_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs := Finset.mem_range.1 hs
  rw [Units.val_zpow_eq_zpow_val, inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg,
    ← zpow_add₀ t.ne_zero]
  congr 1
  push_cast [Nat.sub_sub, Nat.cast_sub (by omega : 1 + s ≤ n)]
  ring

theorem qFactorial_eq_qfact (t : Kˣ) (n : ℕ) :
    LieLean.QuantumGroup.qFactorial (t : K) n = qfact t n := by
  induction n with
  | zero => simp [LieLean.QuantumGroup.qFactorial, qfact]
  | succ n ih =>
    rw [LieLean.QuantumGroup.qFactorial, ih, qfact, qfact, Finset.prod_range_succ, qInt_eq_qint,
      mul_comm]

omit [DecidableEq I] in
theorem val_vi (i : I) : ((vi C.dot v i : Kˣ) : K) = (v : K) ^ C.toLusztig.d i := by
  rw [vi, Units.val_zpow_eq_zpow_val, ← zpow_natCast]
  congr 1
  have := two_mul_d C i
  omega

omit [DecidableEq I] in
theorem qDivPow_equiv (i : I) (a : ℕ) :
    (equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I).symm (dpow C.dot v i a) =
      LieLean.QuantumGroup.qDivPow ((v : K) ^ C.toLusztig.d i) a (LusztigF.θ K i) := by
  rw [dpow, map_smul, map_pow, equivFreeAlgebra_symm_θ, LieLean.QuantumGroup.qDivPow, ← val_vi,
    qFactorial_eq_qfact]

omit [DecidableEq I] in
/-- The divided-power Serre elements agree. -/
theorem serreDiv_equiv (i j : I) :
    (equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I).symm
        (serreDiv C.dot v i j (C.serreN i j)) =
      LusztigF.serreElement C.toLusztig (v : K) i j := by
  have hN : (1 - C.toLusztig.cartanMatrix i j).toNat = C.serreN i j := rfl
  rw [serreDiv, map_sum, ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, LusztigF.serreElement,
    LieLean.QuantumGroup.qSerreDiv, hN]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Prod.swap_prod_mk, map_smul, map_mul, qDivPow_equiv, equivFreeAlgebra_symm_θ]

end PreF

namespace CartanDatum

variable {I : Type*} (C : CartanDatum I)

/-- **The quantum Gabber–Kac theorem** (Lusztig, Theorem 33.1.3(a)) for a Cartan datum with
finitely many simple roots, from `LusztigF.radical_eq_serreIdeal_ratFunc`. -/
theorem quantumGabberKac_of_finite [Finite I] : C.QuantumGabberKac := by
  classical
  refine le_antisymm (fun x hx => ?_) (C.span_serreSet_le_radical vQ C.c)
  have hx' := (PreF.mem_radical_iff_equiv C vQ x).1 hx
  rw [vQ_val, LusztigF.radical_eq_serreIdeal_ratFunc] at hx'
  rw [TwoSidedIdeal.mem_asIdeal, ← AlgEquiv.apply_symm_apply
    (PreF.equivFreeAlgebra : FreeAlgebra (RatFunc ℚ) I ≃ₐ[RatFunc ℚ] PreF (RatFunc ℚ) I) x]
  generalize (PreF.equivFreeAlgebra : FreeAlgebra (RatFunc ℚ) I ≃ₐ[RatFunc ℚ] PreF (RatFunc ℚ) I).symm
    x = y at hx' ⊢
  induction hx' using TwoSidedIdeal.span_induction with
  | mem y hy =>
    obtain ⟨i, j, hij, rfl⟩ := hy
    have e := PreF.serreDiv_equiv C vQ i j
    rw [vQ_val] at e
    rw [← e, AlgEquiv.apply_symm_apply]
    have hs : PreF.serreDiv C.dot vQ i j (C.serreN i j) =
        (qfact (PreF.vi C.dot vQ i) (C.serreN i j))⁻¹ •
          PreF.serreSeq C.dot vQ i j (C.serreN i j) := by
      rw [C.serreSeq_eq_qfact_smul_serreDiv hij, smul_smul,
        inv_mul_cancel₀ (C.qfact_ne_zero i _), one_smul]
    rw [hs, Algebra.smul_def]
    exact TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span ⟨i, j, hij, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact TwoSidedIdeal.add_mem _ ha hb
  | neg a _ ha => rw [map_neg]; exact TwoSidedIdeal.neg_mem _ ha
  | left_absorb a b _ hb => rw [map_mul]; exact TwoSidedIdeal.mul_mem_left _ _ _ hb
  | right_absorb a b _ ha => rw [map_mul]; exact TwoSidedIdeal.mul_mem_right _ _ _ ha

/-- The restriction of a Cartan datum to a subset of its index set. -/
def restrict (S : Set I) : CartanDatum S where
  dot i j := C.dot i j
  symm i j := C.symm i j
  dot_self_pos i := C.dot_self_pos i
  dot_self_even i := C.dot_self_even i
  dot_nonpos i j h := C.dot_nonpos i j fun h' => h (Subtype.ext h')
  dvd_two_mul i j := C.dvd_two_mul i j

end CartanDatum

/-! ### Reduction to finitely many simple roots -/

namespace PreF

variable {I : Type*} {K : Type*} [Field K] (S : Set I)

/-- The inclusion `'f(S) → 'f(I)` of the free algebra on a subset of the generators. -/
def incl : PreF K S →ₐ[K] PreF K I :=
  MonoidAlgebra.mapDomainAlgHom K K (FreeMonoid.map (Subtype.val : S → I))

theorem incl_word (w : FreeMonoid S) :
    incl S (word w : PreF K S) = word (FreeMonoid.map Subtype.val w) := by
  simp [incl, word]

theorem incl_θ (i : S) : incl S (θ i : PreF K S) = θ (i : I) := by
  rw [θ, incl_word, FreeMonoid.map_of]; rfl

theorem incl_word_of_mul (i : S) (w : FreeMonoid S) :
    incl S (word (FreeMonoid.of i * w) : PreF K S) = θ (i : I) * incl S (word w) := by
  rw [word_of_mul, map_mul, incl_θ]

theorem counit_incl (x : PreF K S) : counit (incl S x) = counit x := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | smul_word w r =>
    rw [map_smul, map_smul, map_smul]
    congr 1
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul i w _ => rw [incl_word_of_mul, word_of_mul, counit_θ_mul, counit_θ_mul]

variable (C : CartanDatum I) (v : Kˣ)

theorem d_incl (i : S) (y : PreF K S) :
    d C.dot v i (incl S y) = incl S (d (C.restrict S).dot v i y) := by
  induction y using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | smul_word w r =>
    rw [map_smul, map_smul, map_smul, map_smul]
    congr 1
    induction w using FreeMonoid.inductionOn' with
    | one => rw [word_one, map_one, d_one, d_one, map_zero]
    | of_mul j w ih =>
      rw [incl_word_of_mul, d_θ_mul, ih, d_word_of_mul, map_add, map_smul, map_mul, incl_θ]
      congr 1
      by_cases h : j = i
      · subst h; simp
      · simp [h, Subtype.coe_ne_coe.2 h]

theorem form_incl (c : I → K) (x y : PreF K S) :
    form C.dot v c (incl S x) (incl S y) = form (C.restrict S).dot v (c ∘ Subtype.val) x y := by
  induction x using induction_linear generalizing y with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | smul_word w r =>
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    induction w using FreeMonoid.inductionOn' generalizing y with
    | one => rw [word_one, map_one, form_one, form_one, counit_incl]
    | of_mul i w ih =>
      rw [incl_word_of_mul, form_θ_mul, d_incl, ih, word_of_mul, form_θ_mul]
      rfl

theorem serreSeq_incl (i j : S) (m : ℕ) :
    incl S (serreSeq (C.restrict S).dot v i j m) = serreSeq C.dot v (i : I) j m := by
  induction m with
  | zero => exact incl_θ S j
  | succ m ih =>
    rw [serreSeq_succ, serreSeq_succ, map_sub, map_mul, map_smul, map_mul, incl_θ, ih]
    rfl

theorem word_mem_range (w : FreeMonoid I) (h : ∀ a ∈ FreeMonoid.toList w, a ∈ S) :
    word w ∈ LinearMap.range (incl (K := K) S).toLinearMap := by
  refine ⟨word (FreeMonoid.ofList ((FreeMonoid.toList w).pmap Subtype.mk h)), ?_⟩
  rw [AlgHom.toLinearMap_apply, incl_word]
  congr 1
  apply FreeMonoid.toList.injective
  rw [FreeMonoid.toList_map, FreeMonoid.toList_ofList, List.map_pmap, List.pmap_eq_self]
  exact fun _ _ => rfl

/-- Every element of `'f` lies in the free algebra on finitely many generators. -/
theorem exists_incl_eq (x : PreF K I) :
    ∃ S : Set I, S.Finite ∧ ∃ x' : PreF K S, incl S x' = x := by
  suffices h : ∃ T : Set I, T.Finite ∧ ∀ S : Set I, T ⊆ S →
      x ∈ LinearMap.range (incl (K := K) S).toLinearMap by
    obtain ⟨T, hT, h⟩ := h
    obtain ⟨x', hx'⟩ := h T le_rfl
    exact ⟨T, hT, x', hx'⟩
  induction x using induction_linear with
  | zero => exact ⟨∅, Set.finite_empty, fun S _ => Submodule.zero_mem _⟩
  | add x y hx hy =>
    obtain ⟨T, hT, hx⟩ := hx
    obtain ⟨T', hT', hy⟩ := hy
    exact ⟨T ∪ T', hT.union hT', fun S hS =>
      Submodule.add_mem _ (hx S (Set.subset_union_left.trans hS))
        (hy S (Set.subset_union_right.trans hS))⟩
  | smul_word w r =>
    exact ⟨{a | a ∈ FreeMonoid.toList w}, List.finite_toSet _, fun S hS =>
      Submodule.smul_mem _ _ (word_mem_range S w fun a ha => hS ha)⟩

end PreF

namespace CartanDatum

variable {I : Type*} (C : CartanDatum I)

/-- **The quantum Gabber–Kac theorem** (Lusztig, *Introduction to quantum groups*, Theorem
33.1.3(a)) for every Cartan datum: over `ℚ(v)` with Lusztig's normalisation, the radical of the
bilinear form on `'f` is the two-sided ideal generated by the quantum Serre elements. -/
theorem quantumGabberKac : C.QuantumGabberKac := by
  refine le_antisymm (fun x hx => ?_) (C.span_serreSet_le_radical vQ C.c)
  obtain ⟨S, hS, x, rfl⟩ := PreF.exists_incl_eq x
  have : Finite S := hS.to_subtype
  have hx' : x ∈ PreF.radical (C.restrict S).dot vQ (C.restrict S).c := fun y => by
    have := hx (PreF.incl S y)
    rwa [PreF.form_incl] at this
  have h := (C.restrict S).quantumGabberKac_of_finite
  unfold QuantumGabberKac GabberKac at h
  rw [h, TwoSidedIdeal.mem_asIdeal] at hx'
  rw [TwoSidedIdeal.mem_asIdeal]
  clear hx
  induction hx' using TwoSidedIdeal.span_induction with
  | mem y hy =>
    obtain ⟨i, j, hij, rfl⟩ := hy
    exact TwoSidedIdeal.subset_span ⟨i, j, Subtype.coe_ne_coe.2 hij, PreF.serreSeq_incl S C vQ i j _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact TwoSidedIdeal.add_mem _ ha hb
  | neg a _ ha => rw [map_neg]; exact TwoSidedIdeal.neg_mem _ ha
  | left_absorb a b _ hb => rw [map_mul]; exact TwoSidedIdeal.mul_mem_left _ _ _ hb
  | right_absorb a b _ ha => rw [map_mul]; exact TwoSidedIdeal.mul_mem_right _ _ _ ha

end CartanDatum

/-! ### KL III, Proposition 2.5 -/

namespace UDot.KL3

variable {I : Type*} {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y)

/-- **Khovanov–Lauda III, Proposition 2.5 for `( , )`** (arXiv:0807.3250v1, §2.1.3), for an
arbitrary Cartan datum. -/
theorem formNondeg_unconditional : FormNondeg RD :=
  formNondeg_of_quantumGabberKac RD C.quantumGabberKac

/-- **Khovanov–Lauda III, Proposition 2.5** (arXiv:0807.3250v1, §2.1.3): both `( , )` and
`⟨ , ⟩` are nondegenerate on `U̇`, for an arbitrary Cartan datum. -/
theorem prop_2_5_unconditional : FormNondeg RD ∧ ∀ x, (∀ y, sform RD x y = 0) → x = 0 :=
  prop_2_5_of_quantumGabberKac RD C.quantumGabberKac

end UDot.KL3

end Categorification.QuantumGroup

end
