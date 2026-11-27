/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtWrapHom
import Categorification.WeightedKLR.Rigidity.RigidityExtStandardSum
import Categorification.WeightedKLR.Rigidity.RigidityExtRankOne

/-!
# Corollary 7.7, top degree

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Corollary 7.7, top degree.

* `GProj.exists_smul_eq_of_homGdim_eq_one`: for a norm-one projective `A e`, `e A e = k e`.
* `ProjectiveResolution.extLinearEquivHomZero`: `Ext⁰(X, Y) ≅ Hom(P₀, Y)` when `P₁ = 0`.
* `Stendhal.exists_extLinearEquiv_standard`: the `k`-linear form of
  `exists_extAddEquiv_standard`, in every degree `|u|` including `0`.
-/

universe v

open CategoryTheory Abelian Limits MulOpposite

/-! ### Endomorphisms of a norm-one projective -/

namespace Categorification.Graded.GProj

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [HasGdim 𝒜]

/-- For a projective `A e` with graded endomorphism series one, every element of `e A e` is a
multiple of `e` (Webster, arXiv:1309.3796v3, §7.1, proof of Lemma 7.3). -/
theorem exists_smul_eq_of_homGdim_eq_one {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0)
    (a : ℤ) (hn : homGdim ((ofIdempotent e he he0).shift a) ((ofIdempotent e he he0).shift a) = 1)
    (x : A) (hx : e * x * e = x) : ∃ c : k, x = c • e := by
  let P := (ofIdempotent e he he0).shift a
  let val : P.carrier → A := fun p => ((show leftIdeal e from p) : A)
  have hval_smul (c : A) (p : P.carrier) : val (c • p) = c * val p := rfl
  have hval_add (p q : P.carrier) : val (p + q) = val p + val q := rfl
  have hxe : x * e = x := by rw [← hx, mul_assoc, he.eq]
  have hex : e * x = x := by rw [← hx, ← mul_assoc, ← mul_assoc, he.eq]
  let mk' : A → P.carrier := fun y => show leftIdeal e from ⟨y * e,
    show y * e * e = y * e by rw [mul_assoc, he.eq]⟩
  have hmk' (y : A) : val (mk' y) = y * e := rfl
  let g : P.carrier →ₗ[A] P.carrier :=
    { toFun p := mk' (val p * x)
      map_add' p q := by
        apply Subtype.ext
        change (val (p + q) * x) * e = (val p * x) * e + (val q * x) * e
        rw [hval_add, add_mul, add_mul]
      map_smul' c p := by
        apply Subtype.ext
        change (val (c • p) * x) * e = c * ((val p * x) * e)
        rw [hval_smul, mul_assoc, mul_assoc, mul_assoc] }
  obtain ⟨c, hc⟩ := exists_scalar_of_homGdim_eq_one P hn g
  let ge : P.carrier := show leftIdeal e from ⟨e, he.eq⟩
  have h := congrArg val (LinearMap.congr_fun hc ge)
  change (e * x) * e = val (c • ge) at h
  rw [hex, hxe] at h
  refine ⟨c, h.trans ?_⟩
  rw [← algebraMap_smul A c ge, hval_smul, Algebra.smul_def]

end Categorification.Graded.GProj

/-! ### Ext in degree zero through a projective resolution -/

namespace CategoryTheory.ProjectiveResolution

variable {C : Type*} [Category C] [Abelian C] [HasExt.{v} C] {X Y : C}
  (P : ProjectiveResolution X) {R : Type*} [CommRing R] [Linear R C]

/-- `Ext⁰(X, Y) ≅ Hom(P₀, Y)` when the term `P₁` of a projective resolution of `X` is zero. -/
noncomputable def extLinearEquivHomZero (hz : IsZero (P.complex.X 1)) :
    Ext X Y 0 ≃ₗ[R] (P.complex.X 0 ⟶ Y) :=
  have : IsIso (P.π.f 0) :=
    CokernelCofork.IsColimit.isIso_π _ P.isColimitCokernelCofork (hz.eq_of_src _ _)
  Ext.linearEquiv₀.trans (Linear.homCongr R (asIso (P.π.f 0)).symm (Iso.refl Y))

end CategoryTheory.ProjectiveResolution

/-- If `V^J ≅ W^{J'}` for nonempty finite `J`, `J'` of the same cardinality and `W` is
finite-dimensional, then `V` and `W` have the same dimension. -/
theorem finrank_eq_of_linearEquiv_pi {k : Type*} [Field k] {V W : Type*} [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W] {J J' : Type*}
    [Fintype J] [Fintype J'] [Nonempty J] (hc : Fintype.card J = Fintype.card J')
    (e : (J → V) ≃ₗ[k] (J' → W)) : Module.finrank k V = Module.finrank k W :=
  finrank_eq_of_linearEquiv_fun (e.trans (LinearEquiv.funCongrLeft k W (Fintype.equivOfCardEq hc)))

/-! ### Ext out of a standard module in the top degree, `k`-linearly -/

namespace Categorification.Stendhal

open KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

section Ext

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) {ν : Multiset I}
  (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ) {θ : Multiset I} (t : Seq (stendhalWeight ℓ θ))
  (ht : IsRedOrdered t) (u : List I) (h : θ + wordWt u 0 = ν)
  (Y : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]

include hR hall in
/-- **Ext out of a standard module in the top degree**, `k`-linearly (Webster,
arXiv:1309.3796v3, §7.1, proof of Corollary 7.7): if no projective `T^λ e(i_T)` with
`|T| = |u| - 1` of the resolution of Proposition 7.6 maps nontrivially to `Y`, then
`Ext^{|u|}(S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u.reverse)), Y) ≅ Hom(T^λ e(s), Y)` for the loading `s`
with word `t, u, λ_ℓ`. Under the route hypothesis `hall` of Proposition 7.6. -/
theorem exists_extLinearEquiv_standard
    (hY : ∀ p, p + 1 = u.length → ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s),
      s.word ∈ websterWords (t.word.map (addRedColor ℓ)) u.reverse p →
        Subsingleton (loadingProj Q Λ s hs ⟶ Y)) :
    ∃ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s),
      s.word = t.word.map (addRedColor ℓ) ++ u.map Sum.inl ++ [Sum.inr (Fin.last ℓ)] ∧
        Nonempty (Ext (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ u)) Y u.length ≃ₗ[k]
          (loadingProj Q Λ s hs ⟶ Y)) := by
  obtain ⟨P, hP⟩ := exists_projectiveResolution_websterWords Q Λ hQ hR hall t ht u h
  have htop := hP u.reverse.length
  rw [websterWords_length, websterWord_range, List.reverse_reverse, List.length_reverse] at htop
  obtain ⟨s, hs, hw, ⟨e⟩⟩ := htop.exists_equiv_of_singleton
  have hz : IsZero (P.complex.X (u.length + 1)) := by
    have := hP (u.length + 1)
    rw [websterWords_eq_zero _ _ (by simp)] at this
    exact this.isZero
  refine ⟨s, hs, hw, ⟨?_⟩⟩
  have key : Nonempty (Ext (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ u)) Y
      u.length ≃ₗ[k] (P.complex.X u.length ⟶ Y)) := by
    rcases hu : u.length with _ | p
    · rw [hu] at hz
      exact ⟨P.extLinearEquivHomZero hz⟩
    · rw [hu] at hz
      have := (hP p).subsingleton_hom (hY p hu.symm)
      exact ⟨P.extLinearEquivHom p (p + 1) rfl hz⟩
  exact key.some.trans (Linear.homCongr k e (Iso.refl Y))

end Ext

/-! ### Divided-power splittings -/

section Divided

open KLRAlgebra

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

omit [DecidableEq I] in
theorem expandDiv_reverse (d : List (I × ℕ)) : expandDiv d.reverse = (expandDiv d).reverse := by
  induction d with
  | nil => rfl
  | cons q d ih =>
    simp only [expandDiv] at ih ⊢
    simp [List.flatMap_append, ih]

omit [DecidableEq I] in
theorem coe_expandDiv_reverse (d : List (I × ℕ)) :
    (expandDiv d.reverse : Multiset I) = wordWt (expandDiv d) 0 := by
  rw [expandDiv_reverse, coe_reverse_eq_wordWt]

/-- **`e(î)` splits through the reflected divided-power idempotent in a cyclotomic quotient**:
the image of `exists_isSplitting_e` under the horizontal flip and the cyclotomic projection. -/
theorem exists_isSplitting_cyc_hflip (a' : I → Polynomial k) {β : Multiset I} {s : Seq β}
    {bs : List (ℕ × ℕ)} (hb : IsBlocks s bs) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (a b : ι → CycKLR k Q a' β),
      Graded.IsSplitting (CycKLR.mk k Q a' β (KLRAlgebra.e s))
        (fun _ => CycKLR.mk k Q a' β (KLRAlgebra.hflip (KLRAlgebra.divIdem s bs))) a b ∧
        Fintype.card ι = (bs.map fun b => b.2.factorial).prod := by
  obtain ⟨ι, _, _, a, b, hS, hc⟩ := KLRAlgebra.exists_isSplitting_e (k := k) (Q := Q) hb
  have hS' := hS.map_anti (AddMonoidHom.mk' KLRAlgebra.hflip KLRAlgebra.hflip_add)
    KLRAlgebra.hflip_mul
  simp only [AddMonoidHom.mk'_apply, KLRAlgebra.hflip_e] at hS'
  exact ⟨ι, inferInstance, inferInstance, _, _, hS'.map (CycKLR.mk k Q a' β), hc⟩

/-- The projective `R^{λ_ℓ} 1_{d̄}` of the divided-power idempotent (reflected, as in
`dividedProjective`) of the reversed divided word `d̄ = d.reverse`, over the cyclotomic quotient
of the last red strand. Its standardization with `T^{λ'} e(t)` has `T^λ e(t, d̂, λ_ℓ)` in the top
degree of its resolution. -/
noncomputable abbrev cycDivProj (d : List (I × ℕ)) :
    ModuleCat.{0} (CycKLR k Q (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j) (wordWt (expandDiv d) 0)) :=
  ModuleCat.of _ (lIdeal (CycKLR.mk k Q (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j) _
    (KLRAlgebra.hflip (KLRAlgebra.divIdem
    (KLRAlgebra.Seq.ofList (expandDiv d.reverse) (coe_expandDiv_reverse d))
    (blocksDiv d.reverse 0)))))

/-- **`R^{λ_ℓ} e(d̂)` is a sum of `∏ nₐ!` copies of `R^{λ_ℓ} 1_{d̄}`**: a bicone over the constant
family `cycDivProj d` with point `cycWord (expandDiv d)`. -/
theorem exists_bicone_cycWord_cycDivProj (d : List (I × ℕ)) :
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
      (ι : J → (cycDivProj Q Λ d →ₗ[CycKLR k Q (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j)
        (wordWt (expandDiv d) 0)] cycWord Q Λ (expandDiv d)))
      (π : J → (cycWord Q Λ (expandDiv d) →ₗ[CycKLR k Q
        (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j) (wordWt (expandDiv d) 0)] cycDivProj Q Λ d)),
      (∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0) ∧
      ∑ j, (ι j).comp (π j) = LinearMap.id ∧
      Fintype.card J = (d.map fun q => q.2.factorial).prod := by
  have hseq : KLRAlgebra.Seq.ofList (expandDiv d.reverse) (coe_expandDiv_reverse d) =
      KLRAlgebra.Seq.ofList (expandDiv d).reverse (coe_reverse_eq_wordWt _) :=
    Seq.word_injective (by rw [Seq.word_ofList, Seq.word_ofList, expandDiv_reverse])
  obtain ⟨J, _, _, a, b, hS, hc⟩ := exists_isSplitting_cyc_hflip (Q := Q)
    (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j) (isBlocks_ofList d.reverse
      (coe_expandDiv_reverse d))
  have he : CycKLR.mk k Q (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j) _ (KLRAlgebra.e
      (KLRAlgebra.Seq.ofList (expandDiv d.reverse) (coe_expandDiv_reverse d))) =
      CycKLR.mk k Q (fun j => Polynomial.X ^ Λ (Fin.last ℓ) j) _ (KLRAlgebra.e
        (KLRAlgebra.Seq.ofList (expandDiv d).reverse (coe_reverse_eq_wordWt _))) := by
    rw [hseq]
  rw [he] at hS
  obtain ⟨g⟩ := nonempty_cycWord_equiv_cycProj Q Λ (expandDiv d)
  refine ⟨J, inferInstance, inferInstance,
    fun j => g.symm.toLinearMap.comp (lIdealSplitIncl hS j),
    fun j => (lIdealSplitProj hS j).comp g.toLinearMap, fun i j => ?_, ?_, ?_⟩
  · refine LinearMap.ext fun w => ?_
    have h := LinearMap.congr_fun (lIdealSplitProj_comp_incl hS i j) w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h ⊢
    exact h
  · refine LinearMap.ext fun x => ?_
    have h := LinearMap.congr_fun (sum_lIdealSplitIncl_comp_proj hS) (g x)
    rw [LinearMap.sum_apply] at h ⊢
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at h ⊢
    rw [← map_sum, h, LinearEquiv.symm_apply_apply]
  · rw [hc, prod_factorial_blocksDiv, List.map_reverse, List.prod_reverse]


end Divided

/-! ### The coevaluation standard module and the head of the wrap projective -/

section Coevaluation

open KLRAlgebra TwoRedErase

variable {I : Type} {k : Type} [DecidableEq I] [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 2 → I →₀ ℕ)

omit [DecidableEq I] in
/-- The word of the wrap loading: the first red strand, the black word, the second red strand. -/
theorem word_wrap {ν : Multiset I} (t : Seq ν) :
    (wrap ν t).word = Sum.inr 0 :: t.word.map Sum.inl ++ [Sum.inr 1] := by
  rw [wrap, seqWord_appendRedLoading, SingleRed.insertWord, Seq.word_cast, Seq.word_append,
    Seq.word_map, Seq.word_singleton]
  simp [addRedColor]

omit [DecidableEq I] in
/-- The only loading of a single red strand. -/
theorem word_eq_of_stendhalWeight_one_zero (t : Seq (stendhalWeight 1 (0 : Multiset I))) :
    t.word = [Sum.inr 0] := by
  have h : ((t.word : List _) : Multiset _) = stendhalWeight 1 (0 : Multiset I) := by
    rw [Seq.word, ← Fin.univ_val_map]
    exact t.2
  have h1 : stendhalWeight 1 (0 : Multiset I) = {Sum.inr 0} := by simp [stendhalWeight]
  exact Multiset.coe_eq_singleton.1 (h.trans h1)

/-- The head of the wrap projective is killed by the cuts (as `coevaluationHead_cut`, for any
idempotent `z` of the first red strand's cyclotomic quotient). -/
theorem wrapHead_cut {ν : Multiset I} (z : CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) ν)
    (s : Seq (stendhalWeight 2 ν)) (hs : IsRedOrdered s) (hcut : ¬HasLastRed s)
    (y : rIdeal (wrapIdem Q Λ ν z) ⧸ coevaluationTrace (cutIdem Q Λ ν)) :
    op (loadingIdem Q Λ s hs) • y = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine Submodule.subset_span ⟨⟨⟨s, hs⟩, hcut⟩, ?_⟩
    change x.val * loadingIdem Q _ s hs * loadingIdem Q _ s hs =
      x.val * loadingIdem Q _ s hs
    rw [mul_assoc, (isIdempotentElem_mk_e s hs).eq]

variable (d : List (I × ℕ))

local notation "νᵈ" => (expandDiv d : Multiset I)
local notation "z₀" => CycKLR.mk k Q (fun i => Polynomial.X ^ Λ 0 i) (expandDiv d : Multiset I)
  (hflip (divIdem (Seq.ofList (expandDiv d) rfl) (blocksDiv d 0)))

/-- **`e(wrap d̂)` is a sum of `∏ nₐ!` copies of the reflected wrap idempotent of `1_d`.** -/
theorem exists_isSplitting_wrap :
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (a b : J → TensorProductAlgebra k Q Λ νᵈ),
      Graded.IsSplitting (loadingIdem Q Λ (wrap νᵈ (Seq.ofList (expandDiv d) rfl))
          (wrap_ordered νᵈ _))
        (fun _ => tensorFlip (wrapIdem Q Λ νᵈ z₀)) a b ∧
      Fintype.card J = (d.map fun q => q.2.factorial).prod := by
  obtain ⟨J, _, _, a, b, hS, hc⟩ := exists_isSplitting_cyc_hflip (Q := Q)
    (fun i => Polynomial.X ^ Λ 0 i) (isBlocks_ofList d rfl)
  have h2 := (hS.map_mul (wrapIdemHom Q Λ νᵈ) (fun x y => (wrapIdem_mul Q Λ νᵈ x y).symm)).map_anti
    (tensorFlip (Q := Q) (Λ := Λ) (ν := (expandDiv d : Multiset I))).toAddMonoidHom tensorFlip_mul
  change Graded.IsSplitting (tensorFlip (wrapIdem Q Λ νᵈ (CycKLR.mk k Q _ _ (e _)))) _ _ _ at h2
  rw [wrapIdem_e, tensorFlip_mk_e] at h2
  exact ⟨J, inferInstance, inferInstance, _, _, h2, by rw [hc, prod_factorial_blocksDiv]⟩

omit [DecidableEq I] in
/-- The product `∏ nₐ!` is positive. -/
theorem prod_factorial_pos : 0 < (d.map fun q => q.2.factorial).prod :=
  List.prod_pos fun n hn => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hn
    exact Nat.factorial_pos _

theorem isIdempotentElem_wrapHeadIdem : IsIdempotentElem z₀ :=
  (isIdempotentElem_hflip_divIdem (Q := Q) (isBlocks_ofList d rfl)).map (CycKLR.mk k Q _ _)

/-- **Webster, arXiv:1309.3796v3, §7.1, Corollary 7.7 (top degree), for two red strands.** Let
`z₀ ∈ R^{λ₁}(ν)` be the reflected divided-power idempotent of `d`, `L` the head of the wrap
projective `wrapIdem z₀ · T` (the quotient by the images of the cut projectives) and `M` the
standard module `S(T^{λ₁} ⊠ R^{λ₂} 1_{d̄})`. If the second red strand's cyclotomic relation
holds on the last black strand, every nonzero element of `z₀ R^{λ₁}(ν)` generates `z₀` and
`z₀ R^{λ₁}(ν) z₀ = k z₀`, then `Ext^{|ν|}(M, L)` is one-dimensional. Ext of left modules, with
`L` a left module through the horizontal reflection; ungraded. Under the route hypothesis `hall`
of Proposition 7.6. -/
theorem finrank_ext_standard_cycDivProj_wrapHead (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I}
    (hRq : IsRouquierQ C Q) (hall : AllFiniteDeltaInjective Q Λ hQ)
    (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t)
    (h : 0 + wordWt (expandDiv d) 0 = νᵈ)
    [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q Λ νᵈ))]
    (hR : LastDotRelation Q Λ νᵈ) (hne : z₀ ≠ 0)
    (hgen : ∀ y : CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) νᵈ, z₀ * y = y → y ≠ 0 →
      ∃ c, y * c = z₀)
    (hscalar : ∀ x : CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) νᵈ, z₀ * x * z₀ = x →
      ∃ c : k, x = c • z₀) :
    Module.finrank k (Ext (tensorStd Q Λ hQ h (oldProj Q Λ 0 t ht) (cycDivProj Q Λ d))
      (flipLeft Q Λ νᵈ (rIdeal (wrapIdem Q Λ νᵈ z₀) ⧸ coevaluationTrace (cutIdem Q Λ νᵈ)))
      (expandDiv d).length) = 1 := by
  classical
  have hz₀ := isIdempotentElem_wrapHeadIdem Q Λ d
  set W := wrapIdem Q Λ νᵈ z₀ with hW
  have he : IsIdempotentElem W := by rw [IsIdempotentElem, hW, wrapIdem_mul, hz₀.eq]
  have hfe : IsIdempotentElem (tensorFlip W) := by
    rw [IsIdempotentElem, ← tensorFlip_mul, he.eq]
  set M := flipLeft Q Λ νᵈ (rIdeal W ⧸ coevaluationTrace (cutIdem Q Λ νᵈ))
  obtain ⟨J₁, _, _, ι, π, hιπ, htot, hc₁⟩ := exists_bicone_cycWord_cycDivProj Q Λ d
  have hB := tensorStdBiconeIsBilimit Q Λ hQ h (oldProj Q Λ 0 t ht) ι π hιπ htot
  have E₁ := Abelian.Ext.biproductLinearEquiv (R := k) hB M (expandDiv d).length
  obtain ⟨s, hs, hw, ⟨E₂⟩⟩ := exists_extLinearEquiv_standard Q Λ hQ hRq hall t ht (expandDiv d)
    h M fun p hp s hs hmem => subsingleton_hom_loadingProj_flipLeft s hs
      (wrapHead_cut Q Λ z₀ s hs (not_hasLastRed_of_mem_websterWords _ _
        (by rw [List.length_reverse]; omega) hmem))
  obtain rfl : s = wrap νᵈ (Seq.ofList (expandDiv d) rfl) := Seq.word_injective (by
    rw [hw, word_wrap, Seq.word_ofList, word_eq_of_stendhalWeight_one_zero t]
    simp [addRedColor])
  obtain ⟨J₂, _, _, a, b, hS, hc₂⟩ := exists_isSplitting_wrap Q Λ d
  have E₃ := Limits.Bicone.homLinearEquiv (R := k) (lIdealBiconeIsBilimit hS) M
  have E₄ := LinearEquiv.piCongrRight fun _ : J₂ => lIdealHomEquiv (k := k) hfe M
  have hfin := finrank_fixedSubspace_flipLeft_wrapHead Q Λ νᵈ hR z₀ hz₀ hne hgen hscalar
  have : FiniteDimensional k (fixedSubspace (k := k) M (tensorFlip W)) :=
    Module.finite_of_finrank_eq_succ hfin
  have : Nonempty J₁ := Fintype.card_pos_iff.1 (hc₁ ▸ prod_factorial_pos d)
  exact (finrank_eq_of_linearEquiv_pi (hc₁.trans hc₂.symm)
    (E₁.symm.trans (E₂.trans (E₃.trans E₄)))).trans hfin

end Coevaluation

end Categorification.Stendhal
