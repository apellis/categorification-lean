/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.KrullSchmidt
import Categorification.Algebra.Graded.G0

/-!
# `G₀` is free on the simple modules, and the pairing `K₀ × G₀ → ℤ((q))`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.5, TeX lines 1513–1556: "`G₀(R(ν))` is a free
`ℤ[q, q⁻¹]`-module with the basis `{[S_b]}`", and the bilinear pairing
`K₀(R(ν)) × G₀(R(ν)) → ℤ[q, q⁻¹]`, `([P], [M]) = gdim HOM(P, M)`, satisfies
`([P_b], [S_{b'}]) = δ_{b b'}` when `End(S_b) = k` (in general the diagonal entries are
`dim_k End(S_b)`).

Let `A` be a `ℤ`-graded algebra over a field `k` with a graded dimension, and assume that every
graded simple module is finite-dimensional (hypothesis `hfd` below: the chosen tops
`S_b = IndecClass.top b` are finite-dimensional; for `R(ν)` this is KL I, Proposition 2.12).

## Main results

* `G0.finrank_homGrade_eq_add_of_shortExact` : `HOM(P, -)` is exact on short exact sequences of
  finite-dimensional graded modules, for `P` in `A-pmod` (graded projectivity).
* `G0.topBasis hfd : Basis (IndecClass 𝒜) ℤ[q, q⁻¹] (G₀(A))`, `topBasis b = [S_b]`, and
  `G0.free`: **`G₀(A)` is free with basis the classes of the graded simples up to shift.**
* `GProj.IndecClass.finrank_homGrade_rep_top` : `dim HOM(P_b, S_{b'})_d = δ_{b b'} δ_{d 0}
  dim_k END(S_b)_0`.
* `pairing : K₀(A) →+ G₀(A) →+ ℤ((q))`, `([P], [M]) = gdim HOM(P, M)` (`pairing_of_of`), and
  `pairing_indecBasis_topBasis` : **dual bases up to `End(S_b)`**:
  `([P_b], [S_{b'}]) = δ_{b b'} dim_k END(S_b)_0`; exactly dual when `END(S_b)_0 = k`
  (`pairing_indecBasis_topBasis_of_finrank_eq_one`).
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum Module Function

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

/-! ### Generalities on `G₀` -/

namespace G0

/-- Induction principle: a property of `G₀` holding on classes and closed under `0`, `+`, `-`
holds everywhere. -/
@[elab_as_elim]
theorem induction_on {motive : G0 𝒜 → Prop} (x : G0 𝒜) (of : ∀ M, motive (of M))
    (zero : motive 0) (add : ∀ x y, motive x → motive y → motive (x + y))
    (neg : ∀ x, motive x → motive (-x)) : motive x := by
  obtain ⟨y, rfl⟩ := mk_surjective x
  induction y using FreeAbelianGroup.induction_on with
  | C0 => simpa using zero
  | C1 c =>
    obtain ⟨M, rfl⟩ := GFin.isoClass_surjective c
    exact of M
  | Cn c h => simpa using neg _ h
  | Cp y z hy hz => simpa using add _ _ hy hz

/-- The class of a zero module vanishes. -/
theorem of_eq_zero_of_subsingleton (M : GFin 𝒜) [Subsingleton M.carrier] : of M = 0 := by
  have e : M.Iso (M.prod M) :=
    GradedEquiv.ofLinearMaps (M := M.carrier) (N := M.carrier × M.carrier)
      (LinearMap.prod LinearMap.id LinearMap.id) (LinearMap.fst A M.carrier M.carrier)
      (fun _ => rfl) (fun _ => Subsingleton.elim _ _) (fun _ _ hx => ⟨hx, hx⟩)
      (fun _ _ hx => hx.1)
  have h := of_eq_of_iso e
  rw [of_prod] at h
  simpa using h

omit [Algebra k A] in
/-- An injective degree-preserving map reflects degrees. -/
theorem mem_of_map_mem {M N : Type*} [AddCommGroup M] [Module A M] [Module k M]
    [AddCommGroup N] [Module A N] [Module k N] {ℳ : ℤ → Submodule k M} [Decomposition ℳ]
    {𝒩 : ℤ → Submodule k N} [Decomposition 𝒩] {f : M →ₗ[A] N} (hf : PreservesGrading ℳ 𝒩 f)
    (hinj : Injective f) {x : M} {d : ℤ} (hx : f x ∈ 𝒩 d) : x ∈ ℳ d := by
  have : x = decompose ℳ x d := hinj (by rw [← decompose_map hf, decompose_of_mem_same _ hx])
  rw [this]
  exact (decompose ℳ x d).2

variable [GradedAlgebra 𝒜]

/-- **`HOM(P, -)` is exact** for `P` in `A-pmod`: for a short exact sequence
`0 → M → N → M'' → 0` of finite-dimensional graded modules,
`dim HOM(P, N)_d = dim HOM(P, M)_d + dim HOM(P, M'')_d`. -/
theorem finrank_homGrade_eq_add_of_shortExact (P : GProj 𝒜) {M N M'' : GFin 𝒜}
    (S : GFin.ShortExact M N M'') (d : ℤ) :
    finrank k (homGrade A P.grading N.grading d) =
      finrank k (homGrade A P.grading M.grading d) +
        finrank k (homGrade A P.grading M''.grading d) := by
  haveI := HasGdim.of_finiteDimensional N.grading
  haveI := hasGdim_homGrade (A := A) P.grading N.grading
  -- composition with `f` and `g`
  let α : homGrade A P.grading M.grading d →ₗ[k] homGrade A P.grading N.grading d :=
    { toFun := fun φ => ⟨S.f ∘ₗ (φ : P.carrier →ₗ[A] M.carrier),
        fun _ _ hx => S.preservesGrading_f (φ.2 hx)⟩
      map_add' := fun φ ψ => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c φ => Subtype.ext (LinearMap.ext fun x =>
        LinearMap.map_smul_of_tower S.f c _) }
  let β : homGrade A P.grading N.grading d →ₗ[k] homGrade A P.grading M''.grading d :=
    { toFun := fun φ => ⟨S.g ∘ₗ (φ : P.carrier →ₗ[A] N.carrier),
        fun _ _ hx => S.preservesGrading_g (φ.2 hx)⟩
      map_add' := fun φ ψ => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c φ => Subtype.ext (LinearMap.ext fun x =>
        LinearMap.map_smul_of_tower S.g c _) }
  refine finrank_eq_add_of_exact (f := α) (g := β) ?_ ?_ ?_
  · intro φ ψ h
    refine Subtype.ext (LinearMap.ext fun x => S.injective ?_)
    exact LinearMap.congr_fun (congrArg Subtype.val h) x
  · -- lifting along `g`, in the shifted grading
    intro ψ
    have hψ : PreservesGrading P.grading (Graded.shift M''.grading (-d))
        (ψ : P.carrier →ₗ[A] M''.carrier) := fun e _ hx => by
      show _ ∈ M''.grading (e - -d)
      rw [sub_neg_eq_add]
      exact ψ.2 hx
    have hg : PreservesGrading (Graded.shift N.grading (-d)) (Graded.shift M''.grading (-d))
        S.g := fun _ _ hx => S.preservesGrading_g hx
    obtain ⟨φ, hφ, hφg⟩ := exists_lift_of_projective 𝒜 hg S.surjective hψ
    refine ⟨⟨φ, fun e _ hx => ?_⟩, Subtype.ext hφg⟩
    have := hφ hx
    rwa [mem_shift, sub_neg_eq_add] at this
  · intro φ
    constructor
    · intro h
      have hrange : ∀ x, (φ : P.carrier →ₗ[A] N.carrier) x ∈ LinearMap.range S.f := fun x =>
        (S.exact _).1 (LinearMap.congr_fun (congrArg Subtype.val h) x)
      let ψ : P.carrier →ₗ[A] M.carrier :=
        (LinearEquiv.ofInjective S.f S.injective).symm.toLinearMap ∘ₗ
          (φ : P.carrier →ₗ[A] N.carrier).codRestrict (LinearMap.range S.f) hrange
      have hfψ : ∀ x, S.f (ψ x) = (φ : P.carrier →ₗ[A] N.carrier) x := fun x => by
        have := (LinearEquiv.ofInjective S.f S.injective).apply_symm_apply
          ⟨(φ : P.carrier →ₗ[A] N.carrier) x, hrange x⟩
        exact congrArg Subtype.val this
      refine ⟨⟨ψ, fun e x hx => ?_⟩, Subtype.ext (LinearMap.ext hfψ)⟩
      exact mem_of_map_mem S.preservesGrading_f S.injective (by rw [hfψ]; exact φ.2 hx)
    · rintro ⟨ψ, rfl⟩
      refine Subtype.ext (LinearMap.ext fun x => ?_)
      exact S.exact.apply_apply_eq_zero _

omit [GradedAlgebra 𝒜] in
theorem homRankG_hiso (P : GProj 𝒜) {M N : GFin 𝒜} (e : M.Iso N) :
    (finrank k (homGrade A P.grading M.grading 0) : ℤ) =
      finrank k (homGrade A P.grading N.grading 0) :=
  congrArg _ (finrank_homGrade_congr_right e 0)

theorem homRankG_hses (P : GProj 𝒜) {M N M'' : GFin 𝒜} (S : GFin.ShortExact M N M'') :
    (finrank k (homGrade A P.grading N.grading 0) : ℤ) =
      finrank k (homGrade A P.grading M.grading 0) +
        finrank k (homGrade A P.grading M''.grading 0) := by
  rw [finrank_homGrade_eq_add_of_shortExact P S 0]
  push_cast
  rfl

/-- For `P` in `A-pmod`, the additive map `[M] ↦ dim_k Hom(P, M)_0` on `G₀(A)`. -/
def homRankG (P : GProj 𝒜) : G0 𝒜 →+ ℤ :=
  lift (fun M => (finrank k (homGrade A P.grading M.grading 0) : ℤ)) (homRankG_hiso P)
    (homRankG_hses P)

theorem homRankG_of (P : GProj 𝒜) (M : GFin 𝒜) :
    homRankG P (of M) = finrank k (homGrade A P.grading M.grading 0) :=
  lift_of _ (homRankG_hiso P) (homRankG_hses P) M

/-- `dim Hom(P, M)_0 ≠ 0` iff there is a nonzero degree-preserving map `P → M`. -/
theorem homRankG_of_ne_zero_iff (P : GProj 𝒜) (M : GFin 𝒜) :
    homRankG P (of M) ≠ 0 ↔
      ∃ f : P.carrier →ₗ[A] M.carrier, PreservesGrading P.grading M.grading f ∧ f ≠ 0 := by
  haveI := HasGdim.of_finiteDimensional M.grading
  haveI := hasGdim_homGrade (A := A) P.grading M.grading
  rw [homRankG_of, Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero,
    Module.finrank_pos_iff_exists_ne_zero]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, preservesGrading_of_mem_homGrade_zero f.2, fun h => hf (Subtype.ext h)⟩
  · rintro ⟨f, hf, hf0⟩
    exact ⟨⟨f, mem_homGrade_zero_of_preservesGrading hf⟩, fun h => hf0 (congrArg Subtype.val h)⟩

omit [GradedAlgebra 𝒜] in
/-- Expansion of the `ℤ[q, q⁻¹]`-action on `G₀`. -/
theorem map_C_mul_T_smul {G : Type*} [AddCommGroup G] (ψ : G0 𝒜 →+ G) (n : ℤ) (a : ℤ)
    (x : G0 𝒜) :
    ψ ((LaurentPolynomial.C n * LaurentPolynomial.T a : LaurentPolynomial ℤ) • x) =
      n • ψ ((LaurentPolynomial.T a : LaurentPolynomial ℤ) • x) := by
  rw [← LaurentPolynomial.smul_eq_C_mul, smul_assoc, map_zsmul]

end G0

/-! ### The simple modules `S_b` as objects of `A-fmod` -/

namespace GProj.IndecClass

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

/-- The top `S_b` as a finite-dimensional graded module (given that it is finite-dimensional). -/
def topFin (hfd : ∀ b : IndecClass 𝒜, FiniteDimensional k b.top) (b : IndecClass 𝒜) :
    GFin 𝒜 :=
  { toGMod := b.top
    finiteDimensional := hfd b }

open scoped Classical in
/-- `HOM(P_b, S_{b'})` is concentrated in degree `0` and vanishes unless `b = b'`; its degree-zero
part for `b = b'` is `END(S_b)_0`. -/
theorem finrank_homGrade_rep_top (b b' : IndecClass 𝒜) (d : ℤ) :
    finrank k (homGrade A b.rep.grading b'.top.grading d) =
      if b = b' ∧ d = 0 then finrank k (endZero A b.top.grading) else 0 := by
  haveI := Graded.hasGdim_homGrade (A := A) b.rep.grading b'.top.grading
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    -- `END(S_b)_0 ≅ HOM(P_b, S_b)_0`, `φ ↦ φ ∘ π_b`
    let Φ : endZero A b.top.grading →ₗ[k] homGrade A b.rep.grading b.top.grading 0 :=
      { toFun := fun φ => ⟨(φ : Module.End A b.top) ∘ₗ b.topMap,
          mem_homGrade_zero_of_preservesGrading (φ.2.comp (preservesGrading_topMap b))⟩
        map_add' := fun φ ψ => Subtype.ext (LinearMap.add_comp _ _ _)
        map_smul' := fun c φ => rfl }
    have hsurj := surjective_of_isGradedSimple (isGradedSimple_top b)
      (preservesGrading_topMap b) (topMap_ne_zero b)
    refine (LinearEquiv.ofBijective Φ ⟨fun φ ψ h => Subtype.ext (LinearMap.ext fun y => ?_),
      fun g => ?_⟩).finrank_eq.symm
    · obtain ⟨x, rfl⟩ := hsurj y
      exact LinearMap.congr_fun (congrArg Subtype.val h) x
    · by_cases hg0 : (g : b.rep.carrier →ₗ[A] b.top) = 0
      · exact ⟨0, Subtype.ext (by rw [hg0]; exact LinearMap.zero_comp _)⟩
      have hgp := preservesGrading_of_mem_homGrade_zero g.2
      have hle := (isIndec_rep b).ker_le_ker (isGradedSimple_top b)
        (preservesGrading_topMap b) (topMap_ne_zero b) hgp hg0
      set φ : b.top →ₗ[A] b.top := ((LinearMap.ker b.topMap).liftQ g hle).comp
        (b.topMap.quotKerEquivOfSurjective hsurj).symm.toLinearMap
      have hφ : ∀ x, φ (b.topMap x) = (g : b.rep.carrier →ₗ[A] b.top) x := fun x => by
        have : (b.topMap.quotKerEquivOfSurjective hsurj).symm (b.topMap x) =
            Submodule.Quotient.mk x := by
          rw [LinearEquiv.symm_apply_eq]
          rfl
        simp only [φ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
          Submodule.liftQ_apply]
      have hφg : PreservesGrading b.top.grading b.top.grading φ := by
        intro e y hy
        obtain ⟨x, rfl⟩ := hsurj y
        rw [← decompose_of_mem_same b.top.grading hy, decompose_map (preservesGrading_topMap b),
          hφ]
        exact hgp (decompose b.rep.grading x e).2
      exact ⟨⟨φ, hφg⟩, Subtype.ext (LinearMap.ext hφ)⟩
  · by_contra hne
    obtain ⟨g₀, hg₀⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (Nat.pos_of_ne_zero hne)
    apply h
    -- `g₀` is a nonzero degree-preserving map `P_b → S_{b'}{-d}`
    have hg : PreservesGrading b.rep.grading (Graded.shift b'.top.grading (-d))
        (g₀ : b.rep.carrier →ₗ[A] b'.top) := fun e _ hx => by
      show _ ∈ b'.top.grading (e - -d)
      rw [sub_neg_eq_add]
      exact g₀.2 hx
    have hg0 : (g₀ : b.rep.carrier →ₗ[A] b'.top) ≠ 0 := fun h' => hg₀ (Subtype.ext h')
    obtain ⟨e⟩ := (isIndec_rep b).nonempty_iso ((isIndec_rep b').shift (-d))
      ((isGradedSimple_top b').shift (-d)) hg hg0 (f' := b'.topMap)
      (fun _ _ hx => (preservesGrading_topMap b') hx) (topMap_ne_zero b')
    obtain rfl := eq_of_iso_rep e
    haveI := (isIndec_rep b).nontrivial
    have := eq_zero_of_gradedEquiv_shift_of_hasGdim (A := A) b.rep.grading e
    exact ⟨rfl, by omega⟩

end GProj.IndecClass

/-! ### `G₀` is free on the simples -/

namespace G0

open GProj GProj.IndecClass

variable [GradedAlgebra 𝒜] [HasGdim 𝒜] (hfd : ∀ b : IndecClass 𝒜, FiniteDimensional k b.top)

include hfd in
/-- The classes `[S_b]` span `G₀(A)` over `ℤ[q, q⁻¹]` (induction on the dimension, splitting off
a graded simple quotient). -/
theorem span_top :
    Submodule.span (LaurentPolynomial ℤ) (Set.range fun b => of (topFin hfd b)) = ⊤ := by
  set V := Submodule.span (LaurentPolynomial ℤ) (Set.range fun b => of (topFin hfd b))
  have key : ∀ M : GFin 𝒜, of M ∈ V := by
    intro M
    induction h : finrank k M.carrier using Nat.strong_induction_on generalizing M with
    | _ n ih =>
      by_cases hM : Nontrivial M.carrier
      · haveI : Module.Finite A M.carrier := Module.Finite.of_restrictScalars_finite k A _
        obtain ⟨N, hN, hNtop, hmax⟩ := exists_isHomogeneous_maximal (A := A) M.grading
        letI := quotDecompositionA M.grading N hN
        let Nfin : GFin 𝒜 :=
          { carrier := N
            grading := Graded.submodule M.grading N
            decomposition := submoduleDecomposition M.grading hN
            finiteDimensional := FiniteDimensional.of_injective (N.subtype.restrictScalars k)
              Subtype.val_injective }
        let Qfin : GFin 𝒜 :=
          { carrier := M.carrier ⧸ N
            grading := quotGradingA M.grading N
            finiteDimensional := Module.Finite.of_surjective (N.mkQ.restrictScalars k)
              N.mkQ_surjective }
        let S : GFin.ShortExact Nfin M Qfin :=
          { f := N.subtype
            g := N.mkQ
            preservesGrading_f := fun _ _ hx => hx
            preservesGrading_g := preservesGrading_mkQ M.grading N
            injective := Subtype.val_injective
            surjective := N.mkQ_surjective
            exact := LinearMap.exact_subtype_mkQ N }
        rw [of_eq_add_of_shortExact S]
        refine add_mem (ih _ ?_ Nfin rfl) ?_
        · rw [← h]
          have hlt : N.restrictScalars k < ⊤ := by
            rw [lt_top_iff_ne_top]
            intro h'
            exact hNtop (by
              rw [eq_top_iff]
              intro x _
              have : x ∈ N.restrictScalars k := h' ▸ Submodule.mem_top
              exact this)
          exact Submodule.finrank_lt hlt.ne
        · have hQ : IsGradedSimple 𝒜 Qfin.grading := isGradedSimple_quot 𝒜 M.grading N hN hNtop hmax
          obtain ⟨b, a, ⟨e⟩⟩ := exists_gradedEquiv_top_shift hQ
          have : of Qfin = (LaurentPolynomial.T a : LaurentPolynomial ℤ) • of (topFin hfd b) := by
            rw [T_smul_of]
            exact of_eq_of_iso e
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
      · rw [not_nontrivial_iff_subsingleton] at hM
        rw [of_eq_zero_of_subsingleton]
        exact zero_mem _
  refine Submodule.eq_top_iff'.2 fun x => ?_
  induction x using G0.induction_on with
  | of M => exact key M
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | neg x hx => exact neg_mem hx

open scoped Classical in
/-- The key computation for linear independence: for `ψ = homRankG (P_{b₀}{d})`,
`ψ(p • [S_b]) = δ_{b b₀} p_d ψ([S_{b₀}{d}])`. -/
theorem homRankG_smul_of_top (b₀ : IndecClass 𝒜) (d : ℤ) (b : IndecClass 𝒜)
    (p : LaurentPolynomial ℤ) :
    homRankG (b₀.rep.shift d) (p • of (topFin hfd b)) =
      if b = b₀ then p d * homRankG (b₀.rep.shift d) (of ((topFin hfd b₀).shift d)) else 0 := by
  have hvanish : ∀ a : ℤ, homRankG (b₀.rep.shift d) (of ((topFin hfd b).shift a)) ≠ 0 →
      b = b₀ ∧ a = d := by
    intro a ha
    obtain ⟨g, hg, hg0⟩ := (homRankG_of_ne_zero_iff _ _).1 ha
    have hS : IsGradedSimple 𝒜 (Graded.shift b.top.grading a) := (isGradedSimple_top b).shift a
    have := eq_of_cover hS (f := g) hg hg0 (b' := b) (a' := a) (f' := b.topMap)
      (fun j _ hx => (preservesGrading_topMap b) (d := j - a) hx) (topMap_ne_zero b)
    exact ⟨this.1.symm, this.2.symm⟩
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [add_smul, map_add, hp, hq]
    split_ifs
    · rw [← add_mul]
      rfl
    · rw [add_zero]
  | C_mul_T a n =>
    rw [map_C_mul_T_smul, T_smul_of, ← LaurentPolynomial.single_eq_C_mul_T,
      Finsupp.single_apply]
    by_cases hb : b = b₀
    · subst hb
      by_cases ha : a = d
      · subst ha
        simp
      · have : homRankG (b.rep.shift d) (of ((topFin hfd b).shift a)) = 0 := by
          by_contra h
          exact ha (hvanish a h).2
        simp [this, ha]
    · have : homRankG (b₀.rep.shift d) (of ((topFin hfd b).shift a)) = 0 := by
        by_contra h
        exact hb (hvanish a h).1
      simp [this, hb]

include hfd in
/-- The classes `[S_b]` are linearly independent over `ℤ[q, q⁻¹]`. -/
theorem linearIndependent_top :
    LinearIndependent (LaurentPolynomial ℤ) fun b => of (topFin hfd b) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  ext b₀ d
  have hc₀ : homRankG (b₀.rep.shift d) (of ((topFin hfd b₀).shift d)) ≠ 0 :=
    (homRankG_of_ne_zero_iff _ _).2 ⟨b₀.topMap,
      fun j _ hx => (preservesGrading_topMap b₀) (d := j - d) hx, topMap_ne_zero b₀⟩
  have h := congrArg (homRankG (b₀.rep.shift d)) hl
  rw [Finsupp.linearCombination_apply, map_finsuppSum, map_zero] at h
  simp only [homRankG_smul_of_top hfd b₀ d] at h
  rw [Finsupp.sum, Finset.sum_ite_eq'] at h
  split_ifs at h with hmem
  · simpa [hc₀] using h
  · simp [Finsupp.not_mem_support_iff.1 hmem]

/-- **KL I, §2.5: `G₀(A)` is a free `ℤ[q, q⁻¹]`-module with basis the classes `[S_b]` of the
graded simple modules up to shift** (assuming the graded simples are finite-dimensional). -/
def topBasis : Basis (IndecClass 𝒜) (LaurentPolynomial ℤ) (G0 𝒜) :=
  Basis.mk (linearIndependent_top hfd) (span_top hfd).ge

@[simp] theorem topBasis_apply (b : IndecClass 𝒜) : topBasis hfd b = of (topFin hfd b) :=
  Basis.mk_apply _ _ _

include hfd in
/-- **`G₀(A)` is a free `ℤ[q, q⁻¹]`-module.** -/
theorem free : Module.Free (LaurentPolynomial ℤ) (G0 𝒜) :=
  Module.Free.of_basis (topBasis hfd)

end G0

/-! ### The pairing `K₀ × G₀ → ℤ((q))` -/

section Pairing

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

open GProj

/-- `gdim HOM(P, M)` for `P` in `A-pmod` and `M` in `A-fmod`. -/
def pairingGdim (P : GProj 𝒜) (M : GFin 𝒜) : LaurentSeries ℤ :=
  gdim (homGrade A P.grading M.grading)

instance (P : GProj 𝒜) (M : GFin 𝒜) : HasGdim (homGrade A P.grading M.grading) :=
  haveI := HasGdim.of_finiteDimensional M.grading
  hasGdim_homGrade P.grading M.grading

/-- For fixed `M`, the additive map `[P] ↦ gdim HOM(P, M)` on `K₀`. -/
def pairingRight (M : GFin 𝒜) : K0 𝒜 →+ LaurentSeries ℤ :=
  QuotientAddGroup.lift (K0.relSubgroup 𝒜)
    (FreeAbelianGroup.lift fun c : GProj.IsoClass 𝒜 =>
      Quotient.lift (fun P => pairingGdim P M)
        (fun P P' (h : Nonempty (P.Iso P')) =>
          gdim_eq_of_finrank_eq fun d => (finrank_homGrade_congr_left h.some d).symm) c)
    (by
      rw [K0.relSubgroup, AddSubgroup.closure_le]
      rintro _ ⟨P, P', rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift.of]
      show pairingGdim (P.prod P') M - pairingGdim P M - pairingGdim P' M = 0
      have : pairingGdim (P.prod P') M = pairingGdim P M + pairingGdim P' M := by
        haveI : HasGdim (homGrade A (P.prod P').grading M.grading) := inferInstance
        exact gdim_eq_add_of_finrank_eq fun d => finrank_homGrade_prod_left d
      rw [this]
      abel)

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem pairingRight_of (P : GProj 𝒜) (M : GFin 𝒜) :
    pairingRight M (K0.of P) = pairingGdim P M := by
  show QuotientAddGroup.lift _ _ _ (QuotientAddGroup.mk' _ _) = _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk, FreeAbelianGroup.lift.of]
  rfl

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem pairingRight_hiso {M N : GFin 𝒜} (e : M.Iso N) : pairingRight M = pairingRight N :=
  K0.hom_ext fun P => by
    rw [pairingRight_of, pairingRight_of]
    exact gdim_eq_of_finrank_eq fun d => finrank_homGrade_congr_right e d

omit [HasGdim 𝒜] in
theorem pairingRight_hses {M N M'' : GFin 𝒜} (S : GFin.ShortExact M N M'') :
    pairingRight N = pairingRight M + pairingRight M'' :=
  K0.hom_ext fun P => by
    rw [AddMonoidHom.add_apply, pairingRight_of, pairingRight_of, pairingRight_of]
    exact gdim_eq_add_of_finrank_eq fun d => G0.finrank_homGrade_eq_add_of_shortExact P S d

/-- **The pairing** `K₀(A) × G₀(A) → ℤ((q))`, `([P], [M]) = gdim HOM(P, M)` (KL I, §2.5). -/
def pairing : K0 𝒜 →+ G0 𝒜 →+ LaurentSeries ℤ :=
  (G0.lift (fun M => pairingRight M) pairingRight_hiso pairingRight_hses).flip

omit [HasGdim 𝒜] in
@[simp] theorem pairing_of_of (P : GProj 𝒜) (M : GFin 𝒜) :
    pairing (K0.of P) (G0.of M) = gdim (homGrade A P.grading M.grading) := by
  rw [pairing, AddMonoidHom.flip_apply,
    G0.lift_of (fun M => pairingRight M) pairingRight_hiso pairingRight_hses M, pairingRight_of]
  rfl

variable (hfd : ∀ b : IndecClass 𝒜, FiniteDimensional k b.top)

open scoped Classical in
/-- **KL I, §2.5: the bases `[P_b]` of `K₀` and `[S_b]` of `G₀` are dual up to `End(S_b)`**:
`([P_b], [S_{b'}]) = δ_{b b'} dim_k END(S_b)_0`. -/
theorem pairing_indecBasis_topBasis (b b' : IndecClass 𝒜) :
    pairing (K0.indecBasis 𝒜 b) (G0.topBasis hfd b') =
      if b = b' then HahnSeries.single 0 (finrank k (endZero A b.top.grading) : ℤ) else 0 := by
  rw [K0.indecBasis_apply, G0.topBasis_apply, pairing_of_of]
  ext d
  rw [coeff_gdim]
  change (finrank k (homGrade A b.rep.grading b'.top.grading d) : ℤ) = _
  rw [IndecClass.finrank_homGrade_rep_top]
  by_cases hb : b = b'
  · by_cases hd : d = 0
    · subst hd
      simp [hb]
    · simp [hb, hd, HahnSeries.coeff_single_of_ne hd]
  · simp [hb]

open scoped Classical in
/-- **Exactly dual bases** when every `END(S_b)_0` is `k` (one-dimensional):
`([P_b], [S_{b'}]) = δ_{b b'}`. -/
theorem pairing_indecBasis_topBasis_of_finrank_eq_one
    (hk : ∀ b : IndecClass 𝒜, finrank k (endZero A b.top.grading) = 1) (b b' : IndecClass 𝒜) :
    pairing (K0.indecBasis 𝒜 b) (G0.topBasis hfd b') = if b = b' then 1 else 0 := by
  classical
  rw [pairing_indecBasis_topBasis, hk]
  split_ifs <;> rfl

end Pairing

end Categorification.Graded
