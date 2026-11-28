/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.UpResolutionProjDim

/-!
# Kernels and heads in `C↑`

Let `A` be a finite-dimensional graded algebra over a field `k`. This file adds two closure
properties of the class of finite-dimensional graded modules with a graded projective resolution
in `C↑`, used in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Theorem 5.28 (a simple module is the head of a standard module whose
other composition factors are lower in the standard order):

* `GFin.UpResolution.ofKernel` : for `0 → K → M → L → 0`, up-resolutions of `M` and `L` give one
  of `K`.
* `GFin.exists_upResolution_of_head` : let `ε ∈ A` and let `L` be a graded simple module that is
  an ungraded subquotient of a module `M` with an up-resolution, with `ε L ≠ 0` and `dim ε M ≤ dim ε L`. If every graded
  simple subquotient of `M` killed by `ε` has an up-resolution, so does `L`.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum Function Module

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] [Module.Finite k A]

namespace GFin

namespace UpResolution

/-- `0 → P → K ⊕ P → K → 0`. -/
def prodSwapSES (K P : GFin 𝒜) : ShortExact P (K.prod P) K where
  f := LinearMap.inr A K.carrier P.carrier
  g := LinearMap.fst A K.carrier P.carrier
  preservesGrading_f _ _ hx := ⟨zero_mem _, hx⟩
  preservesGrading_g _ _ hx := hx.1
  injective := LinearMap.inr_injective
  surjective := LinearMap.fst_surjective
  exact := Function.Exact.inr_fst

/-- **Up-resolutions of kernels**: for `0 → K → M → L → 0`, up-resolutions of `M` and `L` give
one of `K`. With `P → L` the first term of the resolution of `L`, `K ⊕ P` is an extension of `M`
by `Ω₁(L)`, and `K = (K ⊕ P)/P`. -/
def ofKernel {K M L : GFin 𝒜} (S : ShortExact K M L) {c : ℤ} (RM : UpResolution M c)
    (RL : UpResolution L c) : UpResolution K (c + 2) :=
  haveI := RL.projective 0
  let S' := kerShortExact (LinearMap.id : K.carrier →ₗ[A] K.carrier) (fun _ _ hx => hx)
    Function.surjective_id
  haveI : Subsingleton (ker (LinearMap.id : K.carrier →ₗ[A] K.carrier) fun _ _ hx => hx).carrier :=
    ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩
  let S'' := (RL.ses 0).congr (GradedEquiv.refl _) RL.iso
  let RH := horseshoe (horseSES S S' S'') (ofSubsingleton _ (c - 1)) RL.tail
  let RKP := horseshoe (horseCover S S' S'') (RH.mono (c' := c) (by omega)) RM
  let RP := ofProjective (RL.term 0) (m := -c) fun j hj => RL.vanish 0 j (by omega)
  (ofQuotient (prodSwapSES K (RL.term 0)) (RP.mono (c' := c + 1) (by omega))
    (RKP.mono (c' := c + 1) (by omega))).mono (by omega)

end UpResolution

section Head

/-- The action of `ε ∈ A` on a module, as a `k`-linear map. -/
def smulLin (ε : A) (M : Type*) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    M →ₗ[k] M where
  toFun x := ε • x
  map_add' := smul_add ε
  map_smul' c x := by
    rw [RingHom.id_apply, ← algebraMap_smul A c x, ← algebraMap_smul A c (ε • x), smul_smul,
      smul_smul, Algebra.commutes]

variable (k) in
/-- `dim_k ε N`. -/
def epsDim (ε : A) (N : GFin 𝒜) : ℕ := finrank k (LinearMap.range (smulLin (k := k) ε N.carrier))

section Types

variable {X Y : Type*} [AddCommGroup X] [Module A X] [Module k X] [IsScalarTower k A X]
  [AddCommGroup Y] [Module A Y] [Module k Y] [IsScalarTower k A Y]

/-- The restriction of an `A`-linear map to the images of `ε`. -/
def smulLinRange (ε : A) (f : X →ₗ[A] Y) :
    LinearMap.range (smulLin (k := k) ε X) →ₗ[k] LinearMap.range (smulLin (k := k) ε Y) :=
  LinearMap.codRestrict _ ((f.restrictScalars k) ∘ₗ Submodule.subtype _) fun x => by
    obtain ⟨x, y, hy⟩ := x
    refine ⟨f y, ?_⟩
    change ε • f y = f x
    rw [← map_smul, ← hy]
    rfl

omit [Module.Finite k A] in
theorem finrank_range_smulLin_le_of_injective [FiniteDimensional k Y] (ε : A) (f : X →ₗ[A] Y)
    (hf : Injective f) :
    finrank k (LinearMap.range (smulLin (k := k) ε X)) ≤
      finrank k (LinearMap.range (smulLin (k := k) ε Y)) :=
  LinearMap.finrank_le_finrank_of_injective (f := smulLinRange ε f) fun _ _ h =>
    Subtype.ext (hf (congrArg Subtype.val h))

omit [Module.Finite k A] in
theorem finrank_range_smulLin_le_of_surjective [FiniteDimensional k X] (ε : A) (g : X →ₗ[A] Y)
    (hg : Surjective g) :
    finrank k (LinearMap.range (smulLin (k := k) ε Y)) ≤
      finrank k (LinearMap.range (smulLin (k := k) ε X)) := by
  refine LinearMap.finrank_le_finrank_of_surjective (f := smulLinRange ε g) fun z => ?_
  obtain ⟨z, y, rfl⟩ := z
  obtain ⟨x, rfl⟩ := hg y
  refine ⟨⟨ε • x, x, rfl⟩, Subtype.ext ?_⟩
  change g (ε • x) = ε • g x
  rw [map_smul]

end Types

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem epsDim_le_of_injective (ε : A) {X Y : GFin 𝒜} (f : X.carrier →ₗ[A] Y.carrier)
    (hf : Injective f) : epsDim k ε X ≤ epsDim k ε Y :=
  finrank_range_smulLin_le_of_injective ε f hf

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem epsDim_le_of_surjective (ε : A) {X Y : GFin 𝒜} (g : X.carrier →ₗ[A] Y.carrier)
    (hg : Surjective g) : epsDim k ε Y ≤ epsDim k ε X :=
  finrank_range_smulLin_le_of_surjective ε g hg

variable (A) in
/-- `L` is a subquotient of `M` as an ungraded module. -/
def IsUngradedSubquotient (L M : Type*) [AddCommGroup L] [Module A L] [AddCommGroup M]
    [Module A M] : Prop :=
  ∃ (X : Submodule A M) (g : X →ₗ[A] L), Surjective g

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem IsSubquotient.isUngradedSubquotient {L M : GFin 𝒜} (h : IsSubquotient L M) :
    IsUngradedSubquotient A L.carrier M.carrier := by
  obtain ⟨X, f, g, -, hf, -, hg⟩ := h
  let e := LinearEquiv.ofInjective f hf
  exact ⟨LinearMap.range f, g ∘ₗ e.symm.toLinearMap, hg.comp e.symm.surjective⟩

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem epsDim_le_of_isUngradedSubquotient (ε : A) {L M : GFin 𝒜}
    (h : IsUngradedSubquotient A L.carrier M.carrier) : epsDim k ε L ≤ epsDim k ε M := by
  obtain ⟨X, g, hg⟩ := h
  have : FiniteDimensional k X :=
    Module.Finite.of_injective ((X.subtype).restrictScalars k) Subtype.val_injective
  exact (finrank_range_smulLin_le_of_surjective ε g hg).trans
    (finrank_range_smulLin_le_of_injective ε X.subtype Subtype.val_injective)

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem epsDim_le_of_isSubquotient (ε : A) {L M : GFin 𝒜} (h : IsSubquotient L M) :
    epsDim k ε L ≤ epsDim k ε M := by
  obtain ⟨X, f, g, -, hf, -, hg⟩ := h
  exact (epsDim_le_of_surjective ε g hg).trans (epsDim_le_of_injective ε f hf)
omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem epsDim_add_le (ε : A) {K M L : GFin 𝒜} (S : ShortExact K M L) :
    epsDim k ε K + epsDim k ε L ≤ epsDim k ε M := by
  let π : LinearMap.range (smulLin (k := k) ε M.carrier) →ₗ[k]
      LinearMap.range (smulLin (k := k) ε L.carrier) :=
    LinearMap.codRestrict _ ((S.g.restrictScalars k) ∘ₗ Submodule.subtype _) fun x => by
      obtain ⟨x, y, hy⟩ := x
      refine ⟨S.g y, ?_⟩
      change ε • S.g y = S.g x
      rw [← map_smul, ← hy]
      rfl
  have hπ : Surjective π := fun z => by
    obtain ⟨z, y, rfl⟩ := z
    obtain ⟨x, rfl⟩ := S.surjective y
    refine ⟨⟨ε • x, x, rfl⟩, Subtype.ext ?_⟩
    change S.g (ε • x) = ε • S.g x
    rw [map_smul]
  let ι : LinearMap.range (smulLin (k := k) ε K.carrier) →ₗ[k] LinearMap.ker π :=
    LinearMap.codRestrict _ (LinearMap.codRestrict _ ((S.f.restrictScalars k) ∘ₗ
      Submodule.subtype _) fun x => by
        obtain ⟨x, y, hy⟩ := x
        refine ⟨S.f y, ?_⟩
        change ε • S.f y = S.f x
        rw [← map_smul, ← hy]
        rfl) fun x => by
      refine Subtype.ext ?_
      change S.g (S.f x.1) = 0
      exact (S.exact _).2 ⟨_, rfl⟩
  have hι : Injective ι := fun x y h =>
    Subtype.ext (S.injective (congrArg (fun z => (z.1 : M.carrier)) h))
  have h1 := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.2 hπ, finrank_top] at h1
  have h2 := LinearMap.finrank_le_finrank_of_injective hι
  change finrank k _ + finrank k _ ≤ finrank k _
  omega

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem smul_eq_zero_of_epsDim_eq_zero {ε : A} {N : GFin 𝒜} (h : epsDim k ε N = 0)
    (x : N.carrier) : ε • x = 0 := by
  have := Submodule.finrank_eq_zero.1 h
  have hx : smulLin (k := k) ε N.carrier x ∈ LinearMap.range (smulLin (k := k) ε N.carrier) :=
    ⟨x, rfl⟩
  rw [this] at hx
  exact hx

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem epsDim_pos {ε : A} {N : GFin 𝒜} {x : N.carrier} (hx : ε • x ≠ 0) : 0 < epsDim k ε N :=
  Nat.pos_of_ne_zero fun h => hx (smul_eq_zero_of_epsDim_eq_zero h x)

omit [Module.Finite k A] in
/-- **Subquotients across a simple quotient.** Let `L` be a graded simple module that is an
ungraded subquotient of `M`, and `π : M → Q` a map onto a graded simple module. Then `L` is an
ungraded subquotient of `ker π`, or `L ≅ Q` as ungraded modules. -/
theorem isUngradedSubquotient_ker_or_iso {L M Q : GFin 𝒜} (hL : IsGradedSimple 𝒜 L.grading)
    (hQ : IsGradedSimple 𝒜 Q.grading) (h : IsUngradedSubquotient A L.carrier M.carrier)
    (π : M.carrier →ₗ[A] Q.carrier) :
    IsUngradedSubquotient A L.carrier (LinearMap.ker π) ∨
      Nonempty (Q.carrier ≃ₗ[A] L.carrier) := by
  have := hL.isSimpleModule
  have := hQ.isSimpleModule
  have := IsSimpleModule.nontrivial A L.carrier
  obtain ⟨X, g, hg⟩ := h
  let φ : X →ₗ[A] Q.carrier := π ∘ₗ X.subtype
  rcases IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range (g ∘ₗ (LinearMap.ker φ).subtype))
    with hb | ht
  · right
    have hle : LinearMap.ker φ ≤ LinearMap.ker g := fun x hx => by
      have : g x ∈ LinearMap.range (g ∘ₗ (LinearMap.ker φ).subtype) := ⟨⟨x, hx⟩, rfl⟩
      rw [hb] at this
      exact this
    have hφs : Surjective φ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range φ) with h0 | h0
      · exfalso
        obtain ⟨y, hy⟩ := exists_ne (0 : L.carrier)
        obtain ⟨x, rfl⟩ := hg y
        exact hy (hle (LinearMap.range_eq_bot.1 h0 ▸ rfl))
      · exact LinearMap.range_eq_top.1 h0
    let e := φ.quotKerEquivOfSurjective hφs
    let hmap : Q.carrier →ₗ[A] L.carrier := (LinearMap.ker φ).liftQ g hle ∘ₗ e.symm.toLinearMap
    have hcomp : ∀ x, hmap (φ x) = g x := fun x => by
      change (LinearMap.ker φ).liftQ g hle (e.symm (φ x)) = g x
      rw [show e.symm (φ x) = Submodule.Quotient.mk x from e.symm_apply_eq.2 rfl]
      rfl
    have hm0 : hmap ≠ 0 := fun h0 => by
      obtain ⟨y, hy⟩ := exists_ne (0 : L.carrier)
      obtain ⟨x, rfl⟩ := hg y
      exact hy (by rw [← hcomp, h0, LinearMap.zero_apply])
    exact ⟨LinearEquiv.ofBijective hmap (LinearMap.bijective_of_ne_zero hm0)⟩
  · left
    let X' : Submodule A (LinearMap.ker π) := X.comap (LinearMap.ker π).subtype
    let ι : X' →ₗ[A] X :=
      LinearMap.codRestrict X ((LinearMap.ker π).subtype ∘ₗ X'.subtype) fun y => y.2
    refine ⟨X', g ∘ₗ ι, fun l => ?_⟩
    obtain ⟨x, rfl⟩ : l ∈ LinearMap.range (g ∘ₗ (LinearMap.ker φ).subtype) := ht ▸ trivial
    exact ⟨⟨⟨x.1.1, x.2⟩, x.1.2⟩, rfl⟩

omit [Module.Finite k A] in
/-- **Heads in `C↑`.** Let `ε ∈ A` and let `L` be a graded simple module that is an ungraded
subquotient of a module `M` with an up-resolution, with `ε L ≠ 0` and `dim ε M ≤ dim ε L`. If
every graded simple subquotient of `M` killed by `ε` has an up-resolution, so does `L`. -/
theorem exists_upResolution_of_head (ε : A) (L : GFin 𝒜) (hL : IsGradedSimple 𝒜 L.grading)
    (hεL : ∃ x : L.carrier, ε • x ≠ 0) :
    ∀ M : GFin 𝒜, IsUngradedSubquotient A L.carrier M.carrier → epsDim k ε M ≤ epsDim k ε L →
      (∃ c, Nonempty (UpResolution M c)) →
      (∀ L' : GFin 𝒜, IsGradedSimple 𝒜 L'.grading → IsSubquotient L' M →
        (∀ x : L'.carrier, ε • x = 0) → ∃ c, Nonempty (UpResolution L' c)) →
      ∃ c, Nonempty (UpResolution L c) := by
  obtain ⟨x₀, hx₀⟩ := hεL
  have hLpos : 0 < epsDim k ε L := epsDim_pos hx₀
  intro M
  induction hN : finrank k M.carrier using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    intro hsub hdim hM hzero
    have hnt : Nontrivial M.carrier := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      obtain ⟨X, g, hg⟩ := hsub
      obtain ⟨x, rfl⟩ := hg x₀
      have hx : x = 0 := Subtype.ext (Subsingleton.elim _ _)
      exact hx₀ (by rw [hx, map_zero, smul_zero])
    have : Module.Finite A M.carrier := Module.Finite.of_restrictScalars_finite k A _
    obtain ⟨p, hp, hptop, hmax⟩ := exists_isHomogeneous_maximal (A := A) M.grading
    let := quotDecompositionA M.grading p hp
    let Lfin : GFin 𝒜 :=
      { carrier := M.carrier ⧸ p
        grading := quotGradingA M.grading p
        finiteDimensional := Module.Finite.of_surjective (p.mkQ.restrictScalars k)
          p.mkQ_surjective }
    have hmk : PreservesGrading M.grading Lfin.grading p.mkQ :=
      preservesGrading_mkQ M.grading p
    have hker : LinearMap.ker p.mkQ = p := Submodule.ker_mkQ p
    let K := ker (M := M) (N := Lfin) p.mkQ hmk
    let S := kerShortExact (M := M) (N := Lfin) p.mkQ hmk p.mkQ_surjective
    have hKlt : finrank k K.carrier < n := by
      rw [← hN]
      have hlt : (LinearMap.ker p.mkQ).restrictScalars k < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro h'
        refine hptop ?_
        rw [eq_top_iff, ← hker]
        intro x _
        have : x ∈ (LinearMap.ker p.mkQ).restrictScalars k := h' ▸ Submodule.mem_top
        exact this
      exact Submodule.finrank_lt hlt.ne
    have hLs : IsGradedSimple 𝒜 Lfin.grading := isGradedSimple_quot 𝒜 M.grading p hp hptop hmax
    have hsubK : ∀ L' : GFin 𝒜, IsSubquotient L' K → IsSubquotient L' M := fun L' h =>
      h.trans_injective (f := (LinearMap.ker p.mkQ).subtype) (fun _ _ hx => hx)
        Subtype.val_injective
    have hadd : epsDim k ε K + epsDim k ε Lfin ≤ epsDim k ε M := epsDim_add_le ε S
    obtain ⟨cM, ⟨RM⟩⟩ := hM
    -- In the second case `L ≅ M/p` up to a shift, resolved from a resolution of `M/p`.
    have hiso : ∀ (e : Lfin.carrier ≃ₗ[A] L.carrier) (cQ : ℤ), UpResolution Lfin cQ →
        ∃ c, Nonempty (UpResolution L c) := fun e cQ RQ => by
      have he : (e.symm.toLinearMap : L.carrier →ₗ[A] Lfin.carrier) ≠ 0 := fun h0 => by
        have := hL.nontrivial
        obtain ⟨y, hy⟩ := exists_ne (0 : L.carrier)
        exact hy (e.symm.injective (by rw [map_zero]; exact LinearMap.congr_fun h0 y))
      obtain ⟨a, ⟨ea⟩⟩ := hL.exists_gradedEquiv_shift_of_ne_zero hLs he
      exact ⟨_, ⟨(RQ.shift a).congr ea.symm⟩⟩
    by_cases hQ0 : epsDim k ε Lfin = 0
    · -- `ε` kills the simple quotient: pass to the kernel.
      obtain ⟨cQ, ⟨RQ⟩⟩ := hzero Lfin hLs (IsSubquotient.of_surjective hmk p.mkQ_surjective)
        (smul_eq_zero_of_epsDim_eq_zero hQ0)
      have RK := UpResolution.ofKernel S (RM.mono (le_max_left cM cQ))
        (RQ.mono (le_max_right cM cQ))
      rcases isUngradedSubquotient_ker_or_iso hL hLs hsub p.mkQ with hK | he
      · exact ih _ hKlt K rfl hK (by omega) ⟨_, ⟨RK⟩⟩ fun L' h₁ h₂ h₃ => hzero L' h₁ (hsubK L' h₂) h₃
      · exfalso
        obtain ⟨e⟩ := he
        have := epsDim_le_of_surjective (k := k) (X := Lfin) (Y := L) ε e.toLinearMap e.surjective
        omega
    · rcases isUngradedSubquotient_ker_or_iso hL hLs hsub p.mkQ with hK | he
      · exfalso
        have := epsDim_le_of_isUngradedSubquotient (k := k) (L := L) (M := K) ε hK
        omega
      · -- `L ≅ M/p`, and `ε` kills the kernel.
        obtain ⟨e⟩ := he
        have hLQ := epsDim_le_of_surjective (k := k) (X := Lfin) (Y := L) ε e.toLinearMap
          e.surjective
        have hK0 : epsDim k ε K = 0 := by omega
        obtain ⟨cK, ⟨RK⟩⟩ := exists_upResolution_of_isSubquotient K fun L' h₁ h₂ =>
          hzero L' h₁ (hsubK L' h₂) (smul_eq_zero_of_epsDim_eq_zero
            (Nat.eq_zero_of_le_zero ((epsDim_le_of_isSubquotient ε h₂).trans hK0.le)))
        exact hiso e _ (UpResolution.ofQuotient S (RK.mono (le_max_left cK cM))
          (RM.mono (le_max_right cK cM)))

end Head

end GFin

end Categorification.Graded
