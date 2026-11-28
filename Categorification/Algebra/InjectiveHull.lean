/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerFaithfulEmbedding
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Injective hulls

An *injective hull* of a module `N` is an injective module `I` with an embedding `N → I` such
that every nonzero element of `I` has a nonzero multiple in the image of `N`. Every module has
one (`exists_isInjectiveHull`): a maximal essential extension of `N` inside an injective module is
a retract of it.

An indecomposable injective module of finite length is *uniform*: two nonzero submodules meet
(`IsIndecomposableModule.inf_ne_bot_of_baer`, from Fitting's lemma). Hence it is a summand of the
injective hull of every module sharing a nonzero submodule with it
(`IsIndecomposableModule.isModuleSummand_of_isInjectiveHull`). These are the steps (1) ⇒ (2) of
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 5.30.

## Main definitions

* `IsInjectiveHull f`: `f : N → I` is an injective hull.
* `IsSummandOfInjectiveHull R P N`: `P` is a summand of an injective hull of `N`.

## Main results

* `exists_isInjectiveHull`: injective hulls exist.
* `IsSummandOfInjectiveHull.baer`: a summand of an injective hull is injective.
* `IsIndecomposableModule.inf_ne_bot_of_baer`: indecomposable injectives of finite length are
  uniform.
* `IsIndecomposableModule.isModuleSummand_of_isInjectiveHull`: such a module is a summand of the
  injective hull of any module sharing a nonzero submodule with it.
* `exists_isIndecomposable_summand_of_injective`: a nonzero module embedding into a module of
  finite length has a nonzero submodule embedding into an indecomposable summand of it.
-/

universe u v

namespace Categorification

open _root_.Module

section Hull

variable {R : Type*} [Ring R]

/-- `f : N → I` is an **injective hull** of `N`: it is injective, `I` is an injective module (in
the form of Baer's criterion, which is equivalent to injectivity), and every nonzero element of
`I` has a nonzero multiple in the image of `f`. -/
def IsInjectiveHull {N I : Type*} [AddCommGroup N] [Module R N] [AddCommGroup I] [Module R I]
    (f : N →ₗ[R] I) : Prop :=
  Function.Injective f ∧ Module.Baer R I ∧
    ∀ x : I, x ≠ 0 → ∃ a : R, a • x ≠ 0 ∧ a • x ∈ LinearMap.range f

variable (R) in
/-- `P` is a direct summand of an injective hull of `N`. -/
def IsSummandOfInjectiveHull (P N : Type v) [AddCommGroup P] [Module R P] [AddCommGroup N]
    [Module R N] : Prop :=
  ∃ (I : Type v) (_ : AddCommGroup I) (_ : Module R I) (f : N →ₗ[R] I),
    IsInjectiveHull f ∧ IsModuleSummand R P I

/-- A summand of an injective hull is injective (as a Baer module). -/
theorem IsSummandOfInjectiveHull.baer {P N : Type v} [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] (h : IsSummandOfInjectiveHull R P N) : Module.Baer R P := by
  obtain ⟨I, _, _, f, hf, i, r, hri⟩ := h
  exact Module.Baer.of_retract i r hri hf.2.1

end Hull

section Uniform

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **Indecomposable injective modules of finite length are uniform**: two nonzero submodules
meet. Otherwise the projection of `K₁ ⊕ K₂` onto `K₁` extends to an endomorphism that is neither
nilpotent nor bijective, against Fitting's lemma. -/
theorem IsIndecomposableModule.inf_ne_bot_of_baer [IsArtinian R M] [IsNoetherian R M]
    (hM : IsIndecomposableModule R M) (hB : Module.Baer R M) {K₁ K₂ : Submodule R M}
    (h₁ : K₁ ≠ ⊥) (h₂ : K₂ ≠ ⊥) : K₁ ⊓ K₂ ≠ ⊥ := by
  intro h
  let j : (K₁ × K₂) →ₗ[R] M := K₁.subtype.coprod K₂.subtype
  have hj : Function.Injective j := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have hab' : (a : M) + b = 0 := hab
    have ha : (a : M) ∈ K₁ ⊓ K₂ :=
      ⟨a.2, by rw [eq_neg_of_add_eq_zero_left hab']; exact K₂.neg_mem b.2⟩
    rw [h, Submodule.mem_bot] at ha
    have hb : (b : M) = 0 := by rw [ha, zero_add] at hab'; exact hab'
    simp only [Submodule.mem_bot, Prod.mk_eq_zero]
    exact ⟨Subtype.ext ha, Subtype.ext hb⟩
  obtain ⟨g, hg⟩ := hB.extension_property j hj (K₁.subtype ∘ₗ LinearMap.fst R K₁ K₂)
  have hg₁ : ∀ a ∈ K₁, g a = a := fun a ha => by
    have := LinearMap.congr_fun hg (⟨a, ha⟩, 0)
    simpa [j] using this
  have hg₂ : ∀ b ∈ K₂, g b = 0 := fun b hb => by
    have := LinearMap.congr_fun hg (0, ⟨b, hb⟩)
    simpa [j] using this
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂
  rcases hM.isNilpotent_or_bijective g with ⟨n, hn⟩ | hbij
  · have : ∀ m : ℕ, (g ^ m) a = a := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, hg₁ a ha]
    exact ha0 (by rw [← this n, hn, LinearMap.zero_apply])
  · exact hb0 (hbij.1 (by rw [hg₂ b hb, map_zero]))

/-- **An indecomposable injective module of finite length is a summand of an injective hull of
any module sharing a nonzero submodule with it.** If `a : K → M` and `b : K → S` are injective
with `K ≠ 0` and `f : S → I` is an injective hull, extending `f ∘ b` along `a` and `a` along
`f ∘ b` gives maps `M → I → M` whose composite fixes `a K`; it is injective since `M` is uniform,
hence bijective. -/
theorem IsIndecomposableModule.isModuleSummand_of_isInjectiveHull [IsArtinian R M]
    [IsNoetherian R M] (hM : IsIndecomposableModule R M) (hB : Module.Baer R M)
    {S I K : Type*} [AddCommGroup S] [Module R S] [AddCommGroup I] [Module R I] [AddCommGroup K]
    [Module R K] [Nontrivial K] {f : S →ₗ[R] I} (hf : IsInjectiveHull f) {a : K →ₗ[R] M}
    (ha : Function.Injective a) {b : K →ₗ[R] S} (hb : Function.Injective b) :
    IsModuleSummand R M I := by
  obtain ⟨φ, hφ⟩ := hf.2.1.extension_property a ha (f ∘ₗ b)
  obtain ⟨H, hH⟩ := hB.extension_property (f ∘ₗ b) (hf.1.comp hb) a
  let g : Module.End R M := H ∘ₗ φ
  have hga : ∀ x, g (a x) = a x := fun x => by
    change H (φ (a x)) = a x
    rw [← LinearMap.comp_apply φ a, hφ, ← LinearMap.comp_apply H, hH]
  have hker : LinearMap.ker g ⊓ LinearMap.range a = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy, x, rfl⟩
    have hy' : g (a x) = 0 := hy
    rw [hga] at hy'
    rw [hy', Submodule.mem_bot]
  have hrange : LinearMap.range a ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : K)
    intro h0
    exact hx (ha (by rw [map_zero]; exact (Submodule.mem_bot R).1 (h0 ▸ ⟨x, rfl⟩)))
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    exact hM.inf_ne_bot_of_baer hB hne hrange hker
  let e := LinearEquiv.ofBijective g (IsArtinian.bijective_of_injective_endomorphism g hinj)
  refine ⟨φ, e.symm.toLinearMap ∘ₗ H, fun x => ?_⟩
  change e.symm (H (φ x)) = x
  exact e.symm_apply_apply x

end Uniform

section Existence

variable {R : Type u} [Ring R]

/-- **A maximal essential extension inside a Baer module is a retract**: for `N ≤ E` with `E`
injective, there is `M ≥ N`, essential over `N` (every nonzero element of `M` has a nonzero
multiple in `N`), which is itself a Baer module. -/
theorem exists_baer_essential {E : Type*} [AddCommGroup E] [Module R E] (hE : Module.Baer R E)
    (N : Submodule R E) :
    ∃ M : Submodule R E, N ≤ M ∧ (∀ x ∈ M, x ≠ 0 → ∃ a : R, a • x ≠ 0 ∧ a • x ∈ N) ∧
      Module.Baer R M := by
  classical
  let 𝓐 : Set (Submodule R E) :=
    {M | N ≤ M ∧ ∀ x ∈ M, x ≠ 0 → ∃ a : R, a • x ≠ 0 ∧ a • x ∈ N}
  have hchain : ∀ c ⊆ 𝓐, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ 𝓐, ∀ z ∈ c, z ≤ ub := by
    intro c hc hch y hy
    refine ⟨sSup c, ⟨(hc hy).1.trans (le_sSup hy), fun x hx hx0 => ?_⟩, fun z hz => le_sSup hz⟩
    obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hch.directedOn).1 hx
    exact (hc hz).2 x hxz hx0
  obtain ⟨M, -, hMmax⟩ := zorn_le_nonempty₀ 𝓐 hchain N
    ⟨le_rfl, fun x hx hx0 => ⟨1, by rwa [one_smul], by rwa [one_smul]⟩⟩
  obtain ⟨hNM, hess⟩ := hMmax.1
  -- a complement `C` of `M`, maximal among submodules meeting `M` trivially
  let 𝓒 : Set (Submodule R E) := {C | Disjoint C M}
  have hchain' : ∀ c ⊆ 𝓒, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ 𝓒, ∀ z ∈ c, z ≤ ub := by
    intro c hc hch y hy
    refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
    refine Submodule.disjoint_def.2 fun x hx hxM => ?_
    obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hch.directedOn).1 hx
    exact Submodule.disjoint_def.1 (hc hz) x hxz hxM
  obtain ⟨C, -, hCmax⟩ := zorn_le_nonempty₀ 𝓒 hchain' ⊥ disjoint_bot_left
  have hCM : Disjoint C M := hCmax.1
  let πM : M →ₗ[R] E ⧸ C := C.mkQ ∘ₗ M.subtype
  have hπM : Function.Injective πM := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    have hmC : (m : E) ∈ C := (Submodule.Quotient.mk_eq_zero C).1 hm
    rw [Submodule.mem_bot]
    exact Subtype.ext (Submodule.disjoint_def.1 hCM _ hmC m.2)
  obtain ⟨ψ, hψ⟩ := hE.extension_property πM hπM M.subtype
  have hψm : ∀ m ∈ M, ψ (C.mkQ m) = m := fun m hm => LinearMap.congr_fun hψ ⟨m, hm⟩
  -- `π M` is essential in `E / C`
  have hkey : ∀ y : E, C.mkQ y ≠ 0 →
      ∃ r : R, ∃ m ∈ M, m ≠ 0 ∧ C.mkQ m = r • C.mkQ y := by
    intro y hy
    have hyC : y ∉ C := fun h => hy ((Submodule.Quotient.mk_eq_zero C).2 h)
    have hnot : ¬ Disjoint (C ⊔ R ∙ y) M := by
      intro hd
      exact hyC (hCmax.2 hd le_sup_left (Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self y)))
    obtain ⟨m, ⟨hmC, hmM⟩, hm0⟩ : ∃ m, m ∈ (C ⊔ R ∙ y) ⊓ M ∧ m ≠ 0 := by
      by_contra h
      push Not at h
      exact hnot (Submodule.disjoint_def.2 fun x hx hxM => h x ⟨hx, hxM⟩)
    obtain ⟨c, hc, z, hz, rfl⟩ := Submodule.mem_sup.1 hmC
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨r, _, hmM, hm0, ?_⟩
    rw [map_add, map_smul, show C.mkQ c = 0 from (Submodule.Quotient.mk_eq_zero C).2 hc, zero_add]
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [Submodule.mem_bot]
    by_contra hz0
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective C z
    obtain ⟨r, m, hm, hm0, hrm⟩ := hkey y hz0
    apply hm0
    have hψz : ψ (C.mkQ y) = 0 := hz
    have := congrArg ψ hrm
    rwa [hψm m hm, map_smul, hψz, smul_zero] at this
  have hrange : LinearMap.range ψ ∈ 𝓐 := by
    refine ⟨hNM.trans fun m hm => ⟨C.mkQ m, hψm m hm⟩, ?_⟩
    rintro _ ⟨z, rfl⟩ hx0
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective C z
    have hz0 : C.mkQ y ≠ 0 := fun h => hx0 (by change ψ (C.mkQ y) = 0; rw [h, map_zero])
    obtain ⟨r, m, hm, hm0, hrm⟩ := hkey y hz0
    obtain ⟨a, ha0, haN⟩ := hess m hm hm0
    have : (a * r) • ψ (C.mkQ y) = a • m := by
      rw [mul_smul, ← map_smul, ← hrm, hψm m hm]
    exact ⟨a * r, this ▸ ha0, this ▸ haN⟩
  have hle : LinearMap.range ψ ≤ M := hMmax.2 hrange fun m hm => ⟨C.mkQ m, hψm m hm⟩
  let ρ : E →ₗ[R] M := (ψ ∘ₗ C.mkQ).codRestrict M fun x => hle ⟨C.mkQ x, rfl⟩
  exact ⟨M, hNM, hess, Module.Baer.of_retract M.subtype ρ (fun m => Subtype.ext (hψm m m.2)) hE⟩

/-- **Injective hulls exist.** -/
theorem exists_isInjectiveHull (S : Type u) [AddCommGroup S] [Module R S] :
    ∃ (I : Type u) (_ : AddCommGroup I) (_ : Module R I) (f : S →ₗ[R] I), IsInjectiveHull f := by
  let E : ModuleCat.{u} R := CategoryTheory.Injective.under (ModuleCat.of R S)
  let ι : ModuleCat.of R S ⟶ E := CategoryTheory.Injective.ι (ModuleCat.of R S)
  have hι : Function.Injective ι.hom := (ModuleCat.mono_iff_injective ι).1 inferInstance
  have hE : Module.Baer R E :=
    Module.Baer.of_injective ((Module.injective_iff_injective_object R E).2
      (CategoryTheory.Injective.injective_under (ModuleCat.of R S)))
  obtain ⟨M, hNM, hess, hM⟩ := exists_baer_essential hE (LinearMap.range ι.hom)
  let f : S →ₗ[R] M := ι.hom.codRestrict M fun x => hNM ⟨x, rfl⟩
  refine ⟨M, inferInstance, inferInstance, f, fun x y h => hι (congrArg Subtype.val h), hM,
    fun x hx => ?_⟩
  obtain ⟨a, ha0, s, hs⟩ := hess x x.2 fun h => hx (Subtype.ext h)
  exact ⟨a, fun h => ha0 (congrArg Subtype.val h), s, Subtype.ext hs⟩

end Existence

section Decomposition

variable {R : Type*} [Ring R] {X : Type*} [AddCommGroup X] [Module R X]

/-- **A nonzero submodule meets an indecomposable summand.** If a nontrivial module `K` embeds
into a module `X` of finite length, some nonzero submodule of `K` embeds into an indecomposable
direct summand of `X`: split a minimal summand admitting such an embedding. -/
theorem exists_isIndecomposable_summand [IsArtinian R X] {K : Type*} [AddCommGroup K]
    [Module R K] [Nontrivial K] (φ : K →ₗ[R] X) (hφ : Function.Injective φ) :
    ∃ S : Submodule R X, IsIndecomposableModule R S ∧ IsModuleSummand R S X ∧
      ∃ K' : Submodule R K, K' ≠ ⊥ ∧ ∃ ψ : K' →ₗ[R] S, Function.Injective ψ := by
  classical
  let 𝓢 : Set (Submodule R X) := {S | (∃ r : X →ₗ[R] S, ∀ x : S, r x = x) ∧
    ∃ K' : Submodule R K, K' ≠ ⊥ ∧ ∃ ψ : K' →ₗ[R] X, Function.Injective ψ ∧
      LinearMap.range ψ ≤ S}
  have htop : ⊤ ∈ 𝓢 := ⟨⟨LinearMap.id.codRestrict ⊤ fun _ => trivial, fun _ => rfl⟩, ⊤,
    by simp, φ ∘ₗ Submodule.subtype ⊤, hφ.comp Subtype.val_injective, le_top⟩
  obtain ⟨S, ⟨⟨r, hr⟩, K', hK', ψ, hψ, hψS⟩, hmin⟩ := wellFounded_lt.has_min 𝓢 ⟨⊤, htop⟩
  let ψ' : K' →ₗ[R] S := ψ.codRestrict S fun x => hψS ⟨x, rfl⟩
  have hψ' : Function.Injective ψ' := fun x y h => hψ (congrArg Subtype.val h)
  have : Nontrivial K' := Submodule.nontrivial_iff_ne_bot.2 hK'
  refine ⟨S, ⟨?_, fun e he => ?_⟩, ⟨S.subtype, r, hr⟩, K', hK', ψ', hψ'⟩
  · obtain ⟨x, hx⟩ := exists_ne (0 : K')
    exact ⟨ψ' x, 0, fun h => hx (hψ' (by rw [h, map_zero]))⟩
  by_contra hne
  push Not at hne
  obtain ⟨he0, he1⟩ := hne
  have hfix : ∀ y : S, y ∈ LinearMap.range e → e y = y := by
    rintro _ ⟨z, rfl⟩
    rw [← Module.End.mul_apply, he.eq]
  let S₁ : Submodule R X := (LinearMap.range e).map S.subtype
  let S₂ : Submodule R X := (LinearMap.ker e).map S.subtype
  have hS₁ : S₁ < S := by
    refine lt_of_le_of_ne (Submodule.map_subtype_le _ _) fun h => he1 (LinearMap.ext fun y => ?_)
    have hy : (y : X) ∈ S₁ := by rw [h]; exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := Subtype.ext hzy
    subst this
    rw [Module.End.one_apply, hfix z hz]
  have hS₂ : S₂ < S := by
    refine lt_of_le_of_ne (Submodule.map_subtype_le _ _) fun h => he0 (LinearMap.ext fun y => ?_)
    have hy : (y : X) ∈ S₂ := by rw [h]; exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := Subtype.ext hzy
    subst this
    rw [LinearMap.zero_apply]
    exact hz
  let e' : Module.End R S := 1 - e
  have he' : ∀ y, e (e' y) = 0 := fun y => by
    rw [show e' y = y - e y from rfl, map_sub, ← Module.End.mul_apply, he.eq, sub_self]
  by_cases hinj : Function.Injective (e ∘ₗ ψ')
  · refine hmin S₁ ⟨⟨(S.subtype ∘ₗ e ∘ₗ r).codRestrict S₁ fun x => ⟨e (r x), ⟨r x, rfl⟩, rfl⟩,
      fun x => Subtype.ext ?_⟩, K', hK', S.subtype ∘ₗ e ∘ₗ ψ',
      Subtype.val_injective.comp hinj, ?_⟩ hS₁
    · obtain ⟨w, ⟨z, hzw⟩, hw⟩ := x.2
      change ((e (r x) : S) : X) = x
      rw [← hw, Submodule.subtype_apply, hr w, hfix w ⟨z, hzw⟩]
    · rintro _ ⟨k, rfl⟩
      exact ⟨e (ψ' k), ⟨ψ' k, rfl⟩, rfl⟩
  · obtain ⟨k₀, hk₀⟩ : ∃ k : K', k ∈ LinearMap.ker (e ∘ₗ ψ') ∧ k ≠ 0 := by
      by_contra h
      push Not at h
      exact hinj ((injective_iff_map_eq_zero _).2 fun k hk => h k hk)
    let K'' : Submodule R K := (LinearMap.ker (e ∘ₗ ψ')).map K'.subtype
    have hle : K'' ≤ K' := Submodule.map_subtype_le _ _
    refine hmin S₂ ⟨⟨(S.subtype ∘ₗ e' ∘ₗ r).codRestrict S₂ fun x =>
      ⟨e' (r x), he' (r x), rfl⟩, fun x => Subtype.ext ?_⟩, K'', ?_,
      ψ ∘ₗ Submodule.inclusion hle, hψ.comp (Submodule.inclusion_injective hle), ?_⟩ hS₂
    · obtain ⟨z, hz, hzx⟩ := x.2
      change ((e' (r x) : S) : X) = x
      rw [← hzx, Submodule.subtype_apply, hr z, show e' z = z - e z from rfl,
        show e z = 0 from hz, sub_zero]
    · intro h0
      apply hk₀.2
      have : (k₀ : K) ∈ K'' := ⟨k₀, hk₀.1, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact Subtype.ext this
    · rintro _ ⟨k, rfl⟩
      obtain ⟨k', hk', hkk'⟩ := k.2
      have hk'' : Submodule.inclusion hle k = k' := Subtype.ext hkk'.symm
      refine ⟨ψ' k', hk', ?_⟩
      change (ψ k' : X) = ψ (Submodule.inclusion hle k)
      rw [hk'']

end Decomposition

section Summand

variable {R : Type u} [Ring R] {P X : Type u} [AddCommGroup P] [Module R P] [AddCommGroup X]
  [Module R X]

/-- **An indecomposable injective module of finite length is a summand of the injective hull of an
indecomposable summand of `X`** as soon as a nonzero submodule of it embeds into `X` (`X` of
finite length). -/
theorem IsIndecomposableModule.exists_isSummandOfInjectiveHull [IsArtinian R P]
    [IsNoetherian R P] [IsArtinian R X] (hP : IsIndecomposableModule R P) (hB : Module.Baer R P)
    {K : Submodule R P} (hK : K ≠ ⊥) (φ : K →ₗ[R] X) (hφ : Function.Injective φ) :
    ∃ S : Submodule R X, IsIndecomposableModule R S ∧ IsModuleSummand R S X ∧
      IsSummandOfInjectiveHull R P S := by
  have : Nontrivial K := Submodule.nontrivial_iff_ne_bot.2 hK
  obtain ⟨S, hS, hSX, K', hK', ψ, hψ⟩ := exists_isIndecomposable_summand φ hφ
  have : Nontrivial K' := Submodule.nontrivial_iff_ne_bot.2 hK'
  obtain ⟨I, _, _, f, hf⟩ := exists_isInjectiveHull (R := R) S
  exact ⟨S, hS, hSX, I, inferInstance, inferInstance, f, hf,
    hP.isModuleSummand_of_isInjectiveHull hB hf (a := K.subtype ∘ₗ K'.subtype)
      (Subtype.val_injective.comp Subtype.val_injective) hψ⟩

end Summand

end Categorification
