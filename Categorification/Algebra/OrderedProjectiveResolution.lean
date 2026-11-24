/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentEquiv
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Categorification.Algebra.ModuleFiltration

/-!
# Projective resolutions with ordered loading support

The higher loading terms in Webster, arXiv:1309.3796v2, Lemma 6.11, p. 65
(step `f_n → s_n`), can be obtained from the higher standard filtrations of
the kernels of the standard quotients. Lifting a projective cover of the
quotient in a short exact sequence constructs the next kernel as an extension,
so its filtration labels remain above the original labels.
-/

namespace Categorification.ModuleFiltration

universe u v w

variable {R : Type u} [Ring R] {ι : Type w} {L : ι → ModuleCat.{v} R}
  {X Y Z P Q : ModuleCat.{v} R}

/-- Combining surjections onto the two ends of a short exact sequence by a supplied lift
produces a surjection onto the middle term whose kernel extends the two given kernels. -/
theorem HasFiltration.cover_extension_kernel
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hf : Function.Injective f)
    (hfg : Function.Exact f g)
    (p : P →ₗ[R] X) (q : Q →ₗ[R] Z) (hps : Function.Surjective p)
    (lift : Q →ₗ[R] Y) (hlift : g.comp lift = q)
    {mp mq : List ι}
    (hp : HasFiltration L mp (ModuleCat.of R (LinearMap.ker p)))
    (hq : HasFiltration L mq (ModuleCat.of R (LinearMap.ker q))) :
    (Function.Surjective q → Function.Surjective ((f.comp p).coprod lift)) ∧
      HasFiltration L (mq ++ mp) (ModuleCat.of R
        (LinearMap.ker ((f.comp p).coprod lift))) := by
  let F : (P × Q) →ₗ[R] Y := (f.comp p).coprod lift
  have eqF (a : P) (b : Q) : F (a,b) = f (p a) + lift b := rfl
  have eqgF (a : P) (b : Q) : g (F (a,b)) = q b := by
    rw [eqF, map_add, hfg.apply_apply_eq_zero, zero_add]
    exact LinearMap.congr_fun hlift b
  constructor
  · intro hqs y
    obtain ⟨b, hb⟩ := hqs (g y)
    obtain ⟨x, hx⟩ := (hfg (y - lift b)).mp (by
      rw [map_sub, show g (lift b) = q b from LinearMap.congr_fun hlift b, hb, sub_self])
    obtain ⟨a, ha⟩ := hps x
    exact ⟨(a,b), by rw [eqF, ha, hx, sub_add_cancel]⟩
  · let i : LinearMap.ker p →ₗ[R] LinearMap.ker F :=
      (((LinearMap.inl R P Q).comp (LinearMap.ker p).subtype).codRestrict _ (by
        intro a
        change F ((a : P), 0) = 0
        rw [eqF, show p (a : P) = 0 from a.2, map_zero, map_zero, add_zero]))
    let j : LinearMap.ker F →ₗ[R] LinearMap.ker q :=
      (((LinearMap.snd R P Q).comp (LinearMap.ker F).subtype).codRestrict _ (by
        intro z
        change q z.1.2 = 0
        rw [← eqgF, show F z.1 = 0 from z.2, map_zero]))
    have hi : Function.Injective i := fun a b h => Subtype.ext
      (congrArg (fun z : LinearMap.ker F => z.1.1) h)
    have hij : Function.Exact i j := by
      rintro ⟨⟨a,b⟩, h⟩
      constructor
      · intro hz
        have hb : b = 0 := congrArg Subtype.val hz
        subst b
        have hpa : p a = 0 := hf (by
          change F (a,0) = 0 at h
          rw [eqF, map_zero, add_zero] at h
          exact h.trans (map_zero f).symm)
        exact ⟨⟨a,hpa⟩, rfl⟩
      · rintro ⟨z,hz⟩
        rw [← hz]
        rfl
    have hj : Function.Surjective j := by
      intro b
      obtain ⟨x, hx⟩ := (hfg (-lift b.1)).mp (by
        rw [map_neg, show g (lift b.1) = q b.1 from LinearMap.congr_fun hlift b.1,
          show q b.1 = 0 from b.2, neg_zero])
      obtain ⟨a, ha⟩ := hps x
      refine ⟨⟨(a,b.1), ?_⟩, rfl⟩
      change F (a,b.1) = 0
      rw [eqF, ha, hx, neg_add_cancel]
    exact hq.extension i j hi hij hj hp


private theorem projective_prod {R : Type u} [Ring R] {X Y : Type u}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (hX : Module.Projective R X) (hY : Module.Projective R Y) :
    Module.Projective R (X × Y) := by
  apply Module.Projective.of_lifting_property
  intro M N _ _ _ _ f g hf
  obtain ⟨p, hp⟩ := Module.projective_lifting_property f (g.comp (LinearMap.inl R X Y)) hf
  obtain ⟨q, hq⟩ := Module.projective_lifting_property f (g.comp (LinearMap.inr R X Y)) hf
  refine ⟨p.coprod q, ?_⟩
  apply LinearMap.ext
  rintro ⟨x,y⟩
  change f (p x + q y) = g (x,y)
  rw [map_add, show f (p x) = g (x,0) from LinearMap.congr_fun hp x,
    show f (q y) = g (0,y) from LinearMap.congr_fun hq y, ← map_add]
  congr 1; simp

section Ordered

variable {A : Type u} [Ring A] {Label : Type w} {S : Label → ModuleCat.{u} A}
  (e : Label → A) (above : Label → Label → Prop)
  (q : ∀ c, lIdeal (e c) →ₗ[A] S c)
  (hq : ∀ c, Function.Surjective (q c))
  (hproj : ∀ c, Module.Projective A (lIdeal (e c)))
  (hker : ∀ c, ∃ m : List Label, (∀ d ∈ m, above c d) ∧
    HasFiltration S m (ModuleCat.of A (LinearMap.ker (q c))))

include q hq hproj hker in
/-- A standard-filtered module admits a surjection from loading projectives at its
filtration labels. Its next kernel has a standard filtration at higher labels. -/
theorem HasFiltration.exists_loading_cover_of_ordered_kernels
    {m : List Label} {Y : ModuleCat.{u} A} (h : HasFiltration S m Y) :
    ∃ (P : ModuleCat.{u} A) (p : P →ₗ[A] Y), Function.Surjective p ∧ Module.Projective A P ∧
      (∃ (J : Type) (label : J → Label) (inc : ∀ j, lIdeal (e (label j)) →ₗ[A] P),
        (∀ j, label j ∈ m) ∧
          ∀ x : P, x ∈ Submodule.span A {y | ∃ j z, inc j z = y}) ∧
      ∃ m' : List Label, (∀ d ∈ m', ∃ c ∈ m, above c d) ∧
        HasFiltration S m' (ModuleCat.of A (LinearMap.ker p)) := by
  induction h with
  | @zero Y hY =>
    let P : ModuleCat.{u} A := ModuleCat.of A PUnit.{u+1}
    let p : P →ₗ[A] Y := 0
    refine ⟨P, p, fun y => ⟨0, Subsingleton.elim _ _⟩, ?_,
      ⟨Empty, Empty.elim, fun j => j.elim, fun j => j.elim, ?_⟩,
      [], by simp, HasFiltration.zero inferInstance⟩
    · apply Module.Projective.of_lifting_property
      intro M N _ _ _ _ f g _
      exact ⟨0, LinearMap.ext fun x => by rw [Subsingleton.elim x 0]; simp⟩
    · intro x
      rw [Subsingleton.elim x 0]
      exact Submodule.zero_mem _
  | @cons X Y Z f g m c hf hfg hg _ hZ ih =>
    obtain ⟨P,p,hps,hP,⟨J,label,inc,hlabel,hspan⟩,m', hm', hp⟩ := ih
    obtain ⟨eq⟩ := hZ
    let Q := ModuleCat.of A (lIdeal (e c))
    let q' : Q →ₗ[A] Z := eq.symm.toLinearMap.comp (q c)
    have hqs : Function.Surjective q' := eq.symm.surjective.comp (hq c)
    let := hproj c
    obtain ⟨lift, hlift⟩ := Module.projective_lifting_property g q' hg
    obtain ⟨n,hn,hqk⟩ := hker c
    have eqker : LinearMap.ker q' = LinearMap.ker (q c) := by
      ext x
      exact eq.symm.map_eq_zero_iff
    have hqk' : HasFiltration S n (ModuleCat.of A (LinearMap.ker q')) := eqker ▸ hqk
    obtain ⟨hF, hkF⟩ := hp.cover_extension_kernel f g hf hfg p q' hps lift hlift hqk'
    let P' := ModuleCat.of A (P × Q)
    let lab : J ⊕ Unit → Label := Sum.elim label (fun _ => c)
    let F : ∀ j : J ⊕ Unit, lIdeal (e (lab j)) →ₗ[A] P'
      | .inl j => (LinearMap.inl A P Q).comp (inc j)
      | .inr _ => LinearMap.inr A P Q
    refine ⟨P', (f.comp p).coprod lift, hF hqs, projective_prod hP (hproj c), ⟨J ⊕ Unit,lab,F,?_ ,?_⟩, n ++ m', ?_, hkF⟩
    · rintro (j | j)
      · exact List.mem_cons_of_mem _ (hlabel j)
      · exact List.mem_cons_self
    · rintro ⟨x,y⟩
      have hx : (LinearMap.inl A P Q) x ∈ Submodule.span A
          {z | ∃ j z', F j z' = z} := by
        have hmap : (Submodule.span A {z | ∃ j z', inc j z' = z}).map
            (LinearMap.inl A P Q) ≤ Submodule.span A {z | ∃ j z', F j z' = z} := by
          rw [Submodule.map_span]
          apply Submodule.span_le.mpr
          rintro _ ⟨_, ⟨j,z,rfl⟩, rfl⟩
          exact Submodule.subset_span ⟨.inl j, z, rfl⟩
        exact hmap ⟨x, hspan x, rfl⟩
      have hy : (LinearMap.inr A P Q) y ∈ Submodule.span A {z | ∃ j z', F j z' = z} :=
        Submodule.subset_span ⟨.inr (), y, rfl⟩
      have heq : (x,y) = (LinearMap.inl A P Q) x + (LinearMap.inr A P Q) y := by
        ext <;> simp
      rw [heq]
      exact Submodule.add_mem _ hx hy
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact ⟨c, List.mem_cons_self, hn d hd⟩
      · obtain ⟨c', hc', hcd⟩ := hm' d hd
        exact ⟨c', List.mem_cons_of_mem _ hc', hcd⟩

end Ordered


section Resolution

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {A : Type u} [Ring A] {Label : Type w} {S : Label → ModuleCat.{u} A}
  {e : Label → A} {above : Label → Label → Prop}

/-- Loading projectives surject onto the individual standards, with higher standard kernels. -/
structure OrderedStandardCovers (S : Label → ModuleCat.{u} A) (e : Label → A)
    (above : Label → Label → Prop) where
  quotient : ∀ c, lIdeal (e c) →ₗ[A] S c
  surjective : ∀ c, Function.Surjective (quotient c)
  projective : ∀ c, Module.Projective A (lIdeal (e c))
  kernel : ∀ c, ∃ m : List Label, (∀ d ∈ m, above c d) ∧
    HasFiltration S m (ModuleCat.of A (LinearMap.ker (quotient c)))

private structure FilteredSyzygy (S : Label → ModuleCat.{u} A) where
  module : ModuleCat.{u} A
  labels : List Label
  filtration : HasFiltration S labels module

private structure LoadingCover (S : Label → ModuleCat.{u} A) (e : Label → A)
    (above : Label → Label → Prop) (M : FilteredSyzygy S) where
  obj : ModuleCat.{u} A
  map : obj →ₗ[A] M.module
  surjective : Function.Surjective map
  projective : Module.Projective A obj
  index : Type
  label : index → Label
  summand : ∀ j, lIdeal (e (label j)) →ₗ[A] obj
  mem_labels : ∀ j, label j ∈ M.labels
  span : ∀ x : obj, x ∈ Submodule.span A {y | ∃ j z, summand j z = y}
  labels' : List Label
  mem_above : ∀ d ∈ labels', ∃ c ∈ M.labels, above c d
  filtration : HasFiltration S labels' (ModuleCat.of A (LinearMap.ker map))

private def LoadingCover.next {M : FilteredSyzygy S}
    (P : LoadingCover S e above M) : FilteredSyzygy S :=
  ⟨ModuleCat.of A (LinearMap.ker P.map), P.labels', P.filtration⟩

private def chooseCover (data : OrderedStandardCovers S e above) (M : FilteredSyzygy S) :
    LoadingCover S e above M := Classical.choice (by
  obtain ⟨P, p, hp, hP, ⟨J, label, inc, hlabel, hspan⟩, m, hm, hf⟩ :=
    HasFiltration.exists_loading_cover_of_ordered_kernels e above data.quotient data.surjective
      data.projective data.kernel M.filtration
  exact ⟨⟨P, p, hp, hP, J, label, inc, hlabel, hspan, m, hm, hf⟩⟩)

private def syzygy (data : OrderedStandardCovers S e above) (s : Label) : ℕ → FilteredSyzygy S
  | 0 => ⟨S s, [s], HasFiltration.single (LinearEquiv.refl A _)⟩
  | n + 1 => (chooseCover data (syzygy data s n)).next

variable (data : OrderedStandardCovers S e above) (s : Label)

private abbrev cover (n : ℕ) := chooseCover data (syzygy data s n)

private abbrev diff (n : ℕ) : (cover data s (n + 1)).obj →ₗ[A] (cover data s n).obj :=
  (LinearMap.ker (cover data s n).map).subtype.comp (cover data s (n + 1)).map

private theorem exact_diff_map (n : ℕ) :
    Function.Exact (diff data s n) (cover data s n).map := by
  intro x
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := (cover data s (n + 1)).surjective ⟨x, hx⟩
    exact ⟨v, congrArg Subtype.val hv⟩
  · rintro ⟨v,rfl⟩
    exact ((cover data s (n + 1)).map v).2

private theorem exact_diff_diff (n : ℕ) :
    Function.Exact (diff data s (n + 1)) (diff data s n) := by
  intro x
  rw [show diff data s n x = 0 ↔ (cover data s (n + 1)).map x = 0 from
    by
      let K := LinearMap.ker (cover data s n).map
      let y : K := (cover data s (n+1)).map x
      change K.subtype y = 0 ↔ y = 0
      rw [← map_zero K.subtype, (Submodule.injective_subtype _).eq_iff]]
  exact exact_diff_map data s (n + 1) x

private def loadingChain : ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of (fun n => (cover data s n).obj)
    (fun n => ModuleCat.ofHom (diff data s n))
    (fun n => ModuleCat.hom_ext (LinearMap.ext fun x =>
      (exact_diff_diff data s n).apply_apply_eq_zero x))

private theorem loadingChain_d_succ (n : ℕ) :
    (loadingChain data s).d (n+1) n = ModuleCat.ofHom (diff data s n) :=
  by simp [loadingChain]

private theorem loadingChain_exactAt (n : ℕ) : (loadingChain data s).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', loadingChain_d_succ]
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact exact_diff_diff data s n

private def augmentation : loadingChain data s ⟶ (ChainComplex.single₀ _).obj (S s) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom (cover data s 0).map, by
    rw [loadingChain_d_succ]
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => (exact_diff_map data s 0).apply_apply_eq_zero x⟩

private theorem augmentation_quasiIso : QuasiIso (augmentation data s) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · let T := ShortComplex.mk
        (ModuleCat.ofHom (diff data s 0)) (ModuleCat.ofHom (cover data s 0).map)
        (ModuleCat.hom_ext (LinearMap.ext fun x => (exact_diff_map data s 0).apply_apply_eq_zero x))
      refine (ShortComplex.exact_and_epi_g_iff_of_iso (S₂ := T) ?_).2 ⟨?_, ?_⟩
      · refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
        · apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change diff data s 0 x = ((loadingChain data s).d 1 0).hom x
          rw [loadingChain_d_succ]
          rfl
        · apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change (cover data s 0).map x = ((augmentation data s).f 0).hom x
          unfold augmentation
          erw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
          rfl
      · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mpr
        exact exact_diff_map data s 0
      · exact (ModuleCat.epi_iff_surjective _).mpr (cover data s 0).surjective
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact loadingChain_exactAt data s n
    · exact ChainComplex.exactAt_succ_single_obj _ _

/-- A projective resolution assembled from the ordered loading covers of successive syzygies. -/
def OrderedStandardCovers.projectiveResolution : ProjectiveResolution (S s) where
  complex := loadingChain data s
  projective n := (IsProjective.iff_projective ((cover data s n).obj)).mp (cover data s n).projective
  π := augmentation data s
  quasiIso := augmentation_quasiIso data s

private theorem syzygy_above (htrans : ∀ a b c, above a b → above b c → above a c) :
    ∀ n : ℕ, ∀ d ∈ (syzygy data s (n + 1)).labels, above s d := by
  intro n
  induction n with
  | zero =>
    intro d hd
    obtain ⟨c,hc,hcd⟩ := (cover data s 0).mem_above d hd
    have : c = s := List.mem_singleton.mp hc
    exact this ▸ hcd
  | succ n ih =>
    intro d hd
    obtain ⟨c,hc,hcd⟩ := (cover data s (n+1)).mem_above d hd
    exact htrans _ _ _ (ih c hc) hcd

/-- Every positive term of the loading projective resolution is spanned by higher
loading summands, as required in Webster's Lemma 6.11. -/
theorem OrderedStandardCovers.projectiveResolution_loading_support
    (htrans : ∀ a b c, above a b → above b c → above a c) (n : ℕ) :
    ∃ (J : Type) (label : J → Label) (inc : ∀ j,
      lIdeal (e (label j)) →ₗ[A] (data.projectiveResolution s).complex.X (n + 1)),
      (∀ j, above s (label j)) ∧ ∀ x : (data.projectiveResolution s).complex.X (n + 1),
        x ∈ Submodule.span A {y | ∃ j z, inc j z = y} := by
  let P := cover data s (n + 1)
  exact ⟨P.index, P.label, P.summand,
    fun j => syzygy_above data s htrans n _ (P.mem_labels j), P.span⟩

end

end Resolution

end Categorification.ModuleFiltration
