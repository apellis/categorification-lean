/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# The cone of a lifted map of projective resolutions

Webster, arXiv:1309.3796v3, §7.1, proof of Proposition 7.6: given a short exact sequence
`0 → A → B → C → 0` of modules and projective resolutions `P_A → A`, `P_B → B`, lift `A → B` to a
chain map `φ : P_A → P_B`; the cone of `φ` is a projective resolution of `C`. Its term in degree
`n + 1` is `P_B(n + 1) × P_A(n)`, and in degree `0` it is `P_B(0)`.

## Main definitions

* `ModuleCat.ProjectiveResolution.cone`: the projective resolution of `C`.

## Main results

* `ModuleCat.ProjectiveResolution.cone_X_zero`, `cone_X_succ`: its terms.
-/

universe v u

namespace ModuleCat.ProjectiveResolution

open CategoryTheory Limits

variable {R : Type u} [Ring R] {A B C : ModuleCat.{v} R} (f : A ⟶ B) (g : B ⟶ C)
  (PA : CategoryTheory.ProjectiveResolution A) (PB : CategoryTheory.ProjectiveResolution B)

local notation "φ" => CategoryTheory.ProjectiveResolution.lift f PA PB

/-- The terms of the cone: `P_B(0)` in degree `0`, `P_B(n + 1) × P_A(n)` in degree `n + 1`. -/
def coneX : ℕ → ModuleCat.{v} R
  | 0 => PB.complex.X 0
  | n + 1 => ModuleCat.of R (PB.complex.X (n + 1) × PA.complex.X n)

/-- The differential of the cone: `(b, a) ↦ (d b + φ a, -d a)`, and `(b, a) ↦ d b + φ a` into
degree `0`. -/
noncomputable def coneD : ∀ n, coneX PA PB (n + 1) ⟶ coneX PA PB n
  | 0 => ModuleCat.ofHom (LinearMap.coprod (PB.complex.d 1 0).hom ((φ).f 0).hom)
  | n + 1 => ModuleCat.ofHom (LinearMap.prod
      ((PB.complex.d (n + 2) (n + 1)).hom.comp (LinearMap.fst R _ _) +
        ((φ).f (n + 1)).hom.comp (LinearMap.snd R _ _))
      (-((PA.complex.d (n + 1) n).hom.comp (LinearMap.snd R _ _))))

private theorem dd (K : ChainComplex (ModuleCat.{v} R) ℕ) (i j l : ℕ) (x : K.X i) :
    (K.d j l).hom ((K.d i j).hom x) = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d]
  rfl

private theorem comm (i j : ℕ) (x : PA.complex.X i) :
    (PB.complex.d i j).hom (((φ).f i).hom x) = ((φ).f j).hom ((PA.complex.d i j).hom x) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, (φ).comm i j]
  rfl

theorem coneD_comp (n : ℕ) : coneD f PA PB (n + 1) ≫ coneD f PA PB n = 0 := by
  ext ⟨b, a⟩
  cases n with
  | zero =>
    change (PB.complex.d 1 0).hom ((PB.complex.d 2 1).hom b + ((φ).f 1).hom a) +
      ((φ).f 0).hom (-(PA.complex.d 1 0).hom a) = 0
    rw [map_add, dd, comm, map_neg, zero_add, add_neg_cancel]
  | succ n =>
    refine Prod.ext ?_ ?_
    · change (PB.complex.d (n + 2) (n + 1)).hom ((PB.complex.d (n + 3) (n + 2)).hom b +
        ((φ).f (n + 2)).hom a) + ((φ).f (n + 1)).hom (-(PA.complex.d (n + 2) (n + 1)).hom a) = 0
      rw [map_add, dd, comm, map_neg, zero_add, add_neg_cancel]
    · change -(PA.complex.d (n + 1) n).hom (-(PA.complex.d (n + 2) (n + 1)).hom a) = 0
      rw [map_neg, dd, neg_zero, neg_zero]

/-- The cone complex. -/
noncomputable def coneComplex : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (coneX PA PB) (coneD f PA PB) (coneD_comp f PA PB)

theorem coneComplex_d (m : ℕ) : (coneComplex f PA PB).d (m + 1) m = coneD f PA PB m :=
  ChainComplex.of_d (coneX PA PB) (coneD f PA PB) m

instance coneX_projective (n : ℕ) : Projective (coneX PA PB n) := by
  cases n with
  | zero => exact PB.projective 0
  | succ n =>
    exact Projective.of_iso (ModuleCat.biprodIsoProd (PB.complex.X (n + 1)) (PA.complex.X n))
      inferInstance

variable {f g}

private theorem gf (hfg : Function.Exact f g) (x : A) : g.hom (f.hom x) = 0 :=
  (hfg (f.hom x)).2 ⟨x, rfl⟩

private theorem π_comm (x : PA.complex.X 0) :
    (PB.π.f 0).hom (((φ).f 0).hom x) = f.hom ((PA.π.f 0).hom x) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    CategoryTheory.ProjectiveResolution.lift_commutes_zero]
  rfl

private theorem exact_zero (P : CategoryTheory.ProjectiveResolution B) (x : P.complex.X 0)
    (hx : (P.π.f 0).hom x = 0) : ∃ y, (P.complex.d 1 0).hom y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 P.exact₀ x hx

private theorem exact_succ' {Z : ModuleCat.{v} R} (P : CategoryTheory.ProjectiveResolution Z)
    (n : ℕ) (x : P.complex.X (n + 1)) (hx : (P.complex.d (n + 1) n).hom x = 0) :
    ∃ y, (P.complex.d (n + 2) (n + 1)).hom y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (P.exact_succ n) x hx

private theorem exact_zero' (P : CategoryTheory.ProjectiveResolution A) (x : P.complex.X 0)
    (hx : (P.π.f 0).hom x = 0) : ∃ y, (P.complex.d 1 0).hom y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 P.exact₀ x hx

variable (f g)

theorem cone_d_comp_π (hfg : Function.Exact f g) :
    (coneComplex f PA PB).d 1 0 ≫ (PB.π.f 0 ≫ g) = 0 := by
  rw [coneComplex_d f PA PB 0]
  ext ⟨b, a⟩
  change (PB.π.f 0 ≫ g).hom ((PB.complex.d 1 0).hom b + ((φ).f 0).hom a) = 0
  rw [map_add]
  have hb0 : (PB.π.f 0).hom ((PB.complex.d 1 0).hom b) = 0 := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, PB.complex_d_comp_π_f_zero]
    rfl
  have h1 : (PB.π.f 0 ≫ g).hom ((PB.complex.d 1 0).hom b) = 0 :=
    (congrArg g.hom hb0).trans (map_zero g.hom)
  have h2 : (PB.π.f 0 ≫ g).hom (((φ).f 0).hom a) = 0 :=
    (congrArg g.hom (π_comm (f := f) PA PB a)).trans (gf hfg _)
  rw [h1, h2, add_zero]

/-- **The cone of a lifted map of projective resolutions** (Webster, arXiv:1309.3796v3, proof of
Proposition 7.6): for a short exact sequence `0 → A → B → C → 0`, the cone of a lift of
`A → B` to projective resolutions is a projective resolution of `C`. -/
noncomputable def cone (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) : CategoryTheory.ProjectiveResolution C where
  complex := coneComplex f PA PB
  projective n := coneX_projective PA PB n
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨PB.π.f 0 ≫ g, cone_d_comp_π f g PA PB hfg⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine ⟨?_, ?_⟩
        · rw [ShortComplex.moduleCat_exact_iff]
          intro x hx
          change g.hom ((PB.π.f 0).hom x) = 0 at hx
          obtain ⟨y, hy⟩ := (hfg ((PB.π.f 0).hom x)).1 hx
          have hπA : Epi (PA.π.f 0) := inferInstance
          obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hπA y
          obtain ⟨b, hb⟩ := exact_zero PB ((show PB.complex.X 0 from x) - ((φ).f 0).hom a) (by
            rw [map_sub, π_comm, hy, sub_self])
          refine ⟨(b, a), ?_⟩
          change (PB.complex.d 1 0).hom b + ((φ).f 0).hom a = x
          rw [hb, sub_add_cancel]
        · rw [ModuleCat.epi_iff_surjective]
          intro c
          obtain ⟨b, rfl⟩ := hg c
          have hπB : Epi (PB.π.f 0) := inferInstance
          obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hπB b
          exact ⟨x, rfl⟩
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' _ (n + 1) (ChainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (ChainComplex.prev ℕ (n + 1))
          (ChainComplex.next_nat_succ n), ShortComplex.moduleCat_exact_iff]
      rintro ⟨b, a⟩ hx
      cases n with
      | zero =>
        change (PB.complex.d 1 0).hom b + ((φ).f 0).hom a = 0 at hx
        have ha : (PA.π.f 0).hom a = 0 := by
          apply hf
          have hb0 : (PB.π.f 0).hom ((PB.complex.d 1 0).hom b) = 0 := by
            rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, PB.complex_d_comp_π_f_zero]
            rfl
          have hφ : ((φ).f 0).hom a = -(PB.complex.d 1 0).hom b := eq_neg_of_add_eq_zero_right hx
          have h := π_comm (f := f) PA PB a
          rw [hφ, map_neg, hb0, neg_zero] at h
          exact h.symm.trans (map_zero f.hom).symm
        obtain ⟨a', rfl⟩ := exact_zero' PA a ha
        obtain ⟨b', hb'⟩ := exact_succ' PB 0 (b + ((φ).f 1).hom a') (by
          rw [map_add, comm, hx])
        refine ⟨(b', -a'), Prod.ext ?_ ?_⟩
        · change (PB.complex.d 2 1).hom b' + ((φ).f 1).hom (-a') = b
          rw [hb', map_neg, add_neg_cancel_right]
        · change -(PA.complex.d 1 0).hom (-a') = (PA.complex.d 1 0).hom a'
          rw [map_neg, neg_neg]
      | succ n =>
        have hd := coneComplex_d f PA PB
        change ((coneComplex f PA PB).d (n + 2) (n + 1)).hom (b, a) = 0 at hx
        rw [hd] at hx
        have hx1 := congrArg Prod.fst hx
        have hx2 := congrArg Prod.snd hx
        change (PB.complex.d (n + 2) (n + 1)).hom b + ((φ).f (n + 1)).hom a = 0 at hx1
        change -(PA.complex.d (n + 1) n).hom a = 0 at hx2
        obtain ⟨a', rfl⟩ := exact_succ' PA n a (neg_eq_zero.1 hx2)
        obtain ⟨b', hb'⟩ := exact_succ' PB (n + 1) (b + ((φ).f (n + 2)).hom a') (by
          rw [map_add, comm, hx1])
        refine ⟨(b', -a'), ?_⟩
        change ((coneComplex f PA PB).d (n + 3) (n + 2)).hom (b', -a') = (b, _)
        rw [hd]
        refine Prod.ext ?_ ?_
        · change (PB.complex.d (n + 3) (n + 2)).hom b' + ((φ).f (n + 2)).hom (-a') = b
          rw [hb', map_neg, add_neg_cancel_right]
        · change -(PA.complex.d (n + 2) (n + 1)).hom (-a') = (PA.complex.d (n + 2) (n + 1)).hom a'
          rw [map_neg, neg_neg]⟩

theorem cone_X_zero (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) : (cone f g PA PB hf hfg hg).complex.X 0 = PB.complex.X 0 :=
  rfl

theorem cone_X_succ (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (n : ℕ) : (cone f g PA PB hf hfg hg).complex.X (n + 1) =
      ModuleCat.of R (PB.complex.X (n + 1) × PA.complex.X n) :=
  rfl

end ModuleCat.ProjectiveResolution
