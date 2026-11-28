/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Modules coinduced from a corner are right orthogonal to modules killed by the corner

Let `e` be an idempotent of a ring `C` and `δ : D → C` a ring map into the corner `e C e`, so
that `e C` is a `D`–`C` bimodule. For a `D`-module `W`, the coinduced module
`Hom_D(e C, W)` (`CornerCoind`) is a left `C`-module by `(c f)(x) = f(x c)`. It is written as the
additive maps `f : C → W` with `f(e c) = f(c)` and `f(δ(d) c) = d f(c)`, i.e. the maps that
factor through `c ↦ e c` and are `D`-linear.

If `L` is a `C`-module with `e L = 0`, then

* there are no nonzero maps `L → Hom_D(e C, W)` (`CornerCoind.hom_eq_zero`), and
* every extension of `L` by `Hom_D(e C, W)` splits: a map `L → E / F` with `F ≅ Hom_D(e C, W)`
  lifts to `E` (`CornerCoind.exists_lift`).

So `Hom_D(e C, W)` is right orthogonal to `L` (`IsRightOrthogonal`), the module form of
`Ext^{≤ 1}_C(L, Hom_D(e C, W)) = 0`. Right orthogonality passes along finite filtrations: if the
layers of `E ⊇ F_1 ⊇ F_2 ⊇ … ⊇ F_N = 0` are right orthogonal to `L`, then
`Hom_C(L, E) → Hom_C(L, E / F_1)` is bijective (`bijective_mkQ_comp_of_layers`).

This is used for the trace half of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, Lemma 7.19, where the exchange layers of the window filtration are
coinduced from the corner `e_L C̃` and `L e_L = 0`.

## Main definitions

* `CornerCoind e δ W`: the coinduced module `Hom_D(e C, W)`.
* `IsRightOrthogonal C L G`: `Hom(L, G) = 0` and extensions of `L` by `G` split.

## Main results

* `CornerCoind.isRightOrthogonal`.
* `bijective_mkQ_comp_of_layers`.
-/

universe u

namespace Categorification

open Submodule

variable {C : Type u} [Ring C]

/-! ### Right orthogonality -/

/-- **`G` is right orthogonal to `L`**: there are no nonzero maps `L → G`, and every extension
of `L` by `G` splits, i.e. for a submodule `F ≅ G` of any `E`, every map `L → E / F` lifts to
`E`. -/
structure IsRightOrthogonal (C : Type u) [Ring C] (L G : Type u) [AddCommGroup L] [Module C L]
    [AddCommGroup G] [Module C G] : Prop where
  hom_eq_zero : ∀ g : L →ₗ[C] G, g = 0
  exists_lift : ∀ (E : Type u) [AddCommGroup E] [Module C E] (F : Submodule C E)
    (_ : F ≃ₗ[C] G) (g : L →ₗ[C] E ⧸ F), ∃ h : L →ₗ[C] E, F.mkQ ∘ₗ h = g

/-! ### The coinduced module of a corner -/

section Coind

variable (e : C) {D : Type u} [Ring D] (δ : D →+* C) (W : Type u) [AddCommGroup W] [Module D W]

/-- **The coinduced module `Hom_D(e C, W)`**, as the additive maps `f : C → W` that factor
through `c ↦ e c` and are linear over `D` acting through `δ`. -/
def CornerCoind : AddSubgroup (C →+ W) where
  carrier := {f | (∀ c, f (e * c) = f c) ∧ ∀ d c, f (δ d * c) = d • f c}
  add_mem' {f g} hf hg :=
    ⟨fun c => by simp only [AddMonoidHom.add_apply, hf.1, hg.1],
      fun d c => by simp only [AddMonoidHom.add_apply, hf.2, hg.2, smul_add]⟩
  zero_mem' := ⟨fun _ => rfl, fun d _ => (smul_zero d).symm⟩
  neg_mem' {f} hf :=
    ⟨fun c => by simp only [AddMonoidHom.neg_apply, hf.1],
      fun d c => by simp only [AddMonoidHom.neg_apply, hf.2, smul_neg]⟩

variable {e δ W}

namespace CornerCoind

theorem map_e (f : CornerCoind e δ W) (c : C) : f.1 (e * c) = f.1 c := f.2.1 c

theorem map_δ (f : CornerCoind e δ W) (d : D) (c : C) : f.1 (δ d * c) = d • f.1 c := f.2.2 d c

@[ext]
theorem ext {f g : CornerCoind e δ W} (h : ∀ c, f.1 c = g.1 c) : f = g :=
  Subtype.ext (AddMonoidHom.ext h)

/-- `(c f)(x) = f(x c)`. -/
instance : SMul C (CornerCoind e δ W) where
  smul c f := ⟨f.1.comp (AddMonoidHom.mulRight c),
    fun x => by simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulRight, mul_assoc,
      map_e f],
    fun d x => by simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulRight, mul_assoc,
      map_δ f]⟩

theorem smul_apply (c : C) (f : CornerCoind e δ W) (x : C) : (c • f).1 x = f.1 (x * c) := rfl

instance : Module C (CornerCoind e δ W) where
  one_smul f := ext fun x => by rw [smul_apply, mul_one]
  mul_smul c c' f := ext fun x => by rw [smul_apply, smul_apply, smul_apply, mul_assoc]
  smul_zero c := ext fun x => rfl
  smul_add c f g := ext fun x => rfl
  add_smul c c' f := ext fun x => by
    change f.1 (x * (c + c')) = f.1 (x * c) + f.1 (x * c')
    rw [mul_add, map_add]
  zero_smul f := ext fun x => by
    change f.1 (x * 0) = 0
    rw [mul_zero, map_zero]

variable (he : IsIdempotentElem e) (hδl : ∀ d, e * δ d = δ d) (hδr : ∀ d, δ d * e = δ d)
  {L : Type u} [AddCommGroup L] [Module C L] (hL : ∀ l : L, e • l = 0)

include hL in
/-- **No maps from a module killed by `e` to a coinduced module.** -/
theorem hom_eq_zero (g : L →ₗ[C] CornerCoind e δ W) : g = 0 := by
  ext l c
  have h1 : (g l).1 c = (g (c • l)).1 1 := by
    rw [map_smul g c l, smul_apply, one_mul]
  have h2 : (g (c • l)).1 1 = (g (e • c • l)).1 1 := by
    rw [map_smul g e (c • l), smul_apply, one_mul, ← map_e (g (c • l)) 1, mul_one]
  rw [h1, h2, hL, map_zero]
  rfl

section Lift

variable {E : Type u} [AddCommGroup E] [Module C E] (F : Submodule C E)
  (eF : F ≃ₗ[C] CornerCoind e δ W) (g : L →ₗ[C] E ⧸ F)

/-- The preimage of the image of `g`. -/
def liftDomain : Submodule C E := (LinearMap.range g).comap F.mkQ

include hL in
theorem mem_of_mem_liftDomain {x : E} (hx : x ∈ liftDomain F g) (c : C) : (e * c) • x ∈ F := by
  obtain ⟨l, hl⟩ := hx
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul, ← hl, ← map_smul,
    mul_smul, hL, map_zero]

/-- The retraction of `liftDomain F g` onto `F`, at an element: `c ↦ eF((e c) x)(1)`. -/
def retractFun (x : liftDomain F g) : C →+ W where
  toFun c := (eF ⟨(e * c) • x.1, mem_of_mem_liftDomain hL F g x.2 c⟩).1 1
  map_zero' := by
    simp only [mul_zero, zero_smul]
    rw [show (⟨0, _⟩ : F) = 0 from rfl, map_zero]
    rfl
  map_add' c c' := by
    simp only [mul_add, add_smul]
    rw [show (⟨(e * c) • x.1 + (e * c') • x.1, _⟩ : F) =
      ⟨(e * c) • x.1, mem_of_mem_liftDomain hL F g x.2 c⟩ +
        ⟨(e * c') • x.1, mem_of_mem_liftDomain hL F g x.2 c'⟩ from rfl, map_add]
    rfl

theorem retractFun_apply (x : liftDomain F g) (c : C) :
    retractFun hL F eF g x c = (eF ⟨(e * c) • x.1, mem_of_mem_liftDomain hL F g x.2 c⟩).1 1 :=
  rfl

include he hδl hδr in
theorem retractFun_mem (x : liftDomain F g) :
    retractFun hL F eF g x ∈ CornerCoind e δ W := by
  refine ⟨fun c => ?_, fun d c => ?_⟩
  · rw [retractFun_apply, retractFun_apply]
    simp only [← mul_assoc, he.eq]
  · rw [retractFun_apply, retractFun_apply]
    have hm : (⟨(e * (δ d * c)) • x.1, mem_of_mem_liftDomain hL F g x.2 _⟩ : F) =
        δ d • ⟨(e * c) • x.1, mem_of_mem_liftDomain hL F g x.2 c⟩ := by
      apply Subtype.ext
      change (e * (δ d * c)) • x.1 = δ d • (e * c) • x.1
      rw [← mul_smul, ← mul_assoc, hδl, ← mul_assoc, hδr]
    rw [hm, map_smul, smul_apply, one_mul, ← mul_one (δ d), map_δ]

/-- **The retraction** `liftDomain F g → Hom_D(e C, W)`. -/
def retract : liftDomain F g →ₗ[C] CornerCoind e δ W where
  toFun x := ⟨retractFun hL F eF g x, retractFun_mem he hδl hδr hL F eF g x⟩
  map_add' x y := ext fun c => by
    change retractFun hL F eF g (x + y) c = retractFun hL F eF g x c + retractFun hL F eF g y c
    rw [retractFun_apply, retractFun_apply, retractFun_apply]
    rw [show (⟨(e * c) • (x + y).1, mem_of_mem_liftDomain hL F g (x + y).2 c⟩ : F) =
      ⟨(e * c) • x.1, mem_of_mem_liftDomain hL F g x.2 c⟩ +
        ⟨(e * c) • y.1, mem_of_mem_liftDomain hL F g y.2 c⟩ from
      Subtype.ext (smul_add _ _ _), map_add]
    rfl
  map_smul' c' x := ext fun c => by
    change retractFun hL F eF g (c' • x) c = retractFun hL F eF g x (c * c')
    rw [retractFun_apply, retractFun_apply]
    congr 3
    refine Subtype.ext ?_
    change (e * c) • c' • x.1 = (e * (c * c')) • x.1
    rw [← mul_smul, mul_assoc]

theorem retract_apply_of_mem (x : liftDomain F g) (hx : x.1 ∈ F) :
    retract he hδl hδr hL F eF g x = eF ⟨x.1, hx⟩ := ext fun c => by
  change (eF ⟨(e * c) • x.1, _⟩).1 1 = (eF ⟨x.1, hx⟩).1 c
  rw [show (⟨(e * c) • x.1, mem_of_mem_liftDomain hL F g x.2 c⟩ : F) =
    (e * c) • ⟨x.1, hx⟩ from rfl, map_smul, smul_apply, one_mul, map_e]

/-- The section on `liftDomain F g`: `x ↦ x - eF⁻¹(r(x))`, which kills `F`. -/
def sect : liftDomain F g →ₗ[C] E :=
  (liftDomain F g).subtype - F.subtype ∘ₗ eF.symm.toLinearMap ∘ₗ retract he hδl hδr hL F eF g

theorem sect_eq_zero_of_mem (x : liftDomain F g) (hx : x.1 ∈ F) :
    sect he hδl hδr hL F eF g x = 0 := by
  change x.1 - (eF.symm (retract he hδl hδr hL F eF g x)).1 = 0
  rw [retract_apply_of_mem he hδl hδr hL F eF g x hx, LinearEquiv.symm_apply_apply, sub_self]

theorem mkQ_sect (x : liftDomain F g) : F.mkQ (sect he hδl hδr hL F eF g x) = F.mkQ x.1 := by
  change F.mkQ (x.1 - (eF.symm _).1) = _
  rw [map_sub, Submodule.mkQ_apply F (eF.symm _).1,
    (Submodule.Quotient.mk_eq_zero F).2 (eF.symm _).2, sub_zero]

theorem exists_preimage (l : L) : ∃ x : liftDomain F g, F.mkQ x.1 = g l := by
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective F (g l)
  exact ⟨⟨x, l, hx.symm⟩, hx⟩

include he hδl hδr hL eF in
/-- **Every extension of `L` by `Hom_D(e C, W)` splits.** -/
theorem exists_lift : ∃ h : L →ₗ[C] E, F.mkQ ∘ₗ h = g := by
  classical
  choose pre hpre using exists_preimage F g
  have key : ∀ (x y : liftDomain F g), F.mkQ x.1 = F.mkQ y.1 →
      sect he hδl hδr hL F eF g x = sect he hδl hδr hL F eF g y := fun x y hxy => by
    rw [← sub_eq_zero, ← map_sub]
    refine sect_eq_zero_of_mem he hδl hδr hL F eF g _ ?_
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    change F.mkQ (x.1 - y.1) = 0
    rw [map_sub, hxy, sub_self]
  refine ⟨{ toFun := fun l => sect he hδl hδr hL F eF g (pre l)
            map_add' := fun l l' => ?_
            map_smul' := fun c l => ?_ }, ?_⟩
  · rw [← map_add]
    refine key _ _ ?_
    change F.mkQ (pre (l + l')).1 = F.mkQ ((pre l).1 + (pre l').1)
    rw [hpre, map_add, map_add, hpre, hpre]
  · rw [RingHom.id_apply, ← map_smul]
    refine key _ _ ?_
    change F.mkQ (pre (c • l)).1 = F.mkQ (c • (pre l).1)
    rw [hpre, map_smul, map_smul, hpre]
  · refine LinearMap.ext fun l => ?_
    change F.mkQ (sect he hδl hδr hL F eF g (pre l)) = g l
    rw [mkQ_sect, hpre]

end Lift

include he hδl hδr hL in
/-- **`Hom_D(e C, W)` is right orthogonal to every module killed by `e`.** -/
theorem isRightOrthogonal : IsRightOrthogonal C L (CornerCoind e δ W) where
  hom_eq_zero := hom_eq_zero hL
  exists_lift _ _ _ F eF g := exists_lift he hδl hδr hL F eF g

end CornerCoind

end Coind

/-! ### Dévissage along a finite filtration -/

section Filtration

variable {L E : Type u} [AddCommGroup L] [Module C L] [AddCommGroup E] [Module C E]
  (Fl : ℕ → Submodule C E) (hanti : ∀ m, Fl (m + 1) ≤ Fl m) (N : ℕ) (hN : Fl N = ⊥)
  (hlay : ∀ m, 1 ≤ m → IsRightOrthogonal C L ((Fl m).map (Fl (m + 1)).mkQ))

include hanti hN hlay in
theorem eq_zero_of_le_filtration :
    ∀ d m, 1 ≤ m → N ≤ m + d → ∀ h : L →ₗ[C] E, LinearMap.range h ≤ Fl m → h = 0 := by
  intro d
  induction d with
  | zero =>
    intro m _ hm h hh
    have hle : Fl m ≤ Fl N := (antitone_nat_of_succ_le hanti) hm
    rw [hN] at hle
    exact LinearMap.range_eq_bot.1 (le_bot_iff.1 (hh.trans hle))
  | succ d ih =>
    intro m hm hmd h hh
    refine ih (m + 1) (by omega) (by omega) h ?_
    have h0 := (hlay m hm).hom_eq_zero
      (((Fl (m + 1)).mkQ ∘ₗ h).codRestrict ((Fl m).map (Fl (m + 1)).mkQ)
        fun l => ⟨h l, hh ⟨l, rfl⟩, rfl⟩)
    rintro _ ⟨l, rfl⟩
    have := congrArg Subtype.val (LinearMap.congr_fun h0 l)
    exact (Submodule.Quotient.mk_eq_zero _).1 this

include hanti hN hlay in
theorem exists_lift_of_filtration :
    ∀ d m, 1 ≤ m → N ≤ m + d → ∀ g : L →ₗ[C] E ⧸ Fl m, ∃ h : L →ₗ[C] E, (Fl m).mkQ ∘ₗ h = g := by
  intro d
  induction d with
  | zero =>
    intro m _ hm g
    have hb : Fl m = ⊥ := le_bot_iff.1 (hN ▸ (antitone_nat_of_succ_le hanti) hm)
    refine ⟨(Submodule.quotEquivOfEqBot _ hb).toLinearMap ∘ₗ g, LinearMap.ext fun l => ?_⟩
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ (g l)
    change (Fl m).mkQ (Submodule.quotEquivOfEqBot _ hb (g l)) = g l
    rw [← hx]
    exact congrArg (Fl m).mkQ (Submodule.quotEquivOfEqBot_apply_mk _ hb x)
  | succ d ih =>
    intro m hm hmd g
    let ψ := Submodule.quotientQuotientEquivQuotient (Fl (m + 1)) (Fl m) (hanti m)
    obtain ⟨h₁, hh₁⟩ := (hlay m hm).exists_lift _ _ (LinearEquiv.refl _ _)
      (ψ.symm.toLinearMap ∘ₗ g)
    obtain ⟨h, hh⟩ := ih (m + 1) (by omega) (by omega) h₁
    refine ⟨h, LinearMap.ext fun l => ?_⟩
    have e1 := LinearMap.congr_fun hh₁ l
    have e2 := LinearMap.congr_fun hh l
    change (Fl m).mkQ (h l) = g l
    change ((Fl m).map (Fl (m + 1)).mkQ).mkQ (h₁ l) = ψ.symm (g l) at e1
    change (Fl (m + 1)).mkQ (h l) = h₁ l at e2
    rw [← ψ.apply_symm_apply (g l), ← e1, ← e2]
    rfl

include hanti hN hlay in
/-- **Dévissage**: if the layers `F_m / F_{m+1}` (`m ≥ 1`) of a finite filtration
`E ⊇ F_1 ⊇ F_2 ⊇ … ⊇ F_N = 0` are right orthogonal to `L`, then composing with `E → E / F_1` is
a bijection `Hom_C(L, E) ≅ Hom_C(L, E / F_1)`. -/
theorem bijective_mkQ_comp_of_layers :
    Function.Bijective fun h : L →ₗ[C] E => (Fl 1).mkQ ∘ₗ h := by
  refine ⟨fun h h' hhh => ?_, fun g => exists_lift_of_filtration Fl hanti N hN hlay N 1
    le_rfl (by omega) g⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_le_filtration Fl hanti N hN hlay N 1 le_rfl (by omega) _ ?_
  rintro _ ⟨l, rfl⟩
  have := LinearMap.congr_fun hhh l
  change (Fl 1).mkQ (h l) = (Fl 1).mkQ (h' l) at this
  change h l - h' l ∈ Fl 1
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
  exact sub_eq_zero.2 this

end Filtration

end Categorification
