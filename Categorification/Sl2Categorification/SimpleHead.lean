/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.SimpleSocle
import Categorification.TwoRep.Coop

/-!
# The head of `E U` for a simple object `U`

Chuang–Rouquier, arXiv:math/0407205v2, Proposition 5.20 (b), head part, for `i = 1`: for `U`
simple, any two simple quotients of `E U` are isomorphic compatibly with the quotient maps
(`WeakSl2.exists_iso_of_epi_E`), so the head of `E U` is simple; likewise for `F U`
(`WeakSl2.exists_iso_of_epi_F`). Chuang–Rouquier say that the proof for the head is similar to
the one for the socle; we obtain it from the socle statement
(`WeakSl2.subobject_mk_eq_of_simple`) in the opposite category, with the opposite
categorification (`WeakSl2.op`) and the opposite nil-Hecke action (`NilHeckeData.op`), whose
dot and crossing are the opposites of the original ones (Chuang–Rouquier, §5.1.1).

This is the input of Webster, arXiv:1309.3796v2, Proposition 5.12 (the heads of `E_i L` and
`F_i L` are simple for a simple module `L`).

## Main results

* `NilHecke.idemNH_one`: the idempotent `e_1` of `NH_1` is `1`, so `E^{(1)} = E`
  (`NilHeckeData.isIso_divι_one`).
* `NilHeckeData.op`: the nil-Hecke action on `E.op` in the opposite category.
* `WeakSl2.exists_iso_of_epi_E`, `WeakSl2.exists_iso_of_epi_F`: **Chuang–Rouquier,
  Proposition 5.20 (b)**, head part, for `i = 1`.
-/

namespace Categorification.NilHecke

variable (k : Type*) [Field k]

/-- The idempotent `e_1 = x^δ ∂_{w_0}` of `NH_1` is the identity. -/
theorem idemNH_one : idemNH k 1 = 1 := by
  have hx : xDelta (k := k) (m := 1) 1 = 1 := by simp [xDelta]
  simp [idemNH, hx, w0Word]

end Categorification.NilHecke

namespace Categorification.Sl2

open CategoryTheory Limits Opposite Module

universe v u

variable {C : Type u} [Category.{v} C]

namespace NilHeckeData

section DivOne

variable [Abelian C] {E : C ⥤ C} (D : NilHeckeData E) [E.Additive] (k : Type*) [Field k]
  [Linear k C]

/-- `E^{(1)} M ⟶ E M` is an isomorphism. -/
instance isIso_divι_one (M : C) : IsIso (D.divι k 1 M) := by
  have h1 : (⟨NilHecke.idemNH k 1, NilHecke.idemNH_mem⟩ : NilHecke.nilHecke k 1) = 1 :=
    Subtype.ext (NilHecke.idemNH_one k)
  have hγ : (D.γ (k := k) 1 ⟨NilHecke.idemNH k 1, NilHecke.idemNH_mem⟩).app M = 𝟙 _ := by
    rw [h1, map_one]; rfl
  have : Epi ((D.γ (k := k) 1 ⟨NilHecke.idemNH k 1, NilHecke.idemNH_mem⟩).app M) := by
    rw [hγ]; infer_instance
  have : Epi (D.divι k 1 M) := by
    unfold divι
    exact epi_of_epi_fac (image.fac _)
  exact isIso_of_mono_of_epi _

end DivOne

section Op

variable [Preadditive C] {E : C ⥤ C} (D : NilHeckeData E)

/-- The nil-Hecke action on `E.op` in the opposite category: the dot and the crossing are the
opposites of those of `E` (Chuang–Rouquier, §5.1.1). -/
def op : NilHeckeData E.op where
  X := NatTrans.op D.X
  T := (NatTrans.op D.T : (E ⋙ E).op ⟶ (E ⋙ E).op)
  T_mul_T := by
    refine NatTrans.ext (funext fun M ↦ ?_); apply Quiver.Hom.unop_inj
    exact congrArg (fun a : End (E ⋙ E) ↦ a.app (unop M)) D.T_mul_T
  braid := by
    refine NatTrans.ext (funext fun M ↦ ?_); apply Quiver.Hom.unop_inj
    have := congrArg (fun a : End ((E ⋙ E) ⋙ E) ↦ a.app (unop M)) D.braid
    simpa [End.mul_def, wR, wL₂] using this
  x_T_sub := by
    have hs : ∀ (a b : End (E.op ⋙ E.op)) (M : Cᵒᵖ), (a - b).app M = a.app M - b.app M :=
      fun _ _ _ ↦ rfl
    have hs' : ∀ (a b : End (E ⋙ E)) (M : C), (a - b).app M = a.app M - b.app M :=
      fun _ _ _ ↦ rfl
    refine NatTrans.ext (funext fun M ↦ ?_); apply Quiver.Hom.unop_inj
    have := congrArg (fun a : End (E ⋙ E) ↦ a.app (unop M)) D.T_x_sub
    simpa [hs, hs', End.mul_def, wR, wL, unop_sub, NatTrans.comp_app, NatTrans.op_app,
      unop_comp, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.op_map,
      Quiver.Hom.unop_op] using this
  T_x_sub := by
    have hs : ∀ (a b : End (E.op ⋙ E.op)) (M : Cᵒᵖ), (a - b).app M = a.app M - b.app M :=
      fun _ _ _ ↦ rfl
    have hs' : ∀ (a b : End (E ⋙ E)) (M : C), (a - b).app M = a.app M - b.app M :=
      fun _ _ _ ↦ rfl
    refine NatTrans.ext (funext fun M ↦ ?_); apply Quiver.Hom.unop_inj
    have := congrArg (fun a : End (E ⋙ E) ↦ a.app (unop M)) D.x_T_sub
    simpa [hs, hs', End.mul_def, wR, wL, unop_sub, NatTrans.comp_app, NatTrans.op_app,
      unop_comp, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.op_map,
      Quiver.Hom.unop_op] using this

/-- The opposite of a nilpotent endomorphism is nilpotent. -/
theorem isNilpotent_op {X : C} {f : End X} (hf : IsNilpotent f) :
    IsNilpotent (R := End (Opposite.op X)) f.op := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  have : ∀ p : ℕ, (show End (Opposite.op X) from f.op) ^ p = (f ^ p).op := by
    intro p
    induction p with
    | zero => rfl
    | succ p ih =>
      rw [pow_succ, ih, pow_succ', End.mul_def, End.mul_def, op_comp]
  rw [this, hn]; rfl

end Op

end NilHeckeData

namespace WeakSl2

variable [Abelian C]

/-- The opposite of an Artinian object is Noetherian. -/
theorem isNoetherianObject_op (X : C) [IsArtinianObject X] :
    IsNoetherianObject (Opposite.op X) := by
  let e := Abelian.subobjectIsoSubobjectOp X
  let φ : Subobject (Opposite.op X) → Subobject X := fun y ↦ e.symm (OrderDual.toDual y)
  have hwf : WellFoundedGT (Subobject (Opposite.op X)) :=
    Subrelation.wf (fun {a b} h ↦ show φ a < φ b from
      e.symm.lt_iff_lt.mpr (OrderDual.toDual_lt_toDual.mpr h)) (InvImage.wf φ wellFounded_lt)
  exact ⟨hwf⟩

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V] (A : WeakSl2 C ι V)
variable [∀ X : C, IsArtinianObject X] [∀ X : C, IsNoetherianObject X]
variable [A.E.Additive] [A.F.Additive] (DE : NilHeckeData A.E) (DF : NilHeckeData A.F)
variable (k : Type*) [Field k] [Linear k C] [A.E.Linear k] [A.F.Linear k]

/-- **Chuang–Rouquier, Proposition 5.20 (b)**, head part, for `E` and `i = 1`: for `U` simple,
any two simple quotients of `E U` are isomorphic compatibly with the quotient maps, so the head
of `E U` is simple.

The hypotheses `hX`, `hXF` are the nilpotence of the dots on `E` and `F` (Chuang–Rouquier,
§5.2.1, eigenvalue `0`), and `hEnd` is the condition `End(S) = k` for simple `S`. -/
theorem exists_iso_of_epi_E
    (hX : ∀ M, IsNilpotent (R := End (A.E.obj M)) (DE.X.app M))
    (hXF : ∀ M, IsNilpotent (R := End (A.F.obj M)) (DF.X.app M))
    (hEnd : ∀ S : C, Simple S → finrank k (S ⟶ S) = 1)
    {U : C} (hU : Simple U) {S₁ S₂ : C} [hS₁ : Simple S₁] [Simple S₂]
    (q₁ : A.E.obj U ⟶ S₁) (q₂ : A.E.obj U ⟶ S₂) [Epi q₁] [Epi q₂] :
    ∃ e : S₁ ≅ S₂, q₁ ≫ e.hom = q₂ := by
  have : ∀ X : Cᵒᵖ, IsArtinianObject X := fun X ↦ isArtinianObject_op X.unop
  have : ∀ X : Cᵒᵖ, IsNoetherianObject X := fun X ↦ isNoetherianObject_op X.unop
  -- `1 ≤ h₊([U])`
  have hi : 1 ≤ hPlus A.op.e (A.op.cls (Opposite.op U)) := by
    have hpos := A.repr_cls_pos_of_mono_of_epi q₁ (𝟙 S₁)
    rw [A.cls_E, A.cls_simple U hU] at hpos
    have := A.posBasis.hPlus_lt_of_e hpos.ne'
    change 1 ≤ hPlus A.e (A.cls U)
    rw [A.cls_simple U hU]; omega
  have hEnd' : ∀ S : Cᵒᵖ, Simple S → finrank k (S ⟶ S) = 1 := fun S hS ↦ by
    rcases S with ⟨S⟩
    exact (TwoRep.finrank_op_hom k S S).trans (hEnd S ((simple_op_iff S).mp hS))
  have : Simple (Opposite.op S₁) := (simple_op_iff _).mpr inferInstance
  have : Simple (Opposite.op S₂) := (simple_op_iff _).mpr inferInstance
  have : A.op.E.Additive := (inferInstance : A.E.op.Additive)
  have : A.op.F.Additive := (inferInstance : A.F.op.Additive)
  have : A.op.E.Linear k := (inferInstance : A.E.op.Linear k)
  have : A.op.F.Linear k := (inferInstance : A.F.op.Linear k)
  let DE' : NilHeckeData A.op.E := DE.op
  let DF' : NilHeckeData A.op.F := DF.op
  let ι₁ := DE'.divι k 1 (Opposite.op U)
  have : IsIso ι₁ := NilHeckeData.isIso_divι_one DE' k _
  let p₁ : Opposite.op S₁ ⟶ (Epow A.op.E 1).obj (Opposite.op U) := q₁.op
  let p₂ : Opposite.op S₂ ⟶ (Epow A.op.E 1).obj (Opposite.op U) := q₂.op
  have : Mono p₁ := (inferInstance : Mono q₁.op)
  have : Mono p₂ := (inferInstance : Mono q₂.op)
  let φ₁ : Opposite.op S₁ ⟶ DE'.divObj k 1 (Opposite.op U) := p₁ ≫ inv ι₁
  let φ₂ : Opposite.op S₂ ⟶ DE'.divObj k 1 (Opposite.op U) := p₂ ≫ inv ι₁
  have : Mono φ₁ := mono_comp _ _
  have : Mono φ₂ := mono_comp _ _
  have h := A.op.subobject_mk_eq_of_simple DE' DF' k
    (fun M ↦ NilHeckeData.isNilpotent_op (hX M.unop))
    (fun M ↦ NilHeckeData.isNilpotent_op (hXF M.unop)) hEnd'
    ((simple_op_iff U).mpr hU) hi φ₁ φ₂
  set g := Subobject.isoOfMkEqMk φ₁ φ₂ h
  have hg : g.hom ≫ q₂.op = q₁.op := by
    have h' : g.hom ≫ φ₂ = φ₁ := Subobject.ofMkLEMk_comp _
    have h'' : g.hom ≫ p₂ = p₁ := by
      simpa [φ₁, φ₂] using congrArg (· ≫ ι₁) h'
    exact h''
  refine ⟨g.unop.symm, ?_⟩
  change q₁ ≫ g.inv.unop = q₂
  rw [← Quiver.Hom.unop_op q₁, ← hg]
  change (g.inv ≫ g.hom ≫ q₂.op).unop = q₂
  rw [Iso.inv_hom_id_assoc]; rfl

/-- **Chuang–Rouquier, Proposition 5.20 (b)**, head part, for `F` and `i = 1`: for `U` simple,
the head of `F U` is simple. -/
theorem exists_iso_of_epi_F
    (hX : ∀ M, IsNilpotent (R := End (A.E.obj M)) (DE.X.app M))
    (hXF : ∀ M, IsNilpotent (R := End (A.F.obj M)) (DF.X.app M))
    (hEnd : ∀ S : C, Simple S → finrank k (S ⟶ S) = 1)
    {U : C} (hU : Simple U) {S₁ S₂ : C} [Simple S₁] [Simple S₂]
    (q₁ : A.F.obj U ⟶ S₁) (q₂ : A.F.obj U ⟶ S₂) [Epi q₁] [Epi q₂] :
    ∃ e : S₁ ≅ S₂, q₁ ≫ e.hom = q₂ :=
  A.swap.exists_iso_of_epi_E DF DE k hXF hX hEnd hU q₁ q₂

end WeakSl2

end Categorification.Sl2
