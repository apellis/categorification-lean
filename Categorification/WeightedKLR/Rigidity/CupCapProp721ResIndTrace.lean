/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721ResIndCounit

/-!
# The trace of `𝔈_i ⊣ 𝔉_i` on the matrix rings of the categorical action

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31,
as used in §7.3, proof of Proposition 7.21. The adjunction `Res_φ ⊣ Ind_φ` along the matrix map
`φ` of a functor `F` (`KLR.Diagram.MatEnd.resIndAdjunction`), built from `F' ⊣ E` and
`E ⊣ F'` on completed additive envelopes, has an explicit counit: a generator `m` of
`Res (Ind N)` goes to the evaluation `HomTensor.eval` of `E ⊣ F'` at the generator
`β = (F' ⊣ E)(sect)` of `Res` (`KLR.Diagram.MatEnd.resIndAdjunction_counit_app_apply`). On a
generator `z ⊗ n` this is `(β ≫ E z ≫ ε'_{G_X}) • n`
(`KLR.Diagram.MatEnd.resIndAdjunction_counit_app_mk_tmul`): the trace of
`CupCap.resIndCounit_app_mk_tmul` is `z ↦ β ≫ E z ≫ ε'`, the closure of the new strand by the
unit of `F' ⊣ E` and the counit of `E ⊣ F'` (for Webster's functors: a rightward cup and the
leftward cap of Cautis–Lauda's `U_Q(g)`, arXiv:1111.1431v3, Definition 1.1, attached at the right,
as in Webster's description of the action of the 2-morphisms after Theorem 4.31).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Idempotents MulOpposite Categorification.InductionAlong

namespace Categorification.KLR.Diagram.MatEnd

universe v w

variable {C : Type*} [Category.{v} C] [Preadditive C] {D : Type*} [Category.{v} D]
  [Preadditive D] {ι κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) [F.Additive] {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))
  {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} [E.Additive] (adj : mapKaroubi F.mapMat_ ⊣ E)
  (adj' : E ⊣ mapKaroubi F.mapMat_)
  {J : Type*} [Fintype J]
  (π : J → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι' : J → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)

attribute [local instance] HomTensor.bimodule

/-- **The counit of `Res ⊣ Ind` along the matrix map** (Webster, arXiv:1309.3796v3,
Theorem 4.31): at a right `MatEnd X`-module `N`, a generator `m` of `Res (Ind N)` goes to the
evaluation of `E ⊣ F'` at `β = (F' ⊣ E)(sect)` on `Ind N ≅ (G_Y ⟶ F' G_X) ⊗ N`. -/
theorem resIndAdjunction_counit_app_apply (N : ModuleCat.{max w v} (MatEnd X)ᵐᵒᵖ)
    (m : Res (mapEmbOp F he h) (Ind N (mapEmbOp F he h))) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    ((resIndAdjunction F he h adj adj' π ι' hπ).counit.app N).hom m =
      HomTensor.eval ℤ adj' _ _ (resRegularHom F he h adj (resUnit _))
        (indModuleEquiv F he h N m.val) :=
  rfl

/-- **The trace of `Res ⊣ Ind` along the matrix map on generators** (Webster,
arXiv:1309.3796v3, Theorem 4.31): `ε_N (z ⊗ n) = (β ≫ E z ≫ ε'_{G_X}) • n`, with
`β = (F' ⊣ E)(sect)` and `ε'` the counit of `E ⊣ F'`. -/
theorem resIndAdjunction_counit_app_mk_tmul (N : ModuleCat.{max w v} (MatEnd X)ᵐᵒᵖ)
    (z : Corner (mapEmbOp F he h)) (n : N)
    (hz : (mapEmbOp F he h) 1 • (Ind.tmul z n : Ind N (mapEmbOp F he h)) = Ind.tmul z n) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) N
    ((resIndAdjunction F he h adj adj' π ι' hπ).counit.app N).hom (Res.mk (Ind.tmul z n) hz) =
      (op (resRegularHom F he h adj (resUnit _) ≫ E.map (karoubiCorner F he h z) ≫
        adj'.counit.app ((toKaroubi _).obj (familySum X))) :
          (End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ) • n :=
  rfl

end Categorification.KLR.Diagram.MatEnd
