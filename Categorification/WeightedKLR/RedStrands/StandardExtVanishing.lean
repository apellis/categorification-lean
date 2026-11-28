/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardStratificationStd
import Categorification.WeightedKLR.RedStrands.LeftStandardSupport
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Ext between standard modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.26 (the semi-orthogonal decomposition): `Ext^•(S_t, S_s) = 0` whenever the root
function of `t` is strictly above that of `s`, and the higher `Ext`s vanish when the two root
functions are equal.

We prove slightly more, by Webster's argument: `Extⁿ(S_t, S_s) = 0` for all `n` as soon as `t`
is not below `s` in Webster's preorder (`subsingleton_ext_stdModule_of_not_stendhalLE`), and
`Ext^{n+1}(S_t, S_s) = 0` as soon as `s` is below `t` (`subsingleton_ext_succ_stdModule`). The
proof is a descending induction on `t` through `0 → U_t → T^λ e(t) → S_t → 0`: the kernel `U_t`
is filtered by standards strictly above `t` (Corollary 5.22), the projective `T^λ e(t)` has no
higher `Ext`, and it has no maps to `S_s` unless `t ≤ s`, since `e(t)` annihilates `S_s`
(`seqIdem_smul_leftStandard_eq_zero_of_not_stendhalLE`).

## Main results

* `ModuleFiltration.HasFiltration.subsingleton_ext`: `Ext` out of a filtered module vanishes if
  it vanishes out of every subquotient.
* `Stendhal.subsingleton_ext_stdModule_of_not_stendhalLE`,
  `Stendhal.subsingleton_ext_succ_stdModule`, for Rouquier parameters.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe w

namespace Categorification

open CategoryTheory Limits Abelian

section ExtSequences

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]

/-- `Ext` out of isomorphic objects. -/
theorem subsingleton_ext_of_iso {X X' : C} (e : X ≅ X') (Y : C) (n : ℕ)
    [Subsingleton (Ext.{w} X' Y n)] : Subsingleton (Ext.{w} X Y n) :=
  ⟨fun a b => by
    have h : ∀ x : Ext.{w} X Y n, x = (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add n))
        (zero_add n) := fun x => by
      rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
    rw [h a, h b, Subsingleton.elim ((Ext.mk₀ e.inv).comp a (zero_add n))
      ((Ext.mk₀ e.inv).comp b (zero_add n))]⟩

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

include hS

/-- In a short exact sequence, `Ext` out of the middle term vanishes if it vanishes out of the
outer terms. -/
theorem subsingleton_ext_X₂_of_shortExact (n : ℕ)
    [Subsingleton (Ext.{w} S.X₁ Y n)] [Subsingleton (Ext.{w} S.X₃ Y n)] :
    Subsingleton (Ext.{w} S.X₂ Y n) :=
  ⟨fun a b => by
    have h : ∀ x : Ext.{w} S.X₂ Y n, x = 0 := fun x => by
      obtain ⟨x₃, hx₃⟩ := Ext.contravariant_sequence_exact₂ hS Y x (Subsingleton.elim _ _)
      rw [← hx₃, Subsingleton.elim x₃ 0, Ext.comp_zero]
    rw [h a, h b]⟩

/-- In a short exact sequence, `Ext^{n+1}` out of the last term vanishes if `Extⁿ` out of the
first and `Ext^{n+1}` out of the middle term vanish. -/
theorem subsingleton_ext_X₃_succ_of_shortExact (n : ℕ)
    [Subsingleton (Ext.{w} S.X₁ Y n)] [Subsingleton (Ext.{w} S.X₂ Y (n + 1))] :
    Subsingleton (Ext.{w} S.X₃ Y (n + 1)) :=
  ⟨fun a b => by
    have h : ∀ x : Ext.{w} S.X₃ Y (n + 1), x = 0 := fun x => by
      obtain ⟨x₁, hx₁⟩ := Ext.contravariant_sequence_exact₃ hS Y x (Subsingleton.elim _ _)
        (add_comm 1 n)
      rw [← hx₁, Subsingleton.elim x₁ 0, Ext.comp_zero]
    rw [h a, h b]⟩

/-- In a short exact sequence, `Ext⁰` out of the last term vanishes if the middle term has no
maps to `Y`. -/
theorem subsingleton_ext_X₃_zero_of_shortExact [Subsingleton (S.X₂ ⟶ Y)] :
    Subsingleton (Ext.{w} S.X₃ Y 0) :=
  ⟨fun a b => Ext.homEquiv₀.injective (by
    have := hS.epi_g
    exact (cancel_epi S.g).1 (Subsingleton.elim _ _))⟩

end ExtSequences

namespace ModuleFiltration

variable {A : Type} [Ring A] [HasExt.{w} (ModuleCat.{0} A)] {ι : Type*}
  {L : ι → ModuleCat.{0} A}

/-- `Ext` out of a filtered module vanishes if it vanishes out of every subquotient of the
filtration. -/
theorem HasFiltration.subsingleton_ext {m : List ι} {X : ModuleCat.{0} A}
    (h : HasFiltration L m X) (Y : ModuleCat.{0} A) (n : ℕ)
    (hL : ∀ c ∈ m, Subsingleton (Ext.{w} (L c) Y n)) : Subsingleton (Ext.{w} X Y n) := by
  induction h with
  | @zero X hX =>
    have : HasProjectiveDimensionLT X 0 :=
      (ModuleCat.isZero_of_subsingleton X).hasProjectiveDimensionLT_zero
    exact HasProjectiveDimensionLT.subsingleton X 0 n (Nat.zero_le n) Y
  | @cons X₁ X₂ X₃ f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    have := ih fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')
    have := hL c List.mem_cons_self
    have : Subsingleton (Ext.{w} X₃ Y n) := subsingleton_ext_of_iso e.toModuleIso Y n
    exact subsingleton_ext_X₂_of_shortExact (shortExact_of_linearMaps f g hf hfg hg) Y n

end ModuleFiltration

namespace Stendhal

open KLR ModuleFiltration QuantumGroup

open scoped Classical

variable {I : Type} {C : CartanDatum I} {k : Type} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} (hR : IsRouquierQ C Q) (hQs : KLRSymm Q)
  {n : ℕ} (Λ : Fin n → I →₀ ℕ) (ν : Multiset I)

/-- The projective `T^λ e(t)` has no nonzero maps to `S_s` unless `t ≤ s`. -/
theorem subsingleton_hom_lIdeal_stdModule
    {s t : {t : Seq (stendhalWeight n ν) // IsRedOrdered t}} (h : ¬ StendhalLE t.1 s.1) :
    Subsingleton (ModuleCat.of (TensorProductAlgebra k Q Λ ν) (lIdeal (seqIdem Q Λ t.1 t.2)) ⟶
      stdModule Q Λ ν s) := by
  have key : ∀ f : ModuleCat.of (TensorProductAlgebra k Q Λ ν) (lIdeal (seqIdem Q Λ t.1 t.2)) ⟶
      stdModule Q Λ ν s, f = 0 := fun f => by
    ext x
    have hx : x = x.1 • (⟨seqIdem Q Λ t.1 t.2, seqIdem_mul_self Q Λ t.1 t.2⟩ :
        lIdeal (seqIdem Q Λ t.1 t.2)) := Subtype.ext x.2.symm
    have he : (⟨seqIdem Q Λ t.1 t.2, seqIdem_mul_self Q Λ t.1 t.2⟩ :
        lIdeal (seqIdem Q Λ t.1 t.2)) = seqIdem Q Λ t.1 t.2 •
        (⟨seqIdem Q Λ t.1 t.2, seqIdem_mul_self Q Λ t.1 t.2⟩ : lIdeal (seqIdem Q Λ t.1 t.2)) :=
      Subtype.ext (seqIdem_mul_self Q Λ t.1 t.2).symm
    change f.hom x = 0
    rw [hx, map_smul, he, map_smul,
      seqIdem_smul_leftStandard_eq_zero_of_not_stendhalLE s.2 t.2 h, smul_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

variable [HasExt.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]

include hR hQs

/-- **No `Ext` from a standard that is not below** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.26): for red-ordered loadings `s`, `t` with `t` not below `s` in Webster's
preorder (in particular, when the root function of `t` is strictly above that of `s`),
`Extⁿ(S_t, S_s) = 0` for every `n`. For Rouquier parameters `Q`. -/
theorem subsingleton_ext_stdModule_of_not_stendhalLE
    (s t : {t : Seq (stendhalWeight n ν) // IsRedOrdered t}) (h : ¬ StendhalLE t.1 s.1)
    (m : ℕ) : Subsingleton (Ext.{w} (stdModule Q Λ ν t) (stdModule Q Λ ν s) m) := by
  let r : {t : Seq (stendhalWeight n ν) // IsRedOrdered t} →
      {t : Seq (stendhalWeight n ν) // IsRedOrdered t} → Prop :=
    fun a b => StendhalLT b.1 a.1
  have : IsTrans _ r := ⟨fun a b c hab hbc => ⟨stendhalLE_trans hbc.1 hab.1,
    fun hac => hab.2 (stendhalLE_trans hac hbc.1)⟩⟩
  have : Std.Irrefl r := ⟨fun a ha => ha.2 ha.1⟩
  induction t using (Finite.wellFounded_of_trans_of_irrefl r).induction generalizing m with
  | _ t ih =>
  obtain ⟨l, hl, hU⟩ := exists_hasFiltration_leftUpper_of_rouquier hR hQs Λ ν t.1 t.2
  have hS := shortExact_of_linearMaps
    (X := ModuleCat.of _ ((leftUpper Q Λ t.1 t.2).comap (lIdeal (seqIdem Q Λ t.1 t.2)).subtype))
    (Y := ModuleCat.of _ (lIdeal (seqIdem Q Λ t.1 t.2))) (Z := stdModule Q Λ ν t)
    _ _ (Submodule.injective_subtype _)
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
  cases m with
  | zero =>
    have := subsingleton_hom_lIdeal_stdModule (Q := Q) Λ ν h
    exact subsingleton_ext_X₃_zero_of_shortExact.{w} hS (stdModule Q Λ ν s)
  | succ m =>
    have := Stendhal.projective_lIdeal_seqIdem Q Λ t.1 t.2
    have : Subsingleton (Ext.{w} (ModuleCat.of (TensorProductAlgebra k Q Λ ν)
        (lIdeal (seqIdem Q Λ t.1 t.2))) (stdModule Q Λ ν s) (m + 1)) :=
      Ext.subsingleton_of_projective _ _ m
    have : Subsingleton (Ext.{w} (ModuleCat.of (TensorProductAlgebra k Q Λ ν)
        ((leftUpper Q Λ t.1 t.2).comap (lIdeal (seqIdem Q Λ t.1 t.2)).subtype))
        (stdModule Q Λ ν s) m) :=
      hU.subsingleton_ext _ m fun c hc =>
        ih c (hl c hc) (fun hcs => h (stendhalLE_trans (hl c hc).1 hcs)) m
    exact subsingleton_ext_X₃_succ_of_shortExact.{w} hS (stdModule Q Λ ν s) m

/-- **No higher `Ext` from a standard that is not strictly below** (Webster,
arXiv:1309.3796v3, proof of Proposition 5.26): for red-ordered loadings `s ≤ t` in Webster's
preorder (in particular, when their root functions are equal),
`Ext^{m+1}(S_t, S_s) = 0`. For Rouquier parameters `Q`. -/
theorem subsingleton_ext_succ_stdModule
    (s t : {t : Seq (stendhalWeight n ν) // IsRedOrdered t}) (h : StendhalLE s.1 t.1)
    (m : ℕ) : Subsingleton (Ext.{w} (stdModule Q Λ ν t) (stdModule Q Λ ν s) (m + 1)) := by
  obtain ⟨l, hl, hU⟩ := exists_hasFiltration_leftUpper_of_rouquier hR hQs Λ ν t.1 t.2
  have hS := shortExact_of_linearMaps
    (X := ModuleCat.of _ ((leftUpper Q Λ t.1 t.2).comap (lIdeal (seqIdem Q Λ t.1 t.2)).subtype))
    (Y := ModuleCat.of _ (lIdeal (seqIdem Q Λ t.1 t.2))) (Z := stdModule Q Λ ν t)
    _ _ (Submodule.injective_subtype _)
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
  have := Stendhal.projective_lIdeal_seqIdem Q Λ t.1 t.2
  have : Subsingleton (Ext.{w} (ModuleCat.of (TensorProductAlgebra k Q Λ ν)
      (lIdeal (seqIdem Q Λ t.1 t.2))) (stdModule Q Λ ν s) (m + 1)) :=
    Ext.subsingleton_of_projective _ _ m
  have : Subsingleton (Ext.{w} (ModuleCat.of (TensorProductAlgebra k Q Λ ν)
      ((leftUpper Q Λ t.1 t.2).comap (lIdeal (seqIdem Q Λ t.1 t.2)).subtype))
      (stdModule Q Λ ν s) m) :=
    hU.subsingleton_ext _ m fun c hc =>
      subsingleton_ext_stdModule_of_not_stendhalLE hR hQs Λ ν s c
        (fun hcs => (hl c hc).2 (stendhalLE_trans hcs h)) m
  exact subsingleton_ext_X₃_succ_of_shortExact.{w} hS (stdModule Q Λ ν s) m

end Stendhal

end Categorification
