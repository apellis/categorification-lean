/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardStratification
import Categorification.WeightedKLR.RedStrands.OrderedStandardResolution
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Standard modules have finite projective dimension

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Lemma 5.26 and Corollary 5.22.

Lemma 5.26 is stated there for modules with a standard filtration whose subquotients have
finite projective dimension; we prove it for any finite filtration (`HasFiltration`): if every
subquotient has projective dimension `< n`, so does the filtered module.

Corollary 5.22 asserts that every standard module `S_s` has a finite-length projective
resolution. We state finite projective dimension in Mathlib's sense
(`HasProjectiveDimensionLT`, vanishing of `Ext` in large degrees). The proof is Webster's:
descending induction on `s` in Webster's order, using the short exact sequence
`0 → U_s → T^λ e(s) → S_s → 0`, projectivity of `T^λ e(s)`, and the standard filtration of `U_s`
by modules `S_t` with `t > s` (Corollary 5.21, `exists_hasFiltration_leftUpper`).

## Main results

* `ModuleFiltration.HasFiltration.hasProjectiveDimensionLT`: Lemma 5.26 for finite filtrations.
* `exists_hasProjectiveDimensionLT_stdModule`: Corollary 5.22. Route hypothesis:
  `AllFiniteDeltaInjective` (Proposition 5.5, `F`-part), as for Proposition 5.20.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification

open CategoryTheory Limits

namespace ModuleFiltration

variable {A : Type} [Ring A]

/-- A short exact sequence of modules, given by linear maps, as a short exact complex in
`ModuleCat`. -/
theorem shortExact_of_linearMaps {X Y Z : ModuleCat.{0} A} (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    (ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (by ext x; exact hfg.apply_apply_eq_zero x)).ShortExact := by
  have : Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).2 hf
  have : Epi (ModuleCat.ofHom g) := (ModuleCat.epi_iff_surjective _).2 hg
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg⟩

variable {ι : Type*} {L : ι → ModuleCat.{0} A}

/-- **Lemma 5.26** (Webster, arXiv:1309.3796v2), for finite filtrations: if every subquotient
of a finite filtration of `Y` has projective dimension `< n`, so does `Y`. -/
theorem HasFiltration.hasProjectiveDimensionLT {m : List ι} {Y : ModuleCat.{0} A}
    (h : HasFiltration L m Y) (n : ℕ) (hL : ∀ c ∈ m, HasProjectiveDimensionLT (L c) n) :
    HasProjectiveDimensionLT Y n := by
  induction h with
  | @zero Y hY =>
    have : HasProjectiveDimensionLT Y 0 :=
      (ModuleCat.isZero_of_subsingleton Y).hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge Y 0 n (Nat.zero_le n)
  | @cons X Y Z f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    have hX := ih fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')
    have : HasProjectiveDimensionLT (L c) n := hL c List.mem_cons_self
    have hZ' : HasProjectiveDimensionLT Z n :=
      hasProjectiveDimensionLT_of_iso e.symm.toModuleIso n
    exact (shortExact_of_linearMaps f g hf hfg hg).hasProjectiveDimensionLT_X₂ n hX hZ'

end ModuleFiltration

namespace Stendhal

open KLR ModuleFiltration

variable {I : Type} [DecidableEq I] {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k)

section Projective

variable {n : ℕ} (Λ : Fin n → I →₀ ℕ) {ν : Multiset I}

/-- `T^λ e(s)` is a projective left module. -/
theorem projective_lIdeal_seqIdem (s : Seq (stendhalWeight n ν)) (hs : IsRedOrdered s) :
    Projective (ModuleCat.of (TensorProductAlgebra k Q Λ ν) (lIdeal (seqIdem Q Λ s hs))) := by
  rw [← IsProjective.iff_projective]
  refine Module.Projective.of_split (lIdeal (seqIdem Q Λ s hs)).subtype
    { toFun := fun b => ⟨b * seqIdem Q Λ s hs, by
        change _ * _ * _ = _
        rw [mul_assoc, seqIdem_mul_self]⟩
      map_add' := fun a b => Subtype.ext (add_mul a b _)
      map_smul' := fun a b => Subtype.ext (mul_assoc a b _) } ?_
  ext y
  exact y.2

end Projective

variable {C : QuantumGroup.CartanDatum I} (hQ : KLRSymm Q)

/-- **Standard modules have finite projective dimension** (Webster, arXiv:1309.3796v2,
Corollary 5.22): for every red-ordered loading `s`, the standard module `S_s` has finite
projective dimension. Route hypothesis: `AllFiniteDeltaInjective` (Proposition 5.5, `F`-part) at
every number of red strands, as for Proposition 5.20. -/
theorem exists_hasProjectiveDimensionLT_stdModule (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    {n : ℕ} (Λ : Fin n → I →₀ ℕ) (ν : Multiset I)
    (s : {t : Seq (stendhalWeight n ν) // IsRedOrdered t}) :
    ∃ N : ℕ, HasProjectiveDimensionLT (stdModule Q Λ ν s) N := by
  let r : {t : Seq (stendhalWeight n ν) // IsRedOrdered t} →
      {t : Seq (stendhalWeight n ν) // IsRedOrdered t} → Prop :=
    fun a b => StendhalLT b.1 a.1
  have : IsTrans _ r := ⟨fun a b c hab hbc => ⟨stendhalLE_trans hbc.1 hab.1,
    fun hac => hab.2 (stendhalLE_trans hac hbc.1)⟩⟩
  have : Std.Irrefl r := ⟨fun a ha => ha.2 ha.1⟩
  induction s using (Finite.wellFounded_of_trans_of_irrefl r).induction with
  | _ s ih =>
  obtain ⟨m, hm, hU⟩ := exists_hasFiltration_leftUpper Q hQ hR hall Λ ν s.1 s.2
  choose! N hN using fun c (hc : c ∈ m) => ih c (hm c hc)
  set M := (m.map N).sum
  have hUM := hU.hasProjectiveDimensionLT M fun c hc => by
    have := hN c hc
    exact hasProjectiveDimensionLT_of_ge _ (N c) M
      (List.le_sum_of_mem (List.mem_map_of_mem hc))
  have := projective_lIdeal_seqIdem Q Λ s.1 s.2
  refine ⟨M + 1, ?_⟩
  exact (shortExact_of_linearMaps
    (X := ModuleCat.of _ ((leftUpper Q Λ s.1 s.2).comap (lIdeal (seqIdem Q Λ s.1 s.2)).subtype))
    (Y := ModuleCat.of _ (lIdeal (seqIdem Q Λ s.1 s.2))) (Z := stdModule Q Λ ν s)
    _ _ (Submodule.injective_subtype _)
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)).hasProjectiveDimensionLT_X₃
      M hUM inferInstance

/-- In the proof of Webster's Lemma 6.11, the standard resolution must have
higher loading support in positive homological degrees. The kernel
filtrations from Corollary 5.21 supply the resolution with that support. -/
theorem exists_ordered_projectiveResolution_stdModule (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    {n : ℕ} (Λ : Fin n → I →₀ ℕ) (ν : Multiset I)
    (s : {t : Seq (stendhalWeight n ν) // IsRedOrdered t}) :
    ∃ P : ProjectiveResolution (stdModule Q Λ ν s), ∀ j : ℕ,
      ∃ (J : Type) (label : J → {t : Seq (stendhalWeight n ν) // IsRedOrdered t})
        (inc : ∀ i, lIdeal (seqIdem Q Λ (label i).1 (label i).2) →ₗ[TensorProductAlgebra k Q Λ ν]
          P.complex.X (j + 1)),
        (∀ i, StendhalLT s.1 (label i).1) ∧ ∀ x : P.complex.X (j + 1),
          x ∈ Submodule.span (TensorProductAlgebra k Q Λ ν) {y | ∃ i z, inc i z = y} :=
  exists_ordered_projectiveResolution_leftStandard Q Λ
    (fun c => exists_hasFiltration_leftUpper Q hQ hR hall Λ ν c.1 c.2) s

end Stendhal

end Categorification
