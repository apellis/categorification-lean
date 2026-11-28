/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCoefficientAcyclicCover
import Categorification.WeightedKLR.Rigidity.SMoveFactorAlgebraFiltration
import Categorification.WeightedKLR.Rigidity.SMoveReflectedStd
import Categorification.WeightedKLR.RedStrands.ProjectiveStandardFiltrationOrder

/-!
# Separation of standardizations by the black count at the last red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, the off-diagonal `E²` terms. Both sides of the S-move pairing are standard
layers at the last red strand (`SMove.leftStdCutLayerIso`, `SMove.rightStdLayerIso`), and the
resolutions of Proposition 7.8 have as terms standardizations `S(M)` of finite-dimensional
modules `M` over the factor algebra `D_{θ,β}` of a split `θ + β = ν`.

Every standard label of `S(D_{θ,β})` is a two-piece loading `t' λ_{ℓ+1} u`, whose black count
at the last red strand is `θ` (`blackCount_twoPieceLabel_last`). Two loadings with different
black counts at some red strand are not equivalent in Webster's preorder
(`not_stendhalEquiv_of_blackCount_ne`). So for `θ ≠ θ'` no label of `S(D_{θ,β})` is
equivalent to a label of `S(D_{θ',β'})`, and the reflection of `S(D_{θ,β})` has no Tor against
`S(D_{θ',β'})`. The dévissage on both sides (`torAcyclic_of_twoSidedCovers`), with free covers
of finite-dimensional modules, extends this to `S(M)` and `S(M')`.

## Main results

* `not_stendhalEquiv_of_blackCount_ne`, `not_stendhalEquiv_twoPieceLabel_of_ne`.
* `torAcyclic_reflect_stdLayer_factorAlgebra`: no Tor between the reflection of `S(D_{θ,β})`
  and `S(D_{θ',β'})` for `θ ≠ θ'`.
* `torAcyclic_reflect_stdLayer_of_ne`: the same for `S(M)` and `S(M')`, `M`, `M'`
  finite-dimensional, for Rouquier parameters.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR ModuleFiltration Equiv BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- **Loadings with different black counts are inequivalent** in Webster's preorder
(arXiv:1309.3796v3, §5.1): if `s` and `t` have different numbers of black `i`-strands left of
some red strand, then not both `s ≤ t` and `t ≤ s`. -/
theorem not_stendhalEquiv_of_blackCount_ne {I : Type*} [DecidableEq I] {ℓ : ℕ}
    {μ : Multiset (I ⊕ Fin ℓ)} {s t : Seq μ} {r : Fin ℓ} {i : I}
    (h : blackCount s r i ≠ blackCount t r i) : ¬ (StendhalLE s t ∧ StendhalLE t s) :=
  fun hst => h (le_antisymm (hst.1 r i) (hst.2 r i))

/-- **Two-piece loadings of different splits are inequivalent**: the black count at the last
red strand of `t λ_{ℓ+1} u` is `θ`, so for `θ ≠ θ'` no two-piece loading of the split
`θ + β = ν` is equivalent to one of `θ' + β' = ν`. -/
theorem not_stendhalEquiv_twoPieceLabel_of_ne {I : Type} [DecidableEq I] {ℓ : ℕ}
    {θ β θ' β' ν : Multiset I} (h : θ + β = ν) (h' : θ' + β' = ν) (hne : θ ≠ θ')
    (u : Seq β) (d : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t})
    (u' : Seq β') (d' : {t : Seq (stendhalWeight ℓ θ') // IsRedOrdered t}) :
    ¬ (StendhalLE (twoPieceLabel h u d).1 (twoPieceLabel h' u' d').1 ∧
      StendhalLE (twoPieceLabel h' u' d').1 (twoPieceLabel h u d).1) := by
  obtain ⟨i, hi⟩ : ∃ i, θ.count i ≠ θ'.count i := by
    by_contra hc
    exact hne (Multiset.ext.mpr fun i => not_not.mp fun hi => hc ⟨i, hi⟩)
  refine not_stendhalEquiv_of_blackCount_ne (r := Fin.last ℓ) (i := i) ?_
  rw [blackCount_twoPieceLabel_last, blackCount_twoPieceLabel_last]
  exact hi

/-- An exact functor of module categories carries short exact sequences to short exact
sequences. -/
theorem ModuleExactFunctor.shortExact_map {R S : Type} [Ring R] [Ring S]
    {F : ModuleCat.{0} R ⥤ ModuleCat.{0} S} [F.PreservesZeroMorphisms]
    (hF : ModuleExactFunctor F)
    {X : ShortComplex (ModuleCat.{0} R)} (hX : X.ShortExact) : (X.map F).ShortExact := by
  have hm : Mono (X.map F).f := (ModuleCat.mono_iff_injective _).mpr
    (hF.injective X.f ((ModuleCat.mono_iff_injective X.f).mp hX.mono_f))
  have he : Epi (X.map F).g := (ModuleCat.epi_iff_surjective _).mpr
    (hF.surjective X.g ((ModuleCat.epi_iff_surjective X.g).mp hX.epi_g))
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    (hF.exact X.f X.g ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact X).mp
      hX.exact))⟩

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)

local notation "old" => Λ ∘ Fin.castSucc
local notation "T" => TensorProductAlgebra k Q Λ ν

/-- The reflection of left `T^λ`-modules at the trivial braid. -/
abbrev reflectOne : ModuleCat.{0} T ⥤ ModuleCat.{0} Tᵐᵒᵖ :=
  tensorReflectFunctor (Λ := Λ) (ν := ν) hρ hQ 1

theorem shortExact_map_reflectOne {X : ShortComplex (ModuleCat.{0} T)} (hX : X.ShortExact) :
    (X.map (reflectOne Q Λ hQ hρ)).ShortExact :=
  ModuleExactFunctor.shortExact_map (ModuleExactFunctor.restrictScalars _) hX

/-- A finite-dimensional factor module is covered by a free module with a finite-dimensional
kernel, and standardization carries the cover to a short exact sequence. -/
theorem exists_stdLayer_freeCover {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    {θ β : Multiset I} (h : θ + β = ν) (M : FactorModule Q Λ θ β)
    [FiniteDimensional k M.carrier] :
    ∃ (n : ℕ) (K : FactorModule Q Λ θ β) (_ : FiniteDimensional k K.carrier)
      (S : ShortComplex (ModuleCat.{0} T)), S.ShortExact ∧
      S.X₁ = stdLayerModule Q Λ hQ ⟨θ, β, h, K⟩ ∧
      S.X₂ = stdOf Q Λ hQ h (Fin (n + 1) → parabolicFactorAlgebra Q Λ θ β) ∧
      S.X₃ = stdLayerModule Q Λ hQ ⟨θ, β, h, M⟩ := by
  have hDf : Module.Finite k (parabolicFactorAlgebra Q Λ θ β) :=
    Subsingleton.elim (fun a b => Classical.propDecidable (a = b)) ‹DecidableEq I› ▸
      module_finite_parabolicFactorAlgebra_of_rouquier (Λ := Λ) hR θ β
  obtain ⟨n, π, hπ⟩ := exists_free_surjective Q Λ M
  let K := LinearMap.ker π
  have : Module.Finite k (Fin (n + 1) → parabolicFactorAlgebra Q Λ θ β) :=
    Module.Finite.pi (h := fun _ => hDf)
  have hKfin : FiniteDimensional k K :=
    FiniteDimensional.finiteDimensional_submodule (K.restrictScalars k)
  exact ⟨n, factorOf Q Λ K, hKfin, _, stdLayer_shortExact Q Λ hQ h (M₁ := factorOf Q Λ K)
    (M₂ := factorOf Q Λ (Fin (n + 1) → parabolicFactorAlgebra Q Λ θ β)) (M₃ := M) K.subtype π
    Subtype.val_injective (LinearMap.exact_subtype_ker_map π) hπ, rfl, rfl, rfl⟩

variable [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.map (1 : Perm (Fin (ℓ + 1)))
      (List.finRange (ℓ + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} ℤ]

include hρ in
/-- **No Tor between standardized factor algebras of different splits** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, off-diagonal `E²` terms): for splits
`θ + β = ν` and `θ' + β' = ν` with `θ ≠ θ'`, the reflection of `S(D_{θ,β})` has no Tor against
`S(D_{θ',β'})`. Hypotheses as in `torAcyclic_stdLayer_factorAlgebra`: the ordered covers of the
left standards and the standard filtrations of the first `ℓ` red strands. -/
theorem torAcyclic_reflect_stdLayer_factorAlgebra
    (DC : OrderedStandardCovers
      (fun s : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ s.1 s.2))
      (fun s => seqIdem Q Λ s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    (hold : HasStandardFiltrations Q (old)) {θ β θ' β' : Multiset I} (h : θ + β = ν)
    (h' : θ' + β' = ν) (hne : θ ≠ θ') :
    TorAcyclic.{w} (k := ℤ)
      ((reflectOne Q Λ hQ hρ).obj (stdOf Q Λ hQ h (parabolicFactorAlgebra Q Λ θ β)))
      (stdOf Q Λ hQ h' (parabolicFactorAlgebra Q Λ θ' β')) := by
  obtain ⟨l, hl⟩ := exists_hasFiltration_stdLayer_factorAlgebra Q Λ hQ h hold
  have hY : HasFiltration (stdModule Q Λ ν)
      (l.map fun p : Seq β × {d : Seq (stendhalWeight ℓ θ) // IsRedOrdered d} =>
        twoPieceLabel h p.1 p.2) (stdOf Q Λ hQ h (parabolicFactorAlgebra Q Λ θ β)) :=
    HasFiltration.relabel (L := stdModule Q Λ ν) _ hl
  have hN := hasFiltration_tensorReflect_one hQ hρ hY
  refine torAcyclic_stdLayer_factorAlgebra Q Λ hQ hρ DC hold h' hN ?_
  intro t ht u' d'
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp ht
  exact fun hc => not_stendhalEquiv_twoPieceLabel_of_ne h h' hne p.1 p.2 u' d' ⟨hc.2, hc.1⟩

omit [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.map (1 : Perm (Fin (ℓ + 1)))
      (List.finRange (ℓ + 1))))] in
/-- **Reflected standardizations of free factor modules**: if the reflection of `S(D)` is
Tor-acyclic against `Y`, so is the reflection of `S(D^{n+1})`. -/
theorem torAcyclic_reflect_stdLayer_free {θ β : Multiset I} (h : θ + β = ν)
    (Y : ModuleCat.{0} T)
    (hD : TorAcyclic.{w} (k := ℤ)
      ((reflectOne Q Λ hQ hρ).obj (stdOf Q Λ hQ h (parabolicFactorAlgebra Q Λ θ β))) Y) :
    ∀ n : ℕ, TorAcyclic.{w} (k := ℤ) ((reflectOne Q Λ hQ hρ).obj
      (stdOf Q Λ hQ h (Fin (n + 1) → parabolicFactorAlgebra Q Λ θ β))) Y := by
  intro n
  induction n with
  | zero =>
    exact TorAcyclic.of_coefficient_iso Y ((reflectOne Q Λ hQ hρ).mapIso
      (stdLayerIso Q Λ hQ h (M := factorOf Q Λ (parabolicFactorAlgebra Q Λ θ β))
        (M' := factorOf Q Λ (Fin 1 → parabolicFactorAlgebra Q Λ θ β))
        (LinearEquiv.funUnique (Fin 1) _ _).symm)) hD
  | succ n ih =>
    let D := parabolicFactorAlgebra Q Λ θ β
    let F := Fin (n + 1) → D
    have hS := shortExact_map_reflectOne Q Λ hQ hρ (stdLayer_shortExact Q Λ hQ h
      (M₁ := factorOf Q Λ F) (M₂ := factorOf Q Λ (D × F)) (M₃ := factorOf Q Λ D)
      (LinearMap.inr D D F) (LinearMap.fst D D F) LinearMap.inr_injective
      Function.Exact.inr_fst LinearMap.fst_surjective)
    have hmid := TorAcyclic.of_coefficient_shortExact Y hS ih hD
    exact TorAcyclic.of_coefficient_iso Y ((reflectOne Q Λ hQ hρ).mapIso
      (stdLayerIso Q Λ hQ h (M := factorOf Q Λ (D × F))
        (M' := factorOf Q Λ (Fin (n + 1 + 1) → D))
        (Fin.consLinearEquiv D (fun _ : Fin (n + 1 + 1) => D)))) hmid

include hρ in
/-- **Off-diagonal Tor vanishing for standardizations of different splits** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, the `E²` terms of the resolutions of
Proposition 7.8 that are separated at the last red strand): for Rouquier parameters, splits
`θ + β = ν` and `θ' + β' = ν` with `θ ≠ θ'`, and finite-dimensional modules `M` over `D_{θ,β}`
and `M'` over `D_{θ',β'}`, the reflection of `S(M)` has no Tor against `S(M')`. Hypotheses as in
`torAcyclic_reflect_stdLayer_factorAlgebra`. -/
theorem torAcyclic_reflect_stdLayer_of_ne {C : QuantumGroup.CartanDatum I}
    (hR : IsRouquierQ C Q)
    (DC : OrderedStandardCovers
      (fun s : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ s.1 s.2))
      (fun s => seqIdem Q Λ s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    (hold : HasStandardFiltrations Q (old)) {θ β θ' β' : Multiset I} (h : θ + β = ν)
    (h' : θ' + β' = ν) (hne : θ ≠ θ') (M : FactorModule Q Λ θ β)
    [FiniteDimensional k M.carrier] (M' : FactorModule Q Λ θ' β')
    [FiniteDimensional k M'.carrier] :
    TorAcyclic.{w} (k := ℤ) ((reflectOne Q Λ hQ hρ).obj (stdLayerModule Q Λ hQ ⟨θ, β, h, M⟩))
      (stdLayerModule Q Λ hQ ⟨θ', β', h', M'⟩) := by
  let 𝒞X : ModuleCat.{0} Tᵐᵒᵖ → Prop := fun N => ∃ K : FactorModule Q Λ θ β,
    FiniteDimensional k K.carrier ∧
      N = (reflectOne Q Λ hQ hρ).obj (stdLayerModule Q Λ hQ ⟨θ, β, h, K⟩)
  let 𝒫X : ModuleCat.{0} Tᵐᵒᵖ → Prop := fun N => ∃ n : ℕ,
    N = (reflectOne Q Λ hQ hρ).obj (stdOf Q Λ hQ h (Fin (n + 1) → parabolicFactorAlgebra Q Λ θ β))
  let 𝒞Y : ModuleCat.{0} T → Prop := fun Y => ∃ K : FactorModule Q Λ θ' β',
    FiniteDimensional k K.carrier ∧ Y = stdLayerModule Q Λ hQ ⟨θ', β', h', K⟩
  let 𝒫Y : ModuleCat.{0} T → Prop := fun Y => ∃ n : ℕ,
    Y = stdOf Q Λ hQ h' (Fin (n + 1) → parabolicFactorAlgebra Q Λ θ' β')
  refine torAcyclic_of_twoSidedCovers 𝒞X 𝒫X 𝒞Y 𝒫Y ?_ ?_ ?_ _ ⟨M, inferInstance, rfl⟩ _
    ⟨M', inferInstance, rfl⟩
  · rintro N ⟨K, hK, rfl⟩
    obtain ⟨n, K', hK', S, hS, h₁, h₂, h₃⟩ := exists_stdLayer_freeCover Q Λ hQ hR h K
    refine ⟨S.map (reflectOne Q Λ hQ hρ), shortExact_map_reflectOne Q Λ hQ hρ hS,
      ⟨K', hK', by rw [ShortComplex.map_X₁, h₁]⟩, ⟨n, by rw [ShortComplex.map_X₂, h₂]⟩,
      ⟨eqToIso (by rw [ShortComplex.map_X₃, h₃])⟩⟩
  · rintro Y ⟨K, hK, rfl⟩
    obtain ⟨n, K', hK', S, hS, h₁, h₂, h₃⟩ := exists_stdLayer_freeCover Q Λ hQ hR h' K
    exact ⟨S, hS, ⟨K', hK', h₁⟩, ⟨n, h₂⟩, ⟨eqToIso h₃⟩⟩
  · rintro P ⟨a, rfl⟩ P' ⟨b, rfl⟩
    refine torAcyclic_reflect_stdLayer_free Q Λ hQ hρ h _ ?_ a
    exact torAcyclic_stdLayer_free Q Λ hQ h' _
      (torAcyclic_reflect_stdLayer_factorAlgebra Q Λ hQ hρ DC hold h h' hne) b

end Categorification.Stendhal
