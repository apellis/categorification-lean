/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveStdLayerSeparation
import Categorification.WeightedKLR.RedStrands.TensorLayerFiltration

/-!
# Separation of standardizations at an inner red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, the off-diagonal `E²` terms that are separated at an inner red strand. In
the S-move, the first term of the resolution of the right module and the terms of the
resolution of the left module other than the last one have the same black count at the last
red strand. They differ at the middle red strand, and this is seen in their structure over the
first `ℓ` red strands: both are standardizations `Φ(Z) = S(Z ⊠ R e(u))` of modules `Z` over
`T^{λ'}`.

`Φ` is exact and carries a filtration of `Z` by standards `S_d` of `T^{λ'}` to a filtration of
`Φ(Z)` by the standards of the two-piece loadings `d λ_{ℓ+1} u`, whose black counts at the
first `ℓ` red strands are those of `d` (`blackCount_twoPieceLabel_castSucc`). So if `Z` and
`Z'` lie in classes of `T^{λ'}`-modules with covers by standard-filtered modules whose labels
differ in black count at some red strand, then the reflection of `Φ(Z)` has no Tor against
`Φ(Z')` (`torAcyclic_reflect_tensorLayer_of_covers`), by the two-sided dévissage
`torAcyclic_of_twoSidedCovers`.

## Main results

* `exists_tensorLayer_shortExact`: `Φ` carries short exact sequences to short exact sequences.
* `hasFiltration_tensorLayer_standard`: the standard filtration of `Φ(Z)`.
* `not_stendhalEquiv_twoPieceLabel_of_blackCount_ne`.
* `exists_hasFiltration_stdLayer_free`: the standard filtration of `S(D^{n+1})`.
* `torAcyclic_reflect_tensorLayer_of_covers`.
* `torAcyclic_reflect_tensorLayer_stdLayer_of_ne`: the case where `Z`, `Z'` are
  standardizations of finite-dimensional modules over the first `m + 1` red strands whose
  splits differ at the last of them.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR ModuleFiltration Equiv BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q) {ν : Multiset I}

local notation "old" => Λ ∘ Fin.castSucc
local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
local notation "T" => TensorProductAlgebra k Q Λ ν

/-- **`Φ = S(− ⊠ R e(u))` is exact**: a short exact sequence of modules over `T^{λ'}` gives a
short exact sequence of standard layers. -/
theorem exists_tensorLayer_shortExact {θ β : Multiset I} (h : θ + β = ν) (u : Seq β)
    {S : ShortComplex (ModuleCat.{0} (Told θ))} (hS : S.ShortExact) :
    ∃ S' : ShortComplex (ModuleCat.{0} T), S'.ShortExact ∧
      S'.X₁ = stdLayerModule Q Λ hQ (tensorLayer Q Λ h S.X₁ (cycProj Q Λ β u)) ∧
      S'.X₂ = stdLayerModule Q Λ hQ (tensorLayer Q Λ h S.X₂ (cycProj Q Λ β u)) ∧
      S'.X₃ = stdLayerModule Q Λ hQ (tensorLayer Q Λ h S.X₃ (cycProj Q Λ β u)) := by
  have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hg : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  have hfg : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  exact ⟨_, stdLayer_shortExact Q Λ hQ h
    (M₁ := tensorFactor Q Λ S.X₁ (cycProj Q Λ β u))
    (M₂ := tensorFactor Q Λ S.X₂ (cycProj Q Λ β u))
    (M₃ := tensorFactor Q Λ S.X₃ (cycProj Q Λ β u))
    (tensorFactorMapLeft Q Λ (cycProj Q Λ β u) S.f.hom)
    (tensorFactorMapLeft Q Λ (cycProj Q Λ β u) S.g.hom)
    (ExtTensor.map_id_injective (k := k) (P := KMod (k := k) S.X₁) (P' := KMod (k := k) S.X₂)
      (Q := KMod (k := k) (cycProj Q Λ β u)) (f := KMod.map S.f.hom) hf)
    (ExtTensor.map_id_exact (k := k) (P := KMod (k := k) S.X₁) (P' := KMod (k := k) S.X₂)
      (P'' := KMod (k := k) S.X₃) (Q := KMod (k := k) (cycProj Q Λ β u))
      (f := KMod.map S.f.hom) (g := KMod.map S.g.hom) hfg hg)
    (ExtTensor.map_id_surjective (k := k) (P := KMod (k := k) S.X₂)
      (P' := KMod (k := k) S.X₃) (Q := KMod (k := k) (cycProj Q Λ β u))
      (f := KMod.map S.g.hom) hg), rfl, rfl, rfl⟩

/-- **The standard filtration of `Φ(Z)`** (Webster, arXiv:1309.3796v2, proof of
Proposition 5.20): a filtration of `Z` by the standards `S_d` of `T^{λ'}` gives a filtration of
`S(Z ⊠ R e(u))` by the standards of the two-piece loadings `d λ_{ℓ+1} u`. -/
theorem hasFiltration_tensorLayer_standard {θ β : Multiset I} (h : θ + β = ν) (u : Seq β)
    {m : List {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t}} {Z : ModuleCat.{0} (Told θ)}
    (hZ : HasFiltration (stdModule Q (old) θ) m Z) :
    HasFiltration (stdModule Q Λ ν) (m.map (twoPieceLabel h u))
      (stdLayerModule Q Λ hQ (tensorLayer Q Λ h Z (cycProj Q Λ β u))) := by
  have h₁ := hasFiltration_tensorLayer Q Λ hQ h (cycProj Q Λ β u) hZ
  have h₂ : HasFiltration (fun d => stdModule Q Λ ν (twoPieceLabel h u d)) m
      (stdLayerModule Q Λ hQ (tensorLayer Q Λ h Z (cycProj Q Λ β u))) :=
    h₁.mono fun d => nonempty_stdLayerModule_twoPiece_equiv Q Λ hQ h d.2 u
  exact HasFiltration.relabel (L := stdModule Q Λ ν) (twoPieceLabel h u) h₂

omit [Field k] in
/-- Two-piece loadings whose first pieces differ in black count at a red strand are
inequivalent. -/
theorem not_stendhalEquiv_twoPieceLabel_of_blackCount_ne {θ β θ' β' : Multiset I}
    (h : θ + β = ν) (h' : θ' + β' = ν) (u : Seq β) (u' : Seq β')
    (d : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t})
    (d' : {t : Seq (stendhalWeight ℓ θ') // IsRedOrdered t}) {r : Fin ℓ} {i : I}
    (hne : blackCount d.1 r i ≠ blackCount d'.1 r i) :
    ¬ (StendhalLE (twoPieceLabel h u d).1 (twoPieceLabel h' u' d').1 ∧
      StendhalLE (twoPieceLabel h' u' d').1 (twoPieceLabel h u d).1) := by
  refine not_stendhalEquiv_of_blackCount_ne (r := r.castSucc) (i := i) ?_
  rw [blackCount_twoPieceLabel_castSucc, blackCount_twoPieceLabel_castSucc]
  exact hne

/-- **The standard filtration of a standardized free factor module**: `S(D_{θ,β}^{n+1})` is
filtered by standards of two-piece loadings `t' λ_{ℓ+1} u` (from
`exists_hasFiltration_stdLayer_factorAlgebra`, closed under extensions). -/
theorem exists_hasFiltration_stdLayer_free (hold : HasStandardFiltrations Q (old))
    {θ β : Multiset I} (h : θ + β = ν) (n : ℕ) :
    ∃ l : List {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s},
      (∀ s ∈ l, ∃ u d, s = twoPieceLabel h u d) ∧
      HasFiltration (stdModule Q Λ ν) l
        (stdOf Q Λ hQ h (Fin (n + 1) → parabolicFactorAlgebra Q Λ θ β)) := by
  obtain ⟨l₀, hl₀⟩ := exists_hasFiltration_stdLayer_factorAlgebra Q Λ hQ h hold
  have hD : HasFiltration (stdModule Q Λ ν)
      (l₀.map fun p : Seq β × {d : Seq (stendhalWeight ℓ θ) // IsRedOrdered d} =>
        twoPieceLabel h p.1 p.2) (stdOf Q Λ hQ h (parabolicFactorAlgebra Q Λ θ β)) :=
    HasFiltration.relabel (L := stdModule Q Λ ν) _ hl₀
  have hmem : ∀ s ∈ l₀.map fun p : Seq β × {d : Seq (stendhalWeight ℓ θ) // IsRedOrdered d} =>
      twoPieceLabel h p.1 p.2, ∃ u d, s = twoPieceLabel h u d := fun s hs => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hs
    exact ⟨p.1, p.2, rfl⟩
  induction n with
  | zero =>
    exact ⟨_, hmem, hD.of_equiv (stdLayerEquiv Q Λ hQ h
      (M := factorOf Q Λ (parabolicFactorAlgebra Q Λ θ β))
      (M' := factorOf Q Λ (Fin 1 → parabolicFactorAlgebra Q Λ θ β))
      (LinearEquiv.funUnique (Fin 1) _ _).symm)⟩
  | succ n ih =>
    obtain ⟨l, hl, hF⟩ := ih
    let D := parabolicFactorAlgebra Q Λ θ β
    let F := Fin (n + 1) → D
    have hE := HasFiltration.extension hD
      (stdLayerMap Q Λ hQ h (M := factorOf Q Λ F) (M' := factorOf Q Λ (D × F))
        (LinearMap.inr D D F))
      (stdLayerMap Q Λ hQ h (M := factorOf Q Λ (D × F)) (M' := factorOf Q Λ D)
        (LinearMap.fst D D F))
      (parabolicStandardMap_injective Q Λ θ β hQ _ LinearMap.inr_injective)
      (parabolicStandardMap_exact Q Λ θ β hQ _ _ Function.Exact.inr_fst)
      (parabolicStandardMap_surjective Q Λ θ β hQ _ LinearMap.fst_surjective) hF
    refine ⟨_, fun s hs => ?_, hE.of_equiv (stdLayerEquiv Q Λ hQ h
      (M := factorOf Q Λ (D × F)) (M' := factorOf Q Λ (Fin (n + 1 + 1) → D))
      (Fin.consLinearEquiv D (fun _ : Fin (n + 1 + 1) => D)))⟩
    rcases List.mem_append.mp hs with hs | hs
    · exact hmem s hs
    · exact hl s hs

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)
  [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.map (1 : Perm (Fin (ℓ + 1)))
      (List.finRange (ℓ + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} ℤ]

include hρ in
/-- **Off-diagonal Tor vanishing separated at an inner red strand** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, the `E²` terms with equal black counts at
the last red strand). Fix splits `θ + β = ν`, `θ' + β' = ν` and black sequences `u`, `u'`. Let
`𝒵_X`, `𝒵_Y` be classes of modules over `T^{λ'}_θ`, `T^{λ'}_{θ'}` whose members have covers
`0 → K → P → Z → 0` with `K` in the same class and `P` in `𝒫_X` (resp. `𝒫_Y`), and let the
members of `𝒫_X`, `𝒫_Y` be filtered by standards with labels in `L_X`, `L_Y`. If every label of
`L_X` differs from every label of `L_Y` in its black count at some red strand, then for
`Z ∈ 𝒵_X`, `Z' ∈ 𝒵_Y` the reflection of `S(Z ⊠ R e(u))` has no Tor against
`S(Z' ⊠ R e(u'))`. Hypothesis `DC` as in
`isZero_derivedTensorHomology_tensor_of_standardFiltrations`. -/
theorem torAcyclic_reflect_tensorLayer_of_covers
    (DC : OrderedStandardCovers
      (fun s : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ s.1 s.2))
      (fun s => seqIdem Q Λ s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {θ β θ' β' : Multiset I} (h : θ + β = ν) (h' : θ' + β' = ν) (u : Seq β) (u' : Seq β')
    (𝒵X 𝒫X : ModuleCat.{0} (Told θ) → Prop) (𝒵Y 𝒫Y : ModuleCat.{0} (Told θ') → Prop)
    (LX : Set {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t})
    (LY : Set {t : Seq (stendhalWeight ℓ θ') // IsRedOrdered t})
    (hX : ∀ Z, 𝒵X Z → ∃ S : ShortComplex (ModuleCat.{0} (Told θ)), S.ShortExact ∧ 𝒵X S.X₁ ∧
      𝒫X S.X₂ ∧ S.X₃ = Z)
    (hY : ∀ Z, 𝒵Y Z → ∃ S : ShortComplex (ModuleCat.{0} (Told θ')), S.ShortExact ∧ 𝒵Y S.X₁ ∧
      𝒫Y S.X₂ ∧ S.X₃ = Z)
    (hPX : ∀ P, 𝒫X P → ∃ m, (∀ d ∈ m, d ∈ LX) ∧ HasFiltration (stdModule Q (old) θ) m P)
    (hPY : ∀ P, 𝒫Y P → ∃ m, (∀ d ∈ m, d ∈ LY) ∧ HasFiltration (stdModule Q (old) θ') m P)
    (hsep : ∀ d ∈ LX, ∀ d' ∈ LY, ∃ (r : Fin ℓ) (i : I), blackCount d.1 r i ≠ blackCount d'.1 r i)
    (Z : ModuleCat.{0} (Told θ)) (hZ : 𝒵X Z) (Z' : ModuleCat.{0} (Told θ')) (hZ' : 𝒵Y Z') :
    TorAcyclic.{w} (k := ℤ) ((reflectOne Q Λ hQ hρ).obj
        (stdLayerModule Q Λ hQ (tensorLayer Q Λ h Z (cycProj Q Λ β u))))
      (stdLayerModule Q Λ hQ (tensorLayer Q Λ h' Z' (cycProj Q Λ β' u'))) := by
  let ΦX := fun Z : ModuleCat.{0} (Told θ) =>
    stdLayerModule Q Λ hQ (tensorLayer Q Λ h Z (cycProj Q Λ β u))
  let ΦY := fun Z : ModuleCat.{0} (Told θ') =>
    stdLayerModule Q Λ hQ (tensorLayer Q Λ h' Z (cycProj Q Λ β' u'))
  refine torAcyclic_of_twoSidedCovers
    (fun N => ∃ Z, 𝒵X Z ∧ N = (reflectOne Q Λ hQ hρ).obj (ΦX Z))
    (fun N => ∃ P, 𝒫X P ∧ N = (reflectOne Q Λ hQ hρ).obj (ΦX P))
    (fun N => ∃ Z, 𝒵Y Z ∧ N = ΦY Z) (fun N => ∃ P, 𝒫Y P ∧ N = ΦY P) ?_ ?_ ?_ _
    ⟨Z, hZ, rfl⟩ _ ⟨Z', hZ', rfl⟩
  · rintro N ⟨Z, hZ, rfl⟩
    obtain ⟨S, hS, hK, hP, rfl⟩ := hX Z hZ
    obtain ⟨S', hS', h₁, h₂, h₃⟩ := exists_tensorLayer_shortExact Q Λ hQ h u hS
    refine ⟨S'.map (reflectOne Q Λ hQ hρ), shortExact_map_reflectOne Q Λ hQ hρ hS',
      ⟨S.X₁, hK, by rw [ShortComplex.map_X₁, h₁]⟩, ⟨S.X₂, hP, by rw [ShortComplex.map_X₂, h₂]⟩,
      ⟨eqToIso (by rw [ShortComplex.map_X₃, h₃])⟩⟩
  · rintro N ⟨Z, hZ, rfl⟩
    obtain ⟨S, hS, hK, hP, rfl⟩ := hY Z hZ
    obtain ⟨S', hS', h₁, h₂, h₃⟩ := exists_tensorLayer_shortExact Q Λ hQ h' u' hS
    exact ⟨S', hS', ⟨S.X₁, hK, h₁⟩, ⟨S.X₂, hP, h₂⟩, ⟨eqToIso h₃⟩⟩
  · rintro _ ⟨P, hP, rfl⟩ _ ⟨P', hP', rfl⟩
    obtain ⟨m, hm, hfm⟩ := hPX P hP
    obtain ⟨m', hm', hfm'⟩ := hPY P' hP'
    have hN := hasFiltration_tensorReflect_one hQ hρ
      (hasFiltration_tensorLayer_standard Q Λ hQ h u hfm)
    have hY' := hasFiltration_tensorLayer_standard Q Λ hQ h' u' hfm'
    let : HasDerivedCategory.{w, 0}
        (TensorProductAlgebra k Q (Λ ∘ ⇑(1 : Perm (Fin (ℓ + 1)))) ν) :=
      ‹HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)›
    intro n
    refine isZero_derivedTensorHomology_tensor_of_standardFiltrations hρ hQ 1 DC hN hY' ?_ n
    intro t ht s hs
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hs
    obtain ⟨r, i, hri⟩ := hsep d (hm d hd) d' (hm' d' hd')
    exact fun hc => not_stendhalEquiv_twoPieceLabel_of_blackCount_ne h h' u u' d d' hri
      ⟨hc.2, hc.1⟩


section Inner

variable {m : ℕ} (Λ₂ : Fin (m + 1 + 1) → I →₀ ℕ)
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight (m + 1 + 1) ν))) → List ℕ}
  (hρ₂ : TypeA.IsReducedChoice ρ₂)
  [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ₂) (ν := ν)
      (List.map (1 : Perm (Fin (m + 1 + 1))) (List.finRange (m + 1 + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ₂ ν)]

include hρ₂ in
/-- **Off-diagonal Tor vanishing at the next-to-last red strand** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22; in the S-move, the first term of the
resolution of the right module against the terms of the resolution of the left module before
the last one). Let `λ'` be the first `m + 1` red strands, `θ = θ₁ + β₁` and `θ' = θ₁' + β₁'`
splits at the last red strand of `λ'` with `θ₁ ≠ θ₁'`, and `M`, `M'` finite-dimensional factor
modules of these splits. Then for Rouquier parameters the reflection of
`S(S_{λ'}(M) ⊠ R e(u))` has no Tor against `S(S_{λ'}(M') ⊠ R e(u'))`. Hypotheses: `DC` as in
`isZero_derivedTensorHomology_tensor_of_standardFiltrations`, and the standard filtrations of
the first `m` red strands (`hold`). -/
theorem torAcyclic_reflect_tensorLayer_stdLayer_of_ne {C : QuantumGroup.CartanDatum I}
    (hR : IsRouquierQ C Q)
    (DC : OrderedStandardCovers
      (fun s : {s : Seq (stendhalWeight (m + 1 + 1) ν) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ₂ ν) (leftStandard Q Λ₂ s.1 s.2))
      (fun s => seqIdem Q Λ₂ s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    (hold : HasStandardFiltrations Q ((Λ₂ ∘ Fin.castSucc) ∘ Fin.castSucc))
    {θ β θ' β' : Multiset I} (h : θ + β = ν) (h' : θ' + β' = ν) (u : Seq β) (u' : Seq β')
    {θ₁ β₁ θ₁' β₁' : Multiset I} (h₁ : θ₁ + β₁ = θ) (h₁' : θ₁' + β₁' = θ') (hne : θ₁ ≠ θ₁')
    (M : FactorModule Q (Λ₂ ∘ Fin.castSucc) θ₁ β₁) [FiniteDimensional k M.carrier]
    (M' : FactorModule Q (Λ₂ ∘ Fin.castSucc) θ₁' β₁') [FiniteDimensional k M'.carrier] :
    TorAcyclic.{w} (k := ℤ) ((reflectOne Q Λ₂ hQ hρ₂).obj
        (stdLayerModule Q Λ₂ hQ (tensorLayer Q Λ₂ h
          (stdLayerModule Q (Λ₂ ∘ Fin.castSucc) hQ ⟨θ₁, β₁, h₁, M⟩) (cycProj Q Λ₂ β u))))
      (stdLayerModule Q Λ₂ hQ (tensorLayer Q Λ₂ h'
        (stdLayerModule Q (Λ₂ ∘ Fin.castSucc) hQ ⟨θ₁', β₁', h₁', M'⟩) (cycProj Q Λ₂ β' u'))) := by
  refine torAcyclic_reflect_tensorLayer_of_covers Q Λ₂ hQ hρ₂ DC h h' u u'
    (fun Z => ∃ K : FactorModule Q (Λ₂ ∘ Fin.castSucc) θ₁ β₁, FiniteDimensional k K.carrier ∧
      Z = stdLayerModule Q (Λ₂ ∘ Fin.castSucc) hQ ⟨θ₁, β₁, h₁, K⟩)
    (fun P => ∃ n : ℕ, P = stdOf Q (Λ₂ ∘ Fin.castSucc) hQ h₁
      (Fin (n + 1) → parabolicFactorAlgebra Q (Λ₂ ∘ Fin.castSucc) θ₁ β₁))
    (fun Z => ∃ K : FactorModule Q (Λ₂ ∘ Fin.castSucc) θ₁' β₁', FiniteDimensional k K.carrier ∧
      Z = stdLayerModule Q (Λ₂ ∘ Fin.castSucc) hQ ⟨θ₁', β₁', h₁', K⟩)
    (fun P => ∃ n : ℕ, P = stdOf Q (Λ₂ ∘ Fin.castSucc) hQ h₁'
      (Fin (n + 1) → parabolicFactorAlgebra Q (Λ₂ ∘ Fin.castSucc) θ₁' β₁'))
    {d | ∃ v e, d = twoPieceLabel h₁ v e} {d | ∃ v e, d = twoPieceLabel h₁' v e}
    ?_ ?_ ?_ ?_ ?_ _ ⟨M, inferInstance, rfl⟩ _ ⟨M', inferInstance, rfl⟩
  · rintro Z ⟨K, hK, rfl⟩
    obtain ⟨n, K', hK', S, hS, e₁, e₂, e₃⟩ :=
      exists_stdLayer_freeCover Q (Λ₂ ∘ Fin.castSucc) hQ hR h₁ K
    exact ⟨S, hS, ⟨K', hK', e₁⟩, ⟨n, e₂⟩, e₃⟩
  · rintro Z ⟨K, hK, rfl⟩
    obtain ⟨n, K', hK', S, hS, e₁, e₂, e₃⟩ :=
      exists_stdLayer_freeCover Q (Λ₂ ∘ Fin.castSucc) hQ hR h₁' K
    exact ⟨S, hS, ⟨K', hK', e₁⟩, ⟨n, e₂⟩, e₃⟩
  · rintro P ⟨n, rfl⟩
    obtain ⟨l, hl, hF⟩ := exists_hasFiltration_stdLayer_free Q (Λ₂ ∘ Fin.castSucc) hQ hold h₁ n
    exact ⟨l, hl, hF⟩
  · rintro P ⟨n, rfl⟩
    obtain ⟨l, hl, hF⟩ := exists_hasFiltration_stdLayer_free Q (Λ₂ ∘ Fin.castSucc) hQ hold h₁' n
    exact ⟨l, hl, hF⟩
  · rintro _ ⟨v, e, rfl⟩ _ ⟨v', e', rfl⟩
    obtain ⟨i, hi⟩ : ∃ i, θ₁.count i ≠ θ₁'.count i := by
      by_contra hc
      exact hne (Multiset.ext.mpr fun i => not_not.mp fun hi => hc ⟨i, hi⟩)
    refine ⟨Fin.last m, i, ?_⟩
    rw [blackCount_twoPieceLabel_last, blackCount_twoPieceLabel_last]
    exact hi

end Inner

end Categorification.Stendhal
