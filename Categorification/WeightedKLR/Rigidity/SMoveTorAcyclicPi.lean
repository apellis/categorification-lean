/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveStandardizationTor
import Categorification.Algebra.DerivedTensorCoefficientAcyclicCover
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingletons

/-!
# Tor-acyclicity of finite products

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c). The terms of the resolutions of Proposition 7.8 are finite sums
`StdSum` of standardizations (`exists_stdResolution`). Tor-acyclicity of `N ⊗ᴸ_B Y` passes to
finite products in each argument: by induction on the index type, through the split short exact
sequence `0 → Y_∗ → ∏_{Option J} Y → ∏_J Y → 0` and the extension lemmas
`TorAcyclic.of_shortExact` and `TorAcyclic.of_coefficient_shortExact`.

## Main results

* `TorAcyclic.of_subsingleton`: the zero module is Tor-acyclic.
* `TorAcyclic.pi`: a finite product of Tor-acyclic modules is Tor-acyclic.
* `TorAcyclic.pi_coefficient`: the same in the coefficient, over `ℤ`.
* `TorAcyclic.pi_pi`: both at once.
* `TorAcyclic.map_pi`, `TorAcyclic.map_pi_coefficient`: the same after an exact functor
  (`ModuleExactFunctor`), e.g. the S-move functors `SMove.leftStd` and `SMove.rightStd`
  applied to a sum `StdSum`, without a product comparison for the functor.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w

/-! ### The split sequence of a product over `Option J` -/

section Split

variable {R : Type} [Ring R] {J : Type} [DecidableEq J] (Y : Option J → ModuleCat.{0} R)

/-- The short complex `Y_none → ∏_{Option J} Y → ∏_J Y ∘ some`. -/
def piOptionShortComplex : ShortComplex (ModuleCat.{0} R) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.single R (fun o => Y o) none) :
      Y none ⟶ ModuleCat.of R (∀ o, Y o))
    (ModuleCat.ofHom (LinearMap.pi fun j => LinearMap.proj (some j)) :
      ModuleCat.of R (∀ o, Y o) ⟶ ModuleCat.of R (∀ j, Y (some j)))
    (by
      ext x j
      change (Pi.single none x : ∀ o, Y o) (some j) = 0
      exact Pi.single_eq_of_ne (Option.some_ne_none j) x)

theorem piOptionShortComplex_shortExact : (piOptionShortComplex Y).ShortExact := by
  have hex : Function.Exact (LinearMap.single R (fun o => Y o) none)
      (LinearMap.pi fun j => LinearMap.proj (some j) : (∀ o, Y o) →ₗ[R] ∀ j, Y (some j)) := by
    intro x
    constructor
    · intro hx
      refine ⟨x none, ?_⟩
      funext o
      cases o with
      | none => exact Pi.single_eq_same (M := fun o => Y o) none (x none)
      | some j =>
        change (Pi.single none (x none) : ∀ o, Y o) (some j) = x (some j)
        rw [Pi.single_eq_of_ne (Option.some_ne_none j)]
        exact (congrFun hx j).symm
    · rintro ⟨y, rfl⟩
      funext j
      change (Pi.single none y : ∀ o, Y o) (some j) = 0
      exact Pi.single_eq_of_ne (Option.some_ne_none j) y
  have hinj : Function.Injective (LinearMap.single R (fun o => Y o) none) := fun a b h => by
    have := congrFun h none
    change (Pi.single none a : ∀ o, Y o) none = (Pi.single none b : ∀ o, Y o) none at this
    simpa using this
  have hsurj : Function.Surjective
      (LinearMap.pi fun j => LinearMap.proj (some j) : (∀ o, Y o) →ₗ[R] ∀ j, Y (some j)) :=
    fun y => ⟨fun o => Option.rec (motive := fun o => Y o) 0 (fun j => y j) o, rfl⟩
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hex)
    ((ModuleCat.mono_iff_injective _).mpr hinj) ((ModuleCat.epi_iff_surjective _).mpr hsurj)

/-- Reindexing a product along an equivalence of index types. -/
def piCongrLeftIso {J' : Type} (e : J ≃ J') (Y : J' → ModuleCat.{0} R) :
    ModuleCat.of R (∀ j, Y (e j)) ≅ ModuleCat.of R (∀ j', Y j') :=
  (LinearEquiv.piCongrLeft R (fun j' => Y j') e).toModuleIso

end Split

/-! ### Exact functors -/

section ExactFunctor

variable {R S : Type} [Ring R] [Ring S] {F : ModuleCat.{0} R ⥤ ModuleCat.{0} S}
  (hF : ModuleExactFunctor F)

/-- The image of a short exact sequence under an exact functor, with the vanishing of the
composite read off from exactness (no `PreservesZeroMorphisms` instance is needed). -/
def exactMapShortComplex (X : ShortComplex (ModuleCat.{0} R)) (hX : X.ShortExact) :
    ShortComplex (ModuleCat.{0} S) :=
  ShortComplex.mk (F.map X.f) (F.map X.g) (by
    ext x
    exact (hF.exact X.f X.g
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact X).mp hX.exact))
        |>.apply_apply_eq_zero x)

theorem exactMapShortComplex_shortExact (X : ShortComplex (ModuleCat.{0} R))
    (hX : X.ShortExact) : (exactMapShortComplex hF X hX).ShortExact :=
  ShortComplex.ShortExact.mk'
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (hF.exact X.f X.g
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact X).mp hX.exact)))
    ((ModuleCat.mono_iff_injective _).mpr
      (hF.injective X.f ((ModuleCat.mono_iff_injective X.f).mp hX.mono_f)))
    ((ModuleCat.epi_iff_surjective _).mpr
      (hF.surjective X.g ((ModuleCat.epi_iff_surjective X.g).mp hX.epi_g)))

include hF in
/-- An exact functor sends the zero module to a zero module. -/
theorem subsingleton_obj_of_subsingleton (X : ModuleCat.{0} R) [Subsingleton X] :
    Subsingleton (F.obj X) := by
  have h := hF.exact (𝟙 X) (𝟙 X) fun x => ⟨fun _ => ⟨x, rfl⟩, fun _ => Subsingleton.elim _ _⟩
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have := (h a).2 ⟨a, by rw [F.map_id]; rfl⟩
    rwa [F.map_id] at this
  have hb : b = 0 := by
    have := (h b).2 ⟨b, by rw [F.map_id]; rfl⟩
    rwa [F.map_id] at this
  rw [ha, hb]

end ExactFunctor

/-! ### The module argument -/

section Module

variable {k B : Type} [CommRing k] [Ring B] [HasDerivedCategory.{w, 0} k]
  [HasDerivedCategory.{w, 0} B]
  (N : Type) [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N] [SMulCommClass k Bᵐᵒᵖ N]

/-- **The zero module is Tor-acyclic.** -/
theorem TorAcyclic.of_subsingleton (Y : ModuleCat.{0} B) [Subsingleton Y] :
    TorAcyclic.{w} (k := k) N Y := fun n => by
  have : Subsingleton ((degreeZeroModuleFunctor B).obj Y) := inferInstanceAs (Subsingleton Y)
  exact (homologyFunctor (A := k) k n).map_isZero ((derivedTensor.{w} k B N).map_isZero
    (Q.map_isZero (DGModuleCat.isZero_of_subsingleton ((degreeZeroModuleFunctor B).obj Y))))

/-- **A finite product of Tor-acyclic modules is Tor-acyclic.** -/
theorem TorAcyclic.pi {J : Type} [Finite J] (Y : J → ModuleCat.{0} B)
    (h : ∀ j, TorAcyclic.{w} (k := k) N (Y j)) :
    TorAcyclic.{w} (k := k) N (ModuleCat.of B (∀ j, Y j)) := by
  have := Fintype.ofFinite J
  revert Y
  refine Fintype.induction_empty_option
    (P := fun J _ => ∀ Y : J → ModuleCat.{0} B, (∀ j, TorAcyclic.{w} (k := k) N (Y j)) →
      TorAcyclic.{w} (k := k) N (ModuleCat.of B (∀ j, Y j))) ?_ ?_ ?_ J
  · intro α β _ e hα Y hY
    exact TorAcyclic.of_iso N (piCongrLeftIso e Y) (hα (fun a => Y (e a)) fun a => hY (e a))
  · intro Y _
    have : Subsingleton (∀ j : PEmpty, Y j) := inferInstance
    exact TorAcyclic.of_subsingleton N (ModuleCat.of B (∀ j, Y j))
  · intro α _ hα Y hY
    let _ : DecidableEq α := Classical.decEq α
    have h := TorAcyclic.of_shortExact (k := k) N (piOptionShortComplex_shortExact Y) (hY none)
    exact h (hα (fun j => Y (some j)) fun j => hY (some j))

/-- **Tor-acyclicity of the image of a finite product under an exact functor**: if
`N ⊗ᴸ_B F(Y_j)` is acyclic for every `j`, so is `N ⊗ᴸ_B F(∏ Y_j)`. -/
theorem TorAcyclic.map_pi {R : Type} [Ring R] {F : ModuleCat.{0} R ⥤ ModuleCat.{0} B}
    (hF : ModuleExactFunctor F) {J : Type} [Finite J] (Y : J → ModuleCat.{0} R)
    (h : ∀ j, TorAcyclic.{w} (k := k) N (F.obj (Y j))) :
    TorAcyclic.{w} (k := k) N (F.obj (ModuleCat.of R (∀ j, Y j))) := by
  have := Fintype.ofFinite J
  revert Y
  refine Fintype.induction_empty_option
    (P := fun J _ => ∀ Y : J → ModuleCat.{0} R, (∀ j, TorAcyclic.{w} (k := k) N (F.obj (Y j))) →
      TorAcyclic.{w} (k := k) N (F.obj (ModuleCat.of R (∀ j, Y j)))) ?_ ?_ ?_ J
  · intro α β _ e hα Y hY
    exact TorAcyclic.of_iso N (F.mapIso (piCongrLeftIso e Y))
      (hα (fun a => Y (e a)) fun a => hY (e a))
  · intro Y _
    have : Subsingleton (ModuleCat.of R (∀ j : PEmpty, Y j)) :=
      inferInstanceAs (Subsingleton (∀ j : PEmpty, Y j))
    have := subsingleton_obj_of_subsingleton hF (ModuleCat.of R (∀ j : PEmpty, Y j))
    exact TorAcyclic.of_subsingleton N _
  · intro α _ hα Y hY
    let _ : DecidableEq α := Classical.decEq α
    have h := TorAcyclic.of_shortExact (k := k) N (exactMapShortComplex_shortExact hF _
      (piOptionShortComplex_shortExact Y)) (hY none)
    exact h (hα (fun j => Y (some j)) fun j => hY (some j))

end Module

/-! ### The coefficient argument -/

section Coefficient

variable {B : Type} [Ring B] [HasDerivedCategory.{w, 0} ℤ] [HasDerivedCategory.{w, 0} B]

/-- **A finite product of Tor-acyclic coefficients is Tor-acyclic** (over `ℤ`). -/
theorem TorAcyclic.pi_coefficient (Y : ModuleCat.{0} B) {J : Type} [Finite J]
    (N : J → ModuleCat.{0} Bᵐᵒᵖ) (h : ∀ j, TorAcyclic.{w} (k := ℤ) (N j) Y) :
    TorAcyclic.{w} (k := ℤ) (ModuleCat.of Bᵐᵒᵖ (∀ j, N j)) Y := by
  have := Fintype.ofFinite J
  revert N
  refine Fintype.induction_empty_option
    (P := fun J _ => ∀ N : J → ModuleCat.{0} Bᵐᵒᵖ, (∀ j, TorAcyclic.{w} (k := ℤ) (N j) Y) →
      TorAcyclic.{w} (k := ℤ) (ModuleCat.of Bᵐᵒᵖ (∀ j, N j)) Y) ?_ ?_ ?_ J
  · intro α β _ e hα N hN
    exact TorAcyclic.of_coefficient_iso Y (piCongrLeftIso e N)
      (hα (fun a => N (e a)) fun a => hN (e a))
  · intro N _
    have : Subsingleton (ModuleCat.of Bᵐᵒᵖ (∀ j : PEmpty, N j)) :=
      inferInstanceAs (Subsingleton (∀ j : PEmpty, N j))
    exact TorAcyclic.of_subsingleton_coefficient Y _
  · intro α _ hα N hN
    let _ : DecidableEq α := Classical.decEq α
    have h := TorAcyclic.of_coefficient_shortExact Y (piOptionShortComplex_shortExact N) (hN none)
    exact h (hα (fun j => N (some j)) fun j => hN (some j))

/-- **Tor-acyclicity of products in both arguments** (over `ℤ`): if `N_i ⊗ᴸ_B Y_j` is acyclic
for all `i, j`, so is `(∏ N_i) ⊗ᴸ_B (∏ Y_j)`. -/
theorem TorAcyclic.pi_pi {I J : Type} [Finite I] [Finite J] (N : I → ModuleCat.{0} Bᵐᵒᵖ)
    (Y : J → ModuleCat.{0} B) (h : ∀ i j, TorAcyclic.{w} (k := ℤ) (N i) (Y j)) :
    TorAcyclic.{w} (k := ℤ) (ModuleCat.of Bᵐᵒᵖ (∀ i, N i)) (ModuleCat.of B (∀ j, Y j)) :=
  TorAcyclic.pi_coefficient _ N fun i => TorAcyclic.pi _ Y (h i)

/-- **Tor-acyclicity of the image of a finite product of coefficients under an exact
functor** (over `ℤ`). -/
theorem TorAcyclic.map_pi_coefficient (Y : ModuleCat.{0} B) {R : Type} [Ring R]
    {F : ModuleCat.{0} R ⥤ ModuleCat.{0} Bᵐᵒᵖ} (hF : ModuleExactFunctor F) {J : Type}
    [Finite J] (N : J → ModuleCat.{0} R) (h : ∀ j, TorAcyclic.{w} (k := ℤ) (F.obj (N j)) Y) :
    TorAcyclic.{w} (k := ℤ) (F.obj (ModuleCat.of R (∀ j, N j))) Y := by
  have := Fintype.ofFinite J
  revert N
  refine Fintype.induction_empty_option
    (P := fun J _ => ∀ N : J → ModuleCat.{0} R, (∀ j, TorAcyclic.{w} (k := ℤ) (F.obj (N j)) Y) →
      TorAcyclic.{w} (k := ℤ) (F.obj (ModuleCat.of R (∀ j, N j))) Y) ?_ ?_ ?_ J
  · intro α β _ e hα N hN
    exact TorAcyclic.of_coefficient_iso Y (F.mapIso (piCongrLeftIso e N))
      (hα (fun a => N (e a)) fun a => hN (e a))
  · intro N _
    have : Subsingleton (ModuleCat.of R (∀ j : PEmpty, N j)) :=
      inferInstanceAs (Subsingleton (∀ j : PEmpty, N j))
    have := subsingleton_obj_of_subsingleton hF (ModuleCat.of R (∀ j : PEmpty, N j))
    exact TorAcyclic.of_subsingleton_coefficient Y _
  · intro α _ hα N hN
    let _ : DecidableEq α := Classical.decEq α
    have h := TorAcyclic.of_coefficient_shortExact Y (exactMapShortComplex_shortExact hF _
      (piOptionShortComplex_shortExact N)) (hN none)
    exact h (hα (fun j => N (some j)) fun j => hN (some j))

end Coefficient

end Categorification.Stendhal
