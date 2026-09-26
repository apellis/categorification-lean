/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaObjects
import Categorification.Flag.GammaDown
import Categorification.Flag.GammaCups
import StringDiagrams.LocalInterpretation

/-!
# The target of `Γ_N`: the interpretation of the generators of `U(sl_{m+1})` on paths

KL III, arXiv:0807.3250v1, §6.1 (the 2-functor `Γ_N`: eqs. (6.1)–(6.9)).

We build the data `StringDiagrams.Presentation.lift` needs to produce a `K`-linear functor from a
presented category on the signature `psig (slRootDatum m)` of `U(sl_{m+1})` (KL III Definition 3.1
and its variants). `Presentation.lift` needs:

* a category `D` with `[Preadditive D] [Linear K D]` (a *1-category*: the free 2-category of the
  library is the category `Obj S` of 1-cells and diagrams);
* a functor `Obj S ⥤ D`, which the library builds from an `Interpretation`: an object for every
  `Obj S` (a start region and a word of strands, *not necessarily well formed*) and a morphism for
  every well-formed layer `u ⊗ g ⊗ v`;
* `Presentation.Respects`: the functor kills every relation of the presentation after whiskering
  by arbitrary `u`, `v` (with matching regions), and every whiskered interchange law.

We take `D = ModuleCat K` and use `StringDiagrams.LocalInterpretation`, which avoids transporting
morphisms along equalities of objects: all layers act on one ambient module
`V = Π i, M i`, indexed by `ι = Option (valid objects)`:

* `M none = 0`; `M (some a) = RT (gammaR K N a)`, the path bimodule of a valid object as a
  `K`-module (`Categorification.Flag.GammaObjects`);
* an object goes to its own index if valid, to `none` otherwise (`gammaIdx`);
* a layer `L = u ⊗ g ⊗ v` with valid boundaries acts by the bimodule map `layerMap`, the
  generator map `genMap` whiskered by the strands of `u` on the left (`BHom.whiskerLeft`) and
  by the path of `v` on the right (the suffix argument of the local maps), multiplied by a scalar
  `genScal` (`1` except for downward crossings, see below); otherwise it acts by `0`.

The generator maps (`genMap`) are KL III's formulas on the path model:

* dots: multiplication by `ξ` on the strand (`xiStep`, KL III (6.6), (6.7));
* upward crossings: `crossU` (KL III (6.8)); downward crossings: `crossDn` (KL III (6.9)), scaled
  by `dnScal i j`;
* cups and caps: `cupFEW`, `cupEFW` (KL III (6.2), (6.3)), `capFEW`, `capEFW` (KL III (6.4),
  (6.5)), composed with the identification `trS` of the regions to the right of the cup or cap
  (the boundary words of a cup or cap continue from regions that are equal but not
  syntactically equal).

The scalar `dnScal i j : K` on the downward crossing `F_i F_j → F_j F_i` is a parameter: KL III
takes `1`; Cautis–Lauda's normalization of `U_Q(sl_n)` with `t_{ij} = i - j` requires
`t_{ji}^{-1}` for adjacent colours (see the report of the assembly).

## Main definitions

* `dotMap`, `crossMap`, `cupMap`, `capMap`, `genMap`: the generators on a path with arbitrary
  suffix; `layerMap`: a layer.
* `gammaIdx`, `gammaMod`, `gammaOp`, `gammaLI`: the local interpretation;
  `gammaFunctor : Obj (psig (slRootDatum m)) ⥤ ModuleCat K`.
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

/-- The root datum of `sl_{m+1}`, abbreviated. -/
local notation "RD" => slRootDatum m

theorem sh_cancel (b : Bool) (i : Fin m) (r : Wt m) :
    sh (slRootDatum m) (!b, i) + (sh (slRootDatum m) (b, i) + r) = r := by
  have h := sh_dual_add_sh (slRootDatum m) ((b, i) : Letter (Fin m))
  rw [← add_assoc]
  change sh (slRootDatum m) (Letter.dual (b, i)) + sh (slRootDatum m) (b, i) + r = r
  rw [h, zero_add]

/-! ### The generators on paths -/

/-- The bottom boundary of a generator, as a list of colours. -/
abbrev gdom (g : (psig (slRootDatum m)).Gen) : List (WCol m) := (psig (slRootDatum m)).dom g

/-- The top boundary of a generator, as a list of colours. -/
abbrev gcod (g : (psig (slRootDatum m)).Gen) : List (WCol m) := (psig (slRootDatum m)).cod g

section Gens

variable (K N)

/-- **`Γ` of a dot** on the first strand of `c :: right` (KL III (6.6), (6.7)). -/
def dotMap (s : Wt m) (c : WCol m) (right : List (WCol m)) (h : WOK N s (c :: right)) :
    BHom (gammaR K N s (c :: right) h) (gammaR K N s (c :: right) h) :=
  locOne (BHom.mulB (xiStep K c.l (compOf N c.r) (compOf N s) h.step)) (gammaR K N c.r right h.tail)

/-- **`Γ` of a crossing** of the first two strands (KL III (6.8), (6.9)), with rightmost region
`ν` of the crossing. -/
def crossMap : (ε : Bool) → (i j : Fin m) → (ν s : Wt m) → (right : List (WCol m)) →
    (hd : WOK N s (⟨(ε, i), sh RD (ε, j) + ν⟩ :: ⟨(ε, j), ν⟩ :: right)) →
    (hc : WOK N s (⟨(ε, j), sh RD (ε, i) + ν⟩ :: ⟨(ε, i), ν⟩ :: right)) →
    BHom (gammaR K N s _ hd) (gammaR K N s _ hc)
  | true, i, j, ν, _, right, hd, hc =>
    locTwo (crossU K i j hd.step hd.tail.step hc.step hc.tail.step)
      (gammaR K N ν right hd.tail.tail)
  | false, i, j, ν, _, right, hd, hc =>
    locTwo (crossDn K i j hd.step hd.tail.step hc.step hc.tail.step)
      (gammaR K N ν right hd.tail.tail)

/-- **`Γ` of a cup** `1 → c c*` (KL III (6.2), (6.3)) for the colour `c = ⟨(b, i), r⟩`. -/
def cupMap : (b : Bool) → (i : Fin m) → (r s : Wt m) → (right : List (WCol m)) →
    (hd : WOK N s right) →
    (hc : WOK N s (⟨(b, i), r⟩ :: ⟨(!b, i), sh RD (b, i) + r⟩ :: right)) →
    BHom (gammaR K N s right hd) (gammaR K N s _ hc)
  | false, i, r, s, right, hd, hc =>
    (BHom.whiskerLeft (stepB K (false, i) (compOf N r) (compOf N s) hc.step)
      (trS (K := K) (true, i) r s (sh RD (false, i) + r) hc.src.symm right hc.step hc.tail.step
        hd hc.tail.tail)).comp
    (cupFEW K i (hc.step : StepR (true, i) (compOf N s) (compOf N r)) hc.step
      (gammaR K N s right hd))
  | true, i, r, s, right, hd, hc =>
    (BHom.whiskerLeft (stepB K (true, i) (compOf N r) (compOf N s) hc.step)
      (trS (K := K) (false, i) r s (sh RD (true, i) + r) hc.src.symm right hc.step hc.tail.step
        hd hc.tail.tail)).comp
    (cupEFW K i hc.step (hc.step : StepR (false, i) (compOf N s) (compOf N r))
      (gammaR K N s right hd))

/-- **`Γ` of a cap** `c* c → 1` (KL III (6.4), (6.5)) for the colour `c = ⟨(b, i), r⟩`. -/
def capMap : (b : Bool) → (i : Fin m) → (r s : Wt m) → (right : List (WCol m)) →
    (hd : WOK N s (⟨(!b, i), sh RD (b, i) + r⟩ :: ⟨(b, i), r⟩ :: right)) →
    (hc : WOK N s right) →
    BHom (gammaR K N s _ hd) (gammaR K N s right hc)
  | true, i, r, s, right, hd, hc =>
    (capFEW K i (hd.step : StepR (true, i) (compOf N s) (compOf N (sh RD (true, i) + r))) hd.step
      (gammaR K N s right hc)).comp
    (BHom.whiskerLeft (stepB K (false, i) (compOf N (sh RD (true, i) + r)) (compOf N s) hd.step)
      (trS (K := K) (true, i) (sh RD (true, i) + r) r s
        ((sh_cancel true i r).symm.trans hd.src) right hd.tail.step hd.step hd.tail.tail hc))
  | false, i, r, s, right, hd, hc =>
    (capEFW K i hd.step (hd.step : StepR (false, i) (compOf N s) (compOf N (sh RD (false, i) + r)))
      (gammaR K N s right hc)).comp
    (BHom.whiskerLeft (stepB K (true, i) (compOf N (sh RD (false, i) + r)) (compOf N s) hd.step)
      (trS (K := K) (false, i) (sh RD (false, i) + r) r s
        ((sh_cancel false i r).symm.trans hd.src) right hd.tail.step hd.step hd.tail.tail hc))

/-- **`Γ` of a generator** on a path `dom g ++ right` from the region `s`. -/
def genMap (s : Wt m) : (g : (psig RD).Gen) → (right : List (WCol m)) →
    (hd : WOK N s (gdom g ++ right)) →
    (hc : WOK N s (gcod g ++ right)) →
    BHom (gammaR K N s _ hd) (gammaR K N s _ hc)
  | .gen (.dot c), right, hd, _ => dotMap K N s c right hd
  | .gen (.cross ε i j ν), right, hd, hc => crossMap K N ε i j ν s right hd hc
  | .cup ⟨(b, i), r⟩, right, hd, hc => cupMap K N b i r s right hd hc
  | .cap ⟨(b, i), r⟩, right, hd, hc => capMap K N b i r s right hd hc

/-- **`Γ` of a layer** `left ⊗ g ⊗ right` from the region `s`: the generator map whiskered on
the left by the strands of `left`. -/
def layerMap : (s : Wt m) → (left : List (WCol m)) → (g : (psig RD).Gen) →
    (right : List (WCol m)) → (hd : WOK N s (left ++ gdom g ++ right)) →
    (hc : WOK N s (left ++ gcod g ++ right)) →
    BHom (gammaR K N s _ hd) (gammaR K N s _ hc)
  | s, [], g, right, hd, hc => genMap K N s g right hd hc
  | s, c :: left, g, right, hd, hc =>
    BHom.whiskerLeft (stepB K c.l (compOf N c.r) (compOf N s) hd.step)
      (layerMap c.r left g right hd.tail hc.tail)

end Gens

/-! ### The local interpretation -/

section Interp

variable (K N)

/-- The valid objects. -/
abbrev VObj (N m : ℕ) : Type := {a : Obj (psig (slRootDatum m)) // WOK N a.start a.word}

open Classical in
/-- The index of an object: itself if valid, `none` (the zero module) otherwise. -/
def gammaIdx (a : Obj (psig RD)) : Option (VObj N m) :=
  if h : WOK N a.start a.word then some ⟨a, h⟩ else none

theorem gammaIdx_of_wok {a : Obj (psig RD)} (h : WOK N a.start a.word) :
    gammaIdx N a = some ⟨a, h⟩ := dif_pos h

theorem gammaIdx_of_not_wok {a : Obj (psig RD)} (h : ¬ WOK N a.start a.word) :
    gammaIdx N a = none := dif_neg h

/-- The module of an index. -/
def gammaMod : Option (VObj N m) → Type u
  | none => PUnit
  | some a => RT (gammaR K N a.1.start a.1.word a.2)

instance gammaMod.instACG : ∀ i : Option (VObj N m), AddCommGroup (gammaMod K N i)
  | none => inferInstanceAs (AddCommGroup PUnit)
  | some a => inferInstanceAs (AddCommGroup (RT (gammaR K N a.1.start a.1.word a.2)))

instance gammaMod.instModule : ∀ i : Option (VObj N m), Module K (gammaMod K N i)
  | none => inferInstanceAs (Module K PUnit)
  | some a => inferInstanceAs (Module K (RT (gammaR K N a.1.start a.1.word a.2)))

/-- The scalar of a generator: `dnScal i j` for the downward crossing `F_i F_j → F_j F_i`, `1`
otherwise. -/
def genScal (dnScal : Fin m → Fin m → K) : (psig RD).Gen → K
  | .gen (.cross false i j _) => dnScal i j
  | _ => 1

instance VObj.decEq : DecidableEq (VObj N m) := Classical.decEq _

omit [Field K] in
/-- A bimodule map multiplied by a scalar of the right ring. -/
def BHom.csmul {K : Type u} [CommRing K] {A : Type u} [CommRing A] {M M' : BRing A K} (c : K)
    (φ : BHom M M') : BHom M M' :=
  (BHom.mulB (M'.right c)).comp φ

open Classical in
/-- **The operator of a layer** on the ambient module `Π i, M i`: the bimodule map `layerMap`
from the component of the bottom boundary to the component of the top boundary (times
`genScal`), if both are valid; `0` otherwise. -/
def gammaOp (dnScal : Fin m → Fin m → K) (L : Layer (psig RD)) :
    (∀ i : Option (VObj N m), gammaMod K N i) →ₗ[K] (∀ i : Option (VObj N m), gammaMod K N i) :=
  if h : WOK N L.dom.start L.dom.word ∧ WOK N L.cod.start L.cod.word then
    LinearMap.single K (gammaMod K N) (some (⟨L.cod, h.2⟩ : VObj N m)) ∘ₗ
      BHom.toLin (BHom.csmul (genScal K dnScal L.gen)
        (layerMap K N L.start L.left L.gen L.right h.1 h.2)) ∘ₗ
      LinearMap.proj (R := K) (φ := gammaMod K N) (some (⟨L.dom, h.1⟩ : VObj N m))
  else 0

/-- **The local interpretation of `U(sl_{m+1})` on the path model.** -/
def gammaLI (dnScal : Fin m → Fin m → K) :
    LocalInterpretation (psig RD) K (∀ i : Option (VObj N m), gammaMod K N i) (gammaMod (m := m) K N) where
  κ := gammaIdx N
  ext i := LinearMap.single K (gammaMod K N) i
  res i := LinearMap.proj i
  op := gammaOp K N dnScal
  res_comp_ext i := by ext x; simp
  res_op_ext_res L _ := by
    by_cases h : WOK N L.dom.start L.dom.word ∧ WOK N L.cod.start L.cod.word
    · rw [gammaIdx_of_wok N h.1]
      refine LinearMap.ext fun x => ?_
      have e : ∀ (i : Option (VObj N m)) (v : gammaMod K N i),
          (LinearMap.proj (R := K) (φ := gammaMod K N) i) (Pi.single i v) = v := fun i v => by
        rw [LinearMap.proj_apply, Pi.single_eq_same]
      simp only [gammaOp, dif_pos h, LinearMap.comp_apply, LinearMap.coe_single]
      erw [e]
      rfl
    · simp only [gammaOp, dif_neg h, LinearMap.zero_comp, LinearMap.comp_zero]

/-- **`Γ_N` on the free 2-category**: the functor to `K`-modules. -/
def gammaFunctor (dnScal : Fin m → Fin m → K) : Obj (psig RD) ⥤ ModuleCat.{u} K :=
  (gammaLI K N dnScal).functor

end Interp

end Categorification.Flag

end
