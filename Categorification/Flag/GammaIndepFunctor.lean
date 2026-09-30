/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaIndepShadow
import Categorification.Flag.GammaEval
import Categorification.Diagrams.CL.RescaleBasic

/-!
# `Γ_N`-like functors and their values on diagrams

Auxiliary material for the nondegeneracy argument of Khovanov–Lauda III (arXiv:0807.3250v1,
§6.4, TeX `sln-2008-ArXiv.tex` l. 9598–9790).

The 2-representation `Γ_N` is used through a linear functor `F` out of a presented category of
string diagrams which, on every diagram `f`, is `Γ_N` of a transformed diagram `ιF f` times a
unit (`GammaLike`): this covers `Γ_N` itself (after the rescaling isomorphism `Σ` of KL III
§4.2.1, whose units are the `weight`s of the diagrams) and its composite with the embedding
`U(sl_n) → U(sl_{n+1})` used to reach arbitrary characteristic.

* `toMod`: the element of `Γ_N(a)` (as the value `gammaFunctor.obj a` of the functor of the free
  2-category) given by an element of the path bimodule of a valid object `a`.
* `gammaFunctor_map_toMod`: on valid objects, `gammaFunctor.map f` is the chain map `chainBD`
  of the layers of `f`.
* `GammaLike.map_toF`: the same for a `GammaLike` functor, up to the unit.
-/

noncomputable section

namespace Categorification.Flag.Indep

open Categorification.Flag Categorification.KL3.Diagram StringDiagrams CategoryTheory

universe u w₀ w₁ w₂

variable {K : Type u} [Field K] {m N : ℕ}

local notation "RD" => slRootDatum m

/-! ## Modules of equal indices -/

/-- The identification of the modules of equal indices. -/
def modCast {i j : Option (VObj N m)} (e : i = j) : gammaMod K N i →ₗ[K] gammaMod K N j :=
  e ▸ LinearMap.id

theorem single_modCast {i j : Option (VObj N m)} (e : i = j) (y : gammaMod K N i) :
    LinearMap.single K (gammaMod K N) j (modCast e y) = LinearMap.single K (gammaMod K N) i y := by
  subst e; rfl

theorem proj_modCast {i j : Option (VObj N m)} (e : i = j)
    (v : ∀ l : Option (VObj N m), gammaMod K N l) :
    LinearMap.proj (R := K) (φ := gammaMod K N) j v =
      modCast e (LinearMap.proj (R := K) (φ := gammaMod K N) i v) := by
  subst e; rfl

variable (K N) in
/-- An element of the path bimodule of a valid object, as an element of `Γ_N(a)`. -/
def toMod (a : Obj (psig RD)) (ha : WOK N a.start a.word) :
    RT (gammaR K N a.start a.word ha) →ₗ[K] gammaMod K N (gammaIdx N a) :=
  modCast (gammaIdx_of_wok N ha).symm

/-! ## `gammaFunctor` on diagrams with valid ends -/

/-- The layer data of a layer. -/
def dat (L : Layer (psig RD)) : LData m := (L.left, L.gen, L.right)

theorem chainW_dat : ∀ {a b : Obj (psig RD)} {ls : List (Layer (psig RD))}, Chain a ls b →
    ChainW a.word (ls.map dat) b.word
  | _, _, [], h => by subst h; rfl
  | _, _, L :: ls, ⟨_, hd, hc⟩ => by
    subst hd
    exact ⟨rfl, chainW_dat hc⟩

theorem layers_eq_toLayer : ∀ {a b : Obj (psig RD)} {ls : List (Layer (psig RD))}, Chain a ls b →
    ls = (ls.map dat).map (LData.toLayer a.start)
  | _, _, [], _ => rfl
  | _, _, L :: ls, ⟨_, hd, hc⟩ => by
    subst hd
    exact congrArg₂ List.cons rfl (layers_eq_toLayer (a := L.cod) hc)

/-- The identification of path bimodules with equal start regions. -/
def startCast {s s' : Wt m} (e : s = s') (w : List (WCol m)) (h : WOK N s w) (h' : WOK N s' w) :
    RT (gammaR K N s w h) →ₗ[K] RT (gammaR K N s' w h') := by
  subst e; exact LinearMap.id

theorem startCast_rfl {s : Wt m} (e : s = s) (w : List (WCol m)) (h h' : WOK N s w)
    (y : RT (gammaR K N s w h)) : startCast e w h h' y = y := rfl

theorem chain_start : ∀ {a b : Obj (psig RD)} {ls : List (Layer (psig RD))}, Chain a ls b →
    a.start = b.start
  | _, _, [], h => by subst h; rfl
  | _, _, L :: ls, ⟨_, hd, hc⟩ => by subst hd; exact chain_start (a := L.cod) hc

theorem wok_start {a b : Obj (psig RD)} (f : a ⟶ b) (hb : WOK N b.start b.word) :
    WOK N a.start b.word := by rw [chain_start (Diagram.chain f)]; exact hb

set_option backward.isDefEq.respectTransparency false in
/-- **On valid objects, `Γ_N` of a diagram is the chain map of its layers.** -/
theorem gammaFunctor_map_toMod (dnScal : Fin m → Fin m → K) {a b : Obj (psig RD)} (f : a ⟶ b)
    (ha : WOK N a.start a.word) (hb : WOK N b.start b.word)
    (x : RT (gammaR K N a.start a.word ha)) :
    ((gammaFunctor K N dnScal).map f).hom (toMod K N a ha x) =
      toMod K N b hb (startCast (chain_start (Diagram.chain f)) b.word (wok_start f hb) hb
        (BHom.toLin (chainBD K N dnScal a.start a.word ((Diagram.layers f).map dat)
        b.word (chainW_dat (Diagram.chain f)) ha (wok_start f hb)) x)) := by
  obtain ⟨bs, bw⟩ := b
  have hs : a.start = bs := chain_start (Diagram.chain f)
  obtain ⟨as, aw⟩ := a
  simp only at hs
  subst hs
  erw [LocalInterpretation.functor_map_apply]
  show LinearMap.proj (R := K) (φ := gammaMod K N) (gammaIdx N ⟨as, bw⟩)
      ((gammaLI K N dnScal).opList (Diagram.layers f)
        (LinearMap.single K (gammaMod K N) (gammaIdx N ⟨as, aw⟩) (toMod K N _ ha x))) = _
  erw [single_modCast]
  rw [proj_modCast (gammaIdx_of_wok N hb).symm]
  have key := opList_chain (K := K) (N := N) dnScal as aw ((Diagram.layers f).map dat)
    bw (chainW_dat (Diagram.chain f)) ha hb
  rw [← layers_eq_toLayer (Diagram.chain f)] at key
  have k2 := LinearMap.congr_fun key x
  simp only [LinearMap.comp_apply] at k2
  rw [toMod, startCast_rfl]
  exact congrArg _ k2

/-! ## `Γ_N`-like functors -/

variable {S₀ : Signature.{w₀, w₁, w₂}} {P₀ : Presentation S₀ K}

/-- `F` is **`Γ_N`-like**: on objects it is `Γ_N ∘ ιF`, and on a diagram `f` it is `Γ_N (ιF f)`
times the unit `weight χ` of the layers of `ιF f` (`Categorification.KL3.Diagram.CL.Rescale.weight`). -/
structure GammaLike (F : P₀.Presented ⥤ ModuleCat.{u} K) (ιF : Obj S₀ ⥤ Obj (psig (slRootDatum m))) (N : ℕ)
    (dnScal : Fin m → Fin m → K) (χ : (psig (slRootDatum m)).Gen → Kˣ) : Prop where
  obj : ∀ a, F.obj (P₀.obj a) = (gammaFunctor K N dnScal).obj (ιF.obj a)
  map : ∀ {a b : Obj S₀} (f : a ⟶ b), F.map (P₀.diag f) = eqToHom (obj a) ≫
    (((CL.Rescale.weight χ (Diagram.layers (ιF.map f)) : Kˣ) : K) •
      (gammaFunctor K N dnScal).map (ιF.map f)) ≫ eqToHom (obj b).symm

variable {F : P₀.Presented ⥤ ModuleCat.{u} K} {ιF : Obj S₀ ⥤ Obj (psig (slRootDatum m))}
  {dnScal : Fin m → Fin m → K} {χ : (psig (slRootDatum m)).Gen → Kˣ}

namespace GammaLike

variable (hF : GammaLike F ιF N dnScal χ)

/-- An element of the path bimodule of `ιF a`, as an element of `F(a)`. -/
def toF (a : Obj S₀) (ha : WOK N (ιF.obj a).start (ιF.obj a).word) :
    RT (gammaR K N (ιF.obj a).start (ιF.obj a).word ha) →ₗ[K] F.obj (P₀.obj a) :=
  (eqToHom (hF.obj a).symm).hom ∘ₗ toMod K N (ιF.obj a) ha

set_option backward.isDefEq.respectTransparency false in
include hF in
/-- **`F` on a diagram with valid ends**: `unit • ` the chain map of the layers of `ιF f`. -/
theorem map_toF {a b : Obj S₀} (f : a ⟶ b) (ha : WOK N (ιF.obj a).start (ιF.obj a).word)
    (hb : WOK N (ιF.obj b).start (ιF.obj b).word)
    (x : RT (gammaR K N (ιF.obj a).start (ιF.obj a).word ha)) :
    (F.map (P₀.diag f)).hom (hF.toF a ha x) =
      ((CL.Rescale.weight χ (Diagram.layers (ιF.map f)) : Kˣ) : K) •
        hF.toF b hb (startCast (chain_start (Diagram.chain (ιF.map f))) (ιF.obj b).word
          (wok_start (ιF.map f) hb) hb
          (BHom.toLin (chainBD K N dnScal (ιF.obj a).start (ιF.obj a).word
          ((Diagram.layers (ιF.map f)).map dat) (ιF.obj b).word
          (chainW_dat (Diagram.chain (ιF.map f))) ha (wok_start (ιF.map f) hb)) x)) := by
  have h1 : (F.map (P₀.diag f)).hom (hF.toF a ha x) =
      (eqToHom (hF.obj a).symm ≫ F.map (P₀.diag f)).hom (toMod K N (ιF.obj a) ha x) := rfl
  rw [h1, hF.map f, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply,
    gammaFunctor_map_toMod _ _ _ hb, map_smul]
  rfl

/-- The elements `evXi q * iotaE z` (a polynomial in the dots times an element of the rightmost
region), in `F(a)`. -/
def pvec (a : Obj S₀) (ha : WOK N (ιF.obj a).start (ιF.obj a).word) (μ : Wt m)
    (e : lastR (ιF.obj a).start (ιF.obj a).word = μ) (q : MvPolynomial ℕ K)
    (z : H K (compOf N μ)) : F.obj (P₀.obj a) :=
  hF.toF a ha (evXi (ιF.obj a).start (ιF.obj a).word ha q * iotaE _ _ ha μ e z)

set_option backward.isDefEq.respectTransparency false in
theorem pvec_add (a : Obj S₀) (ha : WOK N (ιF.obj a).start (ιF.obj a).word) (μ : Wt m)
    (e : lastR (ιF.obj a).start (ιF.obj a).word = μ) (q q' : MvPolynomial ℕ K)
    (z : H K (compOf N μ)) : hF.pvec a ha μ e (q + q') z = hF.pvec a ha μ e q z + hF.pvec a ha μ e q' z := by
  simp only [pvec, map_add, add_mul]

set_option backward.isDefEq.respectTransparency false in
theorem pvec_smul (a : Obj S₀) (ha : WOK N (ιF.obj a).start (ιF.obj a).word) (μ : Wt m)
    (e : lastR (ιF.obj a).start (ιF.obj a).word = μ) (c : K) (q : MvPolynomial ℕ K)
    (z : H K (compOf N μ)) : hF.pvec a ha μ e (MvPolynomial.C c * q) z = c • hF.pvec a ha μ e q z := by
  simp only [pvec, map_mul, evXi_C, mul_assoc]
  rw [← map_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pvec_zero (a : Obj S₀) (ha : WOK N (ιF.obj a).start (ιF.obj a).word) (μ : Wt m)
    (e : lastR (ιF.obj a).start (ιF.obj a).word = μ) (z : H K (compOf N μ)) :
    hF.pvec a ha μ e 0 z = 0 := by
  simp [pvec]

set_option backward.isDefEq.respectTransparency false in
/-- The shadow of a chain of one layer. -/
theorem shadow_chainBD_one {s : Wt m} {w w' : List (WCol m)} (L : Layer (psig (slRootDatum m)))
    (h : ChainW w [dat L] w') (ha : WOK N s w) (hb : WOK N s w') {μ : Wt m} (e : lastR s w = μ)
    (e' : lastR s w' = μ) {op : MvPolynomial ℕ K → MvPolynomial ℕ K}
    (hS : ∀ hd hc (e₁ : lastR s (L.left ++ gdom L.gen ++ L.right) = μ)
      (e₂ : lastR s (L.left ++ gcod L.gen ++ L.right) = μ),
      Shadow μ e₁ e₂ (layerMap K N s L.left L.gen L.right hd hc) op)
    (hg : genScal K dnScal L.gen = 1) :
    Shadow μ e e' (chainBD K N dnScal s w [dat L] w' h ha hb) op := by
  obtain ⟨h1, h2⟩ := h
  have hL : WOK N s (L.left ++ gcod L.gen ++ L.right) := h2 ▸ hb
  have e₁ : lastR s (L.left ++ gdom L.gen ++ L.right) = μ := h1 ▸ e
  have e₂ : lastR s (L.left ++ gcod L.gen ++ L.right) = μ := h2 ▸ e'
  simp only [chainBD, dat, dite_eq_left hL, hg]
  have := (shadow_trW (K := K) h1 ha (h1 ▸ ha) e e₁).comp
    (((hS (h1 ▸ ha) hL e₁ e₂).csmul (1 : K)).comp
      (shadow_trW (K := K) h2 hL hb e₂ e'))
  simpa [Function.comp_def, BHom.comp_assoc] using this

theorem shadow_startCast {s s' : Wt m} (es : s = s') (w : List (WCol m)) (h : WOK N s w)
    (h' : WOK N s' w) {μ : Wt m} (e : lastR s w = μ) (e' : lastR s' w = μ) (q : MvPolynomial ℕ K)
    (z : H K (compOf N μ)) :
    startCast es w h h' (evXi s w h q * iotaE s w h μ e z) = evXi s' w h' q * iotaE s' w h' μ e' z := by
  subst es; rfl

set_option backward.isDefEq.respectTransparency false in
/-- **`F` on a diagram of one layer with a polynomial shadow.** -/
theorem map_pvec {a b : Obj S₀} (f : a ⟶ b) (L : Layer (psig (slRootDatum m)))
    (hL : Diagram.layers (ιF.map f) = [L]) (ha : WOK N (ιF.obj a).start (ιF.obj a).word)
    (hb : WOK N (ιF.obj b).start (ιF.obj b).word) {μ : Wt m}
    (e : lastR (ιF.obj a).start (ιF.obj a).word = μ) (e' : lastR (ιF.obj b).start (ιF.obj b).word = μ)
    {op : MvPolynomial ℕ K → MvPolynomial ℕ K}
    (hS : ∀ hd hc (e₁ : lastR (ιF.obj a).start (L.left ++ gdom L.gen ++ L.right) = μ)
      (e₂ : lastR (ιF.obj a).start (L.left ++ gcod L.gen ++ L.right) = μ),
      Shadow μ e₁ e₂ (layerMap K N (ιF.obj a).start L.left L.gen L.right hd hc) op)
    (hg : genScal K dnScal L.gen = 1) (q : MvPolynomial ℕ K) (z : H K (compOf N μ)) :
    (F.map (P₀.diag f)).hom (hF.pvec a ha μ e q z) = (χ L.gen : K) • hF.pvec b hb μ e' (op q) z := by
  rw [pvec, hF.map_toF f ha hb]
  have hw : CL.Rescale.weight χ (Diagram.layers (ιF.map f)) = χ L.gen := by
    rw [hL]; simp [CL.Rescale.weight]
  rw [hw]
  congr 2
  have es := chain_start (Diagram.chain (ιF.map f))
  have e'' : lastR (ιF.obj a).start (ιF.obj b).word = μ := by rw [es]; exact e'
  have key : ∀ (ls : List (LData m)) (hls : ls = [dat L]) (hch : ChainW (ιF.obj a).word ls (ιF.obj b).word),
      BHom.toLin (chainBD K N dnScal (ιF.obj a).start (ιF.obj a).word ls (ιF.obj b).word hch ha
        (wok_start (ιF.map f) hb)) (evXi _ _ ha q * iotaE _ _ ha μ e z) =
      evXi _ _ (wok_start (ιF.map f) hb) (op q) * iotaE _ _ (wok_start (ιF.map f) hb) μ e'' z := by
    intro ls hls hch
    subst hls
    exact shadow_chainBD_one L hch ha _ e e'' hS hg q z
  rw [key _ (by rw [hL]; rfl), shadow_startCast es _ _ hb e'' e']

end GammaLike

end Categorification.Flag.Indep

end
