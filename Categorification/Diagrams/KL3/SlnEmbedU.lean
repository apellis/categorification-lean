/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SlnEmbed
import Categorification.Diagrams.KL3.SlideCalculus
import Categorification.Diagrams.CL.RescaleBasic
import StringDiagrams.LayerMap.Generators

/-!
# The 2-functor `U(sl_{m+1}) → U(sl_{m+2})`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1 (TeX source
`sln-2008-ArXiv.tex`), Definition 3.1 (label `def_Ucat`). This file completes the auxiliary
construction of `Categorification.KL3.Diagram.SlnEmbed` used in the proof of Theorem 1.3
(label `thm-nondegenerate`, §6.4) in arbitrary characteristic: the relabelling `ιF` of the free
2-categories (vertices of `sl_{m+1}` as the first `m` vertices of `sl_{m+2}`, weights by
`phiW`) descends to the presented 2-categories.

The relabelling is a map of signatures (`embSig`, a `StringDiagrams.SigMap`), so by the
library's soundness theorem `StringDiagrams.SigMap.lift` it suffices to check that the image of
every defining relation of `U(sl_{m+1})` holds in `U(sl_{m+2})`. In fact every relation is sent
to the corresponding relation (retyped along `ιO_ob`): the relations only depend on the root
datum through `⟨i, λ⟩`, which is preserved (`ip_phiW`), and the KLR polynomials `Q_{ij}`, which
only depend on the Cartan matrix of the vertices involved (`slCartan_dot_castSucc`).

## Main definitions and results

* `embSig m`: the map of signatures (regions `phiW`, strands `ιC`, generators `ιG`);
* `klrSig m`: the relabelling `Fin m → Fin (m + 1)` of the KLR signature, and
  `klrSig_lin_relation`: it sends the KLR relations for `Q = klQ2 (slCartan m)` to those for
  `klQ2 (slCartan (m + 1))`;
* `Ψ`: the relabelling of linear combinations of diagrams between normal-form objects, with
  `Ψ_comp`, `Ψ_of_mkD` and its values on the diagrams of Definition 3.1 (bubbles, fake bubbles,
  curls, the decompositions);
* `lin_embSig_rel`: every defining relation of `pres (slRootDatum m) K` is sent to zero;
* **`embedU K m : (pres (slRootDatum m) K).Presented ⥤ (pres (slRootDatum (m + 1)) K).Presented`**,
  `K`-linear, with `embedU_obj` and `embedU_diag` (on a diagram `d` it is the class of `ιD d`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.SlnEmbed

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Categorification.Flag

universe w

/-! ## Generic facts on layer maps and retyping -/

section Generic

universe u₀ u₁ u₂ u₀' u₁' u₂'

variable {S : Signature.{u₀, u₁, u₂}} {S' : Signature.{u₀', u₁', u₂'}} {R : Type w} [CommRing R]

theorem _root_.StringDiagrams.LayerMap.lin_zero' (φ : LayerMap S S') {a b : Obj S} :
    φ.lin (0 : LinDiagram R a b) = 0 := Finsupp.mapDomain_zero

theorem _root_.StringDiagrams.LayerMap.lin_comp' (φ : LayerMap S S') {a b c : Obj S} (f : LinDiagram R a b)
    (g : LinDiagram R b c) : φ.lin (f ≫ g) = φ.lin f ≫ φ.lin g := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, φ.lin_zero', φ.lin_zero', Limits.zero_comp]
  | add f₁ f₂ h₁ h₂ =>
    rw [Preadditive.add_comp, φ.lin_add, φ.lin_add, h₁, h₂, Preadditive.add_comp]
  | single d r =>
    induction g using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, φ.lin_zero', φ.lin_zero', Limits.comp_zero]
    | add g₁ g₂ h₁ h₂ =>
      rw [Preadditive.comp_add, φ.lin_add, φ.lin_add, h₁, h₂, Preadditive.comp_add]
    | single e s =>
      erw [Free.single_comp_single]
      rw [LayerMap.lin, LayerMap.lin, LayerMap.lin, Finsupp.mapDomain_single,
        Finsupp.mapDomain_single, Finsupp.mapDomain_single, LayerMap.map_comp]
      erw [Free.single_comp_single]


/-- `φ.lin` on endomorphisms, as a homomorphism of `R`-algebras. -/
def linAlg (φ : LayerMap S S') (a : Obj S) : End (Free.of R a) →ₐ[R] End (Free.of R (φ.obj a)) where
  toFun := φ.lin
  map_one' := by
    show φ.lin (LinDiagram.of (𝟙 a)) = LinDiagram.of (𝟙 (φ.obj a))
    rw [LayerMap.lin_of, LayerMap.map_id]
  map_mul' f g := φ.lin_comp' g f
  map_zero' := φ.lin_zero'
  map_add' := φ.lin_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    show φ.lin (r • LinDiagram.of (𝟙 a)) = r • LinDiagram.of (𝟙 (φ.obj a))
    rw [φ.lin_smul, LayerMap.lin_of, LayerMap.map_id]

theorem linAlg_apply (φ : LayerMap S S') (a : Obj S) (f : End (Free.of R a)) :
    linAlg φ a f = φ.lin f := rfl

theorem _root_.StringDiagrams.LayerMap.lin_sum (φ : LayerMap S S') {a b : Obj S} {ι : Type*}
    (T : Finset ι) (f : ι → LinDiagram R a b) : φ.lin (∑ x ∈ T, f x) = ∑ x ∈ T, φ.lin (f x) :=
  map_sum (φ.linMap a b) f T

theorem _root_.StringDiagrams.LayerMap.lin_neg (φ : LayerMap S S') {a b : Obj S}
    (f : LinDiagram R a b) : φ.lin (-f) = -φ.lin f :=
  (φ.linMap a b).map_neg f

/-- Induction on linear combinations of diagrams, with the operations of `LinDiagram`. -/
@[elab_as_elim]
theorem linDiagram_induction {a b : Obj S} {p : LinDiagram R a b → Prop} (f : LinDiagram R a b)
    (zero : p 0) (add : ∀ f g, p f → p g → p (f + g))
    (single : ∀ (d : a ⟶ b) (c : R), p (Finsupp.single d c)) : p f :=
  Finsupp.induction_linear f zero add single

theorem linCast_comp {a b c a' b' c' : Obj S} (f : LinDiagram R a b) (g : LinDiagram R b c)
    (ha : a = a') (hb : b = b') (hc : c = c') :
    LinDiagram.cast (f ≫ g) ha hc = LinDiagram.cast f ha hb ≫ LinDiagram.cast g hb hc := by
  subst ha hb hc; simp only [LinDiagram.cast_rfl]

theorem linCast_self {a b : Obj S} (f : LinDiagram R a b) (ha : a = a) (hb : b = b) :
    LinDiagram.cast f ha hb = f := LinDiagram.cast_rfl f

theorem linCast_cast {a b a' b' a'' b'' : Obj S} (f : LinDiagram R a b) (ha : a = a') (hb : b = b')
    (ha' : a' = a'') (hb' : b' = b'') :
    LinDiagram.cast (LinDiagram.cast f ha hb) ha' hb' = LinDiagram.cast f (ha.trans ha') (hb.trans hb') := by
  subst ha hb ha' hb'; simp only [LinDiagram.cast_rfl]

theorem linCast_id {a a' : Obj S} (h : a = a') :
    LinDiagram.cast (𝟙 (Free.of R a)) h h = 𝟙 (Free.of R a') := by
  subst h; exact LinDiagram.cast_rfl _

theorem linCast_sum {a b a' b' : Obj S} {ι : Type*} (T : Finset ι) (f : ι → LinDiagram R a b)
    (ha : a = a') (hb : b = b') :
    LinDiagram.cast (∑ x ∈ T, f x) ha hb = ∑ x ∈ T, LinDiagram.cast (f x) ha hb := by
  subst ha hb; simp only [LinDiagram.cast_rfl]

theorem linCast_zero {a b a' b' : Obj S} (ha : a = a') (hb : b = b') :
    LinDiagram.cast (0 : LinDiagram R a b) ha hb = 0 := by
  subst ha hb; exact LinDiagram.cast_rfl _

theorem lin_linCast (P : Presentation S R) {a b a' b' : Obj S} (f : LinDiagram R a b) (ha : a = a')
    (hb : b = b') (hf : P.lin f = 0) : P.lin (LinDiagram.cast f ha hb) = 0 := by
  subst ha hb; rw [LinDiagram.cast_rfl]; exact hf

end Generic

/-! ## The map of signatures -/

variable {m : ℕ}

variable (m) in
/-- **The map of signatures** `psig (sl_{m+1}) → psig (sl_{m+2})`: regions `phiW`, strands `ιC`,
generators `ιG`. -/
def embSig : SigMap (psig (slRootDatum m)) (psig (slRootDatum (m + 1))) where
  region := phiW
  colour := ιC
  colourSrc := src_ιC
  colourTgt _ := rfl
  gen := ιG
  dom := ιG_dom
  cod := ιG_cod
  left := ιG_left
  right := ιG_right

@[simp] theorem embSig_obj (a : Obj (psig (slRootDatum m))) : (embSig m).obj a = ιO a := rfl

theorem embSig_layer (L : Layer (psig (slRootDatum m))) : (embSig m).layer L = ιL L := rfl

theorem embSig_map {a b : Obj (psig (slRootDatum m))} (d : a ⟶ b) :
    (embSig m).toLayerMap.map d = ιD d := rfl

/-! ## Relabelling KLR diagrams -/

/-- The relabelling of KLR generators. -/
def klrGen : KLR.Diagram.Gen (Fin m) → KLR.Diagram.Gen (Fin (m + 1))
  | .dot c => .dot c.castSucc
  | .cross c d => .cross c.castSucc d.castSucc

variable (m) in
/-- The relabelling `Fin m → Fin (m + 1)` of the KLR signature. -/
def klrSig : SigMap (KLR.Diagram.sig (Fin m)) (KLR.Diagram.sig (Fin (m + 1))) where
  region := id
  colour := Fin.castSucc
  colourSrc _ := rfl
  colourTgt _ := rfl
  gen := klrGen
  dom g := by cases g <;> rfl
  cod g := by cases g <;> rfl
  left _ := rfl
  right _ := rfl

/-- The relabelling of the KLR relations. -/
def klrRel : KLR.Diagram.Rel (Fin m) → KLR.Diagram.Rel (Fin (m + 1))
  | .sqEq c => .sqEq c.castSucc
  | .sqNe c d h => .sqNe c.castSucc d.castSucc (fun e => h (Fin.castSucc_injective _ e))
  | .slideLEq c => .slideLEq c.castSucc
  | .slideLNe c d h => .slideLNe c.castSucc d.castSucc (fun e => h (Fin.castSucc_injective _ e))
  | .slideREq c => .slideREq c.castSucc
  | .slideRNe c d h => .slideRNe c.castSucc d.castSucc (fun e => h (Fin.castSucc_injective _ e))
  | .braid c d e h => .braid c.castSucc d.castSucc e.castSucc
      (fun h' => h ⟨Fin.castSucc_injective _ h'.1, fun e' => h'.2 (congrArg _ e')⟩)
  | .braidQ c d h => .braidQ c.castSucc d.castSucc (fun e => h (Fin.castSucc_injective _ e))

theorem klrRel_dom (r : KLR.Diagram.Rel (Fin m)) : (klrRel r).dom = (klrSig m).toLayerMap.obj r.dom := by
  cases r <;> rfl

theorem klrRel_cod (r : KLR.Diagram.Rel (Fin m)) : (klrRel r).cod = (klrSig m).toLayerMap.obj r.cod := by
  cases r <;> rfl

theorem klQ2_castSucc (K : Type w) [CommRing K] (c d : Fin m) :
    KLR.klQ2 K (slCartan (m + 1)) c.castSucc d.castSucc = KLR.klQ2 K (slCartan m) c d := by
  simp only [KLR.klQ2, CartanDatum.dij, slCartan_dot_castSucc]

section KLRRelabel

variable (K : Type w) [CommRing K]

theorem klrSig_lin_lpoly {w : Obj (KLR.Diagram.sig (Fin m))} {n : ℕ} (y : Fin n → (w ⟶ w))
    (p : MvPolynomial (Fin n) K) :
    (klrSig m).toLayerMap.lin (KLR.Diagram.lpoly K y p) =
      KLR.Diagram.lpoly K (fun a => (klrSig m).toLayerMap.map (y a)) p := by
  have := AlgHom.map_ncEval (linAlg (R := K) (klrSig m).toLayerMap w)
    (fun a => LinDiagram.of (y a)) p
  rw [linAlg_apply] at this
  rw [KLR.Diagram.lpoly, this]
  simp only [linAlg_apply, LayerMap.lin_of]

/-- **The relabelling sends the KLR relations for `sl_{m+1}` to those for `sl_{m+2}`.** -/
theorem klrSig_lin_relation (r : KLR.Diagram.Rel (Fin m)) :
    (klrSig m).toLayerMap.lin (KLR.Diagram.relation K (KLR.klQ2 K (slCartan m)) r) =
      LinDiagram.cast (KLR.Diagram.relation K (KLR.klQ2 K (slCartan (m + 1))) (klrRel r))
        (klrRel_dom r) (klrRel_cod r) := by
  cases r with
  | sqEq c =>
    refine Eq.trans ?_ (linCast_self _ _ _).symm
    rw [KLR.Diagram.relation, LayerMap.lin_of]; rfl
  | sqNe c d h =>
    refine Eq.trans ?_ (linCast_self _ _ _).symm
    rw [KLR.Diagram.relation, LayerMap.lin_sub, LayerMap.lin_of, klrSig_lin_lpoly]
    simp only [klrRel, KLR.Diagram.relation, klQ2_castSucc]
    congr 2
    funext a
    fin_cases a <;> rfl
  | slideLEq c =>
    refine Eq.trans ?_ (linCast_self _ _ _).symm
    rw [KLR.Diagram.relation, LayerMap.lin_sub, LayerMap.lin_sub, LayerMap.lin_of,
      LayerMap.lin_of, LayerMap.lin_of]; rfl
  | slideLNe c d h =>
    refine Eq.trans ?_ (linCast_self _ _ _).symm
    rw [KLR.Diagram.relation, LayerMap.lin_sub, LayerMap.lin_of, LayerMap.lin_of]; rfl
  | slideREq c =>
    refine Eq.trans ?_ (linCast_self _ _ _).symm
    rw [KLR.Diagram.relation, LayerMap.lin_sub, LayerMap.lin_sub, LayerMap.lin_of,
      LayerMap.lin_of, LayerMap.lin_of]; rfl
  | slideRNe c d h =>
    refine Eq.trans ?_ (linCast_self _ _ _).symm
    rw [KLR.Diagram.relation, LayerMap.lin_sub, LayerMap.lin_of, LayerMap.lin_of]; rfl
  | braid c d e h =>
    refine Eq.trans ?_ (linCast_self _ _ _).symm
    rw [KLR.Diagram.relation, LayerMap.lin_sub, LayerMap.lin_of, LayerMap.lin_of]; rfl
  | braidQ c d h =>
    refine Eq.trans ?_ (linCast_self _ _ _).symm
    rw [KLR.Diagram.relation, LayerMap.lin_sub, LayerMap.lin_sub, LayerMap.lin_of,
      LayerMap.lin_of, klrSig_lin_lpoly]
    simp only [klrRel, KLR.Diagram.relation, klQ2_castSucc]
    congr 2
    funext a
    fin_cases a <;> rfl

end KLRRelabel

/-! ## Relabelling linear combinations of normal-form diagrams -/

section Psi

variable {K : Type w} [CommRing K]

local notation "RD" => slRootDatum m
local notation "RD'" => slRootDatum (m + 1)

/-- The relabelling of linear combinations of diagrams. -/
abbrev Φl {a b : Obj (psig (slRootDatum m))} (f : LinDiagram K a b) : LinDiagram K (ιO a) (ιO b) :=
  (embSig m).toLayerMap.lin f

/-- **The relabelling of linear combinations of normal-form diagrams**, retyped to normal-form
objects along `ιO_ob`. -/
def Ψ {μ : (Fin m → ℤ)} {s t : List (Letter (Fin m))} (f : LinDiagram K (ob RD μ s) (ob RD μ t)) :
    LinDiagram K (ob RD' (phiW μ) (s.map ιl)) (ob RD' (phiW μ) (t.map ιl)) :=
  LinDiagram.cast (Φl f) (ιO_ob μ s) (ιO_ob μ t)

variable {μ : (Fin m → ℤ)} {s r t : List (Letter (Fin m))}

theorem Ψ_comp (f : LinDiagram K (ob RD μ s) (ob RD μ r)) (g : LinDiagram K (ob RD μ r) (ob RD μ t)) :
    Ψ (f ≫ g) = Ψ f ≫ Ψ g := by
  rw [Ψ, Φl, LayerMap.lin_comp', linCast_comp _ _ _ (ιO_ob μ r)]; rfl

theorem Ψ_add (f g : LinDiagram K (ob RD μ s) (ob RD μ t)) : Ψ (f + g) = Ψ f + Ψ g := by
  rw [Ψ, Φl, LayerMap.lin_add, LinDiagram.cast_add]; rfl

theorem Ψ_sub (f g : LinDiagram K (ob RD μ s) (ob RD μ t)) : Ψ (f - g) = Ψ f - Ψ g := by
  rw [Ψ, Φl, LayerMap.lin_sub, LinDiagram.cast_sub]; rfl

theorem Ψ_neg (f : LinDiagram K (ob RD μ s) (ob RD μ t)) : Ψ (-f) = -Ψ f := by
  rw [Ψ, Φl, LayerMap.lin_neg, LinDiagram.cast_neg]; rfl

theorem Ψ_smul (c : K) (f : LinDiagram K (ob RD μ s) (ob RD μ t)) : Ψ (c • f) = c • Ψ f := by
  rw [Ψ, Φl, LayerMap.lin_smul, LinDiagram.cast_smul]; rfl

theorem Ψ_zero : Ψ (0 : LinDiagram K (ob RD μ s) (ob RD μ t)) = 0 := by
  rw [Ψ, Φl, LayerMap.lin_zero', linCast_zero]

theorem Ψ_sum {ι : Type*} (T : Finset ι) (f : ι → LinDiagram K (ob RD μ s) (ob RD μ t)) :
    Ψ (∑ x ∈ T, f x) = ∑ x ∈ T, Ψ (f x) := by
  rw [Ψ, Φl, LayerMap.lin_sum, linCast_sum]; rfl

theorem Ψ_id : Ψ (𝟙 (Free.of K (ob RD μ s))) = 𝟙 _ := by
  show LinDiagram.cast ((embSig m).toLayerMap.lin (LinDiagram.of (𝟙 _))) _ _ = _
  rw [LayerMap.lin_of, LayerMap.map_id]
  exact linCast_id _

theorem Ψ_of_id : Ψ (LinDiagram.of (𝟙 (ob RD μ s)) : LinDiagram K _ _) = LinDiagram.of (𝟙 _) :=
  Ψ_id

theorem Ψ_single (d : ob RD μ s ⟶ ob RD μ t) (c : K) :
    Ψ (Finsupp.single d c : LinDiagram K (ob RD μ s) (ob RD μ t)) =
      Finsupp.single (Diagram.cast (ιD d) (ιO_ob μ s) (ιO_ob μ t)) c := by
  rw [Ψ, Φl, LayerMap.lin, Finsupp.mapDomain_single, LinDiagram.cast_single]; rfl

theorem Ψ_of_eq (d : ob RD μ s ⟶ ob RD μ t)
    (d' : ob RD' (phiW μ) (s.map ιl) ⟶ ob RD' (phiW μ) (t.map ιl))
    (h : Diagram.layers d' = (Diagram.layers d).map ιL) :
    Ψ (LinDiagram.of d : LinDiagram K _ _) = LinDiagram.of d' := by
  rw [Ψ_single]
  congr 1
  exact Diagram.ext h.symm

theorem Ψ_of_mkD (ls : List (LayerData (Fin m))) (h : SChain s ls t) :
    Ψ (LinDiagram.of (mkD RD μ ls h) : LinDiagram K _ _) =
      LinDiagram.of (mkD RD' (phiW μ) (ls.map ιLD) (sChain_ι h)) :=
  Ψ_of_eq _ _ (layers_ιD_mkD μ ls h).symm

theorem mkD_congr (ν : (Fin (m + 1) → ℤ)) {s t : List (Letter (Fin (m + 1)))}
    {ls ls' : List (LayerData (Fin (m + 1)))} (e : ls = ls') (h : SChain s ls t)
    (h' : SChain s ls' t) : mkD RD' ν ls h = mkD RD' ν ls' h' := by
  subst e; rfl

/-! ### The diagrams of Definition 3.1 -/

variable (K)

theorem Ψ_downDot (i : Fin m) (μ : (Fin m → ℤ)) :
    Ψ (LinDiagram.of (downDot RD i μ) : LinDiagram K _ _) =
      LinDiagram.of (downDot RD' i.castSucc (phiW μ)) := by
  unfold downDot; rw [Ψ_of_mkD]; rfl

theorem Ψ_rotDotR (i : Fin m) (μ : (Fin m → ℤ)) :
    Ψ (LinDiagram.of (rotDotR RD i μ) : LinDiagram K _ _) =
      LinDiagram.of (rotDotR RD' i.castSucc (phiW μ)) := by
  unfold rotDotR; rw [Ψ_of_mkD]; rfl

theorem Ψ_rotDotL (i : Fin m) (μ : (Fin m → ℤ)) :
    Ψ (LinDiagram.of (rotDotL RD i μ) : LinDiagram K _ _) =
      LinDiagram.of (rotDotL RD' i.castSucc (phiW μ)) := by
  unfold rotDotL; rw [Ψ_of_mkD]; rfl

theorem Ψ_downCross (j i : Fin m) (μ : (Fin m → ℤ)) :
    Ψ (LinDiagram.of (downCross RD j i μ) : LinDiagram K _ _) =
      LinDiagram.of (downCross RD' j.castSucc i.castSucc (phiW μ)) := by
  unfold downCross; rw [Ψ_of_mkD]; rfl

theorem Ψ_rotCrossR (j i : Fin m) (μ : (Fin m → ℤ)) :
    Ψ (LinDiagram.of (rotCrossR RD j i μ) : LinDiagram K _ _) =
      LinDiagram.of (rotCrossR RD' j.castSucc i.castSucc (phiW μ)) := by
  unfold rotCrossR; rw [Ψ_of_mkD]; rfl

theorem Ψ_rotCrossL (j i : Fin m) (μ : (Fin m → ℤ)) :
    Ψ (LinDiagram.of (rotCrossL RD j i μ) : LinDiagram K _ _) =
      LinDiagram.of (rotCrossL RD' j.castSucc i.castSucc (phiW μ)) := by
  unfold rotCrossL; rw [Ψ_of_mkD]; rfl

theorem Ψ_crossl (i j : Fin m) (μ : (Fin m → ℤ)) :
    Ψ (LinDiagram.of (crossl RD i j μ) : LinDiagram K _ _) =
      LinDiagram.of (crossl RD' i.castSucc j.castSucc (phiW μ)) := by
  unfold crossl; rw [Ψ_of_mkD]; rfl

theorem Ψ_crossr (i j : Fin m) (μ : (Fin m → ℤ)) :
    Ψ (LinDiagram.of (crossr RD i j μ) : LinDiagram K _ _) =
      LinDiagram.of (crossr RD' i.castSucc j.castSucc (phiW μ)) := by
  unfold crossr; rw [Ψ_of_mkD]; rfl

theorem Ψ_curlR (i : Fin m) (μ : (Fin m → ℤ)) :
    Ψ (LinDiagram.of (curlR RD i μ) : LinDiagram K _ _) =
      LinDiagram.of (curlR RD' i.castSucc (phiW μ)) := by
  unfold curlR; rw [Ψ_of_mkD]; rfl

theorem Ψ_curlL (i : Fin m) (μ : (Fin m → ℤ)) :
    Ψ (LinDiagram.of (curlL RD i μ) : LinDiagram K _ _) =
      LinDiagram.of (curlL RD' i.castSucc (phiW μ)) := by
  unfold curlL; rw [Ψ_of_mkD]; rfl

theorem Ψ_cwReal (lam : (Fin m → ℤ)) (i : Fin m) (α : ℕ) :
    Ψ (LinDiagram.of (cwReal RD lam i α) : LinDiagram K _ _) =
      LinDiagram.of (cwReal RD' (phiW lam) i.castSucc α) := by
  unfold cwReal; rw [Ψ_of_mkD]; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_ccwReal (lam : (Fin m → ℤ)) (i : Fin m) (α : ℕ) :
    Ψ (LinDiagram.of (ccwReal RD lam i α) : LinDiagram K _ _) =
      LinDiagram.of (ccwReal RD' (phiW lam) i.castSucc α) := by
  unfold ccwReal; rw [Ψ_of_mkD]; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_dotCapEF (lam : (Fin m → ℤ)) (i : Fin m) (n : ℕ) :
    Ψ (LinDiagram.of (dotCapEF RD lam i n) : LinDiagram K _ _) =
      LinDiagram.of (dotCapEF RD' (phiW lam) i.castSucc n) := by
  unfold dotCapEF; rw [Ψ_of_mkD]; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_cupDotEF (lam : (Fin m → ℤ)) (i : Fin m) (n : ℕ) :
    Ψ (LinDiagram.of (cupDotEF RD lam i n) : LinDiagram K _ _) =
      LinDiagram.of (cupDotEF RD' (phiW lam) i.castSucc n) := by
  unfold cupDotEF; rw [Ψ_of_mkD]; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_dotCapFE (lam : (Fin m → ℤ)) (i : Fin m) (n : ℕ) :
    Ψ (LinDiagram.of (dotCapFE RD lam i n) : LinDiagram K _ _) =
      LinDiagram.of (dotCapFE RD' (phiW lam) i.castSucc n) := by
  unfold dotCapFE; rw [Ψ_of_mkD]; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_cupDotFE (lam : (Fin m → ℤ)) (i : Fin m) (n : ℕ) :
    Ψ (LinDiagram.of (cupDotFE RD lam i n) : LinDiagram K _ _) =
      LinDiagram.of (cupDotFE RD' (phiW lam) i.castSucc n) := by
  unfold cupDotFE; rw [Ψ_of_mkD]; congr 1; apply mkD_congr
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil]; rfl

theorem Ψ_dots (μ : (Fin m → ℤ)) (l : Letter (Fin m)) (n : ℕ) :
    Ψ (LinDiagram.of (dots RD μ [] l [] n) : LinDiagram K _ _) =
      LinDiagram.of (dots RD' (phiW μ) [] (ιl l) [] n) := by
  unfold dots; rw [Ψ_of_mkD]; congr 1; apply mkD_congr
  simp only [List.map_replicate]; rfl

/-! ### Bubbles -/

/-- `Ψ` on the endomorphisms of `1_λ`, as a ring homomorphism. -/
def Ψe (lam : (Fin m → ℤ)) : LEnd RD K (ob RD lam []) →+* LEnd RD' K (ob RD' (phiW lam) []) :=
  (linAlg (R := K) (embSig m).toLayerMap (ob RD lam [])).toRingHom

variable {K}

theorem Ψe_eq (lam : (Fin m → ℤ)) (b : LEnd RD K (ob RD lam [])) : Ψe K lam b = Ψ b :=
  (linCast_self _ _ _).symm

variable (K)

theorem Ψ_cwR (lam : (Fin m → ℤ)) (i : Fin m) (n : ℤ) :
    Ψ (cwR RD K lam i n) = cwR RD' K (phiW lam) i.castSucc n := by
  unfold cwR; split_ifs
  · exact Ψ_cwReal K lam i _
  · exact Ψ_zero

theorem Ψ_ccwR (lam : (Fin m → ℤ)) (i : Fin m) (n : ℤ) :
    Ψ (ccwR RD K lam i n) = ccwR RD' K (phiW lam) i.castSucc n := by
  unfold ccwR; split_ifs
  · exact Ψ_ccwReal K lam i _
  · exact Ψ_zero

theorem Ψ_cwL (lam : (Fin m → ℤ)) (i : Fin m) (n : ℤ) :
    Ψ (cwL RD K lam i n) = cwL RD' K (phiW lam) i.castSucc n := by
  unfold cwL
  rw [ip_phiW]
  split_ifs
  · exact Ψ_cwReal K lam i _
  · rw [← Ψe_eq, CL.Rescale.grassInv_map_ringHom]
    congr 1
    funext a
    rw [Ψe_eq, Ψ_ccwR]
  · exact Ψ_zero

theorem Ψ_ccwL (lam : (Fin m → ℤ)) (i : Fin m) (n : ℤ) :
    Ψ (ccwL RD K lam i n) = ccwL RD' K (phiW lam) i.castSucc n := by
  unfold ccwL
  rw [ip_phiW]
  split_ifs
  · exact Ψ_ccwReal K lam i _
  · rw [← Ψe_eq, CL.Rescale.grassInv_map_ringHom]
    congr 1
    funext a
    rw [Ψe_eq, Ψ_cwR]
  · exact Ψ_zero

variable {K}

theorem Ψ_bubR (lam : (Fin m → ℤ)) (t : List (Letter (Fin m)))
    (b : LinDiagram K (ob RD lam []) (ob RD lam [])) :
    Ψ (bubR RD K lam t b) = bubR RD' K (phiW lam) (t.map ιl) (Ψ b) := by
  induction b using linDiagram_induction with
  | zero =>
    simp only [bubR, LinDiagram.whisker_zero, linCast_zero, Ψ_zero]
  | add f g hf hg =>
    simp only [bubR, LinDiagram.whisker_add, LinDiagram.cast_add, Ψ_add] at hf hg ⊢
    rw [hf, hg]
  | single d c =>
    simp only [bubR, Ψ, Φl, LinDiagram.whisker, LinDiagram.cast, LayerMap.lin,
      Finsupp.mapDomain_single]
    congr 1
    apply Diagram.ext
    simp only [Diagram.layers_cast, Diagram.layers_whisker, LayerMap.layers_map, List.map_map]
    refine List.map_congr_left fun L _ => ?_
    show ιL (L.whisker _ _) = (ιL L).whisker _ _
    rw [ιL_whisker, ιO_ob]; rfl

theorem hwt (μ : (Fin m → ℤ)) (t : List (Letter (Fin m))) :
    ob RD' (phiW (wt RD μ t)) [] = ob RD' (wt RD' (phiW μ) (t.map ιl)) [] := by
  rw [wt_map]

theorem Ψ_bubL (μ : (Fin m → ℤ)) (t : List (Letter (Fin m)))
    (b : LinDiagram K (ob RD (wt RD μ t) []) (ob RD (wt RD μ t) [])) :
    Ψ (bubL RD K μ t b) =
      bubL RD' K (phiW μ) (t.map ιl) (LinDiagram.cast (Ψ b) (hwt μ t) (hwt μ t)) := by
  induction b using linDiagram_induction with
  | zero =>
    simp only [bubL, LinDiagram.whisker_zero, linCast_zero, Ψ_zero]
  | add f g hf hg =>
    simp only [bubL, LinDiagram.whisker_add, LinDiagram.cast_add, Ψ_add] at hf hg ⊢
    rw [hf, hg]
  | single d c =>
    simp only [bubL, Ψ, Φl, LinDiagram.whisker, LinDiagram.cast, LayerMap.lin,
      Finsupp.mapDomain_single]
    congr 1
    apply Diagram.ext
    simp only [Diagram.layers_cast, Diagram.layers_whisker, LayerMap.layers_map, List.map_map]
    refine List.map_congr_left fun L _ => ?_
    show ιL (L.whisker _ _) = (ιL L).whisker _ _
    rw [ιL_whisker, wd_map, show ιO (ob RD (wt RD μ t) []) = ob RD' (wt RD' (phiW μ) (t.map ιl)) [] from
      Obj.ext (wt_map μ t) rfl]

theorem linCast_ccwL {ρ ρ' : (Fin (m + 1) → ℤ)} (h : ρ = ρ') (e e' : ob RD' ρ [] = ob RD' ρ' [])
    (i : Fin (m + 1)) (n : ℤ) : LinDiagram.cast (ccwL RD' K ρ i n) e e' = ccwL RD' K ρ' i n := by
  subst h; exact linCast_self _ _ _

theorem ups_map (w : List (Fin m)) : (ups w).map ιl = ups (w.map Fin.castSucc) := by
  simp only [ups, List.map_map]; rfl

theorem upShape_klrGen (g : KLR.Diagram.Gen (Fin m)) : ιSh (upShape g) = upShape (klrGen g) := by
  cases g <;> rfl

theorem ιL_upLay (μ : (Fin m → ℤ)) (L : Layer (KLR.Diagram.sig (Fin m))) :
    ιL (upLay RD μ L) = upLay RD' (phiW μ) ((klrSig m).layer L) := by
  rw [upLay, ιL_lay, upLay, ups_map, ups_map, upShape_klrGen]; rfl

theorem Ψ_upLin (μ : (Fin m → ℤ)) {a b : Obj (KLR.Diagram.sig (Fin m))} (f : LinDiagram K a b) :
    Ψ (upLin RD K μ f) = LinDiagram.cast (upLin RD' K (phiW μ) ((klrSig m).toLayerMap.lin f))
      (by rw [ups_map]; rfl) (by rw [ups_map]; rfl) := by
  induction f using linDiagram_induction with
  | zero =>
    simp only [upLin, Finsupp.mapDomain_zero, LayerMap.lin_zero', linCast_zero]
    exact Ψ_zero
  | add f g hf hg =>
    have e1 : upLin RD K μ (f + g) = upLin RD K μ f + upLin RD K μ g := Finsupp.mapDomain_add
    have e2 : ∀ x y : LinDiagram K ((klrSig m).toLayerMap.obj a) ((klrSig m).toLayerMap.obj b),
        upLin RD' K (phiW μ) (x + y) = upLin RD' K (phiW μ) x + upLin RD' K (phiW μ) y :=
      fun x y => Finsupp.mapDomain_add
    rw [e1, Ψ_add, hf, hg, LayerMap.lin_add, e2, LinDiagram.cast_add]
  | single d c =>
    simp only [upLin, Finsupp.mapDomain_single, LayerMap.lin, LinDiagram.cast_single]
    rw [Ψ_single]
    congr 1
    apply Diagram.ext
    simp only [Diagram.layers_cast, layers_ιD, layers_upDiag, LayerMap.layers_map, List.map_map]
    refine List.map_congr_left fun L _ => ?_
    exact ιL_upLay μ L

theorem upLin_cast (ν : (Fin (m + 1) → ℤ)) {a b a' b' : Obj (KLR.Diagram.sig (Fin (m + 1)))}
    (f : LinDiagram K a b) (ha : a = a') (hb : b = b') :
    upLin RD' K ν (LinDiagram.cast f ha hb) =
      LinDiagram.cast (upLin RD' K ν f) (by rw [ha]) (by rw [hb]) := by
  subst ha hb; simp only [LinDiagram.cast_rfl]

/-! ### Composite diagrams of the relations -/

variable (K)

theorem Ψ_curlRHS (i : Fin m) (lam : (Fin m → ℤ)) :
    Ψ (curlRHS RD K i lam) = curlRHS RD' K i.castSucc (phiW lam) := by
  unfold curlRHS
  rw [ip_phiW, Ψ_neg, Ψ_sum]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Ψ_comp, Ψ_bubR, Ψ_cwL, Ψ_dots]
  rfl

theorem Ψ_curlLHS (i : Fin m) (μ : (Fin m → ℤ)) :
    Ψ (curlLHS RD K i μ) = curlLHS RD' K i.castSucc (phiW μ) := by
  have hw : phiW (wt RD μ [up i]) = wt RD' (phiW μ) [up i.castSucc] := wt_map μ [up i]
  have hip : ip RD' i.castSucc (wt RD' (phiW μ) [up i.castSucc]) = ip RD i (wt RD μ [up i]) := by
    rw [← hw, ip_phiW]
  unfold curlLHS
  rw [Ψ_sum, hip]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Ψ_comp, Ψ_bubL, Ψ_ccwL, linCast_ccwL hw, Ψ_dots]
  rfl

theorem Ψ_decompEFSum (i : Fin m) (lam : (Fin m → ℤ)) :
    Ψ (decompEFSum RD K i lam) = decompEFSum RD' K i.castSucc (phiW lam) := by
  unfold decompEFSum
  rw [ip_phiW, Ψ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Ψ_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Ψ_comp, Ψ_comp, Ψ_dotCapEF, Ψ_ccwL, Ψ_cupDotEF]

theorem Ψ_decompFESum (i : Fin m) (lam : (Fin m → ℤ)) :
    Ψ (decompFESum RD K i lam) = decompFESum RD' K i.castSucc (phiW lam) := by
  unfold decompFESum
  rw [ip_phiW, Ψ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Ψ_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Ψ_comp, Ψ_comp, Ψ_dotCapFE, Ψ_cwL, Ψ_cupDotFE]

theorem Ψ_klr (μ : (Fin m → ℤ)) (r : KLR.Diagram.Rel (Fin m)) :
    Ψ (upLin RD K μ (KLR.Diagram.relation K (KLR.klQ2 K (slCartan m)) r)) =
      LinDiagram.cast (upLin RD' K (phiW μ)
        (KLR.Diagram.relation K (KLR.klQ2 K (slCartan (m + 1))) (klrRel r)))
        (by rw [ups_map, klrRel_dom]; rfl) (by rw [ups_map, klrRel_cod]; rfl) := by
  rw [Ψ_upLin, klrSig_lin_relation, upLin_cast, linCast_cast]

end Psi

/-! ## The relations are preserved -/

section Relations

variable {K : Type w} [CommRing K]

local notation "RD" => slRootDatum m
local notation "RD'" => slRootDatum (m + 1)

theorem lin_eq_zero_of_Ψ {μ : (Fin m → ℤ)} {s t : List (Letter (Fin m))}
    (f : LinDiagram K (ob RD μ s) (ob RD μ t)) {a b : Obj (psig RD')} (g : LinDiagram K a b)
    (ha : a = ob RD' (phiW μ) (s.map ιl)) (hb : b = ob RD' (phiW μ) (t.map ιl))
    (h : Ψ f = LinDiagram.cast g ha hb) (hg : (pres RD' K).lin g = 0) :
    (pres RD' K).lin (Φl f) = 0 := by
  have e : Φl f = LinDiagram.cast (Ψ f) (ιO_ob μ s).symm (ιO_ob μ t).symm := by
    rw [Ψ, linCast_cast]; exact (linCast_self _ _ _).symm
  rw [e, h, linCast_cast]
  exact lin_linCast _ _ _ _ hg

theorem lin_eq_zero_of_Ψ' {μ : (Fin m → ℤ)} {s t : List (Letter (Fin m))}
    (f : LinDiagram K (ob RD μ s) (ob RD μ t))
    (g : LinDiagram K (ob RD' (phiW μ) (s.map ιl)) (ob RD' (phiW μ) (t.map ιl)))
    (h : Ψ f = g) (hg : (pres RD' K).lin g = 0) : (pres RD' K).lin (Φl f) = 0 :=
  lin_eq_zero_of_Ψ f g rfl rfl (h.trans (linCast_self _ _ _).symm) hg

theorem lin_relation' (r : Rel RD') : (pres RD' K).lin (relation K r) = 0 :=
  (pres RD' K).lin_rel_self (.inr r)

theorem Ψ_sub_eq {μ : (Fin m → ℤ)} {s t : List (Letter (Fin m))}
    {f g : LinDiagram K (ob RD μ s) (ob RD μ t)}
    {f' g' : LinDiagram K (ob RD' (phiW μ) (s.map ιl)) (ob RD' (phiW μ) (t.map ιl))}
    (hf : Ψ f = f') (hg : Ψ g = g') : Ψ (f - g) = f' - g' := by
  rw [Ψ_sub, hf, hg]

theorem Ψ_add_eq {μ : (Fin m → ℤ)} {s t : List (Letter (Fin m))}
    {f g : LinDiagram K (ob RD μ s) (ob RD μ t)}
    {f' g' : LinDiagram K (ob RD' (phiW μ) (s.map ιl)) (ob RD' (phiW μ) (t.map ιl))}
    (hf : Ψ f = f') (hg : Ψ g = g') : Ψ (f + g) = f' + g' := by
  rw [Ψ_add, hf, hg]

theorem Ψ_of_comp_eq {μ : (Fin m → ℤ)} {s r t : List (Letter (Fin m))}
    {d : ob RD μ s ⟶ ob RD μ r} {e : ob RD μ r ⟶ ob RD μ t}
    {d' : ob RD' (phiW μ) (s.map ιl) ⟶ ob RD' (phiW μ) (r.map ιl)}
    {e' : ob RD' (phiW μ) (r.map ιl) ⟶ ob RD' (phiW μ) (t.map ιl)}
    (hd : Ψ (LinDiagram.of d : LinDiagram K _ _) = LinDiagram.of d')
    (he : Ψ (LinDiagram.of e : LinDiagram K _ _) = LinDiagram.of e') :
    Ψ (LinDiagram.of (d ≫ e) : LinDiagram K _ _) = LinDiagram.of (d' ≫ e') := by
  rw [LinDiagram.of_comp, Ψ_comp, hd, he, LinDiagram.of_comp]

theorem ιO_colourObj (c : Col (Fin m) (Fin m → ℤ)) :
    ιO (Pivotal.colourObj (inv RD).toColourDuality c) =
      Pivotal.colourObj (inv RD').toColourDuality (ιC c) :=
  Obj.ext (src_ιC c).symm rfl

theorem ιO_dualObj (c : Col (Fin m) (Fin m → ℤ)) :
    ιO (Pivotal.dualObj (inv RD).toColourDuality c) =
      Pivotal.dualObj (inv RD').toColourDuality (ιC c) :=
  Obj.ext rfl (by
    show [ιC ((inv RD).dual c)] = [(inv RD').dual (ιC c)]
    rw [dual_ιC])

theorem diag_ιD_zigL (c : Col (Fin m) (Fin m → ℤ)) :
    (pres RD' K).diag (ιD (Pivotal.zigL (inv RD).toColourDuality c)) = 𝟙 _ := by
  refine (pres RD' K).diag_eq_id_of_layers _ (Pivotal.zigL (inv RD').toColourDuality (ιC c))
    (ιO_colourObj c) ?_ ((zigzags RD' K) (ιC c)).1
  simp only [layers_ιD, Pivotal.zigL, Diagram.layers_leftZigzag, Pivotal.cupD, Pivotal.capD,
    Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Layer.wl, Layer.wr]
  simp only [ιL, ιG, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_⟩ <;> exact Layer.ext (src_ιC c).symm rfl rfl rfl

theorem diag_ιD_zigR (c : Col (Fin m) (Fin m → ℤ)) :
    (pres RD' K).diag (ιD (Pivotal.zigR (inv RD).toColourDuality c)) = 𝟙 _ := by
  refine (pres RD' K).diag_eq_id_of_layers _ (Pivotal.zigR (inv RD').toColourDuality (ιC c))
    (ιO_dualObj c) ?_ ((zigzags RD' K) (ιC c)).2
  simp only [layers_ιD, Pivotal.zigR, Diagram.layers_rightZigzag, Pivotal.cupD, Pivotal.capD,
    Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Layer.wl, Layer.wr]
  simp only [ιL, ιG, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_⟩ <;> exact Layer.ext rfl (by simp [dual_ιC]) rfl (by simp [dual_ιC])

set_option maxHeartbeats 1000000 in
/-- **Every defining relation of `U(sl_{m+1})` is sent to zero in `U(sl_{m+2})`.** -/
theorem lin_embSig_rel (r : (pres RD K).Rel) : (pres RD' K).lin (Φl ((pres RD K).rel r)) = 0 := by
  rcases r with ((e | c | c) | r)
  · exact e.elim
  · show (pres RD' K).lin (Φl (LinDiagram.of (Pivotal.zigL _ c) - LinDiagram.of (𝟙 _))) = 0
    have h1 : (embSig m).toLayerMap.map (𝟙 (Pivotal.colourObj (inv RD).toColourDuality c)) = 𝟙 _ :=
      LayerMap.map_id _ _
    rw [Φl, LayerMap.lin_sub, LayerMap.lin_of, LayerMap.lin_of, h1,
      Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of, embSig_map, diag_ιD_zigL]
    exact sub_eq_zero.2 ((pres RD' K).diag_id _).symm
  · show (pres RD' K).lin (Φl (LinDiagram.of (Pivotal.zigR _ c) - LinDiagram.of (𝟙 _))) = 0
    have h1 : (embSig m).toLayerMap.map (𝟙 (Pivotal.dualObj (inv RD).toColourDuality c)) = 𝟙 _ :=
      LayerMap.map_id _ _
    rw [Φl, LayerMap.lin_sub, LayerMap.lin_of, LayerMap.lin_of, h1,
      Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of, embSig_map, diag_ιD_zigR]
    exact sub_eq_zero.2 ((pres RD' K).diag_id _).symm
  · cases r with
    | cycDotR i μ =>
      exact lin_eq_zero_of_Ψ' (relation K (.cycDotR i μ)) (relation K (.cycDotR i.castSucc (phiW μ)))
        (Ψ_sub_eq (Ψ_rotDotR K i μ) (Ψ_downDot K i μ)) (lin_relation' _)
    | cycDotL i μ =>
      exact lin_eq_zero_of_Ψ' (relation K (.cycDotL i μ)) (relation K (.cycDotL i.castSucc (phiW μ)))
        (Ψ_sub_eq (Ψ_rotDotL K i μ) (Ψ_downDot K i μ)) (lin_relation' _)
    | cwNeg i lam α h =>
      exact lin_eq_zero_of_Ψ' (relation K (.cwNeg i lam α h))
        (relation K (.cwNeg i.castSucc (phiW lam) α (by rw [ip_phiW]; exact h)))
        (Ψ_cwReal K lam i α) (lin_relation' _)
    | ccwNeg i lam α h =>
      exact lin_eq_zero_of_Ψ' (relation K (.ccwNeg i lam α h))
        (relation K (.ccwNeg i.castSucc (phiW lam) α (by rw [ip_phiW]; exact h)))
        (Ψ_ccwReal K lam i α) (lin_relation' _)
    | cwOne i lam h =>
      have h' : 1 ≤ ip RD' i.castSucc (phiW lam) := by rw [ip_phiW]; exact h
      refine lin_eq_zero_of_Ψ' (relation K (.cwOne i lam h))
        (relation K (.cwOne i.castSucc (phiW lam) h')) (Ψ_sub_eq ?_ Ψ_of_id) (lin_relation' _)
      rw [ip_phiW]; exact Ψ_cwReal K lam i _
    | ccwOne i lam h =>
      have h' : ip RD' i.castSucc (phiW lam) ≤ -1 := by rw [ip_phiW]; exact h
      refine lin_eq_zero_of_Ψ' (relation K (.ccwOne i lam h))
        (relation K (.ccwOne i.castSucc (phiW lam) h')) (Ψ_sub_eq ?_ Ψ_of_id) (lin_relation' _)
      rw [ip_phiW]; exact Ψ_ccwReal K lam i _
    | curlR i lam =>
      exact lin_eq_zero_of_Ψ' (relation K (.curlR i lam)) (relation K (.curlR i.castSucc (phiW lam)))
        (Ψ_sub_eq (Ψ_curlR K i lam) (Ψ_curlRHS K i lam)) (lin_relation' _)
    | curlL i μ =>
      exact lin_eq_zero_of_Ψ' (relation K (.curlL i μ)) (relation K (.curlL i.castSucc (phiW μ)))
        (Ψ_sub_eq (Ψ_curlL K i μ) (Ψ_curlLHS K i μ)) (lin_relation' _)
    | decompEF i lam =>
      exact lin_eq_zero_of_Ψ' (relation K (.decompEF i lam))
        (relation K (.decompEF i.castSucc (phiW lam)))
        (Ψ_sub_eq (Ψ_add_eq Ψ_of_id (Ψ_of_comp_eq (Ψ_crossl K i i lam) (Ψ_crossr K i i lam)))
          (Ψ_decompEFSum K i lam)) (lin_relation' _)
    | decompFE i lam =>
      exact lin_eq_zero_of_Ψ' (relation K (.decompFE i lam))
        (relation K (.decompFE i.castSucc (phiW lam)))
        (Ψ_sub_eq (Ψ_add_eq Ψ_of_id (Ψ_of_comp_eq (Ψ_crossr K i i lam) (Ψ_crossl K i i lam)))
          (Ψ_decompFESum K i lam)) (lin_relation' _)
    | cycCrossR j i μ =>
      exact lin_eq_zero_of_Ψ' (relation K (.cycCrossR j i μ))
        (relation K (.cycCrossR j.castSucc i.castSucc (phiW μ)))
        (Ψ_sub_eq (Ψ_rotCrossR K j i μ) (Ψ_downCross K j i μ)) (lin_relation' _)
    | cycCrossL j i μ =>
      exact lin_eq_zero_of_Ψ' (relation K (.cycCrossL j i μ))
        (relation K (.cycCrossL j.castSucc i.castSucc (phiW μ)))
        (Ψ_sub_eq (Ψ_rotCrossL K j i μ) (Ψ_downCross K j i μ)) (lin_relation' _)
    | downupEF i j h μ =>
      exact lin_eq_zero_of_Ψ' (relation K (.downupEF i j h μ))
        (relation K (.downupEF i.castSucc j.castSucc
          (fun e => h (Fin.castSucc_injective _ e)) (phiW μ)))
        (Ψ_sub_eq (Ψ_of_comp_eq (Ψ_crossl K i j μ) (Ψ_crossr K i j μ)) Ψ_of_id) (lin_relation' _)
    | downupFE i j h μ =>
      exact lin_eq_zero_of_Ψ' (relation K (.downupFE i j h μ))
        (relation K (.downupFE i.castSucc j.castSucc
          (fun e => h (Fin.castSucc_injective _ e)) (phiW μ)))
        (Ψ_sub_eq (Ψ_of_comp_eq (Ψ_crossr K j i μ) (Ψ_crossl K j i μ)) Ψ_of_id) (lin_relation' _)
    | klr μ r =>
      exact lin_eq_zero_of_Ψ (relation K (.klr μ r)) (relation K (.klr (phiW μ) (klrRel r))) _ _
        (Ψ_klr K μ r) (lin_relation' _)

end Relations

/-! ## The functor -/

section Functor

theorem embSig_odd (m : ℕ) (g : (psig (slRootDatum m)).Gen) :
    (psig (slRootDatum (m + 1))).odd ((embSig m).gen g) = (psig (slRootDatum m)).odd g := by
  rw [Signature.IsEven.odd_eq_false, Signature.IsEven.odd_eq_false]

theorem embSig_rel (K : Type w) [CommRing K] (m : ℕ) (r : (pres (slRootDatum m) K).Rel) :
    (freeLift K ((embSig m).toLayerMap.toPresented (pres (slRootDatum (m + 1)) K) fun _ => 1)).map
      ((pres (slRootDatum m) K).rel r) = 0 := by
  rw [LayerMap.freeLift_toPresented_one]
  exact lin_embSig_rel r

/-- **The 2-functor `U(sl_{m+1}) → U(sl_{m+2})`** on each hom-category (`K`-linear, commuting
with whiskering by `SigMap.lift_whisk`): the vertices of `sl_{m+1}` are the first `m` vertices
of `sl_{m+2}`, weights go to `phiW`. -/
def embedU (K : Type w) [CommRing K] (m : ℕ) :
    (pres (slRootDatum m) K).Presented ⥤ (pres (slRootDatum (m + 1)) K).Presented :=
  (embSig m).lift (pres (slRootDatum m) K) (embSig_odd m) (embSig_rel K m)

instance (K : Type w) [CommRing K] (m : ℕ) : (embedU K m).Additive := by
  unfold embedU; infer_instance

instance (K : Type w) [CommRing K] (m : ℕ) : (embedU K m).Linear K := by
  unfold embedU; infer_instance

@[simp] theorem embedU_obj {K : Type w} [CommRing K] {m : ℕ} (a : Obj (psig (slRootDatum m))) :
    (embedU K m).obj ((pres (slRootDatum m) K).obj a) =
      (pres (slRootDatum (m + 1)) K).obj (ιO a) :=
  rfl

/-- **`embedU` on a diagram** is the class of the relabelled diagram. -/
theorem embedU_diag {K : Type w} [CommRing K] {m : ℕ} {a b : Obj (psig (slRootDatum m))}
    (d : a ⟶ b) :
    (embedU K m).map ((pres (slRootDatum m) K).diag d) =
      (pres (slRootDatum (m + 1)) K).diag (ιD d) := by
  unfold embedU
  rw [SigMap.lift_diag, Diagram.weight, Diagram.weightList_one, one_smul]
  rfl

end Functor

end Categorification.KL3.Diagram.SlnEmbed

end
