/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaTarget

/-!
# Evaluating `Γ_N` on diagrams: chains of layers as bimodule maps

The functor `gammaFunctor` (`Categorification.Flag.GammaTarget`) sends a diagram to the composite
of the operators of its layers on the ambient module `Π i, M i`, between the inclusion and the
projection of the end components (`StringDiagrams.LocalInterpretation.functor_map_hom`). This file
identifies that composite with a **bimodule map** between path bimodules, for chains of layers
with a common start region (all whiskered diagrams are of this form):

* `chainBD s w ls w'`: the composite of the layer maps `layerMap` of the layers `ls` (given as
  data `(left, g, right)` from the region `s`), with the identifications `trW` between the
  (propositionally equal) boundary words of consecutive layers, and `0` as soon as an
  intermediate boundary is not valid;
* `opList_chain`: the projection of `opList` between the end components is `chainBD`
  (as a `K`-linear map);
* `chainBD_cons_prefix`: prefixing every layer by one strand `c` on the left whiskers `chainBD` by
  the step bimodule of `c` (`BHom.whiskerLeft`); by induction, prefixing by a word whiskers by
  its path (`chainBD_prefix`).

These are the facts `Presentation.Respects` needs about whiskering: the image of a relation
whiskered by `u` on the left is the whiskering by the path of `u` of the image of the relation
whiskered on the right only.
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-- A layer given by its data `(left, generator, right)`. -/
abbrev LData (m : ℕ) : Type := List (WCol m) × (psig (slRootDatum m)).Gen × List (WCol m)

/-- The layer `left ⊗ g ⊗ right` from the region `s`. -/
def LData.toLayer (s : Wt m) (d : LData m) : Layer (psig RD) := ⟨s, d.1, d.2.1, d.2.2⟩

/-- The boundary words of the layers `ls` match up, from `w` (bottom) to `w'` (top). -/
def ChainW : List (WCol m) → List (LData m) → List (WCol m) → Prop
  | w, [], w' => w = w'
  | w, d :: ls, w' => w = d.1 ++ gdom d.2.1 ++ d.2.2 ∧ ChainW (d.1 ++ gcod d.2.1 ++ d.2.2) ls w'

theorem BHom.toLin_csmul {A : Type u} [CommRing A] {M M' : BRing A K} (c : K) (φ : BHom M M') :
    BHom.toLin (BHom.csmul c φ) = c • BHom.toLin φ := rfl

theorem BHom.csmul_one {A : Type u} [CommRing A] {M M' : BRing A K} (φ : BHom M M') :
    BHom.csmul (1 : K) φ = φ :=
  BHom.ext fun x => by
    show M'.right 1 * φ x = φ x
    rw [map_one, one_mul]

theorem BHom.whiskerLeft_csmul {A B : Type u} [CommRing A] [CommRing B] (L : BRing A B)
    {M M' : BRing B K} (c : K) (φ : BHom M M') :
    BHom.whiskerLeft L (BHom.csmul c φ) = BHom.csmul c (BHom.whiskerLeft L φ) := by
  rw [BHom.csmul, BHom.csmul, BHom.whiskerLeft_comp, BHom.whiskerLeft_mulB]
  rfl

variable (K N)

open Classical in
/-- **The bimodule map of a chain of layers** from the region `s`. -/
def chainBD (dnScal : Fin m → Fin m → K) (s : Wt m) :
    (w : List (WCol m)) → (ls : List (LData m)) → (w' : List (WCol m)) → ChainW w ls w' →
    (ha : WOK N s w) → (hb : WOK N s w') → BHom (gammaR K N s w ha) (gammaR K N s w' hb)
  | _, [], _, h, ha, hb => trW s h ha hb
  | _, d :: ls, w', h, ha, hb =>
    if hL : WOK N s (d.1 ++ gcod d.2.1 ++ d.2.2) then
      (chainBD dnScal s _ ls w' h.2 hL hb).comp
        ((BHom.csmul (genScal K dnScal d.2.1) (layerMap K N s d.1 d.2.1 d.2.2 (h.1 ▸ ha) hL)).comp
          (trW s h.1 ha (h.1 ▸ ha)))
    else 0

variable {K N}

theorem proj_single (s : Wt m) {w₁ w₂ : List (WCol m)} (e : w₁ = w₂) (h₁ : WOK N s w₁)
    (h₂ : WOK N s w₂) :
    (LinearMap.proj (R := K) (φ := gammaMod K N) (some (⟨⟨s, w₂⟩, h₂⟩ : VObj N m))) ∘ₗ
        LinearMap.single K (gammaMod K N) (some (⟨⟨s, w₁⟩, h₁⟩ : VObj N m)) =
      BHom.toLin (trW (K := K) s e h₁ h₂) := by
  subst e
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply, Pi.single_eq_same]
  rfl

/-- **The functor on a chain of layers with a common start region is the bimodule map
`chainBD`.** -/
theorem opList_chain (dnScal : Fin m → Fin m → K) (s : Wt m) :
    ∀ (w : List (WCol m)) (ls : List (LData m)) (w' : List (WCol m)) (h : ChainW w ls w')
      (ha : WOK N s w) (hb : WOK N s w'),
      (LinearMap.proj (R := K) (φ := gammaMod K N) (some (⟨⟨s, w'⟩, hb⟩ : VObj N m))) ∘ₗ
          (gammaLI K N dnScal).opList (ls.map (LData.toLayer s)) ∘ₗ
          LinearMap.single K (gammaMod K N) (some (⟨⟨s, w⟩, ha⟩ : VObj N m)) =
        BHom.toLin (chainBD K N dnScal s w ls w' h ha hb)
  | w, [], w', h, ha, hb => by
    rw [List.map_nil, LocalInterpretation.opList_nil, LinearMap.id_comp]
    exact proj_single s h ha hb
  | w, d :: ls, w', h, ha, hb => by
    rw [List.map_cons, LocalInterpretation.opList_cons]
    by_cases hL : WOK N s (d.1 ++ gcod d.2.1 ++ d.2.2)
    · have hd : WOK N s (d.1 ++ gdom d.2.1 ++ d.2.2) := h.1 ▸ ha
      have hop : (gammaLI K N dnScal).op (LData.toLayer s d) =
          LinearMap.single K (gammaMod K N)
            (some (⟨⟨s, d.1 ++ gcod d.2.1 ++ d.2.2⟩, hL⟩ : VObj N m)) ∘ₗ
            BHom.toLin (BHom.csmul (genScal K dnScal d.2.1) (layerMap K N s d.1 d.2.1 d.2.2 hd hL)) ∘ₗ
            LinearMap.proj (R := K) (φ := gammaMod K N)
              (some (⟨⟨s, d.1 ++ gdom d.2.1 ++ d.2.2⟩, hd⟩ : VObj N m)) :=
        dif_pos (⟨hd, hL⟩ : WOK N s (d.1 ++ gdom d.2.1 ++ d.2.2) ∧
          WOK N s (d.1 ++ gcod d.2.1 ++ d.2.2))
      have ih := opList_chain dnScal s _ ls w' h.2 hL hb
      have hps := proj_single (K := K) s h.1 ha hd
      simp only [chainBD, dif_pos hL, BHom.toLin_comp]
      rw [hop, ← ih, ← hps]
      rfl
    · have hop : (gammaLI K N dnScal).op (LData.toLayer s d) = 0 :=
        dif_neg (fun hh => hL hh.2)
      rw [hop, LinearMap.comp_zero, LinearMap.zero_comp, LinearMap.comp_zero]
      simp only [chainBD, dif_neg hL]
      rfl

/-! ### Whiskering on the left -/

/-- Prefix the layer data by the strands `u` on the left. -/
def LData.pre (u : List (WCol m)) (d : LData m) : LData m := (u ++ d.1, d.2.1, d.2.2)

theorem ChainW.pre (u : List (WCol m)) :
    ∀ {w : List (WCol m)} {ls : List (LData m)} {w' : List (WCol m)}, ChainW w ls w' →
      ChainW (u ++ w) (ls.map (LData.pre u)) (u ++ w')
  | _, [], _, h => congrArg (u ++ ·) h
  | _, d :: ls, _, h => ⟨by rw [h.1]; simp [LData.pre, List.append_assoc],
      by simpa [LData.pre, List.append_assoc] using ChainW.pre u h.2⟩

theorem wok_cons_iff {s : Wt m} {c : WCol m} {w w' : List (WCol m)} (h : WOK N s (c :: w)) :
    WOK N s (c :: w') ↔ WOK N c.r w' :=
  ⟨fun h' => h'.tail, fun h' => ⟨h.1, h.2.1, h'⟩⟩

/-- **Prefixing all layers by one strand whiskers the chain map by its step bimodule.** -/
theorem chainBD_cons_prefix (dnScal : Fin m → Fin m → K) (s : Wt m) (c : WCol m) :
    ∀ (w : List (WCol m)) (ls : List (LData m)) (w' : List (WCol m)) (h : ChainW w ls w')
      (h' : ChainW (c :: w) (ls.map (LData.pre [c])) (c :: w')) (ha : WOK N s (c :: w))
      (hb : WOK N s (c :: w')),
      chainBD K N dnScal s (c :: w) (ls.map (LData.pre [c])) (c :: w') h' ha hb =
        BHom.whiskerLeft (stepB K c.l (compOf N c.r) (compOf N s) ha.step)
          (chainBD K N dnScal c.r w ls w' h ha.tail hb.tail)
  | w, [], w', h, h', ha, hb => by
    simp only [List.map_nil, chainBD]
    subst h
    exact (BHom.whiskerLeft_id _ _).symm
  | w, d :: ls, w', h, h', ha, hb => by
    simp only [List.map_cons, chainBD]
    by_cases hL : WOK N c.r (d.1 ++ gcod d.2.1 ++ d.2.2)
    · have hL' : WOK N s (c :: (d.1 ++ gcod d.2.1 ++ d.2.2)) := (wok_cons_iff ha).2 hL
      rw [dif_pos (show WOK N s ((LData.pre [c] d).1 ++ gcod (LData.pre [c] d).2.1 ++
        (LData.pre [c] d).2.2) from hL'), dif_pos hL, BHom.whiskerLeft_comp, BHom.whiskerLeft_comp,
        ← chainBD_cons_prefix dnScal s c _ ls w' h.2 h'.2 hL' hb, BHom.whiskerLeft_csmul]
      obtain ⟨e, _⟩ := h
      subst e
      rw [trW_self, trW_self, BHom.whiskerLeft_id]
      rfl
    · have hL' : ¬ WOK N s (c :: (d.1 ++ gcod d.2.1 ++ d.2.2)) := fun hh => hL hh.tail
      rw [dif_neg (show ¬ WOK N s ((LData.pre [c] d).1 ++ gcod (LData.pre [c] d).2.1 ++
        (LData.pre [c] d).2.2) from hL'), dif_neg hL]
      exact (BHom.whiskerLeft_zero _).symm

variable (K N) in
/-- **Whiskering by the path of the strands `u`** (from the region `s`) on the left. -/
def wlPath : (s : Wt m) → (u : List (WCol m)) → (X Y : List (WCol m)) →
    (hX : WOK N s (u ++ X)) → (hY : WOK N s (u ++ Y)) →
    BHom (gammaR K N ((psig RD).endR s u) X (wok_append.1 hX).2)
      (gammaR K N ((psig RD).endR s u) Y (wok_append.1 hY).2) →
    BHom (gammaR K N s (u ++ X) hX) (gammaR K N s (u ++ Y) hY)
  | _, [], _, _, _, _, φ => φ
  | s, c :: u, X, Y, hX, hY, φ =>
    BHom.whiskerLeft (stepB K c.l (compOf N c.r) (compOf N s) hX.step)
      (wlPath c.r u X Y hX.tail hY.tail φ)

theorem wlPath_zero : ∀ (s : Wt m) (u : List (WCol m)) (X Y : List (WCol m))
    (hX : WOK N s (u ++ X)) (hY : WOK N s (u ++ Y)), wlPath K N s u X Y hX hY 0 = 0
  | _, [], _, _, _, _ => rfl
  | s, c :: u, X, Y, hX, hY => by
    simp only [wlPath]
    rw [wlPath_zero c.r u X Y hX.tail hY.tail]
    exact BHom.whiskerLeft_zero _

theorem wlPath_add : ∀ (s : Wt m) (u : List (WCol m)) (X Y : List (WCol m))
    (hX : WOK N s (u ++ X)) (hY : WOK N s (u ++ Y)) (φ ψ),
    wlPath K N s u X Y hX hY (φ + ψ) = wlPath K N s u X Y hX hY φ + wlPath K N s u X Y hX hY ψ
  | _, [], _, _, _, _, _, _ => rfl
  | s, c :: u, X, Y, hX, hY, _, _ => by
    simp only [wlPath]
    rw [wlPath_add c.r u X Y hX.tail hY.tail]
    exact BHom.whiskerLeft_add _ _ _

theorem wlPath_neg : ∀ (s : Wt m) (u : List (WCol m)) (X Y : List (WCol m))
    (hX : WOK N s (u ++ X)) (hY : WOK N s (u ++ Y)) (φ),
    wlPath K N s u X Y hX hY (-φ) = -wlPath K N s u X Y hX hY φ
  | _, [], _, _, _, _, _ => rfl
  | s, c :: u, X, Y, hX, hY, φ => by
    simp only [wlPath]
    rw [wlPath_neg c.r u X Y hX.tail hY.tail]
    exact BHom.whiskerLeft_neg _ _

theorem wlPath_sub (s : Wt m) (u : List (WCol m)) (X Y : List (WCol m))
    (hX : WOK N s (u ++ X)) (hY : WOK N s (u ++ Y)) (φ ψ) :
    wlPath K N s u X Y hX hY (φ - ψ) = wlPath K N s u X Y hX hY φ - wlPath K N s u X Y hX hY ψ := by
  have e : φ - ψ = φ + -ψ := BHom.ext fun _ => sub_eq_add_neg _ _
  have e' : wlPath K N s u X Y hX hY φ - wlPath K N s u X Y hX hY ψ =
      wlPath K N s u X Y hX hY φ + -wlPath K N s u X Y hX hY ψ :=
    BHom.ext fun _ => sub_eq_add_neg _ _
  rw [e, e', wlPath_add, wlPath_neg]

theorem wlPath_csmul : ∀ (s : Wt m) (u : List (WCol m)) (X Y : List (WCol m))
    (hX : WOK N s (u ++ X)) (hY : WOK N s (u ++ Y)) (c : K) (φ),
    wlPath K N s u X Y hX hY (BHom.csmul c φ) = BHom.csmul c (wlPath K N s u X Y hX hY φ)
  | _, [], _, _, _, _, _, _ => rfl
  | s, c :: u, X, Y, hX, hY, k, φ => by
    simp only [wlPath]
    rw [wlPath_csmul c.r u X Y hX.tail hY.tail, BHom.whiskerLeft_csmul]

/-- **Prefixing all layers by the strands `u` whiskers the chain map by the path of `u`.** -/
theorem chainBD_prefix (dnScal : Fin m → Fin m → K) :
    ∀ (s : Wt m) (u : List (WCol m)) (w : List (WCol m)) (ls : List (LData m))
      (w' : List (WCol m)) (h : ChainW w ls w') (ha : WOK N s (u ++ w)) (hb : WOK N s (u ++ w')),
      chainBD K N dnScal s (u ++ w) (ls.map (LData.pre u)) (u ++ w') (h.pre u) ha hb =
        wlPath K N s u w w' ha hb
          (chainBD K N dnScal ((psig RD).endR s u) w ls w' h _ _)
  | s, [], w, ls, w', h, ha, hb => by
    have e : ls.map (LData.pre []) = ls := by
      conv_rhs => rw [← List.map_id ls]
      exact List.map_congr_left fun d _ => rfl
    simp only [wlPath]
    congr 1
  | s, c :: u, w, ls, w', h, ha, hb => by
    have e : ls.map (LData.pre (c :: u)) = (ls.map (LData.pre u)).map (LData.pre [c]) := by
      rw [List.map_map]
      exact List.map_congr_left fun d _ => rfl
    have hc := chainBD_cons_prefix (K := K) (N := N) dnScal s c (u ++ w) (ls.map (LData.pre u))
      (u ++ w') (h.pre u) (e ▸ h.pre (c :: u)) ha hb
    simp only [wlPath]
    erw [← chainBD_prefix dnScal c.r u w ls w' h ha.tail hb.tail, ← hc]
    congr 1

/-! ### Linear structure on bimodule maps -/

section Linear

variable {A : Type u} [CommRing A] {M M' : BRing A K}

theorem BHom.toLin_injective : Function.Injective (BHom.toLin : BHom M M' → (RT M →ₗ[K] RT M')) :=
  fun _ _ h => BHom.ext fun x => LinearMap.congr_fun h x

instance BHom.instSMulK : SMul K (BHom M M') := ⟨BHom.csmul⟩

instance BHom.instSMulNat : SMul ℕ (BHom M M') := ⟨fun n φ => BHom.csmul (n : K) φ⟩

instance BHom.instSMulInt : SMul ℤ (BHom M M') := ⟨fun n φ => BHom.csmul (n : K) φ⟩

instance BHom.instAddCommGroupK : AddCommGroup (BHom M M') :=
  Function.Injective.addCommGroup BHom.toLin BHom.toLin_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun φ n => (Nat.cast_smul_eq_nsmul K n (BHom.toLin φ)))
    (fun φ n => (Int.cast_smul_eq_zsmul K n (BHom.toLin φ)))

/-- `BHom.toLin` as an additive map. -/
def BHom.toLinAdd : BHom M M' →+ (RT M →ₗ[K] RT M') :=
  AddMonoidHom.mk' BHom.toLin (fun _ _ => rfl)

instance BHom.instModuleK : Module K (BHom M M') :=
  Function.Injective.module K BHom.toLinAdd BHom.toLin_injective (fun _ _ => rfl)

theorem BHom.smul_def (c : K) (φ : BHom M M') : c • φ = BHom.csmul c φ := rfl

/-- `BHom.toLin` as a `K`-linear map. -/
def BHom.toLinL : BHom M M' →ₗ[K] (RT M →ₗ[K] RT M') where
  toFun := BHom.toLin
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem BHom.toLinL_apply (φ : BHom M M') : BHom.toLinL φ = BHom.toLin φ := rfl

end Linear

variable (K N) in
/-- `wlPath` as a `K`-linear map. -/
def wlPathL (s : Wt m) (u : List (WCol m)) (X Y : List (WCol m)) (hX : WOK N s (u ++ X))
    (hY : WOK N s (u ++ Y)) :
    BHom (gammaR K N ((psig RD).endR s u) X (wok_append.1 hX).2)
        (gammaR K N ((psig RD).endR s u) Y (wok_append.1 hY).2) →ₗ[K]
      BHom (gammaR K N s (u ++ X) hX) (gammaR K N s (u ++ Y) hY) where
  toFun := wlPath K N s u X Y hX hY
  map_add' := wlPath_add s u X Y hX hY
  map_smul' c φ := wlPath_csmul s u X Y hX hY c φ

/-! ### Diagrams whiskered on the right -/

/-- The data of a layer whiskered by `v` on the right. -/
def dataV (v : List (psig RD).Colour) (L : Layer (psig RD)) : LData m := (L.left, L.gen, L.right ++ v)

theorem chainW_of_chain (v : List (psig RD).Colour) :
    ∀ {a b : Obj (psig RD)} {ls : List (Layer (psig RD))}, Chain a ls b →
      ChainW (a.word ++ v) (ls.map (dataV v)) (b.word ++ v)
  | _, _, [], h => by subst h; rfl
  | _, _, L :: ls, ⟨_, hd, hc⟩ => by
    subst hd
    exact ⟨by simp [dataV, Layer.dom, List.append_assoc],
      by simpa [dataV, Layer.cod, List.append_assoc] using chainW_of_chain v hc⟩

theorem chainBD_trW (dnScal : Fin m → Fin m → K) (s : Wt m) {w₁ w₂ w₁' w₂' : List (WCol m)}
    {ls : List (LData m)} (e : w₁ = w₂) (e' : w₁' = w₂') (h₁ : ChainW w₁ ls w₁')
    (h₂ : ChainW w₂ ls w₂') (ha₁ : WOK N s w₁) (ha₂ : WOK N s w₂) (hb₁ : WOK N s w₁')
    (hb₂ : WOK N s w₂') :
    chainBD K N dnScal s w₁ ls w₁' h₁ ha₁ hb₁ =
      (trW s e'.symm hb₂ hb₁).comp ((chainBD K N dnScal s w₂ ls w₂' h₂ ha₂ hb₂).comp
        (trW s e ha₁ ha₂)) := by
  subst e e'
  rfl

variable (K N) in
/-- **The bimodule evaluation of a linear combination of diagrams** `a ⟶ b`, whiskered by `v`
on the right, from the region `s` (the start region of `a`, up to equality). -/
def evalB (dnScal : Fin m → Fin m → K) {a b : Obj (psig RD)} (s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s (a.word ++ v)) (hb : WOK N s (b.word ++ v)) :
    LinDiagram K a b →ₗ[K] BHom (gammaR K N s (a.word ++ v) ha) (gammaR K N s (b.word ++ v) hb) :=
  Finsupp.linearCombination K fun f : a ⟶ b =>
    chainBD K N dnScal s (a.word ++ v) ((Diagram.layers f).map (dataV v)) (b.word ++ v)
      (chainW_of_chain v (Diagram.chain f)) ha hb

theorem evalB_of (dnScal : Fin m → Fin m → K) {a b : Obj (psig RD)} (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s (a.word ++ v)) (hb : WOK N s (b.word ++ v)) (f : a ⟶ b) :
    evalB K N dnScal s v ha hb (LinDiagram.of f) =
      chainBD K N dnScal s (a.word ++ v) ((Diagram.layers f).map (dataV v)) (b.word ++ v)
        (chainW_of_chain v (Diagram.chain f)) ha hb := by
  exact (Finsupp.linearCombination_single K 1 f).trans (one_smul _ _)

/-- **The image of a whiskered diagram** is the whiskering by the path of `u` of the bimodule map
of the diagram whiskered on the right only, up to the associativity of the boundary words. -/
theorem evalW_of_eq (dnScal : Fin m → Fin m → K) {a b : Obj (psig RD)} (f : a ⟶ b)
    (u : Obj (psig RD)) (v : List (psig RD).Colour) (ha : WOK N u.start (u.word ++ a.word ++ v))
    (hb : WOK N u.start (u.word ++ b.word ++ v))
    (ha' : WOK N u.start (u.word ++ (a.word ++ v))) (hb' : WOK N u.start (u.word ++ (b.word ++ v))) :
    (Diagram.layers f).map (·.whisker u v) =
        (((Diagram.layers f).map (dataV v)).map (LData.pre u.word)).map (LData.toLayer u.start) ∧
      (LinearMap.proj (R := K) (φ := gammaMod K N) (some (⟨b.whisker u v, hb⟩ : VObj N m))) ∘ₗ
          (gammaLI K N dnScal).opList ((Diagram.layers f).map (·.whisker u v)) ∘ₗ
          LinearMap.single K (gammaMod K N) (some (⟨a.whisker u v, ha⟩ : VObj N m)) =
        BHom.toLin ((trW u.start (List.append_assoc _ _ _).symm hb' hb).comp
          ((wlPath K N u.start u.word (a.word ++ v) (b.word ++ v) ha' hb'
            (evalB K N dnScal _ v _ _ (LinDiagram.of f))).comp
          (trW u.start (List.append_assoc _ _ _) ha ha'))) := by
  have hmap : (Diagram.layers f).map (·.whisker u v) =
      (((Diagram.layers f).map (dataV v)).map (LData.pre u.word)).map (LData.toLayer u.start) := by
    rw [List.map_map, List.map_map]
    rfl
  refine ⟨hmap, ?_⟩
  have hch := (chainW_of_chain v (Diagram.chain f)).pre u.word
  have hch' : ChainW (u.word ++ a.word ++ v) (((Diagram.layers f).map (dataV v)).map
      (LData.pre u.word)) (u.word ++ b.word ++ v) := by
    simpa only [List.append_assoc] using hch
  rw [hmap]
  have := opList_chain (K := K) (N := N) dnScal u.start _ _ _ hch' ha hb
  erw [this]
  rw [evalB_of, ← chainBD_prefix,
    ← chainBD_trW (e := List.append_assoc _ _ _) (e' := List.append_assoc _ _ _)]

/-! ### Reduction of `Respects` to the bimodule evaluation -/

theorem gammaIdx_whisker_of_wok {a u : Obj (psig RD)} {v : List (psig RD).Colour}
    (h : WOK N u.start (u.word ++ a.word ++ v)) :
    gammaIdx N (a.whisker u v) = some ⟨a.whisker u v, h⟩ := gammaIdx_of_wok N h

theorem linearMap_from_punit_eq_zero {M : Type u} [AddCommGroup M] [Module K M]
    (f : PUnit.{u + 1} →ₗ[K] M) : f = 0 :=
  LinearMap.ext fun x => by rw [show x = 0 from Subsingleton.elim _ _, map_zero]; rfl

theorem linearMap_to_punit_eq_zero {M : Type u} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] PUnit.{u + 1}) : f = 0 :=
  LinearMap.ext fun _ => Subsingleton.elim _ _

/-- **`Respects` from the bimodule evaluation.** If, for every right whiskering `v`, the bimodule
evaluation of a linear combination `X` of diagrams `a ⟶ b` vanishes (from any region equal to the
start region of `a`, whenever both ends are valid), then the image of `X` under `Γ_N` vanishes
after whiskering by arbitrary `u` and `v`. -/
theorem evalW_eq_zero_of_evalB (dnScal : Fin m → Fin m → K) {a b : Obj (psig RD)}
    (X : LinDiagram K a b) (u : Obj (psig RD)) (v : List (psig RD).Colour)
    (hw : a.WhiskerOK u v)
    (hX : ∀ (s : Wt m), s = a.start → ∀ (ha : WOK N s (a.word ++ v)) (hb : WOK N s (b.word ++ v)),
      evalB K N dnScal s v ha hb X = 0) :
    (gammaLI K N dnScal).evalW ((gammaLI K N dnScal).κ (a.whisker u v))
      ((gammaLI K N dnScal).κ (b.whisker u v)) u v X = 0 := by
  show (gammaLI K N dnScal).evalW (gammaIdx N (a.whisker u v)) (gammaIdx N (b.whisker u v)) u v X
    = 0
  by_cases ha : WOK N u.start (u.word ++ a.word ++ v)
  · by_cases hb : WOK N u.start (u.word ++ b.word ++ v)
    · rw [gammaIdx_whisker_of_wok ha, gammaIdx_whisker_of_wok hb]
      have ha' : WOK N u.start (u.word ++ (a.word ++ v)) := by rwa [← List.append_assoc]
      have hb' : WOK N u.start (u.word ++ (b.word ++ v)) := by rwa [← List.append_assoc]
      set F : BHom (gammaR K N ((psig RD).endR u.start u.word) (a.word ++ v) (wok_append.1 ha').2)
          (gammaR K N ((psig RD).endR u.start u.word) (b.word ++ v) (wok_append.1 hb').2) →ₗ[K]
          (gammaMod K N (some (⟨a.whisker u v, ha⟩ : VObj N m)) →ₗ[K]
            gammaMod K N (some (⟨b.whisker u v, hb⟩ : VObj N m))) :=
        { toFun := fun φ => BHom.toLin ((trW u.start (List.append_assoc _ _ _).symm hb' hb).comp
            ((wlPath K N u.start u.word (a.word ++ v) (b.word ++ v) ha' hb' φ).comp
              (trW u.start (List.append_assoc _ _ _) ha ha')))
          map_add' := fun φ ψ => by
            rw [wlPath_add]
            refine LinearMap.ext fun x => ?_
            show trW _ _ _ _ ((wlPath K N u.start u.word _ _ ha' hb' φ + _) _) = _
            rw [BHom.add_apply, BHom.map_add]
            rfl
          map_smul' := fun c φ => by
            rw [BHom.smul_def, wlPath_csmul]
            refine LinearMap.ext fun x => ?_
            show trW _ _ _ _ (_ * _) = _
            rw [BHom.map_right]
            rfl } with hF
      have key : ∀ Y : LinDiagram K a b, (gammaLI K N dnScal).evalW
          (some (⟨a.whisker u v, ha⟩ : VObj N m)) (some (⟨b.whisker u v, hb⟩ : VObj N m)) u v Y =
          F (evalB K N dnScal _ v (wok_append.1 ha').2 (wok_append.1 hb').2 Y) := by
        intro Y
        induction Y using Finsupp.induction_linear with
        | zero => rw [map_zero, map_zero, map_zero]
        | add Y Z hY hZ => rw [map_add, map_add, map_add, hY, hZ]
        | single f r =>
          rw [LocalInterpretation.evalW_single, show (Finsupp.single f r : LinDiagram K a b) =
            r • LinDiagram.of f from by rw [LinDiagram.of, Finsupp.smul_single, smul_eq_mul, mul_one],
            map_smul, map_smul]
          congr 1
          exact (evalW_of_eq dnScal f u v ha hb ha' hb').2
      rw [key, hX ((psig RD).endR u.start u.word) hw.2.1, map_zero]
    · rw [show gammaIdx N (b.whisker u v) = none from gammaIdx_of_not_wok N hb]
      exact linearMap_to_punit_eq_zero _
  · rw [show gammaIdx N (a.whisker u v) = none from gammaIdx_of_not_wok N ha]
    exact linearMap_from_punit_eq_zero _

end Categorification.Flag

end
