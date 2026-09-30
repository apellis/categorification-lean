/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaIndepFunctor

/-!
# Bubbles on the far right under a `Γ_N`-like functor

Khovanov–Lauda III (arXiv:0807.3250v1), §6.4 (TeX `sln-2008-ArXiv.tex` l. 9598–9790): "`D_π`
acts on `HG_{k^i} ≅ HG_{k^i} ⊗_{HG_k} HG_k` via `Γ^G(Id_{1_λ} . D_π) = 1 ⊗_{HG_k} g_{D_π}`".

A diagram `f` whose image under `ιF` is a diagram `bb` of `1_λ` (a bubble) whiskered on the
left by the strands of its source acts, under a `Γ_N`-like functor, on the elements
`evXi q * iotaE z` by multiplying `z` by the element `x ∈ H_λ` by which `Γ_N(bb)` acts on `H_λ`
(`GammaLike.map_pvec_whisker`).
-/

noncomputable section

namespace Categorification.Flag.Indep

open Categorification.Flag Categorification.KL3.Diagram StringDiagrams CategoryTheory

universe u w₀ w₁ w₂

variable {K : Type u} [Field K] {m N : ℕ}

theorem lastR_append_nil : ∀ (s : Wt m) (u : List (WCol m)),
    lastR s (u ++ []) = (psig (slRootDatum m)).endR s u
  | _, [] => rfl
  | _, c :: u => lastR_append_nil c.r u

/-- Left whiskering of the multiplication by an element of the rightmost region. -/
theorem wlPath_mulB : ∀ (s : Wt m) (u : List (WCol m)) (hX hY : WOK N s (u ++ []))
    (x : H K (compOf N ((psig (slRootDatum m)).endR s u))),
    wlPath K N s u [] [] hX hY (BHom.mulB x) =
      BHom.mulB (iotaE s (u ++ []) hX _ (lastR_append_nil s u) x)
  | _, [], _, _, _ => rfl
  | s, c :: u, hX, hY, x => by
    show BHom.whiskerLeft _ (wlPath K N c.r u [] [] hX.tail hY.tail (BHom.mulB x)) = _
    rw [wlPath_mulB c.r u hX.tail hY.tail x, BHom.whiskerLeft_mulB]
    rfl

theorem iotaE_mul (s : Wt m) (W : List (WCol m)) (h : WOK N s W) (μ : Wt m)
    (e : lastR s W = μ) (x z : H K (compOf N μ)) :
    iotaE (K := K) s W h μ e (x * z) = iotaE s W h μ e x * iotaE s W h μ e z := map_mul _ _ _

theorem iotaE_congr (s : Wt m) (W : List (WCol m)) (h : WOK N s W) {μ μ' : Wt m}
    (e : lastR s W = μ) (e' : lastR s W = μ') (hμ : μ = μ') (x : H K (compOf N μ)) :
    iotaE (K := K) s W h μ e x = iotaE s W h μ' e' (hCast K (congrArg (compOf N) hμ) x) := by
  subst hμ; rfl

/-- Transport of a chain map along equalities of the end words and of the layer data. -/
theorem chainBD_transport (dnScal : Fin m → Fin m → K) (s : Wt m) {w₁ w₂ : List (WCol m)}
    {ls₁ ls₂ : List (LData m)} (e : w₁ = w₂) (el : ls₁ = ls₂) (h₁ : ChainW w₁ ls₁ w₁)
    (h₂ : ChainW w₂ ls₂ w₂) (ha₁ hb₁ : WOK N s w₁) (ha₂ hb₂ : WOK N s w₂) :
    chainBD K N dnScal s w₁ ls₁ w₁ h₁ ha₁ hb₁ =
      (trW s e.symm hb₂ hb₁).comp ((chainBD K N dnScal s w₂ ls₂ w₂ h₂ ha₂ hb₂).comp
        (trW s e ha₁ ha₂)) := by
  subst e el; rfl

variable {S₀ : Signature.{w₀, w₁, w₂}} {P₀ : Presentation S₀ K}
  {F : P₀.Presented ⥤ ModuleCat.{u} K} {ιF : Obj S₀ ⥤ Obj (psig (slRootDatum m))}
  {dnScal : Fin m → Fin m → K} {χ : (psig (slRootDatum m)).Gen → Kˣ}

namespace GammaLike

variable (hF : GammaLike F ιF N dnScal χ)

set_option backward.isDefEq.respectTransparency false in
include hF in
/-- **A bubble on the far right** multiplies the component of the rightmost region. -/
theorem map_pvec_whisker {a : Obj S₀} (f : a ⟶ a) {μ : Wt m}
    (bb : ob (slRootDatum m) μ [] ⟶ ob (slRootDatum m) μ []) (x : H K (compOf N μ))
    (hL : Diagram.layers (ιF.map f) = (Diagram.layers bb).map (·.whisker (ιF.obj a) []))
    (hend : (psig (slRootDatum m)).endR (ιF.obj a).start (ιF.obj a).word = μ)
    (hbb : ∀ (s : Wt m) (hs : s = μ) (ha hb : WOK N s ((ob (slRootDatum m) μ []).word ++ [])),
      evalB K N dnScal s [] ha hb (LinDiagram.of bb) = BHom.mulB (hCast K (congrArg (compOf N) hs.symm) x))
    (ha : WOK N (ιF.obj a).start (ιF.obj a).word) (e : lastR (ιF.obj a).start (ιF.obj a).word = μ)
    (q : MvPolynomial ℕ K) (z : H K (compOf N μ)) :
    (F.map (P₀.diag f)).hom (hF.pvec a ha μ e q z) =
      ((CL.Rescale.weight χ (Diagram.layers bb) : Kˣ) : K) • hF.pvec a ha μ e q (x * z) := by
  rw [pvec, hF.map_toF f ha ha]
  have hw : CL.Rescale.weight χ (Diagram.layers (ιF.map f)) = CL.Rescale.weight χ (Diagram.layers bb) := by
    rw [hL, CL.Rescale.weight_map_whisker]
  rw [hw]
  congr 2
  set u := ιF.obj a with hu
  have hwu : u.word = u.word ++ [] := (List.append_nil _).symm
  have hwu' : u.word ++ ([] : List (WCol m)) = u.word ++ (ob (slRootDatum m) μ []).word ++ [] := by
    simp
  have ha' : WOK N u.start (u.word ++ []) := hwu ▸ ha
  have hls : (Diagram.layers (ιF.map f)).map dat =
      (((Diagram.layers bb).map (dataV [])).map (LData.pre u.word)) := by
    rw [hL, List.map_map, List.map_map]; rfl
  have hch : ChainW ((ob (slRootDatum m) μ []).word ++ []) ((Diagram.layers bb).map (dataV []))
      ((ob (slRootDatum m) μ []).word ++ []) := chainW_of_chain [] (Diagram.chain bb)
  have hend' : (psig (slRootDatum m)).endR u.start u.word = μ := hend
  have hin : WOK N ((psig (slRootDatum m)).endR u.start u.word)
      ((ob (slRootDatum m) μ []).word ++ []) := (wok_append.1 ha').2
  have key := chainBD_prefix (K := K) (N := N) dnScal u.start u.word _
    ((Diagram.layers bb).map (dataV [])) _ hch ha' ha'
  have ev := hbb _ hend' hin hin
  rw [evalB_of] at ev
  rw [ev] at key
  have wm := wlPath_mulB (K := K) u.start u.word ha' ha' (hCast K (congrArg (compOf N) hend'.symm) x)
  erw [wm] at key
  -- transport the chain map along `u.word = u.word ++ []`
  have hc2 : ChainW u.word ((Diagram.layers (ιF.map f)).map dat) u.word :=
    chainW_dat (Diagram.chain (ιF.map f))
  have hc3 : ChainW (u.word ++ []) (((Diagram.layers bb).map (dataV [])).map (LData.pre u.word))
      (u.word ++ []) := hch.pre u.word
  have htr := chainBD_transport (K := K) (N := N) dnScal u.start hwu hls hc2 hc3 ha
    (wok_start (ιF.map f) ha) ha' ha'
  have hstart : chain_start (Diagram.chain (ιF.map f)) = (rfl : u.start = u.start) := rfl
  rw [htr]
  simp only [BHom.toLin_comp, LinearMap.comp_apply, BHom.toLin_apply]
  have e1 : lastR u.start (u.word ++ []) = μ := hwu ▸ e
  rw [shadow_trW (K := K) hwu ha ha' e e1 q z]
  simp only [id]
  have k2 := BHom.congr_apply key (evXi u.start (u.word ++ []) ha' q * iotaE u.start (u.word ++ []) ha' μ e1 z)
  erw [k2]
  rw [BHom.mulB_apply, iotaE_congr u.start (u.word ++ []) ha' _ e1 hend', hCast_trans_apply,
    hCast_rfl, mul_left_comm, ← iotaE_mul]
  rw [shadow_trW (K := K) hwu.symm ha' (wok_start (ιF.map f) ha) e1 e q (x * z)]
  exact shadow_startCast _ _ _ ha e e q (x * z)

end GammaLike

end Categorification.Flag.Indep

end
