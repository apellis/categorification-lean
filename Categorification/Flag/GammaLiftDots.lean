/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftBasic
import Categorification.Flag.GammaCupCap

/-!
# `Γ_N` respects the dot cyclicity relations `cycDotR`, `cycDotL`

KL III, arXiv:0807.3250v1, Definition 3.1, eq. (3.3) (`Categorification.KL3.Diagram.Rel.cycDotR`,
`cycDotL`; unchanged in Cautis–Lauda's `U_Q(g)`).

This is the first family of relations checked through the assembly of `Γ_N`
(`Categorification.Flag.gamma_respects`): the hypothesis required there is the vanishing of the
bimodule evaluation `evalB` of the relation. The method, used for every relation:

1. rewrite the layer data of each diagram of the relation into **canonical data**, in which the
   weight of every region is written in the syntactic form produced by the generators before it
   (`chainBD_eq_of_congr`; the equality of the data is weight arithmetic);
2. on canonical data the identifications `trW`, `trS` between consecutive boundaries are
   identities by definition, the validity case distinctions are decided, and the chain map is
   the composite of the generator maps (`canon_rotDotR`, `canon_rotDotL`);
3. identify that composite with the path-model theorem (`cycDot_F'`, `cycDot_F`).
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

theorem BHom.comp_id' {A B : Type u} [CommRing A] [CommRing B] {M M' : BRing A B}
    (φ : BHom M M') : φ.comp (BHom.id M) = φ := BHom.ext fun _ => rfl

theorem trS_self' (l : SLetter m) (L a : Wt m) (e : a = a) (p : List (WCol m))
    (h h' : StepR l (compOf N a) (compOf N L)) (hp hp' : WOK N a p) :
    trS (K := K) l L a a e p h h' hp hp' = BHom.id _ := rfl

set_option maxHeartbeats 1000000 in
/-- The canonical chain of `rotDotR` from the region `s`. -/
theorem canon_rotDotR (dnScal : Fin m → Fin m → K) (i : Fin m) (s : Wt m)
    (v : List (psig RD).Colour)
    (h₂ : ChainW (⟨dn i, sh RD (up i) + s⟩ :: v)
      [([⟨dn i, sh RD (up i) + s⟩], .cup ⟨up i, s⟩, v),
       ([⟨dn i, sh RD (up i) + s⟩], .gen (.dot ⟨up i, s⟩), ⟨dn i, sh RD (up i) + s⟩ :: v),
       ([], .cap ⟨up i, s⟩, ⟨dn i, sh RD (up i) + s⟩ :: v)] (⟨dn i, sh RD (up i) + s⟩ :: v))
    (k₂ : ChainW (⟨dn i, sh RD (up i) + s⟩ :: v) [([], .gen (.dot ⟨dn i, sh RD (up i) + s⟩), v)]
      (⟨dn i, sh RD (up i) + s⟩ :: v))
    (ha : WOK N s (⟨dn i, sh RD (up i) + s⟩ :: v)) :
    chainBD K N dnScal s _ _ _ h₂ ha ha = chainBD K N dnScal s _ _ _ k₂ ha ha := by
  have hmid : WOK N s ([⟨dn i, sh RD (up i) + s⟩] ++ gcod (.cup ⟨up i, s⟩ : (psig RD).Gen) ++ v) :=
    ⟨ha.1, ha.2.1, ha.2.2.realized, rfl, ha.1, ha.2.1, ha.2.2⟩
  simp only [chainBD]
  split_ifs with h1 h2 h3 h4
  · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
    simp only [layerMap, genMap, capMap, cupMap, dotMap, trS_self', BHom.whiskerLeft_id,
      BHom.id_comp', BHom.comp_id']
    simp only [BHom.whiskerLeft_id, BHom.comp_id', locOne, BHom.whiskerRight_mulB,
      BHom.whiskerLeft_mulB, BHom.comp_assoc]
    erw [BHom.whiskerLeft_id, BHom.id_comp']
    exact cycDot_F' (K := K) i (s := compOf N s) (s' := compOf N (sh RD (up i) + s))
      (ha.step : StepR (true, i) (compOf N s) (compOf N (sh RD (up i) + s))) ha.step
      (gammaR K N (sh RD (up i) + s) v ha.2.2)
  all_goals first
    | exact absurd hmid ‹_›
    | exact absurd ha ‹_›

/-- **`Γ_N` respects `cycDotR`** (KL III (3.3), left-hand picture): the rotation of the upward
dot by the cup `1 → E F` on the right and the cap `F E → 1` on the left is the downward dot. -/
theorem evalB_cycDotR (dnScal : Fin m → Fin m → K) (i : Fin m) (μ : Wt m) (s : Wt m)
    (hs : s = (ob RD μ [dn i]).start) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ [dn i]).word ++ v)) (hb : WOK N s ((ob RD μ [dn i]).word ++ v)) :
    evalB K N dnScal s v ha hb (LinDiagram.of (rotDotR RD i μ) - LinDiagram.of (downDot RD i μ))
      = 0 := by
  have e1 : μ = sh RD (up i) + s := by
    rw [hs]
    show μ = sh RD (up i) + (sh RD (dn i) + μ)
    rw [← add_assoc, show sh RD (up i) + sh RD (dn i) = 0 from sh_add_sh_dual RD (up i), zero_add]
  have ew : (ob RD μ [dn i]).word ++ v = (⟨dn i, sh RD (up i) + s⟩ :: v : List (WCol m)) := by
    show ⟨dn i, μ⟩ :: v = _
    rw [← e1]
  have ha₂ : WOK N s (⟨dn i, sh RD (up i) + s⟩ :: v) := ew ▸ ha
  rw [map_sub, evalB_of, evalB_of, sub_eq_zero]
  have e2 : wt RD μ ((Shape.dot (up i)).dom ++ [dn i]) = μ := by
    show sh RD (up i) + (sh RD (dn i) + μ) = μ
    rw [← add_assoc, show sh RD (up i) + sh RD (dn i) = 0 from sh_add_sh_dual RD (up i), zero_add]
  refine chainBD_eq_of_congr dnScal s ew ew ?_ ?_ _ (by exact ⟨rfl, rfl, rfl, rfl⟩) _
    (by exact ⟨rfl, rfl⟩) ha ha₂ hb ha₂
    (canon_rotDotR dnScal i s v _ _ ha₂)
  · simp only [rotDotR, layers_mkD, layList, List.map_cons, List.map_nil, dataV, lay, wd, wt,
      Shape.gen, List.nil_append, List.cons_append, List.append_nil, List.singleton_append]
    rw [e2, ← e1, hs]
    rfl
  · simp only [downDot, layers_mkD, layList, List.map_cons, List.map_nil, dataV, lay, wd, wt,
      Shape.gen, List.nil_append, List.cons_append, List.append_nil]
    rw [← e1]

set_option maxHeartbeats 1000000 in
/-- The canonical chain of `rotDotL` from the region `sh (dn i) + t`. -/
theorem canon_rotDotL (dnScal : Fin m → Fin m → K) (i : Fin m) (t : Wt m)
    (v : List (psig RD).Colour)
    (h₂ : ChainW (⟨dn i, t⟩ :: v)
      [([], .cup ⟨dn i, t⟩, ⟨dn i, t⟩ :: v),
       ([⟨dn i, t⟩], .gen (.dot ⟨up i, sh RD (dn i) + t⟩), ⟨dn i, t⟩ :: v),
       ([⟨dn i, t⟩], .cap ⟨dn i, t⟩, v)] (⟨dn i, t⟩ :: v))
    (k₂ : ChainW (⟨dn i, t⟩ :: v) [([], .gen (.dot ⟨dn i, t⟩), v)] (⟨dn i, t⟩ :: v))
    (ha : WOK N (sh RD (dn i) + t) (⟨dn i, t⟩ :: v)) :
    chainBD K N dnScal (sh RD (dn i) + t) _ _ _ h₂ ha ha =
      chainBD K N dnScal (sh RD (dn i) + t) _ _ _ k₂ ha ha := by
  have hmid : WOK N (sh RD (dn i) + t)
      ([] ++ gcod (.cup ⟨dn i, t⟩ : (psig RD).Gen) ++ ⟨dn i, t⟩ :: v) :=
    ⟨ha.1, rfl, ha.2.2.realized, sh_cancel false i t, ha.1, rfl, ha.2.2⟩
  simp only [chainBD]
  split_ifs with h1 h2 h3 h4
  · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
    simp only [layerMap, genMap, capMap, cupMap, dotMap, trS_self', BHom.whiskerLeft_id,
      BHom.id_comp', BHom.comp_id']
    simp only [BHom.whiskerLeft_id, BHom.comp_id', locOne, BHom.whiskerRight_mulB,
      BHom.whiskerLeft_mulB, BHom.comp_assoc]
    erw [BHom.whiskerLeft_id, BHom.comp_id']
    exact cycDot_F (K := K) i (s := compOf N (sh RD (dn i) + t)) (s' := compOf N t)
      (ha.step : StepR (true, i) (compOf N (sh RD (dn i) + t)) (compOf N t)) ha.step
      (gammaR K N t v ha.2.2)
  all_goals first
    | exact absurd hmid ‹_›
    | exact absurd ha ‹_›

/-- **`Γ_N` respects `cycDotL`** (KL III (3.3), right-hand picture): the rotation of the upward
dot by the cup `1 → F E` on the left and the cap `E F → 1` on the right is the downward dot. -/
theorem evalB_cycDotL (dnScal : Fin m → Fin m → K) (i : Fin m) (μ : Wt m) (s : Wt m)
    (hs : s = (ob RD μ [dn i]).start) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ [dn i]).word ++ v)) (hb : WOK N s ((ob RD μ [dn i]).word ++ v)) :
    evalB K N dnScal s v ha hb (LinDiagram.of (rotDotL RD i μ) - LinDiagram.of (downDot RD i μ))
      = 0 := by
  subst hs
  have e2 : sh RD (up i) + (sh RD (dn i) + μ) = μ := sh_cancel false i μ
  rw [map_sub, evalB_of, evalB_of, sub_eq_zero]
  refine chainBD_eq_of_congr dnScal _ rfl rfl ?_ ?_ _ (by exact ⟨rfl, rfl, rfl, rfl⟩) _
    (by exact ⟨rfl, rfl⟩) ha ha hb hb (canon_rotDotL dnScal i μ v _ _ ha)
  · simp only [rotDotL, layers_mkD, layList, List.map_cons, List.map_nil, dataV, lay, wd, wt,
      Shape.gen, List.nil_append, List.cons_append, List.append_nil, List.singleton_append]
    rw [show sh RD (dn i).dual + (sh RD (dn i) + μ) = μ from e2,
      show wt RD μ ((Shape.dot (up i)).dom ++ [dn i]) = μ from e2,
      show wt RD μ (Shape.cap (dn i)).dom = μ from e2]
  · simp only [downDot, layers_mkD, layList, List.map_cons, List.map_nil, dataV, lay, wd, wt,
      Shape.gen, List.nil_append, List.cons_append, List.append_nil]

end Categorification.Flag

end
