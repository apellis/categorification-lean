/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftPoly
import Categorification.Diagrams.KL3.GammaFlagDecomp

/-!
# `Γ_N` of bubbles, cups and caps with dots, and bubbles next to a strand

KL III, arXiv:0807.3250v1, Definition 3.1 (the dotted bubbles, macros `cbub`, `ccbub`; the fake
bubbles, eq. `eq_infinite_Grass`; the cups and caps with dots of `eq_ident_decomp`) and
Proposition 6.3.

The bimodule evaluation `evalB` (`Categorification.Flag.GammaEval`) of the diagrams of
`Categorification.KL3.Diagram.Relations` that the relations `cwNeg`, `ccwNeg`, `cwOne`, `ccwOne`,
`curlR`, `curlL`, `decompEF`, `decompFE` are built from:

* `evalB_cupDotEF`, `evalB_dotCapEF`, `evalB_cupDotFE`, `evalB_dotCapFE`: the cups and caps
  followed or preceded by dots are `cupEFW`, `capEFW`, `cupFEW`, `capFEW` composed with
  multiplication by powers of `ξ`; `evalB_dots_first_bub`: dots on a single strand;
* **real bubbles** (`evalB_cwReal`, `evalB_ccwReal`): multiplication by `cwRealH`, `ccwRealH` on
  every 1-morphism to their right (also when the 1-morphism through which the bubble factors is
  zero: then the bubble is `0` and so is `cwRealH`, `ccwRealH`);
* **fake bubbles** (`evalB_cwL`, `evalB_ccwL`): the labelled bubbles `cwL`, `ccwL` of
  Definition 3.1, defined by the Grassmannian recursion, act by `cwLH`, `ccwLH` (whose closed
  forms are `cwLH_eq`, `ccwLH_eq`), via `evalB_grassInv`; products of bubbles are composites
  (`evalB_mul_bub`);
* bubbles next to an upward strand (`evalB_bubR_up`, `evalB_bubL_up`).

Tools used for all relations: `chainBD_dots_append`, `chainBD_three` (chains of dots, of three
layers), `trW_head` (a change of the region to the right of one strand is `trS`), and
`chainBD_eq_zero_of_first`.
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory Categorification.KL3.Diagram.Signed

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### Normalization lemmas (definitional, for `dsimp`) -/

theorem bnot_false_rfl : (!false) = true := rfl

theorem bnot_true_rfl : (!true) = false := rfl

theorem list_nil_append_rfl {α : Type*} (l : List α) : ([] : List α).append l = l := rfl

theorem list_cons_append_rfl {α : Type*} (a : α) (l l' : List α) :
    (a :: l).append l' = a :: (l.append l') := rfl

theorem gcod_cap_rfl (c : WCol m) : gcod (.cap c : (psig RD).Gen) = [] := rfl

theorem gdom_cup_rfl (c : WCol m) : gdom (.cup c : (psig RD).Gen) = [] := rfl

theorem gcod_cup_rfl (c : WCol m) :
    gcod (.cup c : (psig RD).Gen) = [c, ⟨c.l.dual, sh RD c.l + c.r⟩] := rfl

theorem gdom_cap_rfl (c : WCol m) :
    gdom (.cap c : (psig RD).Gen) = [⟨c.l.dual, sh RD c.l + c.r⟩, c] := rfl

theorem gdom_dot_rfl (c : WCol m) : gdom (.gen (.dot c) : (psig RD).Gen) = [c] := rfl

theorem gcod_dot_rfl (c : WCol m) : gcod (.gen (.dot c) : (psig RD).Gen) = [c] := rfl

theorem gdom_cross_rfl (ε : Bool) (i j : Fin m) (ν : Wt m) :
    gdom (.gen (.cross ε i j ν) : (psig RD).Gen) = [⟨(ε, i), sh RD (ε, j) + ν⟩, ⟨(ε, j), ν⟩] := rfl

theorem gcod_cross_rfl (ε : Bool) (i j : Fin m) (ν : Wt m) :
    gcod (.gen (.cross ε i j ν) : (psig RD).Gen) = [⟨(ε, j), sh RD (ε, i) + ν⟩, ⟨(ε, i), ν⟩] := rfl

/-! ### Identifications of regions -/

/-- `trW` changing only the region to the right of the first strand is `trS`. -/
theorem trW_head (s : Wt m) (l : SLetter m) (a b : Wt m) (w : List (WCol m))
    (e : (⟨l, a⟩ : WCol m) :: w = ⟨l, b⟩ :: w) (h : WOK N s (⟨l, a⟩ :: w))
    (h' : WOK N s (⟨l, b⟩ :: w)) :
    trW (K := K) s e h h' = trS l s a b (by injection e with e1; injection e1) w h.step h'.step
      h.tail h'.tail := by
  have eab : a = b := by injection e with e1; injection e1
  subst eab
  rfl

theorem sh_up_dn (i : Fin m) (r : Wt m) : sh RD (up i) + (sh RD (dn i) + r) = r :=
  sh_cancel false i r

theorem sh_dn_up (i : Fin m) (r : Wt m) : sh RD (dn i) + (sh RD (up i) + r) = r :=
  sh_cancel true i r

theorem trS_trans' (l : SLetter m) (L a b c : Wt m) (e : a = b) (e' : b = c) (p : List (WCol m))
    (h : StepR l (compOf N a) (compOf N L)) (h' : StepR l (compOf N b) (compOf N L))
    (h'' : StepR l (compOf N c) (compOf N L)) (hp : WOK N a p) (hp' : WOK N b p)
    (hp'' : WOK N c p) :
    (trS (K := K) l L b c e' p h' h'' hp' hp'').comp (trS l L a b e p h h' hp hp') =
      trS l L a c (e.trans e') p h h'' hp hp'' := by
  subst e e'
  rfl

theorem trS_self'' (l : SLetter m) (L a : Wt m) (e : a = a) (p : List (WCol m))
    (h h' : StepR l (compOf N a) (compOf N L)) (hp hp' : WOK N a p) :
    trS (K := K) l L a a e p h h' hp hp' = BHom.id _ := rfl

theorem BHom.comp_id'' {A B : Type u} [CommRing A] [CommRing B] {M M' : BRing A B}
    (φ : BHom M M') : φ.comp (BHom.id M) = φ := BHom.ext fun _ => rfl

theorem BHom.mulB_pow_comp {A B : Type u} [CommRing A] [CommRing B] {M : BRing A B} (x : M.T)
    (n : ℕ) :
    (BHom.mulB (x ^ n)).comp (BHom.mulB x) = BHom.mulB (x ^ (n + 1)) := by
  rw [BHom.mulB_comp_mulB, pow_succ]

/-! ### Chains of dots -/

/-- **A chain of `n` equal dot layers** followed by a chain `ls`: multiplication by the `n`-th
power of the dot, then `ls`. -/
theorem chainBD_dots_append (dnScal : Fin m → Fin m → K) (s : Wt m) (L R : List (WCol m))
    (c : WCol m) (hW : WOK N s (L ++ [c] ++ R)) (x : (gammaR K N s (L ++ [c] ++ R) hW).T)
    (hx : layerMap K N s L (.gen (.dot c)) R hW hW = BHom.mulB x) :
    ∀ (n : ℕ) (ls : List (LData m)) (w' : List (WCol m))
      (h : ChainW (L ++ [c] ++ R) (List.replicate n (L, .gen (.dot c), R) ++ ls) w')
      (h' : ChainW (L ++ [c] ++ R) ls w') (hb : WOK N s w'),
      chainBD K N dnScal s _ _ w' h hW hb =
        (chainBD K N dnScal s _ ls w' h' hW hb).comp (BHom.mulB (x ^ n))
  | 0, ls, w', h, h', hb => by
    rw [pow_zero, BHom.mulB_one]
    rfl
  | n + 1, ls, w', h, h', hb => by
    have ih := chainBD_dots_append dnScal s L R c hW x hx n ls w' h.2 h' hb
    simp only [List.replicate_succ, List.cons_append, chainBD]
    rw [dite_eq_left (show WOK N s (L ++ gcod (.gen (.dot c)) ++ R) from hW)]
    erw [ih]
    rw [show genScal K dnScal (PivotalGen.gen (Gen0.dot c) : (psig RD).Gen) = 1 from rfl,
      BHom.csmul_one, trW_self]
    erw [hx]
    rw [BHom.comp_assoc, BHom.comp_id'', BHom.mulB_comp_mulB, ← pow_succ]

/-- `n` equal dot layers: multiplication by the `n`-th power of the dot. -/
theorem chainBD_dots (dnScal : Fin m → Fin m → K) (s : Wt m) (L R : List (WCol m))
    (c : WCol m) (hW : WOK N s (L ++ [c] ++ R)) (x : (gammaR K N s (L ++ [c] ++ R) hW).T)
    (hx : layerMap K N s L (.gen (.dot c)) R hW hW = BHom.mulB x) (n : ℕ)
    (h : ChainW (L ++ [c] ++ R) (List.replicate n (L, .gen (.dot c), R)) (L ++ [c] ++ R))
    (hb : WOK N s (L ++ [c] ++ R)) :
    chainBD K N dnScal s _ _ _ h hW hb = BHom.mulB (x ^ n) := by
  have el : List.replicate n ((L, .gen (.dot c), R) : LData m) =
      List.replicate n (L, .gen (.dot c), R) ++ [] := (List.append_nil _).symm
  have h' : ChainW (L ++ [c] ++ R) (List.replicate n (L, .gen (.dot c), R) ++ [])
      (L ++ [c] ++ R) := el ▸ h
  rw [chainBD_congr dnScal s rfl rfl el h h' hW hW hb hb]
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']
  rw [chainBD_dots_append dnScal s L R c hW x hx n [] _ h' rfl hb]
  exact BHom.id_comp' _

theorem wok_congr_region {s s' : Wt m} {w : List (WCol m)} (e : s = s') (h : WOK N s w) :
    WOK N s' w := e ▸ h

/-- The dot on the second strand of `E_i F_i ⊗ Y`. -/
theorem layerMap_dot_second (s : Wt m) (cE cF : WCol m) (R : List (WCol m))
    (h : WOK N s ([cE] ++ [cF] ++ R)) :
    layerMap K N s [cE] (.gen (.dot cF)) R h h =
      BHom.mulB (BRing.tmul (stepB K cE.l (compOf N cE.r) (compOf N s) h.step)
        ((stepB K cF.l (compOf N cF.r) (compOf N cE.r) h.tail.step).tensor
          (gammaR K N cF.r R h.tail.tail)) 1
        (BRing.tmul _ _ (xiStep K cF.l (compOf N cF.r) (compOf N cE.r) h.tail.step) 1)) := by
  simp only [layerMap, genMap, dotMap, locOne, BHom.whiskerRight_mulB, BHom.whiskerLeft_mulB]
  rfl

/-- The dot on the first strand of `c ⊗ Y`. -/
theorem layerMap_dot_first (s : Wt m) (c : WCol m) (R : List (WCol m))
    (h : WOK N s ([] ++ [c] ++ R)) :
    layerMap K N s [] (.gen (.dot c)) R h h =
      BHom.mulB (BRing.tmul (stepB K c.l (compOf N c.r) (compOf N s) h.step)
        (gammaR K N c.r R h.tail) (xiStep K c.l (compOf N c.r) (compOf N s) h.step) 1) := by
  simp only [layerMap, genMap, dotMap, locOne, BHom.whiskerRight_mulB]

theorem tmul_one_tmul_pow {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (M : BRing A B) (P : BRing B C) (Q : BRing C K) (a : P.T) (n : ℕ) :
    (BRing.tmul M (P.tensor Q) 1 (BRing.tmul P Q a 1)) ^ n =
      BRing.tmul M (P.tensor Q) 1 (BRing.tmul P Q (a ^ n) 1) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ← BRing.one_eq, ← BRing.one_eq]
  | succ n ih => rw [pow_succ, ih, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, mul_one,
      pow_succ]

theorem tmul_pow_one {A B : Type u} [CommRing A] [CommRing B] (M : BRing A B) (Q : BRing B K)
    (a : M.T) (n : ℕ) : (BRing.tmul M Q a 1) ^ n = BRing.tmul M Q (a ^ n) 1 := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ← BRing.one_eq]
  | succ n ih => rw [pow_succ, ih, BRing.tmul_mul_tmul, mul_one, pow_succ]

/-- **The cup `1_s → E_i F_i`** (layer map, followed by the identification of the region to the
right of `F_i` with `s`) is `cupEFW`. -/
theorem trW_cupEF_eq (s : Wt m) (i : Fin m) (v : List (WCol m))
    (hc : WOK N s (⟨up i, sh RD (dn i) + s⟩ :: ⟨dn i, sh RD (up i) + (sh RD (dn i) + s)⟩ :: v))
    (hW : WOK N s (⟨up i, sh RD (dn i) + s⟩ :: ⟨dn i, s⟩ :: v)) (hd : WOK N s v)
    (e : (⟨up i, sh RD (dn i) + s⟩ : WCol m) :: ⟨dn i, sh RD (up i) + (sh RD (dn i) + s)⟩ :: v =
      ⟨up i, sh RD (dn i) + s⟩ :: ⟨dn i, s⟩ :: v) :
    (trW (K := K) s e hc hW).comp (layerMap K N s [] (.cup ⟨up i, sh RD (dn i) + s⟩) v hd hc) =
      cupEFW K i hW.step hW.tail.step (gammaR K N s v hd) := by
  rw [trW_cons', trW_head]
  simp only [layerMap, genMap, cupMap]
  rw [← BHom.comp_assoc, ← BHom.whiskerLeft_comp, trS_trans', trS_self'', BHom.whiskerLeft_id,
    BHom.id_comp']

/-- **The cup `1_s → F_i E_i`** (layer map, followed by the identification of the region to the
right of `E_i` with `s`) is `cupFEW`. -/
theorem trW_cupFE_eq (s : Wt m) (i : Fin m) (v : List (WCol m))
    (hc : WOK N s (⟨dn i, sh RD (up i) + s⟩ :: ⟨up i, sh RD (dn i) + (sh RD (up i) + s)⟩ :: v))
    (hW : WOK N s (⟨dn i, sh RD (up i) + s⟩ :: ⟨up i, s⟩ :: v)) (hd : WOK N s v)
    (e : (⟨dn i, sh RD (up i) + s⟩ : WCol m) :: ⟨up i, sh RD (dn i) + (sh RD (up i) + s)⟩ :: v =
      ⟨dn i, sh RD (up i) + s⟩ :: ⟨up i, s⟩ :: v) :
    (trW (K := K) s e hc hW).comp (layerMap K N s [] (.cup ⟨dn i, sh RD (up i) + s⟩) v hd hc) =
      cupFEW K i hW.tail.step hW.step (gammaR K N s v hd) := by
  rw [trW_cons', trW_head]
  simp only [layerMap, genMap, cupMap]
  rw [← BHom.comp_assoc, ← BHom.whiskerLeft_comp, trS_trans', trS_self'', BHom.whiskerLeft_id,
    BHom.id_comp']

/-! ### The cup `1_λ → E_i F_i`, then dots on `F_i` -/

set_option maxHeartbeats 1000000 in
/-- **`Γ_N` of `cupDotEF`** (the cup `1_λ → E_i F_i` followed by `n` dots on `F_i`), whiskered
by `v`, from the region `λ`: `cupEFW`, then multiplication by `ξ^n` on `F_i`. -/
theorem evalB_cupDotEF (dnScal : Fin m → Fin m → K) (lam : Wt m) (i : Fin m) (n : ℕ)
    (v : List (psig RD).Colour) (ha : WOK N lam ((ob RD lam []).word ++ v))
    (hb : WOK N lam ((ob RD lam [up i, dn i]).word ++ v)) :
    evalB K N dnScal lam v ha hb (LinDiagram.of (cupDotEF RD lam i n)) =
      (BHom.mulB (BRing.tmul (stepB K (true, i) (compOf N (sh RD (dn i) + lam)) (compOf N lam)
          hb.step) ((stepB K (false, i) (compOf N lam) (compOf N (sh RD (dn i) + lam))
            hb.tail.step).tensor (gammaR K N lam v ha)) 1
          (BRing.tmul _ _ (eXi K i (compOf N (sh RD (dn i) + lam)) hb.tail.step.2 ^ n) 1))).comp
        (cupEFW K i hb.step hb.tail.step (gammaR K N lam v ha)) := by
  rw [evalB_of]
  have el : (Diagram.layers (cupDotEF RD lam i n)).map (dataV v) =
      dataV v (lay RD lam [] (.cup (up i)) []) ::
        List.replicate n (dataV v (lay RD lam [up i] (.dot (dn i)) [])) := by
    simp [cupDotEF, layList, List.map_replicate]
  have hW : WOK N lam ([⟨up i, sh RD (dn i) + lam⟩] ++ [⟨dn i, lam⟩] ++ ([] ++ v)) := hb
  have h₂ : ChainW ((ob RD lam []).word ++ v) (dataV v (lay RD lam [] (.cup (up i)) []) ::
        List.replicate n (dataV v (lay RD lam [up i] (.dot (dn i)) [])))
      ((ob RD lam [up i, dn i]).word ++ v) := el ▸ chainW_of_chain v (Diagram.chain _)
  rw [chainBD_congr dnScal lam rfl rfl el _ h₂ ha ha hb hb, trW_rfl, trW_rfl, BHom.id_comp',
    BHom.comp_id'']
  have hL : WOK N lam (⟨up i, sh RD (dn i) + lam⟩ ::
      ⟨dn i, sh RD (up i) + (sh RD (dn i) + lam)⟩ :: v) :=
    ⟨hb.1, hb.2.1, hb.2.2.1, sh_cancel true i _,
      wok_congr_region (sh_cancel false i lam).symm hb.2.2.2.2⟩
  simp only [chainBD]
  split_ifs with h1
  swap
  · exact absurd hL h1
  have e : (dataV v (lay RD lam [] (Shape.cup (up i)) [])).1 ++
      gcod (dataV v (lay RD lam [] (Shape.cup (up i)) [])).2.1 ++
        (dataV v (lay RD lam [] (Shape.cup (up i)) [])).2.2 =
      [⟨up i, sh RD (dn i) + lam⟩] ++ [⟨dn i, lam⟩] ++ ([] ++ v) := by
    show (⟨up i, sh RD (dn i) + lam⟩ : WCol m) :: ⟨dn i, sh RD (up i) + (sh RD (dn i) + lam)⟩ ::
      v = _
    rw [sh_up_dn]
    rfl
  rw [trW_self, show genScal K dnScal (dataV v (lay RD lam [] (Shape.cup (up i)) [])).2.1 = 1
    from rfl, BHom.csmul_one, BHom.comp_id'']
  rw [chainBD_trW dnScal lam e rfl _ (e ▸ h₂.2) h1 hW hb hb, trW_self, BHom.id_comp']
  erw [chainBD_dots dnScal lam [⟨up i, sh RD (dn i) + lam⟩] ([] ++ v) ⟨dn i, lam⟩ hW _
    (layerMap_dot_second lam _ _ _ hW) n _ hW]
  rw [BHom.comp_assoc]
  erw [trW_cupEF_eq lam i v hL hW ha e]
  rw [tmul_one_tmul_pow]
  rfl

/-- **The cap `E_i F_i → 1_s`** (layer map) is `capEFW`. -/
theorem layerMap_capEF (s : Wt m) (i : Fin m) (R : List (WCol m))
    (hd : WOK N s (⟨up i, sh RD (dn i) + s⟩ :: ⟨dn i, s⟩ :: R)) (hc : WOK N s R) :
    layerMap K N s [] (.cap ⟨dn i, s⟩) R hd hc =
      capEFW K i (hd.step : StepR (true, i) (compOf N (sh RD (dn i) + s)) (compOf N s))
        (hd.tail.step : StepR (false, i) (compOf N s) (compOf N (sh RD (dn i) + s)))
        (gammaR K N s R hc) := by
  simp only [layerMap, genMap, capMap, trS_self'']
  erw [BHom.whiskerLeft_id]
  rfl

/-- **The cap `F_i E_i → 1_s`** (layer map) is `capFEW`. -/
theorem layerMap_capFE (s : Wt m) (i : Fin m) (R : List (WCol m))
    (hd : WOK N s (⟨dn i, sh RD (up i) + s⟩ :: ⟨up i, s⟩ :: R)) (hc : WOK N s R) :
    layerMap K N s [] (.cap ⟨up i, s⟩) R hd hc =
      capFEW K i (hd.tail.step : StepR (true, i) (compOf N s) (compOf N (sh RD (up i) + s)))
        (hd.step : StepR (false, i) (compOf N (sh RD (up i) + s)) (compOf N s))
        (gammaR K N s R hc) := by
  simp only [layerMap, genMap, capMap, trS_self'']
  erw [BHom.whiskerLeft_id]
  rfl

theorem capMap_true_self (i : Fin m) (r : Wt m) (right : List (WCol m))
    (hd : WOK N r (⟨(!true, i), sh RD (true, i) + r⟩ :: ⟨(true, i), r⟩ :: right))
    (hc : WOK N r right) :
    capMap K N true i r r right hd hc =
      capFEW K i (hd.tail.step : StepR (true, i) (compOf N r) (compOf N (sh RD (true, i) + r)))
        (hd.step : StepR (false, i) (compOf N (sh RD (true, i) + r)) (compOf N r))
        (gammaR K N r right hc) := by
  simp only [capMap, trS_self'']
  erw [BHom.whiskerLeft_id]
  rfl

theorem capMap_false_self (i : Fin m) (r : Wt m) (right : List (WCol m))
    (hd : WOK N r (⟨(!false, i), sh RD (false, i) + r⟩ :: ⟨(false, i), r⟩ :: right))
    (hc : WOK N r right) :
    capMap K N false i r r right hd hc =
      capEFW K i (hd.step : StepR (true, i) (compOf N (sh RD (false, i) + r)) (compOf N r))
        (hd.tail.step : StepR (false, i) (compOf N r) (compOf N (sh RD (false, i) + r)))
        (gammaR K N r right hc) := by
  simp only [capMap, trS_self'']
  erw [BHom.whiskerLeft_id]
  rfl

/-! ### Dots on `E_i`, then the cap `E_i F_i → 1_λ` -/

set_option maxHeartbeats 1000000 in
/-- **`Γ_N` of `dotCapEF`** (`n` dots on `E_i`, then the cap `E_i F_i → 1_λ`), whiskered by `v`,
from the region `λ`: multiplication by `ξ^n` on `E_i`, then `capEFW`. -/
theorem evalB_dotCapEF (dnScal : Fin m → Fin m → K) (lam : Wt m) (i : Fin m) (n : ℕ)
    (v : List (psig RD).Colour) (ha : WOK N lam ((ob RD lam [up i, dn i]).word ++ v))
    (hb : WOK N lam ((ob RD lam []).word ++ v)) :
    evalB K N dnScal lam v ha hb (LinDiagram.of (dotCapEF RD lam i n)) =
      (capEFW K i ha.step ha.tail.step (gammaR K N lam v hb)).comp
        (BHom.mulB (BRing.tmul (stepB K (true, i) (compOf N (sh RD (dn i) + lam)) (compOf N lam)
          ha.step) ((stepB K (false, i) (compOf N lam) (compOf N (sh RD (dn i) + lam))
            ha.tail.step).tensor (gammaR K N lam v hb))
          (eXi K i (compOf N (sh RD (dn i) + lam)) ha.tail.step.2 ^ n) 1)) := by
  rw [evalB_of]
  have el : (Diagram.layers (dotCapEF RD lam i n)).map (dataV v) =
      List.replicate n (dataV v (lay RD lam [] (.dot (up i)) [dn i])) ++
        [dataV v (lay RD lam [] (.cap (dn i)) [])] := by
    simp [dotCapEF, layList, List.map_replicate]
  have hW : WOK N lam ([] ++ [⟨up i, sh RD (dn i) + lam⟩] ++ ([⟨dn i, lam⟩] ++ v)) := ha
  have h₂ : ChainW ((ob RD lam [up i, dn i]).word ++ v)
      (List.replicate n (dataV v (lay RD lam [] (.dot (up i)) [dn i])) ++
        [dataV v (lay RD lam [] (.cap (dn i)) [])]) ((ob RD lam []).word ++ v) :=
    el ▸ chainW_of_chain v (Diagram.chain _)
  rw [chainBD_congr dnScal lam rfl rfl el _ h₂ ha ha hb hb]
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']
  have key := chainBD_dots_append dnScal lam [] _ _ hW _ (layerMap_dot_first lam _ _ hW) n
    [dataV v (lay RD lam [] (.cap (dn i)) [])] _ h₂ (by exact ⟨rfl, rfl⟩) hb
  erw [key]
  simp only [chainBD]
  split_ifs with h1
  swap
  · exact absurd hb h1
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']
  rw [show genScal K dnScal (dataV v (lay RD lam [] (Shape.cap (dn i)) [])).2.1 = 1 from rfl,
    BHom.csmul_one]
  erw [layerMap_capEF, tmul_pow_one]
  rfl

/-! ### The cup `1_λ → F_i E_i`, then dots on `E_i` -/

set_option maxHeartbeats 1000000 in
/-- **`Γ_N` of `cupDotFE`** (the cup `1_λ → F_i E_i` followed by `n` dots on `E_i`), whiskered
by `v`, from the region `λ`: `cupFEW`, then multiplication by `ξ^n` on `E_i`. -/
theorem evalB_cupDotFE (dnScal : Fin m → Fin m → K) (lam : Wt m) (i : Fin m) (n : ℕ)
    (v : List (psig RD).Colour) (ha : WOK N lam ((ob RD lam []).word ++ v))
    (hb : WOK N lam ((ob RD lam [dn i, up i]).word ++ v)) :
    evalB K N dnScal lam v ha hb (LinDiagram.of (cupDotFE RD lam i n)) =
      (BHom.mulB (BRing.tmul (stepB K (false, i) (compOf N (sh RD (up i) + lam)) (compOf N lam)
          hb.step) ((stepB K (true, i) (compOf N lam) (compOf N (sh RD (up i) + lam))
            hb.tail.step).tensor (gammaR K N lam v ha)) 1
          (BRing.tmul _ _ (eXi K i (compOf N lam) hb.tail.step.2 ^ n) 1))).comp
        (cupFEW K i hb.tail.step hb.step (gammaR K N lam v ha)) := by
  rw [evalB_of]
  have el : (Diagram.layers (cupDotFE RD lam i n)).map (dataV v) =
      dataV v (lay RD lam [] (.cup (dn i)) []) ::
        List.replicate n (dataV v (lay RD lam [dn i] (.dot (up i)) [])) := by
    simp [cupDotFE, layList, List.map_replicate]
  have hW : WOK N lam ([⟨dn i, sh RD (up i) + lam⟩] ++ [⟨up i, lam⟩] ++ ([] ++ v)) := hb
  have h₂ : ChainW ((ob RD lam []).word ++ v) (dataV v (lay RD lam [] (.cup (dn i)) []) ::
        List.replicate n (dataV v (lay RD lam [dn i] (.dot (up i)) [])))
      ((ob RD lam [dn i, up i]).word ++ v) := el ▸ chainW_of_chain v (Diagram.chain _)
  rw [chainBD_congr dnScal lam rfl rfl el _ h₂ ha ha hb hb, trW_rfl, trW_rfl, BHom.id_comp',
    BHom.comp_id'']
  have hL : WOK N lam (⟨dn i, sh RD (up i) + lam⟩ ::
      ⟨up i, sh RD (dn i) + (sh RD (up i) + lam)⟩ :: v) :=
    ⟨hb.1, hb.2.1, hb.2.2.1, sh_cancel false i _,
      wok_congr_region (sh_cancel true i lam).symm hb.2.2.2.2⟩
  simp only [chainBD]
  split_ifs with h1
  swap
  · exact absurd hL h1
  have e : (dataV v (lay RD lam [] (Shape.cup (dn i)) [])).1 ++
      gcod (dataV v (lay RD lam [] (Shape.cup (dn i)) [])).2.1 ++
        (dataV v (lay RD lam [] (Shape.cup (dn i)) [])).2.2 =
      [⟨dn i, sh RD (up i) + lam⟩] ++ [⟨up i, lam⟩] ++ ([] ++ v) := by
    show (⟨dn i, sh RD (up i) + lam⟩ : WCol m) :: ⟨up i, sh RD (dn i) + (sh RD (up i) + lam)⟩ ::
      v = _
    rw [sh_dn_up]
    rfl
  rw [trW_self, show genScal K dnScal (dataV v (lay RD lam [] (Shape.cup (dn i)) [])).2.1 = 1
    from rfl, BHom.csmul_one, BHom.comp_id'']
  rw [chainBD_trW dnScal lam e rfl _ (e ▸ h₂.2) h1 hW hb hb, trW_self, BHom.id_comp']
  have key := chainBD_dots dnScal lam _ _ _ hW _ (layerMap_dot_second lam _ _ _ hW) n
    (e ▸ h₂.2) hW
  erw [key]
  rw [BHom.comp_assoc]
  erw [trW_cupFE_eq lam i v hL hW ha e]
  rw [tmul_one_tmul_pow]
  rfl

/-! ### Dots on `F_i`, then the cap `F_i E_i → 1_λ` -/

set_option maxHeartbeats 1000000 in
/-- **`Γ_N` of `dotCapFE`** (`n` dots on `F_i`, then the cap `F_i E_i → 1_λ`), whiskered by `v`,
from the region `λ`: multiplication by `ξ^n` on `F_i`, then `capFEW`. -/
theorem evalB_dotCapFE (dnScal : Fin m → Fin m → K) (lam : Wt m) (i : Fin m) (n : ℕ)
    (v : List (psig RD).Colour) (ha : WOK N lam ((ob RD lam [dn i, up i]).word ++ v))
    (hb : WOK N lam ((ob RD lam []).word ++ v)) :
    evalB K N dnScal lam v ha hb (LinDiagram.of (dotCapFE RD lam i n)) =
      (capFEW K i ha.tail.step ha.step (gammaR K N lam v hb)).comp
        (BHom.mulB (BRing.tmul (stepB K (false, i) (compOf N (sh RD (up i) + lam)) (compOf N lam)
          ha.step) ((stepB K (true, i) (compOf N lam) (compOf N (sh RD (up i) + lam))
            ha.tail.step).tensor (gammaR K N lam v hb))
          (eXi K i (compOf N lam) ha.tail.step.2 ^ n) 1)) := by
  rw [evalB_of]
  have el : (Diagram.layers (dotCapFE RD lam i n)).map (dataV v) =
      List.replicate n (dataV v (lay RD lam [] (.dot (dn i)) [up i])) ++
        [dataV v (lay RD lam [] (.cap (up i)) [])] := by
    simp [dotCapFE, layList, List.map_replicate]
  have hW : WOK N lam ([] ++ [⟨dn i, sh RD (up i) + lam⟩] ++ ([⟨up i, lam⟩] ++ v)) := ha
  have h₂ : ChainW ((ob RD lam [dn i, up i]).word ++ v)
      (List.replicate n (dataV v (lay RD lam [] (.dot (dn i)) [up i])) ++
        [dataV v (lay RD lam [] (.cap (up i)) [])]) ((ob RD lam []).word ++ v) :=
    el ▸ chainW_of_chain v (Diagram.chain _)
  rw [chainBD_congr dnScal lam rfl rfl el _ h₂ ha ha hb hb]
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']
  have key := chainBD_dots_append dnScal lam [] _ _ hW _ (layerMap_dot_first lam _ _ hW) n
    [dataV v (lay RD lam [] (.cap (up i)) [])] _ h₂ (by exact ⟨rfl, rfl⟩) hb
  erw [key]
  simp only [chainBD]
  split_ifs with h1
  swap
  · exact absurd hb h1
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']
  rw [show genScal K dnScal (dataV v (lay RD lam [] (Shape.cap (up i)) [])).2.1 = 1 from rfl,
    BHom.csmul_one]
  erw [layerMap_capFE, tmul_pow_one]
  rfl

/-! ### Dots on a single strand -/

/-- **`Γ_N` of `n` dots on a single strand** `l` (`dots μ [] l [] n`), whiskered by `v`, from any
region `s`: multiplication by `ξ^n` on the strand. -/
theorem evalB_dots_first_bub (dnScal : Fin m → Fin m → K) (μ : Wt m) (l : SLetter m) (n : ℕ)
    (s : Wt m) (v : List (psig RD).Colour)
    (ha hb : WOK N s ((ob RD μ ([] ++ [l] ++ [])).word ++ v)) :
    evalB K N dnScal s v ha hb (LinDiagram.of (dots RD μ [] l [] n)) =
      BHom.mulB (BRing.tmul (stepB K l (compOf N μ) (compOf N s) ha.step) (gammaR K N μ v ha.tail)
        (xiStep K l (compOf N μ) (compOf N s) ha.step ^ n) 1) := by
  rw [evalB_of]
  have el : (Diagram.layers (dots RD μ [] l [] n)).map (dataV v) =
      List.replicate n (dataV v (lay RD μ [] (.dot l) [])) := by
    simp [dots, layList, List.map_replicate]
  have hW : WOK N s ([] ++ [⟨l, μ⟩] ++ ([] ++ v)) := ha
  have h₂ : ChainW ((ob RD μ ([] ++ [l] ++ [])).word ++ v)
      (List.replicate n (dataV v (lay RD μ [] (.dot l) [])))
      ((ob RD μ ([] ++ [l] ++ [])).word ++ v) :=
    el ▸ chainW_of_chain v (Diagram.chain _)
  rw [chainBD_congr dnScal s rfl rfl el _ h₂ ha ha hb hb]
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']
  have key := chainBD_dots dnScal s _ _ _ hW _ (layerMap_dot_first s _ _ hW) n h₂ hW
  erw [key, tmul_pow_one]
  rfl

/-! ### Bubbles on the path model -/

section PathBubbles

attribute [local instance] rightAlgebra midAlgebra

variable (i : Fin m) {s s' : Comp m} (hE : StepR (true, i) s s') (hF : StepR (false, i) s' s)

theorem capEFP_sum (S : Finset ℕ) (g : ℕ → ((Est (K := K) i hE).tensor (Fst (K := K) i hF)).T) :
    ∑ f ∈ S, capEFP K i hE hF (g f) = capEFP K i hE hF (∑ f ∈ S, g f) := by
  induction S using Finset.induction_on with
  | empty => simp [capEFP]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, capEFP_add]

theorem capFEP_sum (S : Finset ℕ) (g : ℕ → ((Fst (K := K) i hF).tensor (Est (K := K) i hE)).T) :
    ∑ f ∈ S, capFEP K i hE hF (g f) = capFEP K i hE hF (∑ f ∈ S, g f) := by
  induction S using Finset.induction_on with
  | empty => simp [capFEP]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, capFEP_add]

/-- **The clockwise bubble with `α` dots, whiskered by `Y`** (cup `1 → E_i F_i`, `α` dots on
`F_i`, cap `E_i F_i → 1`) is multiplication by `cwRealH s' i α`. -/
theorem bubbleEF_path {C : Type u} [CommRing C] (Y : BRing (H K s') C) (α : ℕ) (y : Y.T) :
    capEFW K i hE hF Y (BRing.tmul (Est (K := K) i hE) ((Fst (K := K) i hF).tensor Y) 1
        (BRing.tmul _ Y (eXi K i s hE.2 ^ α) 1) * cupEFW K i hE hF Y y) =
      Y.left (cwRealH s' i α) * y := by
  rw [cupEFW_apply, Finset.mul_sum, BHom.map_sum]
  have h1 : ∀ g, BRing.tmul (Est (K := K) i hE) ((Fst (K := K) i hF).tensor Y) 1
      (BRing.tmul _ Y (eXi K i s hE.2 ^ α) 1) *
      BRing.tmul _ _ ((-1) ^ (dEF i hE - g) * eXi K i s hE.2 ^ g : ERing K i s hE.2)
        (BRing.tmul _ Y (xsEF i hE (dEF i hE - g)) y) =
      BRing.tmul _ _ ((-1) ^ (dEF i hE - g) * eXi K i s hE.2 ^ g : ERing K i s hE.2)
        (BRing.tmul _ Y (eXi K i s hE.2 ^ α * xsEF i hE (dEF i hE - g)) y) := by
    intro g
    rw [BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, one_mul]
  simp only [h1, capEFW_tmul, ← Finset.sum_mul, ← map_sum]
  rw [capEFP_sum, ← capEFP_bubble_eq i hE hF α, cupEF, Finset.mul_sum]
  congr 3
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [BRing.tmul_mul_tmul, one_mul]

/-- **The counterclockwise bubble with `α` dots, whiskered by `X`** (cup `1 → F_i E_i`, `α` dots
on `E_i`, cap `F_i E_i → 1`) is multiplication by `ccwRealH s i α`. -/
theorem bubbleFE_path {C : Type u} [CommRing C] (X : BRing (H K s) C) (α : ℕ) (x : X.T) :
    capFEW K i hE hF X (BRing.tmul (Fst (K := K) i hF) ((Est (K := K) i hE).tensor X) 1
        (BRing.tmul _ X (eXi K i s hE.2 ^ α) 1) * cupFEW K i hE hF X x) =
      X.left (ccwRealH s i α) * x := by
  rw [cupFEW_apply, Finset.mul_sum, BHom.map_sum]
  have h1 : ∀ f, BRing.tmul (Fst (K := K) i hF) ((Est (K := K) i hE).tensor X) 1
      (BRing.tmul _ X (eXi K i s hE.2 ^ α) 1) *
      BRing.tmul _ _ ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f : ERing K i s hE.2)
        (BRing.tmul _ X (xsFE i hE (dFE i hE - f)) x) =
      BRing.tmul _ _ ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f : ERing K i s hE.2)
        (BRing.tmul _ X (eXi K i s hE.2 ^ α * xsFE i hE (dFE i hE - f)) x) := by
    intro f
    rw [BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, one_mul]
  simp only [h1, capFEW_tmul, ← Finset.sum_mul, ← map_sum]
  rw [capFEP_sum, ← capFEP_bubble_eq i hE hF α, cupFE, Finset.mul_sum]
  congr 3
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [BRing.tmul_mul_tmul, one_mul]

end PathBubbles

/-! ### Regions next to a realized region -/

theorem ip_eq_nH {lam : Wt m} (h : Realized N lam) (i : Fin m) :
    ip RD i lam = nH (compOf N lam) i := by
  have hw := (compOf_spec h).2
  show slPair m (Pi.single i 1) lam = _
  rw [slPair_single_left]
  conv_lhs => rw [← hw]
  rfl

theorem sum_raise_eq (i : Fin m) (d : Comp m) (h : 0 < d i.succ) :
    ∑ j, raise i d j = ∑ j, d j := by
  have key : raise i d + (Pi.single i.succ 1 : Comp m) = d + Pi.single i.castSucc 1 := by
    funext j
    simp only [Pi.add_apply, Pi.single_apply, raise]
    have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
    by_cases h1 : j = i.castSucc
    · subst h1; simp [hne]
    · by_cases h2 : j = i.succ
      · subst h2; simp [hne.symm]; omega
      · simp [h1, h2]
  have := congrArg (fun d : Comp m => ∑ j, d j) key
  rw [sum_add_single, sum_add_single] at this
  omega

theorem sh_up_eq (i : Fin m) : sh RD (up i) = (slRootDatum m).iX i := by
  simp [sh, QuantumGroup.UDot.sgn_true]

theorem sh_dn_eq (i : Fin m) : sh RD (dn i) = -(slRootDatum m).iX i := by
  simp [sh]

/-- The region `λ + i_X` is realized if block `i + 1` of `λ` is nonempty. -/
theorem realized_up_of_pos {lam : Wt m} (h : Realized N lam) (i : Fin m)
    (hp : 0 < compOf N lam i.succ) : Realized N (sh RD (up i) + lam) := by
  obtain ⟨h1, h2⟩ := compOf_spec h
  refine ⟨raise i (compOf N lam), (sum_raise_eq i _ hp).trans h1, ?_⟩
  rw [compWeight_raise i _ hp, h2, sh_up_eq, add_comm]

/-- The region `λ - i_X` is realized if block `i` of `λ` is nonempty. -/
theorem realized_dn_of_pos {lam : Wt m} (h : Realized N lam) (i : Fin m)
    (hp : 0 < compOf N lam i.castSucc) : Realized N (sh RD (dn i) + lam) := by
  obtain ⟨h1, h2⟩ := compOf_spec h
  set k := compOf N lam
  let d : Comp m := fun j => if j = i.castSucc then k j - 1 else if j = i.succ then k j + 1 else k j
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  have hd : 0 < d i.succ := by simp [d, hne.symm]
  have hr : raise i d = k := by
    funext j
    simp only [raise, d]
    by_cases h1 : j = i.castSucc
    · subst h1; simp; omega
    · by_cases h2 : j = i.succ
      · subst h2; simp [hne.symm]
      · simp [h1, h2]
  refine ⟨d, ?_, ?_⟩
  · rw [← sum_raise_eq i d hd, hr, h1]
  · have := compWeight_raise i d hd
    rw [hr, h2] at this
    rw [sh_dn_eq, this]
    abel

theorem compOf_castSucc_eq_zero {lam : Wt m} (h : Realized N lam) (i : Fin m)
    (hn : ¬ Realized N (sh RD (dn i) + lam)) : compOf N lam i.castSucc = 0 := by
  by_contra h0
  exact hn (realized_dn_of_pos h i (Nat.pos_of_ne_zero h0))

theorem compOf_succ_eq_zero {lam : Wt m} (h : Realized N lam) (i : Fin m)
    (hn : ¬ Realized N (sh RD (up i) + lam)) : compOf N lam i.succ = 0 := by
  by_contra h0
  exact hn (realized_up_of_pos h i (Nat.pos_of_ne_zero h0))

/-- In a region with empty block `i`, the real clockwise bubbles vanish. -/
theorem cwRealH_of_castSucc_zero (k : Comp m) (i : Fin m) (h0 : k i.castSucc = 0) (α : ℕ) :
    cwRealH (K := K) k i α = 0 := by
  rw [cwRealH]
  split_ifs with h1
  · rw [PsiH_of_castSucc_zero _ _ h0, x_eq_zero (by omega), mul_zero]
  · rfl

/-- In a region with empty block `i + 1`, the real counterclockwise bubbles vanish. -/
theorem ccwRealH_of_succ_zero (k : Comp m) (i : Fin m) (h0 : k i.succ = 0) (α : ℕ) :
    ccwRealH (K := K) k i α = 0 := by
  rw [ccwRealH]
  split_ifs with h1
  · rw [PhiH_of_succ_zero _ _ h0, x_eq_zero (by omega), mul_zero]
  · rfl

/-! ### Chains of three layers -/

open Classical in
/-- **The chain map of three layers**, with the identifications `trW` between consecutive
boundaries written out (all intermediate boundaries valid). -/
theorem chainBD_three (dnScal : Fin m → Fin m → K) (s : Wt m) (w w' : List (WCol m))
    (d₁ d₂ d₃ : LData m) (h : ChainW w [d₁, d₂, d₃] w') (ha : WOK N s w) (hb : WOK N s w')
    (hd₁ : WOK N s (d₁.1 ++ gdom d₁.2.1 ++ d₁.2.2)) (hc₁ : WOK N s (d₁.1 ++ gcod d₁.2.1 ++ d₁.2.2))
    (hd₂ : WOK N s (d₂.1 ++ gdom d₂.2.1 ++ d₂.2.2)) (hc₂ : WOK N s (d₂.1 ++ gcod d₂.2.1 ++ d₂.2.2))
    (hd₃ : WOK N s (d₃.1 ++ gdom d₃.2.1 ++ d₃.2.2))
    (hc₃ : WOK N s (d₃.1 ++ gcod d₃.2.1 ++ d₃.2.2)) :
    chainBD K N dnScal s w [d₁, d₂, d₃] w' h ha hb =
      (trW s h.2.2.2 hc₃ hb).comp ((BHom.csmul (genScal K dnScal d₃.2.1)
        (layerMap K N s d₃.1 d₃.2.1 d₃.2.2 hd₃ hc₃)).comp ((trW s h.2.2.1 hc₂ hd₃).comp
        ((BHom.csmul (genScal K dnScal d₂.2.1) (layerMap K N s d₂.1 d₂.2.1 d₂.2.2 hd₂ hc₂)).comp
        ((trW s h.2.1 hc₁ hd₂).comp ((BHom.csmul (genScal K dnScal d₁.2.1)
          (layerMap K N s d₁.1 d₁.2.1 d₁.2.2 hd₁ hc₁)).comp (trW s h.1 ha hd₁)))))) := by
  simp only [chainBD, dite_eq_left hc₁, dite_eq_left hc₂, dite_eq_left hc₃]
  rfl

/-! ### Real bubbles -/

/-- A chain whose first layer ends on an invalid object is zero. -/
theorem chainBD_eq_zero_of_first (dnScal : Fin m → Fin m → K) (s : Wt m) (w : List (WCol m))
    (ls : List (LData m)) (w' : List (WCol m)) (h : ChainW w ls w') (ha : WOK N s w)
    (hb : WOK N s w') (d : LData m) (ds : List (LData m)) (el : ls = d :: ds)
    (hn : ¬ WOK N s (d.1 ++ gcod d.2.1 ++ d.2.2)) :
    chainBD K N dnScal s w ls w' h ha hb = 0 := by
  subst el
  simp only [chainBD]
  rw [dite_eq_right hn]

theorem of_cwReal_eq (lam : Wt m) (i : Fin m) (α : ℕ) :
    (LinDiagram.of (cwReal RD lam i α) : LinDiagram K _ _) =
      LinDiagram.of (cupDotEF RD lam i α) ≫ LinDiagram.of (dotCapEF RD lam i 0) := by
  rw [← LinDiagram.of_comp]
  congr 1
  apply Diagram.ext
  simp [cwReal, cupDotEF, dotCapEF, layList]

theorem of_ccwReal_eq (lam : Wt m) (i : Fin m) (α : ℕ) :
    (LinDiagram.of (ccwReal RD lam i α) : LinDiagram K _ _) =
      LinDiagram.of (cupDotFE RD lam i α) ≫ LinDiagram.of (dotCapFE RD lam i 0) := by
  rw [← LinDiagram.of_comp]
  congr 1
  apply Diagram.ext
  simp [ccwReal, cupDotFE, dotCapFE, layList]

/-- **`Γ_N` of the real clockwise bubble** with `α` dots in the region `λ` (whiskered by `v`) is
multiplication by `cwRealH λ i α` (KL III Proposition 6.3; `capEFP_bubble_eq`). -/
theorem evalB_cwReal (dnScal : Fin m → Fin m → K) (lam : Wt m) (i : Fin m) (α : ℕ)
    (v : List (psig RD).Colour) (ha hb : WOK N lam ((ob RD lam []).word ++ v)) :
    evalB K N dnScal lam v ha hb (LinDiagram.of (cwReal RD lam i α)) =
      BHom.mulB ((gammaR K N lam v ha).left (cwRealH (compOf N lam) i α)) := by
  by_cases hm : WOK N lam ((ob RD lam [up i, dn i]).word ++ v)
  · rw [of_cwReal_eq, evalB_comp dnScal lam v ha hm hb, evalB_cupDotEF, evalB_dotCapEF]
    refine BHom.ext fun y => ?_
    simp only [BHom.comp_apply, BHom.mulB_apply, pow_zero, ← BRing.one_eq, one_mul]
    exact bubbleEF_path i hm.step hm.tail.step (gammaR K N lam v ha) α y
  · have h0 : compOf N lam i.castSucc = 0 :=
      compOf_castSucc_eq_zero ha.realized i fun hr => hm ⟨ha.realized, sh_up_dn i lam, hr, rfl, ha⟩
    rw [cwRealH_of_castSucc_zero _ i h0, map_zero, BHom.mulB_zero', evalB_of]
    refine chainBD_eq_zero_of_first dnScal lam _ _ _ _ ha hb
      (dataV v (lay RD lam [] (.cup (up i)) []))
      (List.replicate α (dataV v (lay RD lam [up i] (Shape.dot (dn i)) [])) ++
        [dataV v (lay RD lam [] (Shape.cap (dn i)) [])]) (by simp [cwReal, layList]) ?_
    intro h1
    exact hm ⟨h1.1, h1.2.1, h1.2.2.1, rfl, wok_congr_region (sh_up_dn i lam) h1.2.2.2.2⟩

/-- **`Γ_N` of the real counterclockwise bubble** with `α` dots in the region `λ` (whiskered by
`v`) is multiplication by `ccwRealH λ i α` (KL III Proposition 6.3; `capFEP_bubble_eq`). -/
theorem evalB_ccwReal (dnScal : Fin m → Fin m → K) (lam : Wt m) (i : Fin m) (α : ℕ)
    (v : List (psig RD).Colour) (ha hb : WOK N lam ((ob RD lam []).word ++ v)) :
    evalB K N dnScal lam v ha hb (LinDiagram.of (ccwReal RD lam i α)) =
      BHom.mulB ((gammaR K N lam v ha).left (ccwRealH (compOf N lam) i α)) := by
  by_cases hm : WOK N lam ((ob RD lam [dn i, up i]).word ++ v)
  · rw [of_ccwReal_eq, evalB_comp dnScal lam v ha hm hb, evalB_cupDotFE, evalB_dotCapFE]
    refine BHom.ext fun y => ?_
    simp only [BHom.comp_apply, BHom.mulB_apply, pow_zero, ← BRing.one_eq, one_mul]
    exact bubbleFE_path i hm.tail.step hm.step (gammaR K N lam v ha) α y
  · have h0 : compOf N lam i.succ = 0 :=
      compOf_succ_eq_zero ha.realized i fun hr => hm ⟨ha.realized, sh_dn_up i lam, hr, rfl, ha⟩
    rw [ccwRealH_of_succ_zero _ i h0, map_zero, BHom.mulB_zero', evalB_of]
    refine chainBD_eq_zero_of_first dnScal lam _ _ _ _ ha hb
      (dataV v (lay RD lam [] (.cup (dn i)) []))
      (List.replicate α (dataV v (lay RD lam [dn i] (Shape.dot (up i)) [])) ++
        [dataV v (lay RD lam [] (Shape.cap (up i)) [])]) (by simp [ccwReal, layList]) ?_
    intro h1
    exact hm ⟨h1.1, h1.2.1, h1.2.2.1, rfl, wok_congr_region (sh_dn_up i lam) h1.2.2.2.2⟩

/-! ### Products of bubbles and fake bubbles -/

/-- `BHom.mulB` as an additive map. -/
def mulBAdd {A : Type u} [CommRing A] (M : BRing A K) : M.T →+ BHom M M :=
  AddMonoidHom.mk' BHom.mulB BHom.mulB_add

theorem mulB_sum' {A : Type u} [CommRing A] {M : BRing A K} {ι : Type*} (S : Finset ι)
    (f : ι → M.T) : BHom.mulB (∑ j ∈ S, f j) = ∑ j ∈ S, BHom.mulB (f j) :=
  map_sum (mulBAdd M) f S

theorem mulB_neg' {A : Type u} [CommRing A] {M : BRing A K} (x : M.T) :
    BHom.mulB (-x) = -BHom.mulB x :=
  map_neg (mulBAdd M) x

/-- `evalB` of the identity. -/
theorem evalB_id_bub (dnScal : Fin m → Fin m → K) (a : Obj (psig RD)) (s : Wt m)
    (v : List (psig RD).Colour) (ha hb : WOK N s (a.word ++ v)) :
    evalB K N dnScal s v ha hb (𝟙 (Free.of K a)) = BHom.id _ := by
  show evalB K N dnScal s v ha hb (LinDiagram.of (𝟙 a)) = _
  rw [evalB_of]
  rfl

/-- `evalB` of a product in the endomorphism ring (`f * g = g ≫ f`). -/
theorem evalB_mul_bub (dnScal : Fin m → Fin m → K) (a : Obj (psig RD)) (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s (a.word ++ v)) (f g : LEnd RD K a) :
    evalB K N dnScal s v ha ha (show LinDiagram K a a from f * g) =
      (evalB K N dnScal s v ha ha f).comp (evalB K N dnScal s v ha ha g) :=
  evalB_comp dnScal s v ha ha ha g f

/-- **`Γ_N` of the Grassmannian recursion**: if the coefficients `c a` act by multiplication by
`c' a` in the region `λ`, then so does `grassInv c k` by `grassInv c' k`. -/
theorem evalB_grassInv (dnScal : Fin m → Fin m → K) (lam : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N lam ((ob RD lam []).word ++ v)) (c : ℕ → LEnd RD K (ob RD lam []))
    (c' : ℕ → H K (compOf N lam))
    (hc : ∀ a, evalB K N dnScal lam v ha ha (c a) = BHom.mulB ((gammaR K N lam v ha).left (c' a))) :
    ∀ k, evalB K N dnScal lam v ha ha (grassInv (A := LEnd RD K (ob RD lam [])) c k) =
      BHom.mulB ((gammaR K N lam v ha).left (grassInv c' k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rw [grassInv_zero, grassInv_zero, map_one (gammaR K N lam v ha).left, BHom.mulB_one]
      exact evalB_id_bub dnScal _ lam v ha ha
    · rw [grassInv_succ, grassInv_succ, map_neg, map_sum, map_neg, map_sum, mulB_neg', mulB_sum']
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [evalB_mul_bub, hc, ih _ (by omega), BHom.mulB_comp_mulB, map_mul]

/-- **`Γ_N` of the labelled clockwise bubble `cwL`** (real or fake, KL III Definition 3.1,
eq. `eq_infinite_Grass`) in the region `λ` is multiplication by `cwLH λ i m`
(`= Ψ_{m+1-n}`, `cwLH_eq`). -/
theorem evalB_cwL (dnScal : Fin m → Fin m → K) (lam : Wt m) (i : Fin m) (mm : ℤ)
    (v : List (psig RD).Colour) (ha hb : WOK N lam ((ob RD lam []).word ++ v)) :
    evalB K N dnScal lam v ha hb (cwL RD K lam i mm) =
      BHom.mulB ((gammaR K N lam v ha).left (cwLH (compOf N lam) i mm)) := by
  have hn := ip_eq_nH ha.realized i
  unfold cwL cwLH
  rw [hn]
  split_ifs with h1 h2
  · exact evalB_cwReal dnScal lam i _ v ha hb
  · refine evalB_grassInv dnScal lam v ha _ _ (fun a => ?_) _
    unfold ccwR ccwRH
    split_ifs with h3
    · exact evalB_ccwReal dnScal lam i _ v ha ha
    · rw [map_zero, map_zero, BHom.mulB_zero']
  · rw [map_zero, map_zero, BHom.mulB_zero']

/-- **`Γ_N` of the labelled counterclockwise bubble `ccwL`** (real or fake) in the region `λ` is
multiplication by `ccwLH λ i m` (`= Φ_{m+1+n}`, `ccwLH_eq`). -/
theorem evalB_ccwL (dnScal : Fin m → Fin m → K) (lam : Wt m) (i : Fin m) (mm : ℤ)
    (v : List (psig RD).Colour) (ha hb : WOK N lam ((ob RD lam []).word ++ v)) :
    evalB K N dnScal lam v ha hb (ccwL RD K lam i mm) =
      BHom.mulB ((gammaR K N lam v ha).left (ccwLH (compOf N lam) i mm)) := by
  have hn := ip_eq_nH ha.realized i
  unfold ccwL ccwLH
  rw [hn]
  split_ifs with h1 h2
  · exact evalB_ccwReal dnScal lam i _ v ha hb
  · refine evalB_grassInv dnScal lam v ha _ _ (fun a => ?_) _
    unfold cwR cwRH
    split_ifs with h3
    · exact evalB_cwReal dnScal lam i _ v ha ha
    · rw [map_zero, map_zero, BHom.mulB_zero']
  · rw [map_zero, map_zero, BHom.mulB_zero']

/-! ### Bubbles next to an upward strand -/

theorem bubR_add' (lam : Wt m) (t : List (SLetter m)) (f g : LEnd RD K (ob RD lam [])) :
    bubR RD K lam t (f + g) = bubR RD K lam t f + bubR RD K lam t g := by
  simp only [bubR]
  rw [show (f + g : LinDiagram K _ _) = (f : LinDiagram K _ _) + g from rfl,
    LinDiagram.whisker_add, LinDiagram.cast_add]

theorem bubL_add' (μ : Wt m) (t : List (SLetter m)) (f g : LEnd RD K (ob RD (wt RD μ t) [])) :
    bubL RD K μ t (f + g) = bubL RD K μ t f + bubL RD K μ t g := by
  simp only [bubL]
  rw [show (f + g : LinDiagram K _ _) = (f : LinDiagram K _ _) + g from rfl,
    LinDiagram.whisker_add, LinDiagram.cast_add]

theorem bubR_zero' (lam : Wt m) (t : List (SLetter m)) :
    bubR RD K lam t (0 : LEnd RD K (ob RD lam [])) = 0 := by
  have h := bubR_add' (K := K) lam t 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem bubL_zero' (μ : Wt m) (t : List (SLetter m)) :
    bubL RD K μ t (0 : LEnd RD K (ob RD (wt RD μ t) [])) = 0 := by
  have h := bubL_add' (K := K) μ t 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem evalB_bubR_up_single (dnScal : Fin m → Fin m → K) (lam : Wt m) (i : Fin m) (s : Wt m)
    (v : List (psig RD).Colour) (ha hb : WOK N s ((ob RD lam [up i]).word ++ v))
    (f : ob RD lam [] ⟶ ob RD lam []) (r : K) :
    evalB K N dnScal s v ha hb (bubR RD K lam [up i] (Finsupp.single f r)) =
      BHom.whiskerLeft (stepB K (true, i) (compOf N lam) (compOf N s) ha.step)
        (evalB K N dnScal (a := ob RD lam []) (b := ob RD lam []) lam v ha.tail hb.tail
          (Finsupp.single f r)) := by
  have e1 : bubR RD K lam [up i] (Finsupp.single f r : LEnd RD K (ob RD lam [])) =
      Finsupp.single (Diagram.cast (Diagram.whisker f (ob RD lam [up i]) []
        (whiskerOK_right RD lam [up i])) (whisker_right_eq RD lam [up i])
        (whisker_right_eq RD lam [up i])) r := by
    simp only [bubR]
    erw [LinDiagram.whisker_single, LinDiagram.cast_single]
  rw [e1, evalB_single, evalB_single, BHom.smul_def, BHom.smul_def, BHom.whiskerLeft_csmul]
  congr 1
  have el : (Diagram.layers (Diagram.cast (Diagram.whisker f (ob RD lam [up i]) []
        (whiskerOK_right RD lam [up i])) (whisker_right_eq RD lam [up i])
        (whisker_right_eq RD lam [up i]))).map (dataV v) =
      ((Diagram.layers f).map (dataV v)).map (LData.pre [⟨up i, lam⟩]) := by
    simp only [Diagram.layers_cast, Diagram.layers_whisker, List.map_map]
    refine List.map_congr_left fun L _ => ?_
    simp [dataV, LData.pre, Layer.whisker]
  have h' := (chainW_of_chain v (Diagram.chain f)).pre [⟨up i, lam⟩]
  show chainBD K N dnScal s ([⟨up i, lam⟩] ++ ((ob RD lam []).word ++ v)) _
    ([⟨up i, lam⟩] ++ ((ob RD lam []).word ++ v)) _ ha hb = _
  rw [chainBD_congr dnScal s rfl rfl el _ h' ha ha hb hb]
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']
  rw [chainBD_prefix dnScal s [⟨up i, lam⟩] _ _ _ (chainW_of_chain v (Diagram.chain f)) ha hb]
  rfl

/-- **A bubble to the right of an upward strand** (`bubR`): `Γ_N` of the bubble in the region
`λ`, whiskered on the left by the strand `E_i`. -/
theorem evalB_bubR_up (dnScal : Fin m → Fin m → K) (lam : Wt m) (i : Fin m) (s : Wt m)
    (v : List (psig RD).Colour) (ha hb : WOK N s ((ob RD lam [up i]).word ++ v))
    (b : LEnd RD K (ob RD lam [])) :
    evalB K N dnScal s v ha hb (bubR RD K lam [up i] b) =
      BHom.whiskerLeft (stepB K (true, i) (compOf N lam) (compOf N s) ha.step)
        (evalB K N dnScal (a := ob RD lam []) (b := ob RD lam []) lam v ha.tail hb.tail b) := by
  induction b using Finsupp.induction_linear with
  | zero => rw [bubR_zero', map_zero, map_zero, BHom.whiskerLeft_zero]
  | add f g hf hg => rw [bubR_add', map_add, hf, hg, map_add, BHom.whiskerLeft_add]
  | single f r => exact evalB_bubR_up_single dnScal lam i s v ha hb f r

theorem evalB_bubL_up_single (dnScal : Fin m → Fin m → K) (μ : Wt m) (i : Fin m) (s : Wt m)
    (v : List (psig RD).Colour) (ha hb : WOK N s ((ob RD μ [up i]).word ++ v))
    (f : ob RD (wt RD μ [up i]) [] ⟶ ob RD (wt RD μ [up i]) []) (r : K) :
    evalB K N dnScal s v ha hb (bubL RD K μ [up i] (Finsupp.single f r)) =
      evalB K N dnScal (a := ob RD (wt RD μ [up i]) []) (b := ob RD (wt RD μ [up i]) []) s
        ([⟨up i, μ⟩] ++ v) ha hb (Finsupp.single f r) := by
  have e1 : bubL RD K μ [up i] (Finsupp.single f r : LEnd RD K (ob RD (wt RD μ [up i]) [])) =
      Finsupp.single (Diagram.cast (Diagram.whisker f (ob RD (wt RD μ [up i]) [])
        (wd RD μ [up i]) (whiskerOK_left RD μ [up i])) (whisker_left_eq RD μ [up i])
        (whisker_left_eq RD μ [up i])) r := by
    simp only [bubL]
    erw [LinDiagram.whisker_single, LinDiagram.cast_single]
  rw [e1, evalB_single, evalB_single]
  congr 1
  have el : (Diagram.layers (Diagram.cast (Diagram.whisker f (ob RD (wt RD μ [up i]) [])
        (wd RD μ [up i]) (whiskerOK_left RD μ [up i])) (whisker_left_eq RD μ [up i])
        (whisker_left_eq RD μ [up i]))).map (dataV v) =
      (Diagram.layers f).map (dataV ([⟨up i, μ⟩] ++ v)) := by
    simp only [Diagram.layers_cast, Diagram.layers_whisker, List.map_map]
    refine List.map_congr_left fun L _ => ?_
    simp [dataV, Layer.whisker, ob]
  show chainBD K N dnScal s ((ob RD (wt RD μ [up i]) []).word ++ ([⟨up i, μ⟩] ++ v)) _
    ((ob RD (wt RD μ [up i]) []).word ++ ([⟨up i, μ⟩] ++ v)) _ ha hb = _
  rw [chainBD_congr dnScal s rfl rfl el _ (chainW_of_chain _ (Diagram.chain f)) ha ha hb hb]
  simp only [trW_self, BHom.id_comp', BHom.comp_id'']

/-- **A bubble to the left of an upward strand** (`bubL`): `Γ_N` of the bubble in the region
`μ + i_X`, whiskered on the right by the strand `E_i` (and `v`). -/
theorem evalB_bubL_up (dnScal : Fin m → Fin m → K) (μ : Wt m) (i : Fin m) (s : Wt m)
    (v : List (psig RD).Colour) (ha hb : WOK N s ((ob RD μ [up i]).word ++ v))
    (b : LEnd RD K (ob RD (wt RD μ [up i]) [])) :
    evalB K N dnScal s v ha hb (bubL RD K μ [up i] b) =
      evalB K N dnScal (a := ob RD (wt RD μ [up i]) []) (b := ob RD (wt RD μ [up i]) []) s
        ([⟨up i, μ⟩] ++ v) ha hb b := by
  induction b using Finsupp.induction_linear with
  | zero => rw [bubL_zero', map_zero, map_zero]
  | add f g hf hg => rw [bubL_add', map_add, hf, hg, map_add]
  | single f r => exact evalB_bubL_up_single dnScal μ i s v ha hb f r

end Categorification.Flag

end
