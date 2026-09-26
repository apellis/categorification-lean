/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaEval
import Categorification.Flag.GammaSideways

/-!
# `Γ_N` respects the interchange law

The presentation `P` of a 2-category on a signature `S` imposes, besides its relations, every
whiskered instance of the interchange law (`StringDiagrams.InterchangeData`): two generators `g`,
`h` separated by strands `mid` can be applied in either order. Here all generators are even, so
the sign is `1`. We prove that `gammaFunctor` kills every whiskered interchange relation
(`gamma_interchange`), which is the `interchange` field of `StringDiagrams.Presentation.Respects`
for any presentation on `psig (slRootDatum m)`.

The proof: the generator maps are natural in the path to their right (`genMap_natural`: for a
family `θ` of bimodule maps between suffix paths, `Γ(g) ∘ (dom g ⊗ θ) = (cod g ⊗ θ) ∘ Γ(g)`),
from the naturality of the whiskered crossings (`locTwo_natural`), dots (`whisker_exchange`),
cups and caps (`cupFEW_nat`, …) and of the identification `trS` (`trS_natural`); a layer with
strands `l₁ ++ l₂` on its left is the whiskering by the path of `l₁` of the layer with `l₂` on its
left (`layerMap_append`); and the intermediate objects of the two orders are valid as soon as the
source and the target are (`wok_mid`).
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### Naturality of the local maps -/

section Natural

variable {A B C D E E' : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [CommRing E] [CommRing E']

theorem whiskerLeft_assoc_hom {L : BRing A B} {L' : BRing B C} {X X' : BRing C E}
    (θ : BHom X X') (z : (L.tensor L').T) (x : X.T) :
    BHom.whiskerLeft L (BHom.whiskerLeft L' θ) ((BRing.assoc L L' X).hom (BRing.tmul _ X z x)) =
      (BRing.assoc L L' X').hom (BRing.tmul _ X' z (θ x)) := by
  refine BRing.induction_on (P := fun z => BHom.whiskerLeft L (BHom.whiskerLeft L' θ)
      ((BRing.assoc L L' X).hom (BRing.tmul (L.tensor L') X z x)) =
      (BRing.assoc L L' X').hom (BRing.tmul (L.tensor L') X' z (θ x))) z ?_ (fun a b => ?_)
    (fun z z' hz hz' => ?_)
  · simp only [BRing.zero_tmul, BHom.map_zero]
  · beta_reduce
    rw [BRing.assoc_hom_tmul, BRing.assoc_hom_tmul, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul]
  · beta_reduce at hz hz' ⊢
    rw [BRing.add_tmul, BHom.map_add, BHom.map_add, hz, hz', BRing.add_tmul, BHom.map_add]

/-- **Naturality of a whiskered two-strand map in the suffix.** -/
theorem locTwo_natural {L : BRing A B} {L' : BRing B C} {R : BRing A D} {R' : BRing D C}
    (φ : BHom (L.tensor L') (R.tensor R')) {X X' : BRing C E} (θ : BHom X X') :
    (locTwo φ X').comp (BHom.whiskerLeft L (BHom.whiskerLeft L' θ)) =
      (BHom.whiskerLeft R (BHom.whiskerLeft R' θ)).comp (locTwo φ X) := by
  refine BHom.ext fun t => ?_
  refine BRing.induction_on (P := fun t => (locTwo φ X').comp
      (BHom.whiskerLeft L (BHom.whiskerLeft L' θ)) t =
      (BHom.whiskerLeft R (BHom.whiskerLeft R' θ)).comp (locTwo φ X) t) t
    (by simp only [BHom.map_zero]) (fun a n => ?_) (fun t t' ht ht' => ?_)
  · refine BRing.induction_on (P := fun n => (locTwo φ X').comp
        (BHom.whiskerLeft L (BHom.whiskerLeft L' θ)) (BRing.tmul L (L'.tensor X) a n) =
        (BHom.whiskerLeft R (BHom.whiskerLeft R' θ)).comp (locTwo φ X)
          (BRing.tmul L (L'.tensor X) a n)) n
      (by simp only [BRing.tmul_zero, BHom.map_zero]) (fun b x => ?_) (fun n n' hn hn' => ?_)
    · beta_reduce
      rw [BHom.comp_apply, BHom.comp_apply, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul,
        locTwo_tmul, locTwo_tmul, whiskerLeft_assoc_hom]
    · beta_reduce at hn hn' ⊢
      rw [BRing.tmul_add, BHom.map_add, BHom.map_add, hn, hn']
  · beta_reduce at ht ht' ⊢
    rw [BHom.map_add, BHom.map_add, ht, ht']

end Natural

section CupsNatural

variable (c : Fin m) {s s' : Comp m} (hE : StepR (true, c) s s') (hF : StepR (false, c) s' s)

theorem cupFEW_nat {C : Type u} [CommRing C] {X X' : BRing (H K s) C} (φ : BHom X X') :
    (cupFEW K c hE hF X').comp φ =
      (BHom.whiskerLeft (Fst (K := K) c hF) (BHom.whiskerLeft (Est (K := K) c hE) φ)).comp
        (cupFEW K c hE hF X) := by
  refine BHom.ext fun x => ?_
  rw [BHom.comp_apply, BHom.comp_apply, cupFEW_apply, cupFEW_apply, BHom.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul]

theorem cupEFW_nat {C : Type u} [CommRing C] {X X' : BRing (H K s') C} (φ : BHom X X') :
    (cupEFW K c hE hF X').comp φ =
      (BHom.whiskerLeft (Est (K := K) c hE) (BHom.whiskerLeft (Fst (K := K) c hF) φ)).comp
        (cupEFW K c hE hF X) := by
  refine BHom.ext fun x => ?_
  rw [BHom.comp_apply, BHom.comp_apply, cupEFW_apply, cupEFW_apply, BHom.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul]

theorem capFEW_nat {C : Type u} [CommRing C] {X X' : BRing (H K s) C} (φ : BHom X X') :
    (capFEW K c hE hF X').comp
        (BHom.whiskerLeft (Fst (K := K) c hF) (BHom.whiskerLeft (Est (K := K) c hE) φ)) =
      φ.comp (capFEW K c hE hF X) := by
  refine BHom.ext fun v => ?_
  refine BRing.induction_on (P := fun v => (capFEW K c hE hF X').comp
      (BHom.whiskerLeft (Fst (K := K) c hF) (BHom.whiskerLeft (Est (K := K) c hE) φ)) v =
      φ.comp (capFEW K c hE hF X) v) v
    (by simp only [BHom.map_zero]) (fun a w => ?_) (fun v v' hv hv' => ?_)
  · refine BRing.induction_on (P := fun w => (capFEW K c hE hF X').comp
        (BHom.whiskerLeft (Fst (K := K) c hF) (BHom.whiskerLeft (Est (K := K) c hE) φ))
          (BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor X) a w) =
        φ.comp (capFEW K c hE hF X)
          (BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor X) a w)) w
      (by simp only [BRing.tmul_zero, BHom.map_zero]) (fun b x => ?_) (fun w w' hw hw' => ?_)
    · beta_reduce
      rw [BHom.comp_apply, BHom.comp_apply, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul,
        capFEW_tmul, capFEW_tmul, φ.map_left]
    · beta_reduce at hw hw' ⊢
      rw [BRing.tmul_add, BHom.map_add, BHom.map_add, hw, hw']
  · beta_reduce at hv hv' ⊢
    rw [BHom.map_add, BHom.map_add, hv, hv']

theorem capEFW_nat {C : Type u} [CommRing C] {X X' : BRing (H K s') C} (φ : BHom X X') :
    (capEFW K c hE hF X').comp
        (BHom.whiskerLeft (Est (K := K) c hE) (BHom.whiskerLeft (Fst (K := K) c hF) φ)) =
      φ.comp (capEFW K c hE hF X) := by
  refine BHom.ext fun v => ?_
  refine BRing.induction_on (P := fun v => (capEFW K c hE hF X').comp
      (BHom.whiskerLeft (Est (K := K) c hE) (BHom.whiskerLeft (Fst (K := K) c hF) φ)) v =
      φ.comp (capEFW K c hE hF X) v) v
    (by simp only [BHom.map_zero]) (fun a w => ?_) (fun v v' hv hv' => ?_)
  · refine BRing.induction_on (P := fun w => (capEFW K c hE hF X').comp
        (BHom.whiskerLeft (Est (K := K) c hE) (BHom.whiskerLeft (Fst (K := K) c hF) φ))
          (BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor X) a w) =
        φ.comp (capEFW K c hE hF X)
          (BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor X) a w)) w
      (by simp only [BRing.tmul_zero, BHom.map_zero]) (fun b x => ?_) (fun w w' hw hw' => ?_)
    · beta_reduce
      rw [BHom.comp_apply, BHom.comp_apply, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul,
        capEFW_tmul, capEFW_tmul, φ.map_left]
    · beta_reduce at hw hw' ⊢
      rw [BRing.tmul_add, BHom.map_add, BHom.map_add, hw, hw']
  · beta_reduce at hv hv' ⊢
    rw [BHom.map_add, BHom.map_add, hv, hv']

end CupsNatural

/-- A family of bimodule maps between the paths `X` and `Y`, indexed by the start region. -/
abbrev SufFam (K : Type u) [Field K] (N : ℕ) (X Y : List (WCol m)) : Type u :=
  ∀ (ρ : Wt m) (hX : WOK N ρ X) (hY : WOK N ρ Y), BHom (gammaR K N ρ X hX) (gammaR K N ρ Y hY)

theorem trS_natural {X Y : List (WCol m)} (θ : SufFam K N X Y) (l : SLetter m) (L a b : Wt m)
    (e : a = b) (h : StepR l (compOf N a) (compOf N L)) (h' : StepR l (compOf N b) (compOf N L))
    (hX : WOK N a X) (hX' : WOK N b X) (hY : WOK N a Y) (hY' : WOK N b Y) :
    (trS (K := K) l L a b e Y h h' hY hY').comp
        (BHom.whiskerLeft (stepB K l (compOf N a) (compOf N L) h) (θ a hX hY)) =
      (BHom.whiskerLeft (stepB K l (compOf N b) (compOf N L) h') (θ b hX' hY')).comp
        (trS l L a b e X h h' hX hX') := by
  subst e
  rfl

/-! ### Naturality of the generator maps in the suffix -/

/-- **`Γ` of a generator is natural in the path to its right.** -/
theorem genMap_natural (s : Wt m) {X Y : List (WCol m)} (θ : SufFam K N X Y) :
    ∀ (g : (psig RD).Gen) (hdX : WOK N s (gdom g ++ X)) (hcX : WOK N s (gcod g ++ X))
      (hdY : WOK N s (gdom g ++ Y)) (hcY : WOK N s (gcod g ++ Y)),
      (genMap K N s g Y hdY hcY).comp (wlPath K N s (gdom g) X Y hdX hdY (θ _ _ _)) =
        (wlPath K N s (gcod g) X Y hcX hcY (θ _ _ _)).comp (genMap K N s g X hdX hcX)
  | .gen (.dot c), hdX, hcX, hdY, hcY =>
    (BHom.whisker_exchange (BHom.mulB (xiStep K c.l (compOf N c.r) (compOf N s) hdX.step))
      (θ c.r hdX.tail hdY.tail)).symm
  | .gen (.cross true i j ν), hdX, hcX, hdY, hcY =>
    locTwo_natural (crossU K i j hdX.step hdX.tail.step hcX.step hcX.tail.step) (θ ν _ _)
  | .gen (.cross false i j ν), hdX, hcX, hdY, hcY =>
    locTwo_natural (crossDn K i j hdX.step hdX.tail.step hcX.step hcX.tail.step) (θ ν _ _)
  | .cup ⟨(false, i), r⟩, hdX, hcX, hdY, hcY => by
    show ((BHom.whiskerLeft _ (trS (K := K) (true, i) r s _ _ Y _ _ hdY _)).comp
      (cupFEW K i _ _ (gammaR K N s Y hdY))).comp (θ s hdX hdY) =
      (BHom.whiskerLeft _ (BHom.whiskerLeft _ (θ _ _ _))).comp
        ((BHom.whiskerLeft _ (trS (true, i) r s _ _ X _ _ hdX _)).comp
          (cupFEW K i _ _ (gammaR K N s X hdX)))
    rw [BHom.comp_assoc, cupFEW_nat, ← BHom.comp_assoc, ← BHom.whiskerLeft_comp,
      trS_natural θ (true, i) r s (sh RD (false, i) + r) _ _ _ hdX
        (hcX.tail.tail : WOK N (sh RD (false, i) + r) X) hdY _,
      BHom.whiskerLeft_comp, BHom.comp_assoc]
  | .cup ⟨(true, i), r⟩, hdX, hcX, hdY, hcY => by
    show ((BHom.whiskerLeft _ (trS (K := K) (false, i) r s _ _ Y _ _ hdY _)).comp
      (cupEFW K i _ _ (gammaR K N s Y hdY))).comp (θ s hdX hdY) =
      (BHom.whiskerLeft _ (BHom.whiskerLeft _ (θ _ _ _))).comp
        ((BHom.whiskerLeft _ (trS (false, i) r s _ _ X _ _ hdX _)).comp
          (cupEFW K i _ _ (gammaR K N s X hdX)))
    rw [BHom.comp_assoc, cupEFW_nat, ← BHom.comp_assoc, ← BHom.whiskerLeft_comp,
      trS_natural θ (false, i) r s (sh RD (true, i) + r) _ _ _ hdX
        (hcX.tail.tail : WOK N (sh RD (true, i) + r) X) hdY _,
      BHom.whiskerLeft_comp, BHom.comp_assoc]
  | .cap ⟨(true, i), r⟩, hdX, hcX, hdY, hcY => by
    show ((capFEW K i _ _ (gammaR K N s Y hcY)).comp
      (BHom.whiskerLeft _ (trS (K := K) (true, i) _ r s _ Y _ _ _ hcY))).comp
        (BHom.whiskerLeft _ (BHom.whiskerLeft _ (θ _ _ _))) =
      (θ s hcX hcY).comp ((capFEW K i _ _ (gammaR K N s X hcX)).comp
        (BHom.whiskerLeft _ (trS (true, i) _ r s _ X _ _ _ hcX)))
    rw [BHom.comp_assoc, ← BHom.whiskerLeft_comp, trS_natural, BHom.whiskerLeft_comp,
      ← BHom.comp_assoc, capFEW_nat, BHom.comp_assoc]
  | .cap ⟨(false, i), r⟩, hdX, hcX, hdY, hcY => by
    show ((capEFW K i _ _ (gammaR K N s Y hcY)).comp
      (BHom.whiskerLeft _ (trS (K := K) (false, i) _ r s _ Y _ _ _ hcY))).comp
        (BHom.whiskerLeft _ (BHom.whiskerLeft _ (θ _ _ _))) =
      (θ s hcX hcY).comp ((capEFW K i _ _ (gammaR K N s X hcX)).comp
        (BHom.whiskerLeft _ (trS (false, i) _ r s _ X _ _ _ hcX)))
    rw [BHom.comp_assoc, ← BHom.whiskerLeft_comp, trS_natural, BHom.whiskerLeft_comp,
      ← BHom.comp_assoc, capEFW_nat, BHom.comp_assoc]

/-! ### Layers with a composite left part -/

theorem trW_cons' (s : Wt m) (c : WCol m) {w w' : List (WCol m)} (e : c :: w = c :: w')
    (h : WOK N s (c :: w)) (h' : WOK N s (c :: w')) :
    trW (K := K) s e h h' =
      BHom.whiskerLeft (stepB K c.l (compOf N c.r) (compOf N s) h.step)
        (trW c.r (List.cons.inj e).2 h.tail h'.tail) := by
  obtain ⟨-, e'⟩ := List.cons.inj e
  subst e'
  exact (BHom.whiskerLeft_id _ _).symm

theorem assoc4 (l₁ l₂ a r : List (WCol m)) : l₁ ++ l₂ ++ a ++ r = l₁ ++ (l₂ ++ a ++ r) := by
  simp only [List.append_assoc]

/-- **A layer with strands `l₁ ++ l₂` on its left is the whiskering by the path of `l₁` of the
layer with `l₂` on its left**, up to the associativity of the boundary words. -/
theorem layerMap_append (s : Wt m) : ∀ (l₁ l₂ : List (WCol m)) (g : (psig RD).Gen)
    (r : List (WCol m)) (hd : WOK N s (l₁ ++ l₂ ++ gdom g ++ r))
    (hc : WOK N s (l₁ ++ l₂ ++ gcod g ++ r)) (hd' : WOK N s (l₁ ++ (l₂ ++ gdom g ++ r)))
    (hc' : WOK N s (l₁ ++ (l₂ ++ gcod g ++ r))),
    layerMap K N s (l₁ ++ l₂) g r hd hc =
      (trW s (assoc4 l₁ l₂ (gcod g) r).symm hc' hc).comp
        ((wlPath K N s l₁ _ _ hd' hc' (layerMap K N ((psig RD).endR s l₁) l₂ g r _ _)).comp
          (trW s (assoc4 l₁ l₂ (gdom g) r) hd hd'))
  | [], l₂, g, r, hd, hc, hd', hc' => rfl
  | c :: l₁, l₂, g, r, hd, hc, hd', hc' => by
    show BHom.whiskerLeft (stepB K c.l (compOf N c.r) (compOf N s) hd.step)
        (layerMap K N c.r (l₁ ++ l₂) g r hd.tail hc.tail) = _
    rw [layerMap_append c.r l₁ l₂ g r hd.tail hc.tail hd'.tail hc'.tail, BHom.whiskerLeft_comp,
      BHom.whiskerLeft_comp, trW_cons', trW_cons']
    rfl

/-! ### Scalars -/

theorem BHom.comp_csmul {A : Type u} [CommRing A] {M M' M'' : BRing A K} (φ : BHom M' M'')
    (c : K) (ψ : BHom M M') : φ.comp (BHom.csmul c ψ) = BHom.csmul c (φ.comp ψ) :=
  BHom.ext fun x => φ.map_right c (ψ x)

theorem BHom.csmul_comp {A : Type u} [CommRing A] {M M' M'' : BRing A K} (c : K)
    (φ : BHom M' M'') (ψ : BHom M M') : (BHom.csmul c φ).comp ψ = BHom.csmul c (φ.comp ψ) := rfl

theorem BHom.csmul_csmul {A : Type u} [CommRing A] {M M' : BRing A K} (c d : K) (φ : BHom M M') :
    BHom.csmul c (BHom.csmul d φ) = BHom.csmul d (BHom.csmul c φ) :=
  BHom.ext fun x => by
    show M'.right c * (M'.right d * φ x) = M'.right d * (M'.right c * φ x)
    exact mul_left_comm _ _ _

/-! ### The interchange law -/

theorem sign_psig (x : InterchangeData (psig RD)) : x.sign = 1 := by
  simp [InterchangeData.sign, Signature.IsEven.odd_eq_false]

theorem BHom.id_comp' {A B : Type u} [CommRing A] [CommRing B] {M M' : BRing A B}
    (φ : BHom M M') : (BHom.id M').comp φ = φ := BHom.ext fun _ => rfl

theorem trW_comp_trW' (s : Wt m) {w₁ w₂ w₃ : List (WCol m)} (e : w₁ = w₂) (e' : w₂ = w₃)
    (h₁ : WOK N s w₁) (h₂ : WOK N s w₂) (h₃ : WOK N s w₃) :
    (trW (K := K) s e' h₂ h₃).comp (trW s e h₁ h₂) = trW s (e.trans e') h₁ h₃ := by
  subst e e'
  rfl

theorem trW_comp_trW (s : Wt m) {w₁ w₂ w₃ : List (WCol m)} (e : w₁ = w₂) (e' : w₂ = w₃)
    (h₁ : WOK N s w₁) (h₂ : WOK N s w₂) (h₃ : WOK N s w₃)
    {M : BRing (H K (compOf N s)) K} (φ : BHom M (gammaR K N s w₁ h₁)) :
    (trW (K := K) s e' h₂ h₃).comp ((trW s e h₁ h₂).comp φ) = (trW s (e.trans e') h₁ h₃).comp φ := by
  subst e e'
  rfl

variable (K N) in
/-- The layer map of `h` after `mid`, as a family indexed by the start region. -/
def midFam (M : List (WCol m)) (h : (psig RD).Gen) (v : List (WCol m)) :
    SufFam K N (M ++ gdom h ++ v) (M ++ gcod h ++ v) :=
  fun ρ hX hY => layerMap K N ρ M h v hX hY

/-- **`Γ_N` respects the interchange law** (bimodule form): the two orders of two generators
separated by `mid`, whiskered by `v` on the right, have the same image. -/
theorem evalB_interchange (dnScal : Fin m → Fin m → K) (x : InterchangeData (psig RD))
    (hx : x.Valid) (s : Wt m) (hs : s = x.start) (v : List (psig RD).Colour)
    (ha : WOK N s (x.dom.word ++ v)) (hb : WOK N s (x.cod.word ++ v)) :
    evalB K N dnScal s v ha hb (InterchangeData.rel K hx) = 0 := by
  subst hs
  rw [InterchangeData.rel, map_sub, map_smul, evalB_of, evalB_of, sign_psig, Int.cast_one,
    one_smul, sub_eq_zero]
  -- the boundary regions of `g`
  have hg1 := hx.gh₁.left_end
  have hg2 := hx.gh₁.dom_end
  have hg3 := hx.gh₁.cod_end
  simp only [InterchangeData.gh₁, Signature.endR_nil] at hg1 hg2 hg3
  have hAB : (psig RD).endR x.start (gdom x.g) = (psig RD).endR x.start (gcod x.g) := by
    rw [hg1, hg2, hg3]
  -- validity of the intermediate objects
  have ha' : WOK N x.start (gdom x.g ++ ((x.mid ++ gdom x.h) ++ v)) := by
    have := ha
    simp only [InterchangeData.dom, List.append_assoc] at this ⊢
    exact this
  have hb' : WOK N x.start (gcod x.g ++ ((x.mid ++ gcod x.h) ++ v)) := by
    have := hb
    simp only [InterchangeData.cod, List.append_assoc] at this ⊢
    exact this
  have hM1 : WOK N x.start (gcod x.g ++ ((x.mid ++ gdom x.h) ++ v)) := by
    rw [wok_append] at ha' hb' ⊢
    exact ⟨hb'.1, hAB ▸ ha'.2⟩
  have hM1' : WOK N x.start (gdom x.g ++ ((x.mid ++ gcod x.h) ++ v)) := by
    rw [wok_append] at ha' hb' ⊢
    exact ⟨ha'.1, hAB.symm ▸ hb'.2⟩
  show chainBD K N dnScal x.start _ [dataV v x.gh₁, dataV v x.gh₂] _ _ ha hb =
    chainBD K N dnScal x.start _ [dataV v x.hg₁, dataV v x.hg₂] _ _ ha hb
  simp only [chainBD]
  rw [dif_pos (show WOK N x.start ((dataV v x.gh₁).1 ++ gcod (dataV v x.gh₁).2.1 ++
      (dataV v x.gh₁).2.2) from hM1),
    dif_pos (show WOK N x.start ((dataV v x.gh₂).1 ++ gcod (dataV v x.gh₂).2.1 ++
      (dataV v x.gh₂).2.2) from hb),
    dif_pos (show WOK N x.start ((dataV v x.hg₁).1 ++ gcod (dataV v x.hg₁).2.1 ++
      (dataV v x.hg₁).2.2) by
        simpa only [dataV, InterchangeData.hg₁, List.append_assoc, List.nil_append] using hM1'),
    dif_pos (show WOK N x.start ((dataV v x.hg₂).1 ++ gcod (dataV v x.hg₂).2.1 ++
      (dataV v x.hg₂).2.2) from hb')]
  simp only [dataV, InterchangeData.gh₁, InterchangeData.gh₂, InterchangeData.hg₁,
    InterchangeData.hg₂]
  rw [layerMap_append x.start (gcod x.g) x.mid x.h ([] ++ v) _ _ hM1 hb',
    layerMap_append x.start (gdom x.g) x.mid x.h ([] ++ v) _ _ ha' hM1']
  simp only [BHom.csmul_comp, BHom.comp_csmul, BHom.comp_assoc]
  rw [BHom.csmul_csmul]
  congr 2
  simp only [trW_comp_trW, trW_comp_trW']
  rw [trW_self, trW_self, BHom.id_comp', BHom.id_comp']
  congr 1
  exact (congrArg (fun F => BHom.comp F (trW x.start _ ha ha'))
    (genMap_natural x.start (midFam K N x.mid x.h ([] ++ v)) x.g ha' hM1 hM1' hb')).symm

/-! ### `Presentation.Respects` -/

/-- **`Γ_N` respects the interchange law**: the `interchange` field of `Presentation.Respects`. -/
theorem gamma_interchange (dnScal : Fin m → Fin m → K) (x : InterchangeData (psig RD))
    (hx : x.Valid) (u : Obj (psig RD)) (v : List (psig RD).Colour) (hw : x.dom.WhiskerOK u v) :
    (gammaLI K N dnScal).evalW ((gammaLI K N dnScal).κ (x.dom.whisker u v))
      ((gammaLI K N dnScal).κ (x.cod.whisker u v)) u v (InterchangeData.rel K hx) = 0 :=
  evalW_eq_zero_of_evalB dnScal _ u v hw fun s hs ha hb =>
    evalB_interchange dnScal x hx s hs v ha hb

/-- **Soundness of `Γ_N` for a presentation on `psig (slRootDatum m)`**: if the bimodule
evaluation of every relation vanishes (whiskered by any `v` on the right, from the start region
of its source, whenever both ends are valid), then `gammaFunctor` respects the presentation, and
descends to the presented category (`gammaLift`). -/
theorem gamma_respects (dnScal : Fin m → Fin m → K) (P : Presentation (psig RD) K)
    (hP : ∀ (r : P.Rel) (s : Wt m), s = (P.dom r).start → ∀ (v : List (psig RD).Colour)
      (ha : WOK N s ((P.dom r).word ++ v)) (hb : WOK N s ((P.cod r).word ++ v)),
      evalB K N dnScal s v ha hb (P.rel r) = 0) :
    P.Respects (gammaFunctor K N dnScal) :=
  (gammaLI K N dnScal).respects_of P
    (fun r u v hw => evalW_eq_zero_of_evalB dnScal (P.rel r) u v hw fun s hs ha hb =>
      hP r s hs v ha hb)
    (fun x hx u v hw => gamma_interchange dnScal x hx u v hw)

variable (K N) in
/-- **`Γ_N` on the presented category** (KL III Theorem 6.11's 2-functor, restricted to each
hom-category and landing in `K`-modules). -/
def gammaLift (dnScal : Fin m → Fin m → K) (P : Presentation (psig RD) K)
    (hP : ∀ (r : P.Rel) (s : Wt m), s = (P.dom r).start → ∀ (v : List (psig RD).Colour)
      (ha : WOK N s ((P.dom r).word ++ v)) (hb : WOK N s ((P.cod r).word ++ v)),
      evalB K N dnScal s v ha hb (P.rel r) = 0) :
    P.Presented ⥤ ModuleCat.{u} K :=
  P.lift (gamma_respects dnScal P hP)

end Categorification.Flag

end
