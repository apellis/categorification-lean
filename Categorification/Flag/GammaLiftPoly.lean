/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftBasic
import Categorification.Diagrams.KL3.Upward

/-!
# `Γ_N` on composites and on polynomials in dots

General facts about the bimodule evaluation `evalB` (`Categorification.Flag.GammaEval`) used by
the relation checks of the assembly of `Γ_N`:

* `chainBD_append`: the chain map of a concatenation of layer lists is the composite of the chain
  maps, when the middle boundary is valid;
* `evalB_comp`: `evalB` sends the composite `F ≫ G` of linear combinations of diagrams to the
  composite of the evaluations (for a valid middle object);
* `evalB_ncEval`: `evalB` of a polynomial `p` evaluated on endomorphisms `y a` of an object
  (`KLR.ncEval`, the form of `KLR.Diagram.lpoly` and of the correction terms of the KLR
  relations) is `p` evaluated on the images of the `y a`, as soon as these images are
  multiplications by commuting elements.
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### Bilinearity of composition of bimodule maps -/

section Bilin

variable {A B : Type u} [CommRing A] [CommRing B] {M M' M'' : BRing A B}

theorem BHom.comp_zero' (φ : BHom M' M'') : φ.comp (0 : BHom M M') = 0 :=
  BHom.ext fun _ => φ.map_zero

theorem BHom.zero_comp' (φ : BHom M M') : (0 : BHom M' M'').comp φ = 0 :=
  BHom.ext fun _ => rfl

theorem BHom.comp_add' (φ : BHom M' M'') (ψ ψ' : BHom M M') :
    φ.comp (ψ + ψ') = φ.comp ψ + φ.comp ψ' :=
  BHom.ext fun x => φ.toAddHom.map_add (ψ x) (ψ' x)

theorem BHom.add_comp' (φ φ' : BHom M' M'') (ψ : BHom M M') :
    (φ + φ').comp ψ = φ.comp ψ + φ'.comp ψ :=
  BHom.ext fun _ => rfl

end Bilin

section SMul

variable {A : Type u} [CommRing A] {M M' M'' : BRing A K}

theorem BHom.comp_smul' (φ : BHom M' M'') (c : K) (ψ : BHom M M') :
    φ.comp (c • ψ) = c • φ.comp ψ :=
  BHom.comp_csmul φ c ψ

theorem BHom.smul_comp' (c : K) (φ : BHom M' M'') (ψ : BHom M M') :
    (c • φ).comp ψ = c • φ.comp ψ := rfl

end SMul

/-! ### Concatenation of chains -/

theorem ChainW.append : ∀ {w w' w'' : List (WCol m)} {ls₁ ls₂ : List (LData m)},
    ChainW w ls₁ w' → ChainW w' ls₂ w'' → ChainW w (ls₁ ++ ls₂) w''
  | _, _, _, [], _, h₁, h₂ => by
    obtain rfl := (h₁ : _ = _)
    exact h₂
  | _, _, _, _ :: _, _, h₁, h₂ => ⟨h₁.1, ChainW.append h₁.2 h₂⟩

open Classical in
/-- **The chain map of a concatenation** is the composite of the chain maps. -/
theorem chainBD_append (dnScal : Fin m → Fin m → K) (s : Wt m) :
    ∀ (w : List (WCol m)) (ls₁ : List (LData m)) (w' : List (WCol m)) (ls₂ : List (LData m))
      (w'' : List (WCol m)) (h₁ : ChainW w ls₁ w') (h₂ : ChainW w' ls₂ w'')
      (h : ChainW w (ls₁ ++ ls₂) w'') (ha : WOK N s w) (hm : WOK N s w') (hb : WOK N s w''),
      chainBD K N dnScal s w (ls₁ ++ ls₂) w'' h ha hb =
        (chainBD K N dnScal s w' ls₂ w'' h₂ hm hb).comp (chainBD K N dnScal s w ls₁ w' h₁ ha hm)
  | w, [], w', ls₂, w'', h₁, h₂, h, ha, hm, hb => by
    obtain rfl := (h₁ : w = w')
    exact BHom.ext fun _ => rfl
  | w, d :: ls, w', ls₂, w'', h₁, h₂, h, ha, hm, hb => by
    by_cases hL : WOK N s (d.1 ++ gcod d.2.1 ++ d.2.2)
    · have ih := chainBD_append dnScal s _ ls w' ls₂ w'' h₁.2 h₂ h.2 hL hm hb
      show (if hL : _ then _ else 0) = BHom.comp _ (if hL : _ then _ else 0)
      rw [dif_pos hL, dif_pos hL]
      exact (congrArg (fun φ => BHom.comp φ _) ih).trans (BHom.comp_assoc _ _ _)
    · show (if hL : _ then _ else 0) = BHom.comp _ (if hL : _ then _ else 0)
      rw [dif_neg hL, dif_neg hL, BHom.comp_zero']

/-! ### Composites of linear combinations -/

theorem evalB_single (dnScal : Fin m → Fin m → K) {a b : Obj (psig RD)} (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s (a.word ++ v)) (hb : WOK N s (b.word ++ v))
    (f : a ⟶ b) (r : K) :
    evalB K N dnScal s v ha hb (Finsupp.single f r) =
      r • chainBD K N dnScal s (a.word ++ v) ((Diagram.layers f).map (dataV v)) (b.word ++ v)
        (chainW_of_chain v (Diagram.chain f)) ha hb :=
  Finsupp.linearCombination_single K r f

theorem chainBD_comp (dnScal : Fin m → Fin m → K) {a b c : Obj (psig RD)} (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s (a.word ++ v)) (hm : WOK N s (b.word ++ v))
    (hc : WOK N s (c.word ++ v)) (f : a ⟶ b) (g : b ⟶ c) :
    chainBD K N dnScal s (a.word ++ v) ((Diagram.layers (f ≫ g)).map (dataV v)) (c.word ++ v)
        (chainW_of_chain v (Diagram.chain (f ≫ g))) ha hc =
      (chainBD K N dnScal s (b.word ++ v) ((Diagram.layers g).map (dataV v)) (c.word ++ v)
          (chainW_of_chain v (Diagram.chain g)) hm hc).comp
        (chainBD K N dnScal s (a.word ++ v) ((Diagram.layers f).map (dataV v)) (b.word ++ v)
          (chainW_of_chain v (Diagram.chain f)) ha hm) := by
  have el : (Diagram.layers (f ≫ g)).map (dataV v) =
      (Diagram.layers f).map (dataV v) ++ (Diagram.layers g).map (dataV v) := by
    rw [Diagram.layers_comp, List.map_append]
  have h' := ChainW.append (chainW_of_chain v (Diagram.chain f)) (chainW_of_chain v (Diagram.chain g))
  rw [chainBD_congr dnScal s rfl rfl el _ h' ha ha hc hc, chainBD_append dnScal s _ _ _ _ _
    (chainW_of_chain v (Diagram.chain f)) (chainW_of_chain v (Diagram.chain g)) h' ha hm hc]
  rfl

/-- **`evalB` of a composite** is the composite of the evaluations. -/
theorem evalB_comp (dnScal : Fin m → Fin m → K) {a b c : Obj (psig RD)} (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s (a.word ++ v)) (hm : WOK N s (b.word ++ v))
    (hc : WOK N s (c.word ++ v)) (F : LinDiagram K a b) (G : LinDiagram K b c) :
    evalB K N dnScal s v ha hc (F ≫ G) =
      (evalB K N dnScal s v hm hc G).comp (evalB K N dnScal s v ha hm F) := by
  induction F using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, BHom.comp_zero']
  | add F₁ F₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, map_add, h₁, h₂, BHom.comp_add']
  | single f r =>
    induction G using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, BHom.zero_comp']
    | add G₁ G₂ h₁ h₂ => rw [Preadditive.comp_add, map_add, map_add, h₁, h₂, BHom.add_comp']
    | single g t =>
      erw [Free.single_comp_single]
      rw [evalB_single, evalB_single, evalB_single, BHom.smul_comp',
        BHom.comp_smul', smul_smul, mul_comm t r, chainBD_comp dnScal s v ha hm hc f g]

/-! ### Composites through an invalid object -/

open Classical in
/-- A chain passing through an invalid boundary is zero. -/
theorem chainBD_append_zero (dnScal : Fin m → Fin m → K) (s : Wt m) :
    ∀ (w : List (WCol m)) (ls₁ : List (LData m)) (w' : List (WCol m)) (ls₂ : List (LData m))
      (w'' : List (WCol m)) (_ : ChainW w ls₁ w') (_ : ¬ WOK N s w')
      (h : ChainW w (ls₁ ++ ls₂) w'') (ha : WOK N s w) (hb : WOK N s w''),
      chainBD K N dnScal s w (ls₁ ++ ls₂) w'' h ha hb = 0
  | w, [], w', _, _, h₁, hm, _, ha, _ => absurd ((h₁ : w = w') ▸ ha) hm
  | _, d :: ls, w', ls₂, w'', h₁, hm, h, _, hb => by
    by_cases hL : WOK N s (d.1 ++ gcod d.2.1 ++ d.2.2)
    · show (if hL : WOK N s (d.1 ++ gcod d.2.1 ++ d.2.2) then _ else 0) = 0
      rw [dif_pos hL]
      exact (congrArg (fun φ => BHom.comp φ _)
        (chainBD_append_zero dnScal s _ ls w' ls₂ w'' h₁.2 hm h.2 hL hb)).trans
        (BHom.zero_comp' _)
    · show (if hL : WOK N s (d.1 ++ gcod d.2.1 ++ d.2.2) then _ else 0) = 0
      rw [dif_neg hL]

theorem chainBD_comp_zero (dnScal : Fin m → Fin m → K) {a b c : Obj (psig RD)} (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s (a.word ++ v)) (hm : ¬ WOK N s (b.word ++ v))
    (hc : WOK N s (c.word ++ v)) (f : a ⟶ b) (g : b ⟶ c) :
    chainBD K N dnScal s (a.word ++ v) ((Diagram.layers (f ≫ g)).map (dataV v)) (c.word ++ v)
        (chainW_of_chain v (Diagram.chain (f ≫ g))) ha hc = 0 := by
  have el : (Diagram.layers (f ≫ g)).map (dataV v) =
      (Diagram.layers f).map (dataV v) ++ (Diagram.layers g).map (dataV v) := by
    rw [Diagram.layers_comp, List.map_append]
  have h' := ChainW.append (chainW_of_chain v (Diagram.chain f))
    (chainW_of_chain v (Diagram.chain g))
  rw [chainBD_congr dnScal s rfl rfl el _ h' ha ha hc hc,
    chainBD_append_zero dnScal s _ _ _ _ _ (chainW_of_chain v (Diagram.chain f)) hm h' ha hc,
    BHom.zero_comp', BHom.comp_zero']

/-- **`evalB` of a composite through an invalid object is zero.** -/
theorem evalB_comp_zero (dnScal : Fin m → Fin m → K) {a b c : Obj (psig RD)} (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s (a.word ++ v)) (hm : ¬ WOK N s (b.word ++ v))
    (hc : WOK N s (c.word ++ v)) (F : LinDiagram K a b) (G : LinDiagram K b c) :
    evalB K N dnScal s v ha hc (F ≫ G) = 0 := by
  induction F using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, map_zero]
  | add F₁ F₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, h₁, h₂, add_zero]
  | single f r =>
    induction G using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, map_zero]
    | add G₁ G₂ h₁ h₂ => rw [Preadditive.comp_add, map_add, h₁, h₂, add_zero]
    | single g t =>
      erw [Free.single_comp_single]
      rw [evalB_single, chainBD_comp_zero dnScal s v ha hm hc f g, smul_zero]

/-! ### Upward placement is a functor on linear combinations -/

theorem upDiag_id (μ : Wt m) (a : Obj (KLR.Diagram.sig (Fin m))) :
    upDiag RD μ (𝟙 a) = 𝟙 _ :=
  Diagram.ext rfl

theorem upDiag_comp (μ : Wt m) {a b c : Obj (KLR.Diagram.sig (Fin m))} (f : a ⟶ b) (g : b ⟶ c) :
    upDiag RD μ (f ≫ g) = upDiag RD μ f ≫ upDiag RD μ g :=
  Diagram.ext (by simp only [layers_upDiag, Diagram.layers_comp, List.map_append])

theorem upLin_comp (μ : Wt m) {a b c : Obj (KLR.Diagram.sig (Fin m))} (F : LinDiagram K a b)
    (G : LinDiagram K b c) : upLin RD K μ (F ≫ G) = upLin RD K μ F ≫ upLin RD K μ G := by
  have hlin : ∀ {a b : Obj (KLR.Diagram.sig (Fin m))} (F F' : LinDiagram K a b),
      upLin RD K μ (F + F') = upLin RD K μ F + upLin RD K μ F' :=
    fun _ _ => Finsupp.mapDomain_add
  have hzero : ∀ {a b : Obj (KLR.Diagram.sig (Fin m))},
      upLin RD K μ (0 : LinDiagram K a b) = 0 := Finsupp.mapDomain_zero
  have hsingle : ∀ {a b : Obj (KLR.Diagram.sig (Fin m))} (f : a ⟶ b) (r : K),
      upLin RD K μ (Finsupp.single f r) = Finsupp.single (upDiag RD μ f) r :=
    fun _ _ => Finsupp.mapDomain_single
  induction F using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, hzero, hzero, Limits.zero_comp]
  | add F₁ F₂ h₁ h₂ => rw [Preadditive.add_comp, hlin, hlin, h₁, h₂, Preadditive.add_comp]
  | single f r =>
    induction G using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, hzero, hzero, Limits.comp_zero]
    | add G₁ G₂ h₁ h₂ => rw [Preadditive.comp_add, hlin, hlin, h₁, h₂, Preadditive.comp_add]
    | single g t =>
      erw [Free.single_comp_single]
      rw [hsingle, hsingle, hsingle, upDiag_comp]
      erw [Free.single_comp_single]

/-! ### Polynomials in commuting multiplications -/

section MulLin

variable {A : Type u} [CommRing A]

/-- Multiplication by elements of the underlying ring, as a ring map to the `K`-linear
endomorphisms. -/
def mulLin (M : BRing A K) : M.T →+* Module.End K (RT M) where
  toFun x := BHom.toLin (BHom.mulB x)
  map_one' := LinearMap.ext fun y => one_mul (show M.T from y)
  map_mul' x x' := LinearMap.ext fun y => mul_assoc x x' (show M.T from y)
  map_zero' := LinearMap.ext fun y => zero_mul (show M.T from y)
  map_add' x x' := LinearMap.ext fun y => add_mul x x' (show M.T from y)

theorem mulLin_apply (M : BRing A K) (x : M.T) : mulLin M x = BHom.toLin (BHom.mulB x) := rfl

theorem algebraMap_end_eq_mulLin (M : BRing A K) (c : K) :
    algebraMap K (Module.End K (RT M)) c = mulLin M (M.right c) :=
  LinearMap.ext fun _ => rfl

/-- `ncEval` of commuting multiplications is the multiplication by the evaluated polynomial. -/
theorem ncEval_mulLin (M : BRing A K) {n : ℕ} (z : Fin n → M.T) (p : MvPolynomial (Fin n) K) :
    KLR.ncEval (fun a => mulLin M (z a)) p = mulLin M (MvPolynomial.eval₂ M.right z p) := by
  simp only [KLR.ncEval, MvPolynomial.eval₂, map_finsuppSum, map_mul, algebraMap_end_eq_mulLin]
  refine Finsupp.sum_congr fun s _ => ?_
  congr 1
  have hof : (List.ofFn fun a => mulLin M (z a) ^ s a) =
      (List.ofFn fun a => z a ^ s a).map (mulLin M) := by
    rw [List.map_ofFn]
    congr 1
    funext a
    exact (map_pow _ _ _).symm
  rw [hof, ← map_list_prod, List.prod_ofFn, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

end MulLin

/-- **`evalB` of a polynomial in commuting dots**: if the evaluations of the endomorphisms
`y a` of `a` are multiplications by the elements `z a`, the evaluation of `ncEval y p` is the
multiplication by `p(z)`. -/
theorem evalB_ncEval (dnScal : Fin m → Fin m → K) {a : Obj (psig RD)} (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s (a.word ++ v)) {n : ℕ}
    (y : Fin n → End (Free.of K a)) (z : Fin n → (gammaR K N s (a.word ++ v) ha).T)
    (hy : ∀ i, evalB K N dnScal s v ha ha (y i) = BHom.mulB (z i))
    (p : MvPolynomial (Fin n) K) :
    evalB K N dnScal s v ha ha (KLR.ncEval (A := End (Free.of K a)) y p) =
      BHom.mulB (MvPolynomial.eval₂ (gammaR K N s (a.word ++ v) ha).right z p) := by
  let φ : End (Free.of K a) →ₗ[K] Module.End K (RT (gammaR K N s (a.word ++ v) ha)) :=
    BHom.toLinL ∘ₗ evalB K N dnScal s v ha ha
  have hmul : ∀ F G, φ (F * G) = φ F * φ G := fun F G => by
    show BHom.toLin (evalB K N dnScal s v ha ha (G ≫ F)) = _
    rw [evalB_comp dnScal s v ha ha ha]
    rfl
  have he : φ 1 = 1 := by
    show BHom.toLin (evalB K N dnScal s v ha ha (Finsupp.single (𝟙 a) 1)) = 1
    rw [evalB_single, one_smul]
    rfl
  have h := KLR.Diagram.ncEval_of_mul φ hmul he y (fun i => mulLin _ (z i))
    (fun i => by rw [mul_one]; exact congrArg BHom.toLin (hy i))
    (fun _ => Commute.one_right _) p
  rw [mul_one, ncEval_mulLin] at h
  exact BHom.toLin_injective h

/-- **`evalB` of a KLR polynomial in dots placed on upward strands** (`KLR.Diagram.lpoly`, the
form of the correction terms of the KLR relations). -/
theorem evalB_upLin_lpoly (dnScal : Fin m → Fin m → K) (μ : Wt m)
    {a : Obj (KLR.Diagram.sig (Fin m))} (s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups a.word)).word ++ v)) {n : ℕ} (y : Fin n → (a ⟶ a))
    (z : Fin n → (gammaR K N s _ ha).T)
    (hy : ∀ i, evalB K N dnScal s v ha ha (LinDiagram.of (upDiag RD μ (y i))) = BHom.mulB (z i))
    (p : MvPolynomial (Fin n) K) :
    evalB K N dnScal s v ha ha (upLin RD K μ (KLR.Diagram.lpoly K y p)) =
      BHom.mulB (MvPolynomial.eval₂ (gammaR K N s _ ha).right z p) := by
  let ψ : End (Free.of K a) →ₗ[K] Module.End K (RT (gammaR K N s _ ha)) :=
    BHom.toLinL ∘ₗ evalB K N dnScal s v ha ha ∘ₗ
      (Finsupp.lmapDomain K K (upDiag RD μ (a := a) (b := a)))
  have hmul : ∀ F G, ψ (F * G) = ψ F * ψ G := fun F G => by
    show BHom.toLin (evalB K N dnScal s v ha ha (upLin RD K μ (G ≫ F))) = _
    rw [upLin_comp, evalB_comp dnScal s v ha ha ha]
    rfl
  have he : ψ 1 = 1 := by
    show BHom.toLin (evalB K N dnScal s v ha ha (upLin RD K μ (Finsupp.single (𝟙 a) 1))) = 1
    rw [upLin, Finsupp.mapDomain_single, upDiag_id, evalB_single, one_smul]
    rfl
  have h := KLR.Diagram.ncEval_of_mul ψ hmul he (fun i => LinDiagram.of (y i)) (fun i => mulLin _ (z i))
    (fun i => by
      rw [mul_one]
      show BHom.toLin (evalB K N dnScal s v ha ha (upLin RD K μ (LinDiagram.of (y i)))) = _
      rw [upLin_of, hy]
      rfl)
    (fun _ => Commute.one_right _) p
  rw [mul_one, ncEval_mulLin] at h
  exact BHom.toLin_injective h

end Categorification.Flag

end
