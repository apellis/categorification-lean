/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.BimodRing
import Categorification.Flag.Bimodule

/-!
# The 1-morphisms of `Flag_N`: iterated tensor products of `H_{k^{±i}}` (KL III Def. 5.6)

Khovanov–Lauda III, arXiv:0807.3250v1, §5.3, Definition 5.6 (TeX `sln-2008-ArXiv.tex`,
subsection "The 2-category `Flag_N`"), and §6.1, eq. (6.1) (label `eq_Es`): the image of
`E_{\mathbf i} 1_λ = E_{s_1} ⋯ E_{s_m} 1_λ` under `Γ_N` is

  `H_{s_2 ⋯ s_m k^{s_1}} ⊗_{H_{s_2 ⋯ s_m k}} ⋯ ⊗_{H_{s_m k}} H_{k^{s_m}}`.

## Conventions

* A composition (block sizes `d_j = k_{j+1} - k_j`) is `d : Comp m = Fin (m + 1) → ℕ`; its ring
  is `H K d` (KL III (5.2)). `E_i` moves one unit from block `i.succ` to block `i.castSucc`
  (`Flag.raise`).
* A signed letter is `l : SLetter m = Bool × Fin m` (`true` for `E_i`, `false` for `F_i`), as for
  the 2-category `U` (`Categorification.KL3.Diagram.Letter`).
* A 1-morphism is given by a **path**: a start composition `s` (the leftmost region), a list of
  pairs `(l, r)` (a letter and the composition of the region to its **right**, read from left to
  right as the words of the string-diagram presentation of `U`), and an end composition `e`
  (the rightmost region). Storing the intermediate compositions (instead of computing them)
  mirrors the objects of the presentation (`Obj`: colours carry their right regions) and makes
  whiskering by identities definitional: a generator changes only the compositions *inside* it.

The step condition `StepR l r s` for a letter `l` from the right region `r` to the left region
`s` is `raise i r = s ∧ 0 < r_{i+1}` for `E_i` and `raise i s = r ∧ 0 < s_{i+1}` for `F_i`. The
step bimodule `stepB K l r s h : BRing (H K s) (H K r)` is (KL III §5.1.1, Definition 5.6)

* for `E_i`: `H_{r^{+i}} = ERing K i r` with `H_s` acting by `p_2^*` (`eLeft`, transported along
  `hCast : H_s ≅ H_{+_i r}`) and `H_r` by `p_1^*` (`eRight`);
* for `F_i`: the *same* ring `H_{s^{+i}} = ERing K i s` with the actions exchanged.

With this convention the rings of `F_i E_i 1_k` and `E_i F_i 1_k` are literally the rings
`H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}` and `H_{k'^{+i}} ⊗_{H_{k'}} H_{k'^{+i}}` of
`Categorification.Flag.Cups` and `Categorification.Flag.CupsMirror` (up to the identification of
the middle rings).

## Main definitions

* `hCast`, `StepR`, `stepB`, `xiStep` (the dot `ξ_i` of a strand, KL III (6.6), (6.7)).
* `PValid s p e`, `gammaP K s p e h : BRing (H K s) (H K e)`: **the 1-morphism `Γ(E_p 1)`**.
* `atPrefix`: whiskering a family of local bimodule maps by the strands to the left
  (`atPrefix_comp`, `atPrefix_add`, `atPrefix_sub`, `atPrefix_neg`, `atPrefix_id`).
* `locTwo`: a bimodule map between two-step tensor products, whiskered by the strands to the
  right (through the associator); `locOne`: the same for one-step bimodules; both functorial.
* `dotP`: `Γ` of a dot on any strand of any path (KL III (6.6), (6.7)).
-/

noncomputable section

namespace Categorification.Flag

universe u

variable (K : Type u) [Field K] {m : ℕ}

/-- A composition of `N` into `m + 1` parts (block sizes). -/
abbrev Comp (m : ℕ) : Type := Fin (m + 1) → ℕ

/-- A signed letter: `(true, i)` is `E_i`, `(false, i)` is `F_i`. -/
abbrev SLetter (m : ℕ) : Type := Bool × Fin m

/-- The ring isomorphism `H_d ≅ H_{d'}` for equal compositions. -/
def hCast {n : ℕ} {d d' : Fin n → ℕ} (h : d = d') : H K d ≃ₐ[K] H K d' := h ▸ AlgEquiv.refl

variable {K}

@[simp] theorem hCast_rfl {n : ℕ} (d : Fin n → ℕ) (z : H K d) : hCast K (rfl : d = d) z = z := rfl

@[simp] theorem hCast_x {n : ℕ} {d d' : Fin n → ℕ} (h : d = d') (j : Fin n) (α : ℕ) :
    hCast K h (x K d j α) = x K d' j α := by
  subst h; rfl

@[simp] theorem hCast_xbar {n : ℕ} {d d' : Fin n → ℕ} (h : d = d') (j : Fin n) (α : ℕ) :
    hCast K h (xbar K d j α) = xbar K d' j α := by
  subst h; rfl

theorem hCast_symm_apply {n : ℕ} {d d' : Fin n → ℕ} (h : d = d') (z : H K d') :
    (hCast K h).symm z = hCast K h.symm z := by
  subst h; rfl

theorem hCast_trans_apply {n : ℕ} {d d' d'' : Fin n → ℕ} (h : d = d') (h' : d' = d'')
    (z : H K d) : hCast K h' (hCast K h z) = hCast K (h.trans h') z := by
  subst h h'; rfl

/-! ### Steps -/

/-- **The step condition**: the letter `l` goes from the region `r` (on its right) to the region
`s` (on its left). For `E_i`: `s = +_i r` and `r_{i+1} > 0`; for `F_i`: `r = +_i s` and
`s_{i+1} > 0`. -/
def StepR : SLetter m → Comp m → Comp m → Prop
  | (true, i), r, s => raise i r = s ∧ 0 < r i.succ
  | (false, i), r, s => raise i s = r ∧ 0 < s i.succ

variable (K)

/-- **The bimodule of one strand** (KL III Definition 5.6): for `E_i` the
`(H_{+_i r}, H_r)`-bimodule `H_{r^{+i}}`, for `F_i` the `(H_s, H_{+_i s})`-bimodule `H_{s^{+i}}`. -/
def stepB : (l : SLetter m) → (r s : Comp m) → StepR l r s → BRing (H K s) (H K r)
  | (true, i), r, _, h =>
    ⟨ERing K i r h.2, (eLeft K i r h.2).toRingHom.comp (hCast K h.1.symm).toRingHom,
      (eRight K i r h.2).toRingHom⟩
  | (false, i), _, s, h =>
    ⟨ERing K i s h.2, (eRight K i s h.2).toRingHom,
      (eLeft K i s h.2).toRingHom.comp (hCast K h.1.symm).toRingHom⟩

/-- **The dot** `ξ_i` of a strand (KL III (6.6), (6.7): `Γ` of a dot is multiplication by `ξ_i`). -/
def xiStep : (l : SLetter m) → (r s : Comp m) → (h : StepR l r s) → (stepB K l r s h).T
  | (true, i), r, _, h => eXi K i r h.2
  | (false, i), _, s, h => eXi K i s h.2

/-! ### Paths and the 1-morphisms `Γ(E_p 1)` -/

variable {K}

/-- A path from the start region `s` (leftmost) through the strands `p` (letters with the regions
on their right) to the end region `e` (rightmost). -/
def PValid : Comp m → List (SLetter m × Comp m) → Comp m → Prop
  | s, [], e => s = e
  | s, x :: p, e => StepR x.1 x.2 s ∧ PValid x.2 p e

variable (K)

/-- **The 1-morphism `Γ(E_p 1)`** (KL III Definition 5.6, (6.1)): the iterated tensor product of
the step bimodules, a `(H_s, H_e)`-bimodule. -/
def gammaP : (s : Comp m) → (p : List (SLetter m × Comp m)) → (e : Comp m) → PValid s p e →
    BRing (H K s) (H K e)
  | s, [], _, h => ⟨H K s, RingHom.id _, (hCast K h).symm.toRingHom⟩
  | s, x :: p, e, h => (stepB K x.1 x.2 s h.1).tensor (gammaP x.2 p e h.2)

theorem gammaP_cons (s : Comp m) (x : SLetter m × Comp m) (p : List (SLetter m × Comp m))
    (e : Comp m) (h : PValid s (x :: p) e) :
    gammaP K s (x :: p) e h = (stepB K x.1 x.2 s h.1).tensor (gammaP K x.2 p e h.2) := rfl

/-! ### Whiskering by strands on the left -/

variable {K}

/-- **Whiskering by the strands `u` on the left**: a family of bimodule maps between the
1-morphisms of the paths `w`, `w'` (for every start region `t`) induces a bimodule map between the
1-morphisms of `u ++ w` and `u ++ w'`. -/
def atPrefix {w w' : List (SLetter m × Comp m)} {e : Comp m}
    (φ : ∀ t (h : PValid t w e) (h' : PValid t w' e), BHom (gammaP K t w e h) (gammaP K t w' e h')) :
    (s : Comp m) → (u : List (SLetter m × Comp m)) → (h : PValid s (u ++ w) e) →
      (h' : PValid s (u ++ w') e) → BHom (gammaP K s (u ++ w) e h) (gammaP K s (u ++ w') e h')
  | s, [], h, h' => φ s h h'
  | s, y :: u, h, h' => BHom.whiskerLeft (stepB K y.1 y.2 s h.1) (atPrefix φ y.2 u h.2 h'.2)

theorem atPrefix_nil {w w' : List (SLetter m × Comp m)} {e : Comp m}
    (φ : ∀ t (h : PValid t w e) (h' : PValid t w' e), BHom (gammaP K t w e h) (gammaP K t w' e h'))
    (s : Comp m) (h : PValid s ([] ++ w) e) (h' : PValid s ([] ++ w') e) :
    atPrefix φ s [] h h' = φ s h h' := rfl

theorem atPrefix_comp {w w' w'' : List (SLetter m × Comp m)} {e : Comp m}
    (φ : ∀ t (h : PValid t w e) (h' : PValid t w' e), BHom (gammaP K t w e h) (gammaP K t w' e h'))
    (ψ : ∀ t (h : PValid t w' e) (h' : PValid t w'' e),
      BHom (gammaP K t w' e h) (gammaP K t w'' e h'))
    (χ : ∀ t (h : PValid t w e) (h' : PValid t w'' e), BHom (gammaP K t w e h) (gammaP K t w'' e h'))
    (hχ : ∀ t h h' h'', χ t h h'' = (ψ t h' h'').comp (φ t h h')) :
    ∀ (s : Comp m) (u : List (SLetter m × Comp m)) (h : PValid s (u ++ w) e)
      (h' : PValid s (u ++ w') e) (h'' : PValid s (u ++ w'') e),
      atPrefix χ s u h h'' = (atPrefix ψ s u h' h'').comp (atPrefix φ s u h h')
  | s, [], h, h', h'' => hχ s h h' h''
  | s, y :: u, h, h', h'' => by
    simp only [atPrefix]
    rw [atPrefix_comp φ ψ χ hχ y.2 u h.2 h'.2 h''.2, BHom.whiskerLeft_comp]

theorem atPrefix_congr {w w' : List (SLetter m × Comp m)} {e : Comp m}
    (φ ψ : ∀ t (h : PValid t w e) (h' : PValid t w' e),
      BHom (gammaP K t w e h) (gammaP K t w' e h'))
    (hφψ : ∀ t h h', φ t h h' = ψ t h h') :
    ∀ (s : Comp m) (u : List (SLetter m × Comp m)) (h : PValid s (u ++ w) e)
      (h' : PValid s (u ++ w') e), atPrefix φ s u h h' = atPrefix ψ s u h h'
  | s, [], h, h' => hφψ s h h'
  | s, y :: u, h, h' => by
    simp only [atPrefix]
    rw [atPrefix_congr φ ψ hφψ y.2 u h.2 h'.2]

theorem atPrefix_id {w : List (SLetter m × Comp m)} {e : Comp m}
    (φ : ∀ t (h : PValid t w e) (h' : PValid t w e), BHom (gammaP K t w e h) (gammaP K t w e h'))
    (hφ : ∀ t h, φ t h h = BHom.id _) :
    ∀ (s : Comp m) (u : List (SLetter m × Comp m)) (h : PValid s (u ++ w) e),
      atPrefix φ s u h h = BHom.id _
  | s, [], h => hφ s h
  | s, y :: u, h => by
    simp only [atPrefix]
    rw [atPrefix_id φ hφ y.2 u h.2]
    exact BHom.whiskerLeft_id _ _

theorem atPrefix_add {w w' : List (SLetter m × Comp m)} {e : Comp m}
    (φ ψ : ∀ t (h : PValid t w e) (h' : PValid t w' e),
      BHom (gammaP K t w e h) (gammaP K t w' e h')) :
    ∀ (s : Comp m) (u : List (SLetter m × Comp m)) (h : PValid s (u ++ w) e)
      (h' : PValid s (u ++ w') e),
      atPrefix (fun t h h' => φ t h h' + ψ t h h') s u h h' = atPrefix φ s u h h' + atPrefix ψ s u h h'
  | s, [], h, h' => rfl
  | s, y :: u, h, h' => by
    simp only [atPrefix]
    rw [atPrefix_add φ ψ y.2 u h.2 h'.2, BHom.whiskerLeft_add]

theorem atPrefix_sub {w w' : List (SLetter m × Comp m)} {e : Comp m}
    (φ ψ : ∀ t (h : PValid t w e) (h' : PValid t w' e),
      BHom (gammaP K t w e h) (gammaP K t w' e h')) :
    ∀ (s : Comp m) (u : List (SLetter m × Comp m)) (h : PValid s (u ++ w) e)
      (h' : PValid s (u ++ w') e),
      atPrefix (fun t h h' => φ t h h' - ψ t h h') s u h h' = atPrefix φ s u h h' - atPrefix ψ s u h h'
  | s, [], h, h' => rfl
  | s, y :: u, h, h' => by
    simp only [atPrefix]
    rw [atPrefix_sub φ ψ y.2 u h.2 h'.2, BHom.whiskerLeft_sub]

theorem atPrefix_neg {w w' : List (SLetter m × Comp m)} {e : Comp m}
    (φ : ∀ t (h : PValid t w e) (h' : PValid t w' e), BHom (gammaP K t w e h) (gammaP K t w' e h')) :
    ∀ (s : Comp m) (u : List (SLetter m × Comp m)) (h : PValid s (u ++ w) e)
      (h' : PValid s (u ++ w') e),
      atPrefix (fun t h h' => -φ t h h') s u h h' = -atPrefix φ s u h h'
  | s, [], h, h' => rfl
  | s, y :: u, h, h' => by
    simp only [atPrefix]
    rw [atPrefix_neg φ y.2 u h.2 h'.2, BHom.whiskerLeft_neg]

theorem atPrefix_zero {w w' : List (SLetter m × Comp m)} {e : Comp m} :
    ∀ (s : Comp m) (u : List (SLetter m × Comp m)) (h : PValid s (u ++ w) e)
      (h' : PValid s (u ++ w') e),
      atPrefix (K := K) (fun t (_ : PValid t w e) (_ : PValid t w' e) => 0) s u h h' = 0
  | s, [], h, h' => rfl
  | s, y :: u, h, h' => by
    simp only [atPrefix]
    rw [atPrefix_zero y.2 u h.2 h'.2]
    exact BHom.whiskerLeft_zero _

/-! ### Local maps whiskered on the right -/

section Local

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- A bimodule map `L ⊗ L' → R ⊗ R'` between two-step tensor products, whiskered by `X` on the
right: `L ⊗ (L' ⊗ X) → R ⊗ (R' ⊗ X)` (through the associators). -/
def locTwo {D : Type u} [CommRing D] {L : BRing A B} {L' : BRing B C} {R : BRing A D}
    {R' : BRing D C} (φ : BHom (L.tensor L') (R.tensor R')) {E : Type u} [CommRing E]
    (X : BRing C E) : BHom (L.tensor (L'.tensor X)) (R.tensor (R'.tensor X)) :=
  (BRing.assoc R R' X).hom.comp ((BHom.whiskerRight φ X).comp (BRing.assoc L L' X).inv)

theorem locTwo_comp {D D' : Type u} [CommRing D] [CommRing D'] {L : BRing A B} {L' : BRing B C}
    {R : BRing A D} {R' : BRing D C} {Q : BRing A D'} {Q' : BRing D' C}
    (φ : BHom (L.tensor L') (R.tensor R')) (ψ : BHom (R.tensor R') (Q.tensor Q')) {E : Type u}
    [CommRing E] (X : BRing C E) :
    locTwo (ψ.comp φ) X = (locTwo ψ X).comp (locTwo φ X) := by
  ext t
  simp only [locTwo, BHom.comp_apply, BHom.whiskerRight_comp, (BRing.assoc R R' X).inv_hom]

theorem locTwo_add {D : Type u} [CommRing D] {L : BRing A B} {L' : BRing B C} {R : BRing A D}
    {R' : BRing D C} (φ ψ : BHom (L.tensor L') (R.tensor R')) {E : Type u} [CommRing E]
    (X : BRing C E) : locTwo (φ + ψ) X = locTwo φ X + locTwo ψ X := by
  ext t
  simp only [locTwo, BHom.comp_apply, BHom.whiskerRight_add, BHom.add_apply]
  exact BHom.map_add _ _ _

theorem locTwo_sub {D : Type u} [CommRing D] {L : BRing A B} {L' : BRing B C} {R : BRing A D}
    {R' : BRing D C} (φ ψ : BHom (L.tensor L') (R.tensor R')) {E : Type u} [CommRing E]
    (X : BRing C E) : locTwo (φ - ψ) X = locTwo φ X - locTwo ψ X := by
  ext t
  simp only [locTwo, BHom.comp_apply, BHom.whiskerRight_sub, BHom.sub_apply]
  exact BHom.map_sub _ _ _

theorem locTwo_neg {D : Type u} [CommRing D] {L : BRing A B} {L' : BRing B C} {R : BRing A D}
    {R' : BRing D C} (φ : BHom (L.tensor L') (R.tensor R')) {E : Type u} [CommRing E]
    (X : BRing C E) : locTwo (-φ) X = -locTwo φ X := by
  ext t
  simp only [locTwo, BHom.comp_apply, BHom.whiskerRight_neg, BHom.neg_apply]
  exact BHom.map_neg _ _

theorem locTwo_zero {D : Type u} [CommRing D] {L : BRing A B} {L' : BRing B C} {R : BRing A D}
    {R' : BRing D C} {E : Type u} [CommRing E] (X : BRing C E) :
    locTwo (0 : BHom (L.tensor L') (R.tensor R')) X = 0 := by
  ext t
  simp only [locTwo, BHom.comp_apply, BHom.whiskerRight_zero, BHom.zero_apply]
  exact BHom.map_zero _

theorem locTwo_id {L : BRing A B} {L' : BRing B C} {E : Type u} [CommRing E] (X : BRing C E) :
    locTwo (BHom.id (L.tensor L')) X = BHom.id _ := by
  ext t
  simp only [locTwo, BHom.comp_apply, BHom.whiskerRight_id, BHom.id_apply,
    (BRing.assoc L L' X).hom_inv]

/-- Multiplication by `a ⊗ b` on `L ⊗ L'`, whiskered, is multiplication by `a ⊗ (b ⊗ 1)`. -/
theorem locTwo_mulB {L : BRing A B} {L' : BRing B C} (a : L.T) (b : L'.T) {E : Type u}
    [CommRing E] (X : BRing C E) :
    locTwo (BHom.mulB (BRing.tmul L L' a b)) X =
      BHom.mulB (BRing.tmul L (L'.tensor X) a (BRing.tmul L' X b 1)) := by
  refine BHom.ext fun t => ?_
  obtain ⟨t', rfl⟩ : ∃ t', (BRing.assoc L L' X).hom t' = t := ⟨_, (BRing.assoc L L' X).hom_inv t⟩
  simp only [locTwo, BHom.comp_apply, BHom.whiskerRight_mulB, BHom.mulB_apply,
    (BRing.assoc L L' X).inv_hom]
  refine BRing.induction_on (P := fun t' => (BRing.assoc L L' X).hom
      (BRing.tmul (L.tensor L') X (BRing.tmul L L' a b) 1 * t') =
      BRing.tmul L (L'.tensor X) a (BRing.tmul L' X b 1) * (BRing.assoc L L' X).hom t') t'
    (by simp) (fun y z => ?_) (fun y z hy hz => ?_)
  · refine BRing.induction_on (P := fun y => (BRing.assoc L L' X).hom
      (BRing.tmul (L.tensor L') X (BRing.tmul L L' a b) 1 * BRing.tmul (L.tensor L') X y z) =
      BRing.tmul L (L'.tensor X) a (BRing.tmul L' X b 1) *
        (BRing.assoc L L' X).hom (BRing.tmul (L.tensor L') X y z)) y
      (by simp) (fun p q => ?_) (fun y y' hy hy' => ?_)
    · beta_reduce
      rw [BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul]
      erw [BRing.assoc_hom_tmul, BRing.assoc_hom_tmul]
      rw [BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul]
    · beta_reduce at hy hy' ⊢
      rw [BRing.add_tmul, mul_add, BHom.map_add, hy, hy', BHom.map_add, mul_add]
  · beta_reduce at hy hz ⊢
    rw [mul_add, BHom.map_add, hy, hz, BHom.map_add, mul_add]

/-- A bimodule map `L → R` of one-step bimodules, whiskered by `X` on the right. -/
def locOne {L R : BRing A B} (φ : BHom L R) (X : BRing B C) : BHom (L.tensor X) (R.tensor X) :=
  BHom.whiskerRight φ X

end Local

/-! ### Dots -/

variable (K)

/-- The dot on the first strand of a path, as a local family. -/
def dotLoc (x : SLetter m × Comp m) (v : List (SLetter m × Comp m)) (e : Comp m) (t : Comp m)
    (h : PValid t (x :: v) e) (h' : PValid t (x :: v) e) :
    BHom (gammaP K t (x :: v) e h) (gammaP K t (x :: v) e h') :=
  locOne (BHom.mulB (xiStep K x.1 x.2 t h.1)) (gammaP K x.2 v e h.2)

/-- **`Γ` of a dot** (KL III (6.6), (6.7)) on the strand `x` of the path `u ++ x :: v`:
multiplication by `ξ` on the tensor factor of `x`. -/
def dotP (s : Comp m) (u : List (SLetter m × Comp m)) (x : SLetter m × Comp m)
    (v : List (SLetter m × Comp m)) (e : Comp m) (h : PValid s (u ++ x :: v) e) :
    BHom (gammaP K s (u ++ x :: v) e h) (gammaP K s (u ++ x :: v) e h) :=
  atPrefix (dotLoc K x v e) s u h h

end Categorification.Flag

end
