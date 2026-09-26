/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLocal

/-!
# Two-strand generators at arbitrary positions of arbitrary paths

KL III, arXiv:0807.3250v1, §6.1.2 (Definition 6.2) defines `Γ_N` on the generating 2-morphisms;
a generator placed between the strands `u` (on the left) and `v` (on the right) of a 1-morphism
is sent to the corresponding map of the local bimodules tensored with identities. On the path
model of `Categorification.Flag.GammaWord` this is `twoAt φ s u v e`: the local two-strand map
`φ` (given for every left region `t`), whiskered on the right by `Γ(v)` (`locTwo`, through the
associator) and on the left by the strands `u` (`atPrefix`).

## Main results

* `twoAt`, with `twoAt_comp` (functoriality), `twoAt_zero`, `twoAt_sub`, `twoAt_add`,
  `twoAt_neg`: every relation among local two-strand maps holds at every position of every path.
* `eeVar`: the canonical second moved variable `⟨i+1, 1⟩` for the Borel model of `E_i E_i`.
* The two-strand relations of `U→(sl_n)` (KL III (4.11), (4.12)), at every position:
  - `crossEE_sq_at` (`ψ² = 0` on `E_i E_i`), `crossEE_slideR_at`, `crossEE_slideL_at`;
  - `crossFar_sq_at` (`ψ² = 1` for `i · j = 0`);
  - `crossAdj_sq_NF_at`, `crossAdj_sq_FN_at` (`ψ² = ±(x_left - x_right)` for `j = i + 1`).
-/

noncomputable section

namespace Categorification.Flag

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-! ### Two-strand maps at a position -/

section TwoAt

variable (K) in
/-- A family of two-strand bimodule maps `Γ(E_a E_b 1) → Γ(E_{a'} E_{b'} 1)`, for every left region
`t` and all validity proofs. -/
abbrev TwoFam (a b a' b' : SLetter m) (r₁ r₂ r₁' : Comp m) : Type u :=
  ∀ (t : Comp m) (h₁ : StepR a r₁ t) (h₂ : StepR b r₂ r₁) (h₁' : StepR a' r₁' t)
    (h₂' : StepR b' r₂ r₁'),
    BHom ((stepB K a r₁ t h₁).tensor (stepB K b r₂ r₁ h₂))
      ((stepB K a' r₁' t h₁').tensor (stepB K b' r₂ r₁' h₂'))

variable {a b a' b' a'' b'' : SLetter m} {r₁ r₂ r₁' r₁'' : Comp m}

/-- **A two-strand generator at the position after the strands `u`** of the path
`u ++ [(a, r₁), (b, r₂)] ++ v`, whiskered by the identities of all other strands. -/
def twoAt (φ : TwoFam K a b a' b' r₁ r₂ r₁') (s : Comp m) (u v : List (SLetter m × Comp m))
    (e : Comp m) (h : PValid s (u ++ (a, r₁) :: (b, r₂) :: v) e)
    (h' : PValid s (u ++ (a', r₁') :: (b', r₂) :: v) e) :
    BHom (gammaP K s (u ++ (a, r₁) :: (b, r₂) :: v) e h)
      (gammaP K s (u ++ (a', r₁') :: (b', r₂) :: v) e h') :=
  atPrefix (w := (a, r₁) :: (b, r₂) :: v) (w' := (a', r₁') :: (b', r₂) :: v)
    (fun t h h' => locTwo (φ t h.1 h.2.1 h'.1 h'.2.1) (gammaP K r₂ v e h.2.2)) s u h h'

/-- **Functoriality**: a relation `χ = ψ ∘ φ` among local maps holds at every position. -/
theorem twoAt_comp (φ : TwoFam K a b a' b' r₁ r₂ r₁') (ψ : TwoFam K a' b' a'' b'' r₁' r₂ r₁'')
    (χ : TwoFam K a b a'' b'' r₁ r₂ r₁'')
    (hχ : ∀ t h₁ h₂ h₁' h₂' h₁'' h₂'', χ t h₁ h₂ h₁'' h₂'' = (ψ t h₁' h₂' h₁'' h₂'').comp
      (φ t h₁ h₂ h₁' h₂')) (s : Comp m) (u v : List (SLetter m × Comp m)) (e : Comp m)
    (h : PValid s (u ++ (a, r₁) :: (b, r₂) :: v) e) (h' : PValid s (u ++ (a', r₁') :: (b', r₂) :: v) e)
    (h'' : PValid s (u ++ (a'', r₁'') :: (b'', r₂) :: v) e) :
    twoAt χ s u v e h h'' = (twoAt ψ s u v e h' h'').comp (twoAt φ s u v e h h') := by
  unfold twoAt
  refine atPrefix_comp _ _ _ (fun t h h' h'' => ?_) s u h h' h''
  rw [hχ t h.1 h.2.1 h'.1 h'.2.1 h''.1 h''.2.1, locTwo_comp]

theorem twoAt_congr (φ ψ : TwoFam K a b a' b' r₁ r₂ r₁')
    (hφψ : ∀ t h₁ h₂ h₁' h₂', φ t h₁ h₂ h₁' h₂' = ψ t h₁ h₂ h₁' h₂') (s : Comp m)
    (u v : List (SLetter m × Comp m)) (e : Comp m) (h : PValid s (u ++ (a, r₁) :: (b, r₂) :: v) e)
    (h' : PValid s (u ++ (a', r₁') :: (b', r₂) :: v) e) :
    twoAt φ s u v e h h' = twoAt ψ s u v e h h' := by
  unfold twoAt
  exact atPrefix_congr _ _ (fun t h h' => by rw [hφψ]) s u h h'

theorem twoAt_zero (s : Comp m) (u v : List (SLetter m × Comp m)) (e : Comp m)
    (h : PValid s (u ++ (a, r₁) :: (b, r₂) :: v) e) (h' : PValid s (u ++ (a', r₁') :: (b', r₂) :: v) e) :
    twoAt (fun _ _ _ _ _ => 0 : TwoFam K a b a' b' r₁ r₂ r₁') s u v e h h' = 0 := by
  unfold twoAt
  simp only [locTwo_zero]
  exact atPrefix_zero s u h h'

theorem twoAt_sub (φ ψ : TwoFam K a b a' b' r₁ r₂ r₁') (s : Comp m)
    (u v : List (SLetter m × Comp m)) (e : Comp m) (h : PValid s (u ++ (a, r₁) :: (b, r₂) :: v) e)
    (h' : PValid s (u ++ (a', r₁') :: (b', r₂) :: v) e) :
    twoAt (fun t h₁ h₂ h₁' h₂' => φ t h₁ h₂ h₁' h₂' - ψ t h₁ h₂ h₁' h₂') s u v e h h' =
      twoAt φ s u v e h h' - twoAt ψ s u v e h h' := by
  unfold twoAt
  simp only [locTwo_sub]
  exact atPrefix_sub _ _ s u h h'

theorem twoAt_add (φ ψ : TwoFam K a b a' b' r₁ r₂ r₁') (s : Comp m)
    (u v : List (SLetter m × Comp m)) (e : Comp m) (h : PValid s (u ++ (a, r₁) :: (b, r₂) :: v) e)
    (h' : PValid s (u ++ (a', r₁') :: (b', r₂) :: v) e) :
    twoAt (fun t h₁ h₂ h₁' h₂' => φ t h₁ h₂ h₁' h₂' + ψ t h₁ h₂ h₁' h₂') s u v e h h' =
      twoAt φ s u v e h h' + twoAt ψ s u v e h h' := by
  unfold twoAt
  simp only [locTwo_add]
  exact atPrefix_add _ _ s u h h'

theorem twoAt_id (s : Comp m) (u v : List (SLetter m × Comp m)) (e : Comp m)
    (h : PValid s (u ++ (a, r₁) :: (b, r₂) :: v) e) :
    twoAt (fun _ _ _ _ _ => BHom.id _ : TwoFam K a b a b r₁ r₂ r₁) s u v e h h = BHom.id _ := by
  unfold twoAt
  simp only [locTwo_id]
  exact atPrefix_id _ (fun _ _ => rfl) s u h

end TwoAt

/-! ### The canonical variables of the Borel models -/

section Vars

/-- The canonical second moved variable `⟨i+1, 1⟩` of the Borel model of `E_i E_i 1` (the first
moved variable is `⟨i+1, 0⟩`). -/
def eeVar (i : Fin m) {t r₁ r₂ : Comp m} (h₁ : StepR (true, i) r₁ t)
    (h₂ : StepR (true, i) r₂ r₁) : Gen r₂ :=
  ⟨i.succ, ⟨1, by
    have h1 := h₁.2
    have h2 := congrFun h₂.1 i.succ
    rw [raise_succ] at h2
    omega⟩⟩

theorem eeVar_hv (i : Fin m) {t r₁ r₂ : Comp m} (h₁ : StepR (true, i) r₁ t)
    (h₂ : StepR (true, i) r₂ r₁) : labJ i h₂ (eeVar i h₁ h₂) = i.succ := by
  have hne : eeVar i h₁ h₂ ≠ movedVar i r₂ h₂.2 := by
    intro h
    simp only [eeVar, movedVar, Sigma.mk.inj_iff, true_and] at h
    have := congrArg Fin.val (eq_of_heq h)
    simp at this
  rw [labJ, moveLab, Function.update_of_ne hne]
  rfl

end Vars

/-! ### The families of crossings -/

section Families

variable (K)

/-- The crossing of two strands coloured `i` as a family. -/
def crossEEFam (i : Fin m) (r₁ r₂ : Comp m) :
    TwoFam K (true, i) (true, i) (true, i) (true, i) r₁ r₂ r₁ :=
  fun _ h₁ h₂ _ _ => crossEEP K i h₁ h₂ (eeVar i h₁ h₂) (eeVar_hv i h₁ h₂)

/-- The crossing of two strands of distant colours as a family. -/
def crossFarFam (i j : Fin m) (hij : i ≠ j) (hf₁ : i.succ ≠ j.castSucc)
    (hf₂ : j.succ ≠ i.castSucc) (r₁ r₂ r₁' : Comp m) :
    TwoFam K (true, i) (true, j) (true, j) (true, i) r₁ r₂ r₁' :=
  fun _ h₁ h₂ h₁' h₂' => crossFarP K i j hij hf₁ hf₂ h₁ h₂ h₁' h₂'

/-- `crossAdjNF` as a family (`E_i E_{i+1} → E_{i+1} E_i`). -/
def crossAdjNFFam (i j : Fin m) (hadj : j.castSucc = i.succ) (r₁ r₂ r₁' : Comp m) :
    TwoFam K (true, i) (true, j) (true, j) (true, i) r₁ r₂ r₁' :=
  fun _ h₁ h₂ h₁' h₂' => crossAdjNF K i j hadj h₁ h₂ h₁' h₂'

/-- `crossAdjFN` as a family (`E_{i+1} E_i → E_i E_{i+1}`). -/
def crossAdjFNFam (i j : Fin m) (hadj : j.castSucc = i.succ) (r₁ r₂ r₁' : Comp m) :
    TwoFam K (true, j) (true, i) (true, i) (true, j) r₁' r₂ r₁ :=
  fun _ h₁' h₂' h₁ h₂ => crossAdjFN K i j hadj h₁ h₂ h₁' h₂'

/-- The dot on the left strand `E_i` of `E_i E_j`, as a family. -/
def dotLFam (i j : Fin m) (r₁ r₂ : Comp m) : TwoFam K (true, i) (true, j) (true, i) (true, j) r₁ r₂ r₁ :=
  fun t h₁ h₂ _ _ => BHom.mulB (BRing.tmul (stepB K (true, i) r₁ t h₁) (stepB K (true, j) r₂ r₁ h₂)
    (eXi K i r₁ h₁.2) 1)

/-- The dot on the right strand `E_j` of `E_i E_j`, as a family. -/
def dotRFam (i j : Fin m) (r₁ r₂ : Comp m) : TwoFam K (true, i) (true, j) (true, i) (true, j) r₁ r₂ r₁ :=
  fun t h₁ h₂ _ _ => BHom.mulB (BRing.tmul (stepB K (true, i) r₁ t h₁) (stepB K (true, j) r₂ r₁ h₂)
    1 (eXi K j r₂ h₂.2))

/-- Multiplication by a local element, as a family. -/
def mulFam {a b : SLetter m} (r₁ r₂ : Comp m)
    (x : ∀ t (h₁ : StepR a r₁ t) (h₂ : StepR b r₂ r₁),
      ((stepB K a r₁ t h₁).tensor (stepB K b r₂ r₁ h₂)).T) : TwoFam K a b a b r₁ r₂ r₁ :=
  fun t h₁ h₂ _ _ => BHom.mulB (x t h₁ h₂)

end Families

/-! ### The two-strand relations at every position -/

section Relations

variable (s : Comp m) (u v : List (SLetter m × Comp m)) (e : Comp m)

/-- **`ψ² = 0` on `E_i E_i`** (KL III Definition 3.1 / 4.1) at every position of every path. -/
theorem crossEE_sq_at (i : Fin m) {r₁ r₂ : Comp m}
    (h : PValid s (u ++ ((true, i), r₁) :: ((true, i), r₂) :: v) e) :
    (twoAt (crossEEFam K i r₁ r₂) s u v e h h).comp (twoAt (crossEEFam K i r₁ r₂) s u v e h h) = 0 := by
  rw [← twoAt_comp (crossEEFam K i r₁ r₂) (crossEEFam K i r₁ r₂) (fun _ _ _ _ _ => 0)
    (fun t h₁ h₂ _ _ _ _ => (crossEEP_sq i h₁ h₂ _ _).symm) s u v e h h h]
  exact twoAt_zero s u v e h h

/-- **`ψ_{ji} ψ_{ij} = 1` for distant colours** (KL III (4.11), `i · j = 0`) at every position. -/
theorem crossFar_sq_at (i j : Fin m) (hij : i ≠ j) (hf₁ : i.succ ≠ j.castSucc)
    (hf₂ : j.succ ≠ i.castSucc) {r₁ r₂ r₁' : Comp m}
    (h : PValid s (u ++ ((true, i), r₁) :: ((true, j), r₂) :: v) e)
    (h' : PValid s (u ++ ((true, j), r₁') :: ((true, i), r₂) :: v) e) :
    (twoAt (crossFarFam K j i hij.symm hf₂ hf₁ r₁' r₂ r₁) s u v e h' h).comp
      (twoAt (crossFarFam K i j hij hf₁ hf₂ r₁ r₂ r₁') s u v e h h') = BHom.id _ := by
  rw [← twoAt_comp (crossFarFam K i j hij hf₁ hf₂ r₁ r₂ r₁')
    (crossFarFam K j i hij.symm hf₂ hf₁ r₁' r₂ r₁) (fun _ _ _ _ _ => BHom.id _)
    (fun t h₁ h₂ h₁' h₂' _ _ => (crossFarP_sq i j hij hf₁ hf₂ h₁ h₂ h₁' h₂').symm) s u v e h h' h]
  exact twoAt_id s u v e h

/-- **KL III (4.11) for `j = i + 1` on `E_i E_{i+1}`** at every position:
`ψ_{i+1,i} ψ_{i,i+1} = x_right - x_left`. -/
theorem crossAdj_sq_NF_at (i j : Fin m) (hadj : j.castSucc = i.succ) {r₁ r₂ r₁' : Comp m}
    (h : PValid s (u ++ ((true, i), r₁) :: ((true, j), r₂) :: v) e)
    (h' : PValid s (u ++ ((true, j), r₁') :: ((true, i), r₂) :: v) e) :
    (twoAt (crossAdjFNFam K i j hadj r₁ r₂ r₁') s u v e h' h).comp
      (twoAt (crossAdjNFFam K i j hadj r₁ r₂ r₁') s u v e h h') =
      twoAt (dotRFam K i j r₁ r₂) s u v e h h - twoAt (dotLFam K i j r₁ r₂) s u v e h h := by
  rw [← twoAt_comp (crossAdjNFFam K i j hadj r₁ r₂ r₁') (crossAdjFNFam K i j hadj r₁ r₂ r₁')
    (fun t h₁ h₂ _ _ => BHom.mulB (BRing.tmul (stepB K (true, i) r₁ t h₁)
      (stepB K (true, j) r₂ r₁ h₂) 1 (eXi K j r₂ h₂.2) - BRing.tmul _ _ (eXi K i r₁ h₁.2) 1))
    (fun t h₁ h₂ h₁' h₂' _ _ => (crossAdj_sq_NF i j hadj h₁ h₂ h₁' h₂').symm) s u v e h h' h,
    ← twoAt_sub]
  exact twoAt_congr _ _ (fun t h₁ h₂ _ _ => BHom.mulB_sub _ _) s u v e h h

/-- **KL III (4.11) for `j = i + 1` on `E_{i+1} E_i`** at every position:
`ψ_{i,i+1} ψ_{i+1,i} = x_left - x_right`. -/
theorem crossAdj_sq_FN_at (i j : Fin m) (hadj : j.castSucc = i.succ) {r₁ r₂ r₁' : Comp m}
    (h : PValid s (u ++ ((true, i), r₁) :: ((true, j), r₂) :: v) e)
    (h' : PValid s (u ++ ((true, j), r₁') :: ((true, i), r₂) :: v) e) :
    (twoAt (crossAdjNFFam K i j hadj r₁ r₂ r₁') s u v e h h').comp
      (twoAt (crossAdjFNFam K i j hadj r₁ r₂ r₁') s u v e h' h) =
      twoAt (dotLFam K j i r₁' r₂) s u v e h' h' - twoAt (dotRFam K j i r₁' r₂) s u v e h' h' := by
  rw [← twoAt_comp (crossAdjFNFam K i j hadj r₁ r₂ r₁') (crossAdjNFFam K i j hadj r₁ r₂ r₁')
    (fun t h₁ h₂ _ _ => BHom.mulB (BRing.tmul (stepB K (true, j) r₁' t h₁)
      (stepB K (true, i) r₂ r₁' h₂) (eXi K j r₁' h₁.2) 1 - BRing.tmul _ _ 1 (eXi K i r₂ h₂.2)))
    (fun t h₁' h₂' h₁ h₂ _ _ => (crossAdj_sq_FN i j hadj h₁ h₂ h₁' h₂').symm) s u v e h' h h',
    ← twoAt_sub]
  exact twoAt_congr _ _ (fun t h₁ h₂ _ _ => BHom.mulB_sub _ _) s u v e h' h'

/-- **Dot slide** `ψ ∘ x_left = 1 + x_right ∘ ψ` on `E_i E_i` at every position. -/
theorem crossEE_slideR_at (i : Fin m) {r₁ r₂ : Comp m}
    (h : PValid s (u ++ ((true, i), r₁) :: ((true, i), r₂) :: v) e) :
    (twoAt (crossEEFam K i r₁ r₂) s u v e h h).comp
        (twoAt (dotLFam K i i r₁ r₂) s u v e h h) =
      BHom.id _ + (twoAt (dotRFam K i i r₁ r₂) s u v e h h).comp
        (twoAt (crossEEFam K i r₁ r₂) s u v e h h) := by
  rw [← twoAt_comp (dotLFam K i i r₁ r₂) (crossEEFam K i r₁ r₂)
      (fun t h₁ h₂ _ _ => (crossEEFam K i r₁ r₂ t h₁ h₂ h₁ h₂).comp (dotLFam K i i r₁ r₂ t h₁ h₂ h₁ h₂))
      (fun _ _ _ _ _ _ _ => rfl) s u v e h h h,
    ← twoAt_comp (crossEEFam K i r₁ r₂) (dotRFam K i i r₁ r₂)
      (fun t h₁ h₂ _ _ => (dotRFam K i i r₁ r₂ t h₁ h₂ h₁ h₂).comp (crossEEFam K i r₁ r₂ t h₁ h₂ h₁ h₂))
      (fun _ _ _ _ _ _ _ => rfl) s u v e h h h,
    ← twoAt_id s u v e h, ← twoAt_add]
  exact twoAt_congr _ _ (fun t h₁ h₂ _ _ => crossEEP_xiL i h₁ h₂ _ _) s u v e h h

/-- **Dot slide** `ψ ∘ x_right = x_left ∘ ψ - 1` on `E_i E_i` at every position. -/
theorem crossEE_slideL_at (i : Fin m) {r₁ r₂ : Comp m}
    (h : PValid s (u ++ ((true, i), r₁) :: ((true, i), r₂) :: v) e) :
    (twoAt (crossEEFam K i r₁ r₂) s u v e h h).comp
        (twoAt (dotRFam K i i r₁ r₂) s u v e h h) =
      (twoAt (dotLFam K i i r₁ r₂) s u v e h h).comp
        (twoAt (crossEEFam K i r₁ r₂) s u v e h h) - BHom.id _ := by
  rw [← twoAt_comp (dotRFam K i i r₁ r₂) (crossEEFam K i r₁ r₂)
      (fun t h₁ h₂ _ _ => (crossEEFam K i r₁ r₂ t h₁ h₂ h₁ h₂).comp (dotRFam K i i r₁ r₂ t h₁ h₂ h₁ h₂))
      (fun _ _ _ _ _ _ _ => rfl) s u v e h h h,
    ← twoAt_comp (crossEEFam K i r₁ r₂) (dotLFam K i i r₁ r₂)
      (fun t h₁ h₂ _ _ => (dotLFam K i i r₁ r₂ t h₁ h₂ h₁ h₂).comp (crossEEFam K i r₁ r₂ t h₁ h₂ h₁ h₂))
      (fun _ _ _ _ _ _ _ => rfl) s u v e h h h,
    ← twoAt_id s u v e h, ← twoAt_sub]
  exact twoAt_congr _ _ (fun t h₁ h₂ _ _ => crossEEP_xiR i h₁ h₂ _ _) s u v e h h

end Relations

end Categorification.Flag

end
