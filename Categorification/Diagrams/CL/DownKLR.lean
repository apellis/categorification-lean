/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.Rotate
import Categorification.Diagrams.CL.Rescale
import Categorification.KLR.Symmetries

/-!
# The KLR relations for `Q'` on downward strands follow from `Q`-cyclicity

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3: Definition 1.1 (2) (TeX label `defU_cat`, pp. 2–3) requires that "the `F`'s
carry an action of the KLR algebra associated to `Q'`", with the dual scalars `Q'` of §2.1.1
(`sec:datum`, p. 5, last display): `r'_i = -r_i`, `t'_{ij} = t_{ji}^{-1}`,
`s'^{pq}_{ij} = t_{ij}^{-1} t_{ji}^{-1} s^{pq}_{ij}` (`CLScalars.dual`). The sentence after
`eq_almost_cyclic` (§2.2, `sec:cycbiadjoint`, p. 6) says that this is ensured by `Q`-cyclicity.
`presCL` (`Categorification.Diagrams.CL.Presentation`) imposes only the upward KLR relations;
`presCLDown` adds the downward ones (`relationDown`). Here we prove CL's claim.

## Method

The rotation by `180°` (`rotC`, the mate for nested cups and caps,
`Categorification.Diagrams.CL.Rotate`) is well defined on `U_Q(g)` without any cyclicity. By
dot cyclicity (`eq_cyclic_dot`) the rotated upward dot is the downward dot
(`presCL_rotDotR`), and by `Q`-cyclicity (`eq_almost_cyclic`) the rotated upward crossing
`E_j E_i ⟶ E_i E_j` is `t_{ij}` times the downward crossing (`presCL_rotCrossR`). Hence the
rotation of a KLR diagram `D` on upward strands is the rotated KLR diagram `rotKD D` (layers
reversed, strands reversed, generators unchanged) on downward strands, times the product of
`t_{dc}` over its crossings `c d ⟶ d c` (`rotC_upLin`). Rotating the upward relations of `R_Q`
therefore gives zero (`lin_dnLin_rotKLin`), and each downward relation for `Q'` is a unit multiple
of a rotated upward relation (`relDown_*`):

* `ψ² = 0` on `F_c F_c`: the rotation of `ψ² = 0` on `E_c E_c` (`t_{cc} = 1`);
* `ψ² = Q'_{cd}(x₀, x₁)` on `F_c F_d`: `t_{cd} t_{dc}` times it is the rotation of
  `ψ² = Q_{dc}(x₀, x₁)` on `E_d E_c`, using `Q_{dc}(v, u) = Q_{cd}(u, v)` (`rename_swap_qCL`) and
  `Q'_{cd} = (t_{cd} t_{dc})^{-1} Q_{cd}` (`qCL_dual`);
* the nilHecke dot slides on `F_c F_c`: `-1` times them are the rotations of the upward ones (the
  two slides `ψ x₀ - x₁ ψ` and `x₀ ψ - ψ x₁` are each mapped to minus themselves), whence
  `r'_c = -r_c`;
* the dot slides on `F_c F_d`, `c ≠ d`: `-t_{dc}` times them are the rotations of the upward
  ones;
* the braid relations on `F_c F_d F_e`: `-t_{dc} t_{ec} t_{ed}` times them are the rotations of
  the upward ones (the rotation exchanges `ψ₀ψ₁ψ₀` and `ψ₁ψ₀ψ₁`); on `F_c F_d F_c`, `c ≠ d`,
  `-t_{cd} t_{dc}` times the relation `ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁ = r'_c Q̄'_{cd}` is the rotation of the
  upward one, since the correction term `r_c Q̄_{cd}` is symmetric in `x₀`, `x₂`
  (`KLR.qbar_rename_rev`) and `-(t_{cd} t_{dc})^{-1} r_c Q̄_{cd} = r'_c Q̄'_{cd}`.

So the scalars coming out are exactly CL's `Q'`: there is no discrepancy with CL's printed
formulas. (Only the products `t_{cd} t_{dc}` enter, so the downward relations do not distinguish
`t_{ij}` from `t_{ji}`.)

## Main results

* `lin_relationDown`: **every added relation of `presCLDown` is zero in `presCL`**;
* `presCLDownEquiv : (presCL RD k S).Presented ≌ (presCLDown RD k S).Presented`, the identity on
  diagrams (`presCLDownEquiv_functor_diag`, `presCLDownEquiv_inverse_diag`), an isomorphism of
  categories (`presCLDownEquiv_functor_comp_inverse`, `presCLDownEquiv_inverse_comp_functor`)
  compatible with whiskering (`presCLDownEquiv_functor_whisk`);
* `presCL_lin_eq_zero_iff`: a linear combination of diagrams vanishes in `presCL` iff it
  vanishes in `presCLDown`.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation MvPolynomial KLR.Diagram

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k] (S : CLScalars C k)

/-! ## Rotation of polynomials in dots -/

section Poly

variable {k}

/-- The rotation of a polynomial in endomorphisms: the reversed polynomial in the rotated
reversed variables. -/
theorem rotKLin_lpoly (τ : I → I → k) {w : Obj (KLR.Diagram.sig I)} {n : ℕ} (y : Fin n → (w ⟶ w))
    (p : MvPolynomial (Fin n) k) :
    rotKLin τ (lpoly k y p) =
      KLR.ncEval (A := End (Free.of k (kobjR w)))
        (fun a => rotKLin τ (LinDiagram.of (y (Fin.rev a)))) (rename Fin.rev p) :=
  ncEval_antihom (A := End (Free.of k w)) (B := End (Free.of k (kobjR w))) (rotKLin τ)
    (rotKLin_id τ w) (fun x y => rotKLin_comp τ y x) _ p

theorem fin2_rev : (Fin.rev : Fin 2 → Fin 2) = ![1, 0] := by
  funext a; fin_cases a <;> rfl

theorem fin3_rev : (Fin.rev : Fin 3 → Fin 3) = ![2, 1, 0] := by
  funext a; fin_cases a <;> rfl

end Poly

/-! ## `Q`-cyclicity in `U_Q(g)` -/

/-- The scalars of the rotated upward crossings in `U_Q(g)`: the rotation of `E_j E_i ⟶ E_i E_j`
is `t_{ij}` times the downward crossing (`eq_almost_cyclic`). -/
abbrev tauCL : I → I → k := fun j i => (S.t i j : k)

/-- Dot cyclicity (CL `eq_cyclic_dot`): the rotated upward dot is the downward dot. -/
theorem presCL_rotDotR (i : I) (μ : X) :
    (presCL RD k S).diag (rotDotR RD i μ) = (presCL RD k S).diag (downDot RD i μ) :=
  (presCL RD k S).diag_eq_of_rel (.inr (.cycDotR i μ)) rfl

/-- `Q`-cyclicity (CL `eq_almost_cyclic`): the upward crossing `E_j E_i ⟶ E_i E_j` rotated by
nested cups on the right and caps on the left is `t_{ij}` times the downward crossing. -/
theorem presCL_rotCrossR (j i : I) (μ : X) :
    (presCL RD k S).diag (rotCrossR RD j i μ) =
      tauCL k S j i • (presCL RD k S).diag (downCross RD j i μ) := by
  have h := (presCL RD k S).lin_rel_self (.inr (.cycCrossR j i μ))
  change (presCL RD k S).lin ((((S.t i j)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossR RD j i μ) -
    LinDiagram.of (downCross RD j i μ)) = 0 at h
  rw [lin_sub, lin_smul, lin_of, lin_of, sub_eq_zero] at h
  rw [← h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

/-- **The rotated upward KLR relations vanish in `U_Q(g)`**: for every KLR relation `r` and every
weight `ν`, the rotation `rotKLin` of the relation `relationR k (qCL S) r` of `R_Q`, placed on
downward strands with rightmost region `ν`, is zero. -/
theorem lin_dnLin_rotKLin (r : KLR.Diagram.Rel I) (ν : X) :
    (presCL RD k S).lin (dnLin RD k ν (rotKLin (tauCL k S)
      (relationR k (qCL S) (fun c => (S.r c : k)) r))) = 0 := by
  have hs : wt RD (ν - wsum RD (KLR.Diagram.Rel.dom r).word)
      (ups (KLR.Diagram.Rel.dom r).word) = ν := by
    rw [wt_ups]; abel
  have ht : wt RD (ν - wsum RD (KLR.Diagram.Rel.dom r).word)
      (ups (KLR.Diagram.Rel.cod r).word) = ν := by
    rw [wt_ups, wsum_relation_cod]; abel
  rw [← rotC_upLin (hz := zigzags RD k S) (tauCL k S) (presCL_rotDotR RD k S)
    (presCL_rotCrossR RD k S) _ ν _ hs ht,
    show (presCL RD k S).lin (upLin RD k (ν - wsum RD (KLR.Diagram.Rel.dom r).word)
      (relationR k (qCL S) (fun c => (S.r c : k)) r)) = 0
      from (presCL RD k S).lin_rel_self (.inr (.klr _ r)), map_zero]

/-! ## The downward relations -/

section Cases

variable {k}

theorem rotKD_X2X2 (c d : I) :
    rotKD (X2 d c ≫ X2 c d) =
      (X2 c d ≫ X2 d c : kobjR (KLR.Diagram.ob [d, c]) ⟶ kobjR (KLR.Diagram.ob [d, c])) := rfl

theorem wK_X2X2 (τ : I → I → k) (c d : I) : wK τ (X2 d c ≫ X2 c d) = τ d c * τ c d := by
  simp [wK, upShape]

theorem rotKLin_sqNe (c d : I) (h : c ≠ d) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.sqNe d c h.symm)) :
      LinDiagram k (KLR.Diagram.ob [c, d]) (KLR.Diagram.ob [c, d])) =
      ((S.t c d : k) * (S.t d c : k)) • LinDiagram.of (X2 c d ≫ X2 d c) -
        lpoly k ![D0 c d, D1 c d] (qCL S c d) := by
  change rotKLin (tauCL k S) (LinDiagram.of (X2 d c ≫ X2 c d) -
    lpoly k ![D0 d c, D1 d c] (qCL S d c)) = _
  have hfun : (fun a => rotKLin (tauCL k S)
      (LinDiagram.of (![D0 d c, D1 d c] (![1, 0] a)) : LinDiagram k _ _)) =
      fun a => (LinDiagram.of (![D0 c d, D1 c d] a) :
        LinDiagram k (kobjR (KLR.Diagram.ob [d, c])) (kobjR (KLR.Diagram.ob [d, c]))) := by
    funext a
    fin_cases a <;> simp [rotKLin_of, wK, upShape] <;> rfl
  rw [map_sub, rotKLin_of]
  erw [rotKLin_lpoly (tauCL k S) ![D0 d c, D1 d c] (qCL S d c)]
  rw [wK_X2X2, rotKD_X2X2, fin2_rev, rename_swap_qCL, hfun]

/-- Rotation of the KLR relation `ψ² = 0` on `E_c E_c`. -/
theorem rotKLin_sqEq (c : I) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.sqEq c)) :
      LinDiagram k (KLR.Diagram.ob [c, c]) (KLR.Diagram.ob [c, c])) =
      ((S.t c c : k) * (S.t c c : k)) • LinDiagram.of (X2 c c ≫ X2 c c) := by
  change rotKLin (tauCL k S) (LinDiagram.of (X2 c c ≫ X2 c c)) = _
  rw [rotKLin_of, wK_X2X2, rotKD_X2X2]

theorem wK_X2_D (τ : I → I → k) {a : Obj (KLR.Diagram.sig I)} {c d : I}
    (D : KLR.Diagram.ob [d, c] ⟶ a) (hD : ∀ L ∈ Diagram.layers D, ∃ e, L.gen = .dot e) :
    wK τ (X2 c d ≫ D) = τ c d := by
  have : wK τ D = 1 := by
    unfold wK
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hx
    obtain ⟨e, he⟩ := hD L hL
    rw [he]; rfl
  rw [wK_comp, this, mul_one]
  simp [wK, upShape]

theorem wK_D_X2 (τ : I → I → k) {a : Obj (KLR.Diagram.sig I)} {c d : I}
    (D : a ⟶ KLR.Diagram.ob [c, d]) (hD : ∀ L ∈ Diagram.layers D, ∃ e, L.gen = .dot e) :
    wK τ (D ≫ X2 c d) = τ c d := by
  have : wK τ D = 1 := by
    unfold wK
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hx
    obtain ⟨e, he⟩ := hD L hL
    rw [he]; rfl
  rw [wK_comp, this, one_mul]
  simp [wK, upShape]

/-- Rotation of the nilHecke dot slide `ψ x₀ - x₁ ψ = r_c` on `E_c E_c`. -/
theorem rotKLin_slideLEq (c : I) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.slideLEq c)) :
      LinDiagram k (KLR.Diagram.ob [c, c]) (KLR.Diagram.ob [c, c])) =
      (S.t c c : k) • LinDiagram.of (D1 c c ≫ X2 c c) -
        (S.t c c : k) • LinDiagram.of (X2 c c ≫ D0 c c) -
        (S.r c : k) • LinDiagram.of (𝟙 (KLR.Diagram.ob [c, c])) := by
  change rotKLin (tauCL k S) (LinDiagram.of (X2 c c ≫ D0 c c) - LinDiagram.of (D1 c c ≫ X2 c c) -
    (S.r c : k) • LinDiagram.of (𝟙 _)) = _
  rw [map_sub, map_sub, map_smul, rotKLin_of, rotKLin_of, rotKLin_of,
    wK_X2_D _ _ (fun L hL => by simp at hL; subst hL; exact ⟨c, rfl⟩),
    wK_D_X2 _ _ (fun L hL => by simp at hL; subst hL; exact ⟨c, rfl⟩)]
  erw [wK_id, rotKD_id, one_smul]
  rfl

/-- Rotation of the nilHecke dot slide `x₀ ψ - ψ x₁ = r_c` on `E_c E_c`. -/
theorem rotKLin_slideREq (c : I) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.slideREq c)) :
      LinDiagram k (KLR.Diagram.ob [c, c]) (KLR.Diagram.ob [c, c])) =
      (S.t c c : k) • LinDiagram.of (X2 c c ≫ D1 c c) -
        (S.t c c : k) • LinDiagram.of (D0 c c ≫ X2 c c) -
        (S.r c : k) • LinDiagram.of (𝟙 (KLR.Diagram.ob [c, c])) := by
  change rotKLin (tauCL k S) (LinDiagram.of (D0 c c ≫ X2 c c) - LinDiagram.of (X2 c c ≫ D1 c c) -
    (S.r c : k) • LinDiagram.of (𝟙 _)) = _
  rw [map_sub, map_sub, map_smul, rotKLin_of, rotKLin_of, rotKLin_of,
    wK_D_X2 _ _ (fun L hL => by simp at hL; subst hL; exact ⟨c, rfl⟩),
    wK_X2_D _ _ (fun L hL => by simp at hL; subst hL; exact ⟨c, rfl⟩)]
  erw [wK_id, rotKD_id, one_smul]
  rfl

/-- Rotation of the dot slide `ψ x₀ = x₁ ψ` on `E_c E_d`, `c ≠ d`. -/
theorem rotKLin_slideLNe (c d : I) (h : c ≠ d) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.slideLNe c d h)) :
      LinDiagram k (KLR.Diagram.ob [c, d]) (KLR.Diagram.ob [d, c])) =
      (S.t d c : k) • LinDiagram.of (D1 c d ≫ X2 c d) -
        (S.t d c : k) • LinDiagram.of (X2 c d ≫ D0 d c) := by
  change rotKLin (tauCL k S) (LinDiagram.of (X2 c d ≫ D0 d c) -
    LinDiagram.of (D1 c d ≫ X2 c d)) = _
  rw [map_sub, rotKLin_of, rotKLin_of,
    wK_X2_D _ _ (fun L hL => by simp at hL; subst hL; exact ⟨d, rfl⟩),
    wK_D_X2 _ _ (fun L hL => by simp at hL; subst hL; exact ⟨d, rfl⟩)]
  rfl

/-- Rotation of the dot slide `x₀ ψ = ψ x₁` on `E_c E_d`, `c ≠ d`. -/
theorem rotKLin_slideRNe (c d : I) (h : c ≠ d) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.slideRNe c d h)) :
      LinDiagram k (KLR.Diagram.ob [c, d]) (KLR.Diagram.ob [d, c])) =
      (S.t d c : k) • LinDiagram.of (X2 c d ≫ D1 d c) -
        (S.t d c : k) • LinDiagram.of (D0 c d ≫ X2 c d) := by
  change rotKLin (tauCL k S) (LinDiagram.of (D0 c d ≫ X2 c d) -
    LinDiagram.of (X2 c d ≫ D1 d c)) = _
  rw [map_sub, rotKLin_of, rotKLin_of,
    wK_D_X2 _ _ (fun L hL => by simp at hL; subst hL; exact ⟨c, rfl⟩),
    wK_X2_D _ _ (fun L hL => by simp at hL; subst hL; exact ⟨c, rfl⟩)]
  rfl

theorem wK_braidL (τ : I → I → k) (c d e : I) :
    wK τ (braidL c d e) = τ c d * τ c e * τ d e := by
  simp [wK, upShape]; ring

theorem wK_braidR (τ : I → I → k) (c d e : I) :
    wK τ (braidR c d e) = τ c d * τ c e * τ d e := by
  simp [wK, upShape]; ring

/-- Rotation of the braid relation `ψ₀ψ₁ψ₀ = ψ₁ψ₀ψ₁` on `E_c E_d E_e`. -/
theorem rotKLin_braid (c d e : I) (h : ¬ (c = e ∧ c ≠ d)) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.braid c d e h)) :
      LinDiagram k (KLR.Diagram.ob [c, d, e]) (KLR.Diagram.ob [e, d, c])) =
      ((S.t d c : k) * (S.t e c : k) * (S.t e d : k)) • LinDiagram.of (braidR c d e) -
        ((S.t d c : k) * (S.t e c : k) * (S.t e d : k)) • LinDiagram.of (braidL c d e) := by
  change rotKLin (tauCL k S) (LinDiagram.of (braidL c d e) - LinDiagram.of (braidR c d e)) = _
  rw [map_sub, rotKLin_of, rotKLin_of, wK_braidL, wK_braidR]
  rfl

/-- Rotation of the braid relation `ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁ = r_c Q̄_{cd}` on `E_c E_d E_c`, `c ≠ d`. -/
theorem rotKLin_braidQ (c d : I) (h : c ≠ d) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.braidQ c d h)) :
      LinDiagram k (KLR.Diagram.ob [c, d, c]) (KLR.Diagram.ob [c, d, c])) =
      ((S.t d c : k) * (S.t c c : k) * (S.t c d : k)) • LinDiagram.of (braidR c d c) -
        ((S.t d c : k) * (S.t c c : k) * (S.t c d : k)) • LinDiagram.of (braidL c d c) -
        (S.r c : k) • lpoly k ![E0 c d c, E1 c d c, E2 c d c] (KLR.qbar (qCL S c d)) := by
  change rotKLin (tauCL k S) (LinDiagram.of (braidL c d c) - LinDiagram.of (braidR c d c) -
    (S.r c : k) • lpoly k ![E0 c d c, E1 c d c, E2 c d c] (KLR.qbar (qCL S c d))) = _
  have hfun : (fun a => rotKLin (tauCL k S)
      (LinDiagram.of (![E0 c d c, E1 c d c, E2 c d c] (![2, 1, 0] a)) : LinDiagram k _ _)) =
      fun a => (LinDiagram.of (![E0 c d c, E1 c d c, E2 c d c] a) :
        LinDiagram k (kobjR (KLR.Diagram.ob [c, d, c])) (kobjR (KLR.Diagram.ob [c, d, c]))) := by
    funext a
    fin_cases a <;> simp [rotKLin_of, wK, upShape] <;> rfl
  rw [map_sub, map_sub, map_smul, rotKLin_of, rotKLin_of, wK_braidL, wK_braidR]
  erw [rotKLin_lpoly (tauCL k S) ![E0 c d c, E1 c d c, E2 c d c] (KLR.qbar (qCL S c d))]
  rw [fin3_rev, KLR.qbar_rename_rev, hfun]
  rfl

/-! ### The downward relations as rotated upward relations -/

section Algebra

variable {M : Type*} [AddCommGroup M] [Module k M]

theorem smul_aux₁ (A L : M) (T x : k) (h : T * x = 1) : T • A - L = T • (A - x • L) := by
  rw [show T • (A - x • L) = T • A - (T * x) • L by module, h, one_smul]

theorem smul_aux₂ (A B L : M) (r : k) :
    (1 : k) • B - (1 : k) • A - r • L = (-1 : k) • (A - B - (-r) • L) := by
  module

theorem smul_aux₃ (A B L : M) (T r x : k) (h : T * x = 1) :
    T • B - T • A - r • L = (-T) • (A - B - (-r) • (x • L)) := by
  rw [show (-T) • (A - B - (-r) • (x • L)) = T • B - T • A - (T * x * r) • L by module, h,
    one_mul]

theorem smul_aux₄ (A B : M) (T : k) : T • B - T • A = (-T) • (A - B) := by
  module

end Algebra

theorem units_mul_inv_mul_inv (a b : kˣ) : ((a * b : kˣ) : k) * ((a⁻¹ * b⁻¹ : kˣ) : k) = 1 := by
  rw [← Units.val_mul, mul_mul_mul_comm, mul_inv_cancel, mul_inv_cancel, mul_one, Units.val_one]

/-- `ψ² = 0` on `F_c F_c`: the rotation of the upward relation. -/
theorem relDown_sqEq (c : I) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.sqEq c)) :
      LinDiagram k (KLR.Diagram.ob [c, c]) (KLR.Diagram.ob [c, c])) =
      ((1 : kˣ) : k) • relationR k (qCL S.dual) (fun c => (S.dual.r c : k)) (.sqEq c) := by
  rw [rotKLin_sqEq, S.t_self, Units.val_one, one_mul, one_smul, one_smul]
  rfl

/-- `ψ² = Q'_{cd}(x₀, x₁)` on `F_c F_d`: `t_{cd} t_{dc}` times it is the rotation of the upward
relation `ψ² = Q_{dc}` on `E_d E_c`. -/
theorem relDown_sqNe (c d : I) (h : c ≠ d) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.sqNe d c h.symm)) :
      LinDiagram k (KLR.Diagram.ob [c, d]) (KLR.Diagram.ob [c, d])) =
      ((S.t c d * S.t d c : kˣ) : k) •
        relationR k (qCL S.dual) (fun c => (S.dual.r c : k)) (.sqNe c d h) := by
  rw [rotKLin_sqNe S c d h]
  change _ = _ • (LinDiagram.of (X2 c d ≫ X2 d c) - lpoly k ![D0 c d, D1 c d] (qCL S.dual c d))
  rw [qCL_dual]
  simp only [lpoly, RescaleDatum.ncEval_C_mul]
  rw [← Units.val_mul]
  exact smul_aux₁ _ _ _ _ (units_mul_inv_mul_inv _ _)

/-- The nilHecke dot slide `ψ x₀ - x₁ ψ = r'_c` on `F_c F_c`, with `r'_c = -r_c`. -/
theorem relDown_slideLEq (c : I) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.slideLEq c)) :
      LinDiagram k (KLR.Diagram.ob [c, c]) (KLR.Diagram.ob [c, c])) =
      ((-1 : kˣ) : k) • relationR k (qCL S.dual) (fun c => (S.dual.r c : k)) (.slideLEq c) := by
  rw [rotKLin_slideLEq, S.t_self, Units.val_one]
  change _ = _ • (LinDiagram.of (X2 c c ≫ D0 c c) - LinDiagram.of (D1 c c ≫ X2 c c) -
    ((S.dual.r c : kˣ) : k) • LinDiagram.of (𝟙 (KLR.Diagram.ob [c, c])))
  rw [CLScalars.dual_r, Units.val_neg, Units.val_neg, Units.val_one]
  exact smul_aux₂ _ _ _ _

/-- The nilHecke dot slide `x₀ ψ - ψ x₁ = r'_c` on `F_c F_c`, with `r'_c = -r_c`. -/
theorem relDown_slideREq (c : I) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.slideREq c)) :
      LinDiagram k (KLR.Diagram.ob [c, c]) (KLR.Diagram.ob [c, c])) =
      ((-1 : kˣ) : k) • relationR k (qCL S.dual) (fun c => (S.dual.r c : k)) (.slideREq c) := by
  rw [rotKLin_slideREq, S.t_self, Units.val_one]
  change _ = _ • (LinDiagram.of (D0 c c ≫ X2 c c) - LinDiagram.of (X2 c c ≫ D1 c c) -
    ((S.dual.r c : kˣ) : k) • LinDiagram.of (𝟙 (KLR.Diagram.ob [c, c])))
  rw [CLScalars.dual_r, Units.val_neg, Units.val_neg, Units.val_one]
  exact smul_aux₂ _ _ _ _

/-- The dot slide `ψ x₀ = x₁ ψ` on `F_c F_d`, `c ≠ d`. -/
theorem relDown_slideLNe (c d : I) (h : c ≠ d) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.slideLNe c d h)) :
      LinDiagram k (KLR.Diagram.ob [c, d]) (KLR.Diagram.ob [d, c])) =
      ((-S.t d c : kˣ) : k) •
        relationR k (qCL S.dual) (fun c => (S.dual.r c : k)) (.slideLNe c d h) := by
  rw [rotKLin_slideLNe, Units.val_neg]
  exact smul_aux₄ _ _ _

/-- The dot slide `x₀ ψ = ψ x₁` on `F_c F_d`, `c ≠ d`. -/
theorem relDown_slideRNe (c d : I) (h : c ≠ d) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.slideRNe c d h)) :
      LinDiagram k (KLR.Diagram.ob [c, d]) (KLR.Diagram.ob [d, c])) =
      ((-S.t d c : kˣ) : k) •
        relationR k (qCL S.dual) (fun c => (S.dual.r c : k)) (.slideRNe c d h) := by
  rw [rotKLin_slideRNe, Units.val_neg]
  exact smul_aux₄ _ _ _

/-- The braid relation `ψ₀ψ₁ψ₀ = ψ₁ψ₀ψ₁` on `F_c F_d F_e`. -/
theorem relDown_braid (c d e : I) (h : ¬ (c = e ∧ c ≠ d)) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.braid c d e h)) :
      LinDiagram k (KLR.Diagram.ob [c, d, e]) (KLR.Diagram.ob [e, d, c])) =
      ((-(S.t d c * S.t e c * S.t e d) : kˣ) : k) •
        relationR k (qCL S.dual) (fun c => (S.dual.r c : k)) (.braid c d e h) := by
  rw [rotKLin_braid, Units.val_neg, Units.val_mul, Units.val_mul]
  exact smul_aux₄ _ _ _

/-- The braid relation `ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁ = r'_c Q̄'_{cd}` on `F_c F_d F_c`, `c ≠ d`. -/
theorem relDown_braidQ (c d : I) (h : c ≠ d) :
    (rotKLin (tauCL k S) (relationR k (qCL S) (fun c => (S.r c : k)) (.braidQ c d h)) :
      LinDiagram k (KLR.Diagram.ob [c, d, c]) (KLR.Diagram.ob [c, d, c])) =
      ((-(S.t c d * S.t d c) : kˣ) : k) •
        relationR k (qCL S.dual) (fun c => (S.dual.r c : k)) (.braidQ c d h) := by
  rw [rotKLin_braidQ, S.t_self, Units.val_one, mul_one]
  change _ = _ • (LinDiagram.of (braidL c d c) - LinDiagram.of (braidR c d c) -
    ((S.dual.r c : kˣ) : k) • lpoly k ![E0 c d c, E1 c d c, E2 c d c] (KLR.qbar (qCL S.dual c d)))
  rw [qCL_dual, RescaleDatum.qbar_C_mul]
  simp only [lpoly, RescaleDatum.ncEval_C_mul]
  rw [CLScalars.dual_r, Units.val_neg, Units.val_neg, show ((S.t d c : k) * (S.t c d : k)) =
    ((S.t c d * S.t d c : kˣ) : k) by rw [Units.val_mul, mul_comm]]
  exact smul_aux₃ _ _ _ _ _ _ (units_mul_inv_mul_inv _ _)

end Cases

/-! ## The main theorem -/

variable {RD k} in
theorem lin_dnLin_eq_zero_of_rot {ν : X} {a b : Obj (KLR.Diagram.sig I)} {Z R' : LinDiagram k a b}
    (v : kˣ) (hZ : (presCL RD k S).lin (dnLin RD k ν Z) = 0) (h : Z = (v : k) • R') :
    (presCL RD k S).lin (dnLin RD k ν R') = 0 := by
  rwa [h, dnLin_smul, lin_smul, ← Units.smul_def, smul_eq_zero_iff_eq] at hZ

/-- **The KLR relations for the dual scalars `Q'` hold on downward strands of `U_Q(g)`**
(CL, arXiv:1111.1431v3, Definition 1.1 (2) and the sentence after `eq_almost_cyclic`, §2.2, p. 6:
"the `F`'s carry an action of the KLR algebra associated to `Q'`", which CL state is ensured by
`Q`-cyclicity). Every added relation `relationDown k S r` of `presCLDown` is zero in `presCL`.

Each downward relation for `Q' = (t', s', r')` is a unit multiple of the rotation by `180°`
(`rotC`, the mate for nested cups and caps) of an upward relation for `Q`: the rotated upward
crossing `E_j E_i ⟶ E_i E_j` is `t_{ij}` times the downward one (`eq_almost_cyclic`), the rotated
upward dot is the downward dot (`eq_cyclic_dot`), so the double crossing on `F_c F_d` is
`(t_{cd} t_{dc})^{-1} Q_{cd} = Q'_{cd}` (`qCL_dual`), the sign of the nilHecke dot slides
changes (`r' = -r`), and the braid relation acquires `r'_c Q̄'_{cd} = -(t_{cd} t_{dc})^{-1} r_c
Q̄_{cd}`. These are exactly CL's `Q'` (§2.1.1, last display). -/
theorem lin_relationDown (r : RelDown RD) : (presCL RD k S).lin (relationDown k S r) = 0 := by
  obtain ⟨ν, r0⟩ := r
  cases r0 with
  | sqEq c =>
    exact lin_dnLin_eq_zero_of_rot S 1 (lin_dnLin_rotKLin RD k S (.sqEq c) ν)
      (relDown_sqEq S c)
  | sqNe c d h =>
    exact lin_dnLin_eq_zero_of_rot S _ (lin_dnLin_rotKLin RD k S (.sqNe d c h.symm) ν)
      (relDown_sqNe S c d h)
  | slideLEq c =>
    exact lin_dnLin_eq_zero_of_rot S _ (lin_dnLin_rotKLin RD k S (.slideLEq c) ν)
      (relDown_slideLEq S c)
  | slideLNe c d h =>
    exact lin_dnLin_eq_zero_of_rot S _ (lin_dnLin_rotKLin RD k S (.slideLNe c d h) ν)
      (relDown_slideLNe S c d h)
  | slideREq c =>
    exact lin_dnLin_eq_zero_of_rot S _ (lin_dnLin_rotKLin RD k S (.slideREq c) ν)
      (relDown_slideREq S c)
  | slideRNe c d h =>
    exact lin_dnLin_eq_zero_of_rot S _ (lin_dnLin_rotKLin RD k S (.slideRNe c d h) ν)
      (relDown_slideRNe S c d h)
  | braid c d e h =>
    exact lin_dnLin_eq_zero_of_rot S _ (lin_dnLin_rotKLin RD k S (.braid c d e h) ν)
      (relDown_braid S c d e h)
  | braidQ c d h =>
    exact lin_dnLin_eq_zero_of_rot S _ (lin_dnLin_rotKLin RD k S (.braidQ c d h) ν)
      (relDown_braidQ S c d h)

/-! ## `presCL` and `presCLDown` present the same 2-category -/

theorem scL_one {S' : Signature} {a b : Obj S'} (f : LinDiagram k a b) :
    Rescale.scL (fun _ => (1 : kˣ)) f = f := by
  induction f using Finsupp.induction_linear with
  | zero => exact Rescale.scL_zero
  | add f g hf hg => rw [Rescale.scL_add, hf, hg]
  | single d r =>
    rw [Rescale.scL_single]
    simp only [Rescale.weight, List.map_const', List.prod_replicate, one_pow, Units.val_one,
      one_smul]
    exact Finsupp.smul_single_one d r

/-- The relations of `presCL` hold in `presCLDown` (they are among its relations). -/
theorem presCLDown_lin_rel (i : (presCL RD k S).Rel) :
    (presCLDown RD k S).lin (Rescale.scL (fun _ => (1 : kˣ)) ((presCL RD k S).rel i)) = 0 := by
  rw [scL_one]
  exact (presCLDown RD k S).lin_rel_self (.inl i)

/-- The relations of `presCLDown` hold in `presCL` (`lin_relationDown`). -/
theorem presCL_lin_rel_down (i : (presCLDown RD k S).Rel) :
    (presCL RD k S).lin (Rescale.scL (fun _ => (1 : kˣ)) ((presCLDown RD k S).rel i)) = 0 := by
  rw [scL_one]
  rcases i with i | r
  · exact (presCL RD k S).lin_rel_self i
  · exact lin_relationDown RD k S r

/-- **`presCL` and `presCLDown` present the same 2-category** (CL, Definition 1.1 (2), after
`eq_almost_cyclic`): the identity on diagrams is an isomorphism of the presented categories
`U_Q(g) = (presCL RD k S).Presented ≌ (presCLDown RD k S).Presented` (an isomorphism of
categories, `presCLDownEquiv_functor_comp_inverse`, `presCLDownEquiv_inverse_comp_functor`),
compatible with whiskering, so that adding the KLR relations for `Q'` on downward strands does
not change `U_Q(g)`. -/
def presCLDownEquiv : (presCL RD k S).Presented ≌ (presCLDown RD k S).Presented :=
  Rescale.equiv (fun _ => (1 : kˣ)) (presCLDown_lin_rel RD k S) (fun _ => (1 : kˣ))
    (presCL_lin_rel_down RD k S) (fun _ => mul_one 1)

theorem presCLDownEquiv_functor_lin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (presCLDownEquiv RD k S).functor.map ((presCL RD k S).lin f) = (presCLDown RD k S).lin f := by
  show (Rescale.functor (fun _ => (1 : kˣ)) (presCLDown_lin_rel RD k S)).map _ = _
  rw [Rescale.functor_lin, scL_one]

theorem presCLDownEquiv_inverse_lin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (presCLDownEquiv RD k S).inverse.map ((presCLDown RD k S).lin f) = (presCL RD k S).lin f := by
  show (Rescale.functor (fun _ => (1 : kˣ)) (presCL_lin_rel_down RD k S)).map _ = _
  rw [Rescale.functor_lin, scL_one]

theorem presCLDownEquiv_functor_diag {a b : Obj (psig RD)} (d : a ⟶ b) :
    (presCLDownEquiv RD k S).functor.map ((presCL RD k S).diag d) = (presCLDown RD k S).diag d :=
  presCLDownEquiv_functor_lin RD k S _

theorem presCLDownEquiv_inverse_diag {a b : Obj (psig RD)} (d : a ⟶ b) :
    (presCLDownEquiv RD k S).inverse.map ((presCLDown RD k S).diag d) = (presCL RD k S).diag d :=
  presCLDownEquiv_inverse_lin RD k S _

theorem presCLDownEquiv_functor_comp_inverse :
    (presCLDownEquiv RD k S).functor ⋙ (presCLDownEquiv RD k S).inverse = 𝟭 _ :=
  Rescale.functor_comp_functor_inv (presCLDown_lin_rel RD k S) (presCL_lin_rel_down RD k S)
    (fun _ => mul_one 1)

theorem presCLDownEquiv_inverse_comp_functor :
    (presCLDownEquiv RD k S).inverse ⋙ (presCLDownEquiv RD k S).functor = 𝟭 _ :=
  Rescale.functor_comp_functor_inv (presCL_lin_rel_down RD k S) (presCLDown_lin_rel RD k S)
    (fun _ => mul_one 1)

/-- The identity is compatible with whiskering: it is a strict 2-functor. -/
theorem presCLDownEquiv_functor_whisk {a b : Obj (psig RD)}
    (f : (presCL RD k S).obj a ⟶ (presCL RD k S).obj b) (u : Obj (psig RD))
    (v : List (psig RD).Colour) :
    (presCLDownEquiv RD k S).functor.map ((presCL RD k S).whisk f u v) =
      (presCLDown RD k S).whisk ((presCLDownEquiv RD k S).functor.map f) u v :=
  Rescale.functor_whisk (presCLDown_lin_rel RD k S) f u v

/-- **The two presentations have the same relations**: a linear combination of diagrams is zero
in `U_Q(g)` if and only if it is zero in `presCLDown`. -/
theorem presCL_lin_eq_zero_iff {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (presCL RD k S).lin f = 0 ↔ (presCLDown RD k S).lin f = 0 := by
  constructor
  · intro h
    rw [← presCLDownEquiv_functor_lin, h, Functor.map_zero]
  · intro h
    rw [← presCLDownEquiv_inverse_lin, h, Functor.map_zero]

end Categorification.KL3.Diagram.CL
