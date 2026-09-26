/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetrySigma

/-!
# Properties and symmetries of the 2-category `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3
(TeX labels `sec_symm`, `eq_almost_biadjoints`).

The symmetries `ψ̃ : U → U^co` (`Categorification.Diagrams.KL3.SymmetryPsi`) and
`σ̃ : U → U^op` (`Categorification.Diagrams.KL3.SymmetrySigma`) are constructed from the
presentation of `U`. This file proves the relations among them stated in §3.3.2 and records the
degree computation behind the almost biadjoints of §3.3.1:

* `sigU_sigU`: `σ̃² = 1` ("The square of `σ̃` is the identity"), on well-formed objects, up to the
  canonical identification `σ̃(σ̃(x)) = x` of objects (`Sig.obj_obj`);
* `psiU_sigU`: `σ̃ ψ̃ = ψ̃ σ̃` (KL III (3.45), second equality);
* `cpm_almost_biadjoint`: KL III (3.41), `c_{-i,λ+i_X} = -c_{+i,λ}`, so that the cap
  `E_{+i} E_{-i} 1_{λ+i_X} → 1_{λ+i_X}` has degree `-c_{+i,λ}`: with the shift
  `E_{-i} 1_{λ+i_X} {-c_{+i,λ} - t}` the units and counits of `E_{+i} 1_λ {t} ⊣ E_{-i}` have
  degree zero (KL III (3.40)–(3.42)).

## Interpretation of the printed statements

* KL III (3.45) prints the first equality as `ω̃σ̃ = ω̃σ̃`, evidently a typo for `ω̃σ̃ = σ̃ω̃`.
  The symmetry `ω̃` (inverting orientations) and the rotation `τ̃` (3.46) are not constructed as
  2-functors here: checking the relations of `U` under `ω̃` requires the relations of `R(ν)`, the
  curl relations and the two descriptions of the sideways crossings on *downward* strands, i.e.
  the rotations of the upward relations by nested cups and caps (for `τ̃` on a single
  Hom-category, the library's `Pivotal.rotateFunctor` for the pivotal structure `pivotal RD k`
  already applies).
* KL III works with grading shifts `{t}`; our `U` has none, and "degree preserving 2-functor" is
  formalized as "sends the degree-`t` part of every Hom-space to the degree-`t` part"
  (`psiU_homDeg`, `sigU_homDeg`). The shift conventions `{t} ↦ {-t}` of `ψ̃` and `{t} ↦ {t}` of
  `σ̃` are then automatic.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Opposite

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## `σ̃² = 1` -/

namespace Sig

theorem col_col (c : Col I X) : col (RD := RD) (col (RD := RD) c) = c := by
  obtain ⟨l, r⟩ := c
  refine Col.ext rfl ?_
  show -(sh RD l + -(sh RD l + r)) = r
  abel

theorem word_word (w : List (psig RD).Colour) : word RD (word RD w) = w := by
  simp [word, List.map_reverse, List.map_map, Function.comp_def, col_col]

theorem gen_gen (g : (psig RD).Gen) : gen (gen g) = g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | ⟨l, r⟩ | ⟨l, r⟩
  · show PivotalGen.gen (Gen0.dot (col (col c))) = _
    rw [col_col]
  · show PivotalGen.gen (Gen0.cross ε i j
      (-(sh RD (ε, j) + (sh RD (ε, i) + -(sh RD (ε, i) + (sh RD (ε, j) + ν)))))) = _
    congr 2
    abel
  · show PivotalGen.cup (⟨l.dual.dual, - -r⟩ : Col I X) = _
    rw [Letter.dual_dual, neg_neg]
  · show PivotalGen.cap (⟨l.dual.dual, - -r⟩ : Col I X) = _
    rw [Letter.dual_dual, neg_neg]

theorem obj_obj (a : Obj (psig RD)) (ha : a.WF) : obj RD (obj RD a) = a := by
  refine Obj.ext ?_ (word_word _)
  show -eR (RD := RD) (-eR (RD := RD) a.start a.word) (word RD a.word) = a.start
  have h := (ok_word (RD := RD) _ _ ha).2
  unfold eR at h ⊢
  rw [h, neg_neg]

theorem rlay_rlay (L : Layer (psig RD)) (hv : L.Valid) : rlay (rlay L) = L := by
  refine Layer.ext ?_ (word_word _) (gen_gen _) (word_word _)
  show -eR (RD := RD) ((psig RD).right (gen L.gen)) (word RD L.left) = L.start
  have h := (ok_word (RD := RD) _ _ hv.left_ok).2
  rw [gen_right, show lR (RD := RD) L.gen = eR (RD := RD) L.start L.left from hv.left_end.symm]
  unfold eR at h ⊢
  rw [h, neg_neg]

theorem sgn_map_rlay [DecidableEq I] (ls : List (Layer (psig RD))) :
    sgn (ls.map rlay) = sgn ls := by
  simp only [sgn, List.map_map, Function.comp_def, rlay, sgnG_gen]

end Sig

variable [DecidableEq I]

open Sig in
/-- **`σ̃² = 1`** (KL III §3.3.2: "The square of `σ̃` is the identity"), on 2-morphisms between
well-formed objects, up to the canonical identifications `σ̃(σ̃(x)) = x` (`Sig.obj_obj`). -/
theorem sigU_sigU {a b : Obj (psig RD)} (ha : a.WF) (hb : b.WF)
    (f : (pres RD k).obj a ⟶ (pres RD k).obj b) :
    (sigU RD k).map ((sigU RD k).map f) = TR RD k (obj_obj a ha) (obj_obj b hb) f := by
  let φ : ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k]
      ((pres RD k).obj (obj RD (obj RD a)) ⟶ (pres RD k).obj (obj RD (obj RD b))) :=
    ((sigU RD k).mapLinearMap k).comp ((sigU RD k).mapLinearMap k)
  have key : φ = TR RD k (obj_obj a ha) (obj_obj b hb) := by
    refine hom_ext_diag RD k _ _ fun d => ?_
    show (sigU RD k).map ((sigU RD k).map ((pres RD k).diag d)) = _
    rw [sigU_diag, Functor.map_smul, sigU_diag, Sig.layers_reflD, sgn_map_rlay, smul_smul, ← Int.cast_mul,
      sgn_sq, Int.cast_one, one_smul, TR_diag]
    apply (pres RD k).diag_eq_of_layers_eq
    simp only [layers_reflD, List.map_map, Diagram.layers_cast]
    conv_rhs => rw [← List.map_id (Diagram.layers d)]
    refine List.map_congr_left fun L hL => ?_
    exact rlay_rlay L (chain_mem (Diagram.chain d) hL).1
  exact LinearMap.congr_fun key f

/-! ## `σ̃ ψ̃ = ψ̃ σ̃` -/

omit [DecidableEq I] in
theorem psi_sig_gen (g : (psig RD).Gen) : Psi.gen (Sig.gen g) = Sig.gen (Psi.gen g) := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | ⟨l, r⟩ | ⟨l, r⟩
  · rfl
  · show PivotalGen.gen (Gen0.cross ε i j (-(sh RD (ε, i) + (sh RD (ε, j) + ν)))) =
      PivotalGen.gen (Gen0.cross ε i j (-(sh RD (ε, j) + (sh RD (ε, i) + ν))))
    rw [add_left_comm]
  · show PivotalGen.cap ((inv RD).dual ⟨l.dual, -r⟩) = PivotalGen.cap ⟨(l.dual).dual, -(sh RD l + r)⟩
    rw [inv_dual]
    congr 2
    show sh RD l.dual + -r = -(sh RD l + r)
    rw [sh_dual]; abel
  · show PivotalGen.cup ((inv RD).dual ⟨l.dual, -r⟩) = PivotalGen.cup ⟨(l.dual).dual, -(sh RD l + r)⟩
    rw [inv_dual]
    congr 2
    show sh RD l.dual + -r = -(sh RD l + r)
    rw [sh_dual]; abel

omit [DecidableEq I] in
theorem psi_rlay_sig_rlay (L : Layer (psig RD)) :
    Psi.rlay (Sig.rlay L) = Sig.rlay (Psi.rlay L) := by
  refine Layer.ext ?_ rfl (psi_sig_gen _) rfl
  show -Sig.eR (RD := RD) ((psig RD).right L.gen) L.right =
    -Sig.eR (RD := RD) ((psig RD).right (Psi.gen L.gen)) L.right
  rw [Psi.gen_right]

theorem sgnG_psi_gen (g : (psig RD).Gen) : Sig.sgnG (Psi.gen g) = Sig.sgnG g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · show (if j = i then -1 else 1 : ℤ) = if i = j then -1 else 1
    simp only [eq_comm]
  · rfl
  · rfl

theorem sgn_rrev (ls : List (Layer (psig RD))) : Sig.sgn (Psi.rrev ls) = Sig.sgn ls := by
  simp only [Sig.sgn, Psi.rrev, List.map_reverse, List.prod_reverse, List.map_map, Function.comp_def,
    Psi.rlay, sgnG_psi_gen]

/-- **`σ̃ ψ̃ = ψ̃ σ̃`** (KL III (3.45)). -/
theorem psiU_sigU {a b : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj b) :
    ((psiU RD k).map ((sigU RD k).map f)).unop = (sigU RD k).map ((psiU RD k).map f).unop := by
  let φ : ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k]
      ((pres RD k).obj (Sig.obj RD b) ⟶ (pres RD k).obj (Sig.obj RD a)) :=
    { toFun := fun f => ((psiU RD k).map ((sigU RD k).map f)).unop
      map_add' := fun f g => by simp only [Functor.map_add, unop_add]
      map_smul' := fun r f => by simp only [Functor.map_smul, unop_smul', RingHom.id_apply] }
  let ψ : ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k]
      ((pres RD k).obj (Sig.obj RD b) ⟶ (pres RD k).obj (Sig.obj RD a)) :=
    { toFun := fun f => (sigU RD k).map ((psiU RD k).map f).unop
      map_add' := fun f g => by simp only [Functor.map_add, unop_add]
      map_smul' := fun r f => by simp only [Functor.map_smul, unop_smul', RingHom.id_apply] }
  have key : φ = ψ := by
    refine hom_ext_diag RD k _ _ fun d => ?_
    show ((psiU RD k).map ((sigU RD k).map ((pres RD k).diag d))).unop =
      (sigU RD k).map ((psiU RD k).map ((pres RD k).diag d)).unop
    rw [sigU_diag, Functor.map_smul, psiU_diag, psiU_diag, Quiver.Hom.unop_op, sigU_diag,
      unop_smul', Quiver.Hom.unop_op, Psi.layers_reflD, sgn_rrev]
    congr 1
    apply (pres RD k).diag_eq_of_layers_eq
    simp only [Psi.layers_reflD, Sig.layers_reflD, Psi.rrev, List.map_reverse, List.map_map,
      Function.comp_def, psi_rlay_sig_rlay]
  exact LinearMap.congr_fun key f

/-! ## Almost biadjoints (KL III (3.40)–(3.42)) -/

omit [DecidableEq I] in
/-- **KL III (3.41)**: `c_{-i,λ+i_X} = -c_{+i,λ}`. Together with `c_{+i,λ}` for the cup
`1_λ → E_{-i} E_{+i} 1_λ` (`deg_cup_FE`) this is the degree computation showing that
`E_{+i} 1_λ {t} ⊣ E_{-i} 1_{λ+i_X} {-c_{+i,λ} - t}` is an adjunction with units and counits of
degree zero. -/
theorem cpm_almost_biadjoint (i : I) (lam : X) :
    cpm RD false i (sh RD (up i) + lam) = -cpm RD true i lam := by
  simp only [cpm, pair_sh, A_self, sgn_true, sgn_false]
  ring

end Categorification.KL3.Diagram
