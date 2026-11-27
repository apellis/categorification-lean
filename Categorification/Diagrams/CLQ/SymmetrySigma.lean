/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetrySigmaSymm
import Categorification.Diagrams.CLQ.SymmetryPsi

/-!
# The symmetry `σ̃` of `U_Q(g)`: reflection in a vertical axis

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3.2
(TeX label `sec_symm`), paragraph "Rescale, reflect across the `y`-axis, and send
`λ ↦ -λ`", for the 2-category `U_Q(g)` of S. Cautis, A. D. Lauda, arXiv:1111.1431v3,
Definition 1.1, with arbitrary scalars `t`, `s` and `r = 1` (`CLQ.pres`).

The signed reflection of diagrams across the `y`-axis with `λ ↦ -λ`
(`Categorification.Diagrams.KL3.SymmetrySigma`: `Sig.reflD`, the sign `Sig.sgn` counting the
crossings of equally labelled strands) maps every relation of `U_Q(g)` to a relation of
`U_Q(g)` **with the same scalars**:

* the cyclicity relations `eq_almost_cyclic` are exchanged (`cycCrossR j i ↔ cycCrossL i j`),
  and both carry the scalar `t_{ij}^{-1}`;
* the mixed relations `sec:mixedrels` are exchanged (`downupEF i j ↔ downupFE j i`), and both
  carry the scalar `t_{ji}`;
* the KLR relations on upward strands for `Q = qCL S` are reflected to KLR relations, since
  `Q_{ji}(u, v) = Q_{ij}(v, u)` (`CL.rename_swap_qCL`, `KSig.ksL_relation_of_symm`);
* the dot cyclicity, the bubble relations, the curl relations and the identity decompositions
  are those of KL III, and are reflected as there.

So `σ̃` is a `k`-linear functor `sigUQ : U_Q(g) ⥤ U_Q(g)`, reversing 1-morphisms
(`sigUQ_whisk`). It is used, with the reflection with inverted orientations
(`Categorification.Diagrams.CLQ.ThetaReflection`), for the orientation reversal `ω̃` of
`U_Q(g)` in Webster, arXiv:1309.3796v3, proof of Lemma 4.29.

## Main results

* `sigUQ RD k sc`, `sigUQ_lin`, `sigUQ_diag`, `sigUQ_dg`, `sigUQ_whisk`;
* `sigUQ_homDeg`: `σ̃` preserves degrees;
* `sigUQ_cwU`, `sigUQ_ccwU`: `σ̃` exchanges clockwise and counterclockwise bubbles, `λ ↦ -λ`;
* `sigLQ_eq_zero_of_lin`: the signed reflection of a linear combination of diagrams that vanishes
  in `U_Q(g)` vanishes in `U_Q(g)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Opposite Sig KSig

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

section Signed

variable [DecidableEq I]

/-- The signed reflection on the free 2-category. -/
def sigFreeQ : Obj (psig RD) ⥤ (pres RD k sc).Presented where
  obj a := (pres RD k sc).obj (obj RD a)
  map d := ((sgn (Diagram.layers d) : ℤ) : k) • (pres RD k sc).diag (reflD d)
  map_id a := by
    rw [Diagram.layers_id, sgn_nil, Int.cast_one, one_smul, reflD_id, Presentation.diag_id]
  map_comp f g := by
    rw [Diagram.layers_comp, sgn_append, reflD_comp, Presentation.diag_comp, Int.cast_mul,
      Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]

/-- The signed reflection of linear combinations of diagrams, in `U`. -/
abbrev sigLQ {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (pres RD k sc).obj (obj RD a) ⟶ (pres RD k sc).obj (obj RD b) :=
  (freeLift k (sigFreeQ RD k sc)).map f

variable {RD k sc}

theorem sigLQ_of {a b : Obj (psig RD)} (d : a ⟶ b) :
    sigLQ RD k sc (LinDiagram.of d) = ((sgn (Diagram.layers d) : ℤ) : k) • (pres RD k sc).diag (reflD d) :=
  freeLift_map_of _ d

theorem sigLQ_single {a b : Obj (psig RD)} (d : a ⟶ b) (r : k) :
    sigLQ RD k sc (Finsupp.single d r) =
      r • ((sgn (Diagram.layers d) : ℤ) : k) • (pres RD k sc).diag (reflD d) :=
  freeLift_map_single _ d r

theorem sigLQ_add' {a b : Obj (psig RD)} (f g : (a ⟶ b) →₀ k) :
    sigLQ RD k sc (f + g : (a ⟶ b) →₀ k) = sigLQ RD k sc f + sigLQ RD k sc g := Functor.map_add _

theorem sigLQ_single' {a b : Obj (psig RD)} (d : a ⟶ b) (r : k) :
    sigLQ RD k sc (Finsupp.single d r : (a ⟶ b) →₀ k) =
      r • ((sgn (Diagram.layers d) : ℤ) : k) • (pres RD k sc).diag (reflD d) :=
  freeLift_map_single _ d r

theorem sigLQ_zero {a b : Obj (psig RD)} : sigLQ RD k sc (0 : LinDiagram k a b) = 0 :=
  Functor.map_zero _ _ _

theorem sigLQ_add {a b : Obj (psig RD)} (f g : LinDiagram k a b) :
    sigLQ RD k sc (f + g) = sigLQ RD k sc f + sigLQ RD k sc g := Functor.map_add _

theorem sigLQ_sub {a b : Obj (psig RD)} (f g : LinDiagram k a b) :
    sigLQ RD k sc (f - g) = sigLQ RD k sc f - sigLQ RD k sc g := Functor.map_sub _

theorem sigLQ_neg {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    sigLQ RD k sc (-f) = -sigLQ RD k sc f := Functor.map_neg _

theorem sigLQ_smul {a b : Obj (psig RD)} (r : k) (f : LinDiagram k a b) :
    sigLQ RD k sc (r • f) = r • sigLQ RD k sc f := Functor.map_smul _ _ _

theorem sigLQ_comp {a b c : Obj (psig RD)} (f : LinDiagram k a b) (g : LinDiagram k b c) :
    sigLQ RD k sc (f ≫ g) = sigLQ RD k sc f ≫ sigLQ RD k sc g := Functor.map_comp _ _ _

theorem sigLQ_id (a : Obj (psig RD)) : sigLQ RD k sc (𝟙 (Free.of k a)) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

theorem sigLQ_sum {a b : Obj (psig RD)} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    sigLQ RD k sc (∑ x ∈ s, f x) = ∑ x ∈ s, sigLQ RD k sc (f x) :=
  Functor.map_sum _ _ _

/-! ## Whiskering -/


theorem sigLQ_whisker {a b : Obj (psig RD)} (f : LinDiagram k a b) (ha : a.WF)
    (hs : b.start = a.start) (he : b.endR = a.endR) {u : Obj (psig RD)}
    {v : List (psig RD).Colour} (hw : a.WhiskerOK u v) :
    sigLQ RD k sc (LinDiagram.whisker f u v hw) =
      eqToHom (congrArg (pres RD k sc).obj (obj_whisker hw.2.1).symm) ≫
        (pres RD k sc).whisk (sigLQ RD k sc f) (sigW a v) (word RD u.word) ≫
          eqToHom (congrArg (pres RD k sc).obj (obj_whisker_cod hs he hw.2.1)) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [show LinDiagram.whisker (0 : LinDiagram k a b) u v hw = 0 from Finsupp.mapDomain_zero,
      sigLQ_zero, sigLQ_zero, Presentation.whisk_zero, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    rw [LinDiagram.whisker_add, sigLQ_add, hf, hg, sigLQ_add, Presentation.whisk_add,
      Preadditive.add_comp, Preadditive.comp_add]
  | single d r =>
    rw [LinDiagram.whisker_single, sigLQ_single, sigLQ_single, Diagram.layers_whisker,
      sgn_map_whisker, reflD_whisker d ha hw, Presentation.diag_cast, Presentation.whisk_smul,
      Presentation.whisk_smul, Presentation.whisk_diag _ _ _ _ (whiskerOK_obj ha hw)]
    simp only [Linear.smul_comp, Linear.comp_smul]
    rfl

theorem sigLQ_whisker_eq_zero {a b : Obj (psig RD)} (f : LinDiagram k a b) (ha : a.WF)
    (hf : sigLQ RD k sc f = 0) {u : Obj (psig RD)} {v : List (psig RD).Colour}
    (hw : a.WhiskerOK u v) : sigLQ RD k sc (LinDiagram.whisker f u v hw) = 0 := by
  by_cases h0 : f = 0
  · subst h0
    rw [show LinDiagram.whisker (0 : LinDiagram k a b) u v hw = 0 from Finsupp.mapDomain_zero,
      sigLQ_zero]
  · obtain ⟨d, -⟩ := Finsupp.ne_iff.mp h0
    rw [sigLQ_whisker f ha (Diagram.chain d).start_eq (Diagram.chain d).endR_eq hw, hf,
      Presentation.whisk_zero, Limits.zero_comp, Limits.comp_zero]

end Signed

open Sig

/-! ## Transport along equalities of objects -/

/-- Transport of 2-morphisms along equalities of their boundary objects. -/
def TRQ {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b') :
    ((pres RD k sc).obj a' ⟶ (pres RD k sc).obj b') →ₗ[k] ((pres RD k sc).obj a ⟶ (pres RD k sc).obj b) where
  toFun f := eqToHom (congrArg (pres RD k sc).obj ea) ≫ f ≫ eqToHom (congrArg (pres RD k sc).obj eb.symm)
  map_add' f g := by rw [Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [Linear.smul_comp, Linear.comp_smul]; rfl

variable {RD k sc}

theorem TRQ_apply {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b')
    (f : (pres RD k sc).obj a' ⟶ (pres RD k sc).obj b') :
    TRQ RD k sc ea eb f =
      eqToHom (congrArg (pres RD k sc).obj ea) ≫ f ≫ eqToHom (congrArg (pres RD k sc).obj eb.symm) :=
  rfl

theorem TRQ_comp {a a' b b' c c' : Obj (psig RD)} (ea : a = a') (eb : b = b') (ec : c = c')
    (f : (pres RD k sc).obj a' ⟶ (pres RD k sc).obj b') (g : (pres RD k sc).obj b' ⟶ (pres RD k sc).obj c') :
    TRQ RD k sc ea eb f ≫ TRQ RD k sc eb ec g = TRQ RD k sc ea ec (f ≫ g) := by
  subst ea eb ec; simp [TRQ_apply]

theorem TRQ_diag {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b') (f : a' ⟶ b') :
    TRQ RD k sc ea eb ((pres RD k sc).diag f) = (pres RD k sc).diag (Diagram.cast f ea.symm eb.symm) := by
  rw [Presentation.diag_cast]; rfl

theorem TRQ_eq_zero {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b')
    {f : (pres RD k sc).obj a' ⟶ (pres RD k sc).obj b'} : TRQ RD k sc ea eb f = 0 ↔ f = 0 := by
  subst ea eb; simp [TRQ_apply]

theorem TRQ_add_sub {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b')
    (x y z : (pres RD k sc).obj a' ⟶ (pres RD k sc).obj b') :
    TRQ RD k sc ea eb x + TRQ RD k sc ea eb y - TRQ RD k sc ea eb z = TRQ RD k sc ea eb (x + y - z) := by
  rw [map_sub, map_add]

theorem TRQ_id {a a' : Obj (psig RD)} (ea : a = a') : TRQ RD k sc ea ea (𝟙 _) = 𝟙 _ := by
  subst ea; simp [TRQ_apply]

theorem TRQ_rfl {a b : Obj (psig RD)} (f : (pres RD k sc).obj a ⟶ (pres RD k sc).obj b) :
    TRQ RD k sc rfl rfl f = f := by simp [TRQ_apply]

section Signed

variable [DecidableEq I]

/-- **`σ̃` on normal-form diagrams**: the reflected layers `(v^rev, shape g, u^rev)` with
rightmost region `ν = -(μ + s_X)`, times the sign, up to the identification of the reflected
objects with normal forms (`Sig.trO`). -/
theorem sigLQ_of_mkD (μ ν : X) {s t : List (Letter I)} (s' t' : List (Letter I))
    (ls : List (LayerData I)) (h : SChain s ls t) (hν : ν = -wt RD μ s) (hs : s.reverse = s')
    (ht : t.reverse = t') :
    sigLQ RD k sc (LinDiagram.of (mkD RD μ ls h)) =
      ((sgnS ls : ℤ) : k) • TRQ RD k sc (hs ▸ trO μ ν s hν)
        (ht ▸ trO μ ν t (hν.trans (by rw [SChain.wt_eq RD μ h])))
        (NF.dg (pres RD k sc) ν s' t' (sls ls)) := by
  subst hs ht
  rw [sigLQ_of, layers_mkD, sgn_layList, reflD_mkD μ ν ls h hν, Presentation.diag_cast,
    NF.dg_of (sChain_sls h)]
  rfl

end Signed


/-! ## The reflected relations hold -/

section Relations

variable [DecidableEq I]

theorem sigLQ_cycDotR (i : I) (μ : X) : sigLQ RD k sc (relation k (.cycDotR i μ : Rel RD)) = 0 := by
  have H := dg_cycDotL RD k sc i (-wt RD μ [dn i])
  rw [relation, sigLQ_sub, rotDotR, downDot, sigLQ_of_mkD μ _ [dn i] [dn i] _ _ rfl rfl rfl,
    sigLQ_of_mkD μ _ [dn i] [dn i] _ _ rfl rfl rfl]
  sls_nf
  rw [← H, sub_self]

theorem sigLQ_cycDotL (i : I) (μ : X) : sigLQ RD k sc (relation k (.cycDotL i μ : Rel RD)) = 0 := by
  have H := dg_cycDotR RD k sc i (-wt RD μ [dn i])
  rw [relation, sigLQ_sub, rotDotL, downDot, sigLQ_of_mkD μ _ [dn i] [dn i] _ _ rfl rfl rfl,
    sigLQ_of_mkD μ _ [dn i] [dn i] _ _ rfl rfl rfl]
  sls_nf
  rw [← H, sub_self]

/-- The cyclicity `t_{ij}^{-1} · rotCrossR j i = downCross j i` is reflected to the cyclicity
`t_{ij}^{-1} · rotCrossL i j = downCross i j`. -/
theorem sigLQ_cycCrossR (j i : I) (μ : X) :
    sigLQ RD k sc (CL.relationCL RD k sc.withRone (.cycCrossR j i μ : Rel RD)) = 0 := by
  have H := dg_cycCrossL RD k sc i j (-wt RD μ [dn j, dn i])
  show sigLQ RD k sc ((((sc.t i j)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossR RD j i μ) -
    LinDiagram.of (downCross RD j i μ)) = 0
  rw [sigLQ_sub, sigLQ_smul, rotCrossR, downCross,
    sigLQ_of_mkD μ _ [dn i, dn j] [dn j, dn i] _ _ rfl rfl rfl,
    sigLQ_of_mkD μ _ [dn i, dn j] [dn j, dn i] _ _ rfl rfl rfl]
  sls_nf
  erw [H]
  rw [map_smul, smul_comm, sub_self]

/-- The cyclicity `t_{ji}^{-1} · rotCrossL j i = downCross j i` is reflected to the cyclicity
`t_{ji}^{-1} · rotCrossR i j = downCross i j`. -/
theorem sigLQ_cycCrossL (j i : I) (μ : X) :
    sigLQ RD k sc (CL.relationCL RD k sc.withRone (.cycCrossL j i μ : Rel RD)) = 0 := by
  have H := dg_cycCrossR RD k sc i j (-wt RD μ [dn j, dn i])
  show sigLQ RD k sc ((((sc.t j i)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossL RD j i μ) -
    LinDiagram.of (downCross RD j i μ)) = 0
  rw [sigLQ_sub, sigLQ_smul, rotCrossL, downCross,
    sigLQ_of_mkD μ _ [dn i, dn j] [dn j, dn i] _ _ rfl rfl rfl,
    sigLQ_of_mkD μ _ [dn i, dn j] [dn j, dn i] _ _ rfl rfl rfl]
  sls_nf
  erw [H]
  rw [map_smul, smul_comm, sub_self]

theorem sigLQ_downupEF (i j : I) (h : i ≠ j) (μ : X) :
    sigLQ RD k sc (CL.relationCL RD k sc.withRone (.downupEF i j h μ : Rel RD)) = 0 := by
  have H := dg_downupFE RD k sc j i (Ne.symm h) (-wt RD μ [up i, dn j])
  have e : -wt RD μ [up i, dn j] = -wt RD μ [dn j, up i] := by
    simp only [wt_cons, wt_nil]; abel
  show sigLQ RD k sc (LinDiagram.of (crossl RD i j μ ≫ crossr RD i j μ) -
    (sc.t j i : k) • LinDiagram.of (𝟙 _)) = 0
  rw [sigLQ_sub, sigLQ_smul, LinDiagram.of_comp, sigLQ_comp, crossl, crossr,
    sigLQ_of_mkD μ _ [dn j, up i] [up i, dn j] _ _ rfl rfl rfl,
    sigLQ_of_mkD μ _ [up i, dn j] [dn j, up i] _ _ e rfl rfl]
  sls_nf
  simp only [ite_eq_right (Ne.symm h), ite_eq_right h, Int.cast_one, one_smul]
  rw [TRQ_comp, NF.dg_comp (by schain) (by schain)]
  erw [H, map_smul, NF.dg_nil, TRQ_id]
  rw [show (LinDiagram.of (𝟙 (ob RD μ [up i, dn j])) : LinDiagram k _ _) = 𝟙 (Free.of k _) from rfl,
    sub_eq_zero]
  exact congrArg _ (sigLQ_id _).symm

theorem sigLQ_downupFE (i j : I) (h : i ≠ j) (μ : X) :
    sigLQ RD k sc (CL.relationCL RD k sc.withRone (.downupFE i j h μ : Rel RD)) = 0 := by
  have H := dg_downupEF RD k sc j i (Ne.symm h) (-wt RD μ [dn i, up j])
  have e : -wt RD μ [dn i, up j] = -wt RD μ [up j, dn i] := by
    simp only [wt_cons, wt_nil]; abel
  show sigLQ RD k sc (LinDiagram.of (crossr RD j i μ ≫ crossl RD j i μ) -
    (sc.t i j : k) • LinDiagram.of (𝟙 _)) = 0
  rw [sigLQ_sub, sigLQ_smul, LinDiagram.of_comp, sigLQ_comp, crossl, crossr,
    sigLQ_of_mkD μ _ [up j, dn i] [dn i, up j] _ _ rfl rfl rfl,
    sigLQ_of_mkD μ _ [dn i, up j] [up j, dn i] _ _ e rfl rfl]
  sls_nf
  simp only [ite_eq_right (Ne.symm h), ite_eq_right h, Int.cast_one, one_smul]
  rw [TRQ_comp, NF.dg_comp (by schain) (by schain)]
  erw [H, map_smul, NF.dg_nil, TRQ_id]
  rw [show (LinDiagram.of (𝟙 (ob RD μ [dn i, up j])) : LinDiagram k _ _) = 𝟙 (Free.of k _) from rfl,
    sub_eq_zero]
  exact congrArg _ (sigLQ_id _).symm

/-! ### Bubbles -/

omit [DecidableEq I] in
theorem TRQ_self {a b : Obj (psig RD)} (ea : a = a) (eb : b = b)
    (f : (pres RD k sc).obj a ⟶ (pres RD k sc).obj b) : TRQ RD k sc ea eb f = f := by
  simp [TRQ_apply]

/-- `σ̃` sends the clockwise bubble with `m` dots in the region `λ` to the counterclockwise bubble
with `m` dots in the region `-λ`. -/
theorem sigLQ_cwReal (lam : X) (i : I) (m : ℕ) :
    sigLQ RD k sc (LinDiagram.of (cwReal RD lam i m)) = NF.dg (pres RD k sc) (-lam) [] [] (ccwLs i m) := by
  rw [cwReal, sigLQ_of_mkD lam (-lam) [] [] _ _ rfl rfl rfl, sgnS_bubble, Int.cast_one, one_smul]
  refine (TRQ_self _ _ _).trans ?_
  rw [sls_append, sls_append, sls_replicate]
  show NF.dg (pres RD k sc) (-lam) [] [] ([([], .cup (dn i), [])] ++ List.replicate m ([], .dot (dn i), [up i]) ++
    [([], .cap (up i), [])]) = _
  dstepQ [] [([], .cap (up i), [])] [] [] (dg_dots_cupDn RD k sc i (-lam) m).symm
  simp [ccwLs]

/-- `σ̃` sends the counterclockwise bubble with `m` dots in the region `λ` to the clockwise
bubble with `m` dots in the region `-λ`. -/
theorem sigLQ_ccwReal (lam : X) (i : I) (m : ℕ) :
    sigLQ RD k sc (LinDiagram.of (ccwReal RD lam i m)) = NF.dg (pres RD k sc) (-lam) [] [] (cwLs i m) := by
  rw [ccwReal, sigLQ_of_mkD lam (-lam) [] [] _ _ rfl rfl rfl, sgnS_bubble, Int.cast_one, one_smul]
  refine (TRQ_self _ _ _).trans ?_
  rw [sls_append, sls_append, sls_replicate]
  show NF.dg (pres RD k sc) (-lam) [] [] ([([], .cup (up i), [])] ++ List.replicate m ([], .dot (up i), [dn i]) ++
    [([], .cap (dn i), [])]) = _
  dstepQ [] [([], .cap (dn i), [])] [] [] (dg_dots_cupUp RD k sc i (-lam) m).symm
  simp [cwLs]

variable (RD k sc) in
/-- `σ̃` on `END(1_λ)`: a ring homomorphism to `END(1_{-λ})`. -/
def sigEndQ (lam : X) : LEnd RD k (ob RD lam []) →+* End ((pres RD k sc).obj (ob RD (-lam) [])) :=
  (functorEndAlg k (freeLift k (sigFreeQ RD k sc)) (Free.of k (ob RD lam []))).toRingHom

theorem sigEndQ_apply (lam : X) (f : LEnd RD k (ob RD lam [])) : sigEndQ RD k sc lam f = sigLQ RD k sc f :=
  rfl

theorem sigLQ_ccwR (lam : X) (i : I) (m : ℤ) :
    sigLQ RD k sc (ccwR RD k lam i m) = (pres RD k sc).lin (cwR RD k (-lam) i m) := by
  unfold ccwR cwR
  split_ifs
  · rw [sigLQ_ccwReal, NF.lin_cwReal]
  · rw [sigLQ_zero, Presentation.lin_zero]

theorem sigLQ_cwR (lam : X) (i : I) (m : ℤ) :
    sigLQ RD k sc (cwR RD k lam i m) = (pres RD k sc).lin (ccwR RD k (-lam) i m) := by
  unfold ccwR cwR
  split_ifs
  · rw [sigLQ_cwReal, NF.lin_ccwReal]
  · rw [sigLQ_zero, Presentation.lin_zero]

/-- **`σ̃` sends the clockwise bubble with label `m` in the region `λ` to the counterclockwise
bubble with label `m` in the region `-λ`**, real or fake. -/
theorem sigLQ_cwL (lam : X) (i : I) (m : ℤ) :
    sigLQ RD k sc (cwL RD k lam i m) = NF.ccwU (pres RD k sc) (-lam) i m := by
  unfold NF.ccwU cwL ccwL
  simp only [ip_neg, ← sub_eq_add_neg]
  split_ifs
  · rw [sigLQ_cwReal, NF.lin_ccwReal]
  · show sigEndQ RD k sc lam _ = linEndQ RD k sc (-lam) _
    rw [map_grassInv, map_grassInv]
    congr 1
    funext a
    rw [sigEndQ_apply, sigLQ_ccwR]
    rfl
  · rw [sigLQ_zero, Presentation.lin_zero]

/-- **`σ̃` sends the counterclockwise bubble with label `m` in the region `λ` to the clockwise
bubble with label `m` in the region `-λ`**, real or fake. -/
theorem sigLQ_ccwL (lam : X) (i : I) (m : ℤ) :
    sigLQ RD k sc (ccwL RD k lam i m) = NF.cwU (pres RD k sc) (-lam) i m := by
  unfold NF.cwU cwL ccwL
  simp only [ip_neg, neg_neg, sub_neg_eq_add]
  split_ifs
  · rw [sigLQ_ccwReal, NF.lin_cwReal]
  · show sigEndQ RD k sc lam _ = linEndQ RD k sc (-lam) _
    rw [map_grassInv, map_grassInv]
    congr 1
    funext a
    rw [sigEndQ_apply, sigLQ_cwR]
    rfl
  · rw [sigLQ_zero, Presentation.lin_zero]

theorem sigLQ_cwNeg (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < ip RD i lam - 1) :
    sigLQ RD k sc (relation k (.cwNeg i lam α h : Rel RD)) = 0 := by
  rw [relation, sigLQ_cwReal]
  exact dg_ccwNeg RD k sc (-lam) i α (by rw [ip_neg]; omega)

theorem sigLQ_ccwNeg (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < -ip RD i lam - 1) :
    sigLQ RD k sc (relation k (.ccwNeg i lam α h : Rel RD)) = 0 := by
  rw [relation, sigLQ_ccwReal]
  exact dg_cwNeg RD k sc (-lam) i α (by rw [ip_neg]; omega)

theorem sigLQ_cwOne (i : I) (lam : X) (h : 1 ≤ ip RD i lam) :
    sigLQ RD k sc (relation k (.cwOne i lam h : Rel RD)) = 0 := by
  rw [relation, sigLQ_sub, sigLQ_cwReal, sub_eq_zero]
  have H := dg_ccwOne RD k sc (-lam) i (by rw [ip_neg]; omega)
  rw [ip_neg, neg_neg, NF.dg_nil] at H
  exact H.trans (sigLQ_id (RD := RD) (k := k) (ob RD lam [])).symm

theorem sigLQ_ccwOne (i : I) (lam : X) (h : ip RD i lam ≤ -1) :
    sigLQ RD k sc (relation k (.ccwOne i lam h : Rel RD)) = 0 := by
  rw [relation, sigLQ_sub, sigLQ_ccwReal, sub_eq_zero]
  have H := dg_cwOne RD k sc (-lam) i (by rw [ip_neg]; omega)
  rw [ip_neg, NF.dg_nil] at H
  exact H.trans (sigLQ_id (RD := RD) (k := k) (ob RD lam [])).symm

/-! ### Bubbles next to strands -/

/-- **`σ̃` moves a bubble to the right of a strand to its left** (and `λ ↦ -λ`). -/
theorem sigLQ_bubR (lam : X) (l : Letter I) (b : LEnd RD k (ob RD lam [])) :
    sigLQ RD k sc (bubR RD k lam [l] b) =
      TRQ RD k sc (trO lam (-wt RD lam [l]) [l] rfl) (trO lam (-wt RD lam [l]) [l] rfl)
        (NF.bubLU (pres RD k sc) (-wt RD lam [l]) l
          (TRQ RD k sc (region_bubR lam l) (region_bubR lam l) (sigLQ RD k sc b))) := by
  induction b using Finsupp.induction_linear with
  | zero => simp only [bubR_zero, sigLQ_zero, map_zero]
  | add f g hf hg =>
    rw [bubR_add, sigLQ_add, hf, hg, sigLQ_add' f g]
    simp only [NF.bubLU, map_add]
  | single d r =>
    have e : bubR RD k lam [l] (Finsupp.single d r) = Finsupp.single (Diagram.cast
        (Diagram.whisker d (ob RD lam [l]) [] (whiskerOK_right RD lam [l]))
        (whisker_right_eq RD lam [l]) (whisker_right_eq RD lam [l])) r := by
      simp only [bubR, LinDiagram.cast, LinDiagram.whisker, Finsupp.mapDomain_single]
    rw [e, sigLQ_single, sigLQ_single', Diagram.layers_cast, Diagram.layers_whisker,
      sgn_map_whisker]
    simp only [NF.bubLU, map_smul]
    congr 2
    rw [TRQ_diag, plcL_diag, TRQ_diag, reflD_cast, reflD_whisker d trivial]
    apply (pres RD k sc).diag_eq_of_layers_eq
    simp only [Diagram.layers_cast, Diagram.layers_whisker]
    congr 1
    funext L
    congr 1
    exact Obj.ext (by simp only [sigW, ob_start, wt_nil]; simp; abel) rfl

/-- **`σ̃` moves a bubble to the left of a strand to its right** (and `λ ↦ -λ`). -/
theorem sigLQ_bubL (μ : X) (l : Letter I) (b : LEnd RD k (ob RD (wt RD μ [l]) [])) :
    sigLQ RD k sc (bubL RD k μ [l] b) =
      TRQ RD k sc (trO μ (-wt RD μ [l]) [l] rfl) (trO μ (-wt RD μ [l]) [l] rfl)
        (NF.bubRU (pres RD k sc) (-wt RD μ [l]) l (sigLQ RD k sc b)) := by
  induction b using Finsupp.induction_linear with
  | zero => simp only [bubL_zero, sigLQ_zero, map_zero]
  | add f g hf hg =>
    rw [bubL_add, sigLQ_add, hf, hg, sigLQ_add' f g]
    simp only [NF.bubRU, map_add]
  | single d r =>
    have e : bubL RD k μ [l] (Finsupp.single d r) = Finsupp.single (Diagram.cast
        (Diagram.whisker d (ob RD (wt RD μ [l]) []) (wd RD μ [l]) (whiskerOK_left RD μ [l]))
        (whisker_left_eq RD μ [l]) (whisker_left_eq RD μ [l])) r := by
      simp only [bubL, LinDiagram.cast, LinDiagram.whisker, Finsupp.mapDomain_single]
    rw [e, sigLQ_single, sigLQ_single', Diagram.layers_cast, Diagram.layers_whisker,
      sgn_map_whisker]
    simp only [NF.bubRU, map_smul]
    congr 2
    rw [plcL_diag, TRQ_diag, reflD_cast, reflD_whisker d trivial]
    apply (pres RD k sc).diag_eq_of_layers_eq
    simp only [Diagram.layers_cast, Diagram.layers_whisker]
    congr 1
    funext L
    congr 1
    exact Obj.ext (by simp only [sigW, ob_start, wt_nil]; simp; abel) rfl

/-! ### Curls -/

theorem sigLQ_dots (lam : X) (l : Letter I) (m : ℕ) :
    sigLQ RD k sc (LinDiagram.of (dots RD lam [] l [] m)) =
      TRQ RD k sc (trO lam (-wt RD lam [l]) [l] rfl) (trO lam (-wt RD lam [l]) [l] rfl)
        (NF.dotsU (pres RD k sc) (-wt RD lam [l]) l m) := by
  rw [dots, sigLQ_of_mkD lam _ [l] [l] _ _ rfl rfl rfl]
  have hs : sgnS (List.replicate m (([] : List (Letter I)), Shape.dot l, ([] : List (Letter I)))) = 1 := by
    simp [sgnS, sgnSh, List.map_replicate, List.prod_replicate]
  rw [hs, Int.cast_one, one_smul, sls_replicate]
  rfl

omit [DecidableEq I] in
theorem ccwU_TRQ {ρ ρ' : X} (h : ob RD ρ [] = ob RD ρ' []) (i : I) (m : ℤ) :
    TRQ RD k sc h h (NF.ccwU (pres RD k sc) ρ' i m) = NF.ccwU (pres RD k sc) ρ i m := by
  obtain rfl : ρ = ρ' := congrArg Obj.start h
  exact TRQ_self _ _ _

omit [DecidableEq I] in
theorem cwU_TRQ {ρ ρ' : X} (h : ob RD ρ [] = ob RD ρ' []) (i : I) (m : ℤ) :
    TRQ RD k sc h h (NF.cwU (pres RD k sc) ρ' i m) = NF.cwU (pres RD k sc) ρ i m := by
  obtain rfl : ρ = ρ' := congrArg Obj.start h
  exact TRQ_self _ _ _

theorem sigLQ_curlR (i : I) (lam : X) : sigLQ RD k sc (relation k (.curlR i lam : Rel RD)) = 0 := by
  have H := dg_curlL RD k sc i (-wt RD lam [up i])
  have hip : ip RD i (wt RD (-wt RD lam [up i]) [up i]) = -ip RD i lam := by
    rw [show wt RD (-wt RD lam [up i]) [up i] = -lam by simp only [wt_cons, wt_nil]; abel, ip_neg]
  rw [hip] at H
  simp only [neg_neg] at H
  have hsum : sigLQ RD k sc (curlRHS RD k i lam) =
      -TRQ RD k sc (trO lam (-wt RD lam [up i]) [up i] rfl) (trO lam (-wt RD lam [up i]) [up i] rfl)
        (∑ f ∈ Finset.range (-ip RD i lam + 1).toNat,
          NF.bubLU (pres RD k sc) (-wt RD lam [up i]) (up i)
            (NF.ccwU (pres RD k sc) (wt RD (-wt RD lam [up i]) [up i]) i (ip RD i lam - 1 + f)) ≫
          NF.dotsU (pres RD k sc) (-wt RD lam [up i]) (up i) (-ip RD i lam - f).toNat) := by
    rw [curlRHS, sigLQ_neg, sigLQ_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [sigLQ_comp, sigLQ_bubR, sigLQ_cwL, sigLQ_dots, TRQ_comp, ccwU_TRQ]
  rw [relation, sigLQ_sub, curlR, sigLQ_of_mkD lam _ [up i] [up i] _ _ rfl rfl rfl, hsum]
  sls_nf
  rw [H, sub_neg_eq_add]
  exact neg_add_cancel _

theorem sigLQ_curlL (i : I) (μ : X) : sigLQ RD k sc (relation k (.curlL i μ : Rel RD)) = 0 := by
  have H := dg_curlR RD k sc i (-wt RD μ [up i])
  have hip : ip RD i (-wt RD μ [up i]) = -ip RD i (wt RD μ [up i]) := ip_neg i _
  rw [hip] at H
  simp only [neg_neg] at H
  have hsum : sigLQ RD k sc (curlLHS RD k i μ) =
      TRQ RD k sc (trO μ (-wt RD μ [up i]) [up i] rfl) (trO μ (-wt RD μ [up i]) [up i] rfl)
        (∑ g ∈ Finset.range (ip RD i (wt RD μ [up i]) + 1).toNat,
          NF.bubRU (pres RD k sc) (-wt RD μ [up i]) (up i)
            (NF.cwU (pres RD k sc) (-wt RD μ [up i]) i (-ip RD i (wt RD μ [up i]) - 1 + g)) ≫
          NF.dotsU (pres RD k sc) (-wt RD μ [up i]) (up i) (ip RD i (wt RD μ [up i]) - g).toNat) := by
    rw [curlLHS, sigLQ_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [sigLQ_comp, sigLQ_bubL, sigLQ_ccwL, sigLQ_dots, TRQ_comp]
  rw [relation, sigLQ_sub, curlL, sigLQ_of_mkD μ _ [up i] [up i] _ _ rfl rfl rfl, hsum]
  sls_nf
  rw [H, map_neg, neg_neg]
  exact sub_self _

/-! ### The decompositions of `1_{EF1_λ}` and `1_{FE1_λ}` -/

omit [DecidableEq I] in
theorem TRQ_comp_mid {a a' b c c' : Obj (psig RD)} (ea : a = a') (eb : b = b) (ec : c = c')
    (f : (pres RD k sc).obj a' ⟶ (pres RD k sc).obj b) (x : (pres RD k sc).obj b ⟶ (pres RD k sc).obj b)
    (g : (pres RD k sc).obj b ⟶ (pres RD k sc).obj c') :
    TRQ RD k sc ea eb f ≫ x ≫ TRQ RD k sc eb ec g = TRQ RD k sc ea ec (f ≫ x ≫ g) := by
  subst ea ec; simp [TRQ_apply]

theorem sigLQ_of_dotCapEF (i : I) (lam : X) (h : -lam = -wt RD lam [up i, dn i]) (m : ℕ) :
    sigLQ RD k sc (LinDiagram.of (dotCapEF RD lam i m)) =
      TRQ RD k sc (trO lam (-lam) [up i, dn i] h) (trO lam (-lam) [] rfl)
        (NF.dg (pres RD k sc) (-lam) [dn i, up i] [] (dotCapFELs i m)) := by
  rw [dotCapEF, sigLQ_of_mkD lam (-lam) [dn i, up i] [] _ _ h rfl rfl,
    sgnS_dots_cap m _ _ ⟨_, rfl⟩ ⟨_, rfl⟩, Int.cast_one, one_smul,
    sls_append, sls_replicate]
  congr 1
  exact (dg_dots_cap_up RD k sc (-lam) i m).symm

theorem sigLQ_of_cupDotEF (i : I) (lam : X) (h : -lam = -wt RD lam [up i, dn i]) (m : ℕ) :
    sigLQ RD k sc (LinDiagram.of (cupDotEF RD lam i m)) =
      TRQ RD k sc (trO lam (-lam) [] rfl) (trO lam (-lam) [up i, dn i] h)
        (NF.dg (pres RD k sc) (-lam) [] [dn i, up i] (cupDotFELs i m)) := by
  rw [cupDotEF, sigLQ_of_mkD lam (-lam) [] [dn i, up i] _ _ rfl rfl rfl,
    sgnS_cup_dots m _ _ ⟨_, rfl⟩ ⟨_, rfl⟩, Int.cast_one, one_smul, sls_append, sls_replicate]
  congr 1
  exact (dg_dots_cupDn RD k sc i (-lam) m).symm

theorem sigLQ_of_dotCapFE (i : I) (lam : X) (h : -lam = -wt RD lam [dn i, up i]) (m : ℕ) :
    sigLQ RD k sc (LinDiagram.of (dotCapFE RD lam i m)) =
      TRQ RD k sc (trO lam (-lam) [dn i, up i] h) (trO lam (-lam) [] rfl)
        (NF.dg (pres RD k sc) (-lam) [up i, dn i] [] (dotCapEFLs i m)) := by
  rw [dotCapFE, sigLQ_of_mkD lam (-lam) [up i, dn i] [] _ _ h rfl rfl,
    sgnS_dots_cap m _ _ ⟨_, rfl⟩ ⟨_, rfl⟩, Int.cast_one, one_smul,
    sls_append, sls_replicate]
  congr 1
  exact dg_dots_cap_dn RD k sc (-lam) i m

theorem sigLQ_of_cupDotFE (i : I) (lam : X) (h : -lam = -wt RD lam [dn i, up i]) (m : ℕ) :
    sigLQ RD k sc (LinDiagram.of (cupDotFE RD lam i m)) =
      TRQ RD k sc (trO lam (-lam) [] rfl) (trO lam (-lam) [dn i, up i] h)
        (NF.dg (pres RD k sc) (-lam) [] [up i, dn i] (cupDotEFLs i m)) := by
  rw [cupDotFE, sigLQ_of_mkD lam (-lam) [] [up i, dn i] _ _ rfl rfl rfl,
    sgnS_cup_dots m _ _ ⟨_, rfl⟩ ⟨_, rfl⟩, Int.cast_one, one_smul, sls_append, sls_replicate]
  congr 1
  exact (dg_dots_cupUp RD k sc i (-lam) m).symm

theorem sigLQ_decompEF (i : I) (lam : X) :
    sigLQ RD k sc (relation k (.decompEF i lam : Rel RD)) = 0 := by
  have h1 : -lam = -wt RD lam [up i, dn i] := by simp
  have h2 : -lam = -wt RD lam [dn i, up i] := by simp
  have H := dg_decompFE RD k sc i (-lam)
  simp only [ip_neg, neg_neg] at H
  have hsum : sigLQ RD k sc (decompEFSum RD k i lam) =
      TRQ RD k sc (trO lam (-lam) [up i, dn i] h1) (trO lam (-lam) [up i, dn i] h1)
        (∑ f ∈ Finset.range (ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
          NF.dg (pres RD k sc) (-lam) [dn i, up i] [] (dotCapFELs i (f - g)) ≫
            NF.cwU (pres RD k sc) (-lam) i (-ip RD i lam - 1 + g) ≫
              NF.dg (pres RD k sc) (-lam) [] [dn i, up i] (cupDotFELs i ((ip RD i lam).toNat - 1 - f))) := by
    unfold decompEFSum
    rw [sigLQ_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [sigLQ_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [sigLQ_comp, sigLQ_comp, sigLQ_of_dotCapEF i lam h1, sigLQ_ccwL, sigLQ_of_cupDotEF i lam h1]
    exact TRQ_comp_mid _ _ _ _ _ _
  have hid : sigLQ RD k sc (LinDiagram.of (𝟙 (ob RD lam [up i, dn i]))) =
      TRQ RD k sc (trO lam (-lam) [up i, dn i] h1) (trO lam (-lam) [up i, dn i] h1)
        (NF.dg (pres RD k sc) (-lam) [dn i, up i] [dn i, up i] []) := by
    rw [NF.dg_nil]; exact (sigLQ_id _).trans (TRQ_id _).symm
  have hcross : sigLQ RD k sc (LinDiagram.of (crossl RD i i lam)) ≫
      sigLQ RD k sc (LinDiagram.of (crossr RD i i lam)) =
      TRQ RD k sc (trO lam (-lam) [up i, dn i] h1) (trO lam (-lam) [up i, dn i] h1)
        (NF.dg (pres RD k sc) (-lam) [dn i, up i] [dn i, up i] (crossrL i i ++ crosslL i i)) := by
    rw [crossl, crossr, sigLQ_of_mkD lam (-lam) [dn i, up i] [up i, dn i] _ _ h1 rfl rfl,
      sigLQ_of_mkD lam (-lam) [up i, dn i] [dn i, up i] _ _ h2 rfl rfl]
    sls_nf
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, TRQ_comp,
      NF.dg_comp (by schain) (by schain)]
    rfl
  rw [relation, sigLQ_sub, sigLQ_add, hid, LinDiagram.of_comp, sigLQ_comp, hcross, hsum]
  refine (TRQ_add_sub _ _ _ _ _).trans ?_
  rw [TRQ_eq_zero, H]
  abel

theorem sigLQ_decompFE (i : I) (lam : X) :
    sigLQ RD k sc (relation k (.decompFE i lam : Rel RD)) = 0 := by
  have h1 : -lam = -wt RD lam [dn i, up i] := by simp
  have h2 : -lam = -wt RD lam [up i, dn i] := by simp
  have H := dg_decompEF RD k sc i (-lam)
  simp only [ip_neg, neg_neg] at H
  have hsum : sigLQ RD k sc (decompFESum RD k i lam) =
      TRQ RD k sc (trO lam (-lam) [dn i, up i] h1) (trO lam (-lam) [dn i, up i] h1)
        (∑ f ∈ Finset.range (-ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
          NF.dg (pres RD k sc) (-lam) [up i, dn i] [] (dotCapEFLs i (f - g)) ≫
            NF.ccwU (pres RD k sc) (-lam) i (ip RD i lam - 1 + g) ≫
              NF.dg (pres RD k sc) (-lam) [] [up i, dn i] (cupDotEFLs i ((-ip RD i lam).toNat - 1 - f))) := by
    unfold decompFESum
    rw [sigLQ_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [sigLQ_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [sigLQ_comp, sigLQ_comp, sigLQ_of_dotCapFE i lam h1, sigLQ_cwL, sigLQ_of_cupDotFE i lam h1]
    exact TRQ_comp_mid _ _ _ _ _ _
  have hid : sigLQ RD k sc (LinDiagram.of (𝟙 (ob RD lam [dn i, up i]))) =
      TRQ RD k sc (trO lam (-lam) [dn i, up i] h1) (trO lam (-lam) [dn i, up i] h1)
        (NF.dg (pres RD k sc) (-lam) [up i, dn i] [up i, dn i] []) := by
    rw [NF.dg_nil]; exact (sigLQ_id _).trans (TRQ_id _).symm
  have hcross : sigLQ RD k sc (LinDiagram.of (crossr RD i i lam)) ≫
      sigLQ RD k sc (LinDiagram.of (crossl RD i i lam)) =
      TRQ RD k sc (trO lam (-lam) [dn i, up i] h1) (trO lam (-lam) [dn i, up i] h1)
        (NF.dg (pres RD k sc) (-lam) [up i, dn i] [up i, dn i] (crosslL i i ++ crossrL i i)) := by
    rw [crossr, crossl, sigLQ_of_mkD lam (-lam) [up i, dn i] [dn i, up i] _ _ h1 rfl rfl,
      sigLQ_of_mkD lam (-lam) [dn i, up i] [up i, dn i] _ _ h2 rfl rfl]
    sls_nf
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, TRQ_comp,
      NF.dg_comp (by schain) (by schain)]
    rfl
  rw [relation, sigLQ_sub, sigLQ_add, hid, LinDiagram.of_comp, sigLQ_comp, hcross, hsum]
  refine (TRQ_add_sub _ _ _ _ _).trans ?_
  rw [TRQ_eq_zero, H]
  abel

end Relations

open KSig

/-! ## The upward KLR relations in `U` -/

section Upward

variable [DecidableEq I]

theorem sigLQ_upLin (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b)
    (hab : wt RD μ (ups b.word) = wt RD μ (ups a.word)) :
    sigLQ RD k sc (upLin RD k μ f) =
      TRQ RD k sc (obj_ups μ a) (by rw [obj_ups μ b, hab]; rfl)
        ((upFunctor RD k sc (-wt RD μ (ups a.word))).map (ksL (CL.qCL sc) f)) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [upLin, Finsupp.mapDomain_zero, sigLQ_zero,
      show ksL (CL.qCL sc) (0 : (a ⟶ b) →₀ k) = 0 from Functor.map_zero _ _ _,
      Functor.map_zero, map_zero]
  | add f g hf hg =>
    rw [upLin, Finsupp.mapDomain_add, ← upLin, ← upLin, sigLQ_add, hf, hg]
    rw [show ksL (CL.qCL sc) (f + g : (a ⟶ b) →₀ k) = ksL (CL.qCL sc) f +
      ksL (CL.qCL sc) g from Functor.map_add _, Functor.map_add, map_add]
  | single d r =>
    rw [upLin, Finsupp.mapDomain_single, sigLQ_single', layers_upDiag,
      show ksL (CL.qCL sc) (Finsupp.single d r : (a ⟶ b) →₀ k) =
        r • ((ksgn (Diagram.layers d) : ℤ) : k) •
          (KLR.Diagram.pres k (CL.qCL sc)).diag (ksD d) from freeLift_map_single _ d r,
      Functor.map_smul, Functor.map_smul, upFunctor_diag, map_smul, map_smul]
    have hs : Sig.sgn ((Diagram.layers d).map (upLay RD μ)) = ksgn (Diagram.layers d) := by
      simp only [Sig.sgn, ksgn, List.map_map, Function.comp_def, sgnG_upLay]
    rw [hs, TRQ_diag]
    congr 2
    apply (pres RD k sc).diag_eq_of_layers_eq
    simp only [layers_reflD, layers_upDiag, Diagram.layers_cast, ksD, Diagram.layers_mk,
      List.map_map]
    refine List.map_congr_left fun L hL => ?_
    obtain ⟨_, l, g, rr⟩ := L
    simp only [Function.comp_apply, upLay, klay, rlay_lay, sig_shape_upShape, upShape_dom]
    have hw := (chain_wsum RD (Diagram.chain d)).2 _ hL
    simp only [KLR.Diagram.Layer.dom_word'] at hw
    congr 1
    · rw [← ups_append, ← ups_append, wt_ups, wt_ups, hw]
      rfl
    · simp [ups, List.map_reverse]
    · simp [ups, List.map_reverse]

theorem sigLQ_klr (μ : X) (r : KLR.Diagram.Rel I) :
    sigLQ RD k sc (CL.relationCL RD k sc.withRone (.klr μ r : Rel RD)) = 0 := by
  rw [show CL.relationCL RD k sc.withRone (.klr μ r) =
      upLin RD k μ (KLR.Diagram.relation k (CL.qCL sc) r) from rel_klr RD k sc μ r,
    sigLQ_upLin μ _ (by rw [wt_ups, wt_ups, wsum_relation_cod]),
    ksL_relation_of_symm k (fun a b _ => (CL.rename_swap_qCL sc b a).symm) r,
    Functor.map_zero, map_zero]

end Upward


/-! ## The zigzag relations and the interchange law -/

section Zigzag

variable [DecidableEq I]

/-- The reflection of the left zigzag of `c` is the right zigzag of `⟨c.l*, -c.r⟩`. -/
theorem sigLQ_zigL (c : Col I X) :
    sigLQ RD k sc (LinDiagram.of (Pivotal.zigL (inv RD).toColourDuality c)) = 𝟙 _ := by
  rw [sigLQ_of, show sgn (Diagram.layers (Pivotal.zigL (inv RD).toColourDuality c)) = 1 from rfl,
    Int.cast_one, one_smul]
  have hw : word RD [c] = [(inv RD).dual ⟨c.l.dual, -c.r⟩] := by
    show [col c] = _; rw [col_eq_dual]
  refine (pres RD k sc).diag_eq_id_of_layers _
    (Pivotal.zigR (inv RD).toColourDuality ⟨c.l.dual, -c.r⟩) (Obj.ext rfl hw) ?_
    ((zigzags RD k sc) _).2
  simp only [layers_reflD, Pivotal.zigL, Pivotal.zigR, Diagram.layers_leftZigzag,
    Diagram.layers_rightZigzag, Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, Layer.wl, Layer.wr]
  refine List.cons_eq_cons.2 ⟨Layer.ext rfl hw rfl rfl,
    List.cons_eq_cons.2 ⟨Layer.ext rfl rfl rfl hw, rfl⟩⟩

/-- The reflection of the right zigzag of `c` is the left zigzag of `⟨c.l*, -c.r⟩`. -/
theorem sigLQ_zigR (c : Col I X) :
    sigLQ RD k sc (LinDiagram.of (Pivotal.zigR (inv RD).toColourDuality c)) = 𝟙 _ := by
  rw [sigLQ_of, show sgn (Diagram.layers (Pivotal.zigR (inv RD).toColourDuality c)) = 1 from rfl,
    Int.cast_one, one_smul]
  have hw : word RD [(inv RD).dual c] = [⟨c.l.dual, -c.r⟩] := by
    show [col ((inv RD).dual c)] = _; rw [col_dual_eq]
  refine (pres RD k sc).diag_eq_id_of_layers _
    (Pivotal.zigL (inv RD).toColourDuality ⟨c.l.dual, -c.r⟩) (Obj.ext (region_dual c) hw) ?_
    ((zigzags RD k sc) _).1
  simp only [layers_reflD, Pivotal.zigL, Pivotal.zigR, Diagram.layers_leftZigzag,
    Diagram.layers_rightZigzag, Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, Layer.wl, Layer.wr]
  refine List.cons_eq_cons.2 ⟨Layer.ext (region_dual c) rfl rfl hw,
    List.cons_eq_cons.2 ⟨Layer.ext (region_dual c) hw rfl rfl, rfl⟩⟩

/-- The reflection of the interchange law is the interchange law (with the generators
exchanged). -/
theorem sigLQ_interchange (x : InterchangeData (psig RD)) (hx : x.Valid) :
    sigLQ RD k sc (InterchangeData.rel k hx) = 0 := by
  obtain ⟨start, g, mid, h⟩ := x
  have g₁ : start = (psig RD).left g := hx.gh₁.left_end
  have g₂ : (psig RD).endR ((psig RD).left g) ((psig RD).dom g) = (psig RD).right g :=
    hx.gh₁.dom_end
  have g₃ : (psig RD).endR ((psig RD).left g) ((psig RD).cod g) = (psig RD).right g :=
    hx.gh₁.cod_end
  have h₁ : (psig RD).endR start ((psig RD).cod g ++ mid) = (psig RD).left h := hx.gh₂.left_end
  have h₂ : (psig RD).endR ((psig RD).left h) ((psig RD).dom h) = (psig RD).right h :=
    hx.gh₂.dom_end
  have h₃ : (psig RD).endR ((psig RD).left h) ((psig RD).cod h) = (psig RD).right h :=
    hx.gh₂.cod_end
  have eg : (psig RD).endR ((psig RD).right g) mid = (psig RD).left h := by
    rw [Signature.endR_append, g₁, g₃] at h₁; exact h₁
  have e₁ : eR (RD := RD) ((psig RD).right g) (mid ++ (psig RD).dom h) = rR (RD := RD) h := by
    show (psig RD).endR _ _ = _
    rw [Signature.endR_append, eg]; exact h₂
  have e₂ : eR (RD := RD) ((psig RD).right g) (mid ++ (psig RD).cod h) = rR (RD := RD) h := by
    show (psig RD).endR _ _ = _
    rw [Signature.endR_append, eg]; exact h₃
  have e₃ : eR (RD := RD) start ((psig RD).dom g ++ mid ++ (psig RD).dom h) = rR (RD := RD) h := by
    show (psig RD).endR _ _ = _
    rw [Signature.endR_append, Signature.endR_append, g₁, g₂, eg]; exact h₂
  have e₄ : eR (RD := RD) start ((psig RD).cod g ++ mid ++ (psig RD).cod h) =
      rR (RD := RD) h := by
    show (psig RD).endR _ _ = _
    rw [Signature.endR_append, Signature.endR_append, g₁, g₃, eg]; exact h₃
  let x : InterchangeData (psig RD) := ⟨start, g, mid, h⟩
  let x' : InterchangeData (psig RD) := ⟨-rR (RD := RD) h, gen h, word RD mid, gen g⟩
  have f₁ : x'.gh₁ = rlay x.hg₁ := by
    simp [x, x', InterchangeData.gh₁, InterchangeData.hg₁, rlay, gen_dom, word_append, word_nil']
  have f₂ : x'.gh₂ = rlay x.hg₂ := by
    simp only [x, x', InterchangeData.gh₂, InterchangeData.hg₂, rlay, gen_cod, word_append]
    rw [e₂]; rfl
  have f₃ : x'.hg₁ = rlay x.gh₁ := by
    simp only [x, x', InterchangeData.hg₁, InterchangeData.gh₁, rlay, gen_dom, word_append]
    rw [e₁]; rfl
  have f₄ : x'.hg₂ = rlay x.gh₂ := by
    simp [x, x', InterchangeData.hg₂, InterchangeData.gh₂, rlay, gen_cod, word_append, word_nil']
  have hx' : x'.Valid := ⟨f₁ ▸ rlay_valid hx.hg₁, f₂ ▸ rlay_valid hx.hg₂, f₃ ▸ rlay_valid hx.gh₁,
    f₄ ▸ rlay_valid hx.gh₂⟩
  have hw : x'.dom.WhiskerOK (Obj.nil x'.start) [] := ⟨trivial, rfl, trivial⟩
  have ha : x'.dom.whisker (Obj.nil x'.start) [] = obj RD x.dom :=
    Obj.ext (by
        show -rR (RD := RD) h =
          -eR (RD := RD) start ((psig RD).dom g ++ mid ++ (psig RD).dom h)
        rw [e₃])
      (by simp [x', x, InterchangeData.dom, Obj.whisker, Obj.nil, gen_dom, word_append])
  have hb : x'.cod.whisker (Obj.nil x'.start) [] = obj RD x.cod :=
    Obj.ext (by
        show -rR (RD := RD) h =
          -eR (RD := RD) start ((psig RD).cod g ++ mid ++ (psig RD).cod h)
        rw [e₄])
      (by simp [x', x, InterchangeData.cod, Obj.whisker, Obj.nil, gen_cod, word_append])
  have key := (pres RD k sc).diag_interchange x' hx' (Obj.nil x'.start) [] hw ha hb
  have hsg : ∀ y : InterchangeData (psig RD), ((y.sign : ℤ) : k) = 1 := by
    intro y; simp [InterchangeData.sign, Signature.IsEven.odd_eq_false]
  rw [hsg, one_smul] at key
  have hs : sgn (Diagram.layers (InterchangeData.hgDiagram hx)) =
      sgn (Diagram.layers (InterchangeData.ghDiagram hx)) := by
    simp only [Sig.sgn, InterchangeData.ghDiagram, InterchangeData.hgDiagram, Diagram.layers_mk,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, InterchangeData.gh₁,
      InterchangeData.gh₂, InterchangeData.hg₁, InterchangeData.hg₂]
    ring
  have d₁ : (pres RD k sc).diag (reflD (InterchangeData.ghDiagram hx)) =
      (pres RD k sc).diag (Diagram.cast (Diagram.whisker (InterchangeData.hgDiagram hx')
        (Obj.nil x'.start) [] hw) ha hb) := by
    apply (pres RD k sc).diag_eq_of_layers_eq
    simp only [layers_reflD, InterchangeData.ghDiagram, InterchangeData.hgDiagram,
      Diagram.layers_mk, Diagram.layers_cast, Diagram.layers_whisker, List.map_cons,
      List.map_nil]
    rw [show (⟨start, g, mid, h⟩ : InterchangeData (psig RD)) = x from rfl, ← f₃, ← f₄]
    simp [Layer.whisker, Obj.nil]
    exact ⟨rfl, rfl⟩
  have d₂ : (pres RD k sc).diag (reflD (InterchangeData.hgDiagram hx)) =
      (pres RD k sc).diag (Diagram.cast (Diagram.whisker (InterchangeData.ghDiagram hx')
        (Obj.nil x'.start) [] hw) ha hb) := by
    apply (pres RD k sc).diag_eq_of_layers_eq
    simp only [layers_reflD, InterchangeData.ghDiagram, InterchangeData.hgDiagram,
      Diagram.layers_mk, Diagram.layers_cast, Diagram.layers_whisker, List.map_cons,
      List.map_nil]
    rw [show (⟨start, g, mid, h⟩ : InterchangeData (psig RD)) = x from rfl, ← f₁, ← f₂]
    simp [Layer.whisker, Obj.nil]
    exact ⟨rfl, rfl⟩
  rw [InterchangeData.rel, sigLQ_sub, sigLQ_smul, sigLQ_of, sigLQ_of, hsg, one_smul, hs, d₁, d₂, key,
    sub_self]

end Zigzag


/-! ## The 2-functor `σ̃ : U → U^op` -/

section Functor

variable [DecidableEq I]

/-- **Every relation of `U_Q(g)`, reflected across the `y`-axis with `λ ↦ -λ` and the sign
`-1` on crossings of equally labelled strands, holds in `U_Q(g)`**, with the same scalars. -/
theorem sigLQ_relation (r : Rel RD) :
    sigLQ RD k sc (CL.relationCL RD k sc.withRone r) = 0 := by
  cases r with
  | cycDotR i μ => exact sigLQ_cycDotR i μ
  | cycDotL i μ => exact sigLQ_cycDotL i μ
  | cwNeg i lam α h => exact sigLQ_cwNeg i lam α h
  | ccwNeg i lam α h => exact sigLQ_ccwNeg i lam α h
  | cwOne i lam h => exact sigLQ_cwOne i lam h
  | ccwOne i lam h => exact sigLQ_ccwOne i lam h
  | curlR i lam => rw [relationCL_curlR]; exact sigLQ_curlR i lam
  | curlL i μ => rw [relationCL_curlL]; exact sigLQ_curlL i μ
  | decompEF i lam => rw [relationCL_decompEF]; exact sigLQ_decompEF i lam
  | decompFE i lam => rw [relationCL_decompFE]; exact sigLQ_decompFE i lam
  | cycCrossR j i μ => exact sigLQ_cycCrossR j i μ
  | cycCrossL j i μ => exact sigLQ_cycCrossL j i μ
  | downupEF i j h μ => exact sigLQ_downupEF i j h μ
  | downupFE i j h μ => exact sigLQ_downupFE i j h μ
  | klr μ r => exact sigLQ_klr μ r

theorem sigLQ_rel (r : (pres RD k sc).Rel) : sigLQ RD k sc ((pres RD k sc).rel r) = 0 := by
  rcases r with ((e | c | c) | r)
  · exact e.elim
  · show sigLQ RD k sc (LinDiagram.of (Pivotal.zigL _ c) - LinDiagram.of (𝟙 _)) = 0
    rw [sigLQ_sub, sigLQ_zigL, sub_eq_zero]
    exact (sigLQ_id _).symm
  · show sigLQ RD k sc (LinDiagram.of (Pivotal.zigR _ c) - LinDiagram.of (𝟙 _)) = 0
    rw [sigLQ_sub, sigLQ_zigR, sub_eq_zero]
    exact (sigLQ_id _).symm
  · exact sigLQ_relation r

omit [DecidableEq I] in
theorem pres_dom_wfQ (r : (pres RD k sc).Rel) : ((pres RD k sc).dom r).WF := by
  rcases r with ((e | c | c) | r)
  · exact e.elim
  · exact Pivotal.colourObj_wf _ c
  · exact Pivotal.dualObj_wf _ c
  · cases r <;> exact ob_wf RD _ _

variable (RD k sc)

/-- The signed reflection on the free 2-category respects all the relations of `U_Q(g)`. -/
theorem sigFreeQ_respects : (pres RD k sc).Respects (sigFreeQ RD k sc) where
  rel r u v hw := sigLQ_whisker_eq_zero _ (pres_dom_wfQ r) (sigLQ_rel r) hw
  interchange x hx u v hw := by
    have hwf : x.dom.WF := by
      have := hx.gh₁.wf_dom
      simpa [Obj.WF, Layer.dom, InterchangeData.gh₁, InterchangeData.dom, List.append_assoc]
        using this
    exact sigLQ_whisker_eq_zero _ hwf (sigLQ_interchange x hx) hw

/-- **The symmetry `σ̃` of KL III §3.3.2 for Cautis–Lauda's `U_Q(g)`**: reflection of diagrams
across the `y`-axis, `λ ↦ -λ`, and the sign `-1` on every crossing of two strands with the same
label. It
reverses the order of 1-morphisms (`Sig.obj`) and preserves the order of composition of
2-morphisms. -/
def sigUQ : (pres RD k sc).Presented ⥤ (pres RD k sc).Presented :=
  (pres RD k sc).lift (sigFreeQ_respects RD k sc)

instance : (sigUQ RD k sc).Additive := by unfold sigUQ; infer_instance

instance : (sigUQ RD k sc).Linear k := by unfold sigUQ; infer_instance

variable {RD k sc}

@[simp] theorem sigUQ_obj (a : Obj (psig RD)) :
    (sigUQ RD k sc).obj ((pres RD k sc).obj a) = (pres RD k sc).obj (obj RD a) := rfl

theorem sigUQ_lin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (sigUQ RD k sc).map ((pres RD k sc).lin f) = sigLQ RD k sc f := by
  unfold sigUQ; rw [Presentation.lift_lin]

/-- `σ̃` on a diagram: the reflected diagram, with the sign `(-1)^{#ii-crossings}`. -/
theorem sigUQ_diag {a b : Obj (psig RD)} (d : a ⟶ b) :
    (sigUQ RD k sc).map ((pres RD k sc).diag d) =
      ((sgn (Diagram.layers d) : ℤ) : k) • (pres RD k sc).diag (reflD d) := by
  unfold sigUQ; rw [Presentation.lift_diag]; rfl

/-- `σ̃` on normal-form diagrams: the layers `(u, g, v)` become `(v^rev, Sig.shape g, u^rev)`,
the rightmost region becomes `ν = -(μ + s_X)`, and the diagram is multiplied by the sign
`(-1)^{#ii-crossings}`; the reflected objects are identified with normal forms by `Sig.trO`. -/
theorem sigUQ_dg (μ ν : X) {s t : List (Letter I)} (s' t' : List (Letter I))
    (ls : List (LayerData I)) (h : SChain s ls t) (hν : ν = -wt RD μ s) (hs : s.reverse = s')
    (ht : t.reverse = t') :
    (sigUQ RD k sc).map (NF.dg (pres RD k sc) μ s t ls) =
      ((sgnS ls : ℤ) : k) • TRQ RD k sc (hs ▸ trO μ ν s hν)
        (ht ▸ trO μ ν t (hν.trans (by rw [SChain.wt_eq RD μ h])))
        (NF.dg (pres RD k sc) ν s' t' (sls ls)) := by
  rw [NF.dg_of h, show (pres RD k sc).diag (mkD RD μ ls h) =
    (pres RD k sc).lin (LinDiagram.of (mkD RD μ ls h)) from rfl, sigUQ_lin]
  exact sigLQ_of_mkD μ ν s' t' ls h hν hs ht

/-- **`σ̃` reverses horizontal composition**: whiskering by `u` on the left and `v` on the right
becomes whiskering by the reflection of `v` on the left and the reflection of `u` on the right
(up to the canonical identification of objects). -/
theorem sigUQ_whisk {a b : Obj (psig RD)} (f : (pres RD k sc).obj a ⟶ (pres RD k sc).obj b)
    (ha : a.WF) (hs : b.start = a.start) (he : b.endR = a.endR) {u : Obj (psig RD)}
    {v : List (psig RD).Colour} (hw : a.WhiskerOK u v) :
    (sigUQ RD k sc).map ((pres RD k sc).whisk f u v) =
      eqToHom (congrArg (pres RD k sc).obj (obj_whisker hw.2.1).symm) ≫
        (pres RD k sc).whisk ((sigUQ RD k sc).map f) (sigW a v) (word RD u.word) ≫
          eqToHom (congrArg (pres RD k sc).obj (obj_whisker_cod hs he hw.2.1)) := by
  obtain ⟨g, rfl⟩ := (pres RD k sc).lin_surjective f
  rw [Presentation.whisk_lin, LinDiagram.whisk_of_ok _ hw, sigUQ_lin, sigUQ_lin,
    sigLQ_whisker g ha hs he hw]

/-- **`σ̃` preserves degrees.** -/
theorem sigUQ_homDeg {a b : Obj (psig RD)} {f : (pres RD k sc).obj a ⟶ (pres RD k sc).obj b} {t : ℤ}
    (hf : f ∈ (pres RD k sc).homDeg (deg RD) a b t) :
    (sigUQ RD k sc).map f ∈ (pres RD k sc).homDeg (deg RD) (obj RD a) (obj RD b) t := by
  obtain ⟨g, hg, rfl⟩ := Presentation.mem_homDeg_iff.1 hf
  clear hf
  rw [sigUQ_lin]
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    rw [sigLQ_single']
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    exact Presentation.diag_mem_homDeg' ((degree_reflD d).trans hd)
  | zero => rw [sigLQ_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [sigLQ_add' x y]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [sigLQ_smul]; exact Submodule.smul_mem _ r hx

/-- **`σ̃` sends the clockwise bubble with label `m` in the region `λ` to the counterclockwise
bubble with label `m` in the region `-λ`** (real and fake bubbles). -/
theorem sigUQ_cwU (lam : X) (i : I) (m : ℤ) :
    (sigUQ RD k sc).map (NF.cwU (pres RD k sc) lam i m) = NF.ccwU (pres RD k sc) (-lam) i m := by
  rw [NF.cwU, sigUQ_lin, sigLQ_cwL]

/-- **`σ̃` sends the counterclockwise bubble with label `m` in the region `λ` to the clockwise
bubble with label `m` in the region `-λ`** (real and fake bubbles). -/
theorem sigUQ_ccwU (lam : X) (i : I) (m : ℤ) :
    (sigUQ RD k sc).map (NF.ccwU (pres RD k sc) lam i m) = NF.cwU (pres RD k sc) (-lam) i m := by
  rw [NF.ccwU, sigUQ_lin, sigLQ_ccwL]

/-- The signed reflection of a linear combination of diagrams that vanishes in `U_Q(g)` vanishes
in `U_Q(g)`. -/
theorem sigLQ_eq_zero_of_lin {a b : Obj (psig RD)} {f : LinDiagram k a b}
    (hf : (pres RD k sc).lin f = 0) : sigLQ RD k sc f = 0 := by
  rw [← sigUQ_lin, hf, Functor.map_zero]

end Functor

end Categorification.KL3.Diagram.CLQ