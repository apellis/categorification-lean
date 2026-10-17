/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Presentation
import Categorification.Diagrams.CL.RescaleBasic
import Categorification.KLR.KL2.ScalarExtension
import Categorification.KLR.BaseChange

/-!
# Integral coefficients of the KL III presentation

Scalar compatibility for the relations of KL III, arXiv:0807.3250v1,
Definition 3.1. This is the presentation input to the integral descent in
§6.4, “Simple nondegeneracy observations”.
-/

noncomputable section
namespace Categorification.KL3.Diagram.IntegralScalars

open CategoryTheory StringDiagrams QuantumGroup UDot

universe u v w

variable (k : Type w) [CommRing k] {S : Signature} {a b c : Obj S}

/-- Extend the integer coefficients of a linear diagram, using the existing
free linear extension functor. -/
def coeff : LinDiagram ℤ a b →ₗ[ℤ] LinDiagram k a b :=
  (freeLift ℤ (Free.embedding k (Obj S))).mapLinearMap ℤ

@[simp] theorem coeff_sub (f g : LinDiagram ℤ a b) :
    coeff k (f - g) = coeff k f - coeff k g := (coeff k).map_sub f g

@[simp] theorem coeff_zero : coeff k (0 : LinDiagram ℤ a b) = 0 := (coeff k).map_zero

@[simp] theorem coeff_add (f g : LinDiagram ℤ a b) :
    coeff k (f + g) = coeff k f + coeff k g := (coeff k).map_add f g

@[simp] theorem coeff_neg (f : LinDiagram ℤ a b) : coeff k (-f) = -coeff k f :=
  (coeff k).map_neg f

@[simp] theorem coeff_sum {J : Type*} (s : Finset J) (f : J → LinDiagram ℤ a b) :
    coeff k (∑ i ∈ s, f i) = ∑ i ∈ s, coeff k (f i) := map_sum (coeff k) f s

@[simp] theorem coeff_single (g : a ⟶ b) (n : ℤ) :
    coeff k (Finsupp.single g n) = Finsupp.single g (n : k) := by
  change (freeLift ℤ (Free.embedding k (Obj S))).map _ = _
  rw [freeLift_map_single]
  change n • Finsupp.single g (1 : k) = Finsupp.single g (n : k)
  rw [Finsupp.smul_single, zsmul_eq_mul, mul_one]

@[simp] theorem coeff_of (g : a ⟶ b) : coeff k (LinDiagram.of g) = LinDiagram.of g :=
  freeLift_map_of (Free.embedding k (Obj S)) g

@[simp] theorem coeff_comp (f : LinDiagram ℤ a b) (g : LinDiagram ℤ b c) :
    coeff k (f ≫ g) = coeff k f ≫ coeff k g :=
  (freeLift ℤ (Free.embedding k (Obj S))).map_comp f g

@[simp] theorem coeff_whisk (f : LinDiagram ℤ a b) (u : Obj S) (v : List S.Colour) :
    coeff k (LinDiagram.whisk f u v) = LinDiagram.whisk (coeff k f) u v := by
  unfold LinDiagram.whisk
  split_ifs with h
  · induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      change coeff k (LinDiagram.whisker ((f : LinDiagram ℤ a b) + g) u v h) = _
      rw [LinDiagram.whisker_add, map_add, hf, hg, map_add, LinDiagram.whisker_add]
    | single f n =>
      erw [LinDiagram.whisker_single (R := ℤ), coeff_single, coeff_single,
        LinDiagram.whisker_single]
  · exact map_zero _

@[simp] theorem coeff_whisker (f : LinDiagram ℤ a b) (u : Obj S) (v : List S.Colour)
    (h : a.WhiskerOK u v) :
    coeff k (LinDiagram.whisker f u v h) = LinDiagram.whisker (coeff k f) u v h := by
  simpa only [LinDiagram.whisk_of_ok _ h] using coeff_whisk k f u v

@[simp] theorem coeff_cast {a' b' : Obj S} (f : LinDiagram ℤ a b)
    (ha : a = a') (hb : b = b') :
    coeff k (LinDiagram.cast f ha hb) = LinDiagram.cast (coeff k f) ha hb := by
  subst ha hb
  simp only [LinDiagram.cast_rfl]

/-- Coefficient extension on the endomorphism ring of a free diagram object. -/
def coeffEnd (a : Obj S) : End (Free.of ℤ a) →+* End (Free.of k a) where
  toFun := coeff k
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := coeff_of k (𝟙 a)
  map_mul' f g := coeff_comp k g f

@[simp] theorem coeffEnd_apply (f : LinDiagram ℤ a a) : coeffEnd k a f = coeff k f := rfl

/-- Evaluation of an integral dot polynomial commutes with coefficient change. -/
theorem coeff_lpoly {I : Type u} {a : Obj (KLR.Diagram.sig I)} {n : ℕ}
    (y : Fin n → (a ⟶ a)) (p : MvPolynomial (Fin n) ℤ) :
    coeff k (KLR.Diagram.lpoly ℤ y p) =
      KLR.Diagram.lpoly k y (MvPolynomial.map (Int.castRingHom k) p) := by
  have h := KLR.map_ncEval (Int.castRingHom k) (coeffEnd k a)
    (fun z => by simp) (fun i => LinDiagram.of (y i)) p
  simpa only [coeffEnd_apply, coeff_of] using h

private theorem coeff_sub_eq {f g : LinDiagram ℤ a b} {f' g' : LinDiagram k a b}
    (hf : coeff k f = f') (hg : coeff k g = g') : coeff k (f - g) = f' - g' :=
  (coeff_sub k f g).trans (congrArg₂ (fun x y : LinDiagram k a b => x - y) hf hg)

/-- All KLR relations appearing in the KL presentation have integral coefficients. -/
theorem coeff_klrRelation {I : Type u} (C : CartanDatum I) (r : KLR.Diagram.Rel I) :
    coeff k (KLR.Diagram.relation ℤ (KLR.klQ2 ℤ C) r) =
      KLR.Diagram.relation k (KLR.klQ2 k C) r := by
  cases r with
  | sqEq c => exact coeff_of k _
  | sqNe c d h =>
    apply coeff_sub_eq k (coeff_of k _)
    exact (coeff_lpoly k _ _).trans
      (congrArg (KLR.Diagram.lpoly k _) (KLR.map_klQ2 C (Int.castRingHom k) c d))
  | slideLEq c => exact coeff_sub_eq k (coeff_sub_eq k (coeff_of k _) (coeff_of k _)) (coeff_of k _)
  | slideLNe c d h => exact coeff_sub_eq k (coeff_of k _) (coeff_of k _)
  | slideREq c => exact coeff_sub_eq k (coeff_sub_eq k (coeff_of k _) (coeff_of k _)) (coeff_of k _)
  | slideRNe c d h => exact coeff_sub_eq k (coeff_of k _) (coeff_of k _)
  | braid c d e h => exact coeff_sub_eq k (coeff_of k _) (coeff_of k _)
  | braidQ c d h =>
    apply coeff_sub_eq k (coeff_sub_eq k (coeff_of k _) (coeff_of k _))
    exact (coeff_lpoly k _ _).trans
      (congrArg (KLR.Diagram.lpoly k _) ((KLR.map_qbar (Int.castRingHom k) _).trans
        (congrArg KLR.qbar (KLR.map_klQ2 C (Int.castRingHom k) c d))))

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)

@[simp] theorem coeff_cwR (μ : X) (i : I) (m : ℤ) :
    coeff k (cwR RD ℤ μ i m) = cwR RD k μ i m := by
  unfold cwR
  split_ifs <;> simp only [coeff_of, coeff_zero]

@[simp] theorem coeff_ccwR (μ : X) (i : I) (m : ℤ) :
    coeff k (ccwR RD ℤ μ i m) = ccwR RD k μ i m := by
  unfold ccwR
  split_ifs <;> simp only [coeff_of, coeff_zero]

@[simp] theorem coeff_ccwL (μ : X) (i : I) (m : ℤ) :
    coeff k (ccwL RD ℤ μ i m) = ccwL RD k μ i m := by
  unfold ccwL
  split_ifs
  · exact coeff_of _ _
  · rw [← coeffEnd_apply, CL.Rescale.grassInv_map_ringHom]
    simp only [coeffEnd_apply, coeff_cwR]
  · exact coeff_zero _

@[simp] theorem coeff_cwL (μ : X) (i : I) (m : ℤ) :
    coeff k (cwL RD ℤ μ i m) = cwL RD k μ i m := by
  unfold cwL
  split_ifs
  · exact coeff_of _ _
  · rw [← coeffEnd_apply, CL.Rescale.grassInv_map_ringHom]
    simp only [coeffEnd_apply, coeff_ccwR]
  · exact coeff_zero _

@[simp] theorem coeff_bubR (μ : X) (s : List (Letter I)) (f : LEnd RD ℤ (ob RD μ [])) :
    coeff k (bubR RD ℤ μ s f) = bubR RD k μ s (coeff k f) := by
  simp only [bubR, coeff_cast, coeff_whisker]

@[simp] theorem coeff_bubL (μ : X) (s : List (Letter I))
    (f : LEnd RD ℤ (ob RD (wt RD μ s) [])) :
    coeff k (bubL RD ℤ μ s f) = bubL RD k μ s (coeff k f) := by
  unfold bubL
  rw [coeff_cast]
  exact congrArg (fun z => LinDiagram.cast z (whisker_left_eq RD μ s) (whisker_left_eq RD μ s))
    (coeff_whisker k f _ _ _)

@[simp] theorem coeff_curlRHS (i : I) (μ : X) :
    coeff k (curlRHS RD ℤ i μ) = curlRHS RD k i μ := by
  simp only [curlRHS, coeff_neg, coeff_sum, coeff_comp, coeff_of, coeff_bubR, coeff_cwL]

@[simp] theorem coeff_curlLHS (i : I) (μ : X) :
    coeff k (curlLHS RD ℤ i μ) = curlLHS RD k i μ := by
  simp only [curlLHS, coeff_sum, coeff_comp, coeff_of, coeff_bubL, coeff_ccwL]

@[simp] theorem coeff_decompEFSum (i : I) (μ : X) :
    coeff k (decompEFSum RD ℤ i μ) = decompEFSum RD k i μ := by
  simp only [decompEFSum, coeff_sum, coeff_comp, coeff_of, coeff_ccwL]

@[simp] theorem coeff_decompFESum (i : I) (μ : X) :
    coeff k (decompFESum RD ℤ i μ) = decompFESum RD k i μ := by
  simp only [decompFESum, coeff_sum, coeff_comp, coeff_of, coeff_cwL]

@[simp] theorem coeff_upLin (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram ℤ a b) :
    coeff k (upLin RD ℤ μ f) = upLin RD k μ (coeff k f) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    change coeff k (0 : LinDiagram ℤ _ _) = (0 : LinDiagram k _ _)
    exact coeff_zero k
  | add f g hf hg =>
    have hZ : upLin RD ℤ μ ((f : LinDiagram ℤ a b) + g) =
        upLin RD ℤ μ f + upLin RD ℤ μ g := Finsupp.mapDomain_add
    have hK : upLin RD k μ (coeff k f + coeff k g) =
        upLin RD k μ (coeff k f) + upLin RD k μ (coeff k g) := Finsupp.mapDomain_add
    rw [hZ, coeff_add, coeff_add, hK, hf, hg]
  | single f n =>
    dsimp only [upLin]
    erw [Finsupp.mapDomain_single, coeff_single, coeff_single, Finsupp.mapDomain_single]
    rfl

/-- The explicit defining relations of KL III commute with integer coefficient extension. -/
theorem coeff_relation (r : Rel RD) :
    coeff k (relation ℤ r) = relation k r := by
  cases r with
  | cycDotR i μ => exact coeff_sub_eq k (coeff_of k _) (coeff_of k _)
  | cycDotL i μ => exact coeff_sub_eq k (coeff_of k _) (coeff_of k _)
  | cwNeg i μ n h => exact coeff_of k _
  | ccwNeg i μ n h => exact coeff_of k _
  | cwOne i μ h => exact coeff_sub_eq k (coeff_of k _) (coeff_of k _)
  | ccwOne i μ h => exact coeff_sub_eq k (coeff_of k _) (coeff_of k _)
  | curlR i μ => exact coeff_sub_eq k (coeff_of k _) (coeff_curlRHS k RD i μ)
  | curlL i μ => exact coeff_sub_eq k (coeff_of k _) (coeff_curlLHS k RD i μ)
  | decompEF i μ =>
    apply coeff_sub_eq k _ (coeff_decompEFSum k RD i μ)
    exact (coeff_add k _ _).trans (congrArg₂ (· + ·) (coeff_of k _) (coeff_of k _))
  | decompFE i μ =>
    apply coeff_sub_eq k _ (coeff_decompFESum k RD i μ)
    exact (coeff_add k _ _).trans (congrArg₂ (· + ·) (coeff_of k _) (coeff_of k _))
  | cycCrossR j i μ => exact coeff_sub_eq k (coeff_of k _) (coeff_of k _)
  | cycCrossL j i μ => exact coeff_sub_eq k (coeff_of k _) (coeff_of k _)
  | downupEF i j h μ => exact coeff_sub_eq k (coeff_of k _) (coeff_of k _)
  | downupFE i j h μ => exact coeff_sub_eq k (coeff_of k _) (coeff_of k _)
  | klr μ r =>
    exact (coeff_upLin k RD μ _).trans
      (congrArg (upLin RD k μ) (coeff_klrRelation k C r))

@[simp] theorem coeff_smul {a b : Obj S} (n : ℤ) (f : LinDiagram ℤ a b) :
    coeff k (n • f) = (n : k) • coeff k f :=
  map_intCast_smul (coeff k) ℤ k n f

/-- Interchange is preserved, including its integral sign. -/
theorem coeff_interchange (x : InterchangeData S) (hx : x.Valid) :
    coeff k (InterchangeData.rel ℤ hx) = InterchangeData.rel k hx := by
  unfold InterchangeData.rel
  rw [coeff_sub, coeff_of, coeff_smul, coeff_of]
  rfl

open Presentation

private theorem coeff_whisk_mem_of_eq (r : (pres RD k).AllRel)
    (f : LinDiagram ℤ r.dom r.cod) (he : coeff k f = r.rel)
    (u : Obj (psig RD)) (v : List (psig RD).Colour) (h : r.dom.WhiskerOK u v) :
    coeff k (LinDiagram.whisker f u v h) ∈
      (pres RD k).ideal (r.dom.whisker u v) (r.cod.whisker u v) := by
  rw [coeff_whisker, he]
  exact (pres RD k).whisker_rel_mem_ideal r u v h

private theorem coeff_whiskRel_mem (r : (pres RD ℤ).AllRel)
    (u : Obj (psig RD)) (v : List (psig RD).Colour) (h : r.dom.WhiskerOK u v) :
    coeff k (LinDiagram.whisker r.rel u v h) ∈
      (pres RD k).ideal (r.dom.whisker u v) (r.cod.whisker u v) := by
  cases r with
  | user r =>
    rcases r with (r | (c | c)) | r
    · exact r.elim
    · exact coeff_whisk_mem_of_eq k RD (.user (.inl (.inr (.inl c)))) _
        (coeff_sub_eq k (coeff_of k _) (coeff_of k _)) u v h
    · exact coeff_whisk_mem_of_eq k RD (.user (.inl (.inr (.inr c)))) _
        (coeff_sub_eq k (coeff_of k _) (coeff_of k _)) u v h
    · exact coeff_whisk_mem_of_eq k RD (.user (.inr r)) _ (coeff_relation k RD r) u v h
  | interchange x hx =>
    exact coeff_whisk_mem_of_eq k RD (.interchange x hx) _ (coeff_interchange k x hx) u v h

private theorem coeff_gen_mem {a b : Obj (psig RD)} {f : LinDiagram ℤ a b}
    (hf : (pres RD ℤ).IdealGen f) : coeff k f ∈ (pres RD k).ideal a b := by
  obtain ⟨r, u, v, h, pre, post⟩ := hf
  have he := (coeff_comp k pre (LinDiagram.whisker r.rel u v h ≫ post)).trans
    (congrArg (fun z => coeff k pre ≫ z) (coeff_comp k (LinDiagram.whisker r.rel u v h) post))
  exact he.symm ▸ (pres RD k).comp_mem_ideal _
    ((pres RD k).mem_ideal_comp (coeff_whiskRel_mem k RD r u v h) _)

/-- Extension of integer coefficients sends the defining tensor ideal into
the target tensor ideal. No linear independence is used. -/
theorem coeff_mem_ideal {a b : Obj (psig RD)} {f : LinDiagram ℤ a b}
    (hf : f ∈ (pres RD ℤ).ideal a b) : coeff k f ∈ (pres RD k).ideal a b := by
  have h : (pres RD ℤ).ideal a b ≤
      (((pres RD k).ideal a b).restrictScalars ℤ).comap (coeff k) := by
    exact Submodule.span_le.mpr fun _ hx => coeff_gen_mem k RD hx
  exact h hf

/-- The canonical integer-linear scalar map on the presented KL Hom modules. -/
def homMap (a b : Obj (psig RD)) :
    ((pres RD ℤ).obj a ⟶ (pres RD ℤ).obj b) →ₗ[ℤ]
      ((pres RD k).obj a ⟶ (pres RD k).obj b) :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun x => Quot.lift (fun f : LinDiagram ℤ a b => (pres RD k).lin (coeff k f))
      (fun f g h => by
        have h' : (pres RD ℤ).homRel f g := by
          rwa [HomRel.compClosure_eq_self] at h
        rw [lin_eq_iff, ← coeff_sub]
        exact coeff_mem_ideal k RD h') x
    map_zero' := by
      change (pres RD k).lin (coeff k (0 : LinDiagram ℤ a b)) = 0
      rw [coeff_zero, lin_zero]
    map_add' := fun x y => by
      obtain ⟨f, rfl⟩ := (pres RD ℤ).lin_surjective x
      obtain ⟨g, rfl⟩ := (pres RD ℤ).lin_surjective y
      rw [← lin_add]
      change (pres RD k).lin (coeff k (f + g)) = _
      rw [coeff_add, lin_add]
      rfl }

@[simp] theorem homMap_lin {a b : Obj (psig RD)} (f : LinDiagram ℤ a b) :
    homMap k RD a b ((pres RD ℤ).lin f) = (pres RD k).lin (coeff k f) := rfl

@[simp] theorem homMap_diag {a b : Obj (psig RD)} (f : a ⟶ b) :
    homMap k RD a b ((pres RD ℤ).diag f) = (pres RD k).diag f := by
  change (pres RD k).lin (coeff k (LinDiagram.of f)) = _
  rw [coeff_of]
  rfl

end Categorification.KL3.Diagram.IntegralScalars
