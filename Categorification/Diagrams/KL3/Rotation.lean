/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.MateCalculus
import Categorification.Diagrams.KL3.Cyclic
import Categorification.Diagrams.KL3.Pitchfork

/-!
# The rotation calculus of `U` in normal form

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1
(Definition 3.1: all 2-morphisms are cyclic) and §3.3.2 (paragraph "Rotation by 180°", eq.
(3.46); TeX label `sec_symm`).

The rotation by `180°` of a 2-morphism `f : E_s 1_μ ⟶ E_t 1_μ` of `U` is its mate
`f^* : E_{t*} 1_ν ⟶ E_{s*} 1_ν` (`ν = μ + s_X`) for the biadjunctions `E_s 1_μ ⊣⊢ E_{s*} 1_ν`
given by nested cups and caps (`biadjWord`), where `s* = rd s` is the reversed sequence of dual
letters. As all 2-morphisms of `U` are cyclic (`isCyclic`), the right and left mates agree.

This file computes the rotation of normal-form diagrams:

* `rotU μ ν s t hs ht`: the rotation, as a `k`-linear map
  `Hom(E_s 1_μ, E_t 1_μ) → Hom(E_{t*} 1_ν, E_{s*} 1_ν)`; it is contravariant (`rotU_comp`,
  `rotU_id`) and an involution (`rotU_rotU`);
* `rotU_dg`: **the rotation of a normal-form diagram is the diagram of rotated layers**, in
  reversed order: a layer `(u, g, v)` becomes `(v*, g^rot, u*)` (`rotLD`), where on generators
  (`rotSh`) the dot on `l` becomes the dot on `l*`, the crossing
  `(ε,i)(ε,j) ⟶ (ε,j)(ε,i)` becomes `(-ε,i)(-ε,j) ⟶ (-ε,j)(-ε,i)`, the cup `1 ⟶ l l*` becomes
  the cap `l l* ⟶ 1` (of `l*`) and the cap `l* l ⟶ 1` the cup `1 ⟶ l* l` (of `l*`).

The proof of `rotU_dg` reduces, by functoriality of mates and the whiskering lemmas
`IsDiag.rightMate_whiskerLeft`, `IsDiag.rightMate_whiskerRight`
(`Categorification.Diagrams.KL3.MateCalculus`), to the six generators: the rotated upward dot
and crossing are the downward ones by the cyclicity relations (3.3) and `eq_cyclic_cross-gen`;
the rotated downward dot and crossing are then the upward ones because rotating twice is the
identity (`rightMate_rightMate`, using cyclicity); the rotated cups and caps are caps and cups by
the zigzag relations (3.1), (3.2).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Bicategory

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Dual signed sequences -/

/-- The dual `t* = l_m* ⋯ l_1*` of a signed sequence `t = l_1 ⋯ l_m`. -/
def rd (t : List (Letter I)) : List (Letter I) := (t.map Letter.dual).reverse

@[simp] theorem rd_nil : rd ([] : List (Letter I)) = [] := rfl

@[simp] theorem rd_cons (l : Letter I) (t : List (Letter I)) : rd (l :: t) = rd t ++ [l.dual] := by
  simp [rd]

@[simp] theorem rd_append (a b : List (Letter I)) : rd (a ++ b) = rd b ++ rd a := by
  simp [rd]

@[simp] theorem rd_rd (t : List (Letter I)) : rd (rd t) = t := by
  simp [rd, List.map_reverse, List.map_map, Function.comp_def]

theorem rd_singleton (l : Letter I) : rd [l] = [l.dual] := rfl

@[simp] theorem length_rd (t : List (Letter I)) : (rd t).length = t.length := by simp [rd]

/-- Reading the dual sequence from the left end of `t` returns to the right end. -/
@[simp] theorem wt_rd (μ : X) (t : List (Letter I)) : wt RD (wt RD μ t) (rd t) = μ := by
  induction t with
  | nil => rfl
  | cons l t ih => simp [wt_append, ih]

theorem wt_rd_append (μ : X) (a b : List (Letter I)) :
    wt RD (wt RD μ (a ++ b)) (rd a) = wt RD μ b := by
  rw [wt_append, wt_rd]

theorem dualWord_wd (μ : X) (t : List (Letter I)) :
    (inv RD).toColourDuality.pivotal.dualWord (wd RD μ t) = wd RD (wt RD μ t) (rd t) := by
  induction t with
  | nil => rfl
  | cons l t ih =>
    rw [wd_cons, Signature.ColourDuality.dualWord_cons, ih, rd_cons, wd_append]
    simp only [wt_cons, wd_cons, wd_nil, Signature.ColourDuality.pivotal_dual]
    congr 2
    simp

/-! ## Objects as 1-morphisms of `U` -/

/-- The 1-morphism `E_t 1_μ` of `U`, from its left region `ν = μ + t_X` to `μ`. -/
def obH (μ ν : X) (t : List (Letter I)) (h : wt RD μ t = ν) : (⟨ν⟩ : U RD k) ⟶ ⟨μ⟩ :=
  ⟨ob RD μ t, h, ob_wf RD μ t, ob_endR RD μ t⟩

@[simp] theorem obH_obj (μ ν : X) (t : List (Letter I)) (h : wt RD μ t = ν) :
    (obH RD k μ ν t h).obj = ob RD μ t := rfl

theorem wt_rd_of (μ ν : X) (t : List (Letter I)) (h : wt RD μ t = ν) : wt RD ν (rd t) = μ := by
  subst h; exact wt_rd RD μ t

/-- The dual of `E_t 1_μ` is `E_{t*} 1_ν`. -/
theorem dual_obH (μ ν : X) (t : List (Letter I)) (h : wt RD μ t = ν) :
    (pres RD k).dualHom (inv RD).toColourDuality.pivotal (obH RD k μ ν t h) =
      obH RD k ν μ (rd t) (wt_rd_of RD μ ν t h) := by
  subst h
  exact Bicat.Hom.ext (Obj.ext (wt_rd RD μ t).symm (dualWord_wd RD μ t))

/-! ## The rotation of 2-morphisms -/

/-- The transport `P.obj x.obj = P.obj y.obj` along an equality of 1-morphisms of `U`. -/
theorem objEq {l m : U RD k} {x y : l ⟶ m} (h : x = y) :
    (pres RD k).obj (Bicat.Hom.obj x) = (pres RD k).obj (Bicat.Hom.obj y) :=
  congrArg (fun z => (pres RD k).obj (Bicat.Hom.obj z)) h

/-- The identity from 2-morphisms of the presented category to 2-morphisms of `U`, as a
`k`-linear map (the two `k`-module structures agree definitionally). -/
def toHC {l m : U RD k} (x x' : l ⟶ m) :
    ((pres RD k).obj x.obj ⟶ (pres RD k).obj x'.obj) →ₗ[k] (x ⟶ x') where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identity from 2-morphisms of `U` to 2-morphisms of the presented category. -/
def ofHC {l m : U RD k} (x x' : l ⟶ m) :
    (x ⟶ x') →ₗ[k] ((pres RD k).obj x.obj ⟶ (pres RD k).obj x'.obj) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The right mate for the nested cups and caps, as a `k`-linear map of the `Hom`-spaces of the
presented category. -/
def mateL {l m : U RD k} (x x' : l ⟶ m) :
    ((pres RD k).obj x.obj ⟶ (pres RD k).obj x'.obj) →ₗ[k]
      ((pres RD k).obj ((pres RD k).dualHom (inv RD).toColourDuality.pivotal x').obj ⟶
        (pres RD k).obj ((pres RD k).dualHom (inv RD).toColourDuality.pivotal x).obj) :=
  (ofHC RD k _ _).comp ((Biadjunction.rightMateLinearEquiv k (biadjWord RD k x)
    (biadjWord RD k x')).toLinearMap.comp (toHC RD k x x'))

theorem mateL_apply {l m : U RD k} (x x' : l ⟶ m)
    (f : (pres RD k).obj x.obj ⟶ (pres RD k).obj x'.obj) :
    mateL RD k x x' f = Biadjunction.rightMate (biadjWord RD k x) (biadjWord RD k x') f := rfl

theorem mateL_comp {l m : U RD k} (x x' x'' : l ⟶ m)
    (f : (pres RD k).obj x.obj ⟶ (pres RD k).obj x'.obj)
    (g : (pres RD k).obj x'.obj ⟶ (pres RD k).obj x''.obj) :
    mateL RD k x x'' (f ≫ g) = mateL RD k x' x'' g ≫ mateL RD k x x' f :=
  Biadjunction.rightMate_comp (biadjWord RD k x) (biadjWord RD k x') (biadjWord RD k x'')
    (f : x ⟶ x') (g : x' ⟶ x'')

theorem mateL_id {l m : U RD k} (x : l ⟶ m) : mateL RD k x x (𝟙 _) = 𝟙 _ :=
  Biadjunction.rightMate_id (biadjWord RD k x)

/-- **The rotation by `180°`** of a 2-morphism `f : E_s 1_μ ⟶ E_t 1_μ` of `U`, where
`ν = μ + s_X = μ + t_X`: its mate `E_{t*} 1_ν ⟶ E_{s*} 1_ν` for the biadjunctions given by the
nested cups and caps (KL III (3.46), `ζ ↦ ζ*`). -/
def rotU (μ ν : X) (s t : List (Letter I)) (hs : wt RD μ s = ν) (ht : wt RD μ t = ν) :
    ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) →ₗ[k]
      ((pres RD k).obj (ob RD ν (rd t)) ⟶ (pres RD k).obj (ob RD ν (rd s))) where
  toFun f := eqToHom (objEq RD k (dual_obH RD k μ ν t ht).symm) ≫
      mateL RD k (obH RD k μ ν s hs) (obH RD k μ ν t ht) f ≫
      eqToHom (objEq RD k (dual_obH RD k μ ν s hs))
  map_add' f g := by
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [map_smul, Linear.smul_comp, Linear.comp_smul]
    rfl

variable {RD k}

theorem rotU_apply (μ ν : X) (s t : List (Letter I)) (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)
    (f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    rotU RD k μ ν s t hs ht f = eqToHom (objEq RD k (dual_obH RD k μ ν t ht).symm) ≫
      mateL RD k (obH RD k μ ν s hs) (obH RD k μ ν t ht) f ≫
      eqToHom (objEq RD k (dual_obH RD k μ ν s hs)) := rfl

/-- The rotation is contravariant. -/
theorem rotU_comp (μ ν : X) (s r t : List (Letter I)) (hs : wt RD μ s = ν) (hr : wt RD μ r = ν)
    (ht : wt RD μ t = ν) (f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ r))
    (g : (pres RD k).obj (ob RD μ r) ⟶ (pres RD k).obj (ob RD μ t)) :
    rotU RD k μ ν s t hs ht (f ≫ g) = rotU RD k μ ν r t hr ht g ≫ rotU RD k μ ν s r hs hr f := by
  have h := mateL_comp RD k (obH RD k μ ν s hs) (obH RD k μ ν r hr) (obH RD k μ ν t ht) f g
  simp only [rotU_apply]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

theorem rotU_id (μ ν : X) (s : List (Letter I)) (hs : wt RD μ s = ν) :
    rotU RD k μ ν s s hs hs (𝟙 _) = 𝟙 _ := by
  have h := mateL_id RD k (obH RD k μ ν s hs)
  rw [rotU_apply]
  erw [h]
  simp

/-! ## Rotated generators and layers -/

/-- The rotation of the shape of a generator by `180°`. -/
def rotSh : Shape I → Shape I
  | .dot l => .dot l.dual
  | .cross ε i j => .cross (!ε) i j
  | .cup l => .cap l.dual
  | .cap l => .cup l.dual

@[simp] theorem rotSh_dot (l : Letter I) : rotSh (.dot l) = .dot l.dual := rfl
@[simp] theorem rotSh_cross (ε : Bool) (i j : I) : rotSh (.cross ε i j) = .cross (!ε) i j := rfl
@[simp] theorem rotSh_cup (l : Letter I) : rotSh (.cup l) = .cap l.dual := rfl
@[simp] theorem rotSh_cap (l : Letter I) : rotSh (.cap l) = .cup l.dual := rfl

theorem rotSh_dom (g : Shape I) : (rotSh g).dom = rd g.cod := by
  cases g <;> simp [rd_singleton]

theorem rotSh_cod (g : Shape I) : (rotSh g).cod = rd g.dom := by
  cases g <;> simp [rd_singleton]

theorem rotSh_rotSh (g : Shape I) : rotSh (rotSh g) = g := by
  cases g <;> simp

/-- The rotation of a layer datum: `(u, g, v) ↦ (v*, g^rot, u*)`. -/
def rotLD (x : LayerData I) : LayerData I := (rd x.2.2, rotSh x.2.1, rd x.1)

/-- The rotation of a normal-form diagram: the rotated layers, in reversed order. -/
def rotLs (ls : List (LayerData I)) : List (LayerData I) := (ls.map rotLD).reverse

@[simp] theorem rotLs_nil : rotLs ([] : List (LayerData I)) = [] := rfl

theorem rotLs_cons (x : LayerData I) (ls : List (LayerData I)) :
    rotLs (x :: ls) = rotLs ls ++ [rotLD x] := by
  simp [rotLs]

theorem rotLs_append (ls ms : List (LayerData I)) : rotLs (ls ++ ms) = rotLs ms ++ rotLs ls := by
  simp [rotLs]

theorem rotLs_rotLs (ls : List (LayerData I)) : rotLs (rotLs ls) = ls := by
  simp [rotLs, rotLD, List.map_reverse, List.map_map, Function.comp_def, rotSh_rotSh]

theorem sChain_rotLs {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    SChain (rd t) (rotLs ls) (rd s) := by
  induction ls generalizing s with
  | nil => exact congrArg rd (show s = t from h).symm
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    rw [rotLs_cons]
    refine (ih h).append ⟨?_, ?_⟩
    · simp [rotLD, rotSh_dom, List.append_assoc]
    · simp [rotLD, rotSh_cod, List.append_assoc]

/-! ## Classes of diagrams with given layers -/

variable (RD k) in
/-- The morphism `θ` of the presented category is the class of a diagram with the layers
`ls`. -/
def IsDg {a b : Obj (psig RD)} (θ : (pres RD k).obj a ⟶ (pres RD k).obj b)
    (ls : List (Layer (psig RD))) : Prop :=
  ∃ D : a ⟶ b, θ = (pres RD k).diag D ∧ Diagram.layers D = ls

theorem IsDg.toIsDiag {l m : U RD k} (x y : l ⟶ m)
    {θ : (pres RD k).obj x.obj ⟶ (pres RD k).obj y.obj} {ls : List (Layer (psig RD))}
    (h : IsDg RD k θ ls) : IsDiag (pres RD k) (show x ⟶ y from θ) ls := h

theorem IsDiag.toIsDg {l m : U RD k} {x y : l ⟶ m} {θ : x ⟶ y} {ls : List (Layer (psig RD))}
    (h : IsDiag (pres RD k) θ ls) :
    IsDg RD k (show (pres RD k).obj x.obj ⟶ (pres RD k).obj y.obj from θ) ls := h

theorem isDg_dg (μ : X) {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    IsDg RD k (dg RD k μ s t ls) (layList RD μ ls) :=
  ⟨mkD RD μ ls h, dg_of h, rfl⟩

theorem IsDg.eqToHom_comp {a a' b : Obj (psig RD)} (e : (pres RD k).obj a' = (pres RD k).obj a)
    {θ : (pres RD k).obj a ⟶ (pres RD k).obj b} {ls : List (Layer (psig RD))}
    (h : IsDg RD k θ ls) : IsDg RD k (eqToHom e ≫ θ) ls := by
  obtain rfl := (pres RD k).obj_injective e
  simpa using h

theorem IsDg.comp_eqToHom {a b b' : Obj (psig RD)} (e : (pres RD k).obj b = (pres RD k).obj b')
    {θ : (pres RD k).obj a ⟶ (pres RD k).obj b} {ls : List (Layer (psig RD))}
    (h : IsDg RD k θ ls) : IsDg RD k (θ ≫ eqToHom e) ls := by
  obtain rfl := (pres RD k).obj_injective e
  simpa using h

/-- A morphism which is the class of a diagram with the layers of a normal-form diagram `L₁`
is the class of a diagram with the layers of any `L₂` with the same class. -/
theorem IsDg.trans_dg {a b : Obj (psig RD)} {θ : (pres RD k).obj a ⟶ (pres RD k).obj b} {ν : X}
    {s t : List (Letter I)} {L₁ L₂ : List (LayerData I)} (hθ : IsDg RD k θ (layList RD ν L₁))
    (ea : a = ob RD ν s) (eb : b = ob RD ν t) (h₁ : SChain s L₁ t) (h₂ : SChain s L₂ t)
    (heq : dg RD k ν s t L₁ = dg RD k ν s t L₂) : IsDg RD k θ (layList RD ν L₂) := by
  subst ea eb
  obtain ⟨D, rfl, hD⟩ := hθ
  refine ⟨mkD RD ν L₂ h₂, ?_, rfl⟩
  rw [← dg_of h₂, ← heq, dg_of h₁]
  exact (pres RD k).diag_eq_of_layers_eq hD

/-- Two classes of diagrams with the same layers are equal, up to the identification of their
boundaries. -/
theorem IsDg.eq_eqToHom {a b a' b' : Obj (psig RD)} {θ : (pres RD k).obj a ⟶ (pres RD k).obj b}
    {θ' : (pres RD k).obj a' ⟶ (pres RD k).obj b'} {ls : List (Layer (psig RD))}
    (h : IsDg RD k θ ls) (h' : IsDg RD k θ' ls) (ea : a = a') (eb : b = b') :
    θ = eqToHom (congrArg (pres RD k).obj ea) ≫ θ' ≫
      eqToHom (congrArg (pres RD k).obj eb.symm) := by
  subst ea eb
  obtain ⟨D, rfl, hD⟩ := h
  obtain ⟨D', rfl, hD'⟩ := h'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (pres RD k).diag_eq_of_layers_eq (hD.trans hD'.symm)

/-! ## The rotations of the generators -/

/-- The mate of a normal-form diagram, as a list of layers: nested cups of `a` to the right of
`b*`, the layers of the diagram between `b*` and `a*`, nested caps of `b` to the left of `a*`. -/
theorem isDg_mateL_raw (ν μ : X) (a b : List (Letter I)) (ha : wt RD ν a = μ) (hb : wt RD ν b = μ)
    (ls : List (LayerData I)) (h : SChain a ls b) :
    IsDg RD k (mateL RD k (obH RD k ν μ a ha) (obH RD k ν μ b hb) (dg RD k ν a b ls))
      ((cupLayers (E := inv RD) μ (wd RD ν a)).map (·.wl (ob RD μ (rd b))) ++
        ((layList RD ν ls).map (·.wr (wd RD μ (rd a)))).map (·.wl (ob RD μ (rd b))) ++
        (capLayers (E := inv RD) ν (wd RD ν b)).map (·.wr (wd RD μ (rd a)))) := by
  have H := IsDiag.rightMate (biadjWord RD k (obH RD k ν μ a ha))
    (biadjWord RD k (obH RD k ν μ b hb))
    (isDiag_biadj_left_unit (zigzags RD k) _) (isDiag_biadj_left_counit (zigzags RD k) _)
    (isDg_dg (RD := RD) (k := k) ν h)
  have e₁ := congrArg Bicat.Hom.obj (dual_obH RD k ν μ b hb)
  have e₂ : ((pres RD k).dualHom (inv RD).toColourDuality.pivotal
      (obH RD k ν μ a ha)).obj.word = wd RD μ (rd a) := by
    rw [dual_obH]; rfl
  simp only [obH_obj] at e₁
  rw [e₁, e₂] at H
  exact H

/-! ### Nested cups and caps in normal form -/

/-- The nested cups `1 ⟶ a a*` in normal form. -/
def nCups : List (Letter I) → List (LayerData I)
  | [] => []
  | l :: a => ([], .cup l, []) :: (nCups a).map (whL [l] [l.dual])

/-- The nested caps `b* b ⟶ 1` in normal form. -/
def nCaps : List (Letter I) → List (LayerData I)
  | [] => []
  | l :: b => (rd b, .cap l, b) :: nCaps b

theorem sChain_nCups : ∀ a : List (Letter I), SChain [] (nCups a) (a ++ rd a)
  | [] => rfl
  | l :: a => by
    refine ⟨rfl, ?_⟩
    have := (sChain_nCups a).whisk [l] [l.dual]
    simpa [List.append_assoc] using this

theorem sChain_nCaps : ∀ b : List (Letter I), SChain (rd b ++ b) (nCaps b) []
  | [] => rfl
  | l :: b => ⟨by simp [List.append_assoc], by simpa using sChain_nCaps b⟩

variable (RD) in
theorem lay_wr_eq (μ ν' : X) (v x y : List (Letter I)) (g : Shape I) (hν : wt RD μ v = ν') :
    (lay RD ν' x g y).wr (wd RD μ v) = lay RD μ x g (y ++ v) := by
  subst hν
  refine Layer.ext ?_ ?_ ?_ ?_
  · simp [lay, Layer.wr, List.append_assoc, wt_append]
  · simp [lay, Layer.wr, List.append_assoc, wt_append]
  · simp [lay, Layer.wr, wt_append]
  · simp [lay, Layer.wr, wd_append]

variable (RD) in
theorem lay_wl_eq (μ ρ : X) (u x y : List (Letter I)) (g : Shape I)
    (hρ : wt RD μ (x ++ g.dom ++ y) = ρ) :
    (lay RD μ x g y).wl (ob RD ρ u) = lay RD μ (u ++ x) g y := by
  subst hρ
  refine Layer.ext ?_ ?_ ?_ ?_
  · simp [lay, Layer.wl, ob, List.append_assoc, wt_append]
  · simp [lay, Layer.wl, ob, List.append_assoc, wt_append, wd_append]
  · rfl
  · rfl

theorem cupLayers_wd (ν : X) : ∀ a : List (Letter I),
    cupLayers (E := inv RD) (wt RD ν a : X) (wd RD ν a) = layList RD (wt RD ν a) (nCups a)
  | [] => rfl
  | l :: a => by
    have ih := cupLayers_wd ν a
    have hm := (sChain_nCups a).wt_mem RD (wt RD ν a)
    simp only [wd_cons, cupLayers, nCups, layList_cons, ih]
    congr 1
    · refine Layer.ext rfl rfl ?_ rfl
      simp [lay, Shape.gen]
    · rw [show (sig0 RD).colourTgt (⟨l, wt RD ν a⟩ : Col I X) = wt RD ν a from rfl, ih]
      simp only [layList, List.map_map]
      refine List.map_congr_left fun x hx => ?_
      simp only [Function.comp_apply, whL]
      have e₁ : [((inv RD).dual ⟨l, wt RD ν a⟩ : Col I X)] =
          wd RD (wt RD ν (l :: a)) [l.dual] := by
        simp [inv_dual]
      have e₂ : (⟨(wt RD ν (l :: a) : X), [⟨l, wt RD ν a⟩]⟩ : Obj (psig RD)) =
          ob RD (wt RD ν a) [l] := rfl
      rw [e₁, lay_wr_eq RD _ (wt RD ν a) _ _ _ _ (by simp), e₂,
        lay_wl_eq RD _ _ _ _ _ _ ?_]
      have h₁ : wt RD (wt RD ν (l :: a)) [l.dual] = wt RD ν a := by simp
      rw [← List.append_assoc, wt_append, h₁, hm x hx]
      rfl

theorem capLayers_wd (ν : X) : ∀ b : List (Letter I),
    capLayers (E := inv RD) ν (wd RD ν b) = layList RD ν (nCaps b)
  | [] => rfl
  | l :: b => by
    have ih := capLayers_wd ν b
    simp only [wd_cons, capLayers, nCaps, layList_cons, ih]
    congr 1
    refine Layer.ext ?_ ?_ rfl ?_
    · simp [lay, Layer.wl, Layer.wr, wt_append]
    · simp only [lay, Layer.wl, Layer.wr, List.append_nil, dualWord_wd]
      congr 1
      simp [wt_append]
    · simp [lay, Layer.wl, Layer.wr]

/-- The mate of a normal-form diagram `ls : a ⟶ b`, in normal form, before straightening:
nested cups of `a` to the right of `b*`, then `ls` between `b*` and `a*`, then nested caps of
`b` to the left of `a*`. -/
def rotRaw (a b : List (Letter I)) (ls : List (LayerData I)) : List (LayerData I) :=
  (nCups a).map (whL (rd b) []) ++ ls.map (whL (rd b) (rd a)) ++ (nCaps b).map (whL [] (rd a))

theorem sChain_rotRaw {a b : List (Letter I)} {ls : List (LayerData I)} (h : SChain a ls b) :
    SChain (rd b) (rotRaw a b ls) (rd a) := by
  have h₁ := (sChain_nCups a).whisk (rd b) []
  have h₂ := h.whisk (rd b) (rd a)
  have h₃ := (sChain_nCaps b).whisk [] (rd a)
  simp only [List.append_nil, List.nil_append] at h₁ h₃
  unfold rotRaw
  refine SChain.append (t' := rd b ++ b ++ rd a)
    (SChain.append (t' := rd b ++ (a ++ rd a)) h₁ ?_) h₃
  simpa [List.append_assoc] using h₂

/-- **The mate of a normal-form diagram, in normal form** (before straightening). -/
theorem isDg_mateL_nf (ν μ : X) (a b : List (Letter I)) (ha : wt RD ν a = μ)
    (hb : wt RD ν b = μ) (ls : List (LayerData I)) (h : SChain a ls b) :
    IsDg RD k (mateL RD k (obH RD k ν μ a ha) (obH RD k ν μ b hb) (dg RD k ν a b ls))
      (layList RD μ (rotRaw a b ls)) := by
  have H := isDg_mateL_raw (RD := RD) (k := k) ν μ a b ha hb ls h
  convert H using 1
  subst ha
  have hμ : wt RD (wt RD ν a) (rd a) = ν := wt_rd RD ν a
  simp only [rotRaw, layList_append]
  congr 1
  congr 1
  · rw [cupLayers_wd]
    have hm := (sChain_nCups a).wt_mem RD (wt RD ν a)
    simp only [layList, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    simp only [Function.comp_apply, whL]
    rw [lay_wl_eq RD _ (wt RD ν a) _ _ _ _
      (show wt RD (wt RD ν a) (x.1 ++ x.2.1.dom ++ x.2.2) = wt RD ν a from hm x hx),
      List.append_nil]
  · have hm := h.wt_mem RD ν
    simp only [layList, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    simp only [Function.comp_apply, whL]
    rw [lay_wr_eq RD _ _ _ _ _ _ hμ, lay_wl_eq RD _ _ _ _ _ _ ?_]
    rw [← List.append_assoc, wt_append, hμ, hm x hx]
  · rw [capLayers_wd]
    simp only [layList, List.map_map]
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, whL, List.nil_append]
    rw [lay_wr_eq RD _ _ _ _ _ _ hμ]

/-! ### Straightening the rotated generators -/

theorem dg_rotRaw_updot (μ : X) (i : I) :
    dg RD k μ (rd [up i]) (rd [up i]) (rotRaw [up i] [up i] [([], .dot (up i), [])]) =
      dg RD k μ (rd [up i]) (rd [up i]) [([], rotSh (.dot (up i)), [])] :=
  (dg_cycDotR RD k i μ).symm

theorem dg_rotRaw_upcross (μ : X) (j i : I) :
    dg RD k μ (rd [up i, up j]) (rd [up j, up i])
        (rotRaw [up j, up i] [up i, up j] [([], .cross true j i, [])]) =
      dg RD k μ (rd [up i, up j]) (rd [up j, up i]) [([], rotSh (.cross true j i), [])] :=
  (dg_cycCrossR RD k j i μ).symm

theorem dg_rotRaw_cup (μ : X) (l : Letter I) :
    dg RD k μ (rd [l, l.dual]) (rd []) (rotRaw [] [l, l.dual] [([], .cup l, [])]) =
      dg RD k μ (rd [l, l.dual]) (rd []) [([], rotSh (.cup l), [])] := by
  obtain ⟨_ | _, i⟩ := l
  · show dg RD k μ [dn i, up i] [] _ = dg RD k μ [dn i, up i] [] _
    simp only [rotRaw, nCups, nCaps, rd_cons, rd_nil, List.nil_append, List.singleton_append,
      rotSh_cup, List.map_nil, List.map_cons, whL, List.append_nil, Letter.dual_mk,
      Bool.not_false, Bool.not_true]
    dat 0 [dn i] [] (dg_zigR' RD k _ (dn i))
  · show dg RD k μ [up i, dn i] [] _ = dg RD k μ [up i, dn i] [] _
    simp only [rotRaw, nCups, nCaps, rd_cons, rd_nil, List.nil_append, List.singleton_append,
      rotSh_cup, List.map_nil, List.map_cons, whL, List.append_nil, Letter.dual_mk,
      Bool.not_false, Bool.not_true]
    dat 0 [up i] [] (dg_zigR' RD k _ (up i))

theorem dg_rotRaw_cap (μ : X) (l : Letter I) :
    dg RD k μ (rd []) (rd [l.dual, l]) (rotRaw [l.dual, l] [] [([], .cap l, [])]) =
      dg RD k μ (rd []) (rd [l.dual, l]) [([], rotSh (.cap l), [])] := by
  obtain ⟨_ | _, i⟩ := l
  · show dg RD k μ [] [up i, dn i] _ = dg RD k μ [] [up i, dn i] _
    simp only [rotRaw, nCups, nCaps, rd_cons, rd_nil, List.nil_append, List.singleton_append,
      rotSh_cap, List.map_nil, List.map_cons, whL, List.append_nil, Letter.dual_mk,
      Bool.not_false, Bool.not_true]
    dat 1 [] [dn i] (dg_zigR' RD k _ (dn i))
  · show dg RD k μ [] [dn i, up i] _ = dg RD k μ [] [dn i, up i] _
    simp only [rotRaw, nCups, nCaps, rd_cons, rd_nil, List.nil_append, List.singleton_append,
      rotSh_cap, List.map_nil, List.map_cons, whL, List.append_nil, Letter.dual_mk,
      Bool.not_false, Bool.not_true]
    dat 1 [] [up i] (dg_zigR' RD k _ (up i))

/-- The mate of a normal-form diagram is the class of any normal-form diagram with the same
class as the unstraightened mate `rotRaw`. -/
theorem isDg_mateL_of (ν μ : X) (a b : List (Letter I)) (ha : wt RD ν a = μ)
    (hb : wt RD ν b = μ) {ls L : List (LayerData I)} (h : SChain a ls b)
    (hL : SChain (rd b) L (rd a))
    (heq : dg RD k μ (rd b) (rd a) (rotRaw a b ls) = dg RD k μ (rd b) (rd a) L) :
    IsDg RD k (mateL RD k (obH RD k ν μ a ha) (obH RD k ν μ b hb) (dg RD k ν a b ls))
      (layList RD μ L) :=
  (isDg_mateL_nf ν μ a b ha hb ls h).trans_dg (congrArg Bicat.Hom.obj (dual_obH RD k ν μ b hb))
    (congrArg Bicat.Hom.obj (dual_obH RD k ν μ a ha)) (sChain_rotRaw h) hL heq

theorem isDg_mateL_updot (ν μ : X) (i : I) (h : wt RD ν [up i] = μ) :
    IsDg RD k (mateL RD k (obH RD k ν μ [up i] h) (obH RD k ν μ [up i] h)
      (dg RD k ν [up i] [up i] [([], .dot (up i), [])])) (layList RD μ [([], .dot (dn i), [])]) :=
  isDg_mateL_of ν μ _ _ h h ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (dg_rotRaw_updot μ i)

theorem isDg_mateL_upcross (ν μ : X) (j i : I) (h : wt RD ν [up j, up i] = μ)
    (h' : wt RD ν [up i, up j] = μ) :
    IsDg RD k (mateL RD k (obH RD k ν μ [up j, up i] h) (obH RD k ν μ [up i, up j] h')
      (dg RD k ν [up j, up i] [up i, up j] [([], .cross true j i, [])]))
      (layList RD μ [([], .cross false j i, [])]) :=
  isDg_mateL_of ν μ _ _ h h' ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (dg_rotRaw_upcross μ j i)

theorem isDg_mateL_downdot (ν μ : X) (i : I) (h : wt RD ν [dn i] = μ) :
    IsDg RD k (mateL RD k (obH RD k ν μ [dn i] h) (obH RD k ν μ [dn i] h)
      (dg RD k ν [dn i] [dn i] [([], .dot (dn i), [])])) (layList RD μ [([], .dot (up i), [])]) := by
  have hA : wt RD μ [up i] = ν := by subst h; simp
  have hup := isDg_mateL_updot (RD := RD) (k := k) μ ν i hA
  have eB : obH RD k ν μ [dn i] h =
      (pres RD k).dualHom (inv RD).toColourDuality.pivotal (obH RD k μ ν [up i] hA) := by
    rw [dual_obH]; rfl
  have hβ := IsDiag.eq_eqToHom
    ((isDg_dg (RD := RD) (k := k) ν (show SChain [dn i] [([], .dot (dn i), [])] [dn i] from
      ⟨rfl, rfl⟩)).toIsDiag (obH RD k ν μ [dn i] h) (obH RD k ν μ [dn i] h))
    (hup.toIsDiag _ _) eB eB
  exact IsDiag.rightMate_rotate_back (zigzags RD k) eB eB (isCyclic RD k _) hβ
    ((isDg_dg (RD := RD) (k := k) μ (show SChain [up i] [([], .dot (up i), [])] [up i] from
      ⟨rfl, rfl⟩)).toIsDiag (obH RD k μ ν [up i] hA) (obH RD k μ ν [up i] hA))

theorem isDg_mateL_downcross (ν μ : X) (j i : I) (h : wt RD ν [dn j, dn i] = μ)
    (h' : wt RD ν [dn i, dn j] = μ) :
    IsDg RD k (mateL RD k (obH RD k ν μ [dn j, dn i] h) (obH RD k ν μ [dn i, dn j] h')
      (dg RD k ν [dn j, dn i] [dn i, dn j] [([], .cross false j i, [])]))
      (layList RD μ [([], .cross true j i, [])]) := by
  have hA : wt RD μ [up j, up i] = ν := by subst h; simp [add_left_comm]
  have hA' : wt RD μ [up i, up j] = ν := by subst h; simp
  have hup := isDg_mateL_upcross (RD := RD) (k := k) μ ν j i hA hA'
  have eB : obH RD k ν μ [dn j, dn i] h =
      (pres RD k).dualHom (inv RD).toColourDuality.pivotal (obH RD k μ ν [up i, up j] hA') := by
    rw [dual_obH]; rfl
  have eB' : obH RD k ν μ [dn i, dn j] h' =
      (pres RD k).dualHom (inv RD).toColourDuality.pivotal (obH RD k μ ν [up j, up i] hA) := by
    rw [dual_obH]; rfl
  have hβ := IsDiag.eq_eqToHom
    ((isDg_dg (RD := RD) (k := k) ν
      (show SChain [dn j, dn i] [([], .cross false j i, [])] [dn i, dn j] from
        ⟨rfl, rfl⟩)).toIsDiag (obH RD k ν μ [dn j, dn i] h) (obH RD k ν μ [dn i, dn j] h'))
    (hup.toIsDiag _ _) eB eB'
  exact IsDiag.rightMate_rotate_back (zigzags RD k) eB eB' (isCyclic RD k _) hβ
    ((isDg_dg (RD := RD) (k := k) μ
      (show SChain [up j, up i] [([], .cross true j i, [])] [up i, up j] from
        ⟨rfl, rfl⟩)).toIsDiag (obH RD k μ ν [up j, up i] hA) (obH RD k μ ν [up i, up j] hA'))

/-- **The rotations of the generators**: the mate of a generator of shape `g` is the generator of
shape `rotSh g`. -/
theorem isDg_mateL_gen (ν μ : X) (g : Shape I) (h₁ : wt RD ν g.dom = μ) (h₂ : wt RD ν g.cod = μ) :
    IsDg RD k (mateL RD k (obH RD k ν μ g.dom h₁) (obH RD k ν μ g.cod h₂)
      (dg RD k ν g.dom g.cod [([], g, [])])) (layList RD μ [([], rotSh g, [])]) := by
  cases g with
  | dot l =>
    obtain ⟨_ | _, i⟩ := l
    · exact isDg_mateL_downdot ν μ i h₁
    · exact isDg_mateL_updot ν μ i h₁
  | cross ε i j =>
    cases ε
    · exact isDg_mateL_downcross ν μ i j h₁ h₂
    · exact isDg_mateL_upcross ν μ i j h₁ h₂
  | cup l => exact isDg_mateL_of ν μ _ _ h₁ h₂ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (dg_rotRaw_cup μ l)
  | cap l => exact isDg_mateL_of ν μ _ _ h₁ h₂ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (dg_rotRaw_cap μ l)

/-- **The rotation of a whiskered generator is the whiskered rotated generator**:
`(u ⊗ g ⊗ v)^* = v* ⊗ g^* ⊗ u*`. -/
theorem isDg_mateL_layer (μ ν : X) (u v : List (Letter I)) (g : Shape I)
    (hs : wt RD μ (u ++ g.dom ++ v) = ν) (ht : wt RD μ (u ++ g.cod ++ v) = ν) :
    IsDg RD k (mateL RD k (obH RD k μ ν _ hs) (obH RD k μ ν _ ht)
      (dg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)]))
      (layList RD ν [(rd v, rotSh g, rd u)]) := by
  have h₂ : wt RD (wt RD μ v) g.cod = wt RD (wt RD μ v) g.dom :=
    (Shape.wt_dom_eq_wt_cod (wt RD μ v) g).symm
  have hu : wt RD (wt RD (wt RD μ v) g.dom) u = ν := by
    rw [← hs, List.append_assoc, wt_append, wt_append]
  let V := obH RD k μ (wt RD μ v) v rfl
  let G₁ := obH RD k (wt RD μ v) (wt RD (wt RD μ v) g.dom) g.dom rfl
  let G₂ := obH RD k (wt RD μ v) (wt RD (wt RD μ v) g.dom) g.cod h₂
  let Uh := obH RD k (wt RD (wt RD μ v) g.dom) ν u hu
  let θ : G₁ ⟶ G₂ := dg RD k (wt RD μ v) g.dom g.cod [([], g, [])]
  have hθ : IsDiag (pres RD k) θ (layList RD (wt RD μ v) [([], g, [])]) :=
    (isDg_dg (RD := RD) (k := k) (wt RD μ v)
      (show SChain g.dom [([], g, [])] g.cod by simp)).toIsDiag G₁ G₂
  have hbase := (isDg_mateL_gen (RD := RD) (k := k) (wt RD μ v) _ g rfl h₂).toIsDiag
    ((pres RD k).dualHom (inv RD).toColourDuality.pivotal G₂)
    ((pres RD k).dualHom (inv RD).toColourDuality.pivotal G₁)
  have hW := (IsDiag.rightMate_whiskerRight (zigzags RD k) V hbase).rightMate_whiskerLeft
    (zigzags RD k) Uh
  have hX : IsDiag (pres RD k) (Uh ◁ (θ ▷ V))
      (((layList RD (wt RD μ v) [([], g, [])]).map (·.wr V.obj.word)).map (·.wl Uh.obj)) :=
    (hθ.whiskerRight V).whiskerLeft Uh
  have e : obH RD k μ ν (u ++ g.dom ++ v) hs = Uh ≫ (G₁ ≫ V) := by
    refine Bicat.Hom.ext (Obj.ext ?_ ?_)
    · show wt RD μ (u ++ g.dom ++ v) = wt RD (wt RD (wt RD μ v) g.dom) u
      rw [hu, hs]
    · show wd RD μ (u ++ g.dom ++ v) =
        wd RD (wt RD (wt RD μ v) g.dom) u ++ (wd RD (wt RD μ v) g.dom ++ wd RD μ v)
      simp [wd_append, wt_append, List.append_assoc]
  have e' : obH RD k μ ν (u ++ g.cod ++ v) ht = Uh ≫ (G₂ ≫ V) := by
    refine Bicat.Hom.ext (Obj.ext ?_ ?_)
    · show wt RD μ (u ++ g.cod ++ v) = wt RD (wt RD (wt RD μ v) g.dom) u
      rw [hu, ht]
    · show wd RD μ (u ++ g.cod ++ v) =
        wd RD (wt RD (wt RD μ v) g.dom) u ++ (wd RD (wt RD μ v) g.cod ++ wd RD μ v)
      simp [wd_append, wt_append, List.append_assoc, h₂]
  have hdg : IsDiag (pres RD k) (show obH RD k μ ν _ hs ⟶ obH RD k μ ν _ ht from
      dg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)])
      (((layList RD (wt RD μ v) [([], g, [])]).map (·.wr V.obj.word)).map (·.wl Uh.obj)) := by
    refine ((isDg_dg (RD := RD) (k := k) μ
      (show SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) from ⟨rfl, rfl⟩)).toIsDiag
      _ _).congr ?_
    simp only [layList_cons, layList_nil, List.map_cons, List.map_nil]
    congr 1
    rw [show V.obj.word = wd RD μ v from rfl, lay_wr_eq RD μ (wt RD μ v) v [] [] g rfl,
      show Uh.obj = ob RD (wt RD (wt RD μ v) g.dom) u from rfl,
      lay_wl_eq RD μ (wt RD (wt RD μ v) g.dom) u [] ([] ++ v) g ?_]
    · simp
    · simp [wt_append]
  have heq := hdg.eq_eqToHom hX e e'
  have H := rightMate_eqToHom_conj (zigzags RD k) e e' (Uh ◁ (θ ▷ V))
  have hfin : IsDiag (pres RD k)
      (Biadjunction.rightMate (biadjWord RD k (obH RD k μ ν _ hs))
        (biadjWord RD k (obH RD k μ ν _ ht))
        (show obH RD k μ ν _ hs ⟶ obH RD k μ ν _ ht from
          dg RD k μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)]))
      (((layList RD (wt RD (wt RD μ v) g.dom) [([], rotSh g, [])]).map
        (·.wl ((pres RD k).dualHom (inv RD).toColourDuality.pivotal V).obj)).map
          (·.wr ((pres RD k).dualHom (inv RD).toColourDuality.pivotal Uh).obj.word)) := by
    rw [heq, H]
    exact (hW.comp_eqToHom _).eqToHom_comp _
  refine (hfin.congr ?_).toIsDg
  have eV := congrArg Bicat.Hom.obj (dual_obH RD k μ (wt RD μ v) v rfl)
  have eU := congrArg (fun x => (Bicat.Hom.obj x).word)
    (dual_obH RD k (wt RD (wt RD μ v) g.dom) ν u hu)
  simp only [obH_obj, ob_word] at eV eU
  simp only [layList_cons, layList_nil, List.map_cons, List.map_nil]
  rw [show V = obH RD k μ (wt RD μ v) v rfl from rfl, eV,
    show Uh = obH RD k (wt RD (wt RD μ v) g.dom) ν u hu from rfl, eU,
    lay_wl_eq RD _ (wt RD μ v) (rd v) [] [] (rotSh g)
      (by simp [rotSh_dom, wt_rd_of RD _ _ g.cod h₂]),
    lay_wr_eq RD ν _ (rd u) _ [] (rotSh g) (wt_rd_of RD _ _ u hu)]
  simp

/-! ## The rotation of normal-form diagrams -/

/-- The rotation of a single layer. -/
theorem rotU_dg_single (μ ν : X) (x : LayerData I) (hs : wt RD μ (x.1 ++ x.2.1.dom ++ x.2.2) = ν)
    (ht : wt RD μ (x.1 ++ x.2.1.cod ++ x.2.2) = ν) :
    rotU RD k μ ν _ _ hs ht (dg RD k μ _ _ [x]) =
      dg RD k ν (rd (x.1 ++ x.2.1.cod ++ x.2.2)) (rd (x.1 ++ x.2.1.dom ++ x.2.2)) [rotLD x] := by
  obtain ⟨u, g, v⟩ := x
  have H := (isDg_mateL_layer (RD := RD) (k := k) μ ν u v g hs ht).eqToHom_comp
    (objEq RD k (dual_obH RD k μ ν _ ht).symm) |>.comp_eqToHom
    (objEq RD k (dual_obH RD k μ ν _ hs))
  have H' := isDg_dg (RD := RD) (k := k) ν (sChain_rotLs
    (show SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) from ⟨rfl, rfl⟩))
  rw [rotU_apply]
  simpa using H.eq_eqToHom H' rfl rfl

/-- **The rotation of a normal-form diagram is the diagram of the rotated layers in reversed
order** (KL III §3.3.2, "Rotation by 180°": `ζ ↦ ζ*`, computed with the cyclicity relations
(3.3), `eq_cyclic_cross-gen` and the zigzag relations (3.1), (3.2)). -/
theorem rotU_dg (μ ν : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t)
    (hs : wt RD μ s = ν) (ht : wt RD μ t = ν) :
    rotU RD k μ ν s t hs ht (dg RD k μ s t ls) = dg RD k ν (rd t) (rd s) (rotLs ls) := by
  induction ls generalizing s with
  | nil =>
    obtain rfl : s = t := h
    rw [dg_nil, rotU_id, rotLs_nil, dg_nil]
  | cons x ls ih =>
    obtain ⟨rfl, h'⟩ := h
    have hr : wt RD μ (x.1 ++ x.2.1.cod ++ x.2.2) = ν := by
      rw [← ht, SChain.wt_eq RD μ h']
    rw [show x :: ls = [x] ++ ls from rfl, ← dg_comp (show SChain _ [x] _ from ⟨rfl, rfl⟩) h',
      rotU_comp μ ν _ _ _ hs hr ht, ih h' hr, rotU_dg_single, rotLs_append,
      show rotLs [x] = [rotLD x] from rfl]
    exact dg_comp (sChain_rotLs h') (sChain_rotLs (show SChain _ [x] _ from ⟨rfl, rfl⟩))

end Categorification.KL3.Diagram
