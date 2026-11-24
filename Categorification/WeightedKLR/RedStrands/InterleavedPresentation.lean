/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.InterleavedPBW

/-!
# Relations of the interleaved loading column

Webster, arXiv:1309.3796v2, §6.1, Prop. 6.4 and the cut after (6.21) in Lemma 6.8.
At the three bottom positions choose a normal exit in each right parabolic row.
Reading it back detects relations between arbitrary sums, not only individual braids.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA Equiv MvPolynomial ExitPBW
variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "Pol" => MvPolynomial (Fin n) k
variable (s : KLR.Seq (stendhalWeight ℓ ν)) (j : ℕ) (hj : j+2 < (stendhalWeight ℓ ν).card)
local notation "τ" => fun o : Order => wordProd n (Order.tail j o)
local notation "q" => fun o : Order => τ o • s
local notation "leg" => fun (o : Order) (v : KLR.Seq μ) => (ψw (Order.tail j o) * e v : R)
local notation "L" => Order.cab
local notation "D" => Order.cba
local notation "U" => Order.bca
local notation "a₀" => Order.bac
local notation "b₁" => Order.acb
local notation "pref" => fun (u : Perm (Fin n)) (f : Pol) => (ψw (canWord n u) * pol f : R)

private theorem corner_rows (v t : KLR.Seq μ) (M : Submodule k R)
    (h₀ : v.lbl ⟨j,by omega⟩ ≠ v.lbl ⟨j+1,by omega⟩) (h₁ : v.lbl ⟨j+1,by omega⟩ ≠ v.lbl ⟨j+2,hj⟩)
    (h₂ : v.lbl ⟨j,by omega⟩ ≠ v.lbl ⟨j+2,hj⟩)
    (gen : ∀ u, Sorted hj u → ∀ o, (u*τ o) • v = t → ∀ f, pref u f * leg o v ∈ M)
    {z : R} (hz : e t * z * e v = z) : z ∈ M := by
  apply (Submodule.span_le.2 ?_) (mem_span_corner' (word hj) (word_choice hj) v t hz)
  rintro _ ⟨w,d,hv,rfl⟩
  let o := order hj w; let u := w*(τ o)⁻¹
  have hu : Sorted hj u := sorted_strip hj w
  have hw : u * τ o = w := by simp only [u,mul_assoc,inv_mul_cancel,mul_one]
  let mon := monomial d (1 : k)
  have H := gen u hu o (hw ▸ hv) (rename (τ o) mon)
  rw [mul_assoc,← local_polynomial Q Λ j hj v o mon h₀ h₁ h₂] at H
  have elt : (ψw (word hj w) * pol mon * e v : R) = ψw (canWord n u) * (ψw (Order.tail j o) * pol mon * e v) := by
    have eq : word hj w = canWord n u ++ Order.tail j o := hw ▸ word_mul hj hu o
    rw [eq,ψw_append]; simp only [mul_assoc]
  change ψw (word hj w) * pol mon * e v ∈ M
  rw [elt]; exact H

private def normal (u : Perm (Fin n)) (o : Order) : Pol →ₗ[k] (R × R) :=
  let pr := (LinearMap.mulLeft k (ψw (canWord n u) : R)).comp pol.toLinearMap
  match o with
  | .cab => ((LinearMap.mulRight k (e (q L))).comp pr).prod 0
  | .cba => ((LinearMap.mulRight k (leg a₀ (q L))).comp pr).prod 0
  | _ => (0 : Pol →ₗ[k] R).prod ((LinearMap.mulRight k (e (q U))).comp pr)

private def delta : R →ₗ[k] R × R :=
  (LinearMap.mulRight k (leg a₀ (q L))).prod (-(LinearMap.mulRight k (leg b₁ (q U))))

private def total : R × R →ₗ[k] R :=
  (LinearMap.mulRight k (leg L s)).coprod (LinearMap.mulRight k (leg U s))

private theorem read_relations {a b : Fin ℓ} {i : I}
    (hb : s.lbl ⟨j,by omega⟩ = .inr b) (hi : s.lbl ⟨j+1,by omega⟩ = .inl i)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (u : Perm (Fin n)) (f : Pol)
    (read : R →ₗ[k] R × R) (eval : ∀ o g, read (pref u g * leg o s) = normal Q Λ s j u o g) :
    let diff := LinearMap.id - read.comp (total Q Λ s j)
    let good := (LinearMap.range (delta Q Λ s j)).comap diff
    (∀ o : Order, o = .abc ∨ o = a₀ ∨ o = L → (pref u f * leg o (q L),0) ∈ good) ∧
    (∀ o : Order, o = .abc ∨ o = b₁ ∨ o = U → (0,pref u f * leg o (q U)) ∈ good) := by
  intro diff good
  let H := pref u f
  let X₀ : Pol := MvPolynomial.X ⟨j,by omega⟩ ^ Λ a i
  let X₂ : Pol := MvPolynomial.X ⟨j+2,hj⟩ ^ Λ b i
  have p₀ : pref u (f*X₀) = H * x ⟨j,by omega⟩ ^ Λ a i := by simp only [H,X₀,map_mul,map_pow,pol_X,mul_assoc]
  have p₂ : pref u (f*X₂) = H * x ⟨j+2,hj⟩ ^ Λ b i := by simp only [H,X₂,map_mul,map_pow,pol_X,mul_assoc]
  obtain ⟨wrongR,midL,midR,wrongL⟩ := exit_rows Q Λ s j hj hb hi ha (canWord n u) f
  obtain ⟨ll,lr,rl,rr⟩ := joint_rows Q Λ s j hj hb hi ha
  have cut (o : Order) : (e (q o) * leg o s : R) = leg o s := by
    rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  have test (x y l r z : R) (he : read (x*leg L s + y*leg U s) = (l,r))
      (hl : z * leg a₀ (q L) = x-l) (hr : -(z * leg b₁ (q U)) = y-r) : (x,y) ∈ good := by
    change (x,y) - read (x*leg L s + y*leg U s) ∈ LinearMap.range (delta Q Λ s j)
    rw [he]; exact ⟨z,Prod.ext hl hr⟩
  have eL (g : Pol) : read (pref u g * leg L s) = (pref u g * e (q L),0) := eval L g
  have eD (g : Pol) : read (pref u g * leg D s) = (pref u g * leg a₀ (q L),0) := eval D g
  have eR (g : Pol) : read (pref u g * leg U s) = (0,pref u g * e (q U)) := eval U g
  have idleg (v : KLR.Seq μ) : leg .abc v = e v := by simp [Order.tail,ψw]
  constructor
  · rintro o (rfl|rfl|rfl)
    · rw [idleg]; apply test _ _ _ _ 0 (by rw [zero_mul,add_zero,mul_assoc _ (e _),cut,eL]) <;> simp
    · apply test _ _ _ _ 0 (by rw [zero_mul,add_zero,midL,eD]) <;> simp
    · refine test _ _ 0 (pref u (f*X₂) * e (q U)) (H * leg b₁ (q D)) ?_ ?_ ?_
      · rw [zero_mul,add_zero,wrongL,← p₂,eR]
      · rw [mul_assoc,rl,sub_zero]
      · rw [mul_assoc,rr,p₂,zero_sub]; simp only [H,mul_assoc]
  · rintro o (rfl|rfl|rfl)
    · rw [idleg]; apply test _ _ _ _ 0 (by rw [zero_mul,zero_add,mul_assoc _ (e _),cut,eR]) <;> simp
    · apply test _ _ _ _ (-H) (by rw [zero_mul,zero_add,midR,eD]) <;> simp [H]
    · refine test _ _ (pref u (f*X₀) * e (q L)) 0 (-(H * leg a₀ (q D))) ?_ ?_ ?_
      · rw [zero_mul,zero_add,wrongR,← p₀,eL]
      · rw [neg_mul,mul_assoc,ll,p₀,zero_sub]; simp only [H,mul_assoc]
      · rw [neg_mul,neg_neg,mul_assoc,lr,sub_zero]

private theorem klr_joint {a b : Fin ℓ} {i : I} (hQ : KLRSymm Q) {Lr Mr : List (Fin ℓ)}
    (t : KLR.Seq μ) (ht : redWord t = Lr ++ a :: b :: Mr)
    (hb : s.lbl ⟨j,by omega⟩ = .inr b) (hi : s.lbl ⟨j+1,by omega⟩ = .inl i)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (x y : R)
    (hx : e t * x * e (q L) = x) (hy : e t * y * e (q U) = y)
    (hz : x * leg L s + y * leg U s = 0) : ∃ z : R, z * leg a₀ (q L) = x ∧ z * leg b₁ (q U) = -y := by
  have hab : b ≠ a := by
    rintro rfl; have he := lbl_inj_of_inr s b hb ha; have := congrArg Fin.val he; dsimp at this; omega
  have h₀ : s.lbl ⟨j,by omega⟩ ≠ s.lbl ⟨j+1,by omega⟩ := by rw [hb,hi]; exact Sum.inr_ne_inl
  have h₁ : s.lbl ⟨j+1,by omega⟩ ≠ s.lbl ⟨j+2,hj⟩ := by rw [hi,ha]; exact Sum.inl_ne_inr
  have h₂ : s.lbl ⟨j,by omega⟩ ≠ s.lbl ⟨j+2,hj⟩ := by simpa only [hb,ha,ne_eq,Sum.inr.injEq] using hab
  obtain ⟨read,eval⟩ := exists_parabolic_read Q Λ s j hj hQ h₀ h₁ h₂ (normal Q Λ s j)
  let G := (LinearMap.range (delta Q Λ s j)).comap (LinearMap.id - read.comp (total Q Λ s j))
  have leftLabels : (q L).lbl ⟨j,by omega⟩ = .inl i ∧ (q L).lbl ⟨j+1,by omega⟩ = .inr a ∧
      (q L).lbl ⟨j+2,hj⟩ = .inr b := by
    simp only [Order.tail,wordProd_cons,wordProd_nil,mul_one,mul_smul,lbl_sadj,sadj_apply_left hj,
      sadj_apply_right hj,sadj_apply_left (show j+1 < n by omega),sadj_apply_right (show j+1 < n by omega),
      sadj_apply_of_ne (k := j+1) (⟨j,by omega⟩ : Fin n) (by simp) (by dsimp; omega),
      sadj_apply_of_ne (k := j) (⟨j+1+1,hj⟩ : Fin n) (by dsimp; omega) (by simp),hb,hi,ha,and_self]
  have rightLabels : (q U).lbl ⟨j,by omega⟩ = .inr a ∧ (q U).lbl ⟨j+1,by omega⟩ = .inr b ∧
      (q U).lbl ⟨j+2,hj⟩ = .inl i := by
    simp only [Order.tail,wordProd_cons,wordProd_nil,mul_one,mul_smul,lbl_sadj,sadj_apply_left hj,
      sadj_apply_right hj,sadj_apply_left (show j+1 < n by omega),sadj_apply_right (show j+1 < n by omega),
      sadj_apply_of_ne (k := j) (⟨j+2,hj⟩ : Fin n) (by simp) (by simp),
      sadj_apply_of_ne (k := j+1) (⟨j,by omega⟩ : Fin n) (by simp) (by dsimp; omega),hb,hi,ha,and_self]
  obtain ⟨li,la,lb⟩ := leftLabels; obtain ⟨ra,rb,ri⟩ := rightLabels
  have hl : x ∈ G.comap (LinearMap.inl k R R) := by
    apply corner_rows Q Λ j hj (q L) t _ (by simp [li,la]) (by simp [la,lb,hab.symm]) (by simp [li,lb]) _ hx
    intro u hu o hw f
    apply (read_relations Q Λ s j hj hb hi ha u f read (eval u hu)).1 o
    apply left_orders hj hu o
    apply lt_of_redWord_eq_append ht
    · simpa only [← hw,lbl_smul,Perm.inv_def,Equiv.symm_apply_apply] using la
    · simpa only [← hw,lbl_smul,Perm.inv_def,Equiv.symm_apply_apply] using lb
  have hr : y ∈ G.comap (LinearMap.inr k R R) := by
    apply corner_rows Q Λ j hj (q U) t _ (by simp [ra,rb,hab.symm]) (by simp [rb,ri]) (by simp [ra,ri]) _ hy
    intro u hu o hw f
    apply (read_relations Q Λ s j hj hb hi ha u f read (eval u hu)).2 o
    apply right_orders hj hu o
    apply lt_of_redWord_eq_append ht
    · simpa only [← hw,lbl_smul,Perm.inv_def,Equiv.symm_apply_apply] using ra
    · simpa only [← hw,lbl_smul,Perm.inv_def,Equiv.symm_apply_apply] using rb
  have mem : (x,y) ∈ G := by simpa only [LinearMap.inl_apply,LinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add] using G.add_mem hl hr
  change (x,y) - read (x * leg L s + y * leg U s) ∈ LinearMap.range (delta Q Λ s j) at mem
  rw [hz,map_zero,sub_zero] at mem
  obtain ⟨z,hz'⟩ := mem
  refine ⟨z,congrArg Prod.fst hz',?_⟩
  have h : -(z*leg b₁ (q U)) = y := congrArg Prod.snd hz'
  exact neg_eq_iff_eq_neg.mp h

local notation "raw" => ofKLR k Q Λ ν
local notation "aff" => BraidedStendhalAlgebra k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "π" => AlgHom.comp mk raw

private theorem read_lift (hQ : KLRSymm Q) (z : aff) : raw (toKLR k Q Λ ν z) = z := by
  let w := canWord n
  have hw : IsReducedChoice w := fun u => ⟨isReduced_canWord _ _,wordProd_canWord _ _⟩
  let bs := basis (Λ := Λ) (ν := ν) hQ w hw
  apply LinearMap.congr_fun (f := (raw).toLinearMap.comp (toKLR k Q Λ ν).toLinearMap) (g := LinearMap.id) _ z
  apply bs.ext; intro b
  change raw (toKLR k Q Λ ν (bs b)) = bs b
  rw [show bs b = _ from basis_apply hQ w hw b,toKLR_ofKLR_std _ _ _ b.2]

include hj in
private theorem joint_fixed : (e (q D) * leg a₀ (q L) : R) = leg a₀ (q L) ∧
    (e (q D) * leg b₁ (q U) : R) = leg b₁ (q U) := by
  have fix (w : List ℕ) (v : KLR.Seq μ) : (e (wordProd n w • v) * (ψw w * e v) : R) = ψw w * e v := by
    rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  have hl := fix (Order.tail j a₀) (q L); have hr := fix (Order.tail j b₁) (q U)
  have eq : τ b₁ • q U = q D := by
    simpa only [Order.tail,wordProd_cons,wordProd_nil,mul_one,mul_smul] using (braid_smul hj s).symm
  rw [eq] at hr
  exact ⟨by simpa only [Order.tail,wordProd_cons,wordProd_nil,mul_one,mul_smul] using hl,hr⟩

private theorem joint_vanish {V : Type*} [Ring V] [Algebra k V] (F : R →ₐ[k] V)
    {a b : Fin ℓ} {i : I} (hb : s.lbl ⟨j,by omega⟩ = .inr b) (hi : s.lbl ⟨j+1,by omega⟩ = .inl i)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (z x y : V)
    (hl : z*F (leg a₀ (q L)) = x) (hr : z*F (leg b₁ (q U)) = -y) :
    x*F (leg L s) + y*F (leg U s) = 0 := by
  have H := exit_rows Q Λ s j hj hb hi ha [] 1
  have braid : leg a₀ (q L) * leg L s = leg b₁ (q U) * leg U s := by
    simpa only [ψw_nil,map_one,one_mul] using H.2.1.trans H.2.2.1.symm
  rw [← hl,← neg_eq_iff_eq_neg.mpr hr,neg_mul,mul_assoc,mul_assoc,← map_mul,← map_mul,braid,add_neg_cancel]

/-- Affine two-exit relations at `b i a`, Webster v2, §6.1, Prop. 6.4 and the
cut following (6.21). In the two loading corners the entire kernel of stacking
is the signed joint image, with arbitrary exterior strands and bottom dots.
The joint coefficient belongs to `e(t) Ã e(a i b)`; there is no higher mark here. -/
theorem interleaved_affine_relation_iff {a b : Fin ℓ} {i : I} (hQ : KLRSymm Q) {Lr Mr : List (Fin ℓ)}
    (t : KLR.Seq μ) (ht : redWord t = Lr ++ a :: b :: Mr) (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (hi : s.lbl ⟨j+1,by omega⟩ = .inl i) (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (x y : aff)
    (hx : raw (e t) * x * raw (e (q L)) = x) (hy : raw (e t) * y * raw (e (q U)) = y) :
    x*raw (leg L s) + y*raw (leg U s) = 0 ↔ ∃ z : aff,
      raw (e t)*z*raw (e (q D)) = z ∧ z*raw (leg a₀ (q L)) = x ∧ z*raw (leg b₁ (q U)) = -y := by
  constructor
  swap
  · rintro ⟨z,-,hl,hr⟩; exact joint_vanish Q Λ s j hj raw hb hi ha z x y hl hr
  intro hz
  let lift := toKLR k Q Λ ν
  obtain ⟨u,hu,hv⟩ := klr_joint Q Λ s j hj hQ t ht hb hi ha (lift x) (lift y)
    (by simpa only [map_mul,toKLR_ofKLR_e,lift] using congrArg lift hx)
    (by simpa only [map_mul,toKLR_ofKLR_e,lift] using congrArg lift hy)
    (by simpa only [map_mul,map_add,map_zero,lift,toKLR_ofKLR_ψw,toKLR_ofKLR_e] using congrArg lift hz)
  have fix (v : KLR.Seq μ) (X : aff) (h : raw (e t)*X*raw (e v) = X) : raw (e t)*X = X := by
    calc _ = raw (e t) * (raw (e t)*X*raw (e v)) := congrArg (raw (e t) * ·) h.symm
         _ = X := by simpa only [← mul_assoc,← map_mul raw,e_mul_self] using h
  obtain ⟨hl,hr⟩ := joint_fixed Q Λ s j hj
  refine ⟨raw (e t*u*e (q D)),?_,?_,?_⟩
  · simp only [← map_mul raw,mul_assoc,e_mul_self]; rw [← mul_assoc (e t),e_mul_self]
  · rw [← map_mul raw,mul_assoc _ (e _),hl,mul_assoc,hu,map_mul,read_lift Q Λ hQ,fix _ _ hx]
  · rw [← map_mul raw,mul_assoc _ (e _),hr,mul_assoc,hv,map_mul,map_neg,read_lift Q Λ hQ,mul_neg,fix _ _ hy]

/-- Two-exit presentation after killing global violations (Webster v2, §6.1,
Lemma 6.8 after (6.21)). Together with two-exit generation this presents the
projective loading column: all mixed and one-sided relations are joint images.
The output is in the projective row, not necessarily in its higher submodule. -/
theorem interleaved_quotient_relation_iff {a b : Fin ℓ} {i : I} (hQ : KLRSymm Q) {Lr Mr : List (Fin ℓ)}
    (t : KLR.Seq μ) (ht : redWord t = Lr ++ a :: b :: Mr) (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (hi : s.lbl ⟨j+1,by omega⟩ = .inl i) (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (x y : ViolQuotient k Q Λ ν)
    (hx : π (e t) * x * π (e (q L)) = x) (hy : π (e t) * y * π (e (q U)) = y) :
    x*π (leg L s) + y*π (leg U s) = 0 ↔ ∃ z : ViolQuotient k Q Λ ν,
      π (e t)*z*π (e (q D)) = z ∧ z*π (leg a₀ (q L)) = x ∧ z*π (leg b₁ (q U)) = -y := by
  constructor
  swap
  · rintro ⟨z,-,hl,hr⟩; exact joint_vanish Q Λ s j hj π hb hi ha z x y hl hr
  intro hz
  obtain ⟨c,d,hc,hd,zero⟩ := exists_interleavedRelation_affine_lift Q Λ s j hj t a b hQ ht hb ha x y hx hy hz
  have fix (v : KLR.Seq μ) (z : aff) : raw (e t) * (raw (e t)*z*raw (e v)) * raw (e v) = raw (e t)*z*raw (e v) := by
    simp only [mul_assoc,← map_mul raw,e_mul_self]; rw [← mul_assoc (raw (e t)),← map_mul raw,e_mul_self]
  obtain ⟨z,he,hl,hr⟩ := (interleaved_affine_relation_iff Q Λ s j hj hQ t ht hb hi ha _ _ (fix _ c) (fix _ d)).1 zero
  exact ⟨mk z,by simpa only [map_mul,AlgHom.comp_apply] using congrArg mk he,
    (map_mul mk _ _).symm.trans ((congrArg mk hl).trans hc),
    (map_mul mk _ _).symm.trans ((congrArg mk hr).trans ((map_neg mk _).trans (congrArg Neg.neg hd)))⟩

local notation "V" => ViolQuotient k Q Λ ν
local notation "J" => fun (t : KLR.Seq μ) (a b : Fin ℓ) => blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t)

/-- At a strictly higher joint all projective relations lift there with their
marks, even when a component is zero. This condition is on the *loading*, not
an assumption about a chosen projective preimage. Webster v2, §6.1, Lemma 6.8,
cut following (6.21). -/
theorem interleaved_marked_joint_of_higher {a b : Fin ℓ} {i : I} (hQ : KLRSymm Q) {Lr Mr : List (Fin ℓ)}
    (t : KLR.Seq μ) (ht : redWord t = Lr ++ a :: b :: Mr) (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (hi : s.lbl ⟨j+1,by omega⟩ = .inl i) (ha : s.lbl ⟨j+2,hj⟩ = .inr a)
    (ho : redWord (q D) = redWord t) (hh : adjacentBlockRoot a b t < adjacentBlockRoot a b (q D))
    (x y : V) (hx : π (e t)*x*π (e (q L)) = x) (hy : π (e t)*y*π (e (q U)) = y)
    (hz : x*π (leg L s) + y*π (leg U s) = 0) : ∃ z ∈ J t a b,
      π (e t)*z*π (e (q D)) = z ∧ z*π (leg a₀ (q L)) = x ∧ z*π (leg b₁ (q U)) = -y := by
  obtain ⟨z,he,h₁,h₂⟩ := (interleaved_quotient_relation_iff Q Λ s j hj hQ t ht hb hi ha x y hx hy).1 hz
  refine ⟨z,?_,he,h₁,h₂⟩
  rw [← he]; exact TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span ⟨q D,ho,hh,rfl⟩)

private theorem return_joint {a b : Fin ℓ} {i : I} (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (hi : s.lbl ⟨j+1,by omega⟩ = .inl i) (ha : s.lbl ⟨j+2,hj⟩ = .inr a) :
    leg a₀ (q L) * leg a₀ (q D) = e (q D) * x ⟨j+1,by omega⟩ ^ Λ a i ∧
    leg b₁ (q U) * leg b₁ (q D) = e (q D) * x ⟨j+1,by omega⟩ ^ Λ b i := by
  have h₀ : (q D).lbl ⟨j,by omega⟩ = .inr a := (braid_smul_apply_zero hj s).trans ha
  have h₁ : (q D).lbl ⟨j+1,by omega⟩ = .inl i := (braid_smul_apply_one hj s).trans hi
  have h₂ : (q D).lbl ⟨j+2,hj⟩ = .inr b := (braid_smul_apply_two hj s).trans hb
  have l := ψ_sq (Q := stendhalQ Q Λ) j (by omega) (q D)
  have r := ψ_sq (Q := stendhalQ Q Λ) (j+1) hj (q D)
  rw [h₀,h₁] at l; rw [h₁,h₂] at r
  have hl : sadj n j • q D = q L := by simp only [Order.tail,wordProd_cons,wordProd_nil,mul_one,mul_smul,sadj_smul_smul]
  have hr : sadj n (j+1) • q D = q U := by
    simp only [Order.tail,wordProd_cons,wordProd_nil,mul_one,mul_smul,braid_smul hj s,sadj_smul_smul]
  have step (c : ℕ) (v : KLR.Seq μ) (hv : sadj n c • q D = v) :
      (ψ c * e v * (ψ c * e (q D)) : R) = ψ c * ψ c * e (q D) := by
    have fix : (e v * (ψ c * e (q D)) : R) = ψ c * e (q D) := by
      rw [ψ_mul_e c (q D),hv,← mul_assoc,e_mul_self]
    rw [mul_assoc,fix,mul_assoc]
  have ca : (ψw (Order.tail j a₀) : R) = ψ j := by simp [Order.tail,ψw]
  have cb : (ψw (Order.tail j b₁) : R) = ψ (j+1) := by simp [Order.tail,ψw]
  dsimp only
  rw [ca,cb,step _ _ hl,step _ _ hr]
  have comm := (show Commute (x ⟨j+1,by omega⟩ : R) (e (q D)) from x_mul_e _ _)
  simpa only [reduceCtorEq,↓reduceIte,stendhalQ_inl_inr,stendhalQ_inr_inl,ncEval_x2,map_pow,
    rename_X,pol_X,Matrix.cons_val_zero,Matrix.cons_val_one,(comm.pow_left _).eq] using And.intro l r

/-- For independently marked components of a projective relation, the joint can
be marked after the smaller of the two return powers, with no condition on which
black supplies the mark. In particular a zero exponent gives an undotted marked
lift. This is not division by that power when both pairings are positive.
Source: Webster v2, (4.2) and the cut in Lemma 6.8 after (6.21). -/
theorem interleaved_joint_dot_mem {a b : Fin ℓ} {i : I} (hQ : KLRSymm Q) {Lr Mr : List (Fin ℓ)}
    (t : KLR.Seq μ) (ht : redWord t = Lr ++ a :: b :: Mr) (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (hi : s.lbl ⟨j+1,by omega⟩ = .inl i) (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (x y : V)
    (hx : π (e t)*x*π (e (q L)) = x) (hy : π (e t)*y*π (e (q U)) = y) (mx : x ∈ J t a b) (my : y ∈ J t a b)
    (hz : x*π (leg L s) + y*π (leg U s) = 0) : ∃ z : V, π (e t)*z*π (e (q D)) = z ∧
      z*π (leg a₀ (q L)) = x ∧ z*π (leg b₁ (q U)) = -y ∧
      z*π (KLRAlgebra.x ⟨j+1,by omega⟩ ^ min (Λ a i) (Λ b i)) ∈ J t a b := by
  obtain ⟨z,he,h₁,h₂⟩ := (interleaved_quotient_relation_iff Q Λ s j hj hQ t ht hb hi ha x y hx hy).1 hz
  refine ⟨z,he,h₁,h₂,?_⟩
  have fix : z * π (e (q D)) = z := by
    calc _ = (π (e t)*z*π (e (q D))) * π (e (q D)) := congrArg (· * π _) he.symm
         _ = z := by rw [mul_assoc _ (π _),← map_mul π,e_mul_self,he]
  obtain ⟨l,r⟩ := return_joint Q Λ s j hj hb hi ha
  rcases le_total (Λ a i) (Λ b i) with h | h
  · rw [min_eq_left h,← fix,mul_assoc,← map_mul π,← l,map_mul,← mul_assoc,h₁]
    exact TwoSidedIdeal.mul_mem_right _ _ _ mx
  · rw [min_eq_right h,← fix,mul_assoc,← map_mul π,← r,map_mul,← mul_assoc,h₂]
    exact TwoSidedIdeal.mul_mem_right _ _ _ ((J t a b).neg_mem my)

end Categorification.Stendhal.BraidedStendhalAlgebra
