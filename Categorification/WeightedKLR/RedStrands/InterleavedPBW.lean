/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.InterleavedColumn

/-!
# Right parabolic words for the two exits

Webster, arXiv:1309.3796v2, §6.1, Proposition 6.4 and the kernel test after
(6.21) in Lemma 6.8. Sort just the three bottom positions. Keep the same exterior
word on every member of its right coset; only the local suffix changes.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra.ExitPBW
open KLR KLRAlgebra TypeA Equiv MvPolynomial

/-- Relative order of the images of the three adjacent bottom positions. -/
inductive Order | abc | bac | acb | bca | cab | cba deriving DecidableEq

/-- A word for the relative order, read from right to left. -/
def Order.tail (j : ℕ) : Order → List ℕ
  | .abc => [] | .bac => [j] | .acb => [j+1]
  | .bca => [j,j+1] | .cab => [j+1,j] | .cba => [j,j+1,j]

section Words
variable {m j : ℕ} (h : j+2 < m)
local notation "p₀" => Fin.mk j (Nat.lt_trans (by omega) h)
local notation "p₁" => Fin.mk (j+1) (Nat.lt_trans (by omega) h)
local notation "p₂" => Fin.mk (j+1+1) h
local notation "τ" => fun o : Order => wordProd m (Order.tail j o)

/-- Minimal representatives for the right parabolic on the three local positions. -/
def Sorted (w : Perm (Fin m)) : Prop := w p₀ < w p₁ ∧ w p₁ < w p₂

def order (w : Perm (Fin m)) : Order :=
  if w p₀ < w p₁ then
    if w p₁ < w p₂ then .abc else if w p₀ < w p₂ then .acb else .bca
  else if w p₀ < w p₂ then .bac else if w p₁ < w p₂ then .cab else .cba

private theorem swap₀₂ : sadj m j p₂ = p₂ := sadj_apply_of_ne _ (by dsimp; omega) (by simp)
private theorem swap₁₀ : sadj m (j+1) p₀ = p₀ := sadj_apply_of_ne _ (by simp) (by dsimp; omega)

local macro "positions" : tactic => `(tactic|
  simp (disch := omega) only [Order.tail,wordProd_cons,wordProd_nil,mul_one,mul_inv_rev,sadj_inv,inv_one,
    Perm.mul_apply,Perm.one_apply,sadj_apply_left,sadj_apply_right,swap₀₂,swap₁₀] at *)

theorem sorted_strip (w : Perm (Fin m)) : Sorted h (w * (τ (order h w))⁻¹) := by
  have n₀₁ := w.injective.ne (show p₀ ≠ p₁ by simp [Fin.ext_iff])
  have n₁₂ := w.injective.ne (show p₁ ≠ p₂ by simp [Fin.ext_iff])
  have n₀₂ := w.injective.ne (show p₀ ≠ p₂ from fun he => by have := congrArg Fin.val he; dsimp at this; omega)
  unfold order Sorted
  split_ifs <;> positions <;> constructor <;> omega

private theorem order_mul {u : Perm (Fin m)} (hu : Sorted h u) (o : Order) : order h (u * τ o) = o := by
  obtain ⟨h₀,h₁⟩ := hu
  cases o <;> unfold order <;> positions <;> split_ifs <;> first | rfl | omega

private theorem append_ascent {w : Perm (Fin m)} {l : List ℕ}
    (hl : IsReduced m l ∧ wordProd m l = w) (n : ℕ) (hn : n+1 < m)
    (ha : w ⟨n,Nat.lt_of_succ_lt hn⟩ < w ⟨n+1,hn⟩) :
    IsReduced m (l ++ [n]) ∧ wordProd m (l ++ [n]) = w * sadj m n := by
  have hw : wordProd m (l ++ [n]) = w * sadj m n := by rw [wordProd_append,hl.2,wordProd_singleton]
  refine ⟨⟨validWord_append.2 ⟨hl.1.1,by simp [ValidWord]; omega⟩,?_⟩,hw⟩
  rw [hw,List.length_append,hl.1.2,hl.2,length_mul_sadj_of_lt hn ha]; rfl

private theorem sorted_append {u : Perm (Fin m)} (hu : Sorted h u) (o : Order) :
    IsReduced m (canWord m u ++ o.tail j) ∧ wordProd m (canWord m u ++ o.tail j) = u * τ o := by
  have e₀ : IsReduced m (canWord m u) ∧ wordProd m (canWord m u) = u :=
    ⟨isReduced_canWord _ _,wordProd_canWord _ _⟩
  obtain ⟨h₀,h₁⟩ := hu
  have ea := append_ascent e₀ j (by omega) h₀
  have eb := append_ascent e₀ (j+1) h h₁
  have eab := append_ascent ea (j+1) h (by positions; exact h₀.trans h₁)
  have eba := append_ascent eb j (by omega) (by positions; exact h₀.trans h₁)
  have eaba := append_ascent eab j (by omega) (by positions; exact h₁)
  cases o <;> simp only [Order.tail,wordProd_cons,wordProd_nil,mul_one,List.append_nil] <;>
    first | exact e₀ | exact ea | exact eb | simpa only [List.append_assoc,List.singleton_append,mul_assoc] using eab
          | simpa only [List.append_assoc,List.singleton_append,mul_assoc] using eba
          | simpa only [List.append_assoc,List.cons_append,List.nil_append,mul_assoc] using eaba

/-- PBW words with a single exterior prefix on each right coset. -/
def word (w : Perm (Fin m)) := canWord m (w * (τ (order h w))⁻¹) ++ (order h w).tail j

theorem word_choice : IsReducedChoice (word h) := fun w => by
  simpa only [word,mul_assoc,inv_mul_cancel,mul_one] using sorted_append h (sorted_strip h w) (order h w)

theorem word_mul {u : Perm (Fin m)} (hu : Sorted h u) (o : Order) :
    word h (u * τ o) = canWord m u ++ o.tail j := by
  simp only [word,order_mul h hu,mul_assoc,mul_inv_cancel,mul_one]

theorem left_orders {u : Perm (Fin m)} (hu : Sorted h u) (o : Order)
    (hw : (u * τ o) p₁ < (u * τ o) p₂) : o = .abc ∨ o = .bac ∨ o = .cab := by
  obtain ⟨h₀,h₁⟩ := hu
  cases o <;> positions <;> first | trivial | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | omega

theorem right_orders {u : Perm (Fin m)} (hu : Sorted h u) (o : Order)
    (hw : (u * τ o) p₀ < (u * τ o) p₁) : o = .abc ∨ o = .acb ∨ o = .bca := by
  obtain ⟨h₀,h₁⟩ := hu
  cases o <;> positions <;> first | trivial | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | omega

end Words

section Diagrams
variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "Pol" => MvPolynomial (Fin n) k
variable (s : KLR.Seq (stendhalWeight ℓ ν)) (j : ℕ) (hj : j+2 < (stendhalWeight ℓ ν).card)
local notation "w₀" => fun o : Order => Order.tail j o
local notation "q" => fun o : Order => wordProd n (w₀ o) • s
local notation "leg" => fun (o : Order) (v : KLR.Seq μ) => (ψw (w₀ o) * e v : R)
local notation "A" => Order.bac
local notation "B" => Order.acb
local notation "L" => Order.cab
local notation "D" => Order.cba
local notation "Rr" => Order.bca

private theorem end_leg (l : List ℕ) (v : KLR.Seq μ) :
    (e (wordProd n l • v) * (ψw l * e v) : R) = ψw l * e v := by
  rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]

omit [DecidableEq I] in
private theorem local_labels {b a : Fin ℓ} {i : I}
    (hb : s.lbl ⟨j,by omega⟩ = .inr b) (hi : s.lbl ⟨j+1,by omega⟩ = .inl i)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) :
    (q L).lbl ⟨j,by omega⟩ = .inl i ∧ (q L).lbl ⟨j+1,by omega⟩ = .inr a ∧
    (q Rr).lbl ⟨j+1,by omega⟩ = .inr b ∧ (q Rr).lbl ⟨j+2,hj⟩ = .inl i := by
  simp only [Order.tail,wordProd_cons,wordProd_nil,mul_one,mul_smul,lbl_sadj,
    sadj_apply_left (show j+1 < n by omega),sadj_apply_right (show j+1 < n by omega),
    sadj_apply_right hj,sadj_apply_left hj,swap₀₂ hj,swap₁₀ hj,hb,hi,ha,and_self]

private theorem exit_squares {a b : Fin ℓ} {i : I}
    (hb : s.lbl ⟨j,by omega⟩ = .inr b) (hi : s.lbl ⟨j+1,by omega⟩ = .inl i)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) :
    (ψ j * ψ j * e (q L) : R) = x ⟨j,by omega⟩ ^ Λ a i * e (q L) ∧
    (ψ (j+1) * ψ (j+1) * e (q Rr) : R) = x ⟨j+2,hj⟩ ^ Λ b i * e (q Rr) := by
  obtain ⟨il,al,br,ir⟩ := local_labels s j hj hb hi ha
  have lsq := ψ_sq (Q := stendhalQ Q Λ) j (by omega) (q L)
  have rsq := ψ_sq (Q := stendhalQ Q Λ) (j+1) hj (q Rr)
  rw [il,al] at lsq; rw [br,ir] at rsq
  simpa only [reduceCtorEq,↓reduceIte,stendhalQ_inl_inr,stendhalQ_inr_inl,ncEval_x2,map_pow,
    rename_X,pol_X,Matrix.cons_val_zero,Matrix.cons_val_one] using And.intro lsq rsq

/-- Components of the joint map on the two extreme right-parabolic rows. Its
second component is taken with a minus sign in the two-exit presentation. The
middle row is the single crossing on each side. Source: Webster v2, (4.2), §6.1,
Lemma 6.8 after (6.21). -/
theorem joint_rows {a b : Fin ℓ} {i : I}
    (hb : s.lbl ⟨j,by omega⟩ = .inr b) (hi : s.lbl ⟨j+1,by omega⟩ = .inl i)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) :
    leg A (q D) * leg A (q L) = x ⟨j,by omega⟩ ^ Λ a i * e (q L) ∧
    leg A (q D) * leg B (q Rr) = leg Rr (q Rr) ∧
    leg B (q D) * leg A (q L) = leg L (q L) ∧
    leg B (q D) * leg B (q Rr) = x ⟨j+2,hj⟩ ^ Λ b i * e (q Rr) := by
  have cutL := end_leg Q Λ (w₀ A) (q L)
  have cutR := end_leg Q Λ (w₀ B) (q Rr)
  have hl : wordProd n (w₀ A) • q L = q D := by
    simp only [Order.tail,wordProd_cons,wordProd_nil,mul_one,mul_smul]
  have hr : wordProd n (w₀ B) • q Rr = q D := by
    simpa only [Order.tail,wordProd_cons,wordProd_nil,mul_one,mul_smul] using (braid_smul hj s).symm
  rw [hl] at cutL; rw [hr] at cutR
  obtain ⟨lsq,rsq⟩ := exit_squares Q Λ s j hj hb hi ha
  simp only [mul_assoc,cutL,cutR]
  simp only [Order.tail,ψw_cons,ψw_nil,mul_one,mul_assoc] at lsq rsq ⊢
  exact ⟨lsq, trivial, trivial, rsq⟩

/-- Local rows of the two-exit column. `w` is the common exterior prefix, with
an arbitrary bottom polynomial `f` immediately below it. The return powers are
at that cut, never transported through `w`. The three rows correspond to `i a b`,
`a i b`, `a b i`. Source: Webster v2, §6.1, Prop. 6.4, (4.2), and (6.21). -/
theorem exit_rows {a b : Fin ℓ} {i : I}
    (hb : s.lbl ⟨j,by omega⟩ = .inr b) (hi : s.lbl ⟨j+1,by omega⟩ = .inl i)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (w : List ℕ) (f : Pol) :
    let H : R := ψw w * pol f
    let xL : R := x ⟨j,by omega⟩ ^ Λ a i
    let xR : R := x ⟨j+2,hj⟩ ^ Λ b i
    (H * leg Rr (q Rr)) * leg Rr s = (H*xL) * leg L s ∧
    (H * leg A (q L)) * leg L s = H * leg D s ∧
    (H * leg B (q Rr)) * leg Rr s = H * leg D s ∧
    (H * leg L (q L)) * leg L s = (H*xR) * leg Rr s := by
  intro H xL xR
  have ne : s.lbl ⟨j,by omega⟩ ≠ s.lbl ⟨j+2,hj⟩ := by
    intro eq
    have hab := Sum.inr_injective (hb.symm.trans (eq.trans ha))
    have hh := lbl_inj_of_inr s a (hab ▸ hb) ha
    have := congrArg Fin.val hh; dsimp at this; omega
  have braid := KLRAlgebra.braid (Q := stendhalQ Q Λ) j hj s
  rw [ite_eq_right (fun h => ne h.1),sub_mul,sub_eq_zero] at braid
  obtain ⟨lsq,rsq⟩ := exit_squares Q Λ s j hj hb hi ha
  have el := end_leg Q Λ (w₀ L) s; have er := end_leg Q Λ (w₀ Rr) s
  have bl : (ψ j * leg L s : R) = ψ (j+1) * leg Rr s := by
    simpa only [Order.tail,ψw_cons,ψw_nil,mul_one,mul_assoc] using braid
  have rl : (ψw (w₀ Rr) * leg Rr s : R) = xL * leg L s := by
    calc _ = ψ j * (ψ (j+1) * leg Rr s) := by simp [Order.tail,ψw,mul_assoc]
         _ = (ψ j * ψ j * e (q L)) * leg L s := by rw [← bl,mul_assoc _ (e _),el,mul_assoc]
         _ = _ := by rw [lsq,mul_assoc,el]
  have lr : (ψw (w₀ L) * leg L s : R) = xR * leg Rr s := by
    calc _ = ψ (j+1) * (ψ j * leg L s) := by simp [Order.tail,ψw,mul_assoc]
         _ = (ψ (j+1) * ψ (j+1) * e (q Rr)) * leg Rr s := by rw [bl,mul_assoc _ (e _),er,mul_assoc]
         _ = _ := by rw [rsq,mul_assoc,er]
  simp only [mul_assoc,el,er,rl,lr]
  simp only [Order.tail,ψw_cons,ψw_nil,mul_one,mul_assoc] at bl ⊢
  simp only [bl,eq_self,and_self]

private def Clean (v : KLR.Seq μ) : List ℕ → Prop
  | [] => True
  | c :: l => Clean v l ∧ ∃ hc : c+1 < n, (wordProd n l • v).lbl ⟨c,Nat.lt_of_succ_lt hc⟩ ≠
      (wordProd n l • v).lbl ⟨c+1,hc⟩

/-- Dots pass through the local suffix, not through the exterior prefix. -/
private theorem slide_clean (v : KLR.Seq μ) (l : List ℕ) (f : Pol) (hc : Clean v l) :
    (ψw l * pol f * e v : R) = pol (rename (wordProd n l) f) * (ψw l * e v) := by
  induction l with
  | nil => simp [ψw]
  | cons c l ih =>
    obtain ⟨hc',h,ne⟩ := hc
    let u := wordProd n l • v
    let z := (ψw l * e v : R)
    have fix : e u * z = z := end_leg Q Λ l v
    let g := rename (wordProd n l) f
    have sw := ψ_mul_pol_mul_e (Q := stendhalQ Q Λ) c h u g
    rw [ite_eq_right ne,add_zero] at sw
    have eq : swapPol c h g = rename (wordProd n (c::l)) f := by
      simp only [g,swapPol,rename_rename,wordProd_cons,Perm.coe_mul,sadj,dite_eq_left h]
    rw [eq] at sw
    calc _ = ψ c * (ψw l * pol f * e v) := by simp only [ψw_cons,mul_assoc]
         _ = (ψ c * pol g * e u) * z := by rw [ih hc',mul_assoc _ (e u),fix,mul_assoc]
         _ = _ := by rw [sw,mul_assoc _ (e u),fix,ψw_cons]; simp only [z,mul_assoc]

omit [DecidableEq I] in
private theorem tail_clean (v : KLR.Seq μ) (o : Order)
    (h₀ : v.lbl ⟨j,by omega⟩ ≠ v.lbl ⟨j+1,by omega⟩)
    (h₁ : v.lbl ⟨j+1,by omega⟩ ≠ v.lbl ⟨j+2,hj⟩)
    (h₂ : v.lbl ⟨j,by omega⟩ ≠ v.lbl ⟨j+2,hj⟩) : Clean v (w₀ o) := by
  cases o <;> simp only [Order.tail,Clean,true_and] <;> repeat' apply And.intro
  all_goals first | trivial | refine ⟨by omega,?_⟩
  all_goals simp (disch := omega) only [wordProd_cons,wordProd_nil,mul_one,mul_smul,one_smul,
    lbl_sadj,sadj_apply_left,sadj_apply_right,swap₀₂,swap₁₀]; assumption

/-- A polynomial immediately below a sorted exterior word and above any local
suffix is the PBW polynomial with its variables permuted by that suffix alone.
No restriction on repeated colours outside the three positions. -/
theorem local_polynomial (v : KLR.Seq μ) (o : Order) (f : Pol)
    (h₀ : v.lbl ⟨j,by omega⟩ ≠ v.lbl ⟨j+1,by omega⟩)
    (h₁ : v.lbl ⟨j+1,by omega⟩ ≠ v.lbl ⟨j+2,hj⟩)
    (h₂ : v.lbl ⟨j,by omega⟩ ≠ v.lbl ⟨j+2,hj⟩) :
    (ψw (w₀ o) * pol f * e v : R) = pol (rename (wordProd n (w₀ o)) f) * leg o v :=
  slide_clean Q Λ v _ f (tail_clean j hj v o h₀ h₁ h₂)

private theorem polynomial_ext {N M : Type*} [AddCommGroup M] [Module k M]
    (a b : MvPolynomial N k →ₗ[k] M) (h : ∀ d, a (monomial d 1) = b (monomial d 1)) : a = b :=
  (basisMonomials N k).ext fun d => by simpa only [coe_basisMonomials] using h d

/-- Polynomial coordinates with the same exterior representative on a whole right
coset. A linear readout prescribed at the bottom of this representative extends
to the column. The distinctness condition is only on the three local labels.
Source: Webster v2, §6.1, Prop. 6.4. -/
theorem exists_parabolic_read {M : Type*} [AddCommGroup M] [Module k M] (hQ : KLRSymm Q)
    (h₀ : s.lbl ⟨j,by omega⟩ ≠ s.lbl ⟨j+1,by omega⟩)
    (h₁ : s.lbl ⟨j+1,by omega⟩ ≠ s.lbl ⟨j+2,hj⟩)
    (h₂ : s.lbl ⟨j,by omega⟩ ≠ s.lbl ⟨j+2,hj⟩)
    (F : Perm (Fin n) → Order → Pol →ₗ[k] M) : ∃ read : R →ₗ[k] M,
    ∀ u, Sorted hj u → ∀ o f, read (ψw (canWord n u) * pol f * leg o s) = F u o f := by
  let bs := basisOfSymm (ν := μ) (stendhalQ_symm Q Λ hQ) (word hj) (word_choice hj)
  let value (w : Perm (Fin n)) : Pol →ₗ[k] M :=
    let o := order hj w
    (F (w * (wordProd n (w₀ o))⁻¹) o).comp (rename (wordProd n (w₀ o))).toLinearMap
  let read := bs.constr k fun b => value b.2.1 (monomial b.2.2 1)
  have basic (w : Perm (Fin n)) (f : Pol) : read (ψw (word hj w) * pol f * e s) = value w f := by
    let atWord := (LinearMap.mulRight k (e s : R)).comp ((LinearMap.mulLeft k (ψw (word hj w))).comp pol.toLinearMap)
    apply LinearMap.congr_fun (f := read.comp atWord) (g := value w) _ f
    apply polynomial_ext; intro d
    simp only [atWord,LinearMap.comp_apply,LinearMap.mulRight_apply,LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply]
    have eq : bs (s,w,d) = ψw (word hj w) * pol (monomial d 1) * e s :=
      basisOfSymm_apply (stendhalQ_symm Q Λ hQ) (word hj) (word_choice hj) (s,w,d)
    rw [← eq]
    exact bs.constr_basis k _ (s,w,d)
  refine ⟨read,fun u hu o f => ?_⟩
  let v := wordProd n (w₀ o)
  let g := rename (v⁻¹ : Perm (Fin n)) f
  have hg : rename v g = f := by simp only [g,rename_rename,← Perm.coe_mul,mul_inv_cancel,Perm.coe_one,rename_id_apply]
  have slide := local_polynomial Q Λ j hj s o g h₀ h₁ h₂
  rw [show rename (wordProd n (w₀ o)) g = f from hg] at slide
  have key := basic (u*v) g
  rw [word_mul hj hu o,ψw_append] at key
  calc read _ = value (u*v) g := by rw [mul_assoc,← slide]; simpa only [mul_assoc] using key
       _ = _ := by
         change F ((u*v) * _) (order hj (u*v)) _ = _
         rw [show order hj (u*v) = o from order_mul hj hu o]
         change F (u*v*v⁻¹) o (rename v g) = _
         rw [mul_assoc,mul_inv_cancel,mul_one,hg]

end Diagrams
end Categorification.Stendhal.BraidedStendhalAlgebra.ExitPBW
