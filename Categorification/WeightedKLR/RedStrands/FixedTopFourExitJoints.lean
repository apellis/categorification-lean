/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EqualBlackHigherPair
import Categorification.KLR.ReturnCrossing
import Categorification.KLR.DividedPowerIdempotents
import Categorification.WeightedKLR.RedStrands.TwoBlackExitWords
import Categorification.KLR.MixedJointKernel

/-!
# Four-exit relations at the fixed right-extreme top

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 and the cut after (6.21).
At the extreme, mixed and full right tops of the five-slot equal-black interval, three common
descents express a supported affine exit relation by its neighboring joints.
The surviving rightmost coefficient is detected by the two reduced PBW rows.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLR.KLRAlgebra Equiv TypeA

variable {I : Type*} {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

/-- With two total black strands of the same colour, the right extreme loading
is stabilized by the identity and the adjacent black transposition. -/
theorem twoBlack_extreme_stabilizer_of_card_two (r : KLR.Seq μ) (b : ℕ) (hp : b + 2 < m)
    (hν : ν.card = 2) (i : I)
    (hL : r.lbl ⟨b + 1, by omega⟩ = Sum.inl i) (hH : r.lbl ⟨b + 2, hp⟩ = Sum.inl i)
    (w : Perm (Fin m)) : w • r = r ↔ w = 1 ∨ w = sadj m (b + 1) := by
  constructor
  · intro h
    have h' : (w * sadj m b) • (sadj m b • r) = r := by
      simpa only [mul_smul, sadj_smul_smul] using h
    have hs := (twoBlack_return_permutations_of_card_two r b hp hν i hL hH _).mp h'
    rcases hs with hs | hs
    · left
      have := congrArg (· * sadj m b) hs
      simpa only [mul_assoc, TypeA.sadj_mul_self, mul_one, wordProd_cons, wordProd_nil] using this
    · right
      have := congrArg (· * sadj m b) hs
      simpa only [mul_assoc, TypeA.sadj_mul_self, mul_one, wordProd_cons, wordProd_nil] using this
  · rintro (rfl | rfl)
    · exact one_smul _ _
    · exact sadj_smul_eq_self hp (hL.trans hH.symm)

end Categorification.Stendhal.BraidedStendhalAlgebra


namespace Categorification.TypeA

private theorem isReduced_shift_four {n p : ℕ} (hp : p + 3 < n) {ρ : List ℕ}
    (hρ : IsReduced 4 ρ) : IsReduced n (shiftWord p ρ) := by
  have hn (k : ℕ) : IsReduced k [] := by simp [IsReduced, ValidWord, wordProd]
  have hm := (hn p).append_shiftWord (show p + 4 = p + 4 from rfl) hρ
  have h := hm.append_shiftWord (show p + 4 + (n - (p + 4)) = n by omega) (hn (n - (p + 4)))
  simpa only [List.nil_append, shiftWord, List.map_nil, List.append_nil] using h

theorem twoBlack_right_extreme_words_reduced {n p : ℕ} (hp : p + 3 < n) :
    IsReduced n [p, p + 1, p + 2] ∧ IsReduced n [p + 2, p, p + 1, p + 2] := by
  have h₁ : IsReduced 4 [0, 1, 2] := by
    refine ⟨by simp [ValidWord], ?_⟩
    rw [length_eq_invCount]
    decide +kernel
  have h₂ : IsReduced 4 [2, 0, 1, 2] := by
    refine ⟨by simp [ValidWord], ?_⟩
    rw [length_eq_invCount]
    decide +kernel
  simpa [shiftWord] using ⟨isReduced_shift_four hp h₁, isReduced_shift_four hp h₂⟩

end Categorification.TypeA

namespace Categorification.Stendhal.BraidedStendhalAlgebra

/-- The four-exit descent cascade with independent top and exit idempotents. -/
theorem exists_rectangular_jointCascade {R : Type*} [Ring R]
    (topCut e₀ e₁ e₂ e₃ jA jB jD : R) (idem : topCut*topCut=topCut)
    (l₀ l₁ l₂ l₃ a₀ a₁ b₁ b₂ d₂ d₃ : R)
    (legA : a₀*l₀=a₁*l₁) (legB : b₁*l₁=b₂*l₂) (legD : d₂*l₂=d₃*l₃)
    (cutA₁ : a₁*e₁=a₁) (cutB₂ : b₂*e₂=b₂) (cutD₂ : d₂*e₂=d₂)
    (factorA : ∀ x, topCut*x*e₀=x → ∃ z, topCut*z*jA=z ∧ z*a₀=x)
    (factorB : ∀ x, topCut*x*e₁=x → ∃ z, topCut*z*jB=z ∧ z*b₁=x)
    (factorD : ∀ x, topCut*x*e₃=x → ∃ z, topCut*z*jD=z ∧ z*d₃=x)
    (cancel : ∀ x, topCut*x*e₂=x → x*l₂=0 → x=0)
    (x₀ x₁ x₂ x₃ : R) (h₀ : topCut*x₀*e₀=x₀) (h₁ : topCut*x₁*e₁=x₁)
    (h₂ : topCut*x₂*e₂=x₂) (h₃ : topCut*x₃*e₃=x₃)
    (rel : x₀*l₀+x₁*l₁+x₂*l₂+x₃*l₃=0) :
    ∃ u v w : R, topCut*u*jA=u ∧ topCut*v*jB=v ∧ topCut*w*jD=w ∧
      x₀=u*a₀ ∧ x₁=v*b₁-u*a₁ ∧ x₂=w*d₂-v*b₂ ∧ x₃=-(w*d₃) := by
  have top (x e' : R) (h : topCut*x*e'=x) : topCut*x=x := by
    have ht := congrArg (fun y => topCut*y) h
    change topCut*(topCut*x*e')=topCut*x at ht
    rw [← mul_assoc topCut,← mul_assoc topCut,idem,h] at ht
    exact ht.symm
  have cutProduct (x d u e' : R) (h : topCut*x*d=x) (hu : u*e'=u) :
      topCut*(x*u)*e'=x*u := by
    rw [← mul_assoc topCut,top x d h,mul_assoc,hu]
  obtain ⟨u,hu,hu0⟩ := factorA x₀ h₀
  have hu1 := cutProduct u jA a₁ e₁ hu cutA₁
  obtain ⟨v,hv,hv1⟩ := factorB (x₁+u*a₁) (by simp only [mul_add,add_mul,h₁,hu1])
  obtain ⟨w,hw,hw3⟩ := factorD (-x₃)
    (by simpa only [mul_neg,neg_mul] using congrArg Neg.neg h₃)
  have x1 : x₁=v*b₁-u*a₁ := by rw [hv1,add_sub_cancel_right]
  have x3 : x₃=-(w*d₃) := by rw [hw3,neg_neg]
  have hcut : topCut*(x₂+v*b₂-w*d₂)*e₂=x₂+v*b₂-w*d₂ := by
    simp only [mul_add,mul_sub,add_mul,sub_mul,h₂,cutProduct v jB b₂ e₂ hv cutB₂,
      cutProduct w jD d₂ e₂ hw cutD₂]
  have hc : (x₂+v*b₂-w*d₂)*l₂=0 := by
    calc
      _ = x₀*l₀+x₁*l₁+x₂*l₂+x₃*l₃ := by
        rw [← hu0,x3]
        simp only [sub_mul,add_mul,neg_mul,mul_assoc,legA,legD]
        rw [← legB,← mul_assoc v b₁,hv1,add_mul,mul_assoc]
        abel
      _ = 0 := rel
  have x2 : x₂=w*d₂-v*b₂ := by
    have hh := congrArg (fun t => t-v*b₂+w*d₂) (cancel _ hcut hc)
    change x₂+v*b₂-w*d₂-v*b₂+w*d₂=0-v*b₂+w*d₂ at hh
    abel_nf at hh ⊢
    exact hh
  exact ⟨u,v,w,hu,hv,hw,hu0.symm,x1,x2,x3⟩

/-- Three successive supported factorizations present a relation by the
neighboring joints. The rightmost exit must detect zero on the upper cut. -/
theorem exists_fixedTop_jointCascade {R : Type*} [Ring R]
    (e₀ e₁ e₂ e₃ jA jB jD : R) (idem : e₂*e₂=e₂)
    (l₀ l₁ l₂ l₃ a₀ a₁ b₁ b₂ d₂ d₃ : R)
    (legA : a₀*l₀=a₁*l₁) (legB : b₁*l₁=b₂*l₂) (legD : d₂*l₂=d₃*l₃)
    (cutA₁ : a₁*e₁=a₁) (cutB₂ : b₂*e₂=b₂) (cutD₂ : d₂*e₂=d₂)
    (factorA : ∀ x, e₂*x*e₀=x → ∃ z, e₂*z*jA=z ∧ z*a₀=x)
    (factorB : ∀ x, e₂*x*e₁=x → ∃ z, e₂*z*jB=z ∧ z*b₁=x)
    (factorD : ∀ x, e₂*x*e₃=x → ∃ z, e₂*z*jD=z ∧ z*d₃=x)
    (cancel : ∀ x, e₂*x*e₂=x → x*l₂=0 → x=0)
    (x₀ x₁ x₂ x₃ : R) (h₀ : e₂*x₀*e₀=x₀) (h₁ : e₂*x₁*e₁=x₁)
    (h₂ : e₂*x₂*e₂=x₂) (h₃ : e₂*x₃*e₃=x₃)
    (rel : x₀*l₀+x₁*l₁+x₂*l₂+x₃*l₃=0) :
    ∃ u v w : R, e₂*u*jA=u ∧ e₂*v*jB=v ∧ e₂*w*jD=w ∧
      x₀=u*a₀ ∧ x₁=v*b₁-u*a₁ ∧ x₂=w*d₂-v*b₂ ∧ x₃=-(w*d₃) :=
  exists_rectangular_jointCascade e₂ e₀ e₁ e₂ e₃ jA jB jD idem l₀ l₁ l₂ l₃ a₀ a₁ b₁ b₂ d₂ d₃
    legA legB legD cutA₁ cutB₂ cutD₂ factorA factorB factorD cancel x₀ x₁ x₂ x₃ h₀ h₁ h₂ h₃ rel

end Categorification.Stendhal.BraidedStendhalAlgebra


namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv MvPolynomial

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "A" => BraidedStendhalAlgebra k Q Λ ν
local notation "raw" => ofKLR k Q Λ ν
local notation "E" => fun v : Seq μ => raw (e v)

private theorem idempotent_cut (v : Seq μ) : E v*E v=E v := by
  rw [← map_mul,e_mul_self]

/-- A common descent in the permutations between two loadings extracts the same
single right crossing from every affine coefficient. -/
theorem exists_supported_descent_factor (hQ : KLRSymm Q) (s t : Seq μ)
    (j : ℕ) (hj : j+1<n)
    (desc : ∀ w : Perm (Fin n), w • s=t → w ⟨j+1,hj⟩ < w ⟨j,by omega⟩)
    (x : A) (hx : E t*x*E s=x) :
    ∃ y : A, E t*y*E (sadj n j • s)=y ∧ y*raw (ψ j*e s)=x := by
  let ρ := descentWord hj
  let hρ := descentWord_spec hj
  let step : R →ₗ[k] R := LinearMap.mulRight k (ψ j*e s)
  obtain ⟨z,rfl⟩ := ofKLR_surjective (Q := Q) (Λ := Λ) x
  let B := lbasis («μ» := μ) (stendhalQ_symm Q Λ hQ) ρ hρ
  have H : ∀ a : R, (e t*a*e s : R) ∈ LinearMap.range step := by
    intro z'
    induction B.mem_span z' using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add,add_mul]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm,smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
    | mem _ hz =>
      obtain ⟨⟨a,w,d⟩,rfl⟩ := hz
      rw [show B (a,w,d)=_ from lbasis_apply ..,mul_assoc,mul_assoc _ (e a),e_mul_e]
      by_cases ha : a=s
      · subst a
        rw [ite_eq_left rfl]
        by_cases hw : w • s=t
        · obtain ⟨l,hl⟩ := exists_descentWord_eq_append hj w (desc w hw)
          refine ⟨e t*pol (monomial d 1)*ψw l,?_⟩
          simp only [step,LinearMap.mulRight_apply,ρ,hl,ψw_append,ψw_cons,ψw_nil,mul_one,mul_assoc]
        · have cut := e_mul_pol_ψw_e (Q := stendhalQ Q Λ) (monomial d (1:k)) (ρ w) s
          rw [(hρ w).2] at cut
          rw [← cut,← mul_assoc,e_mul_e,ite_eq_right (Ne.symm hw),zero_mul]
          exact zero_mem _
      · rw [ite_eq_right ha,mul_zero,mul_zero]
        exact zero_mem _
  obtain ⟨d,hd⟩ := H z
  have eq : E t*raw z*E s=raw d*raw (ψ j*e s) := by
    simpa only [step,LinearMap.mulRight_apply,map_mul] using (congrArg raw hd).symm
  let u := sadj n j • s
  have cut : E u*raw (ψ j*e s)=raw (ψ j*e s) := by
    simp only [← map_mul,u]
    rw [ψ_mul_e,← mul_assoc,e_mul_self]
  refine ⟨E t*raw d*E u,?_,?_⟩
  · change E t*(E t*raw d*E u)*E u=E t*raw d*E u
    calc
      _ = (E t*E t)*raw d*(E u*E u) := by simp only [mul_assoc]
      _ = _ := by rw [idempotent_cut,idempotent_cut]
  · rw [mul_assoc _ (E u),cut,mul_assoc,← eq,← mul_assoc,← mul_assoc,idempotent_cut,hx]

/-- A reduced lower word is right-cancellative on an affine corner with two
upper PBW rows if the black-swap extension of that lower word is reduced. -/
theorem eq_zero_of_rightWord_in_twoRowCorner (hQ : KLRSymm Q) (s t : Seq μ)
    (l : List ℕ) (j : ℕ) (hj : j+1<n) (hl : IsReduced n l)
    (hjl : IsReduced n (j::l)) (ht : wordProd n l • s=t)
    (matching : ∀ w : Perm (Fin n), w • t=t ↔ w=1 ∨ w=sadj n j)
    (z : A) (cut : E t*z*E t=z) (zero : z*raw (ψw l*e s)=0) : z=0 := by
  let K := toKLR k Q Λ ν
  have left : E t*z=z := by
    have h := congrArg (fun y => E t*y) cut
    change E t*(E t*z*E t)=E t*z at h
    rw [← mul_assoc (E t),← mul_assoc (E t),idempotent_cut,cut] at h
    exact h.symm
  have right : z*E t=z := by
    have h := congrArg (fun y => y*E t) cut
    change E t*z*E t*E t=z*E t at h
    rw [mul_assoc _ (E t),idempotent_cut,cut] at h
    exact h.symm
  have heT : K (E t)=e t := by
    change toKLR k Q Λ ν (ofKLR k Q Λ ν (e t))=e t
    rw [toKLR_ofKLR_e]
  have Hleft : e t*K z=K z := by
    rw [← heT,← map_mul K,left]
  have Hright : K z*e t=K z := by
    rw [← heT,← map_mul K,right]
  have nilRed : IsReduced n [] := by constructor <;> simp [ValidWord,wordProd_nil]
  have singleRed : IsReduced n [j] := by
    refine ⟨by simp [ValidWord,hj],?_⟩
    rw [wordProd_singleton,length_sadj hj]
    rfl
  obtain ⟨f,g,hfg⟩ := KLR.KLRAlgebra.exists_two_corner_coefficients
    (stendhalQ_symm Q Λ hQ) t t [] j nilRed singleRed
    (by simpa only [wordProd_nil,wordProd_singleton] using matching) (K z) Hleft Hright
  have crossCut : (e t : R)*(ψw l*e s)=ψw l*e s := by
    rw [← ht,← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  have sum := congrArg K zero
  simp only [K,map_mul,toKLR_ofKLR_ψw,toKLR_ofKLR_e,map_zero] at sum
  change K z*(ψw l*e s)=0 at sum
  have sum' : (pol f*(ψw l*e s)+pol g*(ψw (j::l)*e s) : R)=0 := by
    rw [hfg,add_mul] at sum
    simpa only [mul_assoc,crossCut,ψw_nil,one_mul,ψw_cons,mul_one] using sum
  have hg := (top_polynomial_pair_eq_zero_iff_of_reduced (stendhalQ_symm Q Λ hQ)
    hl j hjl s f g).1 sum'
  have hz : K z=0 := by simp only [hfg,hg.1,hg.2,map_zero,zero_mul,add_zero]
  rw [← ofKLR_toKLR (hQ := hQ) z,hz,map_zero]


section FixedTop

variable {k : Type*} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ₀
local notation "B" => BraidedStendhalAlgebra k Q Λ ν₀
local notation "R₀" => KLRAlgebra k (stendhalQ Q Λ) μ₀
local notation "F" => ofKLR k Q Λ ν₀
local notation "E₀" => fun v : Seq μ₀ => F (e v)
local notation "leg" => fun (l : List ℕ) (v : Seq μ₀) => F (ψw l*e v)

/-- The exchanged bottom with one earlier red and two equal black strands. -/
def fixedTopFourExitBottom : Seq μ₀ :=
  Seq.ofList [.inr 0,.inr 2,.inl (),.inl (),.inr 1] (by decide)

/-- The four consecutive-red exit cuts in planar order and then reversed-middle order. -/
def fixedTopFourExitCut : Fin 4 → Seq μ₀
  | 0 => Seq.ofList [.inr 0,.inl (),.inl (),.inr 1,.inr 2] (by decide)
  | 1 => Seq.ofList [.inr 0,.inl (),.inr 1,.inr 2,.inl ()] (by decide)
  | 2 => Seq.ofList [.inr 0,.inr 1,.inr 2,.inl (),.inl ()] (by decide)
  | _ => Seq.ofList [.inr 0,.inl (),.inr 1,.inr 2,.inl ()] (by decide)

private abbrev bot := fixedTopFourExitBottom
private abbrev v₀ := fixedTopFourExitCut 0
private abbrev v₁ := fixedTopFourExitCut 1
private abbrev v₂ := fixedTopFourExitCut 2
private abbrev v₃ := fixedTopFourExitCut 3
private abbrev jA := sadj n₀ 2 • v₀
private abbrev jB := sadj n₀ 1 • v₁
private abbrev jD := sadj n₀ 1 • v₃

private abbrev mixed := jB

/-- The three five-slot tops with the earlier two red strands first. The
last red lies before, between, or after the two equal black strands. -/
def FiveSlotRightTop (upper : Seq μ₀) : Prop :=
  upper=v₂ ∨ upper=sadj n₀ 2 • v₂ ∨ upper=sadj n₀ 3 • (sadj n₀ 2 • v₂)

private theorem rightTop_pair_descent (upper : Seq μ₀) (ht : FiveSlotRightTop upper) (v : Seq μ₀) (j : ℕ) (hj : j+1<n₀)
    (hl : v.lbl ⟨j,by omega⟩ = .inl ()) (hr : v.lbl ⟨j+1,hj⟩ = .inr 1)
    (w : Perm (Fin n₀)) (hw : w • v=upper) : w ⟨j+1,hj⟩ < w ⟨j,by omega⟩ := by
  have read (f : Fin n₀) : upper.lbl (w f)=v.lbl f := by
    rw [← hw,lbl_smul,show w⁻¹ (w f)=f from w.symm_apply_apply f]
  have ha : upper.lbl (w ⟨j+1,hj⟩)=.inr 1 := (read _).trans hr
  have hb : upper.lbl (w ⟨j,by omega⟩)=.inl () := (read _).trans hl
  have red : upper.lbl ⟨1,by decide⟩ = .inr 1 := by
    rcases ht with rfl|rfl|rfl <;> decide
  have ha' : w ⟨j+1,hj⟩=⟨1,by decide⟩ := lbl_inj_of_inr upper 1 ha red
  rw [ha']
  have before (p : Fin n₀) (hp : upper.lbl p = .inl ()) : (⟨1,by decide⟩ : Fin n₀) < p := by
    rcases ht with rfl|rfl|rfl <;> fin_cases p <;> first | decide | contradiction
  exact before _ hb

private theorem compose_leg (p q : List ℕ) (v : Seq μ₀)
    (hv : wordProd n₀ q • bot = v) :
    leg p v * leg q bot = leg (p++q) bot := by
  change F (ψw p*e v)*F (ψw q*e bot)=F (ψw (p++q)*e bot)
  rw [← map_mul,ψw_append,← hv]
  have cut : (e (wordProd n₀ q • bot) : R₀)*(ψw q*e bot)=ψw q*e bot := by
    rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  rw [mul_assoc,cut,mul_assoc]

private theorem terminal_cancel_words (hQ : KLRSymm Q) (source upper : Seq μ₀)
    (baseWord : List ℕ) (hbase : wordProd n₀ baseWord • bot=source) (l r : List ℕ)
    (hl₀ : IsReduced n₀ l) (hr₀ : IsReduced n₀ r) (hneq : wordProd n₀ l ≠ wordProd n₀ r)
    (matching : ∀ w : Perm (Fin n₀), w • source=upper ↔ w=wordProd n₀ l ∨ w=wordProd n₀ r)
    (hl₁ : IsReduced n₀ (l++baseWord)) (hr₁ : IsReduced n₀ (r++baseWord))
    (hneq' : wordProd n₀ (l++baseWord) ≠ wordProd n₀ (r++baseWord)) (z : B)
    (hz : E₀ upper * z * E₀ source = z) (zero : z * leg baseWord bot = 0) : z = 0 := by
  let G := toKLR k Q Λ ν₀
  have ex : G (E₀ upper) = e upper := toKLR_ofKLR_e ..
  have ey : G (E₀ source) = e source := toKLR_ofKLR_e ..
  have hl : E₀ upper * z = z := by
    have h := congrArg (fun y => E₀ upper * y) hz
    rw [← mul_assoc (E₀ upper), ← mul_assoc (E₀ upper), ← map_mul, e_mul_self, hz] at h
    exact h.symm
  have hr : z * E₀ source = z := by
    have h := congrArg (fun y => y * E₀ source) hz
    rw [mul_assoc _ (E₀ source), ← map_mul, e_mul_self, hz] at h
    exact h.symm
  have hl' : e upper * G z = G z := by rw [← ex, ← map_mul, hl]
  have hr' : G z * e source = G z := by rw [← ey, ← map_mul, hr]
  obtain ⟨f,g,hfg⟩ := KLR.KLRAlgebra.exists_two_corner_coefficients_of_words
    (stendhalQ_symm Q Λ hQ) source upper l r hl₀ hr₀ hneq matching (G z) hl' hr'
  have sum := congrArg G zero
  simp only [G, map_mul, toKLR_ofKLR_ψw, toKLR_ofKLR_e, map_zero] at sum
  change G z * (ψw baseWord * e bot) = 0 at sum
  have cut : (e source : R₀) * (ψw baseWord * e bot) = ψw baseWord * e bot := by
    rw [← hbase,
      ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  rw [hfg, add_mul] at sum
  simp only [mul_assoc, cut] at sum
  rw [← mul_assoc (ψw l), ← mul_assoc (ψw r), ← ψw_append, ← ψw_append] at sum
  have hf := (KLR.KLRAlgebra.top_polynomial_pair_eq_zero_iff_of_words
    (stendhalQ_symm Q Λ hQ)
    hl₁ hr₁ hneq' bot f g).mp sum
  rw [← ofKLR_toKLR (hQ := hQ) z, hfg, hf.1, hf.2]
  simp only [map_zero, zero_mul, add_zero]


private theorem rightTop_cancel (hQ : KLRSymm Q) (upper : Seq μ₀) (ht : FiveSlotRightTop upper)
    (z : B) (hz : E₀ upper * z * E₀ v₂=z) (zero : z*leg [1,2,3] bot=0) : z=0 := by
  have reduced (l : List ℕ) (h : ValidWord n₀ l)
      (hlen : l.length=invCount n₀ (wordProd n₀ l)) : IsReduced n₀ l :=
    ⟨h,by rw [length_eq_invCount]; exact hlen⟩
  rcases ht with rfl|rfl|rfl
  · exact eq_zero_of_rightWord_in_twoRowCorner Q Λ hQ bot v₂ [1,2,3] 3
      (by decide) (@twoBlack_right_extreme_words_reduced n₀ 1 (by decide)).1
      (@twoBlack_right_extreme_words_reduced n₀ 1 (by decide)).2 (by decide)
      (twoBlack_extreme_stabilizer_of_card_two v₂ 2 (by decide) (by decide) () rfl rfl) z hz zero
  · refine terminal_cancel_words Q Λ hQ v₂ (sadj n₀ 2 • v₂) [1,2,3] (by decide) [2] [2,3] ?_ ?_ (by decide)
      (by decide +kernel) ?_ ?_ (by decide) z hz zero
    all_goals apply reduced <;> first | decide | simp [ValidWord,stendhalWeight]
  · refine terminal_cancel_words Q Λ hQ v₂ (sadj n₀ 3 • (sadj n₀ 2 • v₂)) [1,2,3] (by decide) [3,2] [3,2,3] ?_ ?_ (by decide)
      (by decide +kernel) ?_ ?_ (by decide) z hz zero
    all_goals apply reduced <;> first | decide | simp [ValidWord,stendhalWeight]

/-- In the five-slot example with a red spectator and two equal black strands,
all affine four-exit relations at each of the three right tops are generated by
the three neighboring joints in the descent cascade. -/
theorem exists_fiveSlotRightTop_fourExitJointPresentation (hQ : KLRSymm Q)
    (upper : Seq μ₀) (ht : FiveSlotRightTop upper)
    (x₀ x₁ x₂ x₃ : B)
    (h₀ : E₀ upper*x₀*E₀ v₀=x₀) (h₁ : E₀ upper*x₁*E₀ v₁=x₁)
    (h₂ : E₀ upper*x₂*E₀ v₂=x₂) (h₃ : E₀ upper*x₃*E₀ v₃=x₃)
    (rel : x₀*leg [3,2,1] bot+x₁*leg [2,3,1] bot+
      x₂*leg [1,2,3] bot+x₃*leg [2,3,1,2] bot=0) :
    ∃ u v w : B, E₀ upper*u*E₀ jA=u ∧ E₀ upper*v*E₀ jB=v ∧ E₀ upper*w*E₀ jD=w ∧
      x₀=u*leg [2] v₀ ∧ x₁=v*leg [1] v₁-u*leg [3] v₁ ∧
      x₂=w*leg [2,3] v₂-v*leg [2] v₂ ∧ x₃=-(w*leg [1] v₃) := by
  have near := twoBlackNearbyExitWords (Q := stendhalQ Q Λ) 1 (by decide) bot
    (by decide)
  have reversed := twoBlackReversedMiddleExitWords (Q₀ := stendhalQ Q Λ) 1 (by decide) bot
    (a := 1) (b := 2) (i := ()) (j := ()) rfl rfl rfl rfl (by decide)
  have legA : leg [2] v₀*leg [3,2,1] bot=leg [3] v₁*leg [2,3,1] bot := by
    rw [compose_leg Q Λ _ _ _ (by decide),compose_leg Q Λ _ _ _ (by decide)]
    exact congrArg F near.1
  have legB : leg [1] v₁*leg [2,3,1] bot=leg [2] v₂*leg [1,2,3] bot := by
    rw [compose_leg Q Λ _ _ _ (by decide),compose_leg Q Λ _ _ _ (by decide)]
    exact congrArg F near.2
  have legD : leg [2,3] v₂*leg [1,2,3] bot=leg [1] v₃*leg [2,3,1,2] bot := by
    rw [compose_leg Q Λ _ _ _ (by decide),compose_leg Q Λ _ _ _ (by decide)]
    exact congrArg F reversed.2
  have cut (l : List ℕ) (v : Seq μ₀) : leg l v*E₀ v=leg l v := by
    simp only [← map_mul,mul_assoc,e_mul_self]
  have single (j : ℕ) (v : Seq μ₀) : leg [j] v=F (ψ j*e v) := by
    simp only [ψw_cons,ψw_nil,mul_one]
  refine @exists_rectangular_jointCascade B _ (E₀ upper) _ _ _ _ _ _ _ (by rw [← map_mul,e_mul_self])
    _ _ _ _ _ _ _ _ _ _ legA legB legD (cut _ _) (cut _ _) (cut _ _) ?_ ?_ ?_ ?_
    x₀ x₁ x₂ x₃ h₀ h₁ h₂ h₃ rel
  · intro x hx
    rw [single]
    exact exists_supported_descent_factor Q Λ hQ v₀ upper 2 (by decide)
      (rightTop_pair_descent upper ht v₀ 2 (by decide) rfl rfl) x hx
  · intro x hx
    rw [single]
    exact exists_supported_descent_factor Q Λ hQ v₁ upper 1 (by decide)
      (rightTop_pair_descent upper ht v₁ 1 (by decide) rfl rfl) x hx
  · intro x hx
    rw [single]
    exact exists_supported_descent_factor Q Λ hQ v₃ upper 1 (by decide)
      (rightTop_pair_descent upper ht v₃ 1 (by decide) rfl rfl) x hx
  · exact rightTop_cancel Q Λ hQ upper ht

/-- In the five-slot example with a red spectator and two equal black strands,
all affine four-exit relations at the fixed right-extreme top are generated by
the three neighboring joints in the descent cascade. -/
theorem exists_fixedTop_fourExitJointPresentation_prefixOne (hQ : KLRSymm Q)
    (x₀ x₁ x₂ x₃ : B)
    (h₀ : E₀ v₂*x₀*E₀ v₀=x₀) (h₁ : E₀ v₂*x₁*E₀ v₁=x₁)
    (h₂ : E₀ v₂*x₂*E₀ v₂=x₂) (h₃ : E₀ v₂*x₃*E₀ v₃=x₃)
    (rel : x₀*leg [3,2,1] bot+x₁*leg [2,3,1] bot+
      x₂*leg [1,2,3] bot+x₃*leg [2,3,1,2] bot=0) :
    ∃ u v w : B, E₀ v₂*u*E₀ jA=u ∧ E₀ v₂*v*E₀ jB=v ∧ E₀ v₂*w*E₀ jD=w ∧
      x₀=u*leg [2] v₀ ∧ x₁=v*leg [1] v₁-u*leg [3] v₁ ∧
      x₂=w*leg [2,3] v₂-v*leg [2] v₂ ∧ x₃=-(w*leg [1] v₃) := by
  exact exists_fiveSlotRightTop_fourExitJointPresentation Q Λ hQ v₂ (Or.inl rfl) x₀ x₁ x₂ x₃ h₀ h₁ h₂ h₃ rel

/-- In the five-slot example with a red spectator and two equal black strands,
all affine four-exit relations at the mixed top are generated by
the three neighboring joints in the descent cascade. -/
theorem exists_mixedTop_fourExitJointPresentation_prefixOne (hQ : KLRSymm Q)
    (x₀ x₁ x₂ x₃ : B)
    (h₀ : E₀ mixed*x₀*E₀ v₀=x₀) (h₁ : E₀ mixed*x₁*E₀ v₁=x₁)
    (h₂ : E₀ mixed*x₂*E₀ v₂=x₂) (h₃ : E₀ mixed*x₃*E₀ v₃=x₃)
    (rel : x₀*leg [3,2,1] bot+x₁*leg [2,3,1] bot+
      x₂*leg [1,2,3] bot+x₃*leg [2,3,1,2] bot=0) :
    ∃ u v w : B, E₀ mixed*u*E₀ jA=u ∧ E₀ mixed*v*E₀ jB=v ∧ E₀ mixed*w*E₀ jD=w ∧
      x₀=u*leg [2] v₀ ∧ x₁=v*leg [1] v₁-u*leg [3] v₁ ∧
      x₂=w*leg [2,3] v₂-v*leg [2] v₂ ∧ x₃=-(w*leg [1] v₃) := by
  exact exists_fiveSlotRightTop_fourExitJointPresentation Q Λ hQ mixed (Or.inr (Or.inl (by decide))) x₀ x₁ x₂ x₃ h₀ h₁ h₂ h₃ rel

/-- The left extreme, nearby joint, and full joint in the five-slot example.
The last red strand lies after both equal black strands. -/
def FiveSlotLeftTop (upper : Seq μ₀) : Prop :=
  upper=v₀ ∨ upper=sadj n₀ 2 • v₀ ∨ upper=sadj n₀ 1 • (sadj n₀ 2 • v₀)

private theorem leftTop_pair_descent (upper : Seq μ₀) (ht : FiveSlotLeftTop upper)
    (v : Seq μ₀) (j : ℕ) (hj : j+1<n₀)
    (hl : v.lbl ⟨j,by omega⟩ = .inr 2) (hr : v.lbl ⟨j+1,hj⟩ = .inl ())
    (w : Perm (Fin n₀)) (hw : w • v=upper) : w ⟨j+1,hj⟩ < w ⟨j,by omega⟩ := by
  have read (f : Fin n₀) : upper.lbl (w f)=v.lbl f := by
    rw [← hw,lbl_smul,show w⁻¹ (w f)=f from w.symm_apply_apply f]
  have red : upper.lbl ⟨4,by decide⟩ = .inr 2 := by
    rcases ht with rfl|rfl|rfl <;> decide
  have fix : w ⟨j,by omega⟩=⟨4,by decide⟩ := lbl_inj_of_inr upper 2 ((read _).trans hl) red
  rw [fix]
  have before (q : Fin n₀) (hq : upper.lbl q=.inl ()) : q < (⟨4,by decide⟩ : Fin n₀) := by
    rcases ht with rfl|rfl|rfl <;> fin_cases q <;> first | decide | contradiction
  exact before _ ((read _).trans hr)

private theorem leftTop_cancel (hQ : KLRSymm Q) (upper : Seq μ₀) (ht : FiveSlotLeftTop upper)
    (z : B) (hz : E₀ upper*z*E₀ v₀=z) (zero : z*leg [3,2,1] bot=0) : z=0 := by
  have reduced (l : List ℕ) (h : ValidWord n₀ l)
      (hlen : l.length=invCount n₀ (wordProd n₀ l)) : IsReduced n₀ l :=
    ⟨h,by rw [length_eq_invCount]; exact hlen⟩
  rcases ht with rfl|rfl|rfl
  · refine terminal_cancel_words Q Λ hQ v₀ v₀ [3,2,1] (by decide) [] [1] ?_ ?_ (by decide)
      (by decide +kernel) ?_ ?_ (by decide) z hz zero
    all_goals apply reduced <;> first | decide | simp [ValidWord,stendhalWeight]
  · refine terminal_cancel_words Q Λ hQ v₀ (sadj n₀ 2 • v₀) [3,2,1] (by decide) [2] [2,1] ?_ ?_ (by decide)
      (by decide +kernel) ?_ ?_ (by decide) z hz zero
    all_goals apply reduced <;> first | decide | simp [ValidWord,stendhalWeight]
  · refine terminal_cancel_words Q Λ hQ v₀ (sadj n₀ 1 • (sadj n₀ 2 • v₀)) [3,2,1] (by decide) [1,2] [1,2,1] ?_ ?_ (by decide)
      (by decide +kernel) ?_ ?_ (by decide) z hz zero
    all_goals apply reduced <;> first | decide | simp [ValidWord,stendhalWeight]

/-- With the last red after both blacks, all supported affine exit relations
are generated by the three neighboring joints reached by moving that red
to the right. The remaining coefficient is detected on the left extreme
exit. Webster, §6.1, proof of Lemma 6.8 after (6.21). -/
theorem exists_fiveSlotLeftTop_fourExitJointPresentation (hQ : KLRSymm Q)
    (upper : Seq μ₀) (ht : FiveSlotLeftTop upper) (x₀ x₁ x₂ x₃ : B)
    (h₀ : E₀ upper*x₀*E₀ v₀=x₀) (h₁ : E₀ upper*x₁*E₀ v₁=x₁)
    (h₂ : E₀ upper*x₂*E₀ v₂=x₂) (h₃ : E₀ upper*x₃*E₀ v₃=x₃)
    (rel : x₀*leg [3,2,1] bot+x₁*leg [2,3,1] bot+
      x₂*leg [1,2,3] bot+x₃*leg [2,3,1,2] bot=0) :
    ∃ u v w : B, E₀ upper*u*E₀ jB=u ∧ E₀ upper*v*E₀ jA=v ∧ E₀ upper*w*E₀ jA=w ∧
      x₂=u*leg [2] v₂ ∧ x₁=v*leg [3] v₁-u*leg [1] v₁ ∧
      x₀=w*leg [2,1] v₀-v*leg [2] v₀ ∧ x₃=-(w*leg [3] v₃) := by
  have near := twoBlackNearbyExitWords (Q := stendhalQ Q Λ) 1 (by decide) bot (by decide)
  have reversed := twoBlackReversedMiddleExitWords (Q₀ := stendhalQ Q Λ) 1 (by decide) bot
    (a := 1) (b := 2) (i := ()) (j := ()) rfl rfl rfl rfl (by decide)
  have legA : leg [2] v₀*leg [3,2,1] bot=leg [3] v₁*leg [2,3,1] bot := by
    rw [compose_leg Q Λ _ _ _ (by decide),compose_leg Q Λ _ _ _ (by decide)]
    exact congrArg F near.1
  have legB : leg [1] v₁*leg [2,3,1] bot=leg [2] v₂*leg [1,2,3] bot := by
    rw [compose_leg Q Λ _ _ _ (by decide),compose_leg Q Λ _ _ _ (by decide)]
    exact congrArg F near.2
  have legC : leg [2,1] v₀*leg [3,2,1] bot=leg [3] v₃*leg [2,3,1,2] bot := by
    rw [compose_leg Q Λ _ _ _ (by decide),compose_leg Q Λ _ _ _ (by decide)]
    exact congrArg F reversed.1
  have cut (l : List ℕ) (v : Seq μ₀) : leg l v*E₀ v=leg l v := by
    simp only [← map_mul,mul_assoc,e_mul_self]
  have single (j : ℕ) (v : Seq μ₀) : leg [j] v=F (ψ j*e v) := by
    simp only [ψw_cons,ψw_nil,mul_one]
  refine @exists_rectangular_jointCascade B _ (E₀ upper) _ _ _ _ _ _ _ (by rw [← map_mul,e_mul_self])
    _ _ _ _ _ _ _ _ _ _ legB.symm legA.symm legC (cut _ _) (cut _ _) (cut _ _) ?_ ?_ ?_ ?_
    x₂ x₁ x₀ x₃ h₂ h₁ h₀ h₃ (by rw [← rel]; abel)
  · intro x hx
    rw [single]
    exact (show sadj n₀ 2 • v₂ = jB by decide) ▸ exists_supported_descent_factor Q Λ hQ v₂ upper 2 (by decide)
      (leftTop_pair_descent upper ht v₂ 2 (by decide) rfl rfl) x hx
  · intro x hx
    rw [single]
    exact (show sadj n₀ 3 • v₁ = jA by decide) ▸ exists_supported_descent_factor Q Λ hQ v₁ upper 3 (by decide)
      (leftTop_pair_descent upper ht v₁ 3 (by decide) rfl rfl) x hx
  · intro x hx
    rw [single]
    exact (show sadj n₀ 3 • v₃ = jA by decide) ▸ exists_supported_descent_factor Q Λ hQ v₃ upper 3 (by decide)
      (leftTop_pair_descent upper ht v₃ 3 (by decide) rfl rfl) x hx
  · exact leftTop_cancel Q Λ hQ upper ht

end FixedTop
end Categorification.Stendhal.BraidedStendhalAlgebra
