/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopIdeal

/-!
# Four-arm relations at the central five-slot top

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
At the top with a black strand on each side of the red pair, the two
middle exits share an upper loading. Their upper PBW words are the identity
and the transposition of the two black endpoints.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open Stendhal Stendhal.BraidedStendhalAlgebra TypeA Equiv MvPolynomial

variable {k : Type} [CommRing k]
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
variable {Q₀ : Unit ⊕ Fin 3 → Unit ⊕ Fin 3 → MvPolynomial (Fin 2) k}
local notation "R" => KLRAlgebra k Q₀ μ₀
local notation "P" => MvPolynomial (Fin N) k
private abbrev bot := fixedTopFourExitBottom
private abbrev v₀ := fixedTopFourExitCut 0
private abbrev t := fixedTopFourExitCut 1
private abbrev v₂ := fixedTopFourExitCut 2
private abbrev A₀ := sadj N 2 • v₀
private abbrev B₀ := sadj N 1 • t
private abbrev F₀ := sadj N 3 • B₀
private abbrev leg (w : List ℕ) (s : Seq μ₀) : R := ψw w*e s
local notation "L" => leg (Q₀ := Q₀)

private theorem left_cut (w : List ℕ) (s v : Seq μ₀) (hv : wordProd N w • s=v) : (e v : R)*L w s=L w s := by
  rw [← hv,leg,← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]

private theorem product (l w : List ℕ) (s v : Seq μ₀) (hv : wordProd N w • s=v) :
    L l v*L w s=L (l++w) s := by
  have H := left_cut (Q₀ := Q₀) w s v hv
  change (ψw l*e v)*L w s=L (l++w) s
  rw [mul_assoc,H,leg,leg,ψw_append,mul_assoc]

private theorem square (v : Seq μ₀) (j : ℕ) (hj : j+1<N) :
    L [j,j] v=pol (exitSquarePolynomial Q₀ v j hj)*e v := by
  simpa only [leg,wordProd_nil,one_smul,ψw_nil,one_mul] using exit_square_word (Q := Q₀) v [] j hj

/-- The plain and black-crossed full-joint returns give four entries at
the central top. The ordinary double return is the product of the two
far red/black square polynomials. -/
theorem fiveSlotCentral_fullJoint_entries :
    let c := L [1,3] F₀
    let c' := L [1,3,2] F₀
    let b := L [2,3,1] t
    let d := L [3,1] t
    let u := L [1,3,2,3,1] t
    let q := exitSquarePolynomial Q₀ t 1 (by decide)*exitSquarePolynomial Q₀ t 3 (by decide)
    c*b=u ∧ c*d=pol q*e t ∧ c'*b=0 ∧ c'*d=u := by
  intro c c' b d u q
  have shorten : c'=c*L [2] F₀ := by
    exact (product [1,3] [2] F₀ F₀ (by decide)).symm
  have db : L [2] F₀*d=b := product [2] [3,1] t F₀ (by decide)
  have nil : L [2] F₀*L [2] F₀=0 := by
    rw [product _ _ _ _ (by decide)]
    change L [2,2] F₀=0
    rw [square _ _ (by decide),exitSquarePolynomial,ite_eq_left (by decide),map_zero,zero_mul]
  have cb : c*b=u := product [1,3] [2,3,1] t F₀ (by decide)
  refine ⟨cb,?_,?_,?_⟩
  · have far : Commute (ψ 3 : R) (ψ 1) := (ψ_mul_ψ 1 3 (by decide)).symm
    have commute : c*d=L [1,1] t*L [3,3] t := by
      change L [1,3] F₀*L [3,1] t=_
      rw [product _ _ _ _ (by decide),product _ _ _ _ (by decide)]
      simp only [leg,List.cons_append,List.nil_append,ψw_cons,ψw_nil,mul_one,mul_assoc]
      rw [far.left_comm (e t),far.left_comm (ψ 3*e t)]
    rw [commute,square _ _ (by decide),mul_assoc,left_cut _ _ _ (by decide),square _ _ (by decide),
      ← mul_assoc,← map_mul]
  · rw [shorten,← db,mul_assoc,← mul_assoc (L [2] F₀),nil,zero_mul,mul_zero]
  · rw [shorten,mul_assoc,db,cb]

private abbrev l₀ : R := L [3,2,1] bot
private abbrev l₁ : R := L [2,3,1] bot
private abbrev l₂ : R := L [1,2,3] bot
private abbrev l₃ : R := L [2,3,1,2] bot
local notation "xL₀" => l₀ (Q₀ := Q₀)
local notation "xL₁" => l₁ (Q₀ := Q₀)
local notation "xL₂" => l₂ (Q₀ := Q₀)
local notation "xL₃" => l₃ (Q₀ := Q₀)

private theorem central_edges :
    L [2] v₀*xL₀=L [3] t*xL₁ ∧ L [1] t*xL₁=L [2] v₂*xL₂ ∧
    L [2,1] v₀*xL₀=L [3] t*xL₃ ∧ L [2,3] v₂*xL₂=L [1] t*xL₃ ∧
    L [2,3] B₀*L [2] v₂=L [3] B₀*L [2,3] v₂ := by
  have near := twoBlackNearbyExitWords (Q := Q₀) 1 (by decide) bot (by decide)
  have rev := twoBlackReversedMiddleExitWords (Q₀ := Q₀) 1 (by decide) bot
    (a := 1) (b := 2) (i := ()) (j := ()) rfl rfl rfl rfl (by decide)
  have cycle := twoBlackExitCycleWords (Q₀ := Q₀) 1 (by decide) bot
    (a := 1) (b := 2) (i := ()) (j := ()) rfl rfl rfl rfl
  simp only [l₀,l₁,l₂,l₃]
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals rw [product _ _ _ _ (by decide),product _ _ _ _ (by decide)]
  · exact near.1
  · exact near.2
  · exact rev.1
  · exact rev.2
  · have ec := cycle.2.2.1
    change (ψw [2,3,2]*e (wordProd N [1,2,3] • bot) : R)=ψw [3,2,3]*e (wordProd N [1,2,3] • bot) at ec
    rw [show wordProd N [1,2,3] • bot=v₂ by decide] at ec
    exact ec

private theorem reduced (l : List ℕ) (h : ValidWord N l)
    (hlen : l.length=invCount N (wordProd N l)) : TypeA.IsReduced N l :=
  ⟨h,by rw [length_eq_invCount]; exact hlen⟩

private theorem coeffs (hQ : KLRSymm Q₀) (s : Seq μ₀) (v : Seq μ₀) (l r : List ℕ)
    (hL : TypeA.IsReduced N l) (hR : TypeA.IsReduced N r)
    (ne : wordProd N l ≠ wordProd N r)
    (mat : ∀ w : Perm (Fin N), w • s=v ↔ w=wordProd N l ∨ w=wordProd N r)
    (x : R) (cut : e v*x*e s=x) : ∃ f g : P, x=pol f*L l s+pol g*L r s := by
  apply exists_two_corner_coefficients_of_words hQ s v l r hL hR ne mat x
  · have id := congrArg (e v * ·) cut
    change e v*(e v*x*e s)=e v*x at id
    rw [← mul_assoc (e v),← mul_assoc (e v),e_mul_self,cut] at id
    exact id.symm
  · have id := congrArg (· * e s) cut
    change e v*x*e s*e s=x*e s at id
    rw [mul_assoc _ (e s),e_mul_self,cut] at id
    exact id.symm

/-- The two middle arms at the central top have matrix rows `f` and
`g*q+h`, where `q` is the product of their two far red/black squares. -/
theorem fiveSlotCentral_middle_matrix_iff (hQ : KLRSymm Q₀) (f g h i : P) :
    let U := L [1,3,2,3,1] t
    let q := exitSquarePolynomial Q₀ t 1 (by decide)*exitSquarePolynomial Q₀ t 3 (by decide)
    (pol f*e t+pol g*U)*xL₁+(pol h*e t+pol i*U)*xL₃=0 ↔ f=0 ∧ g*q+h=0 := by
  intro U q
  let B : R := L [2,3,1] t
  let D : R := L [3,1] t
  let c : R := L [1,3] F₀
  let c' : R := L [1,3,2] F₀
  obtain ⟨cb,cd,c'b,c'd⟩ := fiveSlotCentral_fullJoint_entries (Q₀ := Q₀)
  change c*B=U at cb
  change c*D=pol q*e t at cd
  change c'*B=0 at c'b
  change c'*D=U at c'd
  obtain ⟨_,eB,_,eD,eBD⟩ := central_edges (Q₀ := Q₀)
  have Bsplit : B=L [2,3] B₀*L [1] t := (product [2,3] [1] t B₀ (by decide)).symm
  have Dsplit : D=L [3] B₀*L [1] t := (product [3] [1] t B₀ (by decide)).symm
  have together : B*xL₁=D*xL₃ := by
    calc
      _ = L [2,3] B₀*(L [1] t*xL₁) := by rw [Bsplit,mul_assoc]
      _ = (L [2,3] B₀*L [2] v₂)*xL₂ := by rw [eB]; exact (mul_assoc _ _ _).symm
      _ = L [3] B₀*(L [1] t*xL₃) := by rw [eBD,mul_assoc,eD]
      _ = _ := by rw [Dsplit]; exact (mul_assoc _ _ _).symm
  have cut₁ : (e t : R)*xL₁=xL₁ := left_cut _ _ _ (by decide)
  have cut₃ : (e t : R)*xL₃=xL₃ := left_cut _ _ _ (by decide)
  have u₁ : U*xL₁=pol q*xL₃ := by
    rw [← cb,mul_assoc,together,← mul_assoc,cd,mul_assoc,cut₃]
  have u₃ : U*xL₃=0 := by
    rw [← c'd,mul_assoc,← together,← mul_assoc,c'b,zero_mul]
  simp only [add_mul,mul_assoc (pol f) (e t) xL₁,mul_assoc (pol g) U xL₁,
    mul_assoc (pol h) (e t) xL₃,mul_assoc (pol i) U xL₃,cut₁,cut₃,u₁,u₃,mul_zero,add_zero]
  rw [add_assoc,← mul_assoc (pol g),← map_mul,← add_mul,← map_add]
  exact top_polynomial_pair_eq_zero_iff_of_words hQ
    (reduced [2,3,1] (by simp [ValidWord,stendhalWeight]) (by decide))
    (reduced [2,3,1,2] (by simp [ValidWord,stendhalWeight]) (by decide)) (by decide) bot f (g*q+h)

/-- Every relation between the two middle exits at their common fixed
top has one coefficient at the full joint. The two pure middle rows
are detected by distinct reduced words on the original bottom. -/
theorem fiveSlotCentral_middle_kernel (hQ : KLRSymm Q₀) (x y : R)
    (hx : e t*x*e t=x) (hy : e t*y*e t=y) (rel : x*xL₁+y*xL₃=0) :
    ∃ z : R, e t*z*e F₀=z ∧ z*L [2,3,1] t=x ∧ z*L [3,1] t= -y := by
  let U : R := L [1,3,2,3,1] t
  let B : R := L [2,3,1] t
  let D : R := L [3,1] t
  let c : R := L [1,3] F₀
  let c' : R := L [1,3,2] F₀
  let q := exitSquarePolynomial Q₀ t 1 (by decide)*exitSquarePolynomial Q₀ t 3 (by decide)
  obtain ⟨cb,cd,c'b,c'd⟩ := fiveSlotCentral_fullJoint_entries (Q₀ := Q₀)
  change c*B=U at cb
  change c*D=pol q*e t at cd
  change c'*B=0 at c'b
  change c'*D=U at c'd
  have head (v : R) (hv : e t*v*e t=v) : ∃ f g : P, v=pol f*e t+pol g*U := by
    simpa only [leg,ψw_nil,one_mul,U] using coeffs hQ t t [] [1,3,2,3,1]
      (reduced _ (by simp [ValidWord,stendhalWeight]) (by decide)) (reduced _ (by simp [ValidWord,stendhalWeight]) (by decide)) (by decide)
      (by decide +kernel) v hv
  obtain ⟨f,g,xform⟩ := head x hx
  obtain ⟨h,i,yform⟩ := head y hy
  rw [xform,yform] at rel
  obtain ⟨hf,hh⟩ := (fiveSlotCentral_middle_matrix_iff hQ f g h i).1 rel
  change g*q+h=0 at hh
  let w := pol g*c-pol i*c'
  have left (z : R) (hz : e t*z*e t=z) : e t*z=z := by
    have h := congrArg (e t * ·) hz
    change e t*(e t*z*e t)=e t*z at h
    rw [← mul_assoc (e t),← mul_assoc (e t),e_mul_self,hz] at h
    exact h.symm
  have cutB : (e F₀ : R)*B=B := left_cut _ _ _ (by decide)
  have cutD : (e F₀ : R)*D=D := left_cut _ _ _ (by decide)
  have ordinary : w*B=x := by
    dsimp only [w]
    rw [xform,hf,map_zero,zero_mul,zero_add,sub_mul,mul_assoc (pol g),mul_assoc (pol i),cb,c'b,mul_zero,sub_zero]
  have crossed : w*D= -y := by
    have hneg : h= -(g*q) := by linear_combination hh
    dsimp only [w]
    rw [yform,hneg,map_neg,neg_mul,sub_mul,mul_assoc (pol g),mul_assoc (pol i),cd,c'd,← mul_assoc (pol g),← map_mul]
    abel
  refine ⟨e t*w*e F₀,?_,?_,?_⟩
  · simp only [← mul_assoc,e_mul_self]
    rw [mul_assoc _ (e F₀),e_mul_self]
  · change e t*w*e F₀*B=x
    rw [mul_assoc _ (e F₀),cutB,mul_assoc,ordinary,left x hx]
  · change e t*w*e F₀*D= -y
    rw [mul_assoc _ (e F₀),cutD,mul_assoc,crossed,mul_neg,left y hy]

private theorem left_fixed {v s : Seq μ₀} {x : R} (hx : e v*x*e s=x) : e v*x=x := by
  have H := congrArg (e v * ·) hx
  change e v*(e v*x*e s)=e v*x at H
  rw [← mul_assoc (e v),← mul_assoc (e v),e_mul_self,hx] at H
  exact H.symm

private theorem word_cut (f : P) (l : List ℕ) (s v : Seq μ₀) (hv : wordProd N l • s=v) :
    (e v : R)*(pol f*L l s)*e s=pol f*L l s := by
  have H := e_mul_pol_ψw_e (Q := Q₀) f l s
  rw [hv] at H
  simp only [mul_assoc] at H
  rw [leg,H,mul_assoc,mul_assoc,e_mul_self]

private theorem cut_times_word (v : Seq μ₀) (w : R) (hw : e t*w=w) (l : List ℕ) :
    e t*(w*L l v)*e v=w*L l v := by
  rw [← mul_assoc (e t),hw]
  simp only [leg,mul_assoc,e_mul_self]

private theorem outer_arms (hQ : KLRSymm Q₀) (x y : R) (hx : e t*x*e v₀=x) (hy : e t*y*e v₂=y) :
    ∃ a b c d : R, e t*a*e A₀=a ∧ e t*b*e B₀=b ∧ e t*c*e A₀=c ∧ e t*d*e B₀=d ∧
      x=a*L [2] v₀+c*L [2,1] v₀ ∧ y=d*L [2,3] v₂-b*L [2] v₂ := by
  obtain ⟨f,g,xf⟩ := coeffs hQ v₀ t [3,2] [3,2,1]
    (reduced _ (by simp [ValidWord,stendhalWeight]) (by decide))
    (reduced _ (by simp [ValidWord,stendhalWeight]) (by decide)) (by decide) (by decide +kernel) x hx
  obtain ⟨h,i,yh⟩ := coeffs hQ v₂ t [1,2] [1,2,3]
    (reduced _ (by simp [ValidWord,stendhalWeight]) (by decide))
    (reduced _ (by simp [ValidWord,stendhalWeight]) (by decide)) (by decide) (by decide +kernel) y hy
  refine ⟨pol f*L [3] A₀,-(pol h*L [1] B₀),pol g*L [3] A₀,pol i*L [1] B₀,
    word_cut _ _ _ _ (by decide),?_,word_cut _ _ _ _ (by decide),word_cut _ _ _ _ (by decide),?_,?_⟩
  · simp only [mul_neg,neg_mul,word_cut _ _ _ _ (by decide : wordProd N [1] • B₀=t)]
  · rw [mul_assoc (pol f),mul_assoc (pol g),product [3] [2] v₀ A₀ (by decide),
      product [3] [2,1] v₀ A₀ (by decide)]
    exact xf
  · rw [neg_mul,sub_neg_eq_add,mul_assoc (pol i),mul_assoc (pol h),product [1] [2,3] v₂ B₀ (by decide),
      product [1] [2] v₂ B₀ (by decide)]
    exact yh.trans (add_comm _ _)

/-- At the central fixed top, all four neighboring joints generate the
affine exit relations. The two extreme arms are eliminated first, then the
residual pair at the central loading is corrected through the full joint. -/
theorem fiveSlotCentral_fourExitJointPresentation (hQ : KLRSymm Q₀)
    (x₀ x₁ x₂ x₃ : R) (h₀ : e t*x₀*e v₀=x₀) (h₁ : e t*x₁*e t=x₁)
    (h₂ : e t*x₂*e v₂=x₂) (h₃ : e t*x₃*e t=x₃)
    (rel : x₀*xL₀+x₁*xL₁+x₂*xL₂+x₃*xL₃=0) :
    ∃ a b c d : R, e t*a*e A₀=a ∧ e t*b*e B₀=b ∧ e t*c*e A₀=c ∧ e t*d*e B₀=d ∧
      x₀=a*L [2] v₀+c*L [2,1] v₀ ∧ x₁=b*L [1] t-a*L [3] t ∧
      x₂=d*L [2,3] v₂-b*L [2] v₂ ∧ x₃= -(c*L [3] t+d*L [1] t) := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hx,hy⟩ := outer_arms hQ x₀ x₂ h₀ h₂
  let u := x₁+a*L [3] t-b*L [1] t
  let v := x₃+c*L [3] t+d*L [1] t
  have cutA := cut_times_word t a (left_fixed ha) [3]
  have cutB := cut_times_word t b (left_fixed hb) [1]
  have cutC := cut_times_word t c (left_fixed hc) [3]
  have cutD := cut_times_word t d (left_fixed hd) [1]
  have uCut : e t*u*e t=u := by simp only [u,mul_add,mul_sub,add_mul,sub_mul,h₁,cutA,cutB]
  have vCut : e t*v*e t=v := by simp only [v,mul_add,add_mul,h₃,cutC,cutD]
  obtain ⟨eA,eB,eC,eD,cycle⟩ := central_edges (Q₀ := Q₀)
  have cancel : u*xL₁+v*xL₃=0 := by
    calc
      _ = x₀*xL₀+x₁*xL₁+x₂*xL₂+x₃*xL₃ := by
        rw [hx,hy]; simp only [u,v,add_mul,sub_mul,mul_assoc,eA,eB,eC,eD]; abel
      _ = 0 := rel
  obtain ⟨z,hz,zB,zD⟩ := fiveSlotCentral_middle_kernel hQ u v uCut vCut cancel
  have zLeft := left_fixed hz
  have splitB : L [2,3] B₀*L [1] t=L [2,3,1] t := product _ _ _ _ (by decide)
  have splitD : L [3] B₀*L [1] t=L [3,1] t := product _ _ _ _ (by decide)
  refine ⟨a,b+z*L [2,3] B₀,c,d+z*L [3] B₀,ha,?_,hc,?_,hx,?_,?_,?_⟩
  · simp only [mul_add,add_mul,hb,cut_times_word B₀ z zLeft]
  · simp only [mul_add,add_mul,hd,cut_times_word B₀ z zLeft]
  · rw [add_mul,mul_assoc z,splitB,zB]; dsimp only [u]; abel
  · rw [hy,add_mul,add_mul,mul_assoc z,mul_assoc z,cycle]; abel
  · rw [add_mul,mul_assoc z,splitD,zD]; dsimp only [v]; abel

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA

variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
local notation "B" => BraidedStendhalAlgebra k Q Λ ν₀
local notation "π" => ofKLR k Q Λ ν₀
local notation "T" => toKLR k Q Λ ν₀
local notation "E" => fun v : Seq μ₀ => π (e v)
local notation "C" => fun (w : List ℕ) (v : Seq μ₀) => π (ψw w*e v)
local notation "bot" => fixedTopFourExitBottom
local notation "v₀" => fixedTopFourExitCut 0
local notation "t₁" => fixedTopFourExitCut 1
local notation "v₂" => fixedTopFourExitCut 2
local notation "jA" => sadj N 2 • v₀
local notation "jB" => sadj N 1 • t₁

/-- In the braided Stendhal algebra every four-exit relation at the central
five-slot top is presented by the four neighboring joints with their prescribed
cuts. Webster, §6.1, Lemma 6.8 after (6.21), before the higher ideal. -/
theorem exists_fiveSlotCentral_fourExitJointPresentation (hQ : KLRSymm Q)
    (x₀ x₁ x₂ x₃ : B) (h₀ : E t₁*x₀*E v₀=x₀) (h₁ : E t₁*x₁*E t₁=x₁)
    (h₂ : E t₁*x₂*E v₂=x₂) (h₃ : E t₁*x₃*E t₁=x₃)
    (rel : x₀*C [3,2,1] bot+x₁*C [2,3,1] bot+x₂*C [1,2,3] bot+x₃*C [2,3,1,2] bot=0) :
    ∃ a b c d : B, E t₁*a*E jA=a ∧ E t₁*b*E jB=b ∧ E t₁*c*E jA=c ∧ E t₁*d*E jB=d ∧
      x₀=a*C [2] v₀+c*C [2,1] v₀ ∧ x₁=b*C [1] t₁-a*C [3] t₁ ∧
      x₂=d*C [2,3] v₂-b*C [2] v₂ ∧ x₃= -(c*C [3] t₁+d*C [1] t₁) := by
  have cut {s : Seq μ₀} {x : B} (h : E t₁*x*E s=x) : e t₁*T x*e s=T x := by
    simpa only [map_mul,toKLR_ofKLR_e] using congrArg T h
  have H := congrArg T rel
  simp only [map_add,map_mul,toKLR_ofKLR_ψw,toKLR_ofKLR_e,map_zero] at H
  obtain ⟨a,b,c,d,ha,hb,hc,hd,r₀,r₁,r₂,r₃⟩ := KLRAlgebra.fiveSlotCentral_fourExitJointPresentation
    (stendhalQ_symm Q Λ hQ) (T x₀) (T x₁) (T x₂) (T x₃) (cut h₀) (cut h₁) (cut h₂) (cut h₃) H
  refine ⟨π a,π b,π c,π d,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [map_mul] using congrArg π ha
  · simpa only [map_mul] using congrArg π hb
  · simpa only [map_mul] using congrArg π hc
  · simpa only [map_mul] using congrArg π hd
  · simpa only [map_add,map_mul,ofKLR_toKLR hQ] using congrArg π r₀
  · simpa only [map_sub,map_mul,ofKLR_toKLR hQ] using congrArg π r₁
  · simpa only [map_sub,map_mul,ofKLR_toKLR hQ] using congrArg π r₂
  · simpa only [map_neg,map_add,map_mul,ofKLR_toKLR hQ] using congrArg π r₃

/-- The four neighboring joints generate every unmarked affine relation
at every nonviolated upper loading of the exchanged red order in this
five-slot column. -/
theorem exists_fiveSlot_nonviolated_fourExitJointPresentation (hQ : KLRSymm Q)
    (upper : Seq μ₀) (order : redWord upper=redWord v₀) (nonviolated : ¬ IsViolated upper)
    (x₀ x₁ x₂ x₃ : B) (h₀ : E upper*x₀*E v₀=x₀) (h₁ : E upper*x₁*E t₁=x₁)
    (h₂ : E upper*x₂*E v₂=x₂) (h₃ : E upper*x₃*E t₁=x₃)
    (rel : x₀*C [3,2,1] bot+x₁*C [2,3,1] bot+x₂*C [1,2,3] bot+x₃*C [2,3,1,2] bot=0) :
    ∃ a b c d : B, E upper*a*E jA=a ∧ E upper*b*E jB=b ∧ E upper*c*E jA=c ∧ E upper*d*E jB=d ∧
      x₀=a*C [2] v₀+c*C [2,1] v₀ ∧ x₁=b*C [1] t₁-a*C [3] t₁ ∧
      x₂=d*C [2,3] v₂-b*C [2] v₂ ∧ x₃= -(c*C [3] t₁+d*C [1] t₁) := by
  have cases' : FiveSlotRightTop upper ∨ FiveSlotLeftTop upper ∨ upper=t₁ := by
    rcases fiveSlot_nonviolated_tops upper order nonviolated with h|rfl|rfl|rfl
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl rfl))
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl (Or.inr (Or.inl rfl)))
  have middle : fixedTopFourExitCut 3=t₁ := by decide
  rcases cases' with hr|hl|rfl
  · obtain ⟨a,b,d,ha,hb,hd,r₀,r₁,r₂,r₃⟩ := exists_fiveSlotRightTop_fourExitJointPresentation Q Λ hQ
      upper hr x₀ x₁ x₂ x₃ h₀ h₁ h₂ h₃ rel
    change x₃= -(d*C [1] (fixedTopFourExitCut 3)) at r₃
    rw [middle] at r₃
    refine ⟨a,b,0,d,ha,hb,by rw [mul_zero,zero_mul],hd,?_,r₁,r₂,?_⟩
    · simpa only [zero_mul,add_zero] using r₀
    · simpa only [zero_mul,zero_add] using r₃
  · obtain ⟨b,a,c,hb,ha,hc,r₂,r₁,r₀,r₃⟩ := exists_fiveSlotLeftTop_fourExitJointPresentation Q Λ hQ
      upper hl x₀ x₁ x₂ x₃ h₀ h₁ h₂ h₃ rel
    change x₃= -(c*C [3] (fixedTopFourExitCut 3)) at r₃
    rw [middle] at r₃
    refine ⟨-a,-b,c,0,?_,?_,hc,by rw [mul_zero,zero_mul],?_,?_,?_,?_⟩
    · simpa only [mul_neg,neg_mul] using congrArg Neg.neg ha
    · simpa only [mul_neg,neg_mul] using congrArg Neg.neg hb
    · rw [r₀,neg_mul]; abel
    · rw [r₁,neg_mul,neg_mul]; abel
    · simpa only [zero_mul,neg_mul,zero_sub,neg_neg] using r₂
    · simpa only [zero_mul,add_zero] using r₃
  · exact exists_fiveSlotCentral_fourExitJointPresentation Q Λ hQ _ _ _ _ h₀ h₁ h₂ h₃ rel

local notation "V" => ViolQuotient k Q Λ ν₀
local notation "mk" => violMk k Q Λ ν₀
local notation "Qe" => fun v : Seq μ₀ => mk (E v)
local notation "Qc" => fun (w : List ℕ) (v : Seq μ₀) => mk (C w v)

/-- The four-arm presentation also holds after killing global violations,
with the actual prescribed coefficients on all four arms. -/
theorem exists_fiveSlot_violQuotient_fourExitJointPresentation (hQ : KLRSymm Q)
    (upper : Seq μ₀) (order : redWord upper=redWord v₀) (x : Fin 4 → V)
    (support : ∀ i, Qe upper*x i*Qe (wordProd N (fiveSlotExitWord i) • bot)=x i)
    (rel : ∑ i, x i*Qc (fiveSlotExitWord i) bot=0) :
    ∃ a b c d : V, Qe upper*a*Qe jA=a ∧ Qe upper*b*Qe jB=b ∧ Qe upper*c*Qe jA=c ∧ Qe upper*d*Qe jB=d ∧
      x 0=a*Qc [2] v₀+c*Qc [2,1] v₀ ∧ x 1=b*Qc [1] t₁-a*Qc [3] t₁ ∧
      x 2=d*Qc [2,3] v₂-b*Qc [2] v₂ ∧ x 3= -(c*Qc [3] t₁+d*Qc [1] t₁) := by
  by_cases hv : IsViolated upper
  · have zzero (i : Fin 4) : x i=0 := by
      have H := support i
      have kill : Qe upper=0 := violMk_e hv
      rw [kill,zero_mul,zero_mul] at H
      exact H.symm
    refine ⟨0,0,0,0,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals simp only [zzero,mul_zero,zero_mul,zero_add,sub_zero,neg_zero]
  obtain ⟨y,cut,eval,sum⟩ := exists_fiveSlotExitRelation_affine_lift_at Q Λ hQ upper
    (order.trans (by decide)) x support rel
  have cut' (i : Fin 4) : E upper*y i*E (fixedTopFourExitCut i)=y i := by
    have ht : wordProd N (fiveSlotExitWord i) • bot=fixedTopFourExitCut i := by fin_cases i <;> decide
    simpa only [ht] using cut i
  have sum' : y 0*C [3,2,1] bot+y 1*C [2,3,1] bot+y 2*C [1,2,3] bot+y 3*C [2,3,1,2] bot=0 := by
    simpa only [Fin.sum_univ_four,fiveSlotExitWord,add_assoc] using sum
  obtain ⟨a,b,c,d,ha,hb,hc,hd,r₀,r₁,r₂,r₃⟩ := exists_fiveSlot_nonviolated_fourExitJointPresentation
    Q Λ hQ upper order hv (y 0) (y 1) (y 2) (y 3) (cut' 0) (cut' 1) (cut' 2) (cut' 3) sum'
  refine ⟨mk a,mk b,mk c,mk d,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [map_mul] using congrArg mk ha
  · simpa only [map_mul] using congrArg mk hb
  · simpa only [map_mul] using congrArg mk hc
  · simpa only [map_mul] using congrArg mk hd
  · simpa only [map_mul,map_add,eval] using congrArg mk r₀
  · simpa only [map_mul,map_sub,eval] using congrArg mk r₁
  · simpa only [map_mul,map_sub,eval] using congrArg mk r₂
  · simpa only [map_mul,map_add,map_neg,eval] using congrArg mk r₃

end Categorification.Stendhal.BraidedStendhalAlgebra
