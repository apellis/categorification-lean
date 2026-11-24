/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MixedJointKernel

/-!
# The equal-black exit kernel with full joint on top

At the top `i,i,r`, the two PBW rows of the right-pair relation have
coefficients `f` and `g+h`. This is the full-joint corner in the proof of
Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 after (6.21).
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open TypeA Equiv MvPolynomial
variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
    {ν : Multiset I}
local notation "m" => Multiset.card ν
local notation "R" => KLRAlgebra k Q ν
local notation "P" => MvPolynomial (Fin m) k

/-- Four polynomial columns at the full fixed top have row coefficients
`f` and `g+h`, over any commutative coefficient ring. -/
theorem fullJoint_return_matrix_iff (hQ : KLRSymm Q) (s : Seq ν) (b : ℕ) (hp : b + 2 < m)
    (he : s.lbl ⟨b+1,by omega⟩=s.lbl ⟨b+2,hp⟩)
    (hn : s.lbl ⟨b,by omega⟩ ≠ s.lbl ⟨b+2,hp⟩)
    (h₂ : IsReduced m [b+1,b]) (h₃ : IsReduced m [b+1,b,b+1]) (f g h i : P) :
    let j := b+1
    let t := sadj m b • s
    let D : R := ψw [j]*e t
    let B : R := ψw [b,j]*e t
    let d : R := ψw [b]*e s
    let d' : R := ψw [b,j]*e s
    (pol f*D+pol g*B)*d+(pol h*D+pol i*B)*d'=0 ↔ f=0 ∧ g+h=0 := by
  intro j t D B d d'
  obtain ⟨a,b',c,e'⟩ := fullJoint_return_columns (Q := Q) s b hp he hn
  change D*d=_ at a
  change B*d=_ at b'
  change D*d'=_ at c
  change B*d'=0 at e'
  have diff : wordProd m [j,b] ≠ wordProd m [j,b,j] := by
    intro h
    have bad : [j,b].length=[j,b,j].length := h₂.2.trans ((congrArg (length m) h).trans h₃.2.symm)
    simp at bad
  rw [add_mul,add_mul,mul_assoc _ D,mul_assoc _ B,mul_assoc _ D,mul_assoc _ B,
    a,b',c,e',mul_zero,add_zero,add_assoc,← add_mul,← map_add]
  exact top_polynomial_pair_eq_zero_iff_of_words hQ h₂ h₃ diff s f (g+h)

/-- The full-joint endomorphisms given by the identity and the black
crossing generate all relations at the full fixed top. -/
theorem exists_fullJoint_corner_cycle_coefficient (hQ : KLRSymm Q) (s : Seq ν) (b : ℕ)
    (hp : b + 2 < m) (he : s.lbl ⟨b+1,by omega⟩=s.lbl ⟨b+2,hp⟩)
    (hn : s.lbl ⟨b,by omega⟩ ≠ s.lbl ⟨b+2,hp⟩)
    (hD : IsReduced m [b+1]) (hB : IsReduced m [b,b+1])
    (h₂ : IsReduced m [b+1,b]) (h₃ : IsReduced m [b+1,b,b+1]) (x y : R) :
    let j := b+1
    let t := sadj m b • s
    let F := sadj m j • t
    (∀ w : Perm (Fin m), w • t=F ↔ w=wordProd m [j] ∨ w=wordProd m [b,j]) →
    e F*x=x → x*e t=x → e F*y=y → y*e t=y →
    x*(ψw [b]*e s)+y*(ψw [b,j]*e s)=0 →
    ∃ c : R, c*e F=c ∧ c*(ψw [b,j]*e t) = -x ∧ c*(ψw [j]*e t)=y := by
  intro j t F matching hx hx' hy hy' rel
  let D : R := ψw [j]*e t
  let B : R := ψw [b,j]*e t
  have diff := (exists_pbw_words_for_crossing hD b hB).1
  have coeff (z : R) (hz : e F*z=z) (hz' : z*e t=z) : ∃ f g : P, z=pol f*D+pol g*B :=
    exists_two_corner_coefficients_of_words hQ t F [j] [b,j] hD hB diff matching z hz hz'
  obtain ⟨f,g,hxg⟩ := coeff x hx hx'
  obtain ⟨h,i,hyi⟩ := coeff y hy hy'
  rw [hxg,hyi] at rel
  obtain ⟨hf,hh⟩ := (fullJoint_return_matrix_iff hQ s b hp he hn h₂ h₃ f g h i).1 rel
  have hneg : h = -g := by linear_combination hh
  obtain ⟨cutD,cutB,vanish,cross⟩ := fullJoint_black_tails (Q := Q) s b hp he
  change e F*D=D at cutD
  change e F*B=B at cutB
  change ψ b*B=0 at vanish
  change ψ b*D=B at cross
  let c : R := (-pol g+pol i*ψ b)*e F
  refine ⟨c,?_,?_,?_⟩
  · simp only [c,mul_assoc,e_mul_self]
  · change c*B= -x
    rw [hxg,hf,map_zero,zero_mul,zero_add]
    simp only [c,mul_assoc,cutB,add_mul,neg_mul,mul_assoc,vanish,mul_zero,add_zero]
  · change c*D=y
    rw [hyi,hneg,map_neg]
    simp only [c,mul_assoc,cutD,add_mul,mul_assoc,cross]

end Categorification.KLR.KLRAlgebra
