/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.EqualBlackReturnKernel

/-!
# The equal-black exit kernel with mixed joint on top

For Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21),
consider the arms starting at the right extreme `r,i,i` and ending at
`i,r,i`. At this mixed fixed top, the four polynomial columns have two
equations and their kernel comes from the full joint `i,i,r`.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open TypeA Equiv MvPolynomial
variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
    {ν : Multiset I}
local notation "m" => Multiset.card ν
local notation "R" => KLRAlgebra k Q ν
local notation "P" => MvPolynomial (Fin m) k

private theorem mixed_leg_top (s : Seq ν) (w : List ℕ) :
    (e (wordProd m w • s) * (ψw w * e s) : R) = ψw w * e s := by
  rw [← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]

/-- Values at the extreme of the plain and black-crossed words from the
mixed joint to the full joint. The common braid appears in two columns. -/
theorem fullJoint_return_columns (s : Seq ν) (b : ℕ) (hp : b + 2 < m)
    (he : s.lbl ⟨b+1,by omega⟩=s.lbl ⟨b+2,hp⟩)
    (hn : s.lbl ⟨b,by omega⟩ ≠ s.lbl ⟨b+2,hp⟩) :
    let j := b+1
    let t := sadj m b • s
    let D : R := ψw [j]*e t
    let B : R := ψw [b,j]*e t
    let d : R := ψw [b]*e s
    let d' : R := ψw [b,j]*e s
    D*d=ψw [j,b]*e s ∧ B*d=ψw [j,b,j]*e s ∧ D*d'=ψw [j,b,j]*e s ∧ B*d'=0 := by
  intro j t D B d d'
  have sj : sadj m j • s=s := sadj_smul_eq_self hp he
  have td : (e t : R)*d=d := by
    simpa only [d,t,wordProd_singleton] using mixed_leg_top (Q := Q) s [b]
  have td' : (e t : R)*d'=d' := by
    simpa only [d',t,wordProd_cons,wordProd_nil,mul_one,mul_smul,sj] using mixed_leg_top (Q := Q) s [b,j]
  have braid' := braid (Q := Q) b hp s
  rw [ite_eq_right (fun h => hn h.1),sub_mul,sub_eq_zero] at braid'
  have cross : (ψ b : R)*(ψ j*d)=ψ j*d' := by
    simpa only [d,d',ψw_cons,ψw_nil,mul_one,mul_assoc,j] using braid'
  have right : (e s : R)*(ψ j*e s)=ψ j*e s := by
    simpa only [wordProd_singleton,sj,ψw_cons,ψw_nil,mul_one] using mixed_leg_top (Q := Q) s [j]
  have nil : (ψ j : R)*(ψ j*e s)=0 := by
    have equal : s.lbl ⟨j,by omega⟩ = s.lbl ⟨j+1,hp⟩ := he
    have H := exit_square_word (Q := Q) s [] j hp
    simpa only [wordProd_nil,one_smul,exitSquarePolynomial,ite_eq_left equal,map_zero,zero_mul,
      ψw_cons,ψw_nil,mul_one,mul_assoc] using H
  have vanish : (ψ b : R)*(ψ j*d')=0 := by
    have H := congrArg (· * (ψ j*e s)) cross
    simpa only [d,d',ψw_cons,ψw_nil,mul_one,mul_assoc,right,nil,mul_zero] using H
  have first : D*d=ψw [j,b]*e s := by
    simp only [D,ψw_cons,ψw_nil,mul_one,mul_assoc,td]
    simp only [d,ψw_cons,ψw_nil,mul_one]
  have last : D*d'=ψw [j,b,j]*e s := by
    simp only [D,ψw_cons,ψw_nil,mul_one,mul_assoc,td']
    simp only [d',ψw_cons,ψw_nil,mul_one,mul_assoc]
  refine ⟨first,?_,last,?_⟩
  · rw [← last]
    simp only [B,D,ψw_cons,ψw_nil,mul_one,mul_assoc,td,td',cross]
  · simp only [B,ψw_cons,ψw_nil,mul_one,mul_assoc,td',vanish]

/-- At the mixed joint, the third-length upper word on the plain arm
returns as the square polynomial times the crossed arm. On the crossed arm
the same upper word vanishes. -/
theorem mixedJoint_return_columns (s : Seq ν) (b : ℕ) (hp : b + 2 < m)
    (he : s.lbl ⟨b + 1, by omega⟩ = s.lbl ⟨b + 2,hp⟩)
    (hn : s.lbl ⟨b, by omega⟩ ≠ s.lbl ⟨b + 2,hp⟩) :
    let j := b + 1
    let t := sadj m b • s
    let q := exitSquarePolynomial Q t j hp
    let U : R := ψw [j,b,j] * e t
    let d : R := ψw [b] * e s
    let d' : R := ψw [b,j] * e s
    U*d=pol q*d' ∧ U*d'=0 := by
  intro j t q U d d'
  have sj : sadj m j • s = s := sadj_smul_eq_self hp he
  have td' : (e t : R)*d'=d' := by
    simpa only [d',wordProd_cons,wordProd_nil,mul_one,mul_smul,sj,t] using mixed_leg_top (Q := Q) s [b,j]
  let B : R := ψw [b,j]*e t
  let D : R := ψw [j]*e t
  obtain ⟨_,cB,cD,cZero⟩ := fullJoint_return_columns (Q := Q) s b hp he hn
  change B*d=_ at cB
  change D*d'=_ at cD
  change B*d'=0 at cZero
  have same : B*d=D*d' := cB.trans cD.symm
  have u : U=(ψ j : R)*B := by simp only [U,B,ψw_cons,ψw_nil,mul_one,mul_assoc]
  have square : (ψ j : R)*(ψ j*d')=pol q*d' := by
    have H := exit_square_word (Q := Q) s [b,j] j hp
    simpa only [wordProd_cons,wordProd_nil,mul_one,mul_smul,sj,ψw_cons,ψw_nil,mul_assoc,d',q,t] using H
  constructor
  · rw [u,mul_assoc,same]
    simpa only [D,ψw_cons,ψw_nil,mul_one,mul_assoc,td'] using square
  · rw [u,mul_assoc,cZero,mul_zero]

/-- The exact two equations on the four PBW coefficients at the mixed joint.
The square polynomial can be arbitrary. -/
theorem mixedJoint_return_matrix_iff (hQ : KLRSymm Q) (s : Seq ν) (b : ℕ) (hp : b + 2 < m)
    (he : s.lbl ⟨b + 1, by omega⟩ = s.lbl ⟨b + 2,hp⟩)
    (hn : s.lbl ⟨b, by omega⟩ ≠ s.lbl ⟨b + 2,hp⟩)
    (h₁ : IsReduced m [b]) (h₂ : IsReduced m [b,b + 1])
    (f g h i : P) :
    let j := b + 1
    let t := sadj m b • s
    let q := exitSquarePolynomial Q t j hp
    let U : R := ψw [j,b,j]*e t
    let d : R := ψw [b]*e s
    let d' : R := ψw [b,j]*e s
    (pol f*e t+pol g*U)*d+(pol h*e t+pol i*U)*d'=0 ↔ f=0 ∧ g*q+h=0 := by
  intro j t q U d d'
  obtain ⟨hU,hU'⟩ := mixedJoint_return_columns (Q := Q) s b hp he hn
  change U*d=pol q*d' at hU
  change U*d'=0 at hU'
  have sj : sadj m j • s=s := sadj_smul_eq_self hp he
  have td : (e t : R)*d=d := by
    simpa only [d,t,wordProd_singleton] using mixed_leg_top (Q := Q) s [b]
  have td' : (e t : R)*d'=d' := by
    simpa only [d',t,wordProd_cons,wordProd_nil,mul_one,mul_smul,sj] using mixed_leg_top (Q := Q) s [b,j]
  have different : wordProd m [b] ≠ wordProd m [b,j] := by
    intro h
    have bad : [b].length = [b,j].length := h₁.2.trans ((congrArg (length m) h).trans h₂.2.symm)
    simp at bad
  rw [add_mul,add_mul,mul_assoc _ (e t),td,mul_assoc _ U,hU,mul_assoc _ (e t),td',
    mul_assoc _ U,hU',mul_zero,add_zero,add_assoc,← mul_assoc (pol g),← map_mul,← add_mul,← map_add]
  exact top_polynomial_pair_eq_zero_iff_of_words hQ h₁ h₂ different s f (g*q+h)

/-- Both tails end at the full joint. Its black crossing takes the plain
tail to the crossed tail and kills the crossed tail. -/
theorem fullJoint_black_tails (s : Seq ν) (b : ℕ) (hp : b + 2 < m)
    (he : s.lbl ⟨b+1,by omega⟩=s.lbl ⟨b+2,hp⟩) :
    let j := b+1
    let t := sadj m b • s
    let F := sadj m j • t
    let D : R := ψw [j]*e t
    let B : R := ψw [b,j]*e t
    e F*D=D ∧ e F*B=B ∧ ψ b*B=0 ∧ ψ b*D=B := by
  intro j t F D B
  have hb : b + 1 < m := by omega
  have same : F.lbl ⟨b,by omega⟩ = F.lbl ⟨b + 1,hb⟩ := by
    change (sadj m j • (sadj m b • s)).1 _ = (sadj m j • (sadj m b • s)).1 _
    let L : Fin m := ⟨b,by omega⟩
    let H : Fin m := ⟨j,by omega⟩
    let Z : Fin m := ⟨j+1,hp⟩
    have jl : sadj m j L=L := sadj_apply_of_ne L (by dsimp [L,j]; omega) (by dsimp [L,j]; omega)
    have bz : sadj m b Z=Z := sadj_apply_of_ne Z (by dsimp [Z,j]; omega) (by dsimp [Z,j]; omega)
    have jh : sadj m j H=Z := sadj_apply_left hp
    have bl : sadj m b L=H := sadj_apply_left hb
    simp only [sadj_smul_apply]
    change s.1 (sadj m b (sadj m j L))=s.1 (sadj m b (sadj m j H))
    rw [jl,jh,bl,bz]
    exact he
  have fixF : sadj m b • F=F := sadj_smul_eq_self hb same
  have cutD : e F*D=D := by
    simpa only [D,F,wordProd_singleton] using mixed_leg_top (Q := Q) t [j]
  have cutB : e F*B=B := by
    have top : wordProd m [b,j] • t=F := by
      simpa only [wordProd_cons,wordProd_nil,mul_one,mul_smul] using fixF
    simpa only [B,top] using mixed_leg_top (Q := Q) t [b,j]
  have c₁B : (ψ b : R)*B=0 := by
    have sq := exit_square_word (Q := Q) t [j] b hb
    have ht : wordProd m [j] • t=F := by rw [wordProd_singleton]
    simpa only [B,ht,exitSquarePolynomial,ite_eq_left same,map_zero,zero_mul,
      ψw_cons,ψw_nil,mul_one,mul_assoc] using sq
  have c₁D : (ψ b : R)*D=B := by simp only [B,D,ψw_cons,ψw_nil,mul_one,mul_assoc]
  exact ⟨cutD,cutB,c₁B,c₁D⟩

/-- Every relation with this fixed mixed top has one common full-joint
coefficient when the two black-endpoint permutations exhaust the corner. -/
theorem exists_mixedJoint_corner_cycle_coefficient (hQ : KLRSymm Q) (s : Seq ν) (b : ℕ)
    (hp : b + 2 < m) (he : s.lbl ⟨b + 1,by omega⟩=s.lbl ⟨b + 2,hp⟩)
    (hn : s.lbl ⟨b,by omega⟩ ≠ s.lbl ⟨b + 2,hp⟩)
    (h₁ : IsReduced m [b]) (h₂ : IsReduced m [b,b + 1]) (h₃ : IsReduced m [b + 1,b,b + 1])
    (x y : R) :
    let j := b + 1
    let t := sadj m b • s
    (∀ w : Perm (Fin m), w • t=t ↔ w=1 ∨ w=wordProd m [j,b,j]) →
    e t*x=x → x*e t=x → e t*y=y → y*e t=y →
    x*(ψw [b]*e s)+y*(ψw [b,j]*e s)=0 →
    ∃ c : R, c*e (sadj m j • t)=c ∧ c*(ψw [b,j]*e t) = -x ∧ c*(ψw [j]*e t)=y := by
  intro j t matching hx hx' hy hy' rel
  let F := sadj m j • t
  let B : R := ψw [b,j]*e t
  let D : R := ψw [j]*e t
  let U : R := ψw [j,b,j]*e t
  let q := exitSquarePolynomial Q t j hp
  have nilRed : IsReduced m [] := by constructor <;> simp [ValidWord,wordProd_nil]
  have neq : wordProd m [] ≠ wordProd m [j,b,j] := by
    intro eq
    have bad : ([] : List ℕ).length=[j,b,j].length :=
      nilRed.2.trans ((congrArg (length m) eq).trans h₃.2.symm)
    simp at bad
  have coeff (z : R) (hz : e t*z=z) (hz' : z*e t=z) :
      ∃ f g : P, z=pol f*e t+pol g*U := by
    simpa only [ψw_nil,one_mul,U] using
      exists_two_corner_coefficients_of_words hQ t t [] [j,b,j] nilRed h₃ neq
        (by simpa only [wordProd_nil] using matching) z hz hz'
  obtain ⟨f,g,hxg⟩ := coeff x hx hx'
  obtain ⟨h,i,hyi⟩ := coeff y hy hy'
  rw [hxg,hyi] at rel
  obtain ⟨hf,hh⟩ := (mixedJoint_return_matrix_iff hQ s b hp he hn h₁ h₂ f g h i).1 rel
  change g*q+h=0 at hh
  have hneg : h = -(g*q) := by linear_combination hh
  obtain ⟨cutD,cutB,c₁B,c₁D⟩ := fullJoint_black_tails (Q := Q) s b hp he
  change e F*D=D at cutD
  change e F*B=B at cutB
  change ψ b*B=0 at c₁B
  change ψ b*D=B at c₁D
  have c₀B : (ψ j : R)*B=U := by simp only [B,U,ψw_cons,ψw_nil,mul_one,mul_assoc]
  have c₀D : (ψ j : R)*D=pol q*e t := by
    have sq := exit_square_word (Q := Q) t [] j hp
    simpa only [D,q,ψw_cons,ψw_nil,mul_one,one_mul,mul_assoc,wordProd_nil,one_smul] using sq
  let c : R := (-(pol g*ψ j)+pol i*(ψ j*ψ b))*e F
  refine ⟨c,?_,?_,?_⟩
  · change c*e F=c
    simp only [c,mul_assoc,e_mul_self]
  · change c*B = -x
    rw [hxg,hf,map_zero,zero_mul,zero_add]
    simp only [c,mul_assoc,cutB,add_mul,neg_mul,mul_assoc,c₀B,c₁B,mul_zero,add_zero]
  · change c*D=y
    rw [hyi,hneg,map_neg,map_mul]
    simp only [c,mul_assoc,cutD,add_mul,neg_mul,mul_assoc,c₀D,c₁D,c₀B]

end Categorification.KLR.KLRAlgebra
