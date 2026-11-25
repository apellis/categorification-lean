/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnBottomBlackAscents
import Categorification.WeightedKLR.RedStrands.BraidColumnBottomReconstruction
import Categorification.WeightedKLR.RedStrands.BraidColumnCorrection
import Categorification.WeightedKLR.RedStrands.BraidedStandardIso

/-!
# Generation by eligible bottom-block braid diagrams

Webster, arXiv:1309.3796v3, proof of Lemma 6.12, p. 66. A nonviolated
bottom can be reconstructed in red-led block coordinates. If all the
successive offsets ascend, the wiring is one of the selected indices.
Otherwise a right descent with black right slot gives a shorter cut.
Changing to the reduced expression through that cut contributes shorter
terms at the original loading pair. This proves generation of the actual
fixed-top column by induction on Coxeter length.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra
open scoped BigOperators
open MvPolynomial
variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "E" => fun κ => violMk k Q Λ ν (redProj k Q Λ ν κ)

/-- A right-stable submodule containing the eligible diagrams contains every
PBW diagram in the prescribed braid column. The induction is on Coxeter length. -/
theorem braidColumnBottomBlock_pbw_mem_of_index_predicate
    (s : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    (P : Perm (Fin m) → Prop)
    (hcutP : ∀ (w : Perm (Fin m)) (j : ℕ) (hj : j + 1 < m),
      w ⟨j+1,hj⟩ < w ⟨j,by omega⟩ →
      ((w⁻¹ • s).lbl ⟨j+1,hj⟩).isLeft → P w → P (w * sadj m j))
    (hsubP : ∀ w v : Perm (Fin m), v ∈ subProds m (ρ w) →
      length m v < length m w → v⁻¹ • s = w⁻¹ • s → P w → P v)
    (D : Submodule k V)
    (hmul : ∀ x ∈ D, ∀ z : V, z * E ((List.finRange ℓ).map σ) = z → x * z ∈ D)
    (hindex : ∀ (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m)
      (φ : Perm (Fin m)), ProjectiveBlockIndex s φ →
      (∀ r : Fin ℓ, (φ⁻¹ • s).lbl (braidBlockPositions n hn ⟨r,0⟩) = .inr r) →
      let w := braidColumnBottomBlockIndex n hn σ φ
      P w → F (ψw (ρ w) * e (w⁻¹ • s)) ∈ D)
    (w : Perm (Fin m)) (horder : redWord (w⁻¹ • s) = (List.finRange ℓ).map σ)
    (hP : P w) (p : MvPolynomial (Fin m) k) :
    F (ψw (ρ w) * pol p * e (w⁻¹ • s)) ∈ D := by
  let κ := (List.finRange ℓ).map σ
  have hright {b : Seq μ} (hb : redWord b = κ) (x : R) :
      F (x * e b) * E κ = F (x * e b) := by
    change violMk k Q Λ ν (ofKLR k Q Λ ν (x * e b)) * _ = _
    rw [← map_mul, map_mul (ofKLR k Q Λ ν), mul_assoc,
      e_mul_redProj, ite_eq_left hb]
    exact congrArg (violMk k Q Λ ν) ((map_mul (ofKLR k Q Λ ν) x (e b)).symm)
  induction hlen : length m w using Nat.strong_induction_on generalizing w p with
  | h d ih =>
    let b := w⁻¹ • s
    have hbOrder : redWord b = κ := horder
    by_cases hbv : IsViolated b
    · have hzero : F (e b : R) = 0 := violMk_e hbv
      change F (ψw (ρ w) * pol p * e b) ∈ D
      rw [map_mul F, hzero, mul_zero]
      exact zero_mem _
    obtain ⟨a,n,hn,ha,hred,hb⟩ := exists_braidBottomBlockReconstruction b σ hbOrder hbv
    have hw : w • (braidBlockPermutation n hn σ • a) = s := by rw [hb]; exact smul_inv_smul _ _
    by_cases hadj : ∀ (j : ℕ) (hj : j + 1 < m),
        ((braidBlockPermutation n hn σ • a).lbl ⟨j+1,hj⟩).isLeft →
        w ⟨j, by omega⟩ < w ⟨j+1,hj⟩
    · obtain ⟨φ,hφ,ha',hw'⟩ :=
        exists_projectiveIndex_of_bottomBlock_adjacent_ascents s a hs ha n hn σ hred w hw hadj
      have hgood := hindex n hn φ hφ (fun r => by rw [ha']; exact hred r)
      change P (braidColumnBottomBlockIndex n hn σ φ) →
        F (ψw (ρ (braidColumnBottomBlockIndex n hn σ φ)) * e
          ((braidColumnBottomBlockIndex n hn σ φ)⁻¹ • s)) ∈ D at hgood
      have hgood' := hgood (hw'.symm ▸ hP)
      rw [hw'] at hgood'
      have hm := hmul _ hgood' _ (hright hbOrder (pol p))
      have he : (ψw (ρ w) * e b) * (pol p * e b) = (ψw (ρ w) * pol p * e b : R) := by
        rw [mul_assoc (ψw (ρ w)), ← mul_assoc (e b), (e_commute_pol _ p).eq,
          mul_assoc (pol p), e_mul_self, ← mul_assoc]
      rwa [← map_mul F, he] at hm
    · push Not at hadj
      obtain ⟨j,hj,hblack,hnlt⟩ := hadj
      have hd : w ⟨j+1,hj⟩ < w ⟨j,by omega⟩ := by
        refine lt_of_le_of_ne hnlt ?_
        intro he
        have he' := w.injective he
        have he'' := congrArg Fin.val he'
        simp at he''
      let v := w * sadj m j
      let c := v⁻¹ • s
      have hc : c = sadj m j • b := by
        dsimp [c,v,b]
        rw [mul_inv_rev,sadj_inv,mul_smul]
      have hcOrder : redWord c = κ := by
        rw [hc, redWord_sadj_smul b hj, hbOrder]
        rw [hb] at hblack
        intro h
        cases he : b.lbl ⟨j+1,hj⟩ <;> simp_all
      have hshort := length_mul_sadj_of_gt hj hd
      have hvlen : length m v < d := by change length m (w * sadj m j) < d; omega
      have hcP : P v := hcutP w j hj hd (by simpa only [hb] using hblack) hP
      have hcut := ih _ hvlen v hcOrder hcP 1 rfl
      simp only [map_one,mul_one] at hcut
      have hh : (e c : R) * (ψ j * pol p * e b) = ψ j * pol p * e b := by
        have he' := e_mul_std (Q := Q) (Λ := Λ) [j] p b
        simpa only [wordProd_singleton, ← hc, ψw_cons,ψw_nil,mul_one] using he'
      have hbFact := hmul _ hcut _ (hright hbOrder (ψ j * pol p))
      have hfactor : F (ψw (ρ v ++ [j]) * pol p * e b) ∈ D := by
        have hf : (ψw (ρ v) * e c) * (ψ j * pol p * e b) =
            (ψw (ρ v ++ [j]) * pol p * e b : R) := by
          rw [mul_assoc (ψw (ρ v)),hh,ψw_append]
          simp only [ψw_cons,ψw_nil,mul_one,mul_assoc]
        rwa [← map_mul F,hf] at hbFact
      have hprod : wordProd m (ρ v ++ [j]) = w := by
        rw [wordProd_append,wordProd_singleton,(hρ v).2]
        change (w * sadj m j) * sadj m j = w
        rw [mul_assoc,TypeA.sadj_mul_self,mul_one]
      have hv' : IsReduced m (ρ v ++ [j]) := by
        refine ⟨validWord_append.2 ⟨(hρ v).1.1, validWord_cons.2 ⟨hj,validWord_nil m⟩⟩,?_⟩
        rw [List.length_append,List.length_singleton,(hρ v).1.2,(hρ v).2,hprod]
        exact hshort
      let f := braidColumnLoadingProjection (Q := Q) (Λ := Λ) s b
      have hp (u : List ℕ) (hu : wordProd m u = w) :
          f (ψw u * pol p * e b) = F (ψw u * pol p * e b) := by
        change F (e s * ((ψw u * pol p * e b) * e b)) = _
        rw [gen_mul_e,ite_eq_left rfl,e_mul_gen,hu,ite_eq_left rfl]
      have hraw := braidEquiv_sub_mem_lowSpan
        (Q := stendhalQ Q Λ)
        (braidEquiv_of_isReduced (hρ w).1 hv' ((hρ w).2.trans hprod.symm))
        (hρ w).1.1 p b
      have hm := Submodule.mem_map_of_mem (f := f) hraw
      rw [map_sub,hp _ (hρ w).2,hp _ hprod] at hm
      have hs' := braidColumnLoadingProjection_map_lowSpan_le_same_bottom (Q := Q) (Λ := Λ)
        s b ρ hρ (subProds m (ρ w)) ((ρ w).length - 2) hm
      have hdiff := (Submodule.span_le.mpr (show _ ⊆ (D : Set V) from by
        rintro _ ⟨u,z,hsu,hz,he,rfl⟩
        have hlen' : (ρ w).length = d := ((hρ w).1.2.trans (congrArg (length m) (hρ w).2)).trans hlen
        have hul : length m u < d := by omega
        have huOrder : redWord (u⁻¹ • s) = κ := he ▸ hbOrder
        have Hu : P u := hsubP w u hsu (by omega) he hP
        have H := ih _ hul u huOrder Hu (monomial z 1) rfl
        rwa [he] at H)) hs'
      have H := add_mem hdiff hfactor
      rw [sub_add_cancel] at H
      exact H

theorem braidColumnBottomBlock_pbw_mem_of_predicate
    (s : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    (P : Seq μ → Prop)
    (hcutP : ∀ (b : Seq μ) (j : ℕ) (hj : j + 1 < m),
      (b.lbl ⟨j+1,hj⟩).isLeft → P b → P (sadj m j • b))
    (D : Submodule k V)
    (hmul : ∀ x ∈ D, ∀ z : V, z * E ((List.finRange ℓ).map σ) = z → x * z ∈ D)
    (hindex : ∀ (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m)
      (φ : Perm (Fin m)), ProjectiveBlockIndex s φ →
      (∀ r : Fin ℓ, (φ⁻¹ • s).lbl (braidBlockPositions n hn ⟨r,0⟩) = .inr r) →
      let w := braidColumnBottomBlockIndex n hn σ φ
      P (w⁻¹ • s) → F (ψw (ρ w) * e (w⁻¹ • s)) ∈ D)
    (w : Perm (Fin m)) (horder : redWord (w⁻¹ • s) = (List.finRange ℓ).map σ)
    (hP : P (w⁻¹ • s)) (p : MvPolynomial (Fin m) k) :
    F (ψw (ρ w) * pol p * e (w⁻¹ • s)) ∈ D := by
  refine braidColumnBottomBlock_pbw_mem_of_index_predicate s hs σ ρ hρ
    (fun w => P (w⁻¹ • s)) ?_ ?_ D hmul hindex w horder hP p
  · intro v j hj _ hblack hv
    rw [mul_inv_rev,sadj_inv,mul_smul]
    exact hcutP (v⁻¹ • s) j hj hblack hv
  · intro v u _ _ hu hv
    rw [hu]
    exact hv

theorem braidColumnBottomBlock_pbw_mem
    (s : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    (D : Submodule k V)
    (hmul : ∀ x ∈ D, ∀ z : V, z * E ((List.finRange ℓ).map σ) = z → x * z ∈ D)
    (hindex : ∀ (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m)
      (φ : Perm (Fin m)), ProjectiveBlockIndex s φ →
      (∀ r : Fin ℓ, (φ⁻¹ • s).lbl (braidBlockPositions n hn ⟨r,0⟩) = .inr r) →
      let w := braidColumnBottomBlockIndex n hn σ φ
      F (ψw (ρ w) * e (w⁻¹ • s)) ∈ D)
    (w : Perm (Fin m)) (horder : redWord (w⁻¹ • s) = (List.finRange ℓ).map σ)
    (p : MvPolynomial (Fin m) k) :
    F (ψw (ρ w) * pol p * e (w⁻¹ • s)) ∈ D :=
  braidColumnBottomBlock_pbw_mem_of_predicate s hs σ ρ hρ (fun _ => True)
    (fun _ _ _ _ _ => trivial) D hmul
    (fun n hn φ hφ hred _ => hindex n hn φ hφ hred) w horder trivial p

end Categorification.Stendhal

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra
open scoped BigOperators

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "E" => fun κ => violMk k Q Λ ν (redProj k Q Λ ν κ)

/-- Products of the eligible v3 diagrams with right support at the source red projector. -/
def braidColumnBottomProductsAt (s : Seq μ) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (P : Perm (Fin m) → Prop) : Set V :=
  {x | ∃ (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m) (φ : Perm (Fin m)),
    ProjectiveBlockIndex s φ ∧
    (∀ r : Fin ℓ, (φ⁻¹ • s).lbl (braidBlockPositions n hn ⟨r,0⟩) = .inr r) ∧
    let w := braidColumnBottomBlockIndex n hn σ φ
    P w ∧ ∃ z : V, z * E ((List.finRange ℓ).map σ) = z ∧
    x = F (ψw (ρ w) * e (w⁻¹ • s)) * z}

/-- The restricted generator span is stable under right multiplication
by a right-supported coefficient. -/
theorem braidColumnBottomProductsAt_mul_mem_span
    (s : Seq μ) (σ : Perm (Fin ℓ)) (ρ : Perm (Fin m) → List ℕ) (P : Perm (Fin m) → Prop)
    {x z : V}
    (hx : x ∈ Submodule.span k (braidColumnBottomProductsAt (Q := Q) (Λ := Λ) s σ ρ P))
    (hz : z * E ((List.finRange ℓ).map σ) = z) :
    x * z ∈ Submodule.span k (braidColumnBottomProductsAt (Q := Q) (Λ := Λ) s σ ρ P) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,hn,φ,hφ,hred,hPy,y,hy,rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨n,hn,φ,hφ,hred,hPy,y * z,by rw [mul_assoc,hz],mul_assoc _ _ _⟩
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

/-- Eligible bottom-block products span every fixed-top PBW diagram with the
specified bottom red order. -/
theorem braidColumnBottomBlock_pbw_mem_span_at
    (s : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    (P : Perm (Fin m) → Prop)
    (hcutP : ∀ (w : Perm (Fin m)) (j : ℕ) (hj : j + 1 < m),
      w ⟨j+1,hj⟩ < w ⟨j,by omega⟩ →
      ((w⁻¹ • s).lbl ⟨j+1,hj⟩).isLeft → P w → P (w * sadj m j))
    (hsubP : ∀ w v : Perm (Fin m), v ∈ subProds m (ρ w) →
      length m v < length m w → v⁻¹ • s = w⁻¹ • s → P w → P v)
    (w : Perm (Fin m)) (horder : redWord (w⁻¹ • s) = (List.finRange ℓ).map σ)
    (hP : P w) (p : MvPolynomial (Fin m) k) :
    F (ψw (ρ w) * pol p * e (w⁻¹ • s)) ∈
      Submodule.span k (braidColumnBottomProductsAt (Q := Q) (Λ := Λ) s σ ρ P) := by
  refine braidColumnBottomBlock_pbw_mem_of_index_predicate s hs σ ρ hρ P hcutP hsubP _ ?_ ?_ w horder hP p
  · exact fun x hx z hz => braidColumnBottomProductsAt_mul_mem_span s σ ρ P hx hz
  · intro n hn φ hφ hr w hPw
    let b := w⁻¹ • s
    let κ := (List.finRange ℓ).map σ
    have horder : redWord b = κ := redWord_braidColumnBottomBlockIndex_bottom s n hn σ φ hr
    have he : (ofKLR k Q Λ ν) (KLRAlgebra.e b) * redProj k Q Λ ν κ =
        (ofKLR k Q Λ ν) (KLRAlgebra.e b) := by rw [e_mul_redProj,ite_eq_left horder]
    have hr' : F (e b : R) * E κ = F (e b : R) := by
      change (violMk k Q Λ ν) (ofKLR k Q Λ ν (e b)) * _ = _
      rw [← map_mul,he]
      rfl
    have he' : F (ψw (ρ w) * e b) = F (ψw (ρ w) * e b) * F (e b) := by
      rw [← map_mul F,mul_assoc (ψw (ρ w)),e_mul_self]
    exact Submodule.subset_span ⟨n,hn,φ,hφ,hr,hPw,F (e b),hr',he'⟩

def braidColumnBottomProductsWhere (s : Seq μ) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (P : Seq μ → Prop) : Set V :=
  braidColumnBottomProductsAt (Q := Q) (Λ := Λ) s σ ρ (fun w => P (w⁻¹ • s))

theorem braidColumnBottomProductsWhere_mul_mem_span
    (s : Seq μ) (σ : Perm (Fin ℓ)) (ρ : Perm (Fin m) → List ℕ) (P : Seq μ → Prop)
    {x z : V}
    (hx : x ∈ Submodule.span k (braidColumnBottomProductsWhere (Q := Q) (Λ := Λ) s σ ρ P))
    (hz : z * E ((List.finRange ℓ).map σ) = z) :
    x * z ∈ Submodule.span k (braidColumnBottomProductsWhere (Q := Q) (Λ := Λ) s σ ρ P) :=
  braidColumnBottomProductsAt_mul_mem_span s σ ρ (fun w => P (w⁻¹ • s)) hx hz

theorem braidColumnBottomBlock_pbw_mem_span_where
    (s : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    (P : Seq μ → Prop)
    (hcutP : ∀ (b : Seq μ) (j : ℕ) (hj : j + 1 < m),
      (b.lbl ⟨j+1,hj⟩).isLeft → P b → P (sadj m j • b))
    (w : Perm (Fin m)) (horder : redWord (w⁻¹ • s) = (List.finRange ℓ).map σ)
    (hP : P (w⁻¹ • s)) (p : MvPolynomial (Fin m) k) :
    F (ψw (ρ w) * pol p * e (w⁻¹ • s)) ∈
      Submodule.span k (braidColumnBottomProductsWhere (Q := Q) (Λ := Λ) s σ ρ P) := by
  refine braidColumnBottomBlock_pbw_mem_span_at s hs σ ρ hρ (fun w => P (w⁻¹ • s))
    ?_ ?_ w horder hP p
  · intro v j hj _ hblack hv
    rw [mul_inv_rev,sadj_inv,mul_smul]
    exact hcutP (v⁻¹ • s) j hj hblack hv
  · intro v u _ _ hu hv
    rw [hu]
    exact hv

/-- Products of all eligible diagrams in the fixed-top column. -/
def braidColumnBottomProducts (s : Seq μ) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) : Set V :=
  braidColumnBottomProductsWhere (Q := Q) (Λ := Λ) s σ ρ (fun _ => True)

theorem braidColumnBottomBlock_pbw_mem_span
    (s : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    (w : Perm (Fin m)) (horder : redWord (w⁻¹ • s) = (List.finRange ℓ).map σ)
    (p : MvPolynomial (Fin m) k) :
    F (ψw (ρ w) * pol p * e (w⁻¹ • s)) ∈
      Submodule.span k (braidColumnBottomProducts (Q := Q) (Λ := Λ) s σ ρ) :=
  braidColumnBottomBlock_pbw_mem_span_where s hs σ ρ hρ (fun _ => True)
    (fun _ _ _ _ _ => trivial) w horder trivial p

end Categorification.Stendhal

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra
open MvPolynomial
variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "E" => fun κ => violMk k Q Λ ν (redProj k Q Λ ν κ)

/-- The eligible bottom-block products span the actual fixed-top braid column. -/
theorem span_braidColumnBottomProducts
    (s : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ) :
    Submodule.span k (braidColumnBottomProducts (Q := Q) (Λ := Λ) s σ ρ) =
      violCorner k Q Λ ν s ((List.finRange ℓ).map σ) := by
  let κ := (List.finRange ℓ).map σ
  let π : V →ₗ[k] V := LinearMap.mulLeft k (F (e s)) ∘ₗ LinearMap.mulRight k (E κ)
  let f : R →ₗ[k] V := π.comp (AlgHom.toLinearMap F)
  have hπ : LinearMap.range π = violCorner k Q Λ ν s κ := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      obtain ⟨a,rfl⟩ := violMk_surjective x
      refine ⟨a, ?_⟩
      change (violMk k Q Λ ν) (ofKLR k Q Λ ν (e s) * (a * redProj k Q Λ ν κ)) =
        F (e s) * ((violMk k Q Λ ν) a * E κ)
      rw [map_mul,map_mul]
      rfl
    · rintro ⟨a,rfl⟩
      refine ⟨violMk k Q Λ ν a, ?_⟩
      change F (e s) * ((violMk k Q Λ ν) a * E κ) =
        (violMk k Q Λ ν) (ofKLR k Q Λ ν (e s) * (a * redProj k Q Λ ν κ))
      rw [map_mul,map_mul]
      rfl
  rw [← hπ]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨n,hn,φ,hφ,hred,_,z,hz,rfl⟩
    let w := braidColumnBottomBlockIndex n hn σ φ
    let b := w⁻¹ • s
    have he : (e s : R) * (ψw (ρ w) * e b) = ψw (ρ w) * e b := by
      have h := e_mul_std (Q := Q) (Λ := Λ) (ρ w) 1 b
      simpa only [(hρ w).2,b,smul_inv_smul,map_one,mul_one] using h
    refine ⟨F (ψw (ρ w) * e b) * z, ?_⟩
    change F (e s) * ((F (ψw (ρ w) * e b) * z) * E κ) = _
    rw [mul_assoc _ z, hz, ← mul_assoc, ← map_mul F, he]
  · rintro _ ⟨x,rfl⟩
    obtain ⟨y,rfl⟩ := (violMk_surjective.comp ofKLR_surjective : Function.Surjective F) x
    have hy : y ∈ Submodule.span k (Set.range (KLRAlgebra.stdElt (Q := stendhalQ Q Λ) (ν := μ) ρ)) := by
      rw [KLRAlgebra.span_stdElt ρ hρ]
      exact Submodule.mem_top
    have hm := Submodule.mem_map_of_mem (f := f) hy
    rw [Submodule.map_span] at hm
    refine (Submodule.span_le.mpr ?_) hm
    rintro _ ⟨_,⟨⟨b,w,a⟩,rfl⟩,rfl⟩
    let p := monomial a (1 : k)
    let y : R := ψw (ρ w) * pol p * e b
    change F (e s) * (F y * E κ) ∈ _
    have hright : F y * E κ = if redWord b = κ then F y else 0 := by
      change (violMk k Q Λ ν) (ofKLR k Q Λ ν y) *
        (violMk k Q Λ ν) (redProj k Q Λ ν κ) = _
      rw [← map_mul]
      have h := map_mul (ofKLR k Q Λ ν) (ψw (ρ w) * pol p) (e b)
      change ofKLR k Q Λ ν y = _ at h
      conv_lhs => rw [h,mul_assoc,e_mul_redProj]
      by_cases h' : redWord b = κ
      · simpa only [h', ↓reduceIte, ← h] using
          (show (violMk k Q Λ ν) (ofKLR k Q Λ ν y) = F y from rfl)
      · simp only [h', ↓reduceIte,mul_zero,map_zero]
    by_cases hb : redWord b = κ
    · rw [hright,ite_eq_left hb,← map_mul F]
      change F (e s * (ψw (ρ w) * pol p * e b)) ∈ _
      rw [e_mul_gen,(hρ w).2]
      by_cases hw : w⁻¹ • s = b
      · subst b
        rw [ite_eq_left rfl]
        exact braidColumnBottomBlock_pbw_mem_span s hs σ ρ hρ w hb p
      · rw [ite_eq_right hw,map_zero]
        exact zero_mem _
    · rw [hright,ite_eq_right hb,mul_zero]
      exact zero_mem _

end Categorification.Stendhal
