/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.SlRootDatum
import Categorification.Diagrams.KL3.Upward
import Categorification.Diagrams.KL3.SymmetryPsi

/-!
# Towards the 2-functor `U(sl_{m+1}) → U(sl_{m+2})`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1 (TeX source
`sln-2008-ArXiv.tex`). This file begins an auxiliary construction for the proof of Theorem 1.3
(label `thm-nondegenerate`, §6.4, l. 9598–9790) in arbitrary characteristic.

## Why this is needed

KL III prove Theorem 1.3 by letting `U(sl_n)` act on the equivariant cohomology rings of partial
flag varieties (the 2-representation `Γ^G`, §6.4), in which the Chern classes of the tautological
bundles are algebraically independent in low degree. The flag 2-representation `Γ_N` of this
library (KL III §6.1–6.3) uses non-equivariant cohomology `H_k`, where the total Chern classes
satisfy `∏_j x_j(t) = 1`. The bubble of colour `i` acts through the ratio of the Chern
polynomials of the blocks `i + 1` and `i`, and in degree `2` the `n - 1` linear parts of these
ratios satisfy one linear relation with coefficients `± 1, …` whose determinant is `n`. Hence if
`char k` divides `n` the bubbles of `U(sl_n)` act by linearly *dependent* operators for every
`N` (for example `sl_2` in characteristic `2`: `Γ_N` of the clockwise degree-`2` bubble is
`-2 x_{1,1} = 0`), and the direct analogue of KL III's argument with `Γ_N` fails.

We circumvent this by embedding `U(sl_{m+1})` into `U(sl_{m+2})` (begun in this file) and composing with
`Γ_N` for `sl_{m+2}`: the extra last block of the flag absorbs the relation `∏_j x_j(t) = 1`, so
that the ratios of consecutive Chern polynomials of the first `m + 1` blocks are independent in
bounded degree for large blocks. This replaces KL III's use of the equivariant `Γ^G`.

## The embedding

The vertices of `sl_{m+1}` are `Fin m`, embedded as the first `m` vertices of `sl_{m+2}`
(`Fin.castSucc`). A weight `λ ∈ ℤ^m` goes to `φ(λ) = (λ, L(λ)) ∈ ℤ^{m+1}` with
`L(λ) = -⌊s(λ)/(m+1)⌋`, `s(λ) = ∑_j (j+1) λ_j` (`phiW`). Since `s(i_X) = (m+1)·[i = m-1]`,
`φ(λ + i_X) = φ(λ) + (castSucc i)_X` (`phiW_add_iX`) and `⟨castSucc i, φ(λ)⟩ = ⟨i, λ⟩`
(`ip_phiW`). (`φ` is not additive: no additive map works, since the root lattice of `sl_{m+1}`
has index `m+1` in `ℤ^m`.) Letters, strands, generators, objects, layers and diagrams are
relabelled accordingly (`ιl`, `ιC`, `ιG`, `ιO`, `ιL`, `ιD`), giving a functor `ιF` between the
free 2-categories on the pivotal signatures.

## Main definitions and results

* weights: `sW`, `lastW`, `phiW`, `phiW_add_iX`, `phiW_sub_iX`, `ip_phiW`; the Cartan matrix of
  `sl_{m+1}` is the upper left block of that of `sl_{m+2}` (`slCartan_dot_castSucc`);
* strands and generators: `ιl`, `ιC`, `ιG`, with compatibility with sources, duals, domains and
  codomains (`src_ιC`, `dual_ιC`, `ιG_left`, `ιG_right`, `ιG_dom`, `ιG_cod`);
* `ιO`, `ιL` (`ιL_valid`, `ιL_dom`, `ιL_cod`), `ιD`, and
  `ιF m : Obj (psig (slRootDatum m)) ⥤ Obj (psig (slRootDatum (m+1)))` on free 2-categories;
  compatibility with whiskering (`ιL_whisker`, `ιO_whisker`, `ιD_whisker`);
* normal forms: `ιSh`, `ιLD`, `ιO_ob`, `ιL_lay`, `ιD_mkD`.

## Not yet formalized

The descent of `ιF` through the relations of Definition 3.1 to the presented 2-categories, i.e.
the `K`-linear functor
`embedU K m : (pres (slRootDatum m) K).Presented ⥤ (pres (slRootDatum (m+1)) K).Presented`
and its value on diagrams `embedU_diag`. (The bubble relations will use `ip_phiW`; the
`R(ν)`-relations will use `slCartan_dot_castSucc`.)
-/

noncomputable section

namespace Categorification.KL3.Diagram.SlnEmbed

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Categorification.Flag

variable {m : ℕ}

/-! ## Weights -/

/-- `s(λ) = ∑_j (j + 1) λ_j`. -/
def sW (lam : Fin m → ℤ) : ℤ := ∑ j : Fin m, ((j : ℤ) + 1) * lam j

/-- The last coordinate `L(λ) = -⌊s(λ) / (m + 1)⌋` of the embedded weight. -/
def lastW (lam : Fin m → ℤ) : ℤ := -(sW lam / ((m : ℤ) + 1))

/-- **The embedding of weights** `λ ↦ (λ, L(λ))`. -/
def phiW (lam : Fin m → ℤ) : Fin (m + 1) → ℤ := Fin.snoc (α := fun _ => ℤ) lam (lastW lam)

@[simp] theorem phiW_castSucc (lam : Fin m → ℤ) (a : Fin m) : phiW lam a.castSucc = lam a :=
  Fin.snoc_castSucc (α := fun _ => ℤ) _ _ _

@[simp] theorem phiW_last (lam : Fin m → ℤ) : phiW lam (Fin.last m) = lastW lam :=
  Fin.snoc_last (α := fun _ => ℤ) _ _

theorem sW_add (lam lam' : Fin m → ℤ) : sW (lam + lam') = sW lam + sW lam' := by
  simp only [sW, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem slCartan_dot_val (a i : Fin m) :
    (slCartan m).dot a i = if a.val = i.val then 2
      else if a.val + 1 = i.val ∨ i.val + 1 = a.val then -1 else 0 := by
  rw [slCartan_dot]
  simp only [Fin.ext_iff]

theorem slCartan_dot_castSucc (a i : Fin m) :
    (slCartan (m + 1)).dot a.castSucc i.castSucc = (slCartan m).dot a i := by
  rw [slCartan_dot_val, slCartan_dot_val]
  simp only [Fin.val_castSucc]

theorem sW_iX (i : Fin m) :
    sW ((slRootDatum m).iX i) = if i.val + 1 = m then (m : ℤ) + 1 else 0 := by
  have key : ∀ a : Fin m, ((a : ℤ) + 1) * (slRootDatum m).iX i a =
      2 * (if a.val = i.val then (i.val : ℤ) + 1 else 0) -
        (if a.val + 1 = i.val then (i.val : ℤ) else 0) -
        (if a.val = i.val + 1 then (i.val : ℤ) + 2 else 0) := by
    intro a
    rw [slRootDatum_iX_apply, slCartan_dot_val]
    split_ifs <;> push_cast <;> omega
  simp only [sW, key, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun n => if n = i.val then (i.val : ℤ) + 1 else 0),
    Fin.sum_univ_eq_sum_range (fun n => if n + 1 = i.val then (i.val : ℤ) else 0),
    Fin.sum_univ_eq_sum_range (fun n => if n = i.val + 1 then (i.val : ℤ) + 2 else 0),
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hi := i.isLt
  have h2 : ∑ n ∈ Finset.range m, (if n + 1 = i.val then (i.val : ℤ) else 0) = i.val := by
    rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · rw [h0]; simp
    · obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := ⟨i.val - 1, by omega⟩
      rw [hj]
      simp only [Nat.add_right_cancel_iff, Finset.sum_ite_eq', Finset.mem_range]
      rw [ite_eq_left (by omega)]
  rw [h2, ite_eq_left (Finset.mem_range.2 hi)]
  simp only [Finset.mem_range]
  split_ifs <;> omega

theorem lastW_add_iX (lam : Fin m → ℤ) (i : Fin m) :
    lastW (lam + (slRootDatum m).iX i) = lastW lam + (slRootDatum (m + 1)).iX i.castSucc (Fin.last m) := by
  have hm : ((m : ℤ) + 1) ≠ 0 := by omega
  rw [slRootDatum_iX_apply, slCartan_dot_val]
  simp only [lastW, sW_add, sW_iX, Fin.val_last, Fin.val_castSucc]
  have h1 : ¬ (m = i.val) := by omega
  have h3 : ¬ (m + 1 = i.val) := by omega
  simp only [h1, h3, false_or, ite_false]
  split_ifs with h
  · rw [show sW lam + ((m : ℤ) + 1) = sW lam + 1 * ((m : ℤ) + 1) by ring,
      Int.add_mul_ediv_right _ _ hm]
    ring
  · simp

/-- **`φ(λ + i_X) = φ(λ) + (castSucc i)_X`.** -/
theorem phiW_add_iX (lam : Fin m → ℤ) (i : Fin m) :
    phiW (lam + (slRootDatum m).iX i) = phiW lam + (slRootDatum (m + 1)).iX i.castSucc := by
  funext a
  refine Fin.lastCases ?_ (fun a => ?_) a
  · rw [phiW_last, Pi.add_apply, phiW_last, lastW_add_iX]
  · rw [phiW_castSucc, Pi.add_apply, Pi.add_apply, phiW_castSucc, slRootDatum_iX_apply,
      slRootDatum_iX_apply, slCartan_dot_castSucc]

theorem phiW_sub_iX (lam : Fin m → ℤ) (i : Fin m) :
    phiW (lam - (slRootDatum m).iX i) = phiW lam - (slRootDatum (m + 1)).iX i.castSucc := by
  have := phiW_add_iX (lam - (slRootDatum m).iX i) i
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

/-- **`⟨castSucc i, φ(λ)⟩ = ⟨i, λ⟩`.** -/
theorem ip_phiW (i : Fin m) (lam : Fin m → ℤ) :
    ip (slRootDatum (m + 1)) i.castSucc (phiW lam) = ip (slRootDatum m) i lam := by
  show slPair (m + 1) (Pi.single i.castSucc 1) (phiW lam) = slPair m (Pi.single i 1) lam
  rw [slPair_single_left, slPair_single_left, phiW_castSucc]

/-! ## Letters, strands and generators -/

/-- The embedding of signed letters. -/
def ιl (l : Letter (Fin m)) : Letter (Fin (m + 1)) := (l.1, l.2.castSucc)

@[simp] theorem ιl_mk (b : Bool) (i : Fin m) : ιl (b, i) = (b, i.castSucc) := rfl

@[simp] theorem ιl_dual (l : Letter (Fin m)) : ιl l.dual = (ιl l).dual := rfl

theorem ιl_injective : Function.Injective (ιl (m := m)) := by
  rintro ⟨b, i⟩ ⟨b', i'⟩ h
  simp only [ιl, Prod.mk.injEq] at h
  rw [h.1, Fin.castSucc_injective _ h.2]

/-- `φ(sh l + x) = sh (ι l) + φ(x)`. -/
theorem sh_ιl (l : Letter (Fin m)) (x : Fin m → ℤ) :
    sh (slRootDatum (m + 1)) (ιl l) + phiW x = phiW (sh (slRootDatum m) l + x) := by
  obtain ⟨b, i⟩ := l
  cases b
  · simp only [sh, ιl, sgn_false, neg_smul, one_smul]
    rw [neg_add_eq_sub, neg_add_eq_sub, phiW_sub_iX]
  · simp only [sh, ιl, sgn_true, one_smul]
    rw [add_comm ((slRootDatum m).iX i) x, phiW_add_iX, add_comm (phiW x)]

/-- The embedding of strand colours `⟨l, r⟩ ↦ ⟨ι l, φ r⟩`. -/
def ιC (c : Col (Fin m) (Fin m → ℤ)) : Col (Fin (m + 1)) (Fin (m + 1) → ℤ) := ⟨ιl c.l, phiW c.r⟩

theorem src_ιC (c : Col (Fin m) (Fin m → ℤ)) :
    (psig (slRootDatum (m + 1))).colourSrc (ιC c) = phiW ((psig (slRootDatum m)).colourSrc c) :=
  sh_ιl c.l c.r

theorem dual_ιC (c : Col (Fin m) (Fin m → ℤ)) :
    (inv (slRootDatum (m + 1))).dual (ιC c) = ιC ((inv (slRootDatum m)).dual c) := by
  rw [inv_dual, inv_dual]
  exact Col.ext rfl (sh_ιl c.l c.r)

theorem ok_map (r : Fin m → ℤ) (w : List (Col (Fin m) (Fin m → ℤ)))
    (h : (psig (slRootDatum m)).ok r w) : (psig (slRootDatum (m + 1))).ok (phiW r) (w.map ιC) := by
  induction w generalizing r with
  | nil => trivial
  | cons c w ih =>
    obtain ⟨hc, hw⟩ := h
    exact ⟨(src_ιC c).trans (congrArg phiW hc), ih c.r hw⟩

theorem endR_map (r : Fin m → ℤ) (w : List (Col (Fin m) (Fin m → ℤ))) :
    (psig (slRootDatum (m + 1))).endR (phiW r) (w.map ιC) =
      phiW ((psig (slRootDatum m)).endR r w) := by
  induction w generalizing r with
  | nil => rfl
  | cons c w ih => exact ih c.r

/-- The embedding of generators. -/
def ιG : (psig (slRootDatum m)).Gen → (psig (slRootDatum (m + 1))).Gen
  | .gen (.dot c) => .gen (.dot (ιC c))
  | .gen (.cross ε i j ν) => .gen (.cross ε i.castSucc j.castSucc (phiW ν))
  | .cup c => .cup (ιC c)
  | .cap c => .cap (ιC c)

theorem ιG_left (g : (psig (slRootDatum m)).Gen) :
    (psig (slRootDatum (m + 1))).left (ιG g) = phiW ((psig (slRootDatum m)).left g) := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · exact src_ιC c
  · show sh _ (ιl (ε, i)) + (sh _ (ιl (ε, j)) + phiW ν) = phiW (sh _ (ε, i) + (sh _ (ε, j) + ν))
    rw [sh_ιl, sh_ιl]
  · exact src_ιC c
  · rfl

theorem ιG_right (g : (psig (slRootDatum m)).Gen) :
    (psig (slRootDatum (m + 1))).right (ιG g) = phiW ((psig (slRootDatum m)).right g) := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · rfl
  · exact src_ιC c
  · rfl

theorem ιG_dom (g : (psig (slRootDatum m)).Gen) :
    (psig (slRootDatum (m + 1))).dom (ιG g) = ((psig (slRootDatum m)).dom g).map ιC := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · show [(⟨ιl (ε, i), sh _ (ιl (ε, j)) + phiW ν⟩ : Col (Fin (m + 1)) (Fin (m + 1) → ℤ)),
      ⟨ιl (ε, j), phiW ν⟩] = [⟨ιl (ε, i), phiW (sh _ (ε, j) + ν)⟩, ⟨ιl (ε, j), phiW ν⟩]
    rw [sh_ιl]
  · rfl
  · show [(inv (slRootDatum (m + 1))).dual (ιC c), ιC c] = [ιC ((inv (slRootDatum m)).dual c), ιC c]
    exact congrArg (fun x => [x, ιC c]) (dual_ιC c)

theorem ιG_cod (g : (psig (slRootDatum m)).Gen) :
    (psig (slRootDatum (m + 1))).cod (ιG g) = ((psig (slRootDatum m)).cod g).map ιC := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · show [(⟨ιl (ε, j), sh _ (ιl (ε, i)) + phiW ν⟩ : Col (Fin (m + 1)) (Fin (m + 1) → ℤ)),
      ⟨ιl (ε, i), phiW ν⟩] = [⟨ιl (ε, j), phiW (sh _ (ε, i) + ν)⟩, ⟨ιl (ε, i), phiW ν⟩]
    rw [sh_ιl]
  · show [ιC c, (inv (slRootDatum (m + 1))).dual (ιC c)] = [ιC c, ιC ((inv (slRootDatum m)).dual c)]
    exact congrArg (fun x => [ιC c, x]) (dual_ιC c)
  · rfl

/-! ## Objects, layers and diagrams -/

/-- The embedding of objects. -/
def ιO (a : Obj (psig (slRootDatum m))) : Obj (psig (slRootDatum (m + 1))) :=
  ⟨phiW a.start, a.word.map ιC⟩

@[simp] theorem ιO_start (a : Obj (psig (slRootDatum m))) : (ιO a).start = phiW a.start := rfl
@[simp] theorem ιO_word (a : Obj (psig (slRootDatum m))) : (ιO a).word = a.word.map ιC := rfl

theorem ιO_endR (a : Obj (psig (slRootDatum m))) : (ιO a).endR = phiW a.endR :=
  endR_map a.start a.word

/-- The embedding of layers. -/
def ιL (L : Layer (psig (slRootDatum m))) : Layer (psig (slRootDatum (m + 1))) :=
  ⟨phiW L.start, L.left.map ιC, ιG L.gen, L.right.map ιC⟩

theorem ιL_valid {L : Layer (psig (slRootDatum m))} (h : L.Valid) : (ιL L).Valid := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨ok_map _ _ h₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (psig _).endR (phiW L.start) (L.left.map ιC) = (psig _).left (ιG L.gen)
    exact (endR_map _ _).trans ((congrArg phiW h₂).trans (ιG_left _).symm)
  · show (psig _).ok ((psig _).left (ιG L.gen)) ((psig _).dom (ιG L.gen))
    rw [ιG_left, ιG_dom]; exact ok_map _ _ h₃
  · show (psig _).endR ((psig _).left (ιG L.gen)) ((psig _).dom (ιG L.gen)) = (psig _).right (ιG L.gen)
    rw [ιG_left, ιG_dom]
    exact (endR_map _ _).trans ((congrArg phiW h₄).trans (ιG_right _).symm)
  · show (psig _).ok ((psig _).left (ιG L.gen)) ((psig _).cod (ιG L.gen))
    rw [ιG_left, ιG_cod]; exact ok_map _ _ h₅
  · show (psig _).endR ((psig _).left (ιG L.gen)) ((psig _).cod (ιG L.gen)) = (psig _).right (ιG L.gen)
    rw [ιG_left, ιG_cod]
    exact (endR_map _ _).trans ((congrArg phiW h₆).trans (ιG_right _).symm)
  · show (psig _).ok ((psig _).right (ιG L.gen)) (L.right.map ιC)
    rw [ιG_right]; exact ok_map _ _ h₇

theorem map_ιC_append₃ (A B C : List (Col (Fin m) (Fin m → ℤ))) :
    A.map ιC ++ B.map ιC ++ C.map ιC = (A ++ B ++ C).map ιC := by
  simp only [List.map_append]

theorem ιL_dom (L : Layer (psig (slRootDatum m))) : (ιL L).dom = ιO L.dom := by
  refine Obj.ext rfl ?_
  simp only [Layer.dom_word, ιL, ιO_word, ιG_dom]
  exact map_ιC_append₃ _ _ _

theorem ιL_cod (L : Layer (psig (slRootDatum m))) : (ιL L).cod = ιO L.cod := by
  refine Obj.ext rfl ?_
  simp only [Layer.cod_word, ιL, ιO_word, ιG_cod]
  exact map_ιC_append₃ _ _ _

theorem chain_ιL {a b : Obj (psig (slRootDatum m))} {ls : List (Layer (psig (slRootDatum m)))}
    (h : Chain a ls b) : Chain (ιO a) (ls.map ιL) (ιO b) := by
  induction ls generalizing a with
  | nil => exact congrArg ιO h
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    exact ⟨ιL_valid hv, ιL_dom L, by rw [ιL_cod]; exact ih hc⟩

/-- The embedding of diagrams (relabelling every layer). -/
def ιD {a b : Obj (psig (slRootDatum m))} (d : a ⟶ b) : ιO a ⟶ ιO b :=
  Diagram.mk ((Diagram.layers d).map ιL) (chain_ιL (Diagram.chain d))

@[simp] theorem layers_ιD {a b : Obj (psig (slRootDatum m))} (d : a ⟶ b) :
    Diagram.layers (ιD d) = (Diagram.layers d).map ιL := rfl

variable (m) in
/-- **The embedding on the free 2-categories.** -/
def ιF : Obj (psig (slRootDatum m)) ⥤ Obj (psig (slRootDatum (m + 1))) where
  obj := ιO
  map := ιD
  map_id _ := rfl
  map_comp f g := Diagram.ext (by simp)

@[simp] theorem ιF_obj (a : Obj (psig (slRootDatum m))) : (ιF m).obj a = ιO a := rfl

@[simp] theorem layers_ιF {a b : Obj (psig (slRootDatum m))} (d : a ⟶ b) :
    Diagram.layers ((ιF m).map d) = (Diagram.layers d).map ιL := rfl

theorem ιL_whisker (L : Layer (psig (slRootDatum m))) (u : Obj (psig (slRootDatum m)))
    (v : List (Col (Fin m) (Fin m → ℤ))) :
    ιL (L.whisker u v) = (ιL L).whisker (ιO u) (v.map ιC) := by
  simp only [ιL, Layer.whisker, ιO]
  congr 1
  · exact List.map_append ..
  · exact List.map_append ..

theorem ιO_whisker (a u : Obj (psig (slRootDatum m))) (v : List (Col (Fin m) (Fin m → ℤ))) :
    ιO (a.whisker u v) = (ιO a).whisker (ιO u) (v.map ιC) := by
  simp only [ιO, Obj.whisker]
  congr 1
  exact (map_ιC_append₃ _ _ _).symm

theorem whiskerOK_ιO {a u : Obj (psig (slRootDatum m))} {v : List (Col (Fin m) (Fin m → ℤ))}
    (hw : a.WhiskerOK u v) : (ιO a).WhiskerOK (ιO u) (v.map ιC) := by
  obtain ⟨hu, hue, hv⟩ := hw
  refine ⟨ok_map _ _ hu, ?_, ?_⟩
  · rw [ιO_endR, hue]; rfl
  · rw [ιO_endR]; exact ok_map _ _ hv

theorem ιD_whisker {a b : Obj (psig (slRootDatum m))} (d : a ⟶ b) (u : Obj (psig (slRootDatum m)))
    (v : List (Col (Fin m) (Fin m → ℤ))) (hw : a.WhiskerOK u v) :
    ιD (Diagram.whisker d u v hw) = Diagram.cast (Diagram.whisker (ιD d) (ιO u) (v.map ιC)
      (whiskerOK_ιO hw)) (ιO_whisker a u v).symm (ιO_whisker b u v).symm := by
  apply Diagram.ext
  rw [layers_ιD, Diagram.layers_cast]
  show ((Diagram.layers d).map (·.whisker u v)).map ιL =
    ((Diagram.layers d).map ιL).map (·.whisker (ιO u) (v.map ιC))
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun L _ => ιL_whisker L u v

/-! ## Normal forms -/

/-- The embedding of shapes of generators. -/
def ιSh : Shape (Fin m) → Shape (Fin (m + 1))
  | .dot l => .dot (ιl l)
  | .cross ε i j => .cross ε i.castSucc j.castSucc
  | .cup l => .cup (ιl l)
  | .cap l => .cap (ιl l)

@[simp] theorem ιSh_dot (l : Letter (Fin m)) : ιSh (.dot l) = .dot (ιl l) := rfl
@[simp] theorem ιSh_cross (ε : Bool) (i j : Fin m) :
    ιSh (.cross ε i j) = .cross ε i.castSucc j.castSucc := rfl
@[simp] theorem ιSh_cup (l : Letter (Fin m)) : ιSh (.cup l) = .cup (ιl l) := rfl
@[simp] theorem ιSh_cap (l : Letter (Fin m)) : ιSh (.cap l) = .cap (ιl l) := rfl

theorem ιSh_dom (g : Shape (Fin m)) : (ιSh g).dom = g.dom.map ιl := by cases g <;> rfl

theorem ιSh_cod (g : Shape (Fin m)) : (ιSh g).cod = g.cod.map ιl := by cases g <;> rfl

theorem wt_map (μ : Fin m → ℤ) (t : List (Letter (Fin m))) :
    phiW (wt (slRootDatum m) μ t) = wt (slRootDatum (m + 1)) (phiW μ) (t.map ιl) := by
  induction t with
  | nil => rfl
  | cons l t ih => rw [wt_cons, List.map_cons, wt_cons, ← ih, sh_ιl]

theorem wd_map (μ : Fin m → ℤ) (t : List (Letter (Fin m))) :
    (wd (slRootDatum m) μ t).map ιC = wd (slRootDatum (m + 1)) (phiW μ) (t.map ιl) := by
  induction t with
  | nil => rfl
  | cons l t ih =>
    rw [wd_cons, List.map_cons, ih, List.map_cons, wd_cons, ← wt_map]
    rfl

theorem ιO_ob (μ : Fin m → ℤ) (t : List (Letter (Fin m))) :
    ιO (ob (slRootDatum m) μ t) = ob (slRootDatum (m + 1)) (phiW μ) (t.map ιl) :=
  Obj.ext (wt_map μ t) (wd_map μ t)

theorem ιG_gen (ν : Fin m → ℤ) (g : Shape (Fin m)) :
    ιG (g.gen (slRootDatum m) ν) = (ιSh g).gen (slRootDatum (m + 1)) (phiW ν) := by
  cases g with
  | dot l => rfl
  | cross ε i j => rfl
  | cap l => rfl
  | cup l =>
    show PivotalGen.cup (ιC ⟨l, sh _ l.dual + ν⟩) = PivotalGen.cup ⟨ιl l, sh _ (ιl l).dual + phiW ν⟩
    rw [← ιl_dual, sh_ιl]
    rfl

theorem ιL_lay (μ : Fin m → ℤ) (u : List (Letter (Fin m))) (g : Shape (Fin m))
    (v : List (Letter (Fin m))) :
    ιL (lay (slRootDatum m) μ u g v) =
      lay (slRootDatum (m + 1)) (phiW μ) (u.map ιl) (ιSh g) (v.map ιl) := by
  refine Layer.ext ?_ ?_ ?_ ?_
  · show phiW (wt _ μ (u ++ g.dom ++ v)) = wt _ (phiW μ) (u.map ιl ++ (ιSh g).dom ++ v.map ιl)
    rw [wt_map, ιSh_dom, List.map_append, List.map_append]
  · show (wd _ (wt _ μ (g.dom ++ v)) u).map ιC =
      wd _ (wt _ (phiW μ) ((ιSh g).dom ++ v.map ιl)) (u.map ιl)
    rw [wd_map, wt_map, ιSh_dom, List.map_append]
  · show ιG (g.gen _ (wt _ μ v)) = (ιSh g).gen _ (wt _ (phiW μ) (v.map ιl))
    rw [ιG_gen, wt_map]
  · exact wd_map μ v

/-- The embedding of layer data. -/
def ιLD (x : LayerData (Fin m)) : LayerData (Fin (m + 1)) := (x.1.map ιl, ιSh x.2.1, x.2.2.map ιl)

theorem sChain_ι {s t : List (Letter (Fin m))} {ls : List (LayerData (Fin m))} (h : SChain s ls t) :
    SChain (s.map ιl) (ls.map ιLD) (t.map ιl) := by
  induction ls generalizing s with
  | nil => exact congrArg (List.map ιl) h
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    refine ⟨by simp [ιLD, ιSh_dom], ?_⟩
    have := ih h
    simpa [ιLD, ιSh_cod] using this

theorem layers_ιD_mkD (μ : Fin m → ℤ) {s t : List (Letter (Fin m))} (ls : List (LayerData (Fin m)))
    (h : SChain s ls t) :
    Diagram.layers (ιD (mkD (slRootDatum m) μ ls h)) =
      layList (slRootDatum (m + 1)) (phiW μ) (ls.map ιLD) := by
  simp only [layers_ιD, layers_mkD, layList, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  exact ιL_lay μ x.1 x.2.1 x.2.2

/-- **The embedding on normal-form diagrams.** -/
theorem ιD_mkD (μ : Fin m → ℤ) {s t : List (Letter (Fin m))} (ls : List (LayerData (Fin m)))
    (h : SChain s ls t) :
    ιD (mkD (slRootDatum m) μ ls h) = Diagram.cast (mkD (slRootDatum (m + 1)) (phiW μ) (ls.map ιLD)
      (sChain_ι h)) (ιO_ob μ s).symm (ιO_ob μ t).symm :=
  Diagram.ext (layers_ιD_mkD μ ls h)

end Categorification.KL3.Diagram.SlnEmbed

end
