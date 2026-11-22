# The integral KL I corner

Khovanov–Lauda, arXiv:0803.4121v2, §2.1 and Theorem 2.5. A diagram has specified colour sequences on its lower and upper boundaries. Diagrams with these boundaries generate an abelian group modulo the local relations. Stacking a diagram above another puts it on the left in the product.

| Source object or convention | Integral Lean realization |
| --- | --- |
| Graph, strand content and boundary words | A simple graph on an arbitrary vertex type, a multiset of vertices, and `Seq ν`. Its content equation counts repetitions and includes the empty word. |
| Algebra of diagrams | `R1 ℤ Γ ν` uses `KLRAlgebra`, the quotient by `Rel` of the free algebra on boundary idempotents, dots and crossings. Idempotents split the unit, dots commute, distant generators commute, and sliding past an equal-colour crossing contributes the idempotent. |
| Local crossing rules | In `Rel.cross_sq` equal colours give zero directly. For distinct colours `klQ` gives the sum of the two dots on an edge and one off an edge. The braid relation uses the divided difference of that polynomial when the outer colours agree and the middle colour differs. |
| Bottom word i and top word j | `corner j i` is the image of multiplication by the corresponding idempotents on the left (j) and right (i). |
| Minimal crossing diagrams | `CornerIdx j i` pairs a permutation taking i to j with a finitely supported vector of natural dot counts. The strand positions form a finite type, so every bottom dot assignment occurs. `IsReduced` requires valid adjacent transpositions and minimal length. `wordProd` fixes their product. |
| Basis vector and grading | `ψw` multiplies the chosen crossings in list order. The right factor `pol (monomial u 1) * e i` puts dots below them. In `klGradingDatum ℤ Γ` a dot has degree two and a crossing contributes minus the Cartan entry of its two colours. |

The integral spec binds the corner basis, its values, and membership of each value in a component of this grading.

The grading has a direct-sum decomposition by `GradingDatum.gradedAlgebra`. Taking degrees in the ambient algebra is sufficient because the boundary idempotents have degree zero. In the two-strand one-colour corner, `Spec/KL1/TwoStrands.lean` checks the equal-colour square and dot slide and obtains a nonzero vector from the integral basis.

## Deviations for Theorem 2.5

| Item | Class | Correspondence |
| --- | --- | --- |
| Graph, finite content and both boundary words (§2.1) | Identical | No finiteness hypothesis on the vertex set. A multiset records finite content. |
| Decidability of vertex equality and adjacency | Convention | Classical decisions supply both for every graph. |
| Minimal presentation for each permutation (§2.3) | Identical | Reducedness includes validity. The separate product equation fixes the permutation. Canonical words witness existence for every size. |
| Generator indices | Convention | Lean counts from zero and uses natural-number lists with an explicit validity condition. This represents every word on the in-range generators. |
| Coefficient group | More general in the library | The underlying corner basis permits integral domains. The spec uses the source coefficient ring ℤ. |
| Basis vectors and degrees (Theorem 2.5) | Identical | The same basis witnesses freeness, the product formula for every index and homogeneity in the graph grading. |

<details>
<summary>Project constants in the unfolded statement (127)</summary>

The closure starts at the type of the spec. It follows project declaration types, definition bodies and inductive constructors. It stops at Mathlib and Lean constants and skips theorem proof bodies. Names below are relative to the prefix on their row.

| Prefix | Names |
| --- | --- |
| `Categorification.CoactionGrading` | `grade` |
| `Categorification.CoactionGrading.grade` | `_proof_1`, `_proof_2`, `_proof_3` |
| `Categorification.KLR` | `Gen`, `GradingDatum`, `KLRAlgebra`, `Rel`, `Seq`, `cartan`, `fe`, `fx`, `fψ`, `klGradingDatum`, `klQ`, `ncEval`, `qbar` |
| `Categorification.KLR.Gen` | `casesOn`, `cross`, `dot`, `idem`, `rec` |
| `Categorification.KLR.GradingDatum` | `coaction`, `degX`, `degΨ`, `dx`, `dψ`, `genImage`, `grade`, `liftF`, `liftF_rel`, `mk` |
| `Categorification.KLR.GradingDatum.dψ` | `_proof_2` |
| `Categorification.KLR.GradingDatum.genImage` | `match_1` |
| `Categorification.KLR.KLRAlgebra` | `CornerIdx`, `corner`, `dotSubalgebra`, `dotSubalgebra_comm`, `e`, `instAlgebra`, `instCommRingSubtypeMemSubalgebraDotSubalgebra`, `instRing`, `mk`, `pol`, `x`, `ψ`, `ψw` |
| `Categorification.KLR.KLRAlgebra.corner` | `_proof_1`, `_proof_2`, `_proof_3`, `_proof_4` |
| `Categorification.KLR.KLRAlgebra.instAlgebra` | `_aux_1`, `_aux_3`, `_proof_5`, `_proof_6` |
| `Categorification.KLR.KLRAlgebra.instRing` | `_aux_1`, `_aux_13`, `_aux_15`, `_aux_20`, `_aux_28`, `_aux_3`, `_aux_32`, `_aux_34`, `_aux_36`, `_aux_43`, `_aux_8`, `_proof_10`, `_proof_11`, `_proof_12`, `_proof_17`, `_proof_18`, `_proof_19`, `_proof_22`, `_proof_23`, `_proof_24`, `_proof_25`, `_proof_26`, `_proof_27`, `_proof_30`, `_proof_31`, `_proof_38`, `_proof_39`, `_proof_40`, `_proof_41`, `_proof_42`, `_proof_45`, `_proof_46`, `_proof_5`, `_proof_6`, `_proof_7` |
| `Categorification.KLR.KLRAlgebra.pol` | `_proof_1` |
| `Categorification.KLR.Rel` | `_proof_1`, `_proof_2`, `_proof_3`, `braid`, `cross_cross`, `cross_idem`, `cross_sq`, `cross_zero`, `dot_cross`, `dot_cross_left`, `dot_cross_right`, `dot_dot`, `dot_idem`, `idem_mul`, `idem_sum` |
| `Categorification.KLR.Seq` | `instDecidableEq`, `instFinite`, `instFintype`, `instMulActionPermFinCard`, `lbl` |
| `Categorification.KLR.Seq.instDecidableEq` | `_aux_1` |
| `Categorification.KLR.Seq.instMulActionPermFinCard` | `_proof_1`, `_proof_2`, `_proof_3` |
| `Categorification.KLR.klGradingDatum` | `_proof_1`, `_proof_2` |
| `Categorification.KLR.klQ` | `_proof_1` |
| `Categorification.KLR.qbar` | `_proof_1`, `_proof_2` |
| `Categorification.TypeA` | `IsReduced`, `ValidWord`, `length`, `sadj`, `wordProd` |
| `Categorification.TypeA.length` | `_proof_1` |
| `Categorification.TypeA.sadj` | `_proof_2` |

</details>
