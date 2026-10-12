/-
Copyright (c) 2024 Pjotr Buys. All rights reserved.
Authors: Pjotr Buys
-/

import Mathlib
import ShearerTriangleFreeInd.Analysis
import ShearerTriangleFreeInd.Analysis_W
import ShearerTriangleFreeInd.Proofs
/-!
# Bounds for triangle-free graphs

The two main statements give Shearer's lower bound on the independence number and the
lower bound on the number of independent sets from [BvdHK2025]. Their proofs combine the
analytic results in `Analysis` and `Analysis_W` with the combinatorial bounds in `Proofs`.
-/

namespace SimpleGraph

theorem triangle_free_independence_bound {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.CliqueFree 3) : G.indepNum ≥
        (Fintype.card V : ℝ) *
        (fun x ↦
          if x = 1 then 1/2
          else          (x * Real.log x - x + 1) / (x - 1)^2) (G.averageDegree) := by
  convert Shearer_bound (f' := F') hT ?_ ?_ ?_
  · rfl
  · exact fun x y hx hy ↦ F_convex_inequality hx hy
  · exact fun x hx ↦ F'_nonpositive hx
  · intro V' _ G'
    by_cases hV : Nonempty V'
    · rw [shearerError_add_one_sq hV]
      exact le_of_eq (by convert (F_diff_equation (x := d(G'))).symm using 1; all_goals rfl)
    · rw [shearerError_of_isEmpty (not_nonempty_iff.1 hV)]
      norm_num

open Classical Finset in
theorem triangle_free_independence_count_bound {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.CliqueFree 3) : #({s | G.IsIndepSet s} : Finset (Set V)) ≥
        Real.exp (
          (Fintype.card V : ℝ) *
          (fun x ↦
            if x = 2 then Real.exp (-W 2)
            else          ((1 / 2) * (W x)^2 + W x - ((1 / 2) * (W 2)^2 + W 2)) / (x - 2))
              (G.averageDegree)
           ) := by
  convert independent_set_count_bound (f' := G') hT ?_ ?_ ?_
  · rfl
  · rfl
  · exact fun x y hx hy ↦ G_convex_inequality hx (le_of_lt hy)
  · exact fun x hx ↦ G'_nonpositive (le_of_lt hx)
  · intro V' _ G'
    by_cases hV : Nonempty V'
    · rw [shearerError_add_one_sq hV, shearerError_one hV]
      convert le_of_lt (goal_bound (Rat.cast_nonneg.2 (averageDegree_nonneg (G := G')))) using 1
      all_goals rfl
    · repeat rw [shearerError_of_isEmpty (not_nonempty_iff.1 hV)]
      norm_num

end SimpleGraph
