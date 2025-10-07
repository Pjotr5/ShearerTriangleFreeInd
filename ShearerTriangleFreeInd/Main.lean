import Mathlib
import ShearerTriangleFreeInd.Analysis
import ShearerTriangleFreeInd.Analysis_W
import ShearerTriangleFreeInd.Proofs



namespace SimpleGraph

theorem triangle_free_independence_bound {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.CliqueFree 3) : G.indepNum ≥
        (Fintype.card V : ℝ) *
        (fun x ↦
          if x = 1 then 1/2
          else          (x * Real.log x - x + 1) / (x - 1)^2) (G.averageDegree) := by
  convert Shearer_bound (f' := F') hT ?_ ?_ ?_
  · exact fun x y hx hy ↦ F_convex_inequality hx hy
  · exact fun x hx ↦ F'_nonpositive hx
  · intro V' _ G'
    by_cases hV : Nonempty V'
    · rw [extra_rewrite_aux hV]
      exact le_of_eq (by convert (F_diff_equation (x := d(G'))).symm using 1)
    · rw [extra_IsEmpty (not_nonempty_iff.1 hV)]
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
  · exact fun x y hx hy ↦ G_convex_inequality hx (le_of_lt hy)
  · exact fun x hx ↦ G'_nonpositive (le_of_lt hx)
  · intro V' _ G'
    by_cases hV : Nonempty V'
    · rw [extra_rewrite_aux hV, extra_rewrite_aux' hV]
      convert le_of_lt (goal_bound (Rat.cast_nonneg.2 (averageDegree_nonneg (G := G')))) using 1
    · repeat rw [extra_IsEmpty (not_nonempty_iff.1 hV)]
      norm_num

end SimpleGraph
