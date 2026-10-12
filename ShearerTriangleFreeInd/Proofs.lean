/-
Copyright (c) 2024 Pjotr Buys. All rights reserved.
Authors: Pjotr Buys
-/
import Mathlib

import ShearerTriangleFreeInd.Analysis
import ShearerTriangleFreeInd.Analysis_W

/-!
# Combinatorial core of the Shearer bounds for triangle-free graphs

This file contains the graph-theoretic part of the proofs of Shearer's lower bound on the
independence number of a triangle-free graph, and of the lower bound on the number of
independent sets from [BvdHK2025]. The analytic ingredients live in
`ShearerTriangleFreeInd.Analysis` and `ShearerTriangleFreeInd.Analysis_W`; the two headline
statements are in `ShearerTriangleFreeInd.Main`.

## Main definitions

* `SimpleGraph.averageDegree`: the average degree `d(G)` of a finite graph, as a rational.
* `SimpleGraph.closedNeighborSet`: the closed neighborhood of a vertex.
* `SimpleGraph.edgeIncidenceFinset`: the edges incident to a vertex set.
* `SimpleGraph.shearerError`: the error functional appearing in the convexity step.

## Main results

* `SimpleGraph.Shearer_bound`: for triangle-free `G` and every `f` satisfying the convexity
  inequality `ConvexIneq f f'`, with `f'` nonpositive on the positives and the Shearer error
  side condition,
  `α(G) ≥ #V(G) * f d(G)`.
* `SimpleGraph.independent_set_count_bound`: the analogous exponential lower bound on the
  number of independent sets of `G`, with its exponential Shearer error side condition.

## References

* [J. B. Shearer, *A note on the independence number of triangle-free graphs*][Shearer1983]
* [P. Buys, J. van den Heuvel, R. J. Kang,
  *Triangle-free graphs with the fewest independent sets*][BvdHK2025]
-/

namespace SimpleGraph

open Finset SimpleGraph BigOperators
attribute [local instance] Classical.propDecidable

variable {V : Type} {G : SimpleGraph V} {v : V}
variable [Fintype V]

/-- The finset of all vertices of `G`, i.e. `Finset.univ`; carries the scoped notation `V(G)`. -/
def vertexFinset (_G : SimpleGraph V) : Finset V := univ

/-- The average degree of a finite graph `G`, as a rational. -/
noncomputable def averageDegree (G : SimpleGraph V) : ℚ := 𝔼 v, (G.degree v : ℚ)

/-- The finset of all independent sets of vertices of `G`; carries the scoped notation `ℐ(G)`. -/
noncomputable def indepSetFinsetAll (G : SimpleGraph V) : Finset (Set V) := {s | G.IsIndepSet s}

scoped notation "V(" G ")" => vertexFinset G
scoped notation "E(" G ")" => edgeFinset G
scoped notation "d(" G ")" => averageDegree G
scoped notation "α(" G ")" => indepNum G
scoped notation "ℐ(" G ")" => indepSetFinsetAll G

lemma vertexFinset_eq_univ : V(G) = univ := rfl
lemma card_vertexFinset : #V(G) = Fintype.card V := rfl

lemma averageDegree_def : d(G) = 𝔼 v, (G.degree v : ℚ) := rfl

lemma mem_indepSetFinsetAll_iff {S : Set V} : S ∈ ℐ(G) ↔ G.IsIndepSet S :=
  mem_filter.trans (and_iff_right (mem_univ _))


lemma averageDegree_nonneg : 0 ≤ d(G) := expect_nonneg fun _ _ ↦ Nat.cast_nonneg' _

lemma averageDegree_pos_of_ne_zero (hd : d(G) ≠ 0) : 0 < d(G) := averageDegree_nonneg.lt_of_ne' hd

/-- The handshake lemma in terms of the average degree: `#V(G) * d(G) = 2 * #E(G)`. -/
lemma card_mul_averageDegree_eq_twice_card_edges : #V(G) * d(G) = 2 * #E(G) := by
  rw [averageDegree_def, vertexFinset_eq_univ, card_mul_expect]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

lemma edgeFinset_eq_empty_of_averageDegree_eq_zero (hd : d(G) = 0) : E(G) = ∅ := by
  simpa [hd] using card_mul_averageDegree_eq_twice_card_edges (G := G)


lemma averageDegree_eq_zero_of_isEmpty (hV : IsEmpty V) : d(G) = 0 := by
  simp [averageDegree]

lemma nonempty_of_averageDegree_pos (h : 0 < d(G)) : Nonempty V :=
  not_isEmpty_iff.mp fun hV ↦ h.ne' <| averageDegree_eq_zero_of_isEmpty hV


lemma cast_averageDegree : (d(G) : ℝ) = 𝔼 v, (G.degree v : ℝ) :=
  algebraMap.coe_expect (M := ℚ) _ _

omit [Fintype V] in
variable (G) (v) in
/-- The closed neighborhood `N[v]` of a vertex `v`, i.e. `v` together with its neighbors. -/
def closedNeighborSet : Set V := insert v (G.neighborSet v)

omit [Fintype V] in
lemma self_mem_closedNeighborSet : v ∈ G.closedNeighborSet v := Set.mem_insert _ _

omit [Fintype V] in
lemma closedNeighborSet_nonempty : (G.closedNeighborSet v).Nonempty :=
  ⟨_, self_mem_closedNeighborSet⟩


lemma card_vertexFinset_induce (S : Set V) [DecidablePred (· ∈ S)] :
    #V(G.induce S) = #S.toFinset := by
  simp [vertexFinset_eq_univ]

lemma card_vertexFinset_eq_card_add_card_compl (S : Set V) :
    #V(G) = #S.toFinset + #Sᶜ.toFinset := by
  rw [card_vertexFinset, Set.toFinset_compl, card_add_card_compl]

lemma card_vertexFinset_induce_compl_lt {S : Set V} (hS : S.Nonempty) :
    #V(G.induce Sᶜ) < #V(G) := by
  rw [card_vertexFinset_induce, Set.toFinset_compl]
  exact S.toFinset.card_compl_lt_iff_nonempty.mpr (Set.toFinset_nonempty.mpr hS)

lemma card_vertexFinset_eq_zero_of_isEmpty (hV : IsEmpty V) : #V(G) = 0 :=
  Fintype.card_eq_zero_iff.2 hV


lemma card_toFinset_closedNeighborSet (v : V) :
    #(G.closedNeighborSet v).toFinset = G.degree v + 1 := by
  classical
  have h : (G.closedNeighborSet v).toFinset = insert v (G.neighborFinset v) := by
    ext w
    rw [Set.mem_toFinset]
    simp [closedNeighborSet]
  rw [h, card_insert_of_notMem (G.notMem_neighborFinset_self v),
    card_neighborFinset_eq_degree]

lemma expect_card_closedNeighborSet (hV : Nonempty V) :
    𝔼 v, (#(G.closedNeighborSet v).toFinset : ℝ) = d(G) + 1 := by
  simp_rw [card_toFinset_closedNeighborSet, Nat.cast_add_one, expect_add_distrib,
    cast_averageDegree, expect_const univ_nonempty]


variable (G) in
/-- The finset of edges of `G` with both endpoints in `S`. -/
noncomputable def edgeFinsetOn (S : Set V) : Finset (Sym2 V) := {e ∈ E(G) | ∀ v ∈ e, v ∈ S}

variable (G) in
/-- The finset of edges of `G` with at least one endpoint in `S`. -/
noncomputable def edgeIncidenceFinset (S : Set V) : Finset (Sym2 V) := {e ∈ E(G) | ∃ v ∈ S, v ∈ e}


lemma map_edgeFinset_induce_eq_edgeFinsetOn (S : Set V) :
    map (Function.Embedding.subtype _).sym2Map E(G.induce S) = G.edgeFinsetOn S := by
  simp [map_edgeFinset_induce, edgeFinsetOn, Finset.ext_iff, Finset.mem_sym2_iff]

lemma card_edgeFinset_induce (S : Set V) : #E(G.induce S) = #(G.edgeFinsetOn S) := by
  rw [← map_edgeFinset_induce_eq_edgeFinsetOn, card_map]


lemma card_edgeIncidenceFinset_eq_zero_of_averageDegree_eq_zero (hd : d(G) = 0) (S : Set V) :
    #(G.edgeIncidenceFinset S) = 0 := by
  simp [edgeIncidenceFinset, edgeFinset_eq_empty_of_averageDegree_eq_zero hd]

lemma averageDegree_induce_eq_zero_of_averageDegree_eq_zero (hd : d(G) = 0) (S : Set V) :
    d(G.induce S) = 0 := by
  simp [edgeFinset_eq_empty.mp (edgeFinset_eq_empty_of_averageDegree_eq_zero hd), averageDegree]

lemma card_edgeFinset_eq_card_edgeIncidenceFinset_add_card_induce_compl (S : Set V) :
    #E(G) = #(G.edgeIncidenceFinset S) + #E(induce Sᶜ G) := by
  convert (card_filter_add_card_filter_not (∃ v ∈ S, v ∈ ·) (s := E(G))).symm using 2
  · rfl
  convert card_edgeFinset_induce (G := G) Sᶜ using 3
  ext e
  simp [edgeFinsetOn, imp_not_comm]

lemma edgeIncidenceFinset_singleton (v : V) : G.edgeIncidenceFinset {v} = G.incidenceFinset v := by
  grind [edgeIncidenceFinset, incidenceFinset_eq_filter]

lemma card_edgeIncidenceFinset_singleton (v : V) : #(G.edgeIncidenceFinset {v}) = G.degree v :=
  edgeIncidenceFinset_singleton v ▸ G.card_incidenceFinset_eq_degree v

lemma degree_eq_zero_of_averageDegree_eq_zero (hd : d(G) = 0) : G.degree v = 0 :=
  mod_cast (expect_eq_zero_iff_of_nonneg fun _ _ ↦ Nat.cast_nonneg' _).mp hd v (mem_univ v)

lemma mem_edgeIncidenceFinset_closedNeighborSet_iff (e : Sym2 V) (v : V) :
    e ∈ G.edgeIncidenceFinset (G.closedNeighborSet v) ↔
    ∃ w ∈ G.neighborSet v, e ∈ G.incidenceSet w := by
  induction e with
  | _ a b =>
    simp only [edgeIncidenceFinset, mem_filter, mem_edgeFinset, mem_edgeSet, closedNeighborSet,
      Set.mem_insert_iff, mem_neighborSet, incidenceSet, Set.mem_ofPred_eq, Sym2.mem_iff]
    grind [adj_comm]

lemma edgeIncidenceFinset_closedNeighborSet (v : V) :
    G.edgeIncidenceFinset (G.closedNeighborSet v) =
      (G.neighborFinset v).biUnion fun u ↦ G.incidenceFinset u := by
  simp [Finset.ext_iff, mem_edgeIncidenceFinset_closedNeighborSet_iff]

omit [Fintype V] in
lemma pairwiseDisjoint_incidenceSet_neighborSet_of_triangleFree (v : V) (hT : G.CliqueFree 3) :
    (G.neighborSet v).PairwiseDisjoint G.incidenceSet := fun _ hu _ hw huw ↦
  Set.disjoint_iff_inter_eq_empty.mpr <| G.incidenceSet_inter_incidenceSet_of_not_adj
    (isIndepSet_neighborSet_of_triangleFree G hT v hu hw huw) huw

lemma pairwiseDisjoint_incidenceFinset_neighborSet_of_triangleFree (v : V) (hT : G.CliqueFree 3) :
    (G.neighborSet v).PairwiseDisjoint (fun u ↦ G.incidenceFinset u) := by
  simpa only [← Finset.pairwiseDisjoint_coe, coe_incidenceFinset] using
    pairwiseDisjoint_incidenceSet_neighborSet_of_triangleFree v hT

lemma card_edgeIncidenceFinset_closedNeighborSet (hT : G.CliqueFree 3) (v : V) :
    #(G.edgeIncidenceFinset (G.closedNeighborSet v)) = ∑ u ∈ G.neighborFinset v, G.degree u := by
  simp [edgeIncidenceFinset_closedNeighborSet, card_biUnion ((coe_neighborFinset G v).symm ▸
    pairwiseDisjoint_incidenceFinset_neighborSet_of_triangleFree v hT)]

lemma expect_card_edgeIncidenceFinset_closedNeighborSet (hT : G.CliqueFree 3) :
    𝔼 v, (#(G.edgeIncidenceFinset (G.closedNeighborSet v)) : ℚ) = 𝔼 v, (G.degree v : ℚ) ^ 2 := by
  simp only [expect_eq_sum_div_card, card_edgeIncidenceFinset_closedNeighborSet hT, Nat.cast_sum]
  congr 1
  rw [sum_comm' (s' := fun u ↦ G.neighborFinset u) (t' := univ) fun v u ↦ by simp [adj_comm]]
  simp [pow_two]

lemma expect_card_edgeIncidenceFinset_closedNeighborSet_real (hT : G.CliqueFree 3) :
    𝔼 v, (#(G.edgeIncidenceFinset (G.closedNeighborSet v)) : ℝ) = 𝔼 v, (G.degree v : ℚ)^2 :=
  expect_card_edgeIncidenceFinset_closedNeighborSet hT ▸ (map_expect (algebraMap ℚ ℝ) _ _).symm

lemma sq_averageDegree_le_expect_sq_degree : d(G) ^ 2 ≤ 𝔼 v, (G.degree v : ℚ) ^ 2 := by
  simpa only [averageDegree_def, expect_eq_sum_div_card] using sum_div_card_sq_le_sum_sq_div_card


lemma bot_mem_indepSetFinsetAll : ⊥ ∈ ℐ(G) := mem_indepSetFinsetAll_iff.mpr <| Set.pairwise_empty _

lemma indepSetFinsetAll_nonempty : ℐ(G).Nonempty := ⟨⊥, bot_mem_indepSetFinsetAll⟩

lemma mem_indepSetFinsetAll_of_subset {S₁ S₂ : Set V} (hind : S₁ ∈ ℐ(G)) (hsub : S₂ ⊆ S₁) :
    S₂ ∈ ℐ(G) :=
  mem_indepSetFinsetAll_iff.mpr ((mem_indepSetFinsetAll_iff.mp hind).mono hsub)

lemma mem_indepSetFinsetAll_induce_iff (S : Set V) (I : Set S) :
    I ∈ ℐ(G.induce S) ↔ Subtype.val '' I ∈ ℐ(G) := by simp [mem_indepSetFinsetAll_iff, Set.Pairwise]


/-- The image under `Subtype.val` as an embedding `Set S ↪ Set V`. -/
def embeddingOfSubsetSubtype (S : Set V) : Set S ↪ Set V :=
  ⟨Set.image Subtype.val, Subtype.val_injective.image_injective⟩

omit [Fintype V] in
lemma embeddingOfSubsetSubtype_apply (S : Set V) (I : Set S) : embeddingOfSubsetSubtype S I =
    Subtype.val '' I := rfl

lemma map_indepSetFinsetAll_induce_eq_filter_subset (S : Set V) :
    map (embeddingOfSubsetSubtype S) ℐ(G.induce S) = filter (· ⊆ S) ℐ(G) := by
  ext I
  simp only [mem_map, embeddingOfSubsetSubtype_apply, mem_indepSetFinsetAll_induce_iff]
  grind [Subtype.coe_image_of_subset]

lemma mem_indepSetFinsetAll_and_subset_of_mem_induce {S : Set V} {I : Set S}
    (hI : I ∈ ℐ(induce S G)) :
    Subtype.val '' I ∈ ℐ(G) ∧ Subtype.val '' I ⊆ S :=
  ⟨(mem_indepSetFinsetAll_induce_iff S I).mp hI, Subtype.coe_image_subset S I⟩

lemma card_indepSetFinsetAll_induce (S : Set V) [DecidablePred (· ∈ S)] :
    #ℐ(G.induce S) = #(filter (· ⊆ S) ℐ(G)) := by
  rw [← map_indepSetFinsetAll_induce_eq_filter_subset, Finset.card_map]
  congr!

lemma ncard_le_indepNum_of_mem_indepSetFinsetAll {I : Set V} (hI : I ∈ ℐ(G)) : I.ncard ≤ α(G) :=
  I.ncard_eq_toFinset_card' ▸
    (I.coe_toFinset.symm ▸ mem_indepSetFinsetAll_iff.mp hI).card_le_indepNum

variable (G) in
lemma exists_mem_indepSetFinsetAll_ncard_eq_indepNum : ∃ I ∈ ℐ(G), I.ncard = α(G) :=
  have ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  ⟨s, mem_indepSetFinsetAll_iff.mpr hs.isIndepSet, (Set.ncard_coe_finset s).trans hs.card_eq⟩

/-- The independent-set version of `isClique_insert`. -/
lemma insert_mem_indepSetFinsetAll_iff {S : Set V} :
    insert v S ∈ ℐ(G) ↔ S ∈ ℐ(G) ∧ ∀ u ∈ S, ¬G.Adj v u := by
  grind [mem_indepSetFinsetAll_iff, Set.pairwise_insert, adj_comm, SimpleGraph.irrefl]

lemma subset_compl_closedNeighborSet_iff_insert_mem_indepSetFinsetAll {v : V} {I : Set V}
    (hI : I ∈ ℐ(G)) :
    I ⊆ (G.closedNeighborSet v)ᶜ ↔ v ∉ I ∧ insert v I ∈ ℐ(G) := by
  rw [insert_mem_indepSetFinsetAll_iff]
  simp only [hI, true_and, Set.subset_def, closedNeighborSet, Set.mem_compl_iff,
    Set.mem_insert_iff, mem_neighborSet, not_or]
  constructor
  · intro h
    exact ⟨fun hv ↦ (h v hv).1 rfl, fun u hu ↦ (h u hu).2⟩
  · rintro ⟨hv, hI'⟩ u hu
    exact ⟨fun h ↦ hv (h ▸ hu), hI' u hu⟩

omit [Fintype V] in
lemma indepNum_induce_compl_closedNeighborSet_add_one_le [Finite V] (v : V) :
    α(G) ≥ α(G.induce (G.closedNeighborSet v)ᶜ) + 1 := by
  cases nonempty_fintype V
  obtain ⟨I, hI, hI_card⟩ :=
    (G.induce (G.closedNeighborSet v)ᶜ).exists_mem_indepSetFinsetAll_ncard_eq_indepNum
  rw [← hI_card, ge_iff_le]
  have := mem_indepSetFinsetAll_and_subset_of_mem_induce (by convert hI)
  rw [subset_compl_closedNeighborSet_iff_insert_mem_indepSetFinsetAll this.1] at this
  convert ncard_le_indepNum_of_mem_indepSetFinsetAll this.2.2
  rw [Set.ncard_insert_of_notMem this.2.1, Set.ncard_image_of_injective _ Subtype.val_injective]

private lemma card_filter_subset_compl_closedNeighborSet_aux (v : V) :
    #(filter (· ⊆ (G.closedNeighborSet v)ᶜ) ℐ(G)) = #(filter (v ∈ ·) ℐ(G)) := by
  refine card_bij' (fun S _ ↦ insert v S) (fun S _ ↦ S \ {v}) ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_filter] at hS ⊢
    exact ⟨((subset_compl_closedNeighborSet_iff_insert_mem_indepSetFinsetAll hS.1).1 hS.2).2,
      Set.mem_insert v S⟩
  · intro S hS
    rw [mem_filter] at hS ⊢
    have hI : S \ {v} ∈ ℐ(G) := mem_indepSetFinsetAll_of_subset hS.1 Set.sdiff_subset
    exact ⟨hI, (subset_compl_closedNeighborSet_iff_insert_mem_indepSetFinsetAll hI).mpr
      ⟨fun h ↦ h.2 rfl,
        mem_indepSetFinsetAll_of_subset hS.1 (Set.insert_subset hS.2 Set.sdiff_subset)⟩⟩
  · exact fun S hS ↦ Set.insert_sdiff_self_of_notMem
      fun hv ↦ (mem_filter.mp hS).2 hv self_mem_closedNeighborSet
  · exact fun S hS ↦ Set.insert_sdiff_self_of_mem (mem_filter.mp hS).2

/-- The fundamental recursion for counting independent sets: the independent sets avoiding a
vertex `v` are counted by `G.induce {v}ᶜ`, those containing `v` by
`G.induce (G.closedNeighborSet v)ᶜ`. -/
lemma card_indepSetFinsetAll_recursion (v : V) :
    #ℐ(G) = #ℐ(G.induce {v}ᶜ) + #ℐ(G.induce (G.closedNeighborSet v)ᶜ) := by
  simp only [card_indepSetFinsetAll_induce, card_filter_subset_compl_closedNeighborSet_aux,
    Set.subset_compl_singleton_iff]
  exact (card_filter_add_card_filter_not (s := ℐ(G)) (v ∈ ·)).symm.trans (add_comm _ _)

/-- Convex **Jensen's inequality**, `Finset.expect` version. -/
lemma _root_.ConvexOn.map_expect_le {α : Type*} {t : Finset α} (ht : t.Nonempty) {s : Set ℝ}
    {f : ℝ → ℝ} (p : α → ℝ) (hmem : ∀ i ∈ t, p i ∈ s) (hf : ConvexOn ℝ s f) :
    f (𝔼 i ∈ t, p i) ≤ 𝔼 i ∈ t, f (p i) := by
  have hc : (0 : ℝ) < #t := Nat.cast_pos.2 (card_pos.2 ht)
  simp_rw [expect_eq_sum_div_card, sum_div, div_eq_inv_mul, ← smul_eq_mul]
  exact hf.map_sum_le (fun _ _ ↦ inv_nonneg.2 hc.le)
    (by simp [sum_const, nsmul_eq_mul, mul_inv_cancel₀ hc.ne']) hmem

/-- The exponential of an average is at most the average of the exponentials
(Jensen's inequality for `Real.exp`). -/
lemma _root_.Real.exp_expect_le_expect_exp {ι : Type*} {t : Finset ι} (ht : t.Nonempty)
    (g : ι → ℝ) : Real.exp (𝔼 i ∈ t, g i) ≤ 𝔼 i ∈ t, Real.exp (g i) :=
  ConvexOn.map_expect_le ht _ (fun _ _ ↦ Set.mem_univ _) convexOn_exp


variable (G) in
/-- The error functional appearing in the convexity step; vanishes when `V` is empty. -/
noncomputable def shearerError (f f' : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if Nonempty V then a * (d(G) * f' d(G) - f d(G)) + b * (-2 * f' d(G)) else 0

lemma shearerError_of_nonempty {f f' : ℝ → ℝ} {a b : ℝ} (hV : Nonempty V) :
    shearerError G f f' a b = a * (d(G) * f' d(G) - f d(G)) + b * (-2 * f' d(G)) :=
  ite_eq_left hV

lemma shearerError_of_isEmpty {f f' : ℝ → ℝ} {a b : ℝ} (hV : IsEmpty V) :
    shearerError G f f' a b = 0 :=
  ite_eq_right (not_nonempty_iff.2 hV)

lemma shearerError_add_one_sq {f f' : ℝ → ℝ} (hV : Nonempty V) :
    G.shearerError f f' (d(G) + 1) (d(G) ^ 2) =
    (d(G) - d(G) ^ 2) * f' d(G) - (d(G) + 1) * f d(G) :=
  (shearerError_of_nonempty hV).trans (by ring)

lemma shearerError_one {f f' : ℝ → ℝ} (hV : Nonempty V) : G.shearerError f f' 1 d(G) =
    -d(G) * f' d(G) - f d(G) := (shearerError_of_nonempty hV).trans (by ring)


variable (G) in
lemma expect_shearerError {f f' : ℝ → ℝ} {g₁ g₂ : V → ℝ} :
    𝔼 v, shearerError G f f' (g₁ v) (g₂ v) = shearerError G f f' (𝔼 v, g₁ v) (𝔼 v, g₂ v) := by
  obtain hV | hV := isEmpty_or_nonempty V
  · simp [shearerError_of_isEmpty hV]
  · simp [shearerError_of_nonempty hV, expect_add_distrib, ← expect_mul]

lemma shearerError_card_zero_of_averageDegree_eq_zero {f f' : ℝ → ℝ} (S : Set V) (h : d(G) = 0) :
    shearerError G f f' (#S.toFinset) 0 = -(#S.toFinset) * f 0 := by
  obtain hV | hV := isEmpty_or_nonempty V
  · simp [shearerError_of_isEmpty hV]
  · simp [shearerError_of_nonempty hV, h]

lemma shearerError_le_shearerError_of_le {a b c : ℝ} {f f' : ℝ → ℝ} (hf' : ∀ x, 0 < x → f' x ≤ 0)
    (hab : b ≤ c) (hdG : 0 < d(G)) :
    shearerError G f f' a b ≤ shearerError G f f' a c := by
  obtain hV | hV := isEmpty_or_nonempty V
  · simp [shearerError_of_isEmpty hV]
  · simp only [shearerError_of_nonempty hV]
    gcongr
    linarith [hf' d(G) (Rat.cast_pos.mpr hdG)]

/-- The tangent-line convexity inequality: `f` lies on or above every line through `(y, f y)`
with slope `f' y`, for all `x ≥ 0` and `y > 0`. -/
def ConvexIneq (f f' : ℝ → ℝ) : Prop :=
    ∀ x y, 0 ≤ x → 0 < y → f x ≥ f y + f' y * (x - y)

lemma shearer_convex_step {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
    {H₁ : SimpleGraph V₁} {H₂ : SimpleGraph V₂} (f f' : ℝ → ℝ) (hf : ConvexIneq f f')
    (hdH₁ : 0 < d(H₁)) : #V(H₂) * f d(H₂) ≥
    #V(H₁) * f d(H₁) + shearerError H₁ f f' (#V(H₁) - #V(H₂)) (#E(H₁) - #E(H₂)) := by
  have h_ineq := hf d(H₂) d(H₁) (Rat.cast_nonneg.2 averageDegree_nonneg) (Rat.cast_pos.2 hdH₁)
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left h_ineq (Nat.cast_nonneg _))
  rw [shearerError_of_nonempty (nonempty_of_averageDegree_pos hdH₁)]
  have e₁ : (#V(H₁) : ℝ) * d(H₁) = 2 * #E(H₁) := by
    exact_mod_cast card_mul_averageDegree_eq_twice_card_edges
  have e₂ : (#V(H₂) : ℝ) * d(H₂) = 2 * #E(H₂) := by
    exact_mod_cast card_mul_averageDegree_eq_twice_card_edges
  linear_combination f' d(H₁) * e₁ - f' d(H₁) * e₂

lemma convex_step_induce (S : Set V) {f f' : ℝ → ℝ} (hf : ConvexIneq f f')
  : #V(G.induce Sᶜ) * f d(G.induce Sᶜ) ≥ #V(G) * f d(G) +
    shearerError G f f' #S.toFinset #(G.edgeIncidenceFinset S) := by
  by_cases hd : d(G) = 0
  · have hd' : d(induce Sᶜ G) = 0 := by
      convert averageDegree_induce_eq_zero_of_averageDegree_eq_zero hd Sᶜ
    rw [hd, hd', Rat.cast_zero,
      card_edgeIncidenceFinset_eq_zero_of_averageDegree_eq_zero hd, Nat.cast_zero,
      shearerError_card_zero_of_averageDegree_eq_zero _ hd, neg_mul, ge_iff_le,
      add_neg_le_iff_le_add, ← add_mul, ← Nat.cast_add, add_comm, card_vertexFinset_induce,
      card_vertexFinset_eq_card_add_card_compl S]
  · convert shearer_convex_step (H₁ := G) (H₂ := G.induce Sᶜ) f f' hf
      (averageDegree_pos_of_ne_zero hd) <;>
    rw [eq_sub_iff_add_eq, ← Nat.cast_add, Nat.cast_inj]
    · rw [card_vertexFinset_induce]
      exact (card_vertexFinset_eq_card_add_card_compl S).symm
    · exact (card_edgeFinset_eq_card_edgeIncidenceFinset_add_card_induce_compl S).symm

lemma convex_step_expect {F : V → Set V} {f f' : ℝ → ℝ} (hf : ConvexIneq f f')
  : 𝔼 v, #V(G.induce (F v)ᶜ) * f d(G.induce (F v)ᶜ) ≥ #V(G) * f d(G) +
    shearerError G f f' (𝔼 v, #(F v).toFinset) (𝔼 v, #(G.edgeIncidenceFinset (F v))) := by
  refine le_trans (le_of_eq ?_) (expect_le_expect fun v _ ↦ convex_step_induce _ hf)
  rw [expect_add_distrib, expect_shearerError]
  congr 1
  by_cases hV : #V(G) = 0
  · simp [hV]
  · exact (expect_const (card_ne_zero.mp hV) _).symm

lemma convex_step_expect_closedNeighbor {f f' : ℝ → ℝ} (hf : ConvexIneq f f')
    (hT : G.CliqueFree 3) (hf' : ∀ (x : ℝ), 0 < x → f' x ≤ 0)
    : 𝔼 v, #V(G.induce (G.closedNeighborSet v)ᶜ) * f d(G.induce (G.closedNeighborSet v)ᶜ)
    ≥ #V(G) * f d(G) + shearerError G f f' (d(G) + 1) (d(G) ^ 2) := by
  by_cases hV : Nonempty V
  · refine le_trans ?_ (convex_step_expect (F := G.closedNeighborSet) hf)
    gcongr
    rw [expect_card_closedNeighborSet hV, expect_card_edgeIncidenceFinset_closedNeighborSet_real hT,
      ← Rat.cast_pow]
    by_cases hdG : d(G) = 0
    · simp [hdG, degree_eq_zero_of_averageDegree_eq_zero]
    · exact shearerError_le_shearerError_of_le hf'
        (Rat.cast_le.2 sq_averageDegree_le_expect_sq_degree) (averageDegree_pos_of_ne_zero hdG)
  · simp_all [shearerError_of_isEmpty, card_vertexFinset_eq_zero_of_isEmpty]

private lemma Shearer_bound_aux {f f' : ℝ → ℝ} (hf : ConvexIneq f f')
    (hf' : ∀ (x : ℝ), 0 < x → f' x ≤ 0)
    (h_extra : ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'},
      0 ≤ G'.shearerError f f' (d(G') + 1) (d(G') ^ 2) + 1)
    (n : ℕ) (ih : ∀ m, m < n → ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'},
      m = #V(G') → G'.CliqueFree 3 → α(G') ≥ m * f d(G'))
    {V : Type} [Fintype V] {G : SimpleGraph V} (hcard : n = #V(G)) (hT : G.CliqueFree 3) :
    α(G) ≥ n * f d(G) := by
  by_cases hV : Nonempty V
  · rw [← expect_const (univ_nonempty_iff.mpr hV) (α(G) : ℝ)]
    calc
      𝔼 v, (α(G) : ℝ)   ≥ 𝔼 v, ((α(G.induce (G.closedNeighborSet v)ᶜ) + 1 : ℕ) : ℝ) :=
        expect_le_expect fun _ _ ↦
          Nat.cast_le.2 (indepNum_induce_compl_closedNeighborSet_add_one_le _)
      _                 = 𝔼 v, (α(G.induce (G.closedNeighborSet v)ᶜ) + 1 : ℝ) := by simp
      _                 = (𝔼 v, (α(G.induce (G.closedNeighborSet v)ᶜ) : ℝ)) + 1 := by
        rw [expect_add_distrib, expect_const (univ_nonempty_iff.mpr hV) _]
      _                 ≥ (𝔼 v, #V(G.induce (G.closedNeighborSet v)ᶜ) *
                          f d(G.induce (G.closedNeighborSet v)ᶜ)) + 1 := by
        gcongr
        apply ih
        · rw [hcard]
          exact card_vertexFinset_induce_compl_lt closedNeighborSet_nonempty
        · rfl
        · exact CliqueFree.comap ⟨Copy.induce G _⟩ hT
      _                 ≥ #V(G) * f d(G) + shearerError G f f' (d(G) + 1) (d(G) ^ 2) + 1 := by
        gcongr
        exact convex_step_expect_closedNeighbor hf hT hf'
      _                 ≥ #V(G) * f d(G) + 0  := by
        rw [add_assoc]
        gcongr
        exact h_extra
      _                 = #V(G) * f d(G)      := add_zero _
    rw [hcard]
  · rw [card_vertexFinset_eq_zero_of_isEmpty (not_nonempty_iff.mp hV)] at hcard
    simp [hcard]

/-- **Shearer's independence-number bound.** For a triangle-free graph `G` and any `f`
satisfying the convexity inequality `ConvexIneq f f'` with `f'` nonpositive on the
positives and `h_extra` (the Shearer error plus one is nonnegative for every finite graph),
`α(G) ≥ #V(G) * f d(G)`. -/
theorem Shearer_bound (hT : G.CliqueFree 3) {f f' : ℝ → ℝ} (hf : ConvexIneq f f')
    (hf' : ∀ (x : ℝ), 0 < x → f' x ≤ 0)
    (h_extra : ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'},
      0 ≤ G'.shearerError f f' (d(G') + 1) (d(G') ^ 2) + 1)
    : α(G) ≥ #V(G) * f d(G) := by
  suffices h : ∀ n, ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'} (hn : n = #V(G'))
    (hT : G'.CliqueFree 3), α(G') ≥ n * (f d(G')) from (h _ rfl hT)
  intro n
  induction n using Nat.strong_induction_on with | _ n hn =>
  intro V _ G hcard hT
  exact Shearer_bound_aux hf hf' h_extra n hn hcard hT


lemma convex_step_expect_vertex_complement {f f' : ℝ → ℝ} (hf : ConvexIneq f f')
    : 𝔼 v, #V(G.induce {v}ᶜ) * f d(G.induce {v}ᶜ)
    ≥ #V(G) * f d(G) + shearerError G f f' 1 d(G) := by
  by_cases hV : Nonempty V
  · convert convex_step_expect (F := fun v ↦ {v}) hf
    · simp
    · simp [card_edgeIncidenceFinset_singleton, cast_averageDegree]
  · simp_all [card_vertexFinset_eq_zero_of_isEmpty, shearerError_of_isEmpty]

/-- The inductive step for `independent_set_count_bound`: if the exponential lower bound holds
for every graph with strictly fewer vertices than `G`, then it holds for `G` itself. -/
private lemma independent_set_count_bound_step {f f' : ℝ → ℝ} {n : ℕ}
    (hn : ∀ m, m < n → ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'},
      m = #V(G') → G'.CliqueFree 3 → #ℐ(G') ≥ Real.exp (#V(G') * f d(G')))
    (hcard : n = #V(G)) (hT : G.CliqueFree 3) (hf : ConvexIneq f f')
    (hf' : ∀ (x : ℝ), 0 < x → f' x ≤ 0)
    (h_extra : ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'},
      1 ≤ Real.exp (G'.shearerError f f' 1 d(G')) +
        Real.exp (G'.shearerError f f' (d(G') + 1) (d(G') ^ 2)))
    : #ℐ(G) ≥ Real.exp (#V(G) * f d(G)) := by
  by_cases hV : Nonempty V
  · rw [← expect_const (univ_nonempty_iff.mpr hV) (#ℐ(G) : ℝ)]
    have key (S : Set V) (hS : S.Nonempty) :
        (#ℐ(G.induce Sᶜ) : ℝ) ≥ Real.exp (#V(G.induce Sᶜ) * f d(G.induce Sᶜ)) := by
      apply hn (#V(G.induce Sᶜ))
      · rw [hcard]
        exact card_vertexFinset_induce_compl_lt hS
      · rfl
      · exact CliqueFree.comap ⟨Copy.induce G _⟩ hT
    calc
      𝔼 v, (#ℐ(G) : ℝ)
            = 𝔼 v, (#ℐ(G.induce {v}ᶜ) + #ℐ(G.induce (G.closedNeighborSet v)ᶜ) : ℝ ) := by
        apply expect_congr rfl
        exact_mod_cast fun _ _ ↦ card_indepSetFinsetAll_recursion _
      _   =   𝔼 v, (#ℐ(G.induce {v}ᶜ) : ℝ)
            + 𝔼 v, (#ℐ(G.induce (G.closedNeighborSet v)ᶜ) : ℝ )  := expect_add_distrib _ _ _
      _   ≥   𝔼 v, Real.exp (#V(G.induce {v}ᶜ) * f d(G.induce {v}ᶜ))
            + 𝔼 v, Real.exp (#V(G.induce (G.closedNeighborSet v)ᶜ)
                              * f d(G.induce (G.closedNeighborSet v)ᶜ)) := by
        gcongr <;> apply key
        · exact Set.singleton_nonempty _
        · exact closedNeighborSet_nonempty
      _   ≥   Real.exp (𝔼 v, #V(G.induce {v}ᶜ) * f d(G.induce {v}ᶜ))
            + Real.exp (𝔼 v, #V(G.induce (G.closedNeighborSet v)ᶜ)
                              * f d(G.induce (G.closedNeighborSet v)ᶜ)) := by
        gcongr <;> exact Real.exp_expect_le_expect_exp (univ_nonempty_iff.2 hV) _
      _   ≥   Real.exp (#V(G) * f d(G) + shearerError G f f' 1 d(G))
            + Real.exp (#V(G) * f d(G) + shearerError G f f' (d(G) + 1) (d(G) ^ 2)) := by
        gcongr
        · exact convex_step_expect_vertex_complement hf
        · exact convex_step_expect_closedNeighbor hf hT hf'
      _   = Real.exp (#V(G) * f d(G)) *
            (Real.exp (shearerError G f f' 1 d(G)) +
              Real.exp (shearerError G f f' (d(G) + 1) (d(G) ^ 2))) := by
        rw [Real.exp_add, Real.exp_add, mul_add]
      _                 ≥ Real.exp (#V(G) * f d(G)) := by
        nth_rewrite 2 [← mul_one (a := Real.exp (↑(#V(G)) * f ↑d(G)))]
        gcongr
        exact h_extra
  · simp [card_vertexFinset_eq_zero_of_isEmpty (not_nonempty_iff.mp hV), indepSetFinsetAll_nonempty]

/-- The number of independent sets of a triangle-free graph `G` is at least
`exp (#V(G) * f d(G))` when `f` satisfies `ConvexIneq f f'`, `f'` is nonpositive on the
positives, and `h_extra` holds: the two exponentiated Shearer errors sum to at least one
for every finite graph. -/
theorem independent_set_count_bound (hT : G.CliqueFree 3) {f f' : ℝ → ℝ}
    (hf : ConvexIneq f f')
    (hf' : ∀ (x : ℝ), 0 < x → f' x ≤ 0)
    (h_extra : ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'},
      1 ≤
        Real.exp (G'.shearerError f f' 1 d(G')) +
        Real.exp (G'.shearerError f f' (d(G') + 1) (d(G') ^ 2)))
    : #ℐ(G) ≥ Real.exp (#V(G) * f d(G)) := by
  suffices h : ∀ n, ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'} (hn : n = #V(G'))
    (hT : G'.CliqueFree 3), #ℐ(G') ≥ Real.exp (#V(G') * f d(G')) from (h _ rfl hT)
  intro n
  induction n using Nat.strong_induction_on with | _ n hn =>
  intro V _ G hcard hT
  exact independent_set_count_bound_step hn hcard hT hf hf' h_extra


end SimpleGraph
