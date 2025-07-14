/-
Copyright (c) 2024 Pjotr Buys. All rights reserved.
Authors: Pjotr Buys
-/

import Mathlib
import ShearerTriangleFreeInd.Analysis

/-!
# The Independence Number of Triangle-Free Graphs

This file proves Shearer's theorem on the independence number of triangle-free graphs.

We prove that if `G` is a triangle-free graph on `n` vertices with average degree `d`,
then its independence number `α` satisfies `α ≥ n · F(d)` where `F` is the Shearer function
defined by `F(x) = (x ln x - x + 1) / (x - 1)²` for `x ≠ 1` and `F(1) = 1/2`.

In this file the theorem is called `triangle_free_independence_bound`.

## Main definitions

* `closedNeighborSet G v` : The closed neighborhood of `V`.
* `puncture G v`: The induced subgraph obtained by removing the closed neighborhood of `v`,
    this is a graph with vertex type the subtype `(G.closedNeighborSet v)ᶜ` of `V`.
* `averageDegree G`: The average degree of vertices in graph `G`, defined as type `ℚ`.

## Implementation notes

The proof follows the proof of Theorem 1 given in [shearer1983]. The most challenging
part was proving the convexity of `F`. This is done in the companion file `Analysis`.

## References

* [J. B. Shearer, *A note on the independence number of triangle-free graphs*,
  Discrete Mathematics 46 (1983) 83-87][shearer1983]
-/


open Finset SimpleGraph
open Classical
open BigOperators


namespace SimpleGraph

variable {V : Type}

/-!
### Definition of puncture
-/

/-- The closed neighborhood of a vertex consists of the vertex and its neighbors. -/
def closedNeighborSet (G : SimpleGraph V) (v : V) := insert v (G.neighborSet v)

/-- The exterior of v is the set of vertices outside v's closed neighborhood. -/
def exterior (G : SimpleGraph V) (v : V) := (G.closedNeighborSet v)ᶜ

/-- The puncture of G at v is the induced subgraph on vertices outside v's closed neighborhood. -/
def puncture (G : SimpleGraph V) (v : V) := G.induce (G.exterior v)

/-!
  ## For coercions.
-/

def φ {G : SimpleGraph V} {v : V} : G.exterior v ↪ V  := Function.Embedding.subtype _
def φG {G : SimpleGraph V} {v : V} : G.puncture v ↪g G := Embedding.induce _

lemma finset_coe_subtype {G : SimpleGraph V} {v : V} (S : Finset (G.exterior v)) :
    (S.map φ : Set V)  = Subtype.val '' (S : Set (G.exterior v)) := coe_map _ _

/-!
## Basic lemmas about G.puncture v without assuming finiteness of V
-/

variable {G : SimpleGraph V} {v : V}

lemma mem_closedNeighborSet_self : v ∈ G.closedNeighborSet v := Set.mem_insert _ _

lemma not_mem_exterior_self : v ∉ G.exterior v := fun hvw ↦ hvw mem_closedNeighborSet_self

lemma adj_mem_closedNeighborSet {w : V} (hw : G.Adj v w) : w ∈ G.closedNeighborSet v :=
  Set.mem_insert_of_mem _ hw

lemma not_adj_of_mem_exterior {w : V} (hw : w ∈ G.exterior v) : ¬ G.Adj v w :=
  fun hvw ↦ hw (adj_mem_closedNeighborSet hvw)

lemma not_mem_image_edge_of_neighbor (e : Sym2 (G.exterior v)) :
    ∀ u, u ∈ G.neighborSet v → u ∉ (φ.sym2Map e) := by
  intro _ hu hue
  have ⟨u, _, hueq⟩ := Sym2.mem_map.1 hue
  exact not_adj_of_mem_exterior (by rw [←hueq]; exact Subtype.coe_prop u) hu

lemma mem_exterior_of_mem_edge_disjoint_neighbors {e : Sym2 V} (he : e ∈ G.edgeSet)
    (hu_not : ∀ u, u ∈ G.neighborSet v → u ∉ e) : ∀ u ∈ e, u ∈ G.exterior v := by
  intro u hue hu_clnbrv
  rcases Set.mem_insert_iff.1 hu_clnbrv with huv | hu_nbrv
  · rw [huv] at hue
    exact hu_not (Sym2.Mem.other hue) ((mem_incidence_iff_neighbor _).1
      ⟨by rwa [Sym2.other_spec hue], Sym2.mem_mk_left v _⟩) (Sym2.other_mem hue)
  · exact (hu_not _ hu_nbrv) hue

lemma exists_preimage_of_edge_disjoint_neighbors {e : Sym2 V}
    (he : e ∈ G.edgeSet) (hu_not : ∀ u, u ∈ G.neighborSet v → u ∉ e)
    : ∃ e' ∈ (G.puncture v).edgeSet, (φ.sym2Map e') = e := by
  have he_eq : φ.sym2Map (e.attachWith (mem_exterior_of_mem_edge_disjoint_neighbors he hu_not)) = e
    := Sym2.attachWith_map_subtypeVal _
  rw [←he_eq] at he
  exact ⟨_, ⟨(Embedding.map_mem_edgeSet_iff φG).mp he, he_eq⟩⟩

variable (G) (v) in
lemma puncture_edgeSet_image_eq : φ.sym2Map '' (G.puncture v).edgeSet =
    G.edgeSet \ ⋃ u ∈ (G.neighborSet v), (G.incidenceSet u) := by
  ext e
  rw [Set.mem_diff, Set.mem_iUnion]
  constructor
  · intro ⟨_, he', he_eq⟩
    rw [←he_eq]
    exact ⟨(Embedding.map_mem_edgeSet_iff φG).mpr he',
      fun ⟨_, _, ⟨huv, ht⟩, hue⟩ ↦
        (by rw [←ht] at hue; exact not_mem_image_edge_of_neighbor _ _ huv hue.2)⟩
  · exact fun ⟨he, he_not⟩ ↦ (Set.mem_image _ _ _).2
      (exists_preimage_of_edge_disjoint_neighbors he
      fun u hu hue ↦ he_not ⟨u, Set.mem_iUnion.2 ⟨hu, ⟨he, hue⟩⟩⟩)

/-!
## Two general lemmas
-/

lemma neighborSet_pairwiseDisjoint_incidenceSet (hT : G.CliqueFree 3) :
    (G.neighborSet v).PairwiseDisjoint (fun u ↦ G.incidenceSet u) := by
  rw [Set.pairwiseDisjoint_iff]
  intro u hu w hw ⟨e, ⟨heu, hew⟩⟩
  by_contra huw
  exact isIndepSet_neighborSet_of_triangleFree _ hT _ hu hw huw
    (adj_of_mem_incidenceSet _ huw heu hew)

/-The independent set version of `isClique_insert`.-/
lemma isIndepSet_insert {T : Set V}
    : G.IsIndepSet (insert v T) ↔ G.IsIndepSet T ∧ ∀ u ∈ T, v ≠ u → ¬G.Adj v u := by
  simp_all [←isClique_compl, ←isClique_compl , isClique_insert]


/-!
## Now we assume that V has Fintype. Lemmas about closedNeighborFinset.
-/

variable [Fintype V]

noncomputable instance fintype_puncture : Fintype (G.exterior v) := Fintype.ofFinite _

variable (G) (v) in
noncomputable def closedNeighborFinset := insert v (G.neighborFinset v)

lemma closedNeighborFinset_coe : closedNeighborFinset G v = G.closedNeighborSet v := by
  simp [closedNeighborFinset, closedNeighborSet, neighborFinset_def]

lemma closedNeighborSet_toFinset : (G.closedNeighborSet v).toFinset = closedNeighborFinset G v := by
  rw [←closedNeighborFinset_coe, toFinset_coe]

lemma puncture_verts_toFinset : (G.exterior v).toFinset = univ \ G.closedNeighborFinset v := by
  simp only [exterior, Set.toFinset_compl, closedNeighborSet_toFinset, compl_eq_univ_sdiff]

lemma closedNeighborFinset_card : #(G.closedNeighborFinset v) = G.degree v + 1 :=
  card_insert_of_notMem (notMem_neighborFinset_self _ _)

lemma V_card_ge_deg_plus_one : Fintype.card V ≥ G.degree v + 1 := by
  rw [←closedNeighborFinset_card]
  exact card_le_univ _

lemma puncture_verts_card : Fintype.card (G.exterior v) = Fintype.card V - (G.degree v + 1) := by
  rw [←Set.toFinset_card, puncture_verts_toFinset, card_univ_diff, closedNeighborFinset_card]

lemma puncture_verts_card_rat :
  (Fintype.card (G.exterior v) : ℚ) = Fintype.card V - (G.degree v + 1) := by
  rw [puncture_verts_card (G := G) (v := v), Nat.cast_sub V_card_ge_deg_plus_one,
  Nat.cast_add, Nat.cast_one]

lemma puncture_verts_card_lt : Fintype.card (G.exterior v) < Fintype.card V := by
  rw [puncture_verts_card, tsub_lt_self_iff, Fintype.card_pos_iff, add_pos_iff]
  exact ⟨Nonempty.intro v, Or.inr Nat.one_pos⟩

lemma V_empty_edgeFinset_card_zero (hV : IsEmpty V) : #G.edgeFinset = 0 := by
  simp only [Set.toFinset_card, Fintype.card_eq_zero]

variable (G) (v) in
theorem alpha_in_rel : (puncture G v).indepNum + 1 ≤ G.indepNum:= by
  have ⟨S,hS⟩ := exists_isNIndepSet_indepNum (G := (puncture G v))
  have hS_coe : (S.map φ : Set V) ⊆ G.exterior v := map_subtype_subset _
  convert IsIndepSet.card_le_indepNum (t := insert v (S.map φ)) ?_
  · rw [←hS.2, card_insert_of_notMem (fun h ↦ not_mem_exterior_self (hS_coe h)), card_map]
  · rw [coe_insert, isIndepSet_insert]
    refine ⟨?_, (fun _ hu _  ↦ (not_adj_of_mem_exterior (hS_coe hu)))⟩
    have this := hS.1
    rwa [puncture, induce_eq_coe_induce_top, isIndepSet_induce, ←finset_coe_subtype] at this




/-!
### The average degree of G.
-/

variable (G) in
/-- The average degree of vertices in a finite graph. -/
noncomputable def averageDegree := 𝔼 v, (G.degree v : ℚ)

lemma averageDegree_nonneg : 0 ≤ averageDegree G := expect_nonneg (fun _ _ ↦ Nat.cast_nonneg' _)

lemma averageDegree_eq_twice_card_edges_div_card :
  (averageDegree G) = 2 * #G.edgeFinset / (Fintype.card V : ℚ) := by
  convert Fintype.expect_eq_sum_div_card (fun v ↦ (G.degree v : ℚ))
  convert congrArg (Nat.cast (R := ℚ)) (sum_degrees_eq_twice_card_edges G).symm using 1 <;> simp

lemma card_mul_averageDegree_eq_twice_card_edges :
    Fintype.card V  * (averageDegree G) = 2 * #G.edgeFinset := by
  rw [averageDegree_eq_twice_card_edges_div_card]
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
  · simp [h, filter_eq_empty_iff]
    rw [Fintype.card_eq_zero_iff, isEmpty_iff] at h
    exact fun x _ ↦ h (x.out).1
  · field_simp

@[simp]
lemma neighborFinset_coe : (G.neighborFinset v : Set V) = G.neighborSet v := by ext _; simp
@[simp]
lemma incidenceFinset_coe : (G.incidenceFinset v : Set (Sym2 V)) = G.incidenceSet v :=
  by ext _; simp

lemma triangleFree_neighbors_disjoint_incidenceFinset (hT : G.CliqueFree 3) :
    (G.neighborSet v).PairwiseDisjoint (fun u ↦ G.incidenceFinset u) := by
  have this := neighborSet_pairwiseDisjoint_incidenceSet (v := v) hT
  rw [Set.pairwiseDisjoint_iff, pairwiseDisjoint_iff] at *
  exact fun u hu w hw ⟨e, he⟩ ↦
    (this hu hw ⟨e, by rwa [mem_inter, mem_incidenceFinset, mem_incidenceFinset] at he⟩)

variable (G) (v) in
lemma puncture_edgeFinset_map_eq : map φ.sym2Map (G.puncture v).edgeFinset =
    G.edgeFinset \ Finset.biUnion (G.neighborFinset v) (fun u ↦ (G.incidenceFinset u)) := by
  rw [←coe_inj]; convert puncture_edgeSet_image_eq G v <;> simp

lemma neighborhood_incidenceFinset_sub :
    Finset.biUnion (G.neighborFinset v) (fun u ↦ (G.incidenceFinset u)) ⊆ G.edgeFinset := by
  intro _ he
  have ⟨_,_,h⟩ := mem_biUnion.1 he
  exact (incidenceFinset_subset _ _ h)

lemma puncture_edge_card (hT : G.CliqueFree 3) : (#(G.puncture v).edgeFinset : ℚ)
    = #G.edgeFinset - ∑ u ∈ G.neighborFinset v, (G.degree u : ℚ) := by
  convert congrArg (Nat.cast (R := ℚ)) (congrArg card (puncture_edgeFinset_map_eq G v))
  · exact (card_map _).symm
  · rw [card_sdiff neighborhood_incidenceFinset_sub,
      Nat.cast_sub (card_le_card neighborhood_incidenceFinset_sub), ←Nat.cast_sum, card_biUnion ?_]
    · simp
    · rw [neighborFinset_coe]
      exact triangleFree_neighbors_disjoint_incidenceFinset hT

lemma expect_sum_degree_neighbors :
    𝔼 v, ∑ u ∈ G.neighborFinset v, (G.degree u : ℚ) = 𝔼 v, (G.degree v : ℚ)^2 := by
  conv => lhs; rhs; intro v ; rw [←(Fintype.sum_ite_mem _ _)]
  simp_rw [expect_sum_comm]
  conv => lhs; rhs; intro u; rhs; intro i; rw [←mul_boole]
  conv => lhs; rhs; intro u; rw [←mul_expect, expect, sum_boole, mul_smul_comm]
  rw [expect, smul_sum]
  congr; ext _; rw [pow_two]; congr 4
  ext _; simp only [mem_neighborFinset, adj_comm, mem_filter, mem_univ, true_and]

lemma expect_puncture_edgeFinset_card (hT : G.CliqueFree 3)
    : (𝔼 v, #(G.puncture v).edgeFinset : ℚ) = #G.edgeFinset - (𝔼 v, (G.degree v : ℚ)^2):= by
  simp_rw [puncture_edge_card hT, expect_sub_distrib, expect_sum_degree_neighbors]
  congr
  by_cases hV : Nonempty V
  · exact expect_const (univ_nonempty_iff.mpr hV) _
  · rw [not_nonempty_iff] at hV
    simp

lemma expect_puncture_edgeFinset_card_real (hT : G.CliqueFree 3)
    : (𝔼 v, #(G.puncture v).edgeFinset : ℝ) = #G.edgeFinset - (𝔼 v, (G.degree v : ℝ)^2):= by
  convert congrArg (Rat.cast (K := ℝ)) (expect_puncture_edgeFinset_card hT)
  · exact (algebraMap.coe_expect univ (fun v ↦ (#(G.puncture v).edgeFinset : ℚ))).symm
  · have this := (algebraMap.coe_expect univ (M := ℚ) (N := ℝ) (fun v ↦ (G.degree v : ℚ)^2)).symm
    simp_all

lemma edge_card_zero_iff_average_degree_zero : #G.edgeFinset = 0 ↔ G.averageDegree = 0 := by
  rw [←Rat.natCast_inj, ←(mul_right_inj_of_invertible 2),
    ←card_mul_averageDegree_eq_twice_card_edges, (by rfl: (0: ℕ) = (0 : ℚ)),
    mul_zero, mul_eq_zero, or_iff_right_iff_imp]
  intro hV
  apply expect_eq_zero
  intro i hi
  rw [Rat.natCast_eq_zero, Fintype.card_eq_zero_iff] at hV
  exact False.elim (IsEmpty.false i)

lemma degree_eq_zero_of_averageDegree_eq_zero (h : G.averageDegree = 0) :
    ∀ v, G.degree v = 0 := fun v ↦ Rat.natCast_eq_zero.mp
  ((expect_eq_zero_iff_of_nonneg ⟨v, mem_univ _⟩ (fun _ _ ↦ Nat.cast_nonneg' _)).1 h v (mem_univ _))

lemma averageDegree_puncture_eq_zero_of_averageDegree_eq_zero (h : G.averageDegree = 0) :
    (G.puncture v).averageDegree = 0 := by
  rw [←edge_card_zero_iff_average_degree_zero] at *
  have map_eq := puncture_edgeFinset_map_eq G v
  rw [card_eq_zero] at h
  rwa [h, empty_sdiff, map_eq_empty, ←card_eq_zero] at map_eq

lemma averageDegree_square_bound : G.averageDegree ^ 2 ≤ 𝔼 v, (G.degree v : ℚ)^2 := by
  convert expect_mul_sq_le_sq_mul_sq (f := fun v ↦ (G.degree v : ℚ)) (g := fun _ ↦ 1) univ
  · simp only [averageDegree, mul_one]
  · by_cases h_nonempty : Nonempty V
    · rw [expect_const (univ_nonempty_iff.2 h_nonempty), one_pow, mul_one]
    · simp_all


/-!
### Proof of the main statement
-/

lemma exists_ge_of_le_expect {a : ℝ} {g : V → ℝ} (h_nonempty : Nonempty V) (h : a ≤ 𝔼 i, g i)
  : ∃ x, a ≤ g x := by
  have ⟨x, _, h_all⟩ := exists_max_image (s := univ) (f := g) (univ_nonempty_iff.mpr h_nonempty)
  exact ⟨x, le_trans h (expect_le (univ_nonempty_iff.mpr h_nonempty) h_all)⟩


lemma exists_good_vertex (h_nonempty : Nonempty V) (hT : CliqueFree G 3) :
    ∃ v, (Fintype.card V) * (F G.averageDegree)
    ≤ 1 + (Fintype.card V - (G.degree v + 1)) * (F (G.puncture v).averageDegree) := by
  by_cases hd₀ : G.averageDegree = 0
  · have ⟨v⟩ := h_nonempty
    use v
    rw [averageDegree_puncture_eq_zero_of_averageDegree_eq_zero hd₀, hd₀, Rat.cast_zero, F_at_zero,
    degree_eq_zero_of_averageDegree_eq_zero hd₀]
    simp only [mul_one, CharP.cast_eq_zero, zero_add, add_sub_cancel, le_refl]
  · have hd_pos : 0 < (G.averageDegree : ℝ) :=
      Rat.cast_pos_of_pos (lt_of_le_of_ne averageDegree_nonneg (by rwa [ne_eq, eq_comm]))
    have cast_rw : (𝔼 i, (G.degree i : ℝ)) = G.averageDegree :=
      (algebraMap.coe_expect _ (M := ℚ) _).symm
    set n := (Fintype.card V : ℝ) with ←hn; set d := (G.averageDegree : ℝ) with ←hd
    apply exists_ge_of_le_expect h_nonempty
    refine le_trans ?_
      (expect_le_expect (f := fun v ↦ 1 + (n - (G.degree v + 1)) *
      (F d + F' d * ((G.puncture v).averageDegree - d))) ?_)
    · rw [←sub_nonneg]
      suffices h : 0 ≤ 1 - F d * (d + 1) + F' d * (d^2 + d - n * d) +
          F' d * 𝔼 i, ((n - ((G.degree i) + 1)) * (G.puncture i).averageDegree) by
        convert h using 1
        rw [←sub_eq_zero]
        simp only [mul_add, add_mul, sub_mul,  expect_sub_distrib, expect_add_distrib,
        expect_const (univ_nonempty_iff.2 h_nonempty), ←expect_mul, ←mul_expect,
        mul_comm (b := F' d), ←mul_assoc (b := F' d), cast_rw, mul_sub, sub_mul]
        ring_nf; simp_rw [mul_assoc, ←mul_expect]; ring
      have h_rw : ∀ v, (n - (↑(G.degree v) + 1)) * ↑(G.puncture v).averageDegree
        = 2 * #(G.puncture v).edgeFinset := by
        intro v
        rw [(by simp : 2 * (#((G.puncture v).edgeFinset) : ℝ)
          = (2 * #((G.puncture v).edgeFinset) : ℚ)),
          ←card_mul_averageDegree_eq_twice_card_edges, puncture_verts_card_rat]
        simp_all
      conv => rhs; rhs; rhs; rhs; intro v; rw [h_rw]
      rw [←mul_expect, expect_puncture_edgeFinset_card_real hT, mul_sub, mul_sub,
        (by simp : 2 * (#(G.edgeFinset) : ℝ) = (2 * #(G.edgeFinset) : ℚ)),
        ←card_mul_averageDegree_eq_twice_card_edges, ←@F_diff_equation d, ←sub_nonneg, Rat.cast_mul,
        Rat.cast_natCast, hn, hd]
      ring_nf; rw [sub_nonneg, mul_comm (a := F' d)]; gcongr ?_ * 2
      refine mul_le_mul_of_nonpos_right ?_ (F'_nonpositive hd_pos)
      convert (Mathlib.Tactic.Rify.ratCast_le _ _).mp (averageDegree_square_bound (G := G))
      · simp [hd]
      · have := (algebraMap.coe_expect univ (M := ℚ) (N := ℝ) (fun v ↦ (G.degree v : ℚ)^2)).symm
        simp_all
    · intro v _
      rw [add_le_add_iff_left]
      apply mul_le_mul_of_nonneg_left
      · exact F_convex_inequality (Rat.cast_nonneg.mpr averageDegree_nonneg) hd_pos
      · convert sub_nonneg.2 (Nat.cast_le (α := ℝ).2 (V_card_ge_deg_plus_one (G := G) (v := v)))
        rw [Nat.cast_add, Nat.cast_one]

/-- **Shearer's Theorem** [shearer1983]: The independence number of a triangle-free graph on
n vertices with average degree d is at least n · F(d) where F is the Shearer function. -/
theorem triangle_free_independence_bound (hT : G.CliqueFree 3)
    : G.indepNum ≥ (Fintype.card V) * (F G.averageDegree) := by
  suffices h : ∀ n, (∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'} (hn : n = Fintype.card V')
    (hT : G'.CliqueFree 3), G'.indepNum ≥ n * (F G'.averageDegree)) from (h _ rfl hT)
  intro n
  induction' n using Nat.strong_induction_on with n hn
  intro V _ G hcard hT
  by_cases hV : Nonempty V
  · have ⟨v, hv⟩ := exists_good_vertex hV hT
    rw [←hcard] at hv
    refine ge_trans (ge_trans (Nat.cast_le.mpr (alpha_in_rel G v)) ?_) hv
    specialize hn _ (by convert puncture_verts_card_lt (G := G) (v := v)) rfl
      (CliqueFree.comap φG hT)
    rw [puncture_verts_card, ←hcard, ge_iff_le, ←(add_le_add_iff_right (a :=1))] at hn
    convert hn using 1
    · rw [←sub_eq_zero]
      simp only [hcard, Nat.cast_sub V_card_ge_deg_plus_one, Nat.cast_add, Nat.cast_one]
      ring
    · simp
  · simp_all

end SimpleGraph
