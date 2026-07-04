import Mathlib
import ShearerTriangleFreeInd.Analysis
import ShearerTriangleFreeInd.Analysis_W

namespace SimpleGraph

open Finset SimpleGraph BigOperators
attribute [local instance] Classical.propDecidable

variable {V : Type} {G : SimpleGraph V} {v : V}
variable [Fintype V]


def VertexFinset (_G : SimpleGraph V) : Finset V := univ
noncomputable def averageDegree {V : Type} [Fintype V] (G : SimpleGraph V) := 𝔼 v, (G.degree v : ℚ)
noncomputable def indepSetFinsetAll (G : SimpleGraph V) : Finset (Set V) := {s | G.IsIndepSet s}

scoped notation "V(" G ")" => VertexFinset G
scoped notation "E(" G ")" => edgeFinset G
scoped notation "d(" G ")" => averageDegree G
scoped notation "α(" G ")" => indepNum G
scoped notation "ℐ(" G ")" => indepSetFinsetAll G

lemma VG_rw : V(G) = univ := rfl
lemma VG_Fintype : #V(G) = Fintype.card V := rfl

lemma d_rw : d(G) = 𝔼 v, (G.degree v : ℚ) := rfl

lemma I_rw {S : Set V} : S ∈ ℐ(G) ↔ G.IsIndepSet S := by
  simp only [indepSetFinsetAll, mem_filter, mem_univ, true_and]


/-
  ## Lemmas about averageDegree
-/

lemma averageDegree_nonneg : 0 ≤ d(G) :=
  expect_nonneg (fun _ _ ↦ Nat.cast_nonneg' _)

lemma averageDegree_pos_from_nonzero (hd : d(G) ≠ 0) : 0 < d(G) :=
  lt_of_le_of_ne averageDegree_nonneg hd.symm

lemma averageDegree_eq_twice_card_edges_div_card : #V(G) * d(G) = 2 * #E(G) := by
  convert congrArg (Nat.cast (R := ℚ)) (sum_degrees_eq_twice_card_edges G) using 1
  · by_cases hV : Nonempty V
    · rw [d_rw, Fintype.expect_eq_sum_div_card, VG_Fintype, (Nat.cast_sum univ _)]
      exact mul_div_cancel₀ _ (by simp)
    · simp_all [VG_rw]
  · rw [Nat.cast_mul, Nat.cast_ofNat]

lemma edgeFinset_empty_from_averageDegree_zero (hd : d(G) = 0) : E(G) = ∅ := by
  rw [←card_eq_zero, ←Rat.natCast_eq_zero_iff, ←mul_eq_zero_iff_left (a := 2) (by norm_num),
      ←averageDegree_eq_twice_card_edges_div_card, hd, mul_zero]


lemma averageDegree_zero_from_vertexType_empty (hV : IsEmpty V) : d(G) = 0 := by
  simp only [averageDegree, univ_eq_empty, expect_empty]

lemma vertexType_Nonempty_from_averageDegree_pos (h : 0 < d(G)) : Nonempty V  := by
  by_contra hV
  rw [not_nonempty_iff] at hV
  linarith [averageDegree_zero_from_vertexType_empty (G := G) hV]


lemma edgeFinset_empty_iff_averageDegree_zero : E(G) = ∅ ↔ d(G) = 0 := by
  constructor
  · intro hE
    have this : #V(G) * d(G) = 0 := by
      simp [averageDegree_eq_twice_card_edges_div_card, card_eq_zero.mpr hE]
    rcases mul_eq_zero.1 this with (h | h)
    · refine averageDegree_zero_from_vertexType_empty (Fintype.card_eq_zero_iff.mp ?_ )
      exact_mod_cast h
    · exact h
  · exact edgeFinset_empty_from_averageDegree_zero


lemma averageDegree_real_cast : (d(G) : ℝ) = 𝔼 v, (G.degree v : ℝ) :=
    algebraMap.coe_expect (M := ℚ) _ _

/-
  ## Closed neighborhood of vertex
-/

omit [Fintype V] in
variable (G) (v) in
def closedNeighborSet := insert v (G.neighborSet v)

omit [Fintype V] in
lemma self_mem_closedNeighborSet : v ∈ G.closedNeighborSet v :=
  Set.mem_insert v (G.neighborSet v)

omit [Fintype V] in
lemma nonempty_closedNeighborSet : (G.closedNeighborSet v).Nonempty :=
    ⟨_, self_mem_closedNeighborSet⟩

omit [Fintype V] in
lemma Adj_of_mem_closedNeighborSet_of_ne_v {u v : V} (hne : v ≠ u)
    (hu : u ∈ G.closedNeighborSet v)
     : G.Adj v u := by
  rcases (Set.mem_insert_iff.1 hu) with (hu | hu)
  · exact (hne hu.symm).elim
  · exact hu

/-
  ## Lemmas induced graph vertex counts
-/

lemma induce_vertex_card (S : Set V) [DecidablePred (· ∈ S)]
    : #V(G.induce S) = #S.toFinset := by simp [VG_rw]

lemma vertex_card_induce_sum (S : Set V) : #V(G) = #S.toFinset + #Sᶜ.toFinset := by
  convert (card_filter_add_card_filter_not (· ∈ S)).symm <;>
    (ext _; simp [VG_rw])

lemma induce_vertex_card_compl_lt {S : Set V} (hS : S.Nonempty) : #V(G.induce Sᶜ) < #V(G) := by
  rw [induce_vertex_card, VG_rw]
  refine card_lt_card ⟨fun _ _ ↦ mem_univ _, sdiff_nonempty.mp ?_⟩
  convert Set.Aesop.toFinset_nonempty_of_nonempty hS
  rw [Set.toFinset_compl, sdiff_compl, inf_of_le_right (le_iff_subset.2 (subset_univ _))]

lemma card_vertices_eq_zero_from_empty (hV : IsEmpty V) : #V(G) = 0 :=
  card_eq_zero.2 (univ_eq_empty_iff.2 hV)

omit [Fintype V] in
lemma vertex_singelton_card [Finite V] (v : V) : #(V(G.induce {v})) = 1 := by
  cases nonempty_fintype V
  convert induce_vertex_card {v}
  rw [Set.toFinset_singleton, card_singleton]

lemma closedNeighbor_card (v : V) : #(G.closedNeighborSet v).toFinset = G.degree v + 1 := by
  simp [closedNeighborSet, ←neighborFinset_eq_filter]

lemma expect_closedNeighbor_card_real (hV : Nonempty V)
    : 𝔼 v, (#(G.closedNeighborSet v).toFinset : ℝ) = d(G) + 1 := by
  simp_rw [closedNeighbor_card, Nat.cast_add, expect_add_distrib, averageDegree_real_cast,
      Nat.cast_one, expect_const univ_nonempty]

lemma closedNeighbor_induce_card (v : V)
    : #(V(G.induce (G.closedNeighborSet v))) = G.degree v + 1 := by
  rw [←closedNeighbor_card, induce_vertex_card]


/-
  ## Lemmas induced graph edge counts
-/

variable (G) in
noncomputable def EdgeFinsetInducedBy (S : Set V) := filter (fun e ↦ ∀ v ∈ e, v ∈ S) E(G)

variable (G) in
noncomputable def EdgeIncidenceFinset (S : Set V) := filter (∃ v ∈ S, v ∈ ·) E(G)


lemma induceEdgeMap (S : Set V) :
    map (Function.Embedding.subtype _).sym2Map E(G.induce S)
    = G.EdgeFinsetInducedBy S := by
  ext e
  constructor <;> simp_rw [EdgeFinsetInducedBy, mem_map, mem_filter, mem_edgeFinset]
  · intro ⟨e', ⟨he', hee'⟩⟩; subst hee'
    refine ⟨(Embedding.map_mem_edgeSet_iff (Embedding.induce _)).2 he', ?_⟩
    simp only [Function.Embedding.sym2Map_apply, Function.Embedding.subtype_apply,
      Sym2.mem_map, Subtype.exists, exists_and_right, exists_eq_right]
    exact fun _ ⟨h, _⟩ ↦ h
  · simp only [Function.Embedding.sym2Map_apply, Function.Embedding.subtype_apply, and_imp]
    intro he hev
    have ⟨v, w, hvwe⟩  := (Sym2.exists).1 ⟨e, rfl⟩; subst hvwe
    refine ⟨s(⟨v, hev _ (Sym2.mem_mk_left _ _)⟩, ⟨w, hev _ (Sym2.mem_mk_right _ _)⟩), he, by simp⟩

lemma induce_edge_card (S : Set V) :
    #E(G.induce S) = #(G.EdgeFinsetInducedBy S) := by rw [←induceEdgeMap, card_map]


lemma EdgeIncidenceFinset_card_zero_from_averageDegree_zero
    (hd : d(G) = 0) (S : Set V) : #(G.EdgeIncidenceFinset S) = 0 := by
  simp [EdgeIncidenceFinset, edgeFinset_empty_from_averageDegree_zero hd]

lemma induceAveragedegree_zero_from_averageDegree_zero
    (hd : d(G) = 0) (S : Set V) : d(G.induce S) = 0 := by
  rw [←edgeFinset_empty_iff_averageDegree_zero, ←card_eq_zero] at *
  rw [←Nat.le_zero, ←hd]
  exact (induce_edge_card S).trans_le (card_le_card (filter_subset _ _))

lemma edge_card_induce_sum (S : Set V) :
    #E(G) = #(G.EdgeIncidenceFinset S) + #E(induce Sᶜ G) := by
  convert (card_filter_add_card_filter_not (∃ v ∈ S, v ∈ ·) (s := E(G))).symm
  · rfl
  convert (induce_edge_card Sᶜ)
  ext _
  simp_rw [EdgeFinsetInducedBy, not_exists, not_and, Set.mem_compl_iff]
  congr! 3
  constructor <;> exact fun hx hv hvS ↦ hx hvS hv

lemma edge_incidence_singelton_eq (v : V) : G.EdgeIncidenceFinset {v} = G.incidenceFinset v := by
  ext _
  simp [mem_incidenceFinset, EdgeIncidenceFinset, mem_filter, incidenceSet]

lemma edge_incidence_singelton_card (v : V) : #(G.EdgeIncidenceFinset {v}) = G.degree v := by
  rw [edge_incidence_singelton_eq, card_incidenceFinset_eq_degree]

lemma degree_zero_of_avg_zero (hd : d(G) = 0) : G.degree v = 0 := by
  rw [←edge_incidence_singelton_card]
  exact EdgeIncidenceFinset_card_zero_from_averageDegree_zero hd _

lemma incident_closedNeighbor_mem_iff (e : Sym2 V) (v : V) :
    (e ∈ G.EdgeIncidenceFinset (G.closedNeighborSet v)) ↔
    ∃ w ∈ G.neighborSet v, e ∈ G.incidenceSet w := by
  simp_rw [EdgeIncidenceFinset, mem_filter, closedNeighborSet, Set.mem_insert_iff,
      mem_neighborSet, exists_eq_or_imp, incidenceSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨he, (hve | ⟨w, hwv, hwe⟩)⟩
    · exact ⟨Sym2.Mem.other hve,
        ⟨by rwa [←mem_edgeSet, Sym2.other_spec, ←mem_edgeFinset],
         ⟨mem_edgeFinset.mp he, Sym2.other_mem _⟩⟩⟩
    · exact ⟨w, ⟨hwv, ⟨mem_edgeFinset.mp he, hwe⟩⟩⟩
  · exact fun ⟨w, ⟨hAdj, ⟨he, hwe⟩⟩⟩ ↦ ⟨mem_edgeFinset.mpr he, Or.inr ⟨w, ⟨hAdj, hwe⟩⟩⟩

lemma incident_closedNeighbor_iff (v : V) :
    G.EdgeIncidenceFinset (G.closedNeighborSet v) =
    Finset.biUnion (G.neighborFinset v) (fun u ↦ (G.incidenceFinset u)):= by
  ext _
  simp [incident_closedNeighbor_mem_iff]

omit [Fintype V] in
lemma triangle_free_neighbors_pairwise_disjoint_incidenceSet (v : V) (hT : G.CliqueFree 3) :
    (G.neighborSet v).PairwiseDisjoint (fun u ↦ G.incidenceSet u) := by
  rw [Set.pairwiseDisjoint_iff]
  intro u hu w hw ⟨e, ⟨heu, hew⟩⟩
  by_contra huw
  exact isIndepSet_neighborSet_of_triangleFree _ hT _ hu hw huw
    (adj_of_mem_incidenceSet _ huw heu hew)

lemma triangle_free_neighbors_pairwise_disjoint_incidenceFinset (v : V) (hT : G.CliqueFree 3) :
    (G.neighborSet v).PairwiseDisjoint (fun u ↦ G.incidenceFinset u) := by
  have this := triangle_free_neighbors_pairwise_disjoint_incidenceSet (v := v) hT
  rw [Set.pairwiseDisjoint_iff, pairwiseDisjoint_iff] at *
  exact fun u hu w hw ⟨e, he⟩ ↦
    (this hu hw ⟨e, by rwa [mem_inter, mem_incidenceFinset, mem_incidenceFinset] at he⟩)

lemma incident_closedNeighbor_card (hT : G.CliqueFree 3) (v : V) :
    #(G.EdgeIncidenceFinset (G.closedNeighborSet v)) =
    ∑ u ∈ G.neighborFinset v, G.degree u := by
  rw [incident_closedNeighbor_iff, card_biUnion ?_]
  · simp only [card_incidenceFinset_eq_degree]
  · convert (triangle_free_neighbors_pairwise_disjoint_incidenceFinset v hT)
    ext _; simp

lemma incidence_closedNeighbor_expectation (hT : G.CliqueFree 3)
    : 𝔼 v, (#(G.EdgeIncidenceFinset (G.closedNeighborSet v)) : ℚ) = 𝔼 v, (G.degree v : ℚ)^2 := by
  conv_lhs => rhs; intro; rw [incident_closedNeighbor_card hT, Nat.cast_sum, ←Fintype.sum_ite_mem]
  rw [expect_sum_comm]
  conv_lhs => rhs; intro; rhs; intro; rw [←mul_boole]
  conv_lhs => rhs; intro; rw [←mul_expect, expect, sum_boole, mul_smul_comm]
  rw [expect, smul_sum]; congr 1; ext; rw [pow_two]; congr 4
  ext; simp [mem_neighborFinset, adj_comm]

lemma incidence_closedNeighbor_expectation_real (hT : G.CliqueFree 3)
    : 𝔼 v, (#(G.EdgeIncidenceFinset (G.closedNeighborSet v)) : ℝ) = 𝔼 v, (G.degree v : ℚ)^2 := by
  rw [←incidence_closedNeighbor_expectation hT]
  convert (algebraMap.coe_expect (M := ℚ) (N := ℝ) _ _).symm
  · norm_cast
  · rfl

lemma averageDegree_square_bound : d(G) ^ 2 ≤ 𝔼 v, (G.degree v : ℚ)^2 := by
  convert expect_mul_sq_le_sq_mul_sq (f := fun v ↦ (G.degree v : ℚ)) (g := fun _ ↦ 1) univ
  · rfl
  · simp only [averageDegree, mul_one]
  · by_cases h_nonempty : Nonempty V
    · rw [expect_const (univ_nonempty_iff.2 h_nonempty), one_pow, mul_one]
    · simp_all




/-
  ## Recursions for α and i
-/


lemma bot_Is_independent : ⊥ ∈ ℐ(G) := by
  rw [I_rw]
  exact fun _ hx _ _ _ _ ↦ hx

lemma indepSetFinsetAll_nonempty : ℐ(G).Nonempty :=
  ⟨⊥, bot_Is_independent⟩

lemma indepSetFinsetAll_subset {S₁ S₂ : Set V} (hind : S₁ ∈ ℐ(G)) (hsub : S₂ ⊆ S₁)
    : S₂ ∈ ℐ(G) := by
  rw [I_rw] at *
  exact fun  x hx y hy hxy ↦ hind (hsub hx) (hsub hy) hxy

lemma IsIndependentInduce (S : Set V) (I : Set S) :
    I ∈ ℐ(G.induce S) ↔ (Subtype.val '' I) ∈ ℐ(G) := by
  simp_rw [I_rw, IsIndepSet, comap_adj, Function.Embedding.subtype_apply]
  constructor
  · intro h _ hx _ hy hxy
    rw [Subtype.coe_image] at hx hy
    exact h hx.2 hy.2 (Subtype.coe_ne_coe.mp hxy)
  · intro h _ hx _ hy hxy
    exact h (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy) (Subtype.coe_ne_coe.mpr hxy)

lemma IsIndependentInduce' {S I : Set V} (hIS : I ⊆ S) :
    {x | x.1 ∈ I} ∈ ℐ(G.induce S) ↔ I ∈ ℐ(G):= by
  rw [IsIndependentInduce, Subtype.coe_image_of_subset hIS]

def embeddingOfSubsetSubtype (S : Set V) [DecidablePred (· ∈ S)] : Set S ↪ Set V where
  toFun := fun I ↦ Subtype.val '' I
  inj' := by intro _ _; simp only [Set.image_val_inj, imp_self]

omit [Fintype V] in
lemma embeddingOfSubsetSubtype_rw (S : Set V) (I : Set S) :
    embeddingOfSubsetSubtype S I = Subtype.val '' I := rfl

omit [Fintype V] in
lemma set_subtype_tofinset_card_iff {S : Set V} {I : Set S}
      : I.ncard = (Subtype.val '' I).ncard:=
    (Set.ncard_image_of_injective I Subtype.val_injective).symm

lemma IsIndependentInduce_map (S : Set V) : map (embeddingOfSubsetSubtype S) ℐ(G.induce S)
    = (filter (· ⊆ S) ℐ(G)) := by
  ext I
  simp_rw [mem_map, mem_filter, embeddingOfSubsetSubtype_rw, IsIndependentInduce]
  exact ⟨ fun ⟨_, ⟨hI, hII'⟩⟩ ↦ (by rw [←hII']; exact ⟨hI, Subtype.coe_image_subset _ _⟩),
          fun ⟨_, _⟩ ↦ ⟨{x | x.1 ∈ I}, by simp_all⟩⟩

lemma IsIndependentInduce_implies {S : Set V} {I : Set S} (hI : I ∈ ℐ(induce S G)) :
    Subtype.val '' I ∈ ℐ(G) ∧ Subtype.val '' I ⊆ S := by simp_all [IsIndependentInduce]

lemma induced_inedependent_set_count (S : Set V) [DecidablePred (· ∈ S)] :
    #ℐ(G.induce S) = #(filter (· ⊆ S) ℐ(G)) := by
  rw [←IsIndependentInduce_map, Finset.card_map]
  congr
  exact Subsingleton.elim _ _

lemma mem_of_indepSetFinsetAll_card_le_indepNum {I : Set V} (hI : I ∈ ℐ(G))
    : I.ncard ≤ α(G) := by
  rw [Set.ncard_eq_toFinset_card' I]
  exact IsIndepSet.card_le_indepNum (by rw [I_rw] at hI; rwa [Set.coe_toFinset])

variable (G) in
lemma exists_mem_indepSetFinsetAll_card_indepNum
    : ∃ I ∈ ℐ(G), I.ncard = α(G) := by
  have ⟨_, ⟨_, card_eq⟩⟩ := G.exists_isNIndepSet_indepNum
  exact ⟨_, ⟨by rwa [I_rw], by rwa [Set.ncard_coe_finset]⟩⟩

/-The independent set version of `isClique_insert`.-/
lemma insert_mem_indepSetFinsetAll_iff {S : Set V}
    : (insert v S) ∈ ℐ(G) ↔ S ∈ ℐ(G) ∧ ∀ u ∈ S, ¬G.Adj v u := by
  simp_rw [I_rw, ←isClique_compl, isClique_insert, isClique_compl, compl_adj]
  exact ⟨ fun ⟨hI, h⟩ ↦ ⟨hI, fun _ hu hAdj ↦ (h _ hu (Adj.ne' hAdj).symm).2 hAdj⟩,
          fun ⟨hI, h⟩ ↦ ⟨hI, fun _ hu hvu ↦ ⟨hvu, h _ hu⟩⟩⟩

lemma indepSet_augment {v : V} {I : Set V} (hI : I ∈ ℐ(G)) :
    I ⊆ (G.closedNeighborSet v)ᶜ ↔ v ∉ I ∧ (insert v I) ∈ ℐ(G) := by
  rw [insert_mem_indepSetFinsetAll_iff]
  exact ⟨fun hI_sub ↦ ⟨fun hIv ↦ hI_sub hIv (Set.mem_insert _ _),
      ⟨hI, fun u hu hAdj ↦ (hI_sub hu (Set.mem_insert_of_mem _ hAdj))⟩⟩,
        fun ⟨hvI, ⟨_, hAdj⟩⟩ u huI huIn ↦
       hAdj u huI (Adj_of_mem_closedNeighborSet_of_ne_v (by grind only) huIn)⟩

omit [Fintype V] in
lemma indepSet_insert_bound [Finite V] (v : V) :
    α(G) ≥ α(G.induce (G.closedNeighborSet v)ᶜ) + 1 := by
  cases nonempty_fintype V
  have ⟨I, hI, hI_card⟩ :=
    (induce (G := G) (G.closedNeighborSet v)ᶜ).exists_mem_indepSetFinsetAll_card_indepNum
  rw [←hI_card, ge_iff_le]
  have this := IsIndependentInduce_implies (by convert hI)
  rw [indepSet_augment this.1] at this
  convert mem_of_indepSetFinsetAll_card_le_indepNum this.2.2
  rw [(Set.ncard_insert_of_notMem this.2.1), ←set_subtype_tofinset_card_iff]


lemma indepSet_card_recursion (v : V)
    : #ℐ(G) = #ℐ(G.induce {v}ᶜ) + #ℐ(G.induce (G.closedNeighborSet v)ᶜ) := by
  rw [add_comm]
  convert (Finset.card_filter_add_card_filter_not (p := (v ∈ ·))).symm
  · convert induced_inedependent_set_count (G := G) (S := (G.closedNeighborSet v)ᶜ) using 1
    symm
    refine Finset.card_bij (i := fun S _ ↦ insert v S) ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, Set.mem_insert_iff, true_or, and_true]
      rw [mem_filter] at hS
      exact ((indepSet_augment hS.1).1 hS.2).2
    · intro S₁ hS₁ S₂ hS₂ heq
      rw [mem_filter] at *
      refine Set.Subset.antisymm ?_ ?_ <;> rw [←Set.insert_subset_insert_iff (a := v) ?_]
      · exact Eq.subset heq
      · exact fun hv ↦ hS₁.2 hv self_mem_closedNeighborSet
      · exact Eq.subset heq.symm
      · exact fun hv ↦ hS₂.2 hv self_mem_closedNeighborSet
    · intro S hS
      use S \ {v}
      simp only [Set.insert_sdiff_singleton, Set.insert_eq_self, mem_filter,
        Set.sdiff_singleton_subset_iff, exists_prop]
      simp_rw [mem_filter] at hS
      refine ⟨⟨indepSetFinsetAll_subset hS.1 Set.sdiff_subset,?_⟩, hS.2⟩
      intro x hx
      refine Set.mem_insert_iff.mpr ?_
      rw [or_iff_not_imp_left]
      intro hxv hxNbr
      rw [I_rw] at hS
      apply hS.1 hx hS.2 hxv (Adj_of_mem_closedNeighborSet_of_ne_v (fun a ↦ hxv a.symm) hxNbr).symm
  · convert induced_inedependent_set_count (S := {v}ᶜ)
    simp
  · exact inferInstance
  · exact inferInstance


lemma Jensen_expect {α : Type} {t : Finset α} (ht : t.Nonempty) {s : Set ℝ} {f : ℝ → ℝ} (p : α → ℝ)
    (hmem : ∀ i ∈ t, p i ∈ s) (hf : ConvexOn ℝ s f) : f (𝔼 i ∈ t, p i) ≤ 𝔼 i ∈ t, f (p i) := by
  have hc : (0 : ℝ) < #t := Nat.cast_pos.2 (card_pos.2 ht)
  have hrw : ∀ g : α → ℝ, 𝔼 i ∈ t, g i = ∑ i ∈ t, (#t : ℝ)⁻¹ • g i := by
    intro g; simp_rw [expect_eq_sum_div_card, sum_div, smul_eq_mul, mul_comm, div_eq_mul_inv]
  rw [hrw, hrw]
  exact hf.map_sum_le (fun _ _ ↦ inv_nonneg.2 hc.le)
    (by simp [sum_const, nsmul_eq_mul, mul_inv_cancel₀ hc.ne']) hmem

lemma exp_expect_le_expect_exp (g : V → ℝ) (hV : Nonempty V)
    : Real.exp (𝔼 v, g v) ≤ 𝔼 v, Real.exp (g v) :=
  Jensen_expect (univ_nonempty_iff.2 hV) _ (by simp) convexOn_exp


/-
  ## Shearer Step
-/

variable (G) in
noncomputable def extra (f f' : ℝ → ℝ) (a : ℝ) (b : ℝ) :=
  if Nonempty V then a * (d(G) * f' d(G) - f d(G)) + b * (- 2 * f' d(G))
                else 0

lemma extra_nonempty {f f' : ℝ → ℝ} {a : ℝ} {b : ℝ} (hV : Nonempty V) :
    extra G f f' a b = a * (d(G) * f' d(G) - f d(G)) + b * (- 2 * f' d(G)) :=
  if_pos hV

lemma extra_IsEmpty {f f' : ℝ → ℝ} {a : ℝ} {b : ℝ} (hV : IsEmpty V) :
    extra G f f' a b = 0 := if_neg (not_nonempty_iff.2 hV)

lemma extra_rewrite_aux {f f' : ℝ → ℝ} (hV : Nonempty V) : G.extra f f' (d(G) + 1) (d(G) ^ 2)
    = ((d(G)) - d(G)^2) * f' (d(G)) - ((d(G)) + 1) * f d(G) := by
  rw [extra_nonempty hV]
  ring

lemma extra_rewrite_aux' {f f' : ℝ → ℝ} (hV : Nonempty V) : G.extra f f' 1 d(G)
    = - (d(G)) * f' (d(G)) - f (d(G)) := by
  rw [extra_nonempty hV]
  ring


variable (G) in
lemma extra_expect {f f' : ℝ → ℝ} {g₁ g₂ : V → ℝ} :
    𝔼 v, extra G f f' (g₁ v) (g₂ v) = extra G f f' (𝔼 v, g₁ v) (𝔼 v, g₂ v) := by
  unfold extra
  split_ifs
  · rw [expect_add_distrib, ←expect_mul, ←expect_mul]
  · exact expect_const_zero _

lemma extra_finset_zero {f f' : ℝ → ℝ} (S : Set V) (h : d(G) = 0)
    : extra G f f' (#S.toFinset) 0 = -(#S.toFinset) * f 0 := by
  unfold extra
  split_ifs <;> simp_all

lemma extra_ineq {a b c : ℝ} {f f' : ℝ → ℝ} (hf' : ∀ x, 0 < x → f' x ≤ 0) (hab : b ≤ c)
    (hdG : 0 < d(G)) :
    extra G f f' a b ≤ extra G f f' a c := by
  unfold extra
  split_ifs
  · gcongr
    linarith [hf' d(G) (Rat.cast_pos.mpr hdG)]
  · exact le_refl _

noncomputable def convexIneq (f f' : ℝ → ℝ) :=
    ∀ x y, 0 ≤ x → 0 < y → f x ≥ f y + f' y * (x - y)

lemma shearer_convex_step {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
    {H₁ : SimpleGraph V₁} {H₂ : SimpleGraph V₂} (f f' : ℝ → ℝ) (hf : convexIneq f f')
    (hdH₁ : 0 < d(H₁)) : #V(H₂) * f d(H₂) ≥
    #V(H₁) * f d(H₁) + extra H₁ f f' (#V(H₁) - #V(H₂)) (#E(H₁) - #E(H₂))
  := by
  have h_ineq := hf d(H₂) d(H₁) (Rat.cast_nonneg.2 averageDegree_nonneg) (Rat.cast_pos.2 hdH₁)
  have cast_rw (a : ℕ) : (a : ℝ) = ((a : ℚ) : ℝ) := rfl
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h_ineq (Nat.cast_nonneg _))
  rw [extra_nonempty (vertexType_Nonempty_from_averageDegree_pos hdH₁),
      ←mul_assoc, mul_comm (b := -2), neg_mul_comm, neg_sub,
      mul_sub (a := 2), ←Nat.cast_ofNat, ←Nat.cast_mul, ←Nat.cast_mul, cast_rw (2 * #E(H₂)),
      Nat.cast_mul,Nat.cast_ofNat, ←averageDegree_eq_twice_card_edges_div_card,
      cast_rw (2 * #E(H₁)), Nat.cast_mul,Nat.cast_ofNat,
      ←averageDegree_eq_twice_card_edges_div_card, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_mul, Rat.cast_natCast, ←sub_nonneg]
  convert le_refl _
  ring

lemma convex_step_induce (S : Set V) {f f' : ℝ → ℝ} (hf : convexIneq f f')
  : #V(G.induce Sᶜ) * f d(G.induce Sᶜ) ≥ #V(G) * f d(G) +
    extra G f f' #S.toFinset #(G.EdgeIncidenceFinset S)  := by
    by_cases hd : d(G) = 0
    · have this : d(induce Sᶜ G) = 0 := by
        convert induceAveragedegree_zero_from_averageDegree_zero hd _
      rw [hd, this, Rat.cast_zero,
      EdgeIncidenceFinset_card_zero_from_averageDegree_zero hd, Nat.cast_zero,
      extra_finset_zero _ hd, neg_mul, ge_iff_le, add_neg_le_iff_le_add, ←add_mul,
      ←Nat.cast_add, add_comm, induce_vertex_card, (vertex_card_induce_sum S)]
    · convert shearer_convex_step (H₁ := G) (H₂ := G.induce Sᶜ) f f' hf
        (averageDegree_pos_from_nonzero hd) <;>
      rw [eq_sub_iff_add_eq, ←Nat.cast_add, Nat.cast_inj]
      · rw [induce_vertex_card]
        exact (vertex_card_induce_sum S).symm
      · exact (edge_card_induce_sum S).symm

lemma convex_step_expect {F : V → Set V} {f f' : ℝ → ℝ} (hf : convexIneq f f')
  : 𝔼 v, #V(G.induce (F v)ᶜ) * f d(G.induce (F v)ᶜ) ≥ #V(G) * f d(G) +
    extra G f f' (𝔼 v, #(F v).toFinset) (𝔼 v, #(G.EdgeIncidenceFinset (F v))) := by
  rw [ge_iff_le]
  convert expect_le_expect
    (f := fun v ↦ #V(G) * f d(G) + extra G f f' #(F v).toFinset #(G.EdgeIncidenceFinset (F v)))
    (fun v hv ↦ convex_step_induce _ hf) using 1
  · rfl
  rw [expect_add_distrib, extra_expect]
  congr 1
  by_cases hV : #V(G) = 0
  · simp [hV]
  · exact (expect_const (card_ne_zero.mp hV) _).symm

lemma convex_step_expect_closedNeighbor {f f' : ℝ → ℝ} (hf : convexIneq f f')
    (hT : G.CliqueFree 3) (hf' : ∀ (x : ℝ), 0 < x → f' x ≤ 0)
    : 𝔼 v, #V(G.induce (G.closedNeighborSet v)ᶜ) * f d(G.induce (G.closedNeighborSet v)ᶜ)
    ≥ #V(G) * f d(G) + extra G f f' (d(G) + 1) (d(G) ^ 2) := by
  by_cases hV : Nonempty V
  · refine le_trans ?_ (convex_step_expect (F := fun v ↦ G.closedNeighborSet v) hf)
    gcongr
    rw [expect_closedNeighbor_card_real hV, incidence_closedNeighbor_expectation_real hT,
      ←Rat.cast_pow]
    by_cases hdG : d(G) = 0
    · simp [hdG, degree_zero_of_avg_zero]
    · exact extra_ineq hf'  (Rat.cast_le.2 averageDegree_square_bound)
                            (averageDegree_pos_from_nonzero hdG)
  · simp_all [extra_IsEmpty, card_vertices_eq_zero_from_empty]

theorem Shearer_bound (hT : G.CliqueFree 3) {f f' : ℝ → ℝ} (hf : convexIneq f f')
    (hf' : ∀ (x : ℝ), 0 < x → f' x ≤ 0)
    (h_extra : ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'},
      0 ≤ G'.extra f f' (d(G') + 1) (d(G') ^ 2) + 1)
    : α(G) ≥ #V(G) * f d(G) := by
  suffices h : ∀ n, ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'} (hn : n = #V(G'))
    (hT : G'.CliqueFree 3), α(G') ≥ n * (f d(G')) from (h _ rfl hT)
  intro n
  induction n using Nat.strong_induction_on with | _ n hn =>
  intro V _ G hcard hT
  by_cases hV : Nonempty V
  · rw [←expect_const (univ_nonempty_iff.mpr hV) (α(G) : ℝ)]
    calc
      𝔼 v, (α(G) : ℝ)   ≥ 𝔼 v, ((α(G.induce (G.closedNeighborSet v)ᶜ) + 1 : ℕ) : ℝ) :=
        expect_le_expect (fun _ _ ↦ (Nat.cast_le.2 (indepSet_insert_bound _)))
      _                 = 𝔼 v, (α(G.induce (G.closedNeighborSet v)ᶜ) + 1 : ℝ) := by simp
      _                 = (𝔼 v, (α(G.induce (G.closedNeighborSet v)ᶜ) : ℝ)) + 1 := by
        rw [expect_add_distrib, expect_const (univ_nonempty_iff.mpr hV) _]
      _                 ≥ (𝔼 v, #V(G.induce (G.closedNeighborSet v)ᶜ) *
                          f d(G.induce (G.closedNeighborSet v)ᶜ)) + 1 := by
        gcongr;
        apply hn
        · rw [hcard]
          exact induce_vertex_card_compl_lt nonempty_closedNeighborSet
        · rfl
        · exact CliqueFree.comap ⟨Copy.induce G _⟩ hT
      _                 ≥ #V(G) * f d(G) + extra G f f' (d(G) + 1) (d(G) ^ 2) + 1 := by
        gcongr;
        exact convex_step_expect_closedNeighbor hf hT hf'
      _                 ≥ #V(G) * f d(G) + 0  := by
        rw [add_assoc]
        gcongr
        exact h_extra
      _                 = #V(G) * f d(G)      := add_zero _
    rw [hcard]
  · rw [card_vertices_eq_zero_from_empty (not_nonempty_iff.mp hV)] at hcard
    simp [hcard]


/-
  ## The result for independent set count
-/

lemma convex_step_expect_vertex_complement {f f' : ℝ → ℝ} (hf : convexIneq f f')
    : 𝔼 v, #V(G.induce {v}ᶜ) * f d(G.induce {v}ᶜ)
    ≥ #V(G) * f d(G) + extra G f f' 1 d(G) := by
  by_cases hV : Nonempty V
  · convert (convex_step_expect (F := fun v ↦ {v}) hf)
    · simp
    · simp [edge_incidence_singelton_card, averageDegree_real_cast]
  · simp_all [card_vertices_eq_zero_from_empty, extra_IsEmpty]

theorem independent_set_count_bound (hT : G.CliqueFree 3) {f f' : ℝ → ℝ}
    (hf : convexIneq f f')
    (hf' : ∀ (x : ℝ), 0 < x → f' x ≤ 0)
    (h_extra : ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'},
      1 ≤
        Real.exp (G'.extra f f' 1 d(G')) +
        Real.exp (G'.extra f f' (d(G') + 1) (d(G') ^ 2)))
    : #ℐ(G) ≥ Real.exp (#V(G) * f d(G)) := by
  suffices h : ∀ n, ∀ {V' : Type} [Fintype V'] {G' : SimpleGraph V'} (hn : n = #V(G'))
    (hT : G'.CliqueFree 3), #ℐ(G') ≥ Real.exp (#V(G') * f d(G')) from (h _ rfl hT)
  intro n
  induction n using Nat.strong_induction_on with | _ n hn =>
  intro V _ G hcard hT
  by_cases hV : Nonempty V
  · rw [←expect_const (univ_nonempty_iff.mpr hV) (#ℐ(G) : ℝ)]
    calc
      𝔼 v, (#ℐ(G) : ℝ)
            = 𝔼 v, (#ℐ(G.induce {v}ᶜ) + #ℐ(G.induce (G.closedNeighborSet v)ᶜ) : ℝ ) := by
        apply expect_congr rfl
        exact_mod_cast fun _ _ ↦ indepSet_card_recursion _
      _   =   𝔼 v, (#ℐ(G.induce {v}ᶜ) : ℝ)
            + 𝔼 v, (#ℐ(G.induce (G.closedNeighborSet v)ᶜ) : ℝ )  := expect_add_distrib _ _ _
      _   ≥   𝔼 v, Real.exp (#V(G.induce {v}ᶜ) * f d(G.induce {v}ᶜ))
            + 𝔼 v, Real.exp (#V(G.induce (G.closedNeighborSet v)ᶜ)
                              * f d(G.induce (G.closedNeighborSet v)ᶜ)) := by
        gcongr <;> rename_i v hv
        · apply hn (#V(G.induce {v}ᶜ))
          · rw [hcard]
            refine induce_vertex_card_compl_lt ⟨v, rfl⟩
          · rfl
          · exact CliqueFree.comap ⟨Copy.induce G _⟩ hT
        · apply hn (#V(G.induce (G.closedNeighborSet v)ᶜ))
          · rw [hcard]
            refine induce_vertex_card_compl_lt nonempty_closedNeighborSet
          · rfl
          · exact CliqueFree.comap ⟨Copy.induce G _⟩ hT
      _   ≥   Real.exp (𝔼 v, #V(G.induce {v}ᶜ) * f d(G.induce {v}ᶜ))
            + Real.exp (𝔼 v, #V(G.induce (G.closedNeighborSet v)ᶜ)
                              * f d(G.induce (G.closedNeighborSet v)ᶜ)) := by
        gcongr <;> exact exp_expect_le_expect_exp _ hV
      _   ≥   Real.exp (#V(G) * f d(G) + extra G f f' 1 d(G))
            + Real.exp (#V(G) * f d(G) + extra G f f' (d(G) + 1) (d(G) ^ 2)) := by
        gcongr
        · exact convex_step_expect_vertex_complement hf
        · exact convex_step_expect_closedNeighbor hf hT hf'
      _   = Real.exp (#V(G) * f d(G)) *
            (Real.exp (extra G f f' 1 d(G)) + Real.exp (extra G f f' (d(G) + 1) (d(G) ^ 2))) := by
        rw [Real.exp_add, Real.exp_add, mul_add]
      _                 ≥ Real.exp (#V(G) * f d(G)) := by
        nth_rewrite 2 [←mul_one (a := Real.exp (↑(#V(G)) * f ↑d(G)))]
        gcongr
        exact h_extra
  · simp [card_vertices_eq_zero_from_empty (not_nonempty_iff.mp hV), indepSetFinsetAll_nonempty]


end SimpleGraph
