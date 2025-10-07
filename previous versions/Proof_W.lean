import Mathlib
import ShearerTriangleFreeInd.Analysis
import ShearerTriangleFreeInd.Analysis_W
import ShearerTriangleFreeInd.Proof



open Finset SimpleGraph BigOperators
open Classical


namespace SimpleGraph

variable {V : Type}



def delete_vtx (G : SimpleGraph V) (v : V) := G.induce {v}ᶜ




def vtx_complementEmbedding {v : V} : Set.Elem {v}ᶜ ↪ V  :=
  Function.Embedding.subtype _
def delete_vtxEmbedding {G : SimpleGraph V} {v : V} : G.delete_vtx v ↪g G :=
  Embedding.induce _
lemma finset_coe_subtype' {v : V} (S : Finset ({v}ᶜ : Set V)) :
    (S.map vtx_complementEmbedding : Set V)  = Subtype.val '' (S : Set ({v}ᶜ : Set V))
  := coe_map _ _



variable {G : SimpleGraph V} {v : V}

#check G.delete_vtx v


lemma vtx_not_mem_image_edge (e : Sym2 (Set.Elem {v}ᶜ))
    : v ∉ (vtx_complementEmbedding.sym2Map e) := by
  intro h
  have ⟨u, _, hueq⟩ := Sym2.mem_map.1 h
  apply (fun a ↦ a rfl : v ∉ ({v}ᶜ : Set V))
  nth_rewrite 2 [←hueq]
  exact u.2

lemma exists_preimage_of_edge {e : Sym2 V}
    (he : e ∈ G.edgeSet) (hu_not : v ∉ e)
    : ∃ e' ∈ (G.delete_vtx v).edgeSet, (vtx_complementEmbedding.sym2Map e') = e := by
  have this : ∀ u ∈ e, u ≠ v := by intro _ _ h; subst h; contradiction
  have he_eq : vtx_complementEmbedding.sym2Map (e.attachWith this) = e
    := Sym2.attachWith_map_subtypeVal _
  rw [←he_eq] at he
  exact ⟨_, ⟨(Embedding.map_mem_edgeSet_iff delete_vtxEmbedding).mp he, he_eq⟩⟩

variable (G) (v) in
lemma delete_vtx_image_eq : vtx_complementEmbedding.sym2Map '' (G.delete_vtx v).edgeSet =
    G.edgeSet \ (G.incidenceSet v) := by
  ext e
  rw [Set.mem_diff]
  constructor
  · intro ⟨_, he', he_eq⟩
    rw [←he_eq]
    refine ⟨(Embedding.map_mem_edgeSet_iff delete_vtxEmbedding).mpr he',
      fun he ↦ vtx_not_mem_image_edge _ he.2⟩
  · exact fun ⟨he, h⟩ ↦ (Set.mem_image _ _ _).2 (exists_preimage_of_edge he (fun hv ↦ h ⟨he, hv⟩))



variable [Fintype V]

variable (G) (v) in
lemma delete_vtx_edgeFinset_map_eq
  : map vtx_complementEmbedding.sym2Map (G.delete_vtx v).edgeFinset =
    G.edgeFinset \ G.incidenceFinset v := by
  rw [←coe_inj];
  convert delete_vtx_image_eq G v <;> simp


example : G.incidenceFinset v ⊆ G.edgeFinset := by
  exact incidenceFinset_subset G v

lemma delete_vtx_edge_card : #(G.delete_vtx v).edgeFinset = #G.edgeFinset - G.degree v := by
  convert (congrArg card (delete_vtx_edgeFinset_map_eq G v))
  · exact (card_map _).symm
  · rw [card_sdiff (incidenceFinset_subset G v), card_incidenceFinset_eq_degree G v]

lemma delete_vtx_edge_card_rat :
    (#(G.delete_vtx v).edgeFinset : ℚ) = #G.edgeFinset - G.degree v := by
  rw [delete_vtx_edge_card, ←card_incidenceFinset_eq_degree G v]
  exact Nat.cast_sub (card_le_card (incidenceFinset_subset G v))

lemma expect_delete_vtx_edgeFinset_card
    : (𝔼 v, #(G.delete_vtx v).edgeFinset : ℚ) = #G.edgeFinset - G.averageDegree := by
  simp_rw [delete_vtx_edge_card_rat, expect_sub_distrib]
  congr
  by_cases hV : Nonempty V
  · exact expect_const (univ_nonempty_iff.mpr hV) _
  · rw [not_nonempty_iff] at hV
    simp


variable (G) in
noncomputable def indepSetFinsetAll : Finset (Finset V) := {s | G.IsIndepSet s}

noncomputable def i := #G.indepSetFinsetAll

lemma indepSetFinsetAll_is_indepSet {W : Type} {H : SimpleGraph W} [Fintype W] (S : Finset W) :
    S ∈ H.indepSetFinsetAll ↔ H.IsIndepSet S := by
  rw [indepSetFinsetAll, mem_filter]
  refine and_iff_right_iff_imp.mpr (fun _ ↦ mem_univ _)


/-
  New idea:
    show that there is a bijection between the independent sets
    of an induced subgraph on a set S and the independent sets
    of G that are contained in S.
-/


lemma induced_inedependent_set_count {V₁ : Type} {H : SimpleGraph V₁}
    [Fintype V₁] {S : Set V₁} :
    #((H.induce S).indepSetFinsetAll) = #(filter (·.toSet ⊆ S) H.indepSetFinsetAll) := by
  apply Set.BijOn.finsetCard_eq (Finset.map (Function.Embedding.subtype fun x => x ∈ S) ·)
  refine Set.BijOn.mk ?_ ?_ ?_
  · intro I hI
    rw [mem_coe, indepSetFinsetAll_is_indepSet] at hI
    simp only [coe_filter, indepSetFinsetAll_is_indepSet, Set.mem_setOf_eq, coe_map,
      Function.Embedding.subtype_apply, Set.image_subset_iff, Subtype.coe_preimage_self,
      Set.subset_univ, and_true]
    exact Set.Pairwise.image hI
  · simp
  · intro I
    simp only [coe_filter, Set.mem_setOf_eq, Set.mem_image, mem_coe, and_imp]
    intro hI_ind hI_S
    refine ⟨Finset.subtype (· ∈ S) I,?_,?_⟩
    · rw [indepSetFinsetAll_is_indepSet] at *
      intro v hv u hu hvu
      simp_all only [mem_coe, mem_subtype, ne_eq, comap_adj, Function.Embedding.subtype_apply]
      exact hI_ind hv hu (Subtype.coe_ne_coe.mpr hvu)
    · rw [subtype_map]
      exact filter_true_of_mem hI_S


lemma delete_vtx_indepSetCount
    : #(G.delete_vtx v).indepSetFinsetAll = #(filter (v ∉ ·) G.indepSetFinsetAll) := by
  convert induced_inedependent_set_count
  simp

lemma puncture_indepSetCount
    : #(G.puncture v).indepSetFinsetAll = #(filter (v ∈ ·) G.indepSetFinsetAll) := by
  convert induced_inedependent_set_count using 1
  refine Set.BijOn.finsetCard_eq (erase · v) (Set.InvOn.bijOn (f' := (insert v ·)) ?_ ?_ ?_  )
  · refine ⟨?_, ?_⟩
    · intro S hS
      rw [mem_coe, mem_filter] at hS
      simp [hS.2]
    · intro S hS
      rw [mem_coe, mem_filter] at hS
      have this : v ∉ S := fun hc ↦ not_mem_exterior_self (hS.2 hc)
      simp [this]
  · intro S hS
    simp_all only [coe_filter, Set.mem_setOf_eq, coe_erase, Set.diff_singleton_subset_iff,
      indepSetFinsetAll, mem_filter, mem_univ, true_and]
    refine ⟨Set.Pairwise.mono (Set.diff_subset) hS.1, ?_⟩
    rw [←Set.toFinset_subset_toFinset, toFinset_coe, Set.toFinset_insert,
        puncture_verts_toFinset, subset_iff]
    intro u hu
    rw [mem_insert, mem_sdiff, or_iff_not_imp_left]
    intro huv
    refine ⟨mem_univ _, ?_⟩
      -- Seperate Lemma
    sorry
  · intro S hS
    simp_all only [indepSetFinsetAll, coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq,
      coe_insert, mem_insert, true_or, and_true, isIndepSet_insert]
    exact fun _ hu _ ↦ not_adj_of_mem_exterior (hS.2 hu)







lemma shearer_convex_step {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
  {H₁ : SimpleGraph V₁} {H₂ : SimpleGraph V₂} (f f' : ℝ → ℝ)
  (hf : f (H₂.averageDegree) ≥
    f (H₁.averageDegree) + f' (H₁.averageDegree) * (H₂.averageDegree - H₁.averageDegree))
  : (Fintype.card V₂) * f (H₂.averageDegree) ≥
    (Fintype.card V₁) * f (H₁.averageDegree) +
    (Fintype.card V₁ - Fintype.card V₂) *
      (H₁.averageDegree * f' H₁.averageDegree - f H₁.averageDegree) -
    2 * (#H₁.edgeFinset - #H₂.edgeFinset) * f' H₁.averageDegree  := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg _))
  rw [mul_sub, mul_sub, ←card_mul_averageDegree_eq_twice_card_edges_real,
    ←card_mul_averageDegree_eq_twice_card_edges_real, ←sub_nonneg]
  convert le_refl _
  ring

lemma expect_const' {c : ℝ} :  𝔼 _ : V, c = (if Fintype.card V = 0 then 0 else 1) * c := by
  split_ifs
  · simp_all [expect]
  · rw [one_mul]
    convert expect_const ?_ (c : ℝ)
    exact card_ne_zero.mp (by assumption)

lemma nonempty_from_averageDegre_nonzero (h : G.averageDegree ≠ 0) :
    (univ : Finset V).Nonempty := by
  by_contra hV
  apply h
  have this : Fintype.card V = 0 := by
    rwa [Fintype.card_eq_zero_iff, ←not_nonempty_iff, ←univ_nonempty_iff]
  rw [averageDegree_eq_twice_card_edges_div_card, this]; simp

lemma shearer_expectation_exterior_step
  {f f' : ℝ → ℝ}
  (hf : ∀ x y, 0 ≤ x → 0 < y → f x ≥ f y + f' y * (x - y))
  (hf0 : 0 ≤ f 0)
  (hf' : 0 ≥ f' G.averageDegree)
  (hT : G.CliqueFree 3)
  : 𝔼 v, (Fintype.card (G.exterior v)) * f (G.puncture v).averageDegree ≥
    (Fintype.card V) * f (G.averageDegree) +
    (G.averageDegree + 1) *
      (G.averageDegree * f' G.averageDegree - f G.averageDegree) -
    2 * G.averageDegree^2 * f' G.averageDegree  := by
  by_cases hd : G.averageDegree = 0
  · conv => lhs; rhs; intro v; rw [averageDegree_puncture_eq_zero_of_averageDegree_eq_zero hd,
      card_exterior_eq_real]
    rw [←expect_mul, expect_sub_distrib, expect_add_distrib, averageDegree_real, hd,
      Rat.cast_zero, zero_mul, zero_sub, zero_pow (by norm_num), mul_zero, zero_mul,
      sub_zero, expect_const', expect_const']
    split_ifs
    · simp_all
    · rw [ge_iff_le, ←sub_nonneg]
      convert le_refl _
      ring_nf
  · refine le_trans ?_ (expect_le_expect (f := fun v ↦
    (Fintype.card V) * f (G.averageDegree) +
    (Fintype.card V - Fintype.card (G.exterior v)) *
      (G.averageDegree * f' G.averageDegree - f G.averageDegree) -
    2 * (#G.edgeFinset - #(G.puncture v).edgeFinset) * f' G.averageDegree
    ) ?_)
    · rw [expect_sub_distrib, expect_add_distrib, ←expect_mul, ←expect_mul, ←expect_mul,
        ←mul_expect, mul_assoc (a := 2), mul_assoc (a := 2)]
      have hV : (univ : Finset V).Nonempty := nonempty_from_averageDegre_nonzero hd
      gcongr (?_ + ?_) - (2 * ?_)
      · rw [expect_const']
        split_ifs <;> simp_all
      · convert le_rfl
        conv => lhs; rhs; intro v; rw [card_exterior_eq_real]; ring_nf
        rw [expect_add_distrib, add_comm, averageDegree_real]
        congr
        refine expect_const hV 1
      · refine mul_le_mul_of_nonpos_right ?_ hf'
        rw [expect_sub_distrib, expect_const hV, expect_puncture_edgeFinset_card_real hT]
        ring_nf
        convert (Mathlib.Tactic.Rify.ratCast_le _ _).mp (averageDegree_square_bound (G := G))
        · simp
        · have := (algebraMap.coe_expect univ (M := ℚ) (N := ℝ) (fun v ↦ (G.degree v : ℚ)^2)).symm
          simp_all
    · intro u hu
      refine shearer_convex_step f f' (hf _ _ ?_ ?_)
      · exact Rat.cast_nonneg.mpr averageDegree_nonneg
      · exact Rat.cast_pos.mpr (lt_of_le_of_ne averageDegree_nonneg (fun a ↦ hd a.symm))



def SimpleGraphToGraph {V : Type} (G : SimpleGraph V) : Graph V (Sym2 V) where
  vertexSet     := ⊤
  IsLink        := fun e v w ↦ G.Adj v w ∧ e = s(v, w)
  isLink_symm   := fun _ _ _ _ ⟨hAdj, hevw⟩ ↦ ⟨hAdj.symm, by rw [hevw, Sym2.eq_swap]⟩
  eq_or_eq_of_isLink_of_isLink := by aesop
  left_mem_of_isLink := fun _ _ _ _ ↦ trivial

def IsLoopless {α β : Type} (G : Graph α β) : Prop := ∀ v, ¬ G.Adj v v
def HasNoMultiedge {α β : Type} (G : Graph α β) : Prop :=
  ∀ e₁ e₂ v w, G.IsLink e₁ v w → G.IsLink e₂ v w → e₁ = e₂

lemma SimpleGraphToGraphLoopless {V : Type} (G : SimpleGraph V) :
    IsLoopless (SimpleGraphToGraph G) := fun _ ⟨_, h, _⟩ ↦ G.loopless _ h

lemma SimpleGraphToGraphHasNoMultiedge {V : Type} (G : SimpleGraph V) :
    HasNoMultiedge (SimpleGraphToGraph G) := fun _ _ _ _ ⟨_, h₁⟩ ⟨_, h₂⟩ ↦ (by rw [h₁, h₂])

lemma SimpleGraphToGraphVertexset {V : Type} (G : SimpleGraph V) :
    (SimpleGraphToGraph G).vertexSet = ⊤ := rfl

def GraphToSimpleGraph {α β : Type} (G : Graph α β) (h : IsLoopless G)
    : SimpleGraph (G.vertexSet) where
  Adj      := fun v w ↦ G.Adj v w
  symm     := fun _ _ ⟨_, he⟩ ↦ ⟨_, G.isLink_symm (Graph.IsLink.edge_mem he) he⟩
  loopless := (h ·)

/- The vertices in S \ G.vertexSet form isolated vertices. -/
def GraphInduce {α β : Type} (G : Graph α β) (S : Set α) : Graph α β where
  vertexSet   := S
  IsLink      := fun e v w ↦ G.IsLink e v w ∧ v ∈ S ∧ w ∈ S
  isLink_symm := fun _ _ _ _ ⟨he, ⟨hv, hw⟩⟩ ↦ ⟨Graph.IsLink.symm he, ⟨hw, hv⟩⟩
  eq_or_eq_of_isLink_of_isLink :=
    fun _ _ _ _ _ ⟨h₁, ⟨_, _⟩⟩ ⟨h₂, ⟨_, _⟩⟩ ↦ G.eq_or_eq_of_isLink_of_isLink h₁ h₂
  left_mem_of_isLink := fun _ _ _ ⟨_, ⟨h, _⟩⟩ ↦ h

lemma GraphToSimpleGraphAdjIff {α β : Type} (G : Graph α β) (h : IsLoopless G) {v w : G.vertexSet} :
    (GraphToSimpleGraph G h).Adj v w ↔ G.Adj v w := by
  sorry

lemma SimpleGraphToGraphAdj {V : Type} (G : SimpleGraph V) {v w : V} :
    (SimpleGraphToGraph G).Adj v w ↔ G.Adj v w := by
  sorry

lemma AdjInduce {α β : Type} {v w : α} {G : Graph α β} {S : Set α}
    (hAdj : (GraphInduce G S).Adj v w) : G.Adj v w := by
  sorry

lemma AdjInduceIff {α β : Type} {v w : α} {G : Graph α β} {S : Set α} (hv : v ∈ S) (hw : w ∈ S) :
    (GraphInduce G S).Adj v w ↔ G.Adj v w := by
  sorry


lemma IsLooplessInduce {α β : Type} {G : Graph α β} (h : IsLoopless G) (S : Set α)
    : IsLoopless (GraphInduce G S)  := fun v hv ↦  h v (AdjInduce hv)

lemma SimpleGraphInduceEquiv {V : Type} (G : SimpleGraph V) (S : Set V) :
      G.induce S =
      GraphToSimpleGraph (GraphInduce (SimpleGraphToGraph G) S)
        (IsLooplessInduce (SimpleGraphToGraphLoopless G) S) := by
  ext v w
  rw [GraphToSimpleGraphAdjIff, AdjInduceIff v.2 w.2, comap_adj, SimpleGraphToGraphAdj]
  rfl



def IsIndependent {α β : Type} (G : Graph α β) (S : Set α) :=
  S ⊆ G.vertexSet ∧ ∀ e, ∀ x ∈ S, ∀ y ∈ S, ¬ G.IsLink e x y

lemma IsIndepSetEquiv {V : Type} (S : Set V) (G : SimpleGraph V)
    : G.IsIndepSet S ↔ IsIndependent (SimpleGraphToGraph G) S :=
  ⟨fun hI ↦ ⟨by intro _ _; trivial, fun _ _ hx _ hy hLink ↦ hI hx hy hLink.1.ne hLink.1⟩,
    fun ⟨hS, hnAdj⟩ v hvS w hwS hvw hvwAdj ↦ hnAdj _ _ hvS _ hwS ⟨hvwAdj, rfl⟩⟩

lemma IsIndependentFromAdj {α β : Type} (G : Graph α β) (S : Set α) :
    IsIndependent G S ↔ S ⊆ G.vertexSet ∧ ∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y := by
  sorry


lemma IsIndependentInduce {V : Type} (S : Set V) (I : Set S) (G : SimpleGraph V) :
    (G.induce S).IsIndepSet I ↔ G.IsIndepSet I := by
  simp_rw [IsIndepSet, comap_adj, Function.Embedding.subtype_apply]
  constructor
  · intro h _ hx _ hy hxy
    rw [Subtype.coe_image] at hx hy
    exact h hx.2 hy.2 (Subtype.coe_ne_coe.mp hxy)
  · intro h _ hx _ hy hxy
    exact h (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy) (Subtype.coe_ne_coe.mpr hxy)

lemma IsIndependentInduce' {V : Type} {S I : Set V} (hSI : I ⊆ S) (G : SimpleGraph V) :
    (G.induce S).IsIndepSet {x | x.1 ∈ I} ↔ G.IsIndepSet I := by
  rw [IsIndependentInduce, Subtype.coe_image_of_subset hSI]


lemma IsIndepSetInduceBijOn {V : Type} (S : Set V) (G : SimpleGraph V) :
    Set.BijOn (Subtype.val '' ·) {I | (G.induce S).IsIndepSet I} {I | G.IsIndepSet I ∧ I ⊆ S} :=
  ⟨ fun _ ↦ by simp [IsIndependentInduce],
    fun  _ _ _ _ ↦ by simp,
    fun I _ ↦ ⟨{x | x.1 ∈ I}, by simp_all [IsIndependentInduce']⟩⟩


variable (G) in
noncomputable def indepSetFinsetAll' : Finset (Set V) := {s | G.IsIndepSet s}

lemma indepSetFinsetAllEquivBijOn :
    Set.BijOn (·.toSet) {I | I ∈ G.indepSetFinsetAll} {I | I ∈ G.indepSetFinsetAll'} := by
  unfold indepSetFinsetAll indepSetFinsetAll'
  exact ⟨by intro _; simp, by simp, by intro x _; exact ⟨x.toFinset, by simp_all⟩ ⟩

lemma indepSetFinsetAllCardEquiv' : #G.indepSetFinsetAll = #G.indepSetFinsetAll' :=
  Set.BijOn.finsetCard_eq (·.toSet) indepSetFinsetAllEquivBijOn

lemma indepSetFinsetAllCardEquiv : #G.indepSetFinsetAll = #G.indepSetFinsetAll' := by
  unfold indepSetFinsetAll indepSetFinsetAll'
  refine Set.BijOn.finsetCard_eq (·.toSet) ⟨?_,?_,?_⟩
  · intro _; simp
  · simp
  · intro x _
    exact ⟨x.toFinset, by simp_all⟩

lemma test {p : V → Prop} (S : Finset V) : filter p S = S ∩ filter p univ := by
  ext _
  simp_all only [mem_filter, mem_inter, mem_univ, true_and]

lemma induced_inedependent_set_count' {V : Type} [Fintype V] (S : Set V) (G : SimpleGraph V) :
    #((G.induce S).indepSetFinsetAll') = #(filter (· ⊆ S) G.indepSetFinsetAll') :=
  Set.BijOn.finsetCard_eq _ (by convert IsIndepSetInduceBijOn S G <;> simp [indepSetFinsetAll'])


lemma filterCardEquiv {α β : Type} {f : α → β} {pα : α → Prop}
    {pβ : β → Prop} {S : Finset α} {T : Finset β} (hbi : Set.BijOn f S T)
    (fp : ∀ a, pα a ↔ pβ (f a)) : #(filter pα S) = #(filter pβ T) := by
  refine Set.BijOn.finsetCard_eq f ⟨?_,?_,?_⟩ <;> simp_rw [coe_filter, fp]
  · exact fun x hx ↦ ⟨hbi.1 hx.1, hx.2⟩
  · exact fun _ hx₁ _ hx₂ heq ↦ hbi.2.1 hx₁.1 hx₂.1 heq
  · intro _ hy
    have ⟨_, ⟨hxS, hxy⟩⟩ := hbi.2.2 hy.1
    subst hxy
    exact ⟨_, ⟨⟨hxS, hy.2⟩, rfl⟩⟩


lemma induced_inedependent_set_count'' {V : Type} [Fintype V] (S : Set V) (G : SimpleGraph V) :
    #((G.induce S).indepSetFinsetAll) = #(filter (·.toSet ⊆ S) G.indepSetFinsetAll) := by
  convert induced_inedependent_set_count' S G
  · exact indepSetFinsetAllCardEquiv
  · exact filterCardEquiv indepSetFinsetAllEquivBijOn (fun _ ↦ Eq.to_iff rfl)




scoped notation "E(" G ")" => SimpleGraph.edgeFinset G

scoped notation "d(" G ")" => averageDegree G

scoped notation "i(" G ")" => indepSetFinsetAll' G

-- This seems very ugly.
def VertexFinset {V : Type} [Fintype V] (G : SimpleGraph V) : Finset V := univ

scoped notation "V(" G ")" => VertexFinset G

scoped notation "α(" G ")" => indepNum G



example : #V(G) * d(G) = 2 * #E(G) := card_mul_averageDegree_eq_twice_card_edges

lemma shearer_convex_step' {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
  {H₁ : SimpleGraph V₁} {H₂ : SimpleGraph V₂} (f f' : ℝ → ℝ)
  (hf : f d(H₂) ≥ f d(H₁) + f' d(H₁) * (d(H₂) - d(H₁)))
  : #V(H₂) * f d(H₂) ≥ #V(H₁) * f d(H₁)
    + ((#V(H₁) - #V(H₂)) * (d(H₁) * f' d(H₁) - f d(H₁)) - 2 * (#E(H₁) - #E(H₂)) * f' d(H₁))
    := by sorry

lemma VG_rw : V(G) = univ := rfl


example {e : Sym2 V} : ∃ v w, e = s(v,w) := by
  refine (Sym2.exists).1 ⟨e, rfl⟩





variable (G) in
lemma induceEdgeMap (S : Set V) :
    map (Function.Embedding.subtype _).sym2Map E(G.induce S)
    = filter (fun e ↦ ∀ v ∈ e, v ∈ S) E(G) := by
  ext e
  constructor <;> simp_rw [mem_map, mem_filter, mem_edgeFinset]
  · intro ⟨e', ⟨he', hee'⟩⟩; subst hee'
    refine ⟨(Embedding.map_mem_edgeSet_iff (Embedding.induce _)).2 he', ?_⟩
    simp only [Function.Embedding.sym2Map_apply, Function.Embedding.subtype_apply,
      Sym2.mem_map, Subtype.exists, exists_and_right, exists_eq_right]
    exact fun _ ⟨h, _⟩ ↦ h
  · simp only [Function.Embedding.sym2Map_apply, Function.Embedding.subtype_apply, and_imp]
    intro he hev
    have ⟨v, w, hvwe⟩  := (Sym2.exists).1 ⟨e, rfl⟩; subst hvwe
    refine ⟨s(⟨v, hev _ (Sym2.mem_mk_left _ _)⟩, ⟨w, hev _ (Sym2.mem_mk_right _ _)⟩), he, by simp⟩


lemma averageDegree_induce_zero_from_averageDegree_zero (S : Set V) (h : d(G) = 0) :
    d(G.induce S) = 0 := by
  rw [←edge_card_zero_iff_average_degree_zero] at *
  have map_eq := induceEdgeMap G S
  rw [card_eq_zero] at h
  rw [h] at map_eq
  simp_all

variable (G) in
lemma induceEdgeCard (S : Set V) :
    #E(G.induce S) = #(filter (fun e ↦ ∀ v ∈ e, v ∈ S) E(G)) := by
  rw [←induceEdgeMap, card_map]



#check Set.toFinset_card

example {a b c : ℝ} : a = b - c ↔ a + c = b := by
  exact eq_sub_iff_add_eq

example {a b e : ℕ} (c d: ℝ) (hc : c = a) (hd : d = b) (he : e = a + b) : c + d = e := by
  rw [hc, hd, he]
  exact Eq.symm (Nat.cast_add a b)

example {S : Finset V} {p : V → Prop} : #S = #(filter p S) + #(filter (¬p ·) S) := by
  exact Eq.symm (filter_card_add_filter_neg_card_eq_card p)

lemma shearer_convex_step_induce (S : Set V) (f f' : ℝ → ℝ)
  (hf : ∀ x y, 0 ≤ x → 0 < y → f x ≥ f y + f' y * (x - y))
  : #V(G.induce S.compl) * f d(G.induce S.compl) ≥
      #V(G) * f d(G) + (#S.toFinset * (d(G) * f' d(G) - f d(G)) -
      2 * (#(filter (fun e ↦ ∃ v ∈ S, v ∈ e) E(G))) * f' d(G))
    := by
  convert shearer_convex_step' (H₁ := G) (H₂ := G.induce Sᶜ) f f' ?_
  · rw [eq_sub_iff_add_eq, VG_rw, Finset.card_univ, ←Set.toFinset_card, ←Nat.cast_add,
        Nat.cast_inj, VG_rw]
    convert filter_card_add_filter_neg_card_eq_card (· ∈ S) <;> (ext _; simp)
  · rw [eq_sub_iff_add_eq, ←Nat.cast_add, Nat.cast_inj]
    convert filter_card_add_filter_neg_card_eq_card (∃ v ∈ S, v ∈ ·)
    · convert (induceEdgeCard G Sᶜ)
      simp_rw [not_exists, not_and, Set.mem_compl_iff]
      constructor <;> exact fun hx _ hv hvS ↦ hx _ hvS hv
    · exact fun x ↦ instDecidableNot
  · by_cases hd : d(G) = 0
    · have this : ↑d(induce Sᶜ G) = 0 := by
        convert averageDegree_induce_zero_from_averageDegree_zero Sᶜ hd
      simp [hd, this]
    · apply hf
      -- Easy stuff; convert these lemma to have d(G) notation
      · sorry
      · sorry

lemma shearer_convex_step_fun (gS : V → Set V) {f f' : ℝ → ℝ}
  (hf : ∀ x y, 0 ≤ x → 0 < y → f x ≥ f y + f' y * (x - y))
  : 𝔼 v, #V(G.induce (gS v).compl) * f d(G.induce (gS v).compl) ≥
      #V(G) * f d(G) + (((𝔼 v, #(gS v).toFinset) : ℝ) * (d(G) * f' d(G) - f d(G)) -
      2 * ((𝔼 w, #(filter (fun e ↦ ∃ v ∈ (gS w), v ∈ e) E(G))) : ℝ) * f' d(G)) := by
  by_cases hV : Nonempty V
  · rw [←univ_nonempty_iff] at hV
    rw [ge_iff_le]
    convert expect_le_expect (s := univ)
      (hfg := (fun v _ ↦ shearer_convex_step_induce (G := G) (gS v) _ _ hf))
    rw [expect_add_distrib, expect_sub_distrib, expect_const hV, ←expect_mul, ←expect_mul,
    ←mul_expect]
  · simp_all [VG_rw]

lemma shearer_expectation_exterior_step''''
  {f f' : ℝ → ℝ}
  (hf : ∀ x y, 0 ≤ x → 0 < y → f x ≥ f y + f' y * (x - y))
  (hf' : 0 ≥ f' d(G))
  (hT : G.CliqueFree 3)
  (hV : Nonempty V)
  : 𝔼 v, #V(G.puncture v) * f d(G.puncture v) ≥
    #V(G) * f d(G) + ((d(G)+ 1) * (d(G) * f' d(G) - f d(G)) - 2 * d(G)^2 * f' d(G)) := by
  rw [ge_iff_le]
  convert le_trans ?_ (shearer_convex_step_fun (G.closedNeighborSet ·) hf)
  gcongr ?_ + (?_ - ?_)
  · exact le_refl _
  · apply le_of_eq
    congr
    -- These are the two lemmas
    sorry
  · rw [mul_assoc,mul_assoc]
    apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonpos_right ?_ hf') (by norm_num)
    -- These are the two lemmas
    sorry

lemma shearer_expectation_exterior_step'''
  {f f' : ℝ → ℝ}
  (hf : ∀ x y, 0 ≤ x → 0 < y → f x ≥ f y + f' y * (x - y))
  (hV : Nonempty V)
  : 𝔼 v, #V(G.delete_vtx v) * f d(G.delete_vtx v) ≥
    #V(G) * f d(G) + ((d(G) * f' d(G) - f d(G)) - 2 * d(G) * f' d(G)) := by
  rw [←one_mul (d(G) * f' d(G) - f d(G))]
  rw [←univ_nonempty_iff] at hV
  convert (shearer_convex_step_fun (G := G) (fun v ↦ {v}) hf)
  · simp [expect_const hV]
  · -- Degree
    sorry



lemma induced_inedependent_set_count''' {V : Type} [Fintype V] (S : Set V) (G : SimpleGraph V) :
    #i(G.induce S) = #(filter (· ⊆ S) i(G)) :=
  Set.BijOn.finsetCard_eq _ (by convert IsIndepSetInduceBijOn S G <;> simp [indepSetFinsetAll'])

lemma indepSetFinsetAll_is_indepSet' {W : Type} {H : SimpleGraph W} [Fintype W] (S : Set W) :
    S ∈ i(H) ↔ H.IsIndepSet S := by
  sorry

lemma indepSetFinsetAll_mem_mono {I₁ I₂ : Set V} (h : I₁ ⊆ I₂) (hI₂ : I₂ ∈ i(G)) :
    I₁ ∈ i(G) := by
  rw [indepSetFinsetAll_is_indepSet'] at *
  exact Set.Pairwise.mono h hI₂

lemma delete_vtx_indepSetCount'
    : #i(G.delete_vtx v) = #(filter (v ∉ ·) i(G)) := by
  convert induced_inedependent_set_count''' {v}ᶜ G using 4
  simp

lemma puncture_indepSetCount' : #i(G.puncture v) = #(filter (v ∈ ·) i(G)) := by
  convert induced_inedependent_set_count''' _ G using 1
  refine Set.BijOn.finsetCard_eq (· \ {v}) (Set.InvOn.bijOn (f' := (insert v ·)) ?_ ?_ ?_)
    <;> simp_rw [coe_filter, indepSetFinsetAll_is_indepSet']
  · refine ⟨by intro _ _; simp_all, ?_⟩
    intro I ⟨_,hI⟩;
    have _ : v ∉ I := fun hc ↦ not_mem_exterior_self (hI hc)
    simp_all
  · intro I ⟨hIi, hIv⟩
    refine ⟨Set.Pairwise.mono Set.diff_subset hIi, ?_⟩
    intro w ⟨hIw, hw⟩
    have hwv : v ≠ w := (fun a ↦ hw a.symm)
    exact mem_exterior_from_not_self_and_not_Adj hwv (hIi hIv hIw hwv)
  · intro _ ⟨hI, hIsub⟩
    refine ⟨isIndepSet_insert.2 ⟨hI, fun _ hu _ ↦ not_adj_of_mem_exterior (hIsub hu)⟩
            , by simp⟩

lemma indepSetCountRecursion : #i(G) = #i(G.puncture v) + #i(G.delete_vtx v) := by
  rw [←Finset.filter_card_add_filter_neg_card_eq_card (v ∈ ·), puncture_indepSetCount',
    delete_vtx_indepSetCount']


/-
  ## One more time.
-/

variable (G) in
noncomputable def extra (f f' : ℝ → ℝ) (a : ℝ) (b : ℝ) :=
  if Nonempty V then a * (d(G) * f' d(G) - f d(G)) + b * (- 2 * f' d(G))
                else 0

noncomputable def convexIneq (f f' : ℝ → ℝ) :=
    ∀ x y, 0 ≤ x → 0 < y → f x ≥ f y + f' y * (x - y)

variable (G) in
noncomputable def SetIncidenceFinset (S : Set V) := filter (∃ v ∈ S, v ∈ ·) E(G)


lemma extra_nonempty {f f' : ℝ → ℝ} {a : ℝ} {b : ℝ} (hV : Nonempty V) :
    extra G f f' a b = a * (d(G) * f' d(G) - f d(G)) + b * (- 2 * f' d(G)) :=
  if_pos hV

lemma card_mul_averageDegree_eq_twice_card_edges' :
   #V(G)  * d(G) = 2 * #E(G) := by sorry


lemma card_mul_averageDegree_eq_twice_card_edges_real' :
   #V(G)  * d(G) = 2 * (#E(G) : ℝ) :=  card_mul_averageDegree_eq_twice_card_edges_real



lemma averageDegree_nonneg' : 0 ≤ d(G) :=
  expect_nonneg (fun _ _ ↦ Nat.cast_nonneg' _)

lemma averageDegree_pos_from_nonzero (hd : d(G) ≠ 0) : 0 < d(G) :=
  lt_of_le_of_ne averageDegree_nonneg' hd.symm

lemma edgeFinset_empty_from_averageDegree_zero (hd : d(G) = 0) : E(G) = ∅ := by
  rw [←card_eq_zero, ←mul_eq_zero_iff_left (a := 2) (by norm_num)]
  -- Irritating rat cast stuff
  sorry

lemma SetIncidenceFinset_card_zero_from_averageDegree_zero
    (hd : d(G) = 0) (S : Set V) : #(G.SetIncidenceFinset S) = 0 := by
  simp [SetIncidenceFinset, edgeFinset_empty_from_averageDegree_zero hd]


variable (G) in
lemma extra_expect {f f' : ℝ → ℝ} {g₁ g₂ : V → ℝ} :
    𝔼 v, extra G f f' (g₁ v) (g₂ v) = extra G f f' (𝔼 v, g₁ v) (𝔼 v, g₂ v) := by
  unfold extra
  split_ifs
  · rw [expect_add_distrib, ←expect_mul, ←expect_mul]
  · exact expect_const_zero _


variable (G) in
lemma V_card_induce (S : Set V) : #V(G.induce S) = #S.toFinset := by simp [VG_rw]

variable (G) in
lemma V_card_sum (S : Set V) : #V(G) = #S.toFinset + #Sᶜ.toFinset := by
  convert (filter_card_add_filter_neg_card_eq_card (· ∈ S)).symm <;> (ext _; simp[VG_rw])

lemma shearer_convex_step₁ {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
    {H₁ : SimpleGraph V₁} {H₂ : SimpleGraph V₂} (f f' : ℝ → ℝ) (hf : convexIneq f f')
    (hdH₁ : 0 < d(H₁)) : #V(H₂) * f d(H₂) ≥
    #V(H₁) * f d(H₁) + extra H₁ f f' (#V(H₁) - #V(H₂)) (#E(H₁) - #E(H₂))
  := by
  have h_ineq := hf d(H₂) d(H₁) (Rat.cast_nonneg.2 averageDegree_nonneg) (Rat.cast_pos.2 hdH₁)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h_ineq (Nat.cast_nonneg _))
  rw [extra_nonempty (by sorry), ←mul_assoc, mul_comm (b := -2), neg_mul_comm, neg_sub,
      mul_sub (a := 2), ←card_mul_averageDegree_eq_twice_card_edges_real',
      ←card_mul_averageDegree_eq_twice_card_edges_real', ←sub_nonneg]
  convert le_refl _
  ring



lemma shearer_convex_step_induce₁ (S : Set V) {f f' : ℝ → ℝ} (hf : convexIneq f f')
  : #V(G.induce Sᶜ) * f d(G.induce Sᶜ) ≥ #V(G) * f d(G) +
    extra G f f' #S.toFinset #(G.SetIncidenceFinset S)  := by
    by_cases hd : d(G) = 0
    · simp_rw [hd]
      rw [SetIncidenceFinset_card_zero_from_averageDegree_zero hd, Nat.cast_zero,
          Rat.cast_zero]
      -- etc
      sorry
    · convert shearer_convex_step₁ (H₁ := G) (H₂ := G.induce Sᶜ) f f' hf
        (averageDegree_pos_from_nonzero hd) <;>
      rw [eq_sub_iff_add_eq, ←Nat.cast_add, Nat.cast_inj]
      · convert (V_card_sum G S).symm
        convert V_card_induce G _
      · convert (filter_card_add_filter_neg_card_eq_card (∃ v ∈ S, v ∈ ·) (s := E(G)))
        convert (induceEdgeCard G Sᶜ)
        simp_rw [not_exists, not_and, Set.mem_compl_iff]
        constructor <;> exact fun hx _ hv hvS ↦ hx _ hvS hv


variable (G) (v) in
theorem indepNum_puncture_succ_le' : α(G) ≥ α(G.induce (G.closedNeighborSet v)ᶜ) + 1 :=
    indepNum_puncture_succ_le G v














#check SimpleGraph.incidenceSet
