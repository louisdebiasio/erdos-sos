import Kalai.TightGrowth

namespace Kalai

universe u v

variable {Vertex : Type u} {Host : Type v}

def TightEdgeOrder (edges : List (List Vertex)) : Prop :=
  edges ≠ [] ∧ ∀ before edge after, edges = before ++ edge :: after → before ≠ [] →
    ∃ newVertex parent, parent ∈ before ∧ newVertex ∈ edge ∧ newVertex ∉ before.flatten ∧
      ∀ vertex ∈ edge, vertex ≠ newVertex → vertex ∈ parent

def IsTightTree (target : FiniteHypergraph Vertex) (uniformity : Nat) : Prop :=
  target.Uniform uniformity ∧
  (∀ vertex, vertex ∈ target.vertices ↔ ∃ edge ∈ target.edges, vertex ∈ edge) ∧
  ∃ ordering, ordering.Perm target.edges ∧ TightEdgeOrder ordering

noncomputable def graphFromEdges (edges : List (List Vertex))
    (distinct : ∀ edge ∈ edges, edge.Nodup)
    (simple : edges.Pairwise (fun first second => ¬ first.Perm second)) : FiniteHypergraph Vertex where
  vertices := uniqueItems edges.flatten
  edges := edges
  vertices_nodup := uniqueItems_nodup _
  edge_nodup := distinct
  edge_vertices := fun edge present _ inEdge =>
    (mem_uniqueItems _ _).mpr (List.mem_flatten.mpr ⟨edge, present, inEdge⟩)
  simple := simple

theorem graphFromEdges_vertex (edges : List (List Vertex)) (distinct simple) (vertex : Vertex) :
    vertex ∈ (graphFromEdges edges distinct simple).vertices ↔ vertex ∈ edges.flatten := mem_uniqueItems _ _

theorem graphFromEdges_edge (edges : List (List Vertex)) (distinct simple) (edge : List Vertex) :
    (graphFromEdges edges distinct simple).HasEdge edge ↔ ∃ stored ∈ edges, stored.Perm edge := Iff.rfl

theorem TightGrowth.congr {uniformity size : Nat} {target : FiniteHypergraph Vertex}
    (tree : TightGrowth uniformity target size) (other : FiniteHypergraph Vertex)
    (vertices : ∀ vertex, vertex ∈ other.vertices ↔ vertex ∈ target.vertices)
    (edges : ∀ edge, other.HasEdge edge ↔ target.HasEdge edge) : TightGrowth uniformity other size := by
  cases tree with
  | single target root data =>
    exact TightGrowth.single other root ⟨(edges root).mpr data.root_edge, data.root_length,
      fun vertex => (vertices vertex).trans (data.vertices vertex),
      fun edge present => (data.edge_iff edge).mp ((edges edge).mp (other.hasEdge_of_mem present))⟩
  | grow smaller target face oldEndpoint newVertex size tree extension =>
    exact TightGrowth.grow smaller other face oldEndpoint newVertex size tree
      ⟨extension.old_root, extension.fresh,
        fun vertex => (vertices vertex).trans (extension.vertices_added vertex),
        fun edge => (edges edge).trans (extension.edges_added edge)⟩

theorem list_snoc_induction {Item : Type u} (predicate : List Item → Prop)
    (empty : predicate []) (step : ∀ before last, predicate before → predicate (before ++ [last]))
    (items : List Item) : predicate items := by
  have reverseProof : ∀ reversed : List Item, predicate reversed.reverse := by
    intro reversed
    induction reversed with
    | nil => exact empty
    | cons head tail inductionHypothesis => simpa only [List.reverse_cons] using step tail.reverse head inductionHypothesis
  simpa only [List.reverse_reverse] using reverseProof items.reverse

theorem TightEdgeOrder.prefix {before : List (List Vertex)} {last : List Vertex}
    (ordered : TightEdgeOrder (before ++ [last])) (nonempty : before ≠ []) : TightEdgeOrder before := by
  refine ⟨nonempty, ?_⟩
  intro beginning edge suffix decomposition beginningNonempty
  exact ordered.2 beginning edge (suffix ++ [last]) (by simp only [decomposition, List.append_assoc, List.cons_append]) beginningNonempty

theorem orderedEdges_tightGrowth (uniformity : Nat) (edges : List (List Vertex))
    (distinct : ∀ edge ∈ edges, edge.Nodup)
    (simple : edges.Pairwise (fun first second => ¬ first.Perm second))
    (uniform : ∀ edge ∈ edges, edge.length = uniformity) (ordered : TightEdgeOrder edges) :
    TightGrowth uniformity (graphFromEdges edges distinct simple) edges.length := by
  classical
  induction edges using list_snoc_induction with
  | empty => exact False.elim (ordered.1 rfl)
  | step before last inductionHypothesis =>
    by_cases empty : before = []
    · subst before
      simp only [List.nil_append, List.length_cons, List.length_nil]
      apply TightGrowth.single _ last
      refine ⟨⟨last, List.mem_singleton_self last, List.Perm.refl _⟩, uniform last (by simp), ?_, ?_⟩
      · intro vertex
        rw [graphFromEdges_vertex]
        simp
      · intro edge present
        exact (List.mem_singleton.mp present) ▸ List.Perm.refl last
    · have beforeDistinct : ∀ edge ∈ before, edge.Nodup :=
        fun edge present => distinct edge (List.mem_append_left [last] present)
      have beforeSimple := (List.pairwise_append.mp simple).1
      have beforeUniform : ∀ edge ∈ before, edge.length = uniformity :=
        fun edge present => uniform edge (List.mem_append_left [last] present)
      let smaller := graphFromEdges before beforeDistinct beforeSimple
      let larger := graphFromEdges (before ++ [last]) distinct simple
      have smallerTree := inductionHypothesis beforeDistinct beforeSimple beforeUniform (ordered.prefix empty)
      obtain ⟨newVertex, parent, parentPresent, newPresent, fresh, contained⟩ :=
        ordered.2 before last [] (by simp) empty
      let face := last.erase newVertex
      have lastDistinct := distinct last (by simp)
      have faceDistinct : face.Nodup := lastDistinct.erase newVertex
      have lastLength := uniform last (by simp)
      have faceLength : face.length + 1 = uniformity := by
        have erased := List.length_erase_of_mem newPresent
        have positive := List.length_pos_of_mem newPresent
        change (last.erase newVertex).length + 1 = _
        omega
      have faceParent : ∀ vertex ∈ face, vertex ∈ parent := by
        intro vertex present
        have removed := lastDistinct.mem_erase_iff.mp present
        exact contained vertex removed.2 removed.1
      have uniformFace : smaller.Uniform (face.length + 1) := by
        rw [faceLength]
        exact beforeUniform
      obtain ⟨oldEndpoint, parentEdge⟩ :=
        (faceInShadow_iff_subset_edge smaller face.length uniformFace face faceDistinct rfl).mpr
          ⟨parent, parentPresent, faceParent⟩
      have lastOrder : last.Perm (face ++ [newVertex]) :=
        (List.perm_cons_erase newPresent).trans (List.perm_append_singleton newVertex face).symm
      have extension : LeafExtension smaller larger face oldEndpoint newVertex := by
        refine ⟨parentEdge, fun present => fresh ((graphFromEdges_vertex before beforeDistinct beforeSimple newVertex).mp present), ?_, ?_⟩
        · intro vertex
          rw [graphFromEdges_vertex, graphFromEdges_vertex]
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append]
          have lastMembership : vertex ∈ last ↔ vertex ∈ face ∨ vertex = newVertex := by
            rw [lastOrder.mem_iff]
            simp
          rw [lastMembership]
          constructor
          · rintro (present | inFace | same)
            · exact Or.inl present
            · exact Or.inl (List.mem_flatten.mpr ⟨parent, parentPresent, faceParent vertex inFace⟩)
            · exact Or.inr same
          · exact fun present => present.elim Or.inl (fun same => Or.inr (Or.inr same))
        · intro edge
          rw [graphFromEdges_edge, graphFromEdges_edge]
          constructor
          · rintro ⟨stored, present, ordering⟩
            rcases List.mem_append.mp present with old | newest
            · exact Or.inl ⟨stored, old, ordering⟩
            · have same := List.mem_singleton.mp newest
              subst stored
              exact Or.inr (ordering.symm.trans lastOrder)
          · rintro (⟨stored, present, ordering⟩ | ordering)
            · exact ⟨stored, List.mem_append_left [last] present, ordering⟩
            · exact ⟨last, by simp, lastOrder.trans ordering.symm⟩
      have result := TightGrowth.grow smaller larger face oldEndpoint newVertex before.length smallerTree extension
      simpa only [List.length_append, List.length_cons, List.length_nil] using result

theorem IsTightTree.growth {target : FiniteHypergraph Vertex} {uniformity : Nat}
    (tree : IsTightTree target uniformity) : TightGrowth uniformity target target.edges.length := by
  obtain ⟨uniform, covered, ordering, permutation, ordered⟩ := tree
  have distinct : ∀ edge ∈ ordering, edge.Nodup :=
    fun edge present => target.edge_nodup edge (permutation.mem_iff.mp present)
  have simple := permutation.symm.pairwise target.simple (fun different same => different same.symm)
  have built := orderedEdges_tightGrowth uniformity ordering distinct simple
    (fun edge present => uniform edge (permutation.mem_iff.mp present)) ordered
  have result := built.congr target (by
    intro vertex
    rw [covered, graphFromEdges_vertex, List.mem_flatten]
    exact ⟨fun ⟨edge, present, inEdge⟩ => ⟨edge, permutation.mem_iff.mpr present, inEdge⟩,
      fun ⟨edge, present, inEdge⟩ => ⟨edge, permutation.mem_iff.mp present, inEdge⟩⟩) (by
    intro edge
    rw [graphFromEdges_edge]
    exact ⟨fun ⟨stored, present, order⟩ => ⟨stored, permutation.mem_iff.mpr present, order⟩,
      fun ⟨stored, present, order⟩ => ⟨stored, permutation.mem_iff.mp present, order⟩⟩)
  exact permutation.length_eq ▸ result

theorem kalai_shadow_bound {target : FiniteHypergraph Vertex} {uniformity : Nat}
    (tree : IsTightTree target uniformity) (host : FiniteHypergraph Host)
    (atLeastTwo : 2 ≤ uniformity) (uniform : host.Uniform uniformity)
    (free : ¬ Nonempty (Embedding target host)) :
    uniformity * host.edges.length ≤ (target.edges.length - 1) * shadowCount host (uniformity - 1) :=
  tightGrowth_shadow_bound tree.growth host (by omega) uniform free

end Kalai
