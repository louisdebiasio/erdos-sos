import Kalai.KalaiTheorem

namespace Kalai

universe u v

variable {Vertex : Type u} {Host : Type v}

theorem tightEdgeOrder_of_index (edges : List (List Vertex)) (nonempty : edges ≠ [])
    (steps : ∀ position : Fin edges.length, position.val ≠ 0 →
      ∃ newVertex parent, parent ∈ edges.take position.val ∧ newVertex ∈ edges[position.val] ∧
        newVertex ∉ (edges.take position.val).flatten ∧
        ∀ vertex ∈ edges[position.val], vertex ≠ newVertex → vertex ∈ parent) : TightEdgeOrder edges := by
  refine ⟨nonempty, ?_⟩
  intro before edge after decomposition beforeNonempty
  have inBounds : before.length < edges.length := by
    simp only [decomposition, List.length_append, List.length_cons]
    omega
  have positionNonzero : before.length ≠ 0 := fun zero => beforeNonempty (List.length_eq_zero_iff.mp zero)
  have step := steps ⟨before.length, inBounds⟩ positionNonzero
  have preceding : edges.take before.length = before := by rw [decomposition, List.take_left]
  have current : edges[before.length] = edge := by
    simp only [decomposition, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
  simpa only [preceding, current] using step

theorem LeafExtension.vertex_count {smaller larger : FiniteHypergraph Vertex} {face : List Vertex}
    {oldEndpoint newVertex : Vertex} (extension : LeafExtension smaller larger face oldEndpoint newVertex) :
    larger.vertices.length = smaller.vertices.length + 1 := by
  have ordering := perm_of_nodup_membership larger.vertices (newVertex :: smaller.vertices)
    larger.vertices_nodup (List.nodup_cons.mpr ⟨extension.fresh, smaller.vertices_nodup⟩)
    (fun vertex => by rw [extension.vertices_added]; simp only [List.mem_cons, or_comm])
  exact ordering.length_eq

theorem TightGrowth.vertex_count {uniformity size : Nat} {target : FiniteHypergraph Vertex}
    (tree : TightGrowth uniformity target size) : target.vertices.length + 1 = size + uniformity := by
  induction tree with
  | single target root data =>
    have ordering := perm_of_nodup_membership target.vertices root target.vertices_nodup
      (target.hasEdge_nodup data.root_edge) data.vertices
    have lengthEq := ordering.length_eq.trans data.root_length
    omega
  | grow smaller larger face oldEndpoint newVertex size tree extension inductionHypothesis =>
    rw [extension.vertex_count]
    omega

theorem IsTightTree.vertex_count {uniformity : Nat} {target : FiniteHypergraph Vertex}
    (tree : IsTightTree target uniformity) : target.vertices.length + 1 = target.edges.length + uniformity :=
  tree.growth.vertex_count

theorem Embedding.vertex_count_le {target : FiniteHypergraph Vertex} {host : FiniteHypergraph Host}
    (embedding : Embedding target host) : target.vertices.length ≤ host.vertices.length := by
  have distinct : (target.vertices.map embedding.toFun).Nodup := by
    change (target.vertices.map embedding.toFun).Pairwise (fun first second => first ≠ second)
    rw [List.pairwise_map]
    exact target.vertices_nodup.imp_of_mem (fun firstPresent secondPresent different same =>
      different (embedding.injective _ firstPresent _ secondPresent same))
  have bound := nodup_length_le_of_subset (target.vertices.map embedding.toFun) host.vertices distinct (by
    intro image present
    obtain ⟨vertex, inTarget, same⟩ := List.mem_map.mp present
    exact same ▸ embedding.maps_vertices vertex inTarget)
  simpa only [List.length_map] using bound

theorem no_embedding_of_too_many_vertices (target : FiniteHypergraph Vertex) (host : FiniteHypergraph Host)
    (tooLarge : host.vertices.length < target.vertices.length) : ¬ Nonempty (Embedding target host) := by
  rintro ⟨embedding⟩
  have bound := embedding.vertex_count_le
  omega

theorem kalai_master {target : FiniteHypergraph Vertex} {uniformity : Nat}
    (tree : IsTightTree target uniformity) (root : List Vertex) (rootEdge : target.HasEdge root)
    (host : FiniteHypergraph Host) (atLeastTwo : 2 ≤ uniformity) (uniform : host.Uniform uniformity) :
    edgeStateCount host ≤ globalSupportCount target host root +
      (target.edges.length - 1) * shadowPermutationCount host (uniformity - 1) :=
  rootedConstruction_master (tree.growth.rooted root rootEdge) host (by omega) uniform

end Kalai
