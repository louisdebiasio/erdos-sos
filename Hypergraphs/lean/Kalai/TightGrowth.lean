import Kalai.LeafInsertion

namespace Kalai

universe u v

variable {Vertex : Type u} {Host : Type v}

theorem SingleRoot.edge_count {target : FiniteHypergraph Vertex} {root : List Vertex} {uniformity : Nat}
    (single : SingleRoot target root uniformity) : target.edges.length = 1 := by
  have uniform : target.Uniform uniformity := fun edge present =>
    (single.edges edge present).length_eq.trans single.root_length
  have same := (orderedEdgeListing target).card_eq_of_iff (orderingUniverse root) single.edge_iff
  rw [orderedEdgeListing_card target uniformity uniform,
    orderingUniverse_card_factorial root (target.hasEdge_nodup single.root_edge), single.root_length] at same
  apply Nat.mul_right_cancel (factorial_positive uniformity)
  simpa using same

theorem LeafExtension.edge_count {smaller larger : FiniteHypergraph Vertex} {face : List Vertex}
    {oldEndpoint newVertex : Vertex} (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (uniformity : Nat) (uniform : smaller.Uniform uniformity) : larger.edges.length = smaller.edges.length + 1 := by
  have separated : ∀ edge, smaller.HasEdge edge → ¬ edge.Perm (face ++ [newVertex]) := by
    intro edge present ordering
    exact extension.fresh (smaller.hasEdge_vertex present
      (ordering.mem_iff.mpr (List.mem_append_right face (by simp))))
  have oldPart := ((orderedEdgeListing larger).restrict smaller.HasEdge).card_eq_of_iff
    (orderedEdgeListing smaller) (fun edge => by
      constructor
      · exact And.right
      · exact fun present => ⟨(extension.edges_added edge).mpr (Or.inl present), present⟩)
  have newPart := ((orderedEdgeListing larger).restrict (fun edge => ¬ smaller.HasEdge edge)).card_eq_of_iff
    (orderingUniverse (face ++ [newVertex])) (fun edge => by
      constructor
      · intro present
        exact ((extension.edges_added edge).mp present.1).resolve_left present.2
      · intro ordering
        exact ⟨(extension.edges_added edge).mpr (Or.inr ordering), fun present => separated edge present ordering⟩)
  have split := (orderedEdgeListing larger).restrict_card_complement smaller.HasEdge
  rw [oldPart, newPart, orderingUniverse_card_factorial _ (larger.hasEdge_nodup extension.new_root),
    orderedEdgeListing_card smaller uniformity uniform,
    orderedEdgeListing_card larger uniformity (extension.uniform uniformity uniform)] at split
  have newSize := larger.hasEdge_length (extension.uniform uniformity uniform) extension.new_root
  rw [newSize] at split
  apply Nat.mul_right_cancel (factorial_positive uniformity)
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using split.symm

inductive TightGrowth (uniformity : Nat) : FiniteHypergraph Vertex → Nat → Prop where
  | single (target : FiniteHypergraph Vertex) (root : List Vertex)
      (data : SingleRoot target root uniformity) : TightGrowth uniformity target 1
  | grow (smaller larger : FiniteHypergraph Vertex) (face : List Vertex) (oldEndpoint newVertex : Vertex)
      (size : Nat) (tree : TightGrowth uniformity smaller size)
      (extension : LeafExtension smaller larger face oldEndpoint newVertex) :
      TightGrowth uniformity larger (size + 1)

theorem TightGrowth.rooted {uniformity size : Nat} {target : FiniteHypergraph Vertex}
    (tree : TightGrowth uniformity target size) (root : List Vertex) (rootEdge : target.HasEdge root) :
    RootedConstruction uniformity target root size := by
  induction tree generalizing root with
  | single target baseRoot data =>
    exact RootedConstruction.reorder target baseRoot root 1
      (RootedConstruction.single target baseRoot data) ((data.edge_iff root).mp rootEdge).symm
  | grow smaller larger face oldEndpoint newVertex size tree extension inductionHypothesis =>
    rcases (extension.edges_added root).mp rootEdge with oldRoot | newRoot
    · exact (inductionHypothesis root oldRoot).insert_leaf larger face oldEndpoint newVertex extension
    · exact RootedConstruction.reorder larger (face ++ [newVertex]) root (size + 1)
        (RootedConstruction.leaf smaller larger face oldEndpoint newVertex size
          (inductionHypothesis (face ++ [oldEndpoint]) extension.old_root) extension) newRoot.symm

theorem TightGrowth.nonempty {uniformity size : Nat} {target : FiniteHypergraph Vertex}
    (tree : TightGrowth uniformity target size) : ∃ root, target.HasEdge root := by
  cases tree with
  | single target root data => exact ⟨root, data.root_edge⟩
  | grow smaller larger face oldEndpoint newVertex size tree extension => exact ⟨face ++ [newVertex], extension.new_root⟩

theorem TightGrowth.uniform {uniformity size : Nat} {target : FiniteHypergraph Vertex}
    (tree : TightGrowth uniformity target size) : target.Uniform uniformity := by
  obtain ⟨root, present⟩ := tree.nonempty
  exact (tree.rooted root present).uniform

theorem TightGrowth.edge_count {uniformity size : Nat} {target : FiniteHypergraph Vertex}
    (tree : TightGrowth uniformity target size) : target.edges.length = size := by
  induction tree with
  | single target root data => exact data.edge_count
  | grow smaller larger face oldEndpoint newVertex size tree extension inductionHypothesis =>
    rw [extension.edge_count uniformity tree.uniform, inductionHypothesis]

theorem tightGrowth_shadow_bound {uniformity size : Nat} {target : FiniteHypergraph Vertex}
    (tree : TightGrowth uniformity target size) (host : FiniteHypergraph Host)
    (positive : 0 < uniformity) (uniform : host.Uniform uniformity)
    (free : ¬ Nonempty (Embedding target host)) :
    uniformity * host.edges.length ≤ (target.edges.length - 1) * shadowCount host (uniformity - 1) := by
  obtain ⟨root, present⟩ := tree.nonempty
  rw [tree.edge_count]
  exact rootedConstruction_shadow_bound (tree.rooted root present) host positive uniform free

end Kalai
