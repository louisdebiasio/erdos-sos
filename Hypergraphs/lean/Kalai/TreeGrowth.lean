import Kalai.RootedConstruction

namespace Kalai

universe u

variable {Vertex : Type u}

def singleEdgeGraph (root : List Vertex) (distinct : root.Nodup) : FiniteHypergraph Vertex where
  vertices := root
  edges := [root]
  vertices_nodup := distinct
  edge_nodup := by intro edge present; simpa only [List.mem_singleton.mp present] using distinct
  edge_vertices := by intro edge present vertex inEdge; simpa only [List.mem_singleton.mp present] using inEdge
  simple := by simp

theorem singleEdgeGraph_hasEdge (root : List Vertex) (distinct : root.Nodup) (edge : List Vertex) :
    (singleEdgeGraph root distinct).HasEdge edge ↔ edge.Perm root := by
  simp [FiniteHypergraph.HasEdge, singleEdgeGraph, List.perm_comm]

theorem singleEdgeGraph_single (root : List Vertex) (distinct : root.Nodup) :
    SingleRoot (singleEdgeGraph root distinct) root root.length :=
  ⟨(singleEdgeGraph root distinct).hasEdge_of_mem (by simp [singleEdgeGraph]), rfl,
    fun _ => Iff.rfl, fun _ present => (List.mem_singleton.mp present) ▸ List.Perm.refl root⟩

theorem SingleRoot.edge_iff {target : FiniteHypergraph Vertex} {root : List Vertex} {uniformity : Nat}
    (single : SingleRoot target root uniformity) (edge : List Vertex) : target.HasEdge edge ↔ edge.Perm root := by
  constructor
  · rintro ⟨stored, present, ordering⟩
    exact ordering.symm.trans (single.edges stored present)
  · intro ordering
    exact (target.hasEdge_perm ordering).mpr single.root_edge

def growGraph (smaller : FiniteHypergraph Vertex) (face : List Vertex) (oldEndpoint newVertex : Vertex)
    (parent : smaller.HasEdge (face ++ [oldEndpoint])) (fresh : newVertex ∉ smaller.vertices) :
    FiniteHypergraph Vertex where
  vertices := newVertex :: smaller.vertices
  edges := (face ++ [newVertex]) :: smaller.edges
  vertices_nodup := List.nodup_cons.mpr ⟨fresh, smaller.vertices_nodup⟩
  edge_nodup := by
    intro edge present
    rcases List.mem_cons.mp present with rfl | oldEdge
    · apply List.pairwise_append.mpr
      refine ⟨List.Sublist.nodup (List.sublist_append_left face [oldEndpoint]) (smaller.hasEdge_nodup parent),
        by simp, ?_⟩
      intro first inFace second inSingleton same
      have isNew := List.mem_singleton.mp inSingleton
      exact fresh ((same.trans isNew) ▸ smaller.hasEdge_vertex parent (List.mem_append_left [oldEndpoint] inFace))
    · exact smaller.edge_nodup edge oldEdge
  edge_vertices := by
    intro edge present vertex inEdge
    rcases List.mem_cons.mp present with rfl | oldEdge
    · rcases List.mem_append.mp inEdge with inFace | inSingleton
      · exact List.mem_cons_of_mem newVertex (smaller.hasEdge_vertex parent (List.mem_append_left [oldEndpoint] inFace))
      · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp inSingleton))
    · exact List.mem_cons_of_mem newVertex (smaller.edge_vertices edge oldEdge vertex inEdge)
  simple := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, smaller.simple⟩
    intro edge present ordering
    exact fresh (smaller.edge_vertices edge present newVertex
      (ordering.mem_iff.mp (List.mem_append_right face (by simp))))

theorem growGraph_extension (smaller : FiniteHypergraph Vertex) (face : List Vertex) (oldEndpoint newVertex : Vertex)
    (parent : smaller.HasEdge (face ++ [oldEndpoint])) (fresh : newVertex ∉ smaller.vertices) :
    LeafExtension smaller (growGraph smaller face oldEndpoint newVertex parent fresh) face oldEndpoint newVertex where
  old_root := parent
  fresh := fresh
  vertices_added := by intro vertex; simp [growGraph, or_comm]
  edges_added := by
    intro edge
    simp only [FiniteHypergraph.HasEdge, growGraph, List.mem_cons]
    constructor
    · rintro ⟨stored, rfl | present, ordering⟩
      · exact Or.inr ordering.symm
      · exact Or.inl ⟨stored, present, ordering⟩
    · rintro (⟨stored, present, ordering⟩ | ordering)
      · exact ⟨stored, Or.inr present, ordering⟩
      · exact ⟨face ++ [newVertex], Or.inl rfl, ordering.symm⟩

theorem LeafExtension.new_root {smaller larger : FiniteHypergraph Vertex} {face : List Vertex}
    {oldEndpoint newVertex : Vertex} (extension : LeafExtension smaller larger face oldEndpoint newVertex) :
    larger.HasEdge (face ++ [newVertex]) := (extension.edges_added _).mpr (Or.inr (List.Perm.refl _))

theorem LeafExtension.uniform {smaller larger : FiniteHypergraph Vertex} {face : List Vertex}
    {oldEndpoint newVertex : Vertex} (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (uniformity : Nat) (uniform : smaller.Uniform uniformity) : larger.Uniform uniformity := by
  intro edge present
  rcases (extension.edges_added edge).mp (larger.hasEdge_of_mem present) with oldEdge | newEdge
  · exact smaller.hasEdge_length uniform oldEdge
  · have rootSize := smaller.hasEdge_length uniform extension.old_root
    have newSize : (face ++ [newVertex]).length = uniformity := by
      simpa only [List.length_append, List.length_cons, List.length_nil] using rootSize
    exact newEdge.length_eq.trans newSize

theorem RootedConstruction.uniform {uniformity size : Nat} {target : FiniteHypergraph Vertex}
    {root : List Vertex} (built : RootedConstruction uniformity target root size) : target.Uniform uniformity := by
  induction built with
  | single target root data => exact fun edge present => (data.edges edge present).length_eq.trans data.root_length
  | leaf smaller larger face oldEndpoint newVertex size built extension inductionHypothesis =>
    exact extension.uniform uniformity inductionHypothesis
  | glue first second joined root firstSize secondSize firstBuilt secondBuilt amalgam firstIH secondIH =>
    intro edge present
    rcases (amalgam.edges_union edge).mp (joined.hasEdge_of_mem present) with inFirst | inSecond
    · exact first.hasEdge_length firstIH inFirst
    · exact second.hasEdge_length secondIH inSecond
  | reorder target root otherRoot size built ordering inductionHypothesis => exact inductionHypothesis

end Kalai
