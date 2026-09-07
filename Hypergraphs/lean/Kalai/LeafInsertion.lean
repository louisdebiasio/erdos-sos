import Kalai.TreeGrowth

namespace Kalai

universe u

variable {Vertex : Type u}

theorem LeafExtension.old_endpoint {smaller larger : FiniteHypergraph Vertex} {face : List Vertex}
    {oldEndpoint newVertex : Vertex} (extension : LeafExtension smaller larger face oldEndpoint newVertex) :
    oldEndpoint ∈ smaller.vertices := smaller.hasEdge_vertex extension.old_root (by simp)

theorem LeafExtension.old_not_face {smaller larger : FiniteHypergraph Vertex} {face : List Vertex}
    {oldEndpoint newVertex : Vertex} (extension : LeafExtension smaller larger face oldEndpoint newVertex) :
    oldEndpoint ∉ face := by
  have distinct := smaller.hasEdge_nodup extension.old_root
  exact fun present => (List.pairwise_append.mp distinct).2.2 oldEndpoint present oldEndpoint (by simp) rfl

theorem singleRoot_insert {uniformity : Nat} {smaller larger : FiniteHypergraph Vertex}
    {root face : List Vertex} {oldEndpoint newVertex : Vertex}
    (single : SingleRoot smaller root uniformity)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex) :
    RootedConstruction uniformity larger root 2 := by
  have parentOrder := (single.edge_iff _).mp extension.old_root
  have oldVertices : ∀ vertex, vertex ∈ smaller.vertices ↔ vertex ∈ face ∨ vertex = oldEndpoint := by
    intro vertex
    rw [single.vertices vertex, ← parentOrder.mem_iff]
    simp
  let freshRoot := face ++ [newVertex]
  have distinct := larger.hasEdge_nodup extension.new_root
  let freshSingle := singleEdgeGraph freshRoot distinct
  have freshLength : freshRoot.length = uniformity := by
    have lengthEq := parentOrder.length_eq.trans single.root_length
    simpa only [freshRoot, List.length_append, List.length_cons, List.length_nil] using lengthEq
  have reverse : LeafExtension freshSingle larger face newVertex oldEndpoint := by
    refine ⟨(singleEdgeGraph_hasEdge freshRoot distinct _).mpr (List.Perm.refl _), ?_, ?_, ?_⟩
    · change oldEndpoint ∉ face ++ [newVertex]
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨extension.old_not_face, fun same => extension.fresh (same ▸ extension.old_endpoint)⟩
    · intro vertex
      rw [extension.vertices_added, oldVertices]
      change (vertex ∈ face ∨ vertex = oldEndpoint) ∨ vertex = newVertex ↔
        vertex ∈ face ++ [newVertex] ∨ vertex = oldEndpoint
      simp only [List.mem_append, List.mem_singleton, or_assoc, or_left_comm, or_comm]
    · intro edge
      rw [extension.edges_added, single.edge_iff]
      have oldOrder : edge.Perm root ↔ edge.Perm (face ++ [oldEndpoint]) :=
        ⟨fun ordering => ordering.trans parentOrder.symm, fun ordering => ordering.trans parentOrder⟩
      rw [oldOrder, singleEdgeGraph_hasEdge]
      exact or_comm
  have freshData : SingleRoot freshSingle freshRoot uniformity := by
    have data := singleEdgeGraph_single freshRoot distinct
    exact ⟨data.root_edge, freshLength, data.vertices, data.edges⟩
  exact RootedConstruction.reorder larger (face ++ [oldEndpoint]) root 2
    (RootedConstruction.leaf freshSingle larger face newVertex oldEndpoint 1
      (RootedConstruction.single freshSingle freshRoot freshData) reverse) parentOrder

theorem RootedConstruction.insert_at_root {uniformity size : Nat}
    {smaller larger : FiniteHypergraph Vertex} {root face : List Vertex} {oldEndpoint newVertex : Vertex}
    (built : RootedConstruction uniformity smaller root size)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (parentOrder : (face ++ [oldEndpoint]).Perm root) :
    RootedConstruction uniformity larger root (size + 1) := by
  let rootGraph := singleEdgeGraph root (smaller.hasEdge_nodup built.root_spec.1)
  have parent : rootGraph.HasEdge (face ++ [oldEndpoint]) := (singleEdgeGraph_hasEdge _ _ _).mpr parentOrder
  have fresh : newVertex ∉ rootGraph.vertices := fun present =>
    extension.fresh (smaller.hasEdge_vertex built.root_spec.1 present)
  let branch := growGraph rootGraph face oldEndpoint newVertex parent fresh
  have branchExtension := growGraph_extension rootGraph face oldEndpoint newVertex parent fresh
  have rootData : SingleRoot rootGraph root uniformity := by
    have data := singleEdgeGraph_single root (smaller.hasEdge_nodup built.root_spec.1)
    exact ⟨data.root_edge, built.root_spec.2.1, data.vertices, data.edges⟩
  have branchBuilt := singleRoot_insert rootData branchExtension
  have amalgam : EdgeAmalgam smaller branch larger root := by
    refine ⟨?_, ?_, ?_, built.root_spec.1, ?_⟩
    · intro vertex
      rw [extension.vertices_added, branchExtension.vertices_added]
      change vertex ∈ smaller.vertices ∨ vertex = newVertex ↔
        vertex ∈ smaller.vertices ∨ vertex ∈ root ∨ vertex = newVertex
      constructor
      · exact fun present => present.elim Or.inl (fun same => Or.inr (Or.inr same))
      · rintro (present | inRoot | same)
        · exact Or.inl present
        · exact Or.inl (smaller.hasEdge_vertex built.root_spec.1 inRoot)
        · exact Or.inr same
    · intro vertex
      rw [branchExtension.vertices_added]
      change (vertex ∈ smaller.vertices ∧ (vertex ∈ root ∨ vertex = newVertex)) ↔ vertex ∈ root
      constructor
      · rintro ⟨present, inRoot | same⟩
        · exact inRoot
        · exact False.elim (extension.fresh (same ▸ present))
      · exact fun present => ⟨smaller.hasEdge_vertex built.root_spec.1 present, Or.inl present⟩
    · intro edge
      rw [extension.edges_added, branchExtension.edges_added, singleEdgeGraph_hasEdge]
      constructor
      · exact fun present => present.elim Or.inl (fun ordering => Or.inr (Or.inr ordering))
      · rintro (present | ordering | newOrder)
        · exact Or.inl present
        · exact Or.inl ((smaller.hasEdge_perm ordering).mpr built.root_spec.1)
        · exact Or.inr newOrder
    · exact (branchExtension.edges_added root).mpr (Or.inl rootData.root_edge)
  have result := RootedConstruction.glue smaller branch larger root size 2 built branchBuilt amalgam
  have sizeEq : size + 2 - 1 = size + 1 := by omega
  exact sizeEq ▸ result

theorem LeafExtension.commute {base first final : FiniteHypergraph Vertex}
    {face nextFace : List Vertex} {oldEndpoint firstNew nextOld nextNew : Vertex}
    (firstExtension : LeafExtension base first face oldEndpoint firstNew)
    (nextExtension : LeafExtension first final nextFace nextOld nextNew)
    (parent : base.HasEdge (nextFace ++ [nextOld])) :
    ∃ middle : FiniteHypergraph Vertex,
      LeafExtension base middle nextFace nextOld nextNew ∧
      LeafExtension middle final face oldEndpoint firstNew := by
  have fresh : nextNew ∉ base.vertices := fun present =>
    nextExtension.fresh ((firstExtension.vertices_added _).mpr (Or.inl present))
  let middle := growGraph base nextFace nextOld nextNew parent fresh
  have middleExtension := growGraph_extension base nextFace nextOld nextNew parent fresh
  refine ⟨middle, middleExtension, ?_⟩
  refine ⟨(middleExtension.edges_added _).mpr (Or.inl firstExtension.old_root), ?_, ?_, ?_⟩
  · intro present
    rcases (middleExtension.vertices_added _).mp present with inBase | same
    · exact firstExtension.fresh inBase
    · exact nextExtension.fresh (same ▸ (firstExtension.vertices_added _).mpr (Or.inr rfl))
  · intro vertex
    rw [nextExtension.vertices_added, firstExtension.vertices_added, middleExtension.vertices_added]
    simp only [or_assoc, or_left_comm, or_comm]
  · intro edge
    rw [nextExtension.edges_added, firstExtension.edges_added, middleExtension.edges_added]
    simp only [or_assoc, or_left_comm, or_comm]

theorem EdgeAmalgam.swap {first second joined : FiniteHypergraph Vertex} {root : List Vertex}
    (amalgam : EdgeAmalgam first second joined root) : EdgeAmalgam second first joined root :=
  ⟨fun vertex => (amalgam.vertices_union vertex).trans or_comm,
    fun vertex => and_comm.trans (amalgam.vertices_intersection vertex),
    fun edge => (amalgam.edges_union edge).trans or_comm, amalgam.second_root, amalgam.first_root⟩

theorem EdgeAmalgam.insert_first {first second joined larger : FiniteHypergraph Vertex}
    {root face : List Vertex} {oldEndpoint newVertex : Vertex}
    (amalgam : EdgeAmalgam first second joined root)
    (extension : LeafExtension joined larger face oldEndpoint newVertex)
    (parent : first.HasEdge (face ++ [oldEndpoint])) :
    ∃ middle : FiniteHypergraph Vertex,
      LeafExtension first middle face oldEndpoint newVertex ∧ EdgeAmalgam middle second larger root := by
  have fresh : newVertex ∉ first.vertices := fun present =>
    extension.fresh ((amalgam.vertices_union _).mpr (Or.inl present))
  have notSecond : newVertex ∉ second.vertices := fun present =>
    extension.fresh ((amalgam.vertices_union _).mpr (Or.inr present))
  let middle := growGraph first face oldEndpoint newVertex parent fresh
  have middleExtension := growGraph_extension first face oldEndpoint newVertex parent fresh
  refine ⟨middle, middleExtension, ?_⟩
  refine ⟨?_, ?_, ?_, (middleExtension.edges_added _).mpr (Or.inl amalgam.first_root), amalgam.second_root⟩
  · intro vertex
    rw [extension.vertices_added, amalgam.vertices_union, middleExtension.vertices_added]
    simp only [or_assoc, or_left_comm, or_comm]
  · intro vertex
    rw [middleExtension.vertices_added, or_and_right]
    have impossible : ¬ (vertex = newVertex ∧ vertex ∈ second.vertices) :=
      fun present => notSecond (present.1 ▸ present.2)
    rw [or_iff_left impossible]
    exact amalgam.vertices_intersection vertex
  · intro edge
    rw [extension.edges_added, amalgam.edges_union, middleExtension.edges_added]
    simp only [or_assoc, or_left_comm, or_comm]

theorem RootedConstruction.insert_leaf {uniformity size : Nat} {smaller : FiniteHypergraph Vertex}
    {root : List Vertex} (built : RootedConstruction uniformity smaller root size)
    (larger : FiniteHypergraph Vertex) (face : List Vertex) (oldEndpoint newVertex : Vertex)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex) :
    RootedConstruction uniformity larger root (size + 1) := by
  induction built generalizing larger face oldEndpoint newVertex with
  | single target root data => exact singleRoot_insert data extension
  | leaf base target rootFace rootOld rootNew baseSize baseBuilt rootExtension inductionHypothesis =>
    rcases (rootExtension.edges_added _).mp extension.old_root with inBase | atRoot
    · obtain ⟨middle, middleExtension, lastExtension⟩ := rootExtension.commute extension inBase
      exact RootedConstruction.leaf middle larger rootFace rootOld rootNew (baseSize + 1)
        (inductionHypothesis middle face oldEndpoint newVertex middleExtension) lastExtension
    · exact (RootedConstruction.leaf base target rootFace rootOld rootNew baseSize baseBuilt rootExtension).insert_at_root extension atRoot
  | glue first second joined root firstSize secondSize firstBuilt secondBuilt amalgam firstIH secondIH =>
    have firstPositive := firstBuilt.root_spec.2.2
    have secondPositive := secondBuilt.root_spec.2.2
    rcases (amalgam.edges_union _).mp extension.old_root with inFirst | inSecond
    · obtain ⟨middle, middleExtension, nextAmalgam⟩ := amalgam.insert_first extension inFirst
      have result := RootedConstruction.glue middle second larger root (firstSize + 1) secondSize
        (firstIH middle face oldEndpoint newVertex middleExtension) secondBuilt nextAmalgam
      have sizeEq : firstSize + 1 + secondSize - 1 = firstSize + secondSize - 1 + 1 := by omega
      exact sizeEq ▸ result
    · obtain ⟨middle, middleExtension, nextAmalgam⟩ := amalgam.swap.insert_first extension inSecond
      have result := RootedConstruction.glue first middle larger root firstSize (secondSize + 1)
        firstBuilt (secondIH middle face oldEndpoint newVertex middleExtension) nextAmalgam.swap
      have sizeEq : firstSize + (secondSize + 1) - 1 = firstSize + secondSize - 1 + 1 := by omega
      exact sizeEq ▸ result
  | reorder target root otherRoot size built ordering inductionHypothesis =>
    exact RootedConstruction.reorder larger root otherRoot (size + 1)
      (inductionHypothesis larger face oldEndpoint newVertex extension) ordering

end Kalai
