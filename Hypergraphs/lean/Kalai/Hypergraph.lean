import Std

namespace Kalai

universe u v

structure FiniteHypergraph (Vertex : Type u) where
  vertices : List Vertex
  edges : List (List Vertex)
  vertices_nodup : vertices.Nodup
  edge_nodup : ∀ edge, edge ∈ edges → edge.Nodup
  edge_vertices : ∀ edge, edge ∈ edges → ∀ vertex, vertex ∈ edge → vertex ∈ vertices
  simple : edges.Pairwise (fun first second => ¬ first.Perm second)

namespace FiniteHypergraph

variable {Vertex : Type u}

def HasEdge (graph : FiniteHypergraph Vertex) (edge : List Vertex) : Prop :=
  ∃ stored, stored ∈ graph.edges ∧ stored.Perm edge

def Uniform (graph : FiniteHypergraph Vertex) (uniformity : Nat) : Prop :=
  ∀ edge, edge ∈ graph.edges → edge.length = uniformity

theorem hasEdge_of_mem (graph : FiniteHypergraph Vertex) {edge : List Vertex}
    (listed : edge ∈ graph.edges) : graph.HasEdge edge :=
  ⟨edge, listed, List.Perm.refl edge⟩

theorem hasEdge_perm (graph : FiniteHypergraph Vertex) {first second : List Vertex}
    (sameVertices : first.Perm second) : graph.HasEdge first ↔ graph.HasEdge second := by
  constructor
  · rintro ⟨stored, listed, ordering⟩
    exact ⟨stored, listed, ordering.trans sameVertices⟩
  · rintro ⟨stored, listed, ordering⟩
    exact ⟨stored, listed, ordering.trans sameVertices.symm⟩

theorem hasEdge_nodup (graph : FiniteHypergraph Vertex) {edge : List Vertex}
    (present : graph.HasEdge edge) : edge.Nodup := by
  obtain ⟨stored, listed, ordering⟩ := present
  exact ordering.nodup_iff.mp (graph.edge_nodup stored listed)

theorem hasEdge_vertex (graph : FiniteHypergraph Vertex) {edge : List Vertex}
    (present : graph.HasEdge edge) {vertex : Vertex} (inEdge : vertex ∈ edge) :
    vertex ∈ graph.vertices := by
  obtain ⟨stored, listed, ordering⟩ := present
  exact graph.edge_vertices stored listed vertex (ordering.mem_iff.mpr inEdge)

theorem hasEdge_length (graph : FiniteHypergraph Vertex) {uniformity : Nat}
    (uniform : graph.Uniform uniformity) {edge : List Vertex}
    (present : graph.HasEdge edge) : edge.length = uniformity := by
  obtain ⟨stored, listed, ordering⟩ := present
  exact ordering.length_eq.symm.trans (uniform stored listed)

end FiniteHypergraph

structure Embedding {Target : Type u} {Host : Type v}
    (target : FiniteHypergraph Target) (host : FiniteHypergraph Host) where
  toFun : Target → Host
  maps_vertices : ∀ vertex, vertex ∈ target.vertices → toFun vertex ∈ host.vertices
  injective : ∀ first, first ∈ target.vertices → ∀ second, second ∈ target.vertices →
    toFun first = toFun second → first = second
  maps_edges : ∀ edge, edge ∈ target.edges → host.HasEdge (edge.map toFun)

namespace Embedding

variable {Target : Type u} {Host : Type v}
variable {target : FiniteHypergraph Target} {host : FiniteHypergraph Host}

theorem map_hasEdge (embedding : Embedding target host) {edge : List Target}
    (present : target.HasEdge edge) : host.HasEdge (edge.map embedding.toFun) := by
  obtain ⟨stored, listed, ordering⟩ := present
  exact (host.hasEdge_perm (ordering.map embedding.toFun)).mp
    (embedding.maps_edges stored listed)

def restrict (embedding : Embedding target host) (smaller : FiniteHypergraph Target)
    (verticesIncluded : ∀ vertex, vertex ∈ smaller.vertices → vertex ∈ target.vertices)
    (edgesIncluded : ∀ edge, smaller.HasEdge edge → target.HasEdge edge) :
    Embedding smaller host where
  toFun := embedding.toFun
  maps_vertices := fun vertex present =>
    embedding.maps_vertices vertex (verticesIncluded vertex present)
  injective := fun first firstPresent second secondPresent equal =>
    embedding.injective first (verticesIncluded first firstPresent)
      second (verticesIncluded second secondPresent) equal
  maps_edges := fun edge present =>
    embedding.map_hasEdge (edgesIncluded edge (smaller.hasEdge_of_mem present))

def Anchored (embedding : Embedding target host) (root : List Target)
    (rootMap : Target → Host) : Prop :=
  ∀ vertex, vertex ∈ root → embedding.toFun vertex = rootMap vertex

theorem anchored_root_edge (embedding : Embedding target host) (root : List Target)
    (rootMap : Target → Host) (rootEdge : target.HasEdge root)
    (anchored : embedding.Anchored root rootMap) : host.HasEdge (root.map rootMap) := by
  have sameImage : root.map embedding.toFun = root.map rootMap :=
    List.map_congr_left anchored
  rw [← sameImage]
  exact embedding.map_hasEdge rootEdge

theorem nonRoot_image_mem (embedding : Embedding target host)
    (root : List Target) (rootMap : Target → Host) (block : List Host)
    (rootVertices : ∀ vertex, vertex ∈ root → vertex ∈ target.vertices)
    (anchored : embedding.Anchored root rootMap)
    (inPrefix : ∀ vertex, vertex ∈ target.vertices →
      embedding.toFun vertex ∈ root.map rootMap ++ block)
    (vertex : Target) (inTarget : vertex ∈ target.vertices) (notRoot : vertex ∉ root) :
    embedding.toFun vertex ∈ block := by
  rcases List.mem_append.mp (inPrefix vertex inTarget) with inAnchor | inBlock
  · obtain ⟨rootVertex, inRoot, sameImage⟩ := List.mem_map.mp inAnchor
    have equalVertices : vertex = rootVertex :=
      embedding.injective vertex inTarget rootVertex (rootVertices rootVertex inRoot)
        (sameImage.symm.trans (anchored rootVertex inRoot).symm)
    exact False.elim (notRoot (equalVertices ▸ inRoot))
  · exact inBlock

end Embedding

def AnchoredSupport {Target : Type u} {Host : Type v}
    (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) (rootMap : Target → Host) (block : List Host) : Prop :=
  ∃ embedding : Embedding target host, embedding.Anchored root rootMap ∧
    ∀ vertex, vertex ∈ target.vertices → embedding.toFun vertex ∈ root.map rootMap ++ block

theorem anchoredSupport_root_edge {Target : Type u} {Host : Type v}
    (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) (rootMap : Target → Host) (block : List Host)
    (rootEdge : target.HasEdge root)
    (supported : AnchoredSupport target host root rootMap block) :
    host.HasEdge (root.map rootMap) := by
  obtain ⟨embedding, anchored, _⟩ := supported
  exact embedding.anchored_root_edge root rootMap rootEdge anchored

theorem anchoredSupport_mono {Target : Type u} {Host : Type v}
    (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) (rootMap : Target → Host) (first second : List Host)
    (included : ∀ vertex, vertex ∈ first → vertex ∈ second)
    (supported : AnchoredSupport target host root rootMap first) :
    AnchoredSupport target host root rootMap second := by
  obtain ⟨embedding, anchored, inPrefix⟩ := supported
  refine ⟨embedding, anchored, ?_⟩
  intro vertex inTarget
  rcases List.mem_append.mp (inPrefix vertex inTarget) with inRoot | inFirst
  · exact List.mem_append.mpr (Or.inl inRoot)
  · exact List.mem_append.mpr (Or.inr (included _ inFirst))

theorem anchoredSupport_perm {Target : Type u} {Host : Type v}
    (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) (rootMap : Target → Host) {first second : List Host}
    (ordering : first.Perm second) :
    AnchoredSupport target host root rootMap first ↔
      AnchoredSupport target host root rootMap second :=
  ⟨anchoredSupport_mono target host root rootMap first second
      (fun _ present => ordering.mem_iff.mp present),
    anchoredSupport_mono target host root rootMap second first
      (fun _ present => ordering.mem_iff.mpr present)⟩

theorem anchoredSupport_restrict {Target : Type u} {Host : Type v}
    (smaller larger : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) (rootMap : Target → Host) (block : List Host)
    (verticesIncluded : ∀ vertex, vertex ∈ smaller.vertices → vertex ∈ larger.vertices)
    (edgesIncluded : ∀ edge, smaller.HasEdge edge → larger.HasEdge edge)
    (supported : AnchoredSupport larger host root rootMap block) :
    AnchoredSupport smaller host root rootMap block := by
  obtain ⟨embedding, anchored, inPrefix⟩ := supported
  exact ⟨embedding.restrict smaller verticesIncluded edgesIncluded,
    anchored, fun vertex present => inPrefix vertex (verticesIncluded vertex present)⟩

structure EdgeAmalgam {Target : Type u}
    (first second joined : FiniteHypergraph Target) (root : List Target) : Prop where
  vertices_union : ∀ vertex, vertex ∈ joined.vertices ↔
    vertex ∈ first.vertices ∨ vertex ∈ second.vertices
  vertices_intersection : ∀ vertex,
    (vertex ∈ first.vertices ∧ vertex ∈ second.vertices) ↔ vertex ∈ root
  edges_union : ∀ edge, joined.HasEdge edge ↔ first.HasEdge edge ∨ second.HasEdge edge
  first_root : first.HasEdge root
  second_root : second.HasEdge root

end Kalai
