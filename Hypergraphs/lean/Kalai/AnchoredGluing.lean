import Kalai.Hypergraph
import Kalai.EnumeratedGluing

namespace Kalai

universe u v

variable {Target : Type u} {Host : Type v}

theorem anchoredSupport_joined_first (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target) (rootMap : Target → Host)
    (amalgam : EdgeAmalgam first second joined root) (block : List Host)
    (supported : AnchoredSupport joined host root rootMap block) :
    AnchoredSupport first host root rootMap block :=
  anchoredSupport_restrict first joined host root rootMap block
    (fun vertex present => (amalgam.vertices_union vertex).mpr (Or.inl present))
    (fun edge present => (amalgam.edges_union edge).mpr (Or.inl present)) supported

theorem anchoredSupport_joined_second (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target) (rootMap : Target → Host)
    (amalgam : EdgeAmalgam first second joined root) (block : List Host)
    (supported : AnchoredSupport joined host root rootMap block) :
    AnchoredSupport second host root rootMap block :=
  anchoredSupport_restrict second joined host root rootMap block
    (fun vertex present => (amalgam.vertices_union vertex).mpr (Or.inr present))
    (fun edge present => (amalgam.edges_union edge).mpr (Or.inr present)) supported

theorem glue_embeddings (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target)
    (amalgam : EdgeAmalgam first second joined root)
    (firstEmbedding : Embedding first host) (secondEmbedding : Embedding second host)
    (agree : ∀ vertex, vertex ∈ first.vertices → vertex ∈ second.vertices →
      firstEmbedding.toFun vertex = secondEmbedding.toFun vertex)
    (separated : ∀ firstVertex, firstVertex ∈ first.vertices →
      firstVertex ∉ second.vertices → ∀ secondVertex, secondVertex ∈ second.vertices →
      secondVertex ∉ first.vertices →
      firstEmbedding.toFun firstVertex ≠ secondEmbedding.toFun secondVertex) :
    ∃ glued : Embedding joined host,
      (∀ vertex, vertex ∈ first.vertices → glued.toFun vertex = firstEmbedding.toFun vertex) ∧
      (∀ vertex, vertex ∈ second.vertices → glued.toFun vertex = secondEmbedding.toFun vertex) := by
  classical
  let combined := fun vertex =>
    if vertex ∈ first.vertices then firstEmbedding.toFun vertex else secondEmbedding.toFun vertex
  have onFirst : ∀ vertex, vertex ∈ first.vertices → combined vertex = firstEmbedding.toFun vertex := by
    intro vertex present
    simp [combined, present]
  have onSecond : ∀ vertex, vertex ∈ second.vertices → combined vertex = secondEmbedding.toFun vertex := by
    intro vertex present
    by_cases inFirst : vertex ∈ first.vertices
    · exact (onFirst vertex inFirst).trans (agree vertex inFirst present)
    · simp [combined, inFirst]
  have crossInjective : ∀ firstVertex, firstVertex ∈ first.vertices →
      ∀ secondVertex, secondVertex ∈ second.vertices →
      combined firstVertex = combined secondVertex → firstVertex = secondVertex := by
    intro firstVertex inFirst secondVertex inSecond sameImage
    by_cases alsoSecond : firstVertex ∈ second.vertices
    · exact secondEmbedding.injective firstVertex alsoSecond secondVertex inSecond
        ((onSecond firstVertex alsoSecond).symm.trans
          (sameImage.trans (onSecond secondVertex inSecond)))
    · by_cases alsoFirst : secondVertex ∈ first.vertices
      · exact firstEmbedding.injective firstVertex inFirst secondVertex alsoFirst
          ((onFirst firstVertex inFirst).symm.trans
            (sameImage.trans (onFirst secondVertex alsoFirst)))
      · exact False.elim (separated firstVertex inFirst alsoSecond secondVertex inSecond alsoFirst
          ((onFirst firstVertex inFirst).symm.trans
            (sameImage.trans (onSecond secondVertex inSecond))))
  let glued : Embedding joined host := {
    toFun := combined
    maps_vertices := by
      intro vertex present
      rcases (amalgam.vertices_union vertex).mp present with inFirst | inSecond
      · rw [onFirst vertex inFirst]
        exact firstEmbedding.maps_vertices vertex inFirst
      · rw [onSecond vertex inSecond]
        exact secondEmbedding.maps_vertices vertex inSecond
    injective := by
      intro firstVertex firstPresent secondVertex secondPresent sameImage
      rcases (amalgam.vertices_union firstVertex).mp firstPresent with firstLeft | firstRight
      · rcases (amalgam.vertices_union secondVertex).mp secondPresent with secondLeft | secondRight
        · exact firstEmbedding.injective firstVertex firstLeft secondVertex secondLeft
            ((onFirst firstVertex firstLeft).symm.trans
              (sameImage.trans (onFirst secondVertex secondLeft)))
        · exact crossInjective firstVertex firstLeft secondVertex secondRight sameImage
      · rcases (amalgam.vertices_union secondVertex).mp secondPresent with secondLeft | secondRight
        · exact (crossInjective secondVertex secondLeft firstVertex firstRight sameImage.symm).symm
        · exact secondEmbedding.injective firstVertex firstRight secondVertex secondRight
            ((onSecond firstVertex firstRight).symm.trans
              (sameImage.trans (onSecond secondVertex secondRight)))
    maps_edges := by
      intro edge listed
      rcases (amalgam.edges_union edge).mp (joined.hasEdge_of_mem listed) with inFirst | inSecond
      · have sameMap : edge.map combined = edge.map firstEmbedding.toFun :=
          List.map_congr_left (fun vertex present =>
            onFirst vertex (first.hasEdge_vertex inFirst present))
        rw [sameMap]
        exact firstEmbedding.map_hasEdge inFirst
      · have sameMap : edge.map combined = edge.map secondEmbedding.toFun :=
          List.map_congr_left (fun vertex present =>
            onSecond vertex (second.hasEdge_vertex inSecond present))
        rw [sameMap]
        exact secondEmbedding.map_hasEdge inSecond
  }
  exact ⟨glued, onFirst, onSecond⟩

theorem anchoredSupport_glue (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target) (rootMap : Target → Host)
    (amalgam : EdgeAmalgam first second joined root) (firstBlock secondBlock : List Host)
    (noDuplicates : (firstBlock ++ secondBlock).Nodup)
    (firstSupported : AnchoredSupport first host root rootMap firstBlock)
    (secondSupported : AnchoredSupport second host root rootMap secondBlock) :
    AnchoredSupport joined host root rootMap (firstBlock ++ secondBlock) := by
  obtain ⟨firstEmbedding, firstAnchored, firstPrefix⟩ := firstSupported
  obtain ⟨secondEmbedding, secondAnchored, secondPrefix⟩ := secondSupported
  have firstRootVertices : ∀ vertex, vertex ∈ root → vertex ∈ first.vertices :=
    fun _ present => first.hasEdge_vertex amalgam.first_root present
  have secondRootVertices : ∀ vertex, vertex ∈ root → vertex ∈ second.vertices :=
    fun _ present => second.hasEdge_vertex amalgam.second_root present
  have agree : ∀ vertex, vertex ∈ first.vertices → vertex ∈ second.vertices →
      firstEmbedding.toFun vertex = secondEmbedding.toFun vertex := by
    intro vertex inFirst inSecond
    have inRoot := (amalgam.vertices_intersection vertex).mp ⟨inFirst, inSecond⟩
    exact (firstAnchored vertex inRoot).trans (secondAnchored vertex inRoot).symm
  have separated : ∀ firstVertex, firstVertex ∈ first.vertices →
      firstVertex ∉ second.vertices → ∀ secondVertex, secondVertex ∈ second.vertices →
      secondVertex ∉ first.vertices →
      firstEmbedding.toFun firstVertex ≠ secondEmbedding.toFun secondVertex := by
    intro firstVertex inFirst outsideSecond secondVertex inSecond outsideFirst
    have firstNotRoot : firstVertex ∉ root :=
      fun present => outsideSecond (secondRootVertices firstVertex present)
    have secondNotRoot : secondVertex ∉ root :=
      fun present => outsideFirst (firstRootVertices secondVertex present)
    have firstImage := firstEmbedding.nonRoot_image_mem root rootMap firstBlock
      firstRootVertices firstAnchored firstPrefix firstVertex inFirst firstNotRoot
    have secondImage := secondEmbedding.nonRoot_image_mem root rootMap secondBlock
      secondRootVertices secondAnchored secondPrefix secondVertex inSecond secondNotRoot
    exact (List.pairwise_append.mp noDuplicates).2.2 _ firstImage _ secondImage
  obtain ⟨glued, onFirst, onSecond⟩ :=
    glue_embeddings first second joined host root amalgam firstEmbedding secondEmbedding agree separated
  refine ⟨glued, ?_, ?_⟩
  · intro vertex inRoot
    exact (onFirst vertex (firstRootVertices vertex inRoot)).trans (firstAnchored vertex inRoot)
  · intro vertex present
    rcases (amalgam.vertices_union vertex).mp present with inFirst | inSecond
    · rw [onFirst vertex inFirst]
      rcases List.mem_append.mp (firstPrefix vertex inFirst) with inRoot | inBlock
      · exact List.mem_append.mpr (Or.inl inRoot)
      · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl inBlock)))
    · rw [onSecond vertex inSecond]
      rcases List.mem_append.mp (secondPrefix vertex inSecond) with inRoot | inBlock
      · exact List.mem_append.mpr (Or.inl inRoot)
      · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr inBlock)))

theorem anchored_gluing_compatible (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target) (rootMap : Target → Host)
    (amalgam : EdgeAmalgam first second joined root) :
    GluingCompatible (AnchoredSupport first host root rootMap)
      (AnchoredSupport second host root rootMap) (AnchoredSupport joined host root rootMap) := by
  intro firstBlock secondBlock noDuplicates firstSupported secondSupported
  exact anchoredSupport_glue first second joined host root rootMap amalgam firstBlock secondBlock
    noDuplicates firstSupported secondSupported

structure EdgeFirstFrame (host : FiniteHypergraph Host) (root : List Target)
    (rootMap : Target → Host) (remaining : List Host) : Prop where
  marking_edge : host.HasEdge (root.map rootMap)
  enumeration : (root.map rootMap ++ remaining).Perm host.vertices

theorem EdgeFirstFrame.remaining_nodup (host : FiniteHypergraph Host) (root : List Target)
    (rootMap : Target → Host) (remaining : List Host)
    (frame : EdgeFirstFrame host root rootMap remaining) : remaining.Nodup :=
  List.Sublist.nodup (List.sublist_append_right (root.map rootMap) remaining)
    (frame.enumeration.nodup_iff.mpr host.vertices_nodup)

theorem EdgeFirstFrame.remaining_avoids_root (host : FiniteHypergraph Host) (root : List Target)
    (rootMap : Target → Host) (remaining : List Host)
    (frame : EdgeFirstFrame host root rootMap remaining) :
    ∀ vertex, vertex ∈ remaining → vertex ∉ root.map rootMap := by
  intro vertex inRemaining inRoot
  have distinct := frame.enumeration.nodup_iff.mpr host.vertices_nodup
  exact (List.pairwise_append.mp distinct).2.2 vertex inRoot vertex inRemaining rfl

noncomputable def anchoredGluingMap (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target) (rootMap : Target → Host)
    (amalgam : EdgeAmalgam first second joined root) (remaining : List Host)
    (frame : EdgeFirstFrame host root rootMap remaining) :
    EnumeratedGluingSource remaining (AnchoredSupport first host root rootMap)
      (AnchoredSupport joined host root rootMap) →
    EnumeratedGluingTarget remaining (AnchoredSupport second host root rootMap) :=
  enumeratedGluingMap remaining (frame.remaining_nodup host root rootMap remaining)
    (AnchoredSupport first host root rootMap) (AnchoredSupport second host root rootMap)
    (AnchoredSupport joined host root rootMap)
    (anchored_gluing_compatible first second joined host root rootMap amalgam)

theorem anchoredGluingMap_injective (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target) (rootMap : Target → Host)
    (amalgam : EdgeAmalgam first second joined root) (remaining : List Host)
    (frame : EdgeFirstFrame host root rootMap remaining)
    (source target : EnumeratedGluingSource remaining (AnchoredSupport first host root rootMap)
      (AnchoredSupport joined host root rootMap))
    (sameImage : anchoredGluingMap first second joined host root rootMap amalgam remaining frame source =
      anchoredGluingMap first second joined host root rootMap amalgam remaining frame target) :
    source = target :=
  enumeratedGluingMap_injective remaining (frame.remaining_nodup host root rootMap remaining)
    (AnchoredSupport first host root rootMap) (AnchoredSupport second host root rootMap)
    (AnchoredSupport joined host root rootMap)
    (anchored_gluing_compatible first second joined host root rootMap amalgam) source target sameImage

end Kalai
