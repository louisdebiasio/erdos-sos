import Kalai.MarkedNormalization

namespace Kalai

universe u v

variable {Target : Type u} {Host : Type v}

structure LeafExtension (smaller larger : FiniteHypergraph Target)
    (face : List Target) (oldEndpoint newVertex : Target) : Prop where
  old_root : smaller.HasEdge (face ++ [oldEndpoint])
  fresh : newVertex ∉ smaller.vertices
  vertices_added : ∀ vertex, vertex ∈ larger.vertices ↔ vertex ∈ smaller.vertices ∨ vertex = newVertex
  edges_added : ∀ edge, larger.HasEdge edge ↔ smaller.HasEdge edge ∨ edge.Perm (face ++ [newVertex])

theorem LeafExtension.face_vertices (smaller larger : FiniteHypergraph Target)
    (face : List Target) (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex) :
    ∀ vertex, vertex ∈ face → vertex ∈ smaller.vertices :=
  fun _ present => smaller.hasEdge_vertex extension.old_root
    (List.mem_append_left [oldEndpoint] present)

theorem extend_leaf_embedding (smaller larger : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (faceMap : Target → Host)
    (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (embedding : Embedding smaller host) (anchoredFace : embedding.Anchored face faceMap)
    (marker : Host)
    (freshImage : ∀ vertex, vertex ∈ smaller.vertices → embedding.toFun vertex ≠ marker)
    (markingEdge : host.HasEdge (face.map faceMap ++ [marker])) :
    ∃ extended : Embedding larger host, extended.toFun newVertex = marker ∧
      ∀ vertex, vertex ∈ smaller.vertices → extended.toFun vertex = embedding.toFun vertex := by
  classical
  let combined := fun vertex => if vertex = newVertex then marker else embedding.toFun vertex
  have atNew : combined newVertex = marker := by simp [combined]
  have onOld : ∀ vertex, vertex ∈ smaller.vertices → combined vertex = embedding.toFun vertex := by
    intro vertex present
    have distinct : vertex ≠ newVertex := fun equal => extension.fresh (equal ▸ present)
    simp [combined, distinct]
  have newInHost : marker ∈ host.vertices :=
    host.hasEdge_vertex markingEdge (List.mem_append_right _ (by simp))
  have faceImage : face.map combined = face.map faceMap :=
    List.map_congr_left (fun vertex present =>
      (onOld vertex (extension.face_vertices smaller larger face oldEndpoint newVertex vertex present)).trans
        (anchoredFace vertex present))
  let extended : Embedding larger host := {
    toFun := combined
    maps_vertices := by
      intro vertex present
      rcases (extension.vertices_added vertex).mp present with oldVertex | isNew
      · rw [onOld vertex oldVertex]
        exact embedding.maps_vertices vertex oldVertex
      · rw [isNew, atNew]
        exact newInHost
    injective := by
      intro first firstPresent second secondPresent sameImage
      rcases (extension.vertices_added first).mp firstPresent with firstOld | firstNew
      · rcases (extension.vertices_added second).mp secondPresent with secondOld | secondNew
        · exact embedding.injective first firstOld second secondOld
            ((onOld first firstOld).symm.trans (sameImage.trans (onOld second secondOld)))
        · have collision : embedding.toFun first = marker := by
            rw [← onOld first firstOld, sameImage, secondNew, atNew]
          exact False.elim (freshImage first firstOld collision)
      · rcases (extension.vertices_added second).mp secondPresent with secondOld | secondNew
        · have collision : embedding.toFun second = marker := by
            rw [← onOld second secondOld, ← sameImage, firstNew, atNew]
          exact False.elim (freshImage second secondOld collision)
        · exact firstNew.trans secondNew.symm
    maps_edges := by
      intro edge present
      rcases (extension.edges_added edge).mp (larger.hasEdge_of_mem present) with oldEdge | newEdge
      · have sameMap : edge.map combined = edge.map embedding.toFun :=
          List.map_congr_left (fun vertex inEdge => onOld vertex (smaller.hasEdge_vertex oldEdge inEdge))
        rw [sameMap]
        exact embedding.map_hasEdge oldEdge
      · apply (host.hasEdge_perm (newEdge.map combined)).mpr
        simpa only [List.map_append, List.map_cons, List.map_nil, faceImage, atNew] using markingEdge
  }
  exact ⟨extended, atNew, onOld⟩

theorem supportsAt_leaf_of_earlier (smaller larger : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (faceMap : Target → Host)
    (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (remaining : List Host) (frame : FaceFrame host (face.map faceMap) remaining)
    (earlier later : MarkedCut Host) (ordering : later.word.Perm remaining)
    (sameWord : earlier.word = later.word)
    (earlierIndex : earlier.before.length < later.before.length)
    (earlierSupported : SupportsAt smaller host face faceMap oldEndpoint earlier)
    (laterMarked : host.HasEdge (face.map faceMap ++ [later.marker])) :
    SupportsAt larger host face faceMap newVertex later := by
  obtain ⟨_, embedding, anchoredFace, _, inEarlier⟩ := earlierSupported
  have avoided := MarkedCut.marker_not_earlier (face.map faceMap) earlier later sameWord earlierIndex
    (frame.fullWord_nodup host (face.map faceMap) remaining later ordering)
  have freshImage : ∀ vertex, vertex ∈ smaller.vertices → embedding.toFun vertex ≠ later.marker := by
    intro vertex present collision
    apply avoided
    rw [← collision]
    exact inEarlier vertex present
  obtain ⟨extended, atNew, onOld⟩ := extend_leaf_embedding smaller larger host face faceMap
    oldEndpoint newVertex extension embedding anchoredFace later.marker freshImage laterMarked
  refine ⟨laterMarked, extended, ?_, atNew, ?_⟩
  · intro vertex present
    exact (onOld vertex (extension.face_vertices smaller larger face oldEndpoint newVertex vertex present)).trans
      (anchoredFace vertex present)
  · intro vertex present
    rcases (extension.vertices_added vertex).mp present with oldVertex | isNew
    · rw [onOld vertex oldVertex]
      rcases List.mem_append.mp (inEarlier vertex oldVertex) with inFace | inOldPrefix
      · exact List.mem_append.mpr (Or.inl inFace)
      · exact List.mem_append.mpr (Or.inr (List.mem_append_left [later.marker]
          (MarkedCut.earlier_prefix_subset earlier later sameWord earlierIndex _ inOldPrefix)))
    · rw [isNew, atNew]
      simp [MarkedCut.prefixList]

theorem supportsAt_leaf_if_earlier (smaller larger : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (faceMap : Target → Host)
    (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (remaining : List Host) (frame : FaceFrame host (face.map faceMap) remaining)
    (state : MarkedCut Host) (ordering : state.word.Perm remaining)
    (marked : host.HasEdge (face.map faceMap ++ [state.marker]))
    (hasEarlier : EarlierSupported (SupportsAt smaller host face faceMap oldEndpoint) state) :
    SupportsAt larger host face faceMap newVertex state := by
  obtain ⟨earlier, sameWord, earlierIndex, earlierSupported⟩ := hasEarlier
  exact supportsAt_leaf_of_earlier smaller larger host face faceMap oldEndpoint newVertex
    extension remaining frame earlier state ordering sameWord earlierIndex earlierSupported marked

noncomputable def leafTransferMap (smaller larger : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (faceMap : Target → Host)
    (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (remaining : List Host) (frame : FaceFrame host (face.map faceMap) remaining)
    (source : MarkedFamily smaller host face faceMap oldEndpoint remaining) :
    Sum (MarkedFamily larger host face faceMap newVertex remaining)
      (ShadowOrderings host (face.map faceMap) remaining) := by
  classical
  exact if hasEarlier : EarlierSupported (SupportsAt smaller host face faceMap oldEndpoint) source.val then
    Sum.inl ⟨source.val, source.property.1,
      supportsAt_leaf_if_earlier smaller larger host face faceMap oldEndpoint newVertex
        extension remaining frame source.val source.property.1 source.property.2.1 hasEarlier⟩
  else
    Sum.inr ⟨source.val.word, source.property.1, source.val.marker, source.property.2.1⟩

theorem leafTransferMap_injective (smaller larger : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (faceMap : Target → Host)
    (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (remaining : List Host) (frame : FaceFrame host (face.map faceMap) remaining)
    (source target : MarkedFamily smaller host face faceMap oldEndpoint remaining)
    (sameImage : leafTransferMap smaller larger host face faceMap oldEndpoint newVertex
      extension remaining frame source = leafTransferMap smaller larger host face faceMap
        oldEndpoint newVertex extension remaining frame target) : source = target := by
  classical
  by_cases sourceEarlier : EarlierSupported (SupportsAt smaller host face faceMap oldEndpoint) source.val
  · by_cases targetEarlier : EarlierSupported (SupportsAt smaller host face faceMap oldEndpoint) target.val
    · simp only [leafTransferMap, dif_pos sourceEarlier, dif_pos targetEarlier] at sameImage
      exact Subtype.ext (congrArg
        (fun state : MarkedFamily larger host face faceMap newVertex remaining => state.val)
        (Sum.inl.inj sameImage))
    · simp [leafTransferMap, sourceEarlier, targetEarlier] at sameImage
  · by_cases targetEarlier : EarlierSupported (SupportsAt smaller host face faceMap oldEndpoint) target.val
    · simp [leafTransferMap, sourceEarlier, targetEarlier] at sameImage
    · simp only [leafTransferMap, dif_neg sourceEarlier, dif_neg targetEarlier] at sameImage
      apply Subtype.ext
      exact first_exception_word_injective (SupportsAt smaller host face faceMap oldEndpoint)
        source.val target.val source.property.2 target.property.2 sourceEarlier targetEarlier
        (congrArg Subtype.val (Sum.inr.inj sameImage))

end Kalai
