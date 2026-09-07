import Kalai.MarkedStates

namespace Kalai

universe u v

variable {Target : Type u} {Host : Type v}

noncomputable def endpointMap (faceMap : Target → Host) (endpoint : Target)
    (marker : Host) : Target → Host := by
  classical
  exact fun vertex => if vertex = endpoint then marker else faceMap vertex

theorem endpointMap_at_endpoint (faceMap : Target → Host) (endpoint : Target) (marker : Host) :
    endpointMap faceMap endpoint marker endpoint = marker := by
  simp [endpointMap]

theorem endpointMap_on_face (face : List Target) (faceMap : Target → Host)
    (endpoint : Target) (marker : Host) (outsideFace : endpoint ∉ face) :
    ∀ vertex, vertex ∈ face → endpointMap faceMap endpoint marker vertex = faceMap vertex := by
  intro vertex present
  have different : vertex ≠ endpoint := fun equal => outsideFace (equal ▸ present)
  simp [endpointMap, different]

theorem endpointMap_rootImage (face : List Target) (faceMap : Target → Host)
    (endpoint : Target) (marker : Host) (outsideFace : endpoint ∉ face) :
    (face ++ [endpoint]).map (endpointMap faceMap endpoint marker) = face.map faceMap ++ [marker] := by
  have onFace := List.map_congr_left (endpointMap_on_face face faceMap endpoint marker outsideFace)
  simp only [List.map_append, List.map_cons, List.map_nil, onFace, endpointMap_at_endpoint]

theorem rootEndpoint_not_face (target : FiniteHypergraph Target)
    (face : List Target) (endpoint : Target) (rootEdge : target.HasEdge (face ++ [endpoint])) :
    endpoint ∉ face := by
  intro repeated
  have distinct := target.hasEdge_nodup rootEdge
  exact (List.pairwise_append.mp distinct).2.2 endpoint repeated endpoint (by simp) rfl

theorem Embedding.anchored_endpoint_iff {target : FiniteHypergraph Target}
    {host : FiniteHypergraph Host} (embedding : Embedding target host)
    (face : List Target) (faceMap : Target → Host) (endpoint : Target) (marker : Host)
    (outsideFace : endpoint ∉ face) :
    embedding.Anchored (face ++ [endpoint]) (endpointMap faceMap endpoint marker) ↔
      embedding.Anchored face faceMap ∧ embedding.toFun endpoint = marker := by
  constructor
  · intro anchored
    constructor
    · intro vertex present
      exact (anchored vertex (List.mem_append_left [endpoint] present)).trans
        (endpointMap_on_face face faceMap endpoint marker outsideFace vertex present)
    · exact (anchored endpoint (List.mem_append_right face (by simp))).trans
        (endpointMap_at_endpoint faceMap endpoint marker)
  · rintro ⟨anchoredFace, atEndpoint⟩ vertex present
    rcases List.mem_append.mp present with inFace | inEndpoint
    · exact (anchoredFace vertex inFace).trans
        (endpointMap_on_face face faceMap endpoint marker outsideFace vertex inFace).symm
    · have equal : vertex = endpoint := List.mem_singleton.mp inEndpoint
      rw [equal, endpointMap_at_endpoint]
      exact atEndpoint

def MarkedCut.toFront (state : MarkedCut Host) : Host × Cut Host :=
  (state.marker, ⟨state.before, state.after⟩)

def MarkedCut.ofFront (front : Host × Cut Host) : MarkedCut Host :=
  ⟨front.2.prefix, front.1, front.2.suffix⟩

theorem MarkedCut.ofFront_toFront (state : MarkedCut Host) :
    MarkedCut.ofFront state.toFront = state := rfl

theorem MarkedCut.toFront_ofFront (front : Host × Cut Host) :
    (MarkedCut.ofFront front).toFront = front := rfl

theorem MarkedCut.front_word_perm (face : List Host) (state : MarkedCut Host) :
    (face ++ [state.toFront.1] ++ state.toFront.2.word).Perm (face ++ state.word) := by
  have exchange := ((List.perm_append_comm (l₁ := [state.marker]) (l₂ := state.before)).append_right
    state.after).append_left face
  simpa [MarkedCut.toFront, MarkedCut.word, Cut.word, List.append_assoc] using exchange

theorem MarkedCut.front_divider (face : List Host) (state : MarkedCut Host) :
    (face.length + 1) + state.toFront.2.prefix.length = face.length + state.before.length + 1 := by
  simp only [MarkedCut.toFront]
  omega

theorem markedSupport_iff_anchoredSupport (target : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (faceMap : Target → Host)
    (endpoint : Target) (state : MarkedCut Host) (outsideFace : endpoint ∉ face) :
    MarkedSupport target host face faceMap endpoint state ↔
      AnchoredSupport target host (face ++ [endpoint]) (endpointMap faceMap endpoint state.marker)
        state.before := by
  have prefixOrdering : (face.map faceMap ++ [state.marker] ++ state.before).Perm
      (face.map faceMap ++ state.prefixList) := by
    simpa only [MarkedCut.prefixList, List.append_assoc] using
      (List.perm_append_comm (l₁ := [state.marker]) (l₂ := state.before)).append_left (face.map faceMap)
  constructor
  · rintro ⟨embedding, anchoredFace, atEndpoint, inPrefix⟩
    refine ⟨embedding,
      (embedding.anchored_endpoint_iff face faceMap endpoint state.marker outsideFace).mpr
        ⟨anchoredFace, atEndpoint⟩, ?_⟩
    intro vertex present
    rw [endpointMap_rootImage face faceMap endpoint state.marker outsideFace]
    exact prefixOrdering.mem_iff.mpr (inPrefix vertex present)
  · rintro ⟨embedding, anchored, inPrefix⟩
    have correspondence :=
      (embedding.anchored_endpoint_iff face faceMap endpoint state.marker outsideFace).mp anchored
    refine ⟨embedding, correspondence.1, correspondence.2, ?_⟩
    intro vertex present
    have available := inPrefix vertex present
    rw [endpointMap_rootImage face faceMap endpoint state.marker outsideFace] at available
    exact prefixOrdering.mem_iff.mp available

theorem supportsAt_iff_anchoredSupport (target : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (faceMap : Target → Host)
    (endpoint : Target) (state : MarkedCut Host)
    (rootEdge : target.HasEdge (face ++ [endpoint])) :
    SupportsAt target host face faceMap endpoint state ↔
      AnchoredSupport target host (face ++ [endpoint]) (endpointMap faceMap endpoint state.marker)
        state.before := by
  have outsideFace := rootEndpoint_not_face target face endpoint rootEdge
  have correspondence := markedSupport_iff_anchoredSupport target host face faceMap endpoint state outsideFace
  constructor
  · exact fun supported => correspondence.mp supported.2
  · intro supported
    refine ⟨?_, correspondence.mpr supported⟩
    have markingEdge := anchoredSupport_root_edge target host (face ++ [endpoint])
      (endpointMap faceMap endpoint state.marker) state.before rootEdge supported
    simpa only [endpointMap_rootImage face faceMap endpoint state.marker outsideFace] using markingEdge

end Kalai
