import Kalai.FactorialCounts

namespace Kalai

universe u v

variable {Vertex : Type u} {Target : Type u} {Host : Type v}

def cutWithMarker (marker : Vertex) (state : Cut Vertex) : MarkedCut Vertex :=
  ⟨state.prefix, marker, state.suffix⟩

theorem cutWithMarker_injective (marker : Vertex) (first second : Cut Vertex)
    (same : cutWithMarker marker first = cutWithMarker marker second) : first = second :=
  congrArg (fun state : MarkedCut Vertex => (⟨state.before, state.after⟩ : Cut Vertex)) same

theorem cutWithMarker_ordering (marker : Vertex) (remaining : List Vertex) (state : Cut Vertex)
    (ordering : state.word.Perm remaining) : (cutWithMarker marker state).word.Perm (marker :: remaining) :=
  List.perm_middle.trans (ordering.cons marker)

noncomputable def rootSliceListing (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (faceMap : Target → Host) (endpoint : Target)
    (marker : Host) (remaining : List Host) :=
  (markedUniverse (marker :: remaining)).restrict (fun state =>
    state.marker = marker ∧ SupportsAt target host face faceMap endpoint state)

noncomputable def rootSliceCount (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (faceMap : Target → Host) (endpoint : Target)
    (marker : Host) (remaining : List Host) : Nat :=
  (rootSliceListing target host face faceMap endpoint marker remaining).card

noncomputable def anchoredToRootSlice (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (faceMap : Target → Host) (endpoint : Target)
    (rootEdge : target.HasEdge (face ++ [endpoint])) (marker : Host) (remaining : List Host)
    (state : {state : Cut Host // state.word.Perm remaining ∧
      AnchoredSupport target host (face ++ [endpoint]) (endpointMap faceMap endpoint marker) state.prefix}) :
    {state : MarkedCut Host // state.word.Perm (marker :: remaining) ∧
      state.marker = marker ∧ SupportsAt target host face faceMap endpoint state} :=
  ⟨cutWithMarker marker state.val, cutWithMarker_ordering marker remaining state.val state.property.1,
    rfl, (supportsAt_iff_anchoredSupport target host face faceMap endpoint
      (cutWithMarker marker state.val) rootEdge).mpr state.property.2⟩

theorem anchoredToRootSlice_injective (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (faceMap : Target → Host) (endpoint : Target)
    (rootEdge : target.HasEdge (face ++ [endpoint])) (marker : Host) (remaining : List Host)
    (first second : {state : Cut Host // state.word.Perm remaining ∧
      AnchoredSupport target host (face ++ [endpoint]) (endpointMap faceMap endpoint marker) state.prefix})
    (same : anchoredToRootSlice target host face faceMap endpoint rootEdge marker remaining first =
      anchoredToRootSlice target host face faceMap endpoint rootEdge marker remaining second) : first = second :=
  Subtype.ext (cutWithMarker_injective marker first.val second.val (congrArg Subtype.val same))

theorem anchoredToRootSlice_surjective (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (faceMap : Target → Host) (endpoint : Target)
    (rootEdge : target.HasEdge (face ++ [endpoint])) (marker : Host) (remaining : List Host)
    (state : {state : MarkedCut Host // state.word.Perm (marker :: remaining) ∧
      state.marker = marker ∧ SupportsAt target host face faceMap endpoint state}) :
    ∃ source, anchoredToRootSlice target host face faceMap endpoint rootEdge marker remaining source = state := by
  rcases state with ⟨⟨before, current, after⟩, ordering, sameMarker, supported⟩
  change current = marker at sameMarker
  subst current
  have removed : (before ++ after).Perm remaining :=
    (List.perm_middle.symm.trans ordering).cons_inv
  have anchored := (supportsAt_iff_anchoredSupport target host face faceMap endpoint
    ⟨before, marker, after⟩ rootEdge).mp supported
  exact ⟨⟨⟨before, after⟩, removed, anchored⟩, rfl⟩

theorem rootSliceCount_eq_cutCount (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (faceMap : Target → Host) (endpoint : Target)
    (rootEdge : target.HasEdge (face ++ [endpoint])) (marker : Host) (remaining : List Host) :
    rootSliceCount target host face faceMap endpoint marker remaining =
      cutCount remaining (AnchoredSupport target host (face ++ [endpoint])
        (endpointMap faceMap endpoint marker)) :=
  ((cutListing remaining (AnchoredSupport target host (face ++ [endpoint])
      (endpointMap faceMap endpoint marker))).card_eq_of_bijection
    (rootSliceListing target host face faceMap endpoint marker remaining)
    (anchoredToRootSlice target host face faceMap endpoint rootEdge marker remaining)
    (anchoredToRootSlice_injective target host face faceMap endpoint rootEdge marker remaining)
    (anchoredToRootSlice_surjective target host face faceMap endpoint rootEdge marker remaining)).symm

noncomputable def fixedMarkerListing (marker : Vertex) (remaining : List Vertex) :=
  (markedUniverse (marker :: remaining)).restrict (fun state => state.marker = marker)

def cutToFixedMarker (marker : Vertex) (remaining : List Vertex)
    (state : {state : Cut Vertex // state.word.Perm remaining}) :
    {state : MarkedCut Vertex // state.word.Perm (marker :: remaining) ∧ state.marker = marker} :=
  ⟨cutWithMarker marker state.val, cutWithMarker_ordering marker remaining state.val state.property, rfl⟩

theorem fixedMarkerListing_card (marker : Vertex) (remaining : List Vertex) :
    (fixedMarkerListing marker remaining).card = (cutUniverse remaining).card := by
  apply Eq.symm
  apply (cutUniverse remaining).card_eq_of_bijection (fixedMarkerListing marker remaining)
    (cutToFixedMarker marker remaining)
  · intro first second same
    exact Subtype.ext (cutWithMarker_injective marker first.val second.val (congrArg Subtype.val same))
  · rintro ⟨⟨before, current, after⟩, ordering, sameMarker⟩
    change current = marker at sameMarker
    subst current
    have removed : (before ++ after).Perm remaining :=
      (List.perm_middle.symm.trans ordering).cons_inv
    exact ⟨⟨⟨before, after⟩, removed⟩, rfl⟩

theorem fixedMarkerListing_card_factorial (marker : Vertex) (remaining : List Vertex)
    (distinct : remaining.Nodup) :
    (fixedMarkerListing marker remaining).card = factorial (remaining.length + 1) := by
  rw [fixedMarkerListing_card, cutUniverse_card_factorial remaining distinct]

end Kalai
