import KalaiTests

namespace Kalai.LeafTests

open Kalai.HypergraphTests

def smaller : FiniteHypergraph Nat where
  vertices := [0, 1, 2]
  edges := [[0, 1, 2]]
  vertices_nodup := by decide
  edge_nodup := by decide
  edge_vertices := by decide
  simple := by decide

theorem extension : LeafExtension smaller firstBranch [0, 1] 2 3 where
  old_root := smaller.hasEdge_of_mem (by decide)
  fresh := by decide
  vertices_added := by
    intro vertex
    simp [smaller, firstBranch, or_assoc]
  edges_added := by
    intro edge
    simp [FiniteHypergraph.HasEdge, smaller, firstBranch, List.perm_comm]

theorem faceFrame : FaceFrame firstBranch [0, 1] [2, 3] where
  enumeration := by decide

def earlier : MarkedCut Nat := ⟨[], 2, [3]⟩

def later : MarkedCut Nat := ⟨[2], 3, []⟩

def earlierEmbedding : Embedding smaller firstBranch where
  toFun := id
  maps_vertices := by
    intro vertex present
    simpa [smaller, firstBranch] using List.mem_append_left [3] present
  injective := by
    intro first _ second _ equal
    exact equal
  maps_edges := by
    intro edge present
    simp only [List.map_id]
    apply firstBranch.hasEdge_of_mem
    simpa [smaller, firstBranch] using List.mem_append_left [[0, 1, 3]] present

def laterMap (vertex : Nat) : Nat := if vertex = 2 then 3 else vertex

def laterEmbedding : Embedding smaller firstBranch where
  toFun := laterMap
  maps_vertices := by
    intro vertex present
    simp only [smaller, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl <;> decide
  injective := by
    intro first firstPresent second secondPresent equal
    simp only [smaller, List.mem_cons, List.not_mem_nil, or_false] at firstPresent secondPresent
    rcases firstPresent with rfl | rfl | rfl <;>
      rcases secondPresent with rfl | rfl | rfl <;> simp_all [laterMap]
  maps_edges := by
    intro edge present
    have rootOnly : edge = [0, 1, 2] := by simpa [smaller] using present
    rw [rootOnly]
    exact firstBranch.hasEdge_of_mem (by decide)

theorem earlierSupported : SupportsAt smaller firstBranch [0, 1] id 2 earlier := by
  refine ⟨firstBranch.hasEdge_of_mem (by decide), earlierEmbedding, ?_, rfl, ?_⟩
  · intro vertex _
    rfl
  · intro vertex present
    simpa [earlierEmbedding, earlier, MarkedCut.prefixList, smaller] using present

theorem laterSupported : SupportsAt smaller firstBranch [0, 1] id 2 later := by
  refine ⟨firstBranch.hasEdge_of_mem (by decide), laterEmbedding, ?_, rfl, ?_⟩
  · intro vertex present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  · intro vertex present
    simpa [later, MarkedCut.prefixList, firstBranch] using laterEmbedding.maps_vertices vertex present

theorem laterHasEarlier : EarlierSupported (SupportsAt smaller firstBranch [0, 1] id 2) later :=
  ⟨earlier, rfl, by decide, earlierSupported⟩

theorem earlierIsFirst : ¬ EarlierSupported (SupportsAt smaller firstBranch [0, 1] id 2) earlier := by
  rintro ⟨previous, _, impossible, _⟩
  simp [earlier] at impossible

theorem transferred : SupportsAt firstBranch firstBranch [0, 1] id 3 later :=
  supportsAt_leaf_of_earlier smaller firstBranch firstBranch [0, 1] id 2 3 extension [2, 3]
    faceFrame earlier later (List.Perm.refl _) rfl (by decide) earlierSupported laterSupported.1

example : AnchoredSupport firstBranch firstBranch [0, 1, 3] (endpointMap id 3 3) [2] :=
  (supportsAt_iff_anchoredSupport firstBranch firstBranch [0, 1] id 3 later
    (firstBranch.hasEdge_of_mem (by decide))).mp transferred

example : earlierEmbedding.toFun 2 = 2 ∧ laterEmbedding.toFun 2 = 3 := ⟨rfl, rfl⟩

example : laterEmbedding.toFun 2 = later.marker := rfl

example : earlier.toFront = (2, (⟨[], [3]⟩ : Cut Nat)) := rfl

example : later.toFront = (3, (⟨[2], []⟩ : Cut Nat)) := rfl

def earlierSource : MarkedFamily smaller firstBranch [0, 1] id 2 [2, 3] :=
  ⟨earlier, List.Perm.refl _, earlierSupported⟩

def laterSource : MarkedFamily smaller firstBranch [0, 1] id 2 [2, 3] :=
  ⟨later, List.Perm.refl _, laterSupported⟩

example : Sum.map
    (fun state : MarkedFamily firstBranch firstBranch [0, 1] id 3 [2, 3] => state.val)
    (fun word : ShadowOrderings firstBranch [0, 1] [2, 3] => word.val)
    (leafTransferMap smaller firstBranch firstBranch [0, 1] id 2 3 extension [2, 3]
      faceFrame earlierSource) = Sum.inr [2, 3] := by
  simp only [leafTransferMap, earlierSource, dif_neg earlierIsFirst]
  rfl

example : Sum.map
    (fun state : MarkedFamily firstBranch firstBranch [0, 1] id 3 [2, 3] => state.val)
    (fun word : ShadowOrderings firstBranch [0, 1] [2, 3] => word.val)
    (leafTransferMap smaller firstBranch firstBranch [0, 1] id 2 3 extension [2, 3]
      faceFrame laterSource) = Sum.inl later := by
  simp [leafTransferMap, laterSource, laterHasEarlier]

end Kalai.LeafTests
