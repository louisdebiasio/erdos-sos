import Kalai

namespace Kalai.Tests

example : Cut.ofWord [10, 20, 30] 0 = (⟨[], [10, 20, 30]⟩ : Cut Nat) := rfl

example : Cut.ofWord [10, 20, 30] 3 = (⟨[10, 20, 30], []⟩ : Cut Nat) := rfl

example (supports : List Nat → Prop) (second tail : List Nat)
    (emptySupported : supports []) :
    rotate supports ⟨second, tail⟩ = ⟨second, tail⟩ := by
  have minimal : FirstSupport supports [] := by
    exact ⟨emptySupported, fun index shorter => by simp at shorter⟩
  simpa using rotate_blocks supports [] second tail minimal

example (supports : List Nat → Prop) (first tail : List Nat)
    (minimal : FirstSupport supports first) :
    rotate supports ⟨first, tail⟩ = ⟨[], first ++ tail⟩ := by
  simpa using rotate_blocks supports first [] tail minimal

example : rotate (fun word : List Nat => 0 < word.length)
    ⟨[10, 20, 30], [40]⟩ = ⟨[20, 30], [10, 40]⟩ := by
  apply rotate_blocks _ [10] [20, 30] [40]
  constructor
  · decide
  · intro index shorter
    have indexZero : index = 0 := by simpa using shorter
    simp [indexZero]

example : recover (fun word : List Nat => 0 < word.length)
    ⟨[20, 30], [10, 40]⟩ = ⟨[10, 20, 30], [40]⟩ := by
  apply recover_blocks _ [10] [20, 30] [40]
  constructor
  · decide
  · intro index shorter
    have indexZero : index = 0 := by simpa using shorter
    simp [indexZero]

example (firstSize secondSize : Nat) :
    GluingCompatible
      (fun word : List Nat => firstSize ≤ word.length)
      (fun word : List Nat => secondSize ≤ word.length)
      (fun word : List Nat => firstSize + secondSize ≤ word.length) := by
  intro first second _ firstBound secondBound
  simp only [List.length_append]
  omega

example (vertices : List Nat) (distinct : vertices.Nodup)
    (firstSupport secondSupport jointSupport : List Nat → Prop)
    (compatible : GluingCompatible firstSupport secondSupport jointSupport)
    (source : EnumeratedGluingSource vertices firstSupport jointSupport) :
    ¬ secondSupport (enumeratedGluingMap vertices distinct firstSupport secondSupport
      jointSupport compatible source).val.prefix :=
  (enumeratedGluingMap vertices distinct firstSupport secondSupport jointSupport
    compatible source).property.2

end Kalai.Tests

namespace Kalai.HypergraphTests

def firstBranch : FiniteHypergraph Nat where
  vertices := [0, 1, 2, 3]
  edges := [[0, 1, 2], [0, 1, 3]]
  vertices_nodup := by decide
  edge_nodup := by decide
  edge_vertices := by decide
  simple := by decide

def secondBranch : FiniteHypergraph Nat where
  vertices := [0, 1, 2, 4]
  edges := [[0, 1, 2], [0, 2, 4]]
  vertices_nodup := by decide
  edge_nodup := by decide
  edge_vertices := by decide
  simple := by decide

def joinedBranches : FiniteHypergraph Nat where
  vertices := [0, 1, 2, 3, 4]
  edges := [[0, 1, 2], [0, 1, 3], [0, 2, 4]]
  vertices_nodup := by decide
  edge_nodup := by decide
  edge_vertices := by decide
  simple := by decide

theorem firstUniform : firstBranch.Uniform 3 := by
  simp [FiniteHypergraph.Uniform, firstBranch]

theorem secondUniform : secondBranch.Uniform 3 := by
  simp [FiniteHypergraph.Uniform, secondBranch]

theorem joinedUniform : joinedBranches.Uniform 3 := by
  simp [FiniteHypergraph.Uniform, joinedBranches]

theorem amalgam : EdgeAmalgam firstBranch secondBranch joinedBranches [0, 1, 2] where
  vertices_union := by
    intro vertex
    simp [firstBranch, secondBranch, joinedBranches, or_assoc, or_left_comm, or_comm]
  vertices_intersection := by
    intro vertex
    simp only [firstBranch, secondBranch, List.mem_cons, List.not_mem_nil, or_false]
    omega
  edges_union := by
    intro edge
    simp [FiniteHypergraph.HasEdge, firstBranch, secondBranch, joinedBranches,
      or_assoc, or_left_comm, or_comm]
  first_root := firstBranch.hasEdge_of_mem (by decide)
  second_root := secondBranch.hasEdge_of_mem (by decide)

def firstEmbedding : Embedding firstBranch joinedBranches where
  toFun := id
  maps_vertices := by
    intro vertex present
    simpa [firstBranch, joinedBranches] using
      (List.mem_append_left [4] present)
  injective := by
    intro first _ second _ equal
    exact equal
  maps_edges := by
    intro edge present
    simp only [List.map_id]
    apply joinedBranches.hasEdge_of_mem
    simpa [firstBranch, joinedBranches] using
      (List.mem_append_left [[0, 2, 4]] present)

def secondEmbedding : Embedding secondBranch joinedBranches where
  toFun := id
  maps_vertices := by
    intro vertex present
    simp only [secondBranch, joinedBranches, List.mem_cons, List.not_mem_nil, or_false, id_eq] at present ⊢
    omega
  injective := by
    intro first _ second _ equal
    exact equal
  maps_edges := by
    intro edge present
    simp only [List.map_id]
    apply joinedBranches.hasEdge_of_mem
    simp only [secondBranch, joinedBranches, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
    rcases present with rootEdge | leafEdge
    · exact Or.inl rootEdge
    · exact Or.inr (Or.inr leafEdge)

theorem firstSupported : AnchoredSupport firstBranch joinedBranches [0, 1, 2] id [3] := by
  refine ⟨firstEmbedding, ?_, ?_⟩
  · intro vertex _
    rfl
  · intro vertex present
    simpa [firstEmbedding, firstBranch] using present

theorem secondSupported : AnchoredSupport secondBranch joinedBranches [0, 1, 2] id [4] := by
  refine ⟨secondEmbedding, ?_, ?_⟩
  · intro vertex _
    rfl
  · intro vertex present
    simpa [secondEmbedding, secondBranch] using present

example : AnchoredSupport joinedBranches joinedBranches [0, 1, 2] id [3, 4] :=
  anchoredSupport_glue firstBranch secondBranch joinedBranches joinedBranches [0, 1, 2] id
    amalgam [3] [4] (by decide) firstSupported secondSupported

example : joinedBranches.HasEdge [2, 0, 1] :=
  (joinedBranches.hasEdge_perm (show [0, 1, 2].Perm [2, 0, 1] from by decide)).mp
    (joinedBranches.hasEdge_of_mem (by decide))

theorem firstNotEmpty : ¬ AnchoredSupport firstBranch joinedBranches [0, 1, 2] id [] := by
  rintro ⟨embedding, anchored, inPrefix⟩
  have impossible := embedding.nonRoot_image_mem [0, 1, 2] id []
    (fun _ present => firstBranch.hasEdge_vertex amalgam.first_root present)
    anchored inPrefix 3 (by decide) (by decide)
  exact List.not_mem_nil impossible

theorem joinedNotOne : ¬ AnchoredSupport joinedBranches joinedBranches [0, 1, 2] id [3] := by
  rintro ⟨embedding, anchored, inPrefix⟩
  have rootVertices : ∀ vertex, vertex ∈ [0, 1, 2] → vertex ∈ joinedBranches.vertices := by
    decide
  have firstImage := embedding.nonRoot_image_mem [0, 1, 2] id [3]
    rootVertices anchored inPrefix 3 (by decide) (by decide)
  have secondImage := embedding.nonRoot_image_mem [0, 1, 2] id [3]
    rootVertices anchored inPrefix 4 (by decide) (by decide)
  have collision := embedding.injective 3 (by decide) 4 (by decide)
    ((List.mem_singleton.mp firstImage).trans (List.mem_singleton.mp secondImage).symm)
  omega

theorem frame : EdgeFirstFrame joinedBranches [0, 1, 2] id [3, 4] where
  marking_edge := joinedBranches.hasEdge_of_mem (by decide)
  enumeration := by decide

def source : EnumeratedGluingSource [3, 4]
    (AnchoredSupport firstBranch joinedBranches [0, 1, 2] id)
    (AnchoredSupport joinedBranches joinedBranches [0, 1, 2] id) :=
  ⟨⟨[3], [4]⟩, List.Perm.refl _, firstSupported, joinedNotOne⟩

example : (anchoredGluingMap firstBranch secondBranch joinedBranches joinedBranches
    [0, 1, 2] id amalgam [3, 4] frame source).val = (⟨[], [3, 4]⟩ : Cut Nat) := by
  change rotate (AnchoredSupport firstBranch joinedBranches [0, 1, 2] id)
    ⟨[3], [4]⟩ = _
  apply rotate_blocks _ [3] [] [4]
  refine ⟨firstSupported, ?_⟩
  intro index shorter
  have indexZero : index = 0 := by simpa using shorter
  simpa [indexZero] using firstNotEmpty

end Kalai.HypergraphTests
