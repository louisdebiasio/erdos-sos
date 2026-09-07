import LeafTests

namespace Kalai.CountingTests

open Kalai.HypergraphTests

theorem empty_orderings : (orderingUniverse ([] : List Nat)).card = 1 := by
  simp [orderingUniverse, wordsOfLength, ListingFor.ofCover, ListingFor.card, uniqueItems]

theorem singleton_orderings : (orderingUniverse [7]).card = 1 := by
  simp [orderingUniverse, wordsOfLength, ListingFor.ofCover, ListingFor.card, uniqueItems]

theorem pair_orderings : (orderingUniverse [2, 3]).card = 2 := by
  have reversed : ([3, 2] : List Nat).Perm [2, 3] := by decide
  have repeated : ¬ ([3, 3] : List Nat).Perm [2, 3] := by decide
  simp [orderingUniverse, wordsOfLength, ListingFor.ofCover, ListingFor.card, uniqueItems,
    reversed, repeated]

example : (orderingUniverse [7, 7]).card = 1 := by
  simp [orderingUniverse, wordsOfLength, ListingFor.ofCover, ListingFor.card, uniqueItems]

example : (cutUniverse ([] : List Nat)).card = 1 := by
  rw [cutUniverse_card, empty_orderings]
  rfl

example : (cutUniverse [7]).card = 2 := by
  rw [cutUniverse_card, singleton_orderings]
  rfl

example : (cutUniverse [2, 3]).card = 6 := by
  rw [cutUniverse_card, pair_orderings]
  rfl

example : markedCount ([] : List Nat) (fun _ => True) = 0 := by
  apply markedCount_eq_zero_of_unsupported
  intro state ordering _
  have lengthEquality := ordering.length_eq
  simp [MarkedCut.word] at lengthEquality

example : cutCount [2, 3] (fun _ => False) = 0 :=
  cutCount_eq_zero_of_unsupported _ _ (fun _ _ impossible => impossible)

example : cutDecode [2, 3] (cutEncode [2, 3]
    ⟨⟨[3, 2], []⟩, by decide⟩) = ⟨⟨[3, 2], []⟩, by decide⟩ :=
  cutDecode_encode _ _

example : cutDecode [2, 3] (cutEncode [2, 3]
    ⟨⟨[], [2, 3]⟩, by decide⟩) = ⟨⟨[], [2, 3]⟩, by decide⟩ :=
  cutDecode_encode _ _

theorem local_exception_count : shadowOrderingCount firstBranch [0, 1] [2, 3] = 2 := by
  rw [shadowOrderingCount_of_shadow firstBranch [0, 1] [2, 3]
    ⟨2, firstBranch.hasEdge_of_mem (by decide)⟩]
  exact pair_orderings

example : markedCount [2, 3] (SupportsAt LeafTests.smaller firstBranch [0, 1] id 2) ≤
    markedCount [2, 3] (SupportsAt firstBranch firstBranch [0, 1] id 3) + 2 := by
  have bound := leaf_transfer_count LeafTests.smaller firstBranch firstBranch [0, 1] id 2 3
    LeafTests.extension [2, 3] LeafTests.faceFrame
  simpa only [List.map_id, local_exception_count] using bound

example : cutCount [3, 4] (AnchoredSupport firstBranch joinedBranches [0, 1, 2] id) +
    cutCount [3, 4] (AnchoredSupport secondBranch joinedBranches [0, 1, 2] id) ≤
    (cutUniverse [3, 4]).card + cutCount [3, 4] (AnchoredSupport joinedBranches joinedBranches [0, 1, 2] id) :=
  anchored_gluing_count firstBranch secondBranch joinedBranches joinedBranches [0, 1, 2] id
    amalgam [3, 4] frame

end Kalai.CountingTests
