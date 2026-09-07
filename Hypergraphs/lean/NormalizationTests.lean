import CountingTests

namespace Kalai.NormalizationTests

open Kalai.HypergraphTests

example : factorial 0 = 1 := rfl

example : factorial 6 = 720 := by decide

example : (orderingUniverse ([0, 1, 2, 3] : List Nat)).card = 24 := by
  rw [orderingUniverse_card_factorial _ (by decide)]
  rfl

example : (orderingUniverse ([0, 1, 2, 3, 4, 5, 6] : List Nat)).card = 5040 := by
  rw [orderingUniverse_card_factorial _ (by decide)]
  rfl

example : (cutUniverse ([0, 1, 2] : List Nat)).card = 24 := by
  rw [cutUniverse_card_factorial _ (by decide)]
  rfl

example : (markedUniverse ([] : List Nat)).card = 0 := by
  simp only [markedUniverse_card, List.length_nil, Nat.zero_mul]

example : (markedUniverse ([0, 1, 2] : List Nat)).card = 18 := by
  rw [markedUniverse_card_factorial _ (by decide)]
  rfl

example : (fixedMarkerListing 9 ([0, 1] : List Nat)).card = 6 := by
  rw [fixedMarkerListing_card_factorial _ _ (by decide)]
  rfl

example : (fixedMarkerListing 7 ([7] : List Nat)).card = 2 := by
  rw [fixedMarkerListing_card_factorial _ _ (by decide)]
  rfl

example : insertAtCut 0 [0] ⟨⟨[], [0]⟩, by decide⟩ =
    insertAtCut 0 [0] ⟨⟨[0], []⟩, by decide⟩ := rfl

example : (⟨[], [0]⟩ : Cut Nat) ≠ ⟨[0], []⟩ := by decide

example : insertAtCut 9 [0, 1] ⟨⟨[], [1, 0]⟩, by decide⟩ =
    ⟨[9, 1, 0], by decide⟩ := rfl

example : insertAtCut 9 [0, 1] ⟨⟨[1, 0], []⟩, by decide⟩ =
    ⟨[1, 0, 9], by decide⟩ := rfl

example : rootSliceCount firstBranch firstBranch [0, 1] id 3 3 [2] =
    cutCount [2] (AnchoredSupport firstBranch firstBranch [0, 1, 3] (endpointMap id 3 3)) :=
  rootSliceCount_eq_cutCount firstBranch firstBranch [0, 1] id 3
    (firstBranch.hasEdge_of_mem (by decide)) 3 [2]

example : shadowOrderingCount firstBranch [0, 1] [2, 3] = factorial 2 :=
  shadowOrderingCount_factorial firstBranch [0, 1] [2, 3] (by decide)
    ⟨2, firstBranch.hasEdge_of_mem (by decide)⟩

example : markedCount [2, 3] (SupportsAt LeafTests.smaller firstBranch [0, 1] id 2) ≤
    markedCount [2, 3] (SupportsAt firstBranch firstBranch [0, 1] id 3) + factorial 2 :=
  leaf_transfer_count_factorial LeafTests.smaller firstBranch firstBranch [0, 1] id 2 3
    LeafTests.extension [2, 3] LeafTests.faceFrame

example : cutCount [3, 4] (AnchoredSupport firstBranch joinedBranches [0, 1, 2] id) +
    cutCount [3, 4] (AnchoredSupport secondBranch joinedBranches [0, 1, 2] id) ≤
    factorial 3 + cutCount [3, 4] (AnchoredSupport joinedBranches joinedBranches [0, 1, 2] id) :=
  anchored_gluing_count_factorial firstBranch secondBranch joinedBranches joinedBranches [0, 1, 2] id
    amalgam [3, 4] frame

end Kalai.NormalizationTests
