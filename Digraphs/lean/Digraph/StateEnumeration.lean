import Digraph.FiniteCounting
import Digraph.MarkedStates

namespace Digraph

universe u

variable {Vertex : Type u}

def wordsOfLength (alphabet : List Vertex) : Nat → List (List Vertex)
  | 0 => [[]]
  | length + 1 => alphabet.flatMap (fun head =>
      (wordsOfLength alphabet length).map (fun tail => head :: tail))

theorem wordsOfLength_complete (alphabet word : List Vertex)
    (contained : ∀ vertex ∈ word, vertex ∈ alphabet) :
    word ∈ wordsOfLength alphabet word.length := by
  induction word with
  | nil => simp [wordsOfLength]
  | cons head tail inductionHypothesis =>
    apply List.mem_flatMap.mpr
    refine ⟨head, contained head (by simp), ?_⟩
    exact List.mem_map.mpr ⟨tail,
      inductionHypothesis (fun vertex present => contained vertex (by simp [present])), rfl⟩

theorem permutation_in_words (remaining word : List Vertex) (ordering : word.Perm remaining) :
    word ∈ wordsOfLength remaining remaining.length := by
  rw [← ordering.length_eq]
  exact wordsOfLength_complete remaining word (fun _ present => ordering.mem_iff.mp present)

def cutCandidates (remaining : List Vertex) : List (Cut Vertex) :=
  (wordsOfLength remaining remaining.length).flatMap (fun word =>
    (List.range (remaining.length + 1)).map (Cut.ofWord word))

theorem cutCandidates_complete (remaining : List Vertex) (state : Cut Vertex)
    (ordering : state.word.Perm remaining) : state ∈ cutCandidates remaining := by
  apply List.mem_flatMap.mpr
  refine ⟨state.word, permutation_in_words remaining state.word ordering, ?_⟩
  apply List.mem_map.mpr
  refine ⟨state.prefix.length, ?_, Cut.ofWord_word state⟩
  apply List.mem_range.mpr
  have lengthEquality := ordering.length_eq
  simp only [Cut.word, List.length_append] at lengthEquality
  omega

def marksOfWord : List Vertex → List (MarkedCut Vertex)
  | [] => []
  | head :: tail => ⟨[], head, tail⟩ ::
      (marksOfWord tail).map (fun state => ⟨head :: state.before, state.marker, state.after⟩)

theorem marksOfWord_complete (state : MarkedCut Vertex) : state ∈ marksOfWord state.word := by
  rcases state with ⟨before, marker, after⟩
  induction before with
  | nil => simp [MarkedCut.word, marksOfWord]
  | cons head tail inductionHypothesis =>
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨⟨tail, marker, after⟩, inductionHypothesis, rfl⟩

def markedCandidates (remaining : List Vertex) : List (MarkedCut Vertex) :=
  (wordsOfLength remaining remaining.length).flatMap marksOfWord

theorem markedCandidates_complete (remaining : List Vertex) (state : MarkedCut Vertex)
    (ordering : state.word.Perm remaining) : state ∈ markedCandidates remaining :=
  List.mem_flatMap.mpr ⟨state.word, permutation_in_words remaining state.word ordering,
    marksOfWord_complete state⟩

noncomputable def cutUniverse (remaining : List Vertex) :
    ListingFor (fun state : Cut Vertex => state.word.Perm remaining) :=
  ListingFor.ofCover (cutCandidates remaining) (fun state => state.word.Perm remaining)
    (cutCandidates_complete remaining)

noncomputable def markedUniverse (remaining : List Vertex) :
    ListingFor (fun state : MarkedCut Vertex => state.word.Perm remaining) :=
  ListingFor.ofCover (markedCandidates remaining) (fun state => state.word.Perm remaining)
    (markedCandidates_complete remaining)

noncomputable def orderingUniverse (remaining : List Vertex) :
    ListingFor (fun word : List Vertex => word.Perm remaining) :=
  ListingFor.ofCover (wordsOfLength remaining remaining.length)
    (fun word => word.Perm remaining) (permutation_in_words remaining)

noncomputable def cutListing (remaining : List Vertex) (support : List Vertex → Prop) :=
  (cutUniverse remaining).restrict (fun state => support state.prefix)

noncomputable def markedListing (remaining : List Vertex) (support : MarkedCut Vertex → Prop) :=
  (markedUniverse remaining).restrict support

noncomputable def cutCount (remaining : List Vertex) (support : List Vertex → Prop) : Nat :=
  (cutListing remaining support).card

noncomputable def markedCount (remaining : List Vertex) (support : MarkedCut Vertex → Prop) : Nat :=
  (markedListing remaining support).card

end Digraph
