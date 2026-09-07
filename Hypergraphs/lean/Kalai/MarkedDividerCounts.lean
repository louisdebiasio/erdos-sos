import Kalai.FactorialCounts

namespace Kalai

universe u

variable {Vertex : Type u}

def markedAsCut (remaining : List Vertex)
    (state : {state : MarkedCut Vertex // state.word.Perm remaining}) :
    {state : Cut Vertex // state.word.Perm remaining ∧ state.suffix ≠ []} :=
  ⟨⟨state.val.before, state.val.marker :: state.val.after⟩, state.property, by simp⟩

theorem markedAsCut_injective (remaining : List Vertex)
    (first second : {state : MarkedCut Vertex // state.word.Perm remaining})
    (same : markedAsCut remaining first = markedAsCut remaining second) : first = second := by
  have sameCuts := congrArg Subtype.val same
  apply Subtype.ext
  apply MarkedCut.eq_of_word_index first.val second.val
  · exact congrArg Cut.word sameCuts
  · exact congrArg (fun state : Cut Vertex => state.prefix.length) sameCuts

theorem markedAsCut_surjective (remaining : List Vertex)
    (state : {state : Cut Vertex // state.word.Perm remaining ∧ state.suffix ≠ []}) :
    ∃ marked, markedAsCut remaining marked = state := by
  rcases state with ⟨⟨before, suffix⟩, ordering, nonempty⟩
  cases suffix with
  | nil => exact False.elim (nonempty rfl)
  | cons marker after => exact ⟨⟨⟨before, marker, after⟩, ordering⟩, rfl⟩

theorem markedUniverse_eq_nonterminal (remaining : List Vertex) :
    (markedUniverse remaining).card =
      ((cutUniverse remaining).restrict (fun state => state.suffix ≠ [])).card :=
  (markedUniverse remaining).card_eq_of_bijection
    ((cutUniverse remaining).restrict (fun state => state.suffix ≠ []))
    (markedAsCut remaining) (markedAsCut_injective remaining) (markedAsCut_surjective remaining)

def orderingAsTerminalCut (remaining : List Vertex)
    (word : {word : List Vertex // word.Perm remaining}) :
    {state : Cut Vertex // state.word.Perm remaining ∧ state.suffix = []} :=
  ⟨⟨word.val, []⟩, by simpa only [Cut.word, List.append_nil] using word.property, rfl⟩

theorem orderingAsTerminalCut_injective (remaining : List Vertex)
    (first second : {word : List Vertex // word.Perm remaining})
    (same : orderingAsTerminalCut remaining first = orderingAsTerminalCut remaining second) :
    first = second :=
  Subtype.ext (congrArg Cut.prefix (congrArg Subtype.val same))

theorem orderingAsTerminalCut_surjective (remaining : List Vertex)
    (state : {state : Cut Vertex // state.word.Perm remaining ∧ state.suffix = []}) :
    ∃ word, orderingAsTerminalCut remaining word = state := by
  rcases state with ⟨⟨before, after⟩, ordering, terminal⟩
  change after = [] at terminal
  subst after
  exact ⟨⟨before, by simpa only [Cut.word, List.append_nil] using ordering⟩, rfl⟩

theorem terminalCut_count (remaining : List Vertex) :
    ((cutUniverse remaining).restrict (fun state => state.suffix = [])).card =
      (orderingUniverse remaining).card :=
  ((orderingUniverse remaining).card_eq_of_bijection
    ((cutUniverse remaining).restrict (fun state => state.suffix = []))
    (orderingAsTerminalCut remaining) (orderingAsTerminalCut_injective remaining)
    (orderingAsTerminalCut_surjective remaining)).symm

theorem markedUniverse_card (remaining : List Vertex) :
    (markedUniverse remaining).card = remaining.length * (orderingUniverse remaining).card := by
  have partition := (cutUniverse remaining).restrict_card_complement (fun state => state.suffix = [])
  rw [← markedUniverse_eq_nonterminal remaining, terminalCut_count remaining,
    cutUniverse_card, Nat.mul_add, Nat.mul_one] at partition
  have bound : (markedUniverse remaining).card = (orderingUniverse remaining).card * remaining.length := by
    omega
  simpa only [Nat.mul_comm] using bound

theorem markedUniverse_card_factorial (remaining : List Vertex) (distinct : remaining.Nodup) :
    (markedUniverse remaining).card = remaining.length * factorial remaining.length := by
  rw [markedUniverse_card, orderingUniverse_card_factorial remaining distinct]

end Kalai
