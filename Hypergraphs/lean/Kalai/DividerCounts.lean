import Kalai.StateEnumeration

namespace Kalai

universe u

variable {Vertex : Type u}

def cutEncode (remaining : List Vertex)
    (state : {state : Cut Vertex // state.word.Perm remaining}) :
    {pair : List Vertex × Nat // pair.1.Perm remaining ∧ pair.2 < remaining.length + 1} := by
  refine ⟨(state.val.word, state.val.prefix.length), state.property, ?_⟩
  have lengthEquality := state.property.length_eq
  simp only [Cut.word, List.length_append] at lengthEquality
  omega

theorem cutEncode_injective (remaining : List Vertex)
    (first second : {state : Cut Vertex // state.word.Perm remaining})
    (same : cutEncode remaining first = cutEncode remaining second) : first = second := by
  have pairEquality := congrArg Subtype.val same
  apply Subtype.ext
  exact Cut.eq_of_word_and_divider first.val second.val
    (congrArg Prod.fst pairEquality) (congrArg Prod.snd pairEquality)

def cutDecode (remaining : List Vertex)
    (pair : {pair : List Vertex × Nat // pair.1.Perm remaining ∧ pair.2 < remaining.length + 1}) :
    {state : Cut Vertex // state.word.Perm remaining} :=
  ⟨Cut.ofWord pair.val.1 pair.val.2, by rw [Cut.word_ofWord]; exact pair.property.1⟩

theorem cutEncode_decode (remaining : List Vertex)
    (pair : {pair : List Vertex × Nat // pair.1.Perm remaining ∧ pair.2 < remaining.length + 1}) :
    cutEncode remaining (cutDecode remaining pair) = pair := by
  have lengthEquality := pair.property.1.length_eq
  have indexBound := pair.property.2
  apply Subtype.ext
  apply Prod.ext
  · exact Cut.word_ofWord pair.val.1 pair.val.2
  · exact Cut.divider_ofWord pair.val.1 pair.val.2 (by omega)

theorem cutDecode_encode (remaining : List Vertex)
    (state : {state : Cut Vertex // state.word.Perm remaining}) :
    cutDecode remaining (cutEncode remaining state) = state :=
  Subtype.ext (Cut.ofWord_word state.val)

theorem cutUniverse_card (remaining : List Vertex) :
    (cutUniverse remaining).card = (orderingUniverse remaining).card * (remaining.length + 1) := by
  let pairs := (orderingUniverse remaining).product (rangeListing (remaining.length + 1))
  have forward := (cutUniverse remaining).card_le_of_injection pairs
    (cutEncode remaining) (cutEncode_injective remaining)
  have backward := pairs.card_le_of_injection (cutUniverse remaining) (cutDecode remaining) (by
    intro first second same
    have encoded := congrArg (cutEncode remaining) same
    simpa only [cutEncode_decode] using encoded)
  have countEquality := Nat.le_antisymm forward backward
  simpa only [pairs, ListingFor.product_card, rangeListing_card] using countEquality

end Kalai
