import Kalai.DividerCounts
import Kalai.TransferCounts

namespace Kalai

universe u v

variable {Vertex : Type u} {Target : Type u} {Host : Type v}

def factorial : Nat → Nat
  | 0 => 1
  | size + 1 => (size + 1) * factorial size

theorem factorial_positive (size : Nat) : 0 < factorial size := by
  induction size with
  | zero => decide
  | succ size inductionHypothesis =>
    exact Nat.mul_pos (by omega) inductionHypothesis

def insertAtCut (marker : Vertex) (remaining : List Vertex)
    (state : {state : Cut Vertex // state.word.Perm remaining}) :
    {word : List Vertex // word.Perm (marker :: remaining)} :=
  ⟨state.val.prefix ++ marker :: state.val.suffix,
    List.perm_middle.trans (state.property.cons marker)⟩

theorem insertAtCut_injective (marker : Vertex) (remaining : List Vertex)
    (fresh : marker ∉ remaining)
    (first second : {state : Cut Vertex // state.word.Perm remaining})
    (same : insertAtCut marker remaining first = insertAtCut marker remaining second) :
    first = second := by
  classical
  have firstAbsent : marker ∉ first.val.prefix := by
    intro present
    exact fresh (first.property.mem_iff.mp (List.mem_append_left first.val.suffix present))
  have secondAbsent : marker ∉ second.val.prefix := by
    intro present
    exact fresh (second.property.mem_iff.mp (List.mem_append_left second.val.suffix present))
  have sameWords := congrArg Subtype.val same
  change first.val.prefix ++ marker :: first.val.suffix =
    second.val.prefix ++ marker :: second.val.suffix at sameWords
  have sameIndex := congrArg (fun word : List Vertex => word.idxOf marker) sameWords
  simp only [List.idxOf_append, if_neg firstAbsent, if_neg secondAbsent,
    List.idxOf_cons_self, Nat.add_zero, Nat.zero_add] at sameIndex
  have samePrefix := List.append_inj_left sameWords sameIndex
  have sameSuffix := (List.cons.inj (List.append_inj_right sameWords sameIndex)).2
  apply Subtype.ext
  exact Cut.eq_of_word_and_divider first.val second.val
    (by simp only [Cut.word, samePrefix, sameSuffix]) sameIndex

theorem insertAtCut_surjective (marker : Vertex) (remaining : List Vertex)
    (word : {word : List Vertex // word.Perm (marker :: remaining)}) :
    ∃ state, insertAtCut marker remaining state = word := by
  have markerPresent : marker ∈ word.val := word.property.mem_iff.mpr (by simp)
  obtain ⟨before, after, splitWord⟩ := List.mem_iff_append.mp markerPresent
  have ordering := word.property
  rw [splitWord] at ordering
  have removed : (before ++ after).Perm remaining :=
    (List.perm_middle.symm.trans ordering).cons_inv
  exact ⟨⟨⟨before, after⟩, removed⟩, Subtype.ext splitWord.symm⟩

theorem orderingUniverse_cons_card (marker : Vertex) (remaining : List Vertex)
    (fresh : marker ∉ remaining) :
    (orderingUniverse (marker :: remaining)).card = (cutUniverse remaining).card :=
  ((cutUniverse remaining).card_eq_of_bijection (orderingUniverse (marker :: remaining))
    (insertAtCut marker remaining) (insertAtCut_injective marker remaining fresh)
    (insertAtCut_surjective marker remaining)).symm

theorem orderingUniverse_nil_card : (orderingUniverse ([] : List Vertex)).card = 1 := by
  simp [orderingUniverse, wordsOfLength, ListingFor.ofCover, ListingFor.card, uniqueItems]

theorem orderingUniverse_card_factorial (remaining : List Vertex) (distinct : remaining.Nodup) :
    (orderingUniverse remaining).card = factorial remaining.length := by
  induction remaining with
  | nil => exact orderingUniverse_nil_card
  | cons marker remaining inductionHypothesis =>
    rw [orderingUniverse_cons_card marker remaining (List.nodup_cons.mp distinct).1,
      cutUniverse_card, inductionHypothesis (List.nodup_cons.mp distinct).2]
    simp only [List.length_cons, factorial, Nat.mul_comm]

theorem cutUniverse_card_factorial (remaining : List Vertex) (distinct : remaining.Nodup) :
    (cutUniverse remaining).card = factorial (remaining.length + 1) := by
  rw [cutUniverse_card, orderingUniverse_card_factorial remaining distinct]
  simp only [factorial, Nat.mul_comm]

theorem shadowOrderingCount_factorial (host : FiniteHypergraph Host) (face remaining : List Host)
    (distinct : remaining.Nodup) (inShadow : FaceInShadow host face) :
    shadowOrderingCount host face remaining = factorial remaining.length := by
  rw [shadowOrderingCount_of_shadow host face remaining inShadow,
    orderingUniverse_card_factorial remaining distinct]

theorem anchored_gluing_count_factorial (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target) (rootMap : Target → Host)
    (amalgam : EdgeAmalgam first second joined root) (remaining : List Host)
    (frame : EdgeFirstFrame host root rootMap remaining) :
    cutCount remaining (AnchoredSupport first host root rootMap) +
      cutCount remaining (AnchoredSupport second host root rootMap) ≤
      factorial (remaining.length + 1) + cutCount remaining (AnchoredSupport joined host root rootMap) := by
  have bound := anchored_gluing_count first second joined host root rootMap amalgam remaining frame
  rw [cutUniverse_card_factorial remaining (frame.remaining_nodup host root rootMap remaining)] at bound
  exact bound

theorem leaf_transfer_count_factorial (smaller larger : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (faceMap : Target → Host)
    (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (remaining : List Host) (frame : FaceFrame host (face.map faceMap) remaining) :
    markedCount remaining (SupportsAt smaller host face faceMap oldEndpoint) ≤
      markedCount remaining (SupportsAt larger host face faceMap newVertex) + factorial remaining.length := by
  have distinct : remaining.Nodup :=
    List.Sublist.nodup (List.sublist_append_right (face.map faceMap) remaining)
      (frame.enumeration.nodup_iff.mpr host.vertices_nodup)
  have bound := leaf_transfer_count_orderings smaller larger host face faceMap oldEndpoint newVertex
    extension remaining frame
  rw [orderingUniverse_card_factorial remaining distinct] at bound
  exact bound

end Kalai
