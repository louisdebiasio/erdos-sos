import Digraph.PrefixRotation

namespace Digraph

universe u v
variable {Host : Type v}

structure MarkedCut (Vertex : Type u) where
  before : List Vertex
  marker : Vertex
  after : List Vertex
  deriving DecidableEq, Repr

def MarkedCut.word (state : MarkedCut Host) : List Host :=
  state.before ++ state.marker :: state.after

def MarkedCut.prefixList (state : MarkedCut Host) : List Host :=
  state.before ++ [state.marker]

theorem MarkedCut.eq_of_word_index (source target : MarkedCut Host)
    (sameWord : source.word = target.word)
    (sameIndex : source.before.length = target.before.length) : source = target := by
  have sameBefore : source.before = target.before := by
    calc
      source.before = source.word.take source.before.length := by simp [MarkedCut.word]
      _ = target.word.take target.before.length := by rw [sameWord, sameIndex]
      _ = target.before := by simp [MarkedCut.word]
  have sameRest : source.marker :: source.after = target.marker :: target.after :=
    List.append_cancel_left (by simpa only [MarkedCut.word, sameBefore] using sameWord)
  have sameMarker := (List.cons.inj sameRest).1
  have sameAfter := (List.cons.inj sameRest).2
  cases source
  cases target
  simp_all

theorem MarkedCut.prefixList_eq_take (state : MarkedCut Host) :
    state.prefixList = state.word.take (state.before.length + 1) := by
  simp [MarkedCut.prefixList, MarkedCut.word, List.take_append]

theorem MarkedCut.earlier_prefix_subset (earlier later : MarkedCut Host)
    (sameWord : earlier.word = later.word)
    (earlierIndex : earlier.before.length < later.before.length) :
    ∀ vertex, vertex ∈ earlier.prefixList → vertex ∈ later.before := by
  intro vertex present
  have bound : earlier.before.length + 1 ≤ later.before.length := by omega
  rw [earlier.prefixList_eq_take, sameWord, MarkedCut.word,
    List.take_append_of_le_length bound] at present
  exact List.mem_of_mem_take present

theorem MarkedCut.marker_not_before (face : List Host) (state : MarkedCut Host)
    (noDuplicates : (face ++ state.word).Nodup) : state.marker ∉ face ++ state.before := by
  intro repeated
  have distinct : ((face ++ state.before) ++ state.marker :: state.after).Nodup := by
    simpa only [MarkedCut.word, List.append_assoc] using noDuplicates
  exact (List.pairwise_append.mp distinct).2.2 state.marker repeated state.marker (by simp) rfl

theorem MarkedCut.marker_not_earlier (face : List Host) (earlier later : MarkedCut Host)
    (sameWord : earlier.word = later.word)
    (earlierIndex : earlier.before.length < later.before.length)
    (noDuplicates : (face ++ later.word).Nodup) :
    later.marker ∉ face ++ earlier.prefixList := by
  intro repeated
  apply later.marker_not_before face noDuplicates
  rcases List.mem_append.mp repeated with inFace | inEarlier
  · exact List.mem_append.mpr (Or.inl inFace)
  · exact List.mem_append.mpr (Or.inr
      (MarkedCut.earlier_prefix_subset earlier later sameWord earlierIndex _ inEarlier))

def EarlierSupported (supports : MarkedCut Host → Prop) (state : MarkedCut Host) : Prop :=
  ∃ earlier, earlier.word = state.word ∧ earlier.before.length < state.before.length ∧ supports earlier

theorem first_exception_word_injective (supports : MarkedCut Host → Prop)
    (source target : MarkedCut Host) (sourceSupported : supports source)
    (targetSupported : supports target) (sourceFirst : ¬ EarlierSupported supports source)
    (targetFirst : ¬ EarlierSupported supports target) (sameWord : source.word = target.word) :
    source = target := by
  apply MarkedCut.eq_of_word_index source target sameWord
  by_cases before : source.before.length < target.before.length
  · exact False.elim (targetFirst ⟨source, sameWord, before, sourceSupported⟩)
  · by_cases after : target.before.length < source.before.length
    · exact False.elim (sourceFirst ⟨target, sameWord.symm, after, targetSupported⟩)
    · omega


end Digraph
