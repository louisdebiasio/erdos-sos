import Std

namespace Digraph

universe u

variable {Vertex : Type u}

structure Cut (Vertex : Type u) where
  «prefix» : List Vertex
  suffix : List Vertex
  deriving DecidableEq, Repr

def Cut.word (state : Cut Vertex) : List Vertex :=
  state.prefix ++ state.suffix

def Cut.ofWord (word : List Vertex) (divider : Nat) : Cut Vertex :=
  ⟨word.take divider, word.drop divider⟩

theorem Cut.word_ofWord (word : List Vertex) (divider : Nat) :
    (Cut.ofWord word divider).word = word := by
  simp [Cut.ofWord, Cut.word]

theorem Cut.ofWord_word (state : Cut Vertex) :
    Cut.ofWord state.word state.prefix.length = state := by
  simp [Cut.ofWord, Cut.word]

theorem Cut.divider_ofWord (word : List Vertex) (divider : Nat)
    (validDivider : divider ≤ word.length) :
    (Cut.ofWord word divider).prefix.length = divider := by
  simp [Cut.ofWord, Nat.min_eq_left validDivider]

theorem Cut.eq_of_word_and_divider (source target : Cut Vertex)
    (sameWord : source.word = target.word)
    (sameDivider : source.prefix.length = target.prefix.length) : source = target := by
  calc
    source = Cut.ofWord source.word source.prefix.length := (Cut.ofWord_word source).symm
    _ = Cut.ofWord target.word target.prefix.length := by rw [sameWord, sameDivider]
    _ = target := Cut.ofWord_word target

def FirstSupport (supports : List Vertex → Prop) (block : List Vertex) : Prop :=
  supports block ∧ ∀ index, index < block.length → ¬ supports (block.take index)

def HasSupportingPrefix (supports : List Vertex → Prop) (word : List Vertex) : Prop :=
  ∃ index, index ≤ word.length ∧ supports (word.take index)

private theorem exists_least_index (predicate : Nat → Prop) (bound : Nat)
    (witness : predicate bound) :
    ∃ index, index ≤ bound ∧ predicate index ∧
      ∀ earlier, earlier < index → ¬ predicate earlier := by
  classical
  induction bound using Nat.strongRecOn with
  | ind bound inductionHypothesis =>
    by_cases earlierExists : ∃ earlier, earlier < bound ∧ predicate earlier
    · obtain ⟨earlier, earlierBound, earlierWitness⟩ := earlierExists
      obtain ⟨index, indexBound, indexWitness, minimal⟩ :=
        inductionHypothesis earlier earlierBound earlierWitness
      exact ⟨index, by omega, indexWitness, minimal⟩
    · exact ⟨bound, Nat.le_refl bound, witness,
        fun earlier earlierBound earlierWitness =>
          earlierExists ⟨earlier, earlierBound, earlierWitness⟩⟩

theorem exists_least_supporting_prefix (supports : List Vertex → Prop)
    (word : List Vertex) (existsPrefix : HasSupportingPrefix supports word) :
    ∃ index, index ≤ word.length ∧ supports (word.take index) ∧
      ∀ earlier, earlier < index → ¬ supports (word.take earlier) := by
  obtain ⟨bound, boundLength, witness⟩ := existsPrefix
  obtain ⟨index, indexBound, indexWitness, minimal⟩ :=
    exists_least_index (fun index => supports (word.take index)) bound witness
  exact ⟨index, by omega, indexWitness, minimal⟩

noncomputable def firstIndex (supports : List Vertex → Prop) (word : List Vertex) : Nat := by
  classical
  exact if existsPrefix : HasSupportingPrefix supports word then
    Classical.choose (exists_least_supporting_prefix supports word existsPrefix)
  else
    0

theorem firstIndex_spec (supports : List Vertex → Prop) (word : List Vertex)
    (existsPrefix : HasSupportingPrefix supports word) :
    firstIndex supports word ≤ word.length ∧
      supports (word.take (firstIndex supports word)) ∧
      ∀ earlier, earlier < firstIndex supports word → ¬ supports (word.take earlier) := by
  classical
  simp only [firstIndex, dif_pos existsPrefix]
  exact Classical.choose_spec (exists_least_supporting_prefix supports word existsPrefix)

theorem firstIndex_eq_length (supports : List Vertex → Prop) (block tail : List Vertex)
    (minimal : FirstSupport supports block) :
    firstIndex supports (block ++ tail) = block.length := by
  have existsPrefix : HasSupportingPrefix supports (block ++ tail) := by
    refine ⟨block.length, ?_, ?_⟩
    · simp
    · simpa using minimal.1
  have specification := firstIndex_spec supports (block ++ tail) existsPrefix
  by_cases tooShort : firstIndex supports (block ++ tail) < block.length
  · have shorterSupport : supports (block.take (firstIndex supports (block ++ tail))) := by
      simpa only [List.take_append_of_le_length (Nat.le_of_lt tooShort)]
        using specification.2.1
    exact False.elim (minimal.2 _ tooShort shorterSupport)
  · by_cases tooLong : block.length < firstIndex supports (block ++ tail)
    · have notSupported := specification.2.2 block.length tooLong
      exact False.elim (notSupported (by simpa using minimal.1))
    · omega

theorem firstIndex_firstSupport (supports : List Vertex → Prop) (word : List Vertex)
    (supported : supports word) :
    FirstSupport supports (word.take (firstIndex supports word)) := by
  have existsPrefix : HasSupportingPrefix supports word :=
    ⟨word.length, Nat.le_refl _, by simpa using supported⟩
  have specification := firstIndex_spec supports word existsPrefix
  refine ⟨specification.2.1, ?_⟩
  intro earlier shorter
  have earlierBound : earlier < firstIndex supports word := by
    simpa only [List.length_take, Nat.min_eq_left specification.1] using shorter
  simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt earlierBound)]
    using specification.2.2 earlier earlierBound

noncomputable def rotate (supports : List Vertex → Prop) (state : Cut Vertex) : Cut Vertex :=
  let index := firstIndex supports state.prefix
  ⟨state.prefix.drop index, state.prefix.take index ++ state.suffix⟩

noncomputable def recover (supports : List Vertex → Prop) (state : Cut Vertex) : Cut Vertex :=
  let index := firstIndex supports state.suffix
  ⟨state.suffix.take index ++ state.prefix, state.suffix.drop index⟩

theorem rotate_blocks (supports : List Vertex → Prop) (first second tail : List Vertex)
    (minimal : FirstSupport supports first) :
    rotate supports ⟨first ++ second, tail⟩ = ⟨second, first ++ tail⟩ := by
  simp [rotate, firstIndex_eq_length supports first second minimal]

theorem recover_blocks (supports : List Vertex → Prop) (first second tail : List Vertex)
    (minimal : FirstSupport supports first) :
    recover supports ⟨second, first ++ tail⟩ = ⟨first ++ second, tail⟩ := by
  simp [recover, firstIndex_eq_length supports first tail minimal]

theorem recover_rotate (supports : List Vertex → Prop) (state : Cut Vertex)
    (supported : supports state.prefix) :
    recover supports (rotate supports state) = state := by
  have minimal := firstIndex_firstSupport supports state.prefix supported
  change recover supports
    ⟨state.prefix.drop (firstIndex supports state.prefix),
      state.prefix.take (firstIndex supports state.prefix) ++ state.suffix⟩ = state
  rw [recover_blocks supports _ _ _ minimal]
  simp only [List.take_append_drop]

theorem rotate_injective_on_support (supports : List Vertex → Prop)
    (source target : Cut Vertex) (sourceSupported : supports source.prefix)
    (targetSupported : supports target.prefix)
    (sameImage : rotate supports source = rotate supports target) : source = target := by
  calc
    source = recover supports (rotate supports source) :=
      (recover_rotate supports source sourceSupported).symm
    _ = recover supports (rotate supports target) := congrArg (recover supports) sameImage
    _ = target := recover_rotate supports target targetSupported

theorem rotate_word_perm (supports : List Vertex → Prop) (state : Cut Vertex) :
    (rotate supports state).word.Perm state.word := by
  have exchange := (List.perm_append_comm
    (l₁ := state.prefix.drop (firstIndex supports state.prefix))
    (l₂ := state.prefix.take (firstIndex supports state.prefix))).append_right state.suffix
  simpa only [List.take_append_drop, List.append_assoc, Cut.word, rotate] using exchange

theorem rotate_anchored_word_perm (supports : List Vertex → Prop)
    (anchor : List Vertex) (state : Cut Vertex) :
    (anchor ++ (rotate supports state).word).Perm (anchor ++ state.word) :=
  (rotate_word_perm supports state).append_left anchor

theorem rotate_nodup_iff (supports : List Vertex → Prop) (state : Cut Vertex) :
    (rotate supports state).word.Nodup ↔ state.word.Nodup :=
  (rotate_word_perm supports state).nodup_iff

theorem rotate_mem_iff (supports : List Vertex → Prop) (state : Cut Vertex)
    (vertex : Vertex) : vertex ∈ (rotate supports state).word ↔ vertex ∈ state.word :=
  (rotate_word_perm supports state).mem_iff

def GluingCompatible (firstSupport secondSupport jointSupport : List Vertex → Prop) : Prop :=
  ∀ first second, (first ++ second).Nodup →
    firstSupport first → secondSupport second → jointSupport (first ++ second)

theorem rotate_avoids_second (firstSupport secondSupport jointSupport : List Vertex → Prop)
    (compatible : GluingCompatible firstSupport secondSupport jointSupport)
    (state : Cut Vertex) (noDuplicates : state.prefix.Nodup)
    (supported : firstSupport state.prefix) (notJoint : ¬ jointSupport state.prefix) :
    ¬ secondSupport (rotate firstSupport state).prefix := by
  intro secondSupported
  have minimal := firstIndex_firstSupport firstSupport state.prefix supported
  have glued := compatible
    (state.prefix.take (firstIndex firstSupport state.prefix))
    (state.prefix.drop (firstIndex firstSupport state.prefix))
    (by simpa only [List.take_append_drop] using noDuplicates)
    minimal.1 secondSupported
  exact notJoint (by simpa only [List.take_append_drop] using glued)

def GluingSource (firstSupport jointSupport : List Vertex → Prop) :=
  {state : Cut Vertex // state.prefix.Nodup ∧ firstSupport state.prefix ∧ ¬ jointSupport state.prefix}

noncomputable def gluingMap
    (firstSupport secondSupport jointSupport : List Vertex → Prop)
    (compatible : GluingCompatible firstSupport secondSupport jointSupport)
    (source : GluingSource firstSupport jointSupport) :
    {state : Cut Vertex // ¬ secondSupport state.prefix} :=
  ⟨rotate firstSupport source.val,
    rotate_avoids_second firstSupport secondSupport jointSupport compatible source.val
      source.property.1 source.property.2.1 source.property.2.2⟩

theorem gluingMap_injective
    (firstSupport secondSupport jointSupport : List Vertex → Prop)
    (compatible : GluingCompatible firstSupport secondSupport jointSupport)
    (source target : GluingSource firstSupport jointSupport)
    (sameImage : gluingMap firstSupport secondSupport jointSupport compatible source =
      gluingMap firstSupport secondSupport jointSupport compatible target) : source = target := by
  apply Subtype.ext
  exact rotate_injective_on_support firstSupport source.val target.val
    source.property.2.1 target.property.2.1 (congrArg Subtype.val sameImage)

end Digraph
