import Digraph.Basic

namespace Digraph

universe u v
variable {A : Type u} {B : Type v}

structure State (B : Type v) where
  root : B
  cut : MarkedCut B
  deriving DecidableEq, Repr

def State.word (q : State B) : List B := q.root :: q.cut.word

theorem State.ext (q t : State B) (root : q.root = t.root) (cut : q.cut = t.cut) : q = t := by
  cases q; cases t; simp_all

def State.swap (q : State B) : State B :=
  ⟨q.cut.marker, ⟨q.cut.before, q.root, q.cut.after⟩⟩

@[simp] theorem State.swap_swap (q : State B) : q.swap.swap = q := by cases q; rfl

theorem State.swap_injective (q t : State B) (h : q.swap = t.swap) : q = t := by
  have h' := congrArg State.swap h
  simpa using h'

theorem State.swap_word_perm (q : State B) : q.swap.word.Perm q.word := by
  exact List.cons_append_cons_perm

def Valid (D : FiniteDigraph B) (s : Sign) (q : State B) : Prop :=
  q.word.Perm D.vertices ∧ D.Adj s q.root q.cut.marker

theorem valid_swap (D : FiniteDigraph B) (s : Sign) (q : State B) (h : Valid D s q) :
    Valid D s.flip q.swap :=
  ⟨q.swap_word_perm.trans h.1, (adj_flip D s _ _).mpr h.2⟩

def Good (T : FiniteDigraph A) (D : FiniteDigraph B) (r : A) (s : Sign)
    (q : State B) : Prop := Valid D s q ∧ Supports T D r q.root q.cut.prefixList

def statesOfWord : List B → List (State B)
  | [] => []
  | x :: rest => (marksOfWord rest).map (fun cut => ⟨x, cut⟩)

def stateCandidates (vertices : List B) : List (State B) :=
  (wordsOfLength vertices vertices.length).flatMap statesOfWord

theorem stateCandidates_complete (vertices : List B) (q : State B)
    (h : q.word.Perm vertices) : q ∈ stateCandidates vertices := by
  apply List.mem_flatMap.mpr
  refine ⟨q.word, permutation_in_words vertices q.word h, ?_⟩
  exact List.mem_map.mpr ⟨q.cut, marksOfWord_complete q.cut, rfl⟩

noncomputable def validListing (D : FiniteDigraph B) (s : Sign) : ListingFor (Valid D s) :=
  ListingFor.ofCover (stateCandidates D.vertices) (Valid D s)
    (fun q h => stateCandidates_complete D.vertices q h.1)

noncomputable def goodListing (T : FiniteDigraph A) (D : FiniteDigraph B)
    (r : A) (s : Sign) : ListingFor (Good T D r s) :=
  (validListing D s).restrict (fun q => Supports T D r q.root q.cut.prefixList)

noncomputable def M (D : FiniteDigraph B) (s : Sign) : Nat := (validListing D s).card
noncomputable def R (T : FiniteDigraph A) (D : FiniteDigraph B) (r : A) (s : Sign) : Nat :=
  (goodListing T D r s).card
noncomputable def Q (D : FiniteDigraph B) : Nat := (orderingUniverse D.vertices).card

/-- The positive and negative marked-state populations agree, even with opposite arcs. -/
theorem signed_population_eq (D : FiniteDigraph B) (s : Sign) : M D s = M D s.flip := by
  apply ListingFor.card_eq_of_bijection (validListing D s) (validListing D s.flip)
    (fun q => ⟨q.val.swap, valid_swap D s q.val q.property⟩)
  · intro q t h
    exact Subtype.ext (State.swap_injective _ _ (congrArg Subtype.val h))
  · intro t
    refine ⟨⟨t.val.swap, ?_⟩, ?_⟩
    · simpa using valid_swap D s.flip t.val t.property
    · exact Subtype.ext t.val.swap_swap

theorem free_support_empty (T : FiniteDigraph A) (D : FiniteDigraph B)
    (r : A) (s : Sign) (free : ¬ Nonempty (Embedding T D)) : R T D r s = 0 := by
  have noGood : ∀ q, ¬ Good T D r s q := by
    intro q h
    obtain ⟨f, _, _⟩ := h.2
    exact free ⟨f⟩
  have empty : (goodListing T D r s).values = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro q h
    exact noGood q (((goodListing T D r s).membership q).mp h)
  unfold R ListingFor.card
  rw [empty]
  rfl

end Digraph
