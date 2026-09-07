import Digraph.SignedStates

namespace Digraph

universe u v
variable {A : Type u} {B : Type v}

def TailGood (S : FiniteDigraph A) (D : FiniteDigraph B) (p : A) (s : Sign)
    (x : B) (cut : MarkedCut B) : Prop :=
  D.Adj s x cut.marker ∧ Supports S D p x cut.prefixList

/-- Swapping the two endpoints of a later mark replaces prefix reversal.
It has the same prefix vertex set and is an involution retaining the cut index. -/
theorem leaf_swap_good (S T : FiniteDigraph A) (D : FiniteDigraph B)
    (p l : A) (s : Sign) (ext : LeafExtension S T p l s)
    (q : State B) (valid : Valid D s.flip q)
    (earlier : EarlierSupported (TailGood S D p s.flip q.root) q.cut) :
    Good T D l s q.swap := by
  obtain ⟨old, sameWord, earlierIndex, oldMark, f, root, inside⟩ := earlier
  have distinct : ([q.root] ++ q.cut.word).Nodup :=
    valid.1.nodup_iff.mpr D.vertices_nodup
  have avoided := MarkedCut.marker_not_earlier [q.root] old q.cut sameWord earlierIndex distinct
  have fresh : ∀ a, a ∈ S.vertices → f.toFun a ≠ q.cut.marker := by
    intro a ha eq
    apply avoided
    rw [← eq]
    exact inside a ha
  have marking : D.Adj s q.cut.marker (f.toFun p) := by
    rw [root]
    exact (adj_flip D s _ _).mp valid.2
  obtain ⟨g, atNew, onOld⟩ := extend_leaf_embedding S T D p l s ext f q.cut.marker fresh marking
  refine ⟨?_, g, atNew, ?_⟩
  · simpa using valid_swap D s.flip q valid
  · intro a ha
    rcases (ext.vertices a).mp ha with oldVertex | newVertex
    · rw [onOld a oldVertex]
      rcases List.mem_cons.mp (inside a oldVertex) with atRoot | inOld
      · simp [State.swap, MarkedCut.prefixList, atRoot]
      · have inBefore := MarkedCut.earlier_prefix_subset old q.cut sameWord earlierIndex _ inOld
        simp [State.swap, MarkedCut.prefixList, inBefore]
    · simp [newVertex, atNew, State.swap]

noncomputable def leafMap (S T : FiniteDigraph A) (D : FiniteDigraph B)
    (p l : A) (s : Sign) (ext : LeafExtension S T p l s)
    (q : {q // Good S D p s.flip q}) :
    Sum {q // Good T D l s q} {word : List B // word.Perm D.vertices} := by
  classical
  exact if earlier : EarlierSupported (TailGood S D p s.flip q.val.root) q.val.cut then
    Sum.inl ⟨q.val.swap, leaf_swap_good S T D p l s ext q.val q.property.1 earlier⟩
  else Sum.inr ⟨q.val.word, q.property.1.1⟩

theorem leafMap_injective (S T : FiniteDigraph A) (D : FiniteDigraph B)
    (p l : A) (s : Sign) (ext : LeafExtension S T p l s)
    (q t : {q // Good S D p s.flip q})
    (same : leafMap S T D p l s ext q = leafMap S T D p l s ext t) : q = t := by
  classical
  by_cases qe : EarlierSupported (TailGood S D p s.flip q.val.root) q.val.cut <;>
    by_cases te : EarlierSupported (TailGood S D p s.flip t.val.root) t.val.cut
  · simp only [leafMap, dif_pos qe, dif_pos te] at same
    exact Subtype.ext (State.swap_injective _ _ (congrArg Subtype.val (Sum.inl.inj same)))
  · simp [leafMap, qe, te] at same
  · simp [leafMap, qe, te] at same
  · simp only [leafMap, dif_neg qe, dif_neg te] at same
    have words := congrArg Subtype.val (Sum.inr.inj same)
    have roots := (List.cons.inj words).1
    have tails := (List.cons.inj words).2
    have cutEq := first_exception_word_injective
      (TailGood S D p s.flip q.val.root) q.val.cut t.val.cut
      ⟨q.property.1.2, q.property.2⟩
      (by simpa only [roots, TailGood] using And.intro t.property.1.2 t.property.2)
      qe (by simpa [roots] using te) tails
    exact Subtype.ext (State.ext _ _ roots cutEq)

/-- The signed leaf inequality with the actual finite populations, not assumed counts. -/
theorem signed_leaf_count (S T : FiniteDigraph A) (D : FiniteDigraph B)
    (p l : A) (s : Sign) (ext : LeafExtension S T p l s) :
    R S D p s.flip ≤ R T D l s + Q D :=
  ListingFor.card_le_add_of_injection (goodListing S D p s.flip)
    (goodListing T D l s) (orderingUniverse D.vertices)
    (leafMap S T D p l s ext) (leafMap_injective S T D p l s ext)

end Digraph
