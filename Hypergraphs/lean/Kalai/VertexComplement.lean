import Kalai.Hypergraph

namespace Kalai

universe u

theorem perm_of_nodup_membership {Vertex : Type u} (first second : List Vertex)
    (firstDistinct : first.Nodup) (secondDistinct : second.Nodup)
    (sameMembers : ∀ vertex, vertex ∈ first ↔ vertex ∈ second) : first.Perm second := by
  classical
  induction first generalizing second with
  | nil =>
    have empty : second = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun vertex present => List.not_mem_nil ((sameMembers vertex).mpr present))
    simp [empty]
  | cons head tail inductionHypothesis =>
    have headPresent : head ∈ second := (sameMembers head).mp (by simp)
    have smaller : tail.Perm (second.erase head) :=
      inductionHypothesis _ (List.nodup_cons.mp firstDistinct).2 (secondDistinct.erase head) (by
        intro vertex
        rw [secondDistinct.mem_erase_iff]
        constructor
        · intro present
          refine ⟨?_, (sameMembers vertex).mp (by simp [present])⟩
          intro same
          exact (List.nodup_cons.mp firstDistinct).1 (same ▸ present)
        · rintro ⟨different, present⟩
          have source := (sameMembers vertex).mpr present
          simpa only [List.mem_cons, different, false_or] using source)
    exact (smaller.cons head).trans (List.perm_cons_erase headPresent).symm

noncomputable def FiniteHypergraph.complement {Vertex : Type u} (host : FiniteHypergraph Vertex)
    (root : List Vertex) : List Vertex := by
  classical
  exact host.vertices.filter (fun vertex => decide (vertex ∉ root))

theorem FiniteHypergraph.mem_complement {Vertex : Type u} (host : FiniteHypergraph Vertex)
    (root : List Vertex) (vertex : Vertex) :
    vertex ∈ host.complement root ↔ vertex ∈ host.vertices ∧ vertex ∉ root := by
  classical
  simp [FiniteHypergraph.complement]

theorem FiniteHypergraph.complement_nodup {Vertex : Type u} (host : FiniteHypergraph Vertex)
    (root : List Vertex) : (host.complement root).Nodup := by
  classical
  exact host.vertices_nodup.filter _

theorem FiniteHypergraph.root_complement_perm {Vertex : Type u} (host : FiniteHypergraph Vertex)
    (root : List Vertex) (distinct : root.Nodup)
    (contained : ∀ vertex ∈ root, vertex ∈ host.vertices) :
    (root ++ host.complement root).Perm host.vertices := by
  classical
  refine perm_of_nodup_membership _ _ ?_ host.vertices_nodup ?_
  · apply List.pairwise_append.mpr
    refine ⟨distinct, host.complement_nodup root, ?_⟩
    intro first inRoot second inComplement same
    exact ((host.mem_complement root second).mp inComplement).2 (same ▸ inRoot)
  · intro vertex
    rw [List.mem_append, host.mem_complement]
    constructor
    · rintro (present | ⟨present, _⟩)
      · exact contained vertex present
      · exact present
    · intro present
      by_cases inRoot : vertex ∈ root
      · exact Or.inl inRoot
      · exact Or.inr ⟨present, inRoot⟩

theorem FiniteHypergraph.complement_length {Vertex : Type u} (host : FiniteHypergraph Vertex)
    (root : List Vertex) (distinct : root.Nodup)
    (contained : ∀ vertex ∈ root, vertex ∈ host.vertices) :
    (host.complement root).length = host.vertices.length - root.length := by
  have lengthEquality := (host.root_complement_perm root distinct contained).length_eq
  simp only [List.length_append] at lengthEquality
  omega

theorem FiniteHypergraph.complement_eq_of_perm {Vertex : Type u} (host : FiniteHypergraph Vertex)
    (first second : List Vertex) (ordering : first.Perm second) :
    host.complement first = host.complement second := by
  classical
  apply congrArg (fun predicate => host.vertices.filter predicate)
  funext vertex
  simp only [ordering.mem_iff]

theorem FiniteHypergraph.tail_perm_complement {Vertex : Type u} (host : FiniteHypergraph Vertex)
    (root tail : List Vertex) (distinct : root.Nodup)
    (contained : ∀ vertex ∈ root, vertex ∈ host.vertices)
    (full : (root ++ tail).Perm host.vertices) : tail.Perm (host.complement root) :=
  (List.perm_append_left_iff root).mp
    (full.trans (host.root_complement_perm root distinct contained).symm)

end Kalai
