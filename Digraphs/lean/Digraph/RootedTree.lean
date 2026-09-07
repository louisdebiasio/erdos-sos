import Digraph.Normalization

namespace Digraph

universe u v
variable {A : Type u} {B : Type v}

structure SingleArc (T : FiniteDigraph A) (r p : A) (s : Sign) : Prop where
  different : r ≠ p
  vertices : ∀ a, a ∈ T.vertices ↔ a = r ∨ a = p
  arcs : ∀ a b, T.Arc a b ↔
    (s = .plus ∧ a = r ∧ b = p) ∨ (s = .minus ∧ a = p ∧ b = r)

theorem singleArc_good (T : FiniteDigraph A) (D : FiniteDigraph B)
    (r p : A) (s : Sign) (one : SingleArc T r p s)
    (q : State B) (valid : Valid D s q) : Good T D r s q := by
  classical
  let f := fun a => if a = r then q.root else q.cut.marker
  have atRoot : f r = q.root := by simp [f]
  have atOther : f p = q.cut.marker := by simp [f, Ne.symm one.different]
  have different : q.root ≠ q.cut.marker := by
    intro eq
    have h : D.Adj s q.root q.root := by simpa only [← eq] using valid.2
    cases s <;> exact D.loopless q.root h
  refine ⟨valid, { toFun := f, maps_vertices := ?_, injective := ?_, maps_arcs := ?_ }, atRoot, ?_⟩
  · intro a ha
    rcases (one.vertices a).mp ha with eq | eq
    · rw [eq, atRoot]; exact (adj_endpoints D s valid.2).1
    · rw [eq, atOther]; exact (adj_endpoints D s valid.2).2
  · intro a ha b hb eq
    rcases (one.vertices a).mp ha with ar | ap <;>
      rcases (one.vertices b).mp hb with br | bp
    · exact ar.trans br.symm
    · exact False.elim (different (by simpa only [ar, bp, atRoot, atOther] using eq))
    · exact False.elim (different (by simpa only [ap, br, atRoot, atOther] using eq.symm))
    · exact ap.trans bp.symm
  · intro a b hab
    rcases (one.arcs a b).mp hab with ⟨sign, ar, bp⟩ | ⟨sign, ap, br⟩
    · rw [ar, bp, atRoot, atOther]; simpa only [sign, FiniteDigraph.Adj] using valid.2
    · rw [ap, br, atOther, atRoot]; simpa only [sign, FiniteDigraph.Adj] using valid.2
  · intro a ha
    change f a ∈ q.root :: q.cut.prefixList
    rcases (one.vertices a).mp ha with eq | eq
    · simp [eq, atRoot]
    · simp [eq, atOther, MarkedCut.prefixList]

theorem singleArc_count (T : FiniteDigraph A) (D : FiniteDigraph B)
    (r p : A) (s : Sign) (one : SingleArc T r p s) : R T D r s = M D s :=
  ListingFor.card_eq_of_iff (goodListing T D r s) (validListing D s)
    (fun q => ⟨fun h => h.1, singleArc_good T D r p s one q⟩)

/-- A rooted, nontrivial antidirected tree, constructed from an edge by
adding a new leaf root or identifying roots of disjoint rooted branches.
The index is the number of vertices minus two, not an assumed density bound. -/
inductive RootedTree : FiniteDigraph A → A → Sign → Nat → Prop where
  | edge (T : FiniteDigraph A) (r p : A) (s : Sign) (one : SingleArc T r p s) :
      RootedTree T r s 0
  | leaf (S T : FiniteDigraph A) (p l : A) (s : Sign) (k : Nat)
      (built : RootedTree S p s.flip k) (ext : LeafExtension S T p l s) :
      RootedTree T l s (k + 1)
  | branch (S U T : FiniteDigraph A) (r : A) (s : Sign) (i j : Nat)
      (first : RootedTree S r s i) (second : RootedTree U r s j)
      (am : RootAmalgam S U T r) : RootedTree T r s (i + j + 1)

theorem length_eq_of_membership (a b : List A) (ha : a.Nodup) (hb : b.Nodup)
    (same : ∀ x, x ∈ a ↔ x ∈ b) : a.length = b.length :=
  Nat.le_antisymm (nodup_length_le_of_subset a b ha (fun x h => (same x).mp h))
    (nodup_length_le_of_subset b a hb (fun x h => (same x).mpr h))

theorem leaf_vertex_count (S T : FiniteDigraph A) (p l : A) (s : Sign)
    (ext : LeafExtension S T p l s) : T.vertices.length = S.vertices.length + 1 := by
  have h := length_eq_of_membership T.vertices (l :: S.vertices) T.vertices_nodup
    (List.nodup_cons.mpr ⟨ext.fresh, S.vertices_nodup⟩) (by
      intro a; simp only [ext.vertices a, List.mem_cons, or_comm])
  simpa using h

theorem branch_vertex_count (S U T : FiniteDigraph A) (r : A) (am : RootAmalgam S U T r) :
    T.vertices.length + 1 = S.vertices.length + U.vertices.length := by
  classical
  have nd : (S.vertices ++ U.vertices.erase r).Nodup := by
    apply List.pairwise_append.mpr
    refine ⟨S.vertices_nodup, U.vertices_nodup.erase r, ?_⟩
    intro a ha b hb eq
    have ub := U.vertices_nodup.mem_erase_iff.mp hb
    have root := (am.vertices_intersection b).mp ⟨eq ▸ ha, ub.2⟩
    exact ub.1 root
  have count := length_eq_of_membership T.vertices (S.vertices ++ U.vertices.erase r)
    T.vertices_nodup nd (by
      intro a
      rw [am.vertices_union, List.mem_append, U.vertices_nodup.mem_erase_iff]
      constructor
      · rintro (hs | hu)
        · exact Or.inl hs
        · by_cases h : a = r
          · exact Or.inl (h ▸ am.first_root)
          · exact Or.inr ⟨h, hu⟩
      · rintro (hs | ⟨_, hu⟩)
        · exact Or.inl hs
        · exact Or.inr hu)
  have erased := List.length_erase_of_mem am.second_root
  have positive := List.length_pos_of_mem am.second_root
  simp only [List.length_append] at count
  omega

theorem RootedTree.vertex_count {T : FiniteDigraph A} {r : A} {s : Sign} {k : Nat}
    (tree : RootedTree T r s k) : T.vertices.length = k + 2 := by
  induction tree with
  | edge T r p s one =>
    have h := length_eq_of_membership T.vertices [r, p] T.vertices_nodup
      (by simp [one.different]) (by intro a; simp [one.vertices])
    simpa using h
  | leaf S T p l s k built ext ih => rw [leaf_vertex_count S T p l s ext, ih]
  | branch S U T r s i j first second am ihs ihu =>
    have count := branch_vertex_count S U T r am
    omega

theorem rooted_master {T : FiniteDigraph A} {r : A} {s : Sign} {k : Nat}
    (tree : RootedTree T r s k) (D : FiniteDigraph B) : M D s ≤ R T D r s + k * Q D := by
  induction tree with
  | edge T r p s one => rw [singleArc_count T D r p s one]; simp
  | leaf S T p l s k built ext ih =>
    have transfer := signed_leaf_count S T D p l s ext
    have same := signed_population_eq D s
    rw [Nat.add_mul, Nat.one_mul]
    omega
  | branch S U T r s i j first second am ihs ihu =>
    have transfer := signed_branch_count S U T D r s am
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- Density bound for the explicit rooted-tree construction above. -/
theorem antidirected_density {T : FiniteDigraph A} {r : A} {s : Sign} {k : Nat}
    (tree : RootedTree T r s k) (D : FiniteDigraph B)
    (free : ¬ Nonempty (Embedding T D)) :
    D.arcs.length ≤ (T.vertices.length - 2) * D.vertices.length := by
  have bound := rooted_master tree D
  rw [free_support_empty T D r s free, Nat.zero_add] at bound
  have result := population_density_cancel D s k bound
  simpa only [tree.vertex_count, Nat.add_sub_cancel] using result

theorem antidirected_contains_tree {T : FiniteDigraph A} {r : A} {s : Sign} {k : Nat}
    (tree : RootedTree T r s k) (D : FiniteDigraph B)
    (dense : (T.vertices.length - 2) * D.vertices.length < D.arcs.length) :
    Nonempty (Embedding T D) := by
  classical
  by_cases existsCopy : Nonempty (Embedding T D)
  · exact existsCopy
  · have bound := antidirected_density tree D existsCopy
    omega

end Digraph
