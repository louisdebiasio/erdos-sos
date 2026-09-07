import Digraph.SimpleCycles

namespace Digraph
universe u v
variable {A : Type u} {B : Type v}

theorem unique_mem_of_short (xs : List A) (size : xs.length ≤ 1) (p : A) (hp : p ∈ xs)
    (a : A) (ha : a ∈ xs) : a = p := by
  cases xs with
  | nil => simp at hp
  | cons x rest =>
    cases rest with
    | nil => simp only [List.mem_singleton] at hp ha; exact ha.trans hp.symm
    | cons y rest => simp only [List.length_cons] at size; omega

/-- Every listed vertex can be used as root, with its actual source/sink sign.
The only graph hypotheses are connectedness, cycle exclusion and coloring. -/
theorem conventional_rooted (G : FiniteDigraph A) (c : A → Sign)
    (color : ∀ a b, G.Arc a b → c a = .plus ∧ c b = .minus)
    (conn : UnderlyingConnected G) (acyclic : UnderlyingAcyclic G)
    (size : 2 ≤ G.vertices.length) (r : A) (hr : r ∈ G.vertices) :
    ∃ k, RootedTree G r (c r) k := by
  have build : ∀ n, ∀ H : FiniteDigraph A, H.vertices.length = n →
      (∀ a b, H.Arc a b → c a = .plus ∧ c b = .minus) →
      UnderlyingConnected H → UnderlyingAcyclic H → 2 ≤ n →
      ∀ r, r ∈ H.vertices → ∃ k, RootedTree H r (c r) k := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro H hn colored connected acyc large r root
      obtain ⟨p,edge⟩ := connected_neighbor H connected (hn ▸ large) r root
      let L := induced H (Reach (WithoutEdge H r p) r)
      let R := induced H (Reach (WithoutEdge H r p) p)
      let U := induced H (fun x => x = r ∨ Reach (WithoutEdge H r p) p x)
      have am : RootAmalgam L U H r := cut_amalgam H r p edge connected acyc
      have ext : LeafExtension R U p r (c r) := cut_leaf_extension H r p c colored edge acyc
      have colorL : ∀ a b, L.Arc a b → c a = .plus ∧ c b = .minus :=
        fun a b h => colored a b ((induced_arc _ _ _ _).mp h).1
      have colorR : ∀ a b, R.Arc a b → c a = .plus ∧ c b = .minus :=
        fun a b h => colored a b ((induced_arc _ _ _ _).mp h).1
      have colorU : ∀ a b, U.Arc a b → c a = .plus ∧ c b = .minus :=
        fun a b h => colored a b ((induced_arc _ _ _ _).mp h).1
      have shorterL : L.vertices.length < n := by
        rw [← hn]
        exact induced_shorter H _ p (uadj_mem H edge).2 (acyc r p edge)
      have shorterR : R.vertices.length < n := by
        rw [← hn]
        exact induced_shorter H _ r root
          (fun h => cut_disjoint H r p edge acyc r (.refl _) h)
      have rootedU : ∃ k, RootedTree U r (c r) k := by
        by_cases bigR : 2 ≤ R.vertices.length
        · obtain ⟨j,old⟩ := ih R.vertices.length shorterR R rfl colorR
            (component_connected H r p p) (induced_acyclic H _ acyc) bigR p ext.old_root
          have flip := (colored_edge H c colored edge).2
          rw [flip] at old
          exact ⟨j+1, .leaf R U p r (c r) j old ext⟩
        · have singleton : ∀ a, a ∈ R.vertices → a = p :=
            unique_mem_of_short R.vertices (by omega) p ext.old_root
          have vertices : ∀ a, a ∈ U.vertices ↔ a = r ∨ a = p := by
            intro a; rw [ext.vertices]
            constructor
            · rintro (h | eq)
              · exact Or.inr (singleton a h)
              · exact Or.inl eq
            · rintro (rfl | rfl)
              · exact Or.inr rfl
              · exact Or.inl ext.old_root
          have edgeU : U.UAdj r p := (induced_uadj _ _ _ _).mpr
            ⟨edge,Or.inl rfl,Or.inr (.refl _)⟩
          exact ⟨0,.edge U r p (c r) (single_of_two U r p c colorU edgeU vertices)⟩
      obtain ⟨j,other⟩ := rootedU
      by_cases bigL : 2 ≤ L.vertices.length
      · obtain ⟨i,first⟩ := ih L.vertices.length shorterL L rfl colorL
          (component_connected H r p r) (induced_acyclic H _ acyc) bigL r am.first_root
        exact ⟨i+j+1,.branch L U H r (c r) i j first other am⟩
      · have singleton : ∀ a, a ∈ L.vertices → a = r :=
          unique_mem_of_short L.vertices (by omega) r am.first_root
        have vertices : ∀ a, a ∈ H.vertices ↔ a ∈ U.vertices := by
          intro a; rw [am.vertices_union]
          constructor
          · rintro (h | h)
            · exact (singleton a h).symm ▸ am.second_root
            · exact h
          · exact Or.inr
        have arcs : ∀ a b, H.Arc a b ↔ U.Arc a b := by
          intro a b; rw [am.arcs_union]
          constructor
          · rintro (h | h)
            · have ar := singleton a (L.endpoints a b h).1
              have br := singleton b (L.endpoints a b h).2
              exact False.elim (L.loopless r (by simpa [ar,br] using h))
            · exact h
          · exact Or.inr
        exact ⟨j,other.transport H vertices arcs⟩
  exact build G.vertices.length G rfl color conn acyclic size r hr

/-- The representation bridge: conventional tree data produces the old certificate. -/
theorem ConventionalTree.to_recursive {G : FiniteDigraph A} (tree : ConventionalTree G) :
    IsAntidirectedTree G := by
  obtain ⟨c,color⟩ := tree.antidirected
  obtain ⟨r,hr⟩ := List.exists_mem_of_length_pos (l := G.vertices) (by have h := tree.nontrivial; omega)
  obtain ⟨k,built⟩ := conventional_rooted G c color tree.connected tree.acyclic tree.nontrivial r hr
  exact ⟨r,c r,k,built⟩

/-- Density theorem with conventional graph hypotheses and global injectivity. -/
theorem addarioBerry_bound_of_connected_acyclic (T : FiniteDigraph A) (D : FiniteDigraph B)
    (tree : ConventionalTree T) (free : ¬ Nonempty (Embedding T D)) :
    D.arcs.length ≤ (T.vertices.length - 2) * D.vertices.length := by
  obtain ⟨r,s,k,built⟩ := tree.to_recursive
  exact antidirected_density built D free

theorem addarioBerry_contains_of_connected_acyclic (T : FiniteDigraph A) (D : FiniteDigraph B)
    (tree : ConventionalTree T)
    (dense : (T.vertices.length - 2) * D.vertices.length < D.arcs.length) :
    Nonempty (Embedding T D) := by
  obtain ⟨r,s,k,built⟩ := tree.to_recursive
  exact antidirected_contains_tree built D dense

/-- The graph predicate is equivalent to ordinary connectedness and absence
of vertex-simple cycles, with the source/sink coloring and size explicit. -/
theorem conventionalTree_iff (T : FiniteDigraph A) :
    ConventionalTree T ↔ 2 ≤ T.vertices.length ∧ Antidirected T ∧
      UnderlyingConnected T ∧ NoSimpleCycle T := by
  constructor
  · intro h
    exact ⟨h.nontrivial,h.antidirected,h.connected,(acyclic_iff_no_simple_cycle T).mp h.acyclic⟩
  · rintro ⟨size,anti,conn,no⟩
    exact ⟨size,anti,conn,(acyclic_iff_no_simple_cycle T).mpr no⟩

/-- The final public interface requires no recursive construction or
edge-cut certificate from the caller. -/
theorem addarioBerry_bound_of_no_simple_cycle (T : FiniteDigraph A) (D : FiniteDigraph B)
    (size : 2 ≤ T.vertices.length) (anti : Antidirected T)
    (connected : UnderlyingConnected T) (acyclic : NoSimpleCycle T)
    (free : ¬ Nonempty (Embedding T D)) :
    D.arcs.length ≤ (T.vertices.length - 2) * D.vertices.length :=
  addarioBerry_bound_of_connected_acyclic T D
    ((conventionalTree_iff T).mpr ⟨size,anti,connected,acyclic⟩) free

theorem addarioBerry_contains_of_no_simple_cycle (T : FiniteDigraph A) (D : FiniteDigraph B)
    (size : 2 ≤ T.vertices.length) (anti : Antidirected T)
    (connected : UnderlyingConnected T) (acyclic : NoSimpleCycle T)
    (dense : (T.vertices.length - 2) * D.vertices.length < D.arcs.length) :
    Nonempty (Embedding T D) :=
  addarioBerry_contains_of_connected_acyclic T D
    ((conventionalTree_iff T).mpr ⟨size,anti,connected,acyclic⟩) dense

end Digraph
