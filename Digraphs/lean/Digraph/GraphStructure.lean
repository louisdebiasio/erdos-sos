import Digraph.TreeSemantics

namespace Digraph
universe u
variable {A : Type u}

/-- The ordinary undirected adjacency relation, forgetting arc directions. -/
def FiniteDigraph.UAdj (G : FiniteDigraph A) (a b : A) : Prop :=
  G.Arc a b ∨ G.Arc b a
instance [DecidableEq A] (G : FiniteDigraph A) (a b : A) : Decidable (G.UAdj a b) :=
  inferInstanceAs (Decidable ((a,b) ∈ G.arcs ∨ (b,a) ∈ G.arcs))



theorem uadj_symm (G : FiniteDigraph A) {a b : A} (h : G.UAdj a b) : G.UAdj b a := h.elim Or.inr Or.inl

theorem uadj_mem (G : FiniteDigraph A) {a b : A} (h : G.UAdj a b) :
    a ∈ G.vertices ∧ b ∈ G.vertices := by
  rcases h with h | h
  · exact G.endpoints a b h
  · exact (G.endpoints b a h).symm

theorem uadj_ne (G : FiniteDigraph A) {a b : A} (h : G.UAdj a b) : a ≠ b := by
  intro eq; subst b; rcases h with h | h <;> exact G.loopless a h

/-- Existence of a finite walk, with zero-edge walks allowed. -/
inductive Reach (E : A → A → Prop) : A → A → Prop where
  | refl (a) : Reach E a a
  | tail {a b c} : Reach E a b → E b c → Reach E a c

theorem Reach.trans {E : A → A → Prop} {a b c : A}
    (h : Reach E a b) (g : Reach E b c) : Reach E a c := by
  induction g with
  | refl => exact h
  | tail _ edge ih => exact .tail ih edge

theorem Reach.mono {E F : A → A → Prop} {a b : A}
    (h : Reach E a b) (sub : ∀ x y, E x y → F x y) : Reach F a b := by
  induction h with
  | refl => exact .refl _
  | tail _ edge ih => exact .tail ih (sub _ _ edge)

theorem Reach.symm {E : A → A → Prop} (sym : ∀ x y, E x y → E y x)
    {a b : A} (h : Reach E a b) : Reach E b a := by
  induction h with
  | refl => exact .refl _
  | tail _ edge ih => exact (Reach.tail (.refl _) (sym _ _ edge)).trans ih

/-- Delete one undirected edge, in both directions, from adjacency. -/
def WithoutEdge (G : FiniteDigraph A) (r p a b : A) : Prop :=
  G.UAdj a b ∧ ¬ ((a = r ∧ b = p) ∨ (a = p ∧ b = r))

theorem withoutEdge_symm (G : FiniteDigraph A) (r p a b : A)
    (h : WithoutEdge G r p a b) : WithoutEdge G r p b a := by
  refine ⟨uadj_symm G h.1, ?_⟩
  rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩)
  · exact h.2 (Or.inr ⟨h₂,h₁⟩)
  · exact h.2 (Or.inl ⟨h₂,h₁⟩)

/-- Ordinary connectedness on the listed vertex set. -/
def UnderlyingConnected (G : FiniteDigraph A) : Prop :=
  ∀ a, a ∈ G.vertices → ∀ b, b ∈ G.vertices → Reach G.UAdj a b

/-- Cycle exclusion in edge-bypass form: no edge has an alternate walk
between its endpoints after that edge is removed. This is independent of
any tree construction, vertex-count identity, or density inequality. -/
def UnderlyingAcyclic (G : FiniteDigraph A) : Prop :=
  ∀ a b, G.UAdj a b → ¬ Reach (WithoutEdge G a b) a b

/-- A nontrivial conventional antidirected tree, not a recursive certificate. -/
structure ConventionalTree (G : FiniteDigraph A) : Prop where
  nontrivial : 2 ≤ G.vertices.length
  antidirected : Antidirected G
  connected : UnderlyingConnected G
  acyclic : UnderlyingAcyclic G

noncomputable def induced (G : FiniteDigraph A) (P : A → Prop) : FiniteDigraph A := by
  classical
  exact {
    vertices := G.vertices.filter (fun a => decide (P a))
    arcs := G.arcs.filter (fun ab => decide (P ab.1 ∧ P ab.2))
    vertices_nodup := G.vertices_nodup.filter _
    arcs_nodup := G.arcs_nodup.filter _
    endpoints := by
      intro a b h
      have z : (a,b) ∈ G.arcs ∧ P a ∧ P b := by simpa using h
      have m := G.endpoints a b z.1
      simpa using And.intro (And.intro m.1 z.2.1) (And.intro m.2 z.2.2)
    loopless := by intro a h; exact G.loopless a (List.mem_filter.mp h).1 }

@[simp] theorem induced_mem (G : FiniteDigraph A) (P : A → Prop) (a : A) :
    a ∈ (induced G P).vertices ↔ a ∈ G.vertices ∧ P a := by
  classical
  simp [induced]

@[simp] theorem induced_arc (G : FiniteDigraph A) (P : A → Prop) (a b : A) :
    (induced G P).Arc a b ↔ G.Arc a b ∧ P a ∧ P b := by
  classical
  simp [induced, FiniteDigraph.Arc]

@[simp] theorem induced_uadj (G : FiniteDigraph A) (P : A → Prop) (a b : A) :
    (induced G P).UAdj a b ↔ G.UAdj a b ∧ P a ∧ P b := by
  simp only [FiniteDigraph.UAdj, induced_arc]
  constructor
  · rintro (⟨h,ha,hb⟩ | ⟨h,hb,ha⟩)
    · exact ⟨Or.inl h,ha,hb⟩
    · exact ⟨Or.inr h,ha,hb⟩
  · rintro ⟨h,ha,hb⟩; exact h.elim (fun h => Or.inl ⟨h,ha,hb⟩) (fun h => Or.inr ⟨h,hb,ha⟩)

theorem induced_acyclic (G : FiniteDigraph A) (P : A → Prop)
    (acyclic : UnderlyingAcyclic G) : UnderlyingAcyclic (induced G P) := by
  intro a b hab path
  apply acyclic a b ((induced_uadj G P a b).mp hab).1
  exact path.mono (fun x y h => ⟨((induced_uadj G P x y).mp h.1).1, h.2⟩)

theorem induced_shorter (G : FiniteDigraph A) (P : A → Prop) (v : A)
    (mem : v ∈ G.vertices) (excluded : ¬ P v) : (induced G P).vertices.length < G.vertices.length := by
  classical
  have sub : List.Sublist (induced G P).vertices G.vertices := List.filter_sublist
  have le := sub.length_le
  by_cases lt : (induced G P).vertices.length < G.vertices.length
  · exact lt
  · have eq := sub.eq_of_length (by omega)
    have m : v ∈ (induced G P).vertices := eq.symm ▸ mem
    exact False.elim (excluded ((induced_mem G P v).mp m).2)

/-- The two endpoints of an edge separate its two walk-components. -/
theorem cut_disjoint (G : FiniteDigraph A) (r p : A) (edge : G.UAdj r p)
    (acyclic : UnderlyingAcyclic G) (x : A)
    (left : Reach (WithoutEdge G r p) r x) (right : Reach (WithoutEdge G r p) p x) : False :=
  acyclic r p edge (left.trans (right.symm (withoutEdge_symm G r p)))

theorem cut_cover (G : FiniteDigraph A) (r p : A) {x : A}
    (path : Reach G.UAdj r x) :
    Reach (WithoutEdge G r p) r x ∨ Reach (WithoutEdge G r p) p x := by
  classical
  induction path with
  | refl => exact Or.inl (.refl _)
  | @tail b c h adj ih =>
    by_cases removed : (b = r ∧ c = p) ∨ (b = p ∧ c = r)
    · rcases removed with ⟨_,eq⟩ | ⟨_,eq⟩
      · subst c; exact Or.inr (.refl _)
      · subst c; exact Or.inl (.refl _)
    · exact ih.elim (fun z => Or.inl (.tail z ⟨adj,removed⟩)) (fun z => Or.inr (.tail z ⟨adj,removed⟩))

theorem component_path (G : FiniteDigraph A) (r p v : A) {x : A}
    (path : Reach (WithoutEdge G r p) v x) :
    Reach (induced G (Reach (WithoutEdge G r p) v)).UAdj v x := by
  induction path with
  | refl => exact .refl _
  | @tail b c h adj ih =>
    exact .tail ih ((induced_uadj _ _ _ _).mpr ⟨adj.1,h,.tail h adj⟩)

theorem component_connected (G : FiniteDigraph A) (r p v : A) :
    UnderlyingConnected (induced G (Reach (WithoutEdge G r p) v)) := by
  intro a ha b hb
  have pa := component_path G r p v ((induced_mem _ _ _).mp ha).2
  have pb := component_path G r p v ((induced_mem _ _ _).mp hb).2
  exact (pa.symm (fun _ _ h => uadj_symm _ h)).trans pb

theorem connected_neighbor (G : FiniteDigraph A) (conn : UnderlyingConnected G)
    (size : 2 ≤ G.vertices.length) (r : A) (hr : r ∈ G.vertices) : ∃ p, G.UAdj r p := by
  classical
  by_cases existsEdge : ∃ p, G.UAdj r p
  · exact existsEdge
  · have all : ∀ x, x ∈ G.vertices → x = r := by
      intro x hx
      have path := conn r hr x hx
      induction path with
      | refl => rfl
      | @tail b c h edge ih =>
        exact False.elim (existsEdge ⟨c, (ih (uadj_mem G edge).1) ▸ edge⟩)
    have bound := nodup_length_le_of_subset G.vertices [r] G.vertices_nodup
      (fun x hx => by simp [all x hx])
    simp only [List.length_singleton] at bound
    omega

theorem colored_edge (G : FiniteDigraph A) (c : A → Sign)
    (color : ∀ a b, G.Arc a b → c a = .plus ∧ c b = .minus)
    {a b : A} (h : G.UAdj a b) : G.Adj (c a) a b ∧ c b = (c a).flip := by
  rcases h with h | h
  · obtain ⟨ha,hb⟩ := color a b h
    simp only [ha, hb, FiniteDigraph.Adj, Sign.flip]
    exact ⟨h,True.intro⟩
  · obtain ⟨hb,ha⟩ := color b a h
    simp only [ha, hb, FiniteDigraph.Adj, Sign.flip]
    exact ⟨h,True.intro⟩

theorem single_of_two (G : FiniteDigraph A) (r p : A) (c : A → Sign)
    (color : ∀ a b, G.Arc a b → c a = .plus ∧ c b = .minus)
    (edge : G.UAdj r p) (vertices : ∀ a, a ∈ G.vertices ↔ a = r ∨ a = p) :
    SingleArc G r p (c r) := by
  have directed := (colored_edge G c color edge).1
  refine ⟨uadj_ne G edge, vertices, ?_⟩
  intro a b
  constructor
  · intro h
    rcases (vertices a).mp (G.endpoints a b h).1 with ar | ap <;>
      rcases (vertices b).mp (G.endpoints a b h).2 with br | bp
    · exact False.elim (G.loopless r (by simpa [ar,br] using h))
    · exact Or.inl ⟨by simpa [ar] using (color a b h).1,ar,bp⟩
    · exact Or.inr ⟨by simpa [br] using (color a b h).2,ap,br⟩
    · exact False.elim (G.loopless p (by simpa [ap,bp] using h))
  · rintro (⟨sign,rfl,rfl⟩ | ⟨sign,rfl,rfl⟩)
    · simpa [sign, FiniteDigraph.Adj] using directed
    · simpa [sign, FiniteDigraph.Adj] using directed

theorem RootedTree.transport {G : FiniteDigraph A} {r : A} {s : Sign} {k : Nat}
    (built : RootedTree G r s k) (H : FiniteDigraph A)
    (vertices : ∀ a, a ∈ H.vertices ↔ a ∈ G.vertices)
    (arcs : ∀ a b, H.Arc a b ↔ G.Arc a b) : RootedTree H r s k := by
  cases built with
  | edge G r p s one =>
    exact .edge H r p s ⟨one.different, fun a => (vertices a).trans (one.vertices a),
      fun a b => (arcs a b).trans (one.arcs a b)⟩
  | leaf S G p l s k old ext =>
    exact .leaf S H p _ s k old ⟨ext.old_root, ext.fresh,
      fun a => (vertices a).trans (ext.vertices a), fun a b => (arcs a b).trans (ext.arcs a b)⟩
  | branch S U G r s i j first second am =>
    exact .branch S U H r s i j first second ⟨am.first_root, am.second_root,
      fun a => (vertices a).trans (am.vertices_union a), am.vertices_intersection,
      fun a b => (arcs a b).trans (am.arcs_union a b)⟩

theorem cut_cross (G : FiniteDigraph A) (r p : A) (edge : G.UAdj r p)
    (acyclic : UnderlyingAcyclic G) {a b : A}
    (left : Reach (WithoutEdge G r p) r a) (right : Reach (WithoutEdge G r p) p b)
    (adj : G.UAdj a b) : a = r ∧ b = p := by
  classical
  by_cases removed : (a = r ∧ b = p) ∨ (a = p ∧ b = r)
  · rcases removed with h | ⟨eq,_⟩
    · exact h
    · exact False.elim (cut_disjoint G r p edge acyclic p (eq ▸ left) (.refl _))
  · exact False.elim (cut_disjoint G r p edge acyclic b (.tail left ⟨adj,removed⟩) right)

theorem cut_leaf_extension (G : FiniteDigraph A) (r p : A) (c : A → Sign)
    (color : ∀ a b, G.Arc a b → c a = .plus ∧ c b = .minus)
    (edge : G.UAdj r p) (acyclic : UnderlyingAcyclic G) :
    LeafExtension (induced G (Reach (WithoutEdge G r p) p))
      (induced G (fun x => x = r ∨ Reach (WithoutEdge G r p) p x)) p r (c r) := by
  have hr := (uadj_mem G edge).1
  have hp := (uadj_mem G edge).2
  have directed := (colored_edge G c color edge).1
  have notRight : ¬ Reach (WithoutEdge G r p) p r :=
    fun h => cut_disjoint G r p edge acyclic r (.refl _) h
  constructor
  · exact (induced_mem _ _ _).mpr ⟨hp,.refl _⟩
  · intro h; exact notRight ((induced_mem _ _ _).mp h).2
  · intro a
    simp only [induced_mem]
    constructor
    · rintro ⟨h,eq | right⟩
      · exact Or.inr eq
      · exact Or.inl ⟨h,right⟩
    · rintro (⟨h,right⟩ | rfl)
      · exact ⟨h,Or.inr right⟩
      · exact ⟨hr,Or.inl rfl⟩
  · intro a b
    simp only [induced_arc]
    constructor
    · rintro ⟨hab,(ar | ha),(br | hb)⟩
      · exact False.elim (G.loopless r (by simpa [ar,br] using hab))
      · have eq := (cut_cross G r p edge acyclic (ar.symm ▸ Reach.refl r) hb (Or.inl hab)).2
        exact Or.inr (Or.inl ⟨by simpa [ar] using (color a b hab).1,ar,eq⟩)
      · have eq := (cut_cross G r p edge acyclic (br.symm ▸ Reach.refl r) ha (Or.inr hab)).2
        exact Or.inr (Or.inr ⟨by simpa [br] using (color a b hab).2,eq,br⟩)
      · exact Or.inl ⟨hab,ha,hb⟩
    · rintro (⟨hab,ha,hb⟩ | ⟨sign,rfl,rfl⟩ | ⟨sign,rfl,rfl⟩)
      · exact ⟨hab,Or.inr ha,Or.inr hb⟩
      · exact ⟨by simpa [sign, FiniteDigraph.Adj] using directed, Or.inl rfl, Or.inr (.refl _)⟩
      · exact ⟨by simpa [sign, FiniteDigraph.Adj] using directed, Or.inr (.refl _), Or.inl rfl⟩

theorem cut_amalgam (G : FiniteDigraph A) (r p : A) (edge : G.UAdj r p)
    (conn : UnderlyingConnected G) (acyclic : UnderlyingAcyclic G) :
    RootAmalgam (induced G (Reach (WithoutEdge G r p) r))
      (induced G (fun x => x = r ∨ Reach (WithoutEdge G r p) p x)) G r := by
  classical
  have hr := (uadj_mem G edge).1
  have cover : ∀ x, x ∈ G.vertices →
      Reach (WithoutEdge G r p) r x ∨ Reach (WithoutEdge G r p) p x :=
    fun x hx => cut_cover G r p (conn r hr x hx)
  constructor
  · exact (induced_mem _ _ _).mpr ⟨hr,.refl _⟩
  · exact (induced_mem _ _ _).mpr ⟨hr,Or.inl rfl⟩
  · intro a
    simp only [induced_mem]
    constructor
    · intro ha
      exact (cover a ha).elim (fun h => Or.inl ⟨ha,h⟩) (fun h => Or.inr ⟨ha,Or.inr h⟩)
    · rintro (h | h) <;> exact h.1
  · intro a
    simp only [induced_mem]
    constructor
    · rintro ⟨⟨_,left⟩,⟨_,eq | right⟩⟩
      · exact eq
      · exact False.elim (cut_disjoint G r p edge acyclic a left right)
    · rintro rfl; exact ⟨⟨hr,.refl _⟩,⟨hr,Or.inl rfl⟩⟩
  · intro a b
    simp only [induced_arc]
    constructor
    · intro hab
      rcases cover a (G.endpoints a b hab).1 with la | ra <;>
        rcases cover b (G.endpoints a b hab).2 with lb | rb
      · exact Or.inl ⟨hab,la,lb⟩
      · have eq := (cut_cross G r p edge acyclic la rb (Or.inl hab)).1
        exact Or.inr ⟨hab,Or.inl eq,Or.inr rb⟩
      · have eq := (cut_cross G r p edge acyclic lb ra (Or.inr hab)).1
        exact Or.inr ⟨hab,Or.inr ra,Or.inl eq⟩
      · exact Or.inr ⟨hab,Or.inr ra,Or.inr rb⟩
    · rintro (h | h) <;> exact h.1

end Digraph
