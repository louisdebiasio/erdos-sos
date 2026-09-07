import Digraph.StateEnumeration

namespace Digraph

universe u v

/-- Arcs are ordered pairs. Opposite arcs are allowed; loops and repeated arcs are not. -/
structure FiniteDigraph (Vertex : Type u) where
  vertices : List Vertex
  arcs : List (Vertex × Vertex)
  vertices_nodup : vertices.Nodup
  arcs_nodup : arcs.Nodup
  endpoints : ∀ a b, (a, b) ∈ arcs → a ∈ vertices ∧ b ∈ vertices
  loopless : ∀ a, (a, a) ∉ arcs

def FiniteDigraph.Arc {V : Type u} (G : FiniteDigraph V) (a b : V) : Prop :=
  (a, b) ∈ G.arcs

inductive Sign where
  | plus | minus
  deriving DecidableEq, Repr

def Sign.flip : Sign → Sign
  | .plus => .minus
  | .minus => .plus

@[simp] theorem Sign.flip_flip (s : Sign) : s.flip.flip = s := by cases s <;> rfl

def FiniteDigraph.Adj {V : Type u} (G : FiniteDigraph V) (s : Sign) (a b : V) : Prop :=
  match s with
  | .plus => G.Arc a b
  | .minus => G.Arc b a

@[simp] theorem adj_flip {V : Type u} (G : FiniteDigraph V) (s : Sign) (a b : V) :
    G.Adj s.flip a b ↔ G.Adj s b a := by cases s <;> rfl

theorem adj_endpoints {V : Type u} (G : FiniteDigraph V) (s : Sign) {a b : V}
    (h : G.Adj s a b) : a ∈ G.vertices ∧ b ∈ G.vertices := by
  cases s with
  | plus => exact G.endpoints a b h
  | minus => exact (G.endpoints b a h).symm

/-- A source/sink assignment, with no restriction on isolated vertices. -/
def Antidirected {V : Type u} (T : FiniteDigraph V) : Prop :=
  ∃ color : V → Sign, ∀ a b, T.Arc a b → color a = .plus ∧ color b = .minus

/-- Injectivity is across ALL listed target vertices, not separately in each color class. -/
structure Embedding {A : Type u} {B : Type v}
    (T : FiniteDigraph A) (D : FiniteDigraph B) where
  toFun : A → B
  maps_vertices : ∀ a, a ∈ T.vertices → toFun a ∈ D.vertices
  injective : ∀ a, a ∈ T.vertices → ∀ b, b ∈ T.vertices → toFun a = toFun b → a = b
  maps_arcs : ∀ a b, T.Arc a b → D.Arc (toFun a) (toFun b)

theorem Embedding.maps_adj {A : Type u} {B : Type v}
    {T : FiniteDigraph A} {D : FiniteDigraph B} (f : Embedding T D)
    (s : Sign) (a b : A) (h : T.Adj s a b) : D.Adj s (f.toFun a) (f.toFun b) := by
  cases s with
  | plus => exact f.maps_arcs a b h
  | minus => exact f.maps_arcs b a h

def Supports {A : Type u} {B : Type v} (T : FiniteDigraph A) (D : FiniteDigraph B)
    (r : A) (x : B) (block : List B) : Prop :=
  ∃ f : Embedding T D, f.toFun r = x ∧
    ∀ a, a ∈ T.vertices → f.toFun a ∈ x :: block

theorem supports_mono {A : Type u} {B : Type v} (T : FiniteDigraph A)
    (D : FiniteDigraph B) (r : A) (x : B) (a b : List B)
    (included : ∀ y, y ∈ a → y ∈ b) (h : Supports T D r x a) : Supports T D r x b := by
  obtain ⟨f, root, inside⟩ := h
  refine ⟨f, root, ?_⟩
  intro y hy
  rcases List.mem_cons.mp (inside y hy) with eq | mem
  · exact List.mem_cons.mpr (Or.inl eq)
  · exact List.mem_cons.mpr (Or.inr (included _ mem))

theorem nonroot_in_block {A : Type u} {B : Type v} {T : FiniteDigraph A}
    {D : FiniteDigraph B} (f : Embedding T D) (r : A) (hr : r ∈ T.vertices)
    (x : B) (block : List B) (root : f.toFun r = x)
    (inside : ∀ a, a ∈ T.vertices → f.toFun a ∈ x :: block)
    (a : A) (ha : a ∈ T.vertices) (ne : a ≠ r) : f.toFun a ∈ block := by
  rcases List.mem_cons.mp (inside a ha) with eq | mem
  · exact False.elim (ne (f.injective a ha r hr (eq.trans root.symm)))
  · exact mem

/-- The explicit leaf-extension hypothesis records exactly the arcs being added. -/
structure LeafExtension {A : Type u} (S T : FiniteDigraph A) (p l : A) (s : Sign) : Prop where
  old_root : p ∈ S.vertices
  fresh : l ∉ S.vertices
  vertices : ∀ a, a ∈ T.vertices ↔ a ∈ S.vertices ∨ a = l
  arcs : ∀ a b, T.Arc a b ↔ S.Arc a b ∨
    (s = .plus ∧ a = l ∧ b = p) ∨ (s = .minus ∧ a = p ∧ b = l)

theorem extend_leaf_embedding {A : Type u} {B : Type v}
    (S T : FiniteDigraph A) (D : FiniteDigraph B) (p l : A) (s : Sign)
    (ext : LeafExtension S T p l s) (f : Embedding S D) (z : B)
    (fresh : ∀ a, a ∈ S.vertices → f.toFun a ≠ z)
    (mark : D.Adj s z (f.toFun p)) :
    ∃ g : Embedding T D, g.toFun l = z ∧
      ∀ a, a ∈ S.vertices → g.toFun a = f.toFun a := by
  classical
  let combined := fun a => if a = l then z else f.toFun a
  have onNew : combined l = z := by simp [combined]
  have onOld : ∀ a, a ∈ S.vertices → combined a = f.toFun a := by
    intro a ha
    have ne : a ≠ l := fun eq => ext.fresh (eq ▸ ha)
    simp [combined, ne]
  refine ⟨{ toFun := combined, maps_vertices := ?_, injective := ?_, maps_arcs := ?_ },
    onNew, onOld⟩
  · intro a ha
    rcases (ext.vertices a).mp ha with old | new
    · rw [onOld a old]; exact f.maps_vertices a old
    · rw [new, onNew]; exact (adj_endpoints D s mark).1
  · intro a ha b hb eq
    rcases (ext.vertices a).mp ha with oldA | newA <;>
      rcases (ext.vertices b).mp hb with oldB | newB
    · exact f.injective a oldA b oldB ((onOld a oldA).symm.trans (eq.trans (onOld b oldB)))
    · exact False.elim (fresh a oldA (by simpa [onOld a oldA, newB, onNew] using eq))
    · exact False.elim (fresh b oldB (by simpa [onOld b oldB, newA, onNew] using eq.symm))
    · exact newA.trans newB.symm
  · intro a b hab
    rcases (ext.arcs a b).mp hab with old | ⟨sign, rfl, rfl⟩ | ⟨sign, rfl, rfl⟩
    · rw [onOld a (S.endpoints a b old).1, onOld b (S.endpoints a b old).2]
      exact f.maps_arcs a b old
    · rw [onNew, onOld _ ext.old_root]; simpa [sign, FiniteDigraph.Adj] using mark
    · rw [onOld _ ext.old_root, onNew]; simpa [sign, FiniteDigraph.Adj] using mark

end Digraph
