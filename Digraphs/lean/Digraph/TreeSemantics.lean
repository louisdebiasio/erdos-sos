import Digraph.RootedTree

namespace Digraph

universe u
variable {A : Type u}

theorem RootedTree.root_mem {T : FiniteDigraph A} {r : A} {s : Sign} {k : Nat}
    (tree : RootedTree T r s k) : r ∈ T.vertices := by
  cases tree with
  | edge T r p s one => exact (one.vertices r).mpr (Or.inl rfl)
  | leaf S T p l s k built ext => exact (ext.vertices _).mpr (Or.inr rfl)
  | branch S U T r s i j first second am =>
    exact (am.vertices_union r).mpr (Or.inl am.first_root)

/-- The sign in a construction is genuinely its source/sink sign. -/
theorem RootedTree.color {T : FiniteDigraph A} {r : A} {s : Sign} {k : Nat}
    (tree : RootedTree T r s k) :
    ∃ c : A → Sign, c r = s ∧ ∀ a b, T.Arc a b → c a = .plus ∧ c b = .minus := by
  classical
  induction tree with
  | edge T r p s one =>
    let c := fun a => if a = r then s else s.flip
    refine ⟨c, by simp [c], ?_⟩
    intro a b h
    rcases (one.arcs a b).mp h with ⟨sign, ar, bp⟩ | ⟨sign, ap, br⟩
    · simp [c, ar, bp, sign, Ne.symm one.different, Sign.flip]
    · simp [c, ap, br, sign, Ne.symm one.different, Sign.flip]
  | leaf S T p l s k built ext ih =>
    obtain ⟨old, atRoot, colored⟩ := ih
    let c := fun a => if a = l then s else old a
    have onOld : ∀ a, a ∈ S.vertices → c a = old a := by
      intro a ha
      have ne : a ≠ l := fun eq => ext.fresh (eq ▸ ha)
      simp [c, ne]
    have onNew : c l = s := by simp [c]
    refine ⟨c, onNew, ?_⟩
    intro a b h
    rcases (ext.arcs a b).mp h with oldArc | ⟨sign, al, bp⟩ | ⟨sign, ap, bl⟩
    · rw [onOld a (S.endpoints a b oldArc).1, onOld b (S.endpoints a b oldArc).2]
      exact colored a b oldArc
    · rw [al, bp, onNew, onOld p ext.old_root, atRoot, sign]
      decide
    · rw [ap, bl, onOld p ext.old_root, onNew, atRoot, sign]
      decide
  | branch S U T r s i j first second am ihs ihu =>
    obtain ⟨cs, sr, scolor⟩ := ihs
    obtain ⟨cu, ur, ucolor⟩ := ihu
    let c := fun a => if a ∈ S.vertices then cs a else cu a
    have onS : ∀ a, a ∈ S.vertices → c a = cs a := by
      intro a ha; simp [c, ha]
    have onU : ∀ a, a ∈ U.vertices → c a = cu a := by
      intro a ha
      by_cases hs : a ∈ S.vertices
      · have eq := (am.vertices_intersection a).mp ⟨hs, ha⟩
        simp [c, hs, eq, sr, ur]
      · simp [c, hs]
    refine ⟨c, (onS r am.first_root).trans sr, ?_⟩
    intro a b h
    rcases (am.arcs_union a b).mp h with sh | uh
    · rw [onS a (S.endpoints a b sh).1, onS b (S.endpoints a b sh).2]
      exact scolor a b sh
    · rw [onU a (U.endpoints a b uh).1, onU b (U.endpoints a b uh).2]
      exact ucolor a b uh

theorem RootedTree.antidirected {T : FiniteDigraph A} {r : A} {s : Sign} {k : Nat}
    (tree : RootedTree T r s k) : Antidirected T := by
  obtain ⟨c, _, colored⟩ := tree.color
  exact ⟨c, colored⟩

/-- Unrooted constructive interface. Its size is the actual vertex-list length. -/
def IsAntidirectedTree (T : FiniteDigraph A) : Prop :=
  ∃ r s k, RootedTree T r s k

theorem isAntidirectedTree_antidirected (T : FiniteDigraph A) (h : IsAntidirectedTree T) :
    Antidirected T := by
  obtain ⟨r, s, k, tree⟩ := h
  exact tree.antidirected

theorem addarioBerry_bound {B : Type u} (T : FiniteDigraph A) (D : FiniteDigraph B)
    (tree : IsAntidirectedTree T) (free : ¬ Nonempty (Embedding T D)) :
    D.arcs.length ≤ (T.vertices.length - 2) * D.vertices.length := by
  obtain ⟨r, s, k, built⟩ := tree
  exact antidirected_density built D free

theorem addarioBerry_contains {B : Type u} (T : FiniteDigraph A) (D : FiniteDigraph B)
    (tree : IsAntidirectedTree T)
    (dense : (T.vertices.length - 2) * D.vertices.length < D.arcs.length) :
    Nonempty (Embedding T D) := by
  obtain ⟨r, s, k, built⟩ := tree
  exact antidirected_contains_tree built D dense

end Digraph
