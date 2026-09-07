import Digraph.SignedLeaf

namespace Digraph

universe u v
variable {A : Type u} {B : Type v}

structure RootAmalgam (S U T : FiniteDigraph A) (r : A) : Prop where
  first_root : r ∈ S.vertices
  second_root : r ∈ U.vertices
  vertices_union : ∀ a, a ∈ T.vertices ↔ a ∈ S.vertices ∨ a ∈ U.vertices
  vertices_intersection : ∀ a, (a ∈ S.vertices ∧ a ∈ U.vertices) ↔ a = r
  arcs_union : ∀ a b, T.Arc a b ↔ S.Arc a b ∨ U.Arc a b

theorem supports_restrict (S T : FiniteDigraph A) (D : FiniteDigraph B)
    (r : A) (x : B) (block : List B)
    (vertices : ∀ a, a ∈ S.vertices → a ∈ T.vertices)
    (arcs : ∀ a b, S.Arc a b → T.Arc a b)
    (h : Supports T D r x block) : Supports S D r x block := by
  obtain ⟨f, root, inside⟩ := h
  let g : Embedding S D := {
    toFun := f.toFun
    maps_vertices := fun a ha => f.maps_vertices a (vertices a ha)
    injective := fun a ha b hb eq => f.injective a (vertices a ha) b (vertices b hb) eq
    maps_arcs := fun a b h => f.maps_arcs a b (arcs a b h)
  }
  exact ⟨g, root, fun a ha => inside a (vertices a ha)⟩

theorem supports_glue (S U T : FiniteDigraph A) (D : FiniteDigraph B)
    (r : A) (am : RootAmalgam S U T r) (x : B) (a b : List B)
    (distinct : (a ++ b).Nodup) (hs : Supports S D r x a) (hu : Supports U D r x b) :
    Supports T D r x (a ++ b) := by
  classical
  obtain ⟨f, fr, fi⟩ := hs
  obtain ⟨g, gr, gi⟩ := hu
  let combined := fun y => if y ∈ S.vertices then f.toFun y else g.toFun y
  have onS : ∀ y, y ∈ S.vertices → combined y = f.toFun y := by
    intro y hy; simp [combined, hy]
  have onU : ∀ y, y ∈ U.vertices → combined y = g.toFun y := by
    intro y hy
    by_cases h : y ∈ S.vertices
    · have eq := (am.vertices_intersection y).mp ⟨h, hy⟩
      simp [combined, h, eq, fr, gr]
    · simp [combined, h]
  have cross : ∀ y, y ∈ S.vertices → ∀ z, z ∈ U.vertices →
      combined y = combined z → y = z := by
    intro y hy z hz eq
    by_cases yu : y ∈ U.vertices
    · apply g.injective y yu z hz
      simpa only [onU y yu, onU z hz] using eq
    · by_cases zs : z ∈ S.vertices
      · apply f.injective y hy z zs
        simpa only [onS y hy, onS z zs] using eq
      · have yr : y ≠ r := fun h => yu (h ▸ am.second_root)
        have zr : z ≠ r := fun h => zs (h ▸ am.first_root)
        have fy := nonroot_in_block f r am.first_root x a fr fi y hy yr
        have gz := nonroot_in_block g r am.second_root x b gr gi z hz zr
        have disj := (List.pairwise_append.mp distinct).2.2
        exact False.elim (disj _ fy _ gz (by simpa only [onS y hy, onU z hz] using eq))
  have inj : ∀ y, y ∈ T.vertices → ∀ z, z ∈ T.vertices →
      combined y = combined z → y = z := by
    intro y hy z hz eq
    rcases (am.vertices_union y).mp hy with sy | uy <;>
      rcases (am.vertices_union z).mp hz with sz | uz
    · apply f.injective y sy z sz
      simpa only [onS y sy, onS z sz] using eq
    · exact cross y sy z uz eq
    · exact (cross z sz y uy eq.symm).symm
    · apply g.injective y uy z uz
      simpa only [onU y uy, onU z uz] using eq
  refine ⟨{ toFun := combined, maps_vertices := ?_, injective := inj, maps_arcs := ?_ }, ?_, ?_⟩
  · intro y hy
    rcases (am.vertices_union y).mp hy with sy | uy
    · rw [onS y sy]; exact f.maps_vertices y sy
    · rw [onU y uy]; exact g.maps_vertices y uy
  · intro y z h
    rcases (am.arcs_union y z).mp h with sh | uh
    · rw [onS y (S.endpoints y z sh).1, onS z (S.endpoints y z sh).2]
      exact f.maps_arcs y z sh
    · rw [onU y (U.endpoints y z uh).1, onU z (U.endpoints y z uh).2]
      exact g.maps_arcs y z uh
  · exact (onS r am.first_root).trans fr
  · intro y hy
    change combined y ∈ x :: (a ++ b)
    rcases (am.vertices_union y).mp hy with sy | uy
    · rw [onS y sy]
      rcases List.mem_cons.mp (fi y sy) with eq | mem
      · simp [eq]
      · simp [mem]
    · rw [onU y uy]
      rcases List.mem_cons.mp (gi y uy) with eq | mem
      · simp [eq]
      · simp [mem]

end Digraph
