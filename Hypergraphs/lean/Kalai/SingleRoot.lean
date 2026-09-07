import Kalai.ShadowCounts

namespace Kalai

universe u v

variable {Target : Type u} {Host : Type v}

structure SingleRoot (target : FiniteHypergraph Target) (root : List Target) (uniformity : Nat) : Prop where
  root_edge : target.HasEdge root
  root_length : root.length = uniformity
  vertices : ∀ vertex, vertex ∈ target.vertices ↔ vertex ∈ root
  edges : ∀ edge ∈ target.edges, edge.Perm root

theorem exists_map_lists (source : List Target) (distinct : source.Nodup)
    (image : List Host) (sameLength : source.length = image.length) (default : Host) :
    ∃ mapping : Target → Host, source.map mapping = image := by
  classical
  induction source generalizing image with
  | nil =>
    have empty : image = [] := List.length_eq_zero_iff.mp sameLength.symm
    exact ⟨fun _ => default, by simp [empty]⟩
  | cons head tail inductionHypothesis =>
    cases image with
    | nil => simp at sameLength
    | cons imageHead imageTail =>
      obtain ⟨tailMap, tailEq⟩ := inductionHypothesis (List.nodup_cons.mp distinct).2 imageTail
        (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using sameLength)
      let mapping := fun vertex => if vertex = head then imageHead else tailMap vertex
      have tailAgreement : tail.map mapping = tail.map tailMap := by
        apply List.map_inj_left.mpr
        intro vertex present
        have different : vertex ≠ head := fun same => (List.nodup_cons.mp distinct).1 (same ▸ present)
        simp only [mapping, if_neg different]
      exact ⟨mapping, by rw [List.map_cons, tailAgreement, tailEq]; simp [mapping]⟩

theorem injective_on_list_of_map_nodup (source : List Target) (mapping : Target → Host)
    (distinct : (source.map mapping).Nodup) :
    ∀ first ∈ source, ∀ second ∈ source, mapping first = mapping second → first = second := by
  induction source with
  | nil => simp
  | cons head tail inductionHypothesis =>
    have headAbsent := (List.nodup_cons.mp distinct).1
    have tailDistinct := (List.nodup_cons.mp distinct).2
    intro first inFirst second inSecond same
    rcases List.mem_cons.mp inFirst with rfl | firstInTail
    · rcases List.mem_cons.mp inSecond with rfl | secondInTail
      · rfl
      · exact False.elim (headAbsent (List.mem_map.mpr ⟨second, secondInTail, same.symm⟩))
    · rcases List.mem_cons.mp inSecond with rfl | secondInTail
      · exact False.elim (headAbsent (List.mem_map.mpr ⟨first, firstInTail, same⟩))
      · exact inductionHypothesis tailDistinct first firstInTail second secondInTail same

theorem singleRoot_orderedSupport (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) (uniformity : Nat) (positive : 0 < uniformity)
    (single : SingleRoot target root uniformity) (uniform : host.Uniform uniformity)
    (image block : List Host) (edge : host.HasEdge image) : OrderedSupport target host root image block := by
  have imageLength := host.hasEdge_length uniform edge
  have imageNonempty : image ≠ [] := by intro empty; simp [empty] at imageLength; omega
  obtain ⟨mapping, prescribed⟩ := exists_map_lists root (target.hasEdge_nodup single.root_edge) image
    (single.root_length.trans imageLength.symm) (image.head imageNonempty)
  have imageDistinct : (root.map mapping).Nodup := prescribed ▸ host.hasEdge_nodup edge
  let embedding : Embedding target host := {
    toFun := mapping
    maps_vertices := fun vertex present => host.hasEdge_vertex edge
      (prescribed ▸ List.mem_map.mpr ⟨vertex, (single.vertices vertex).mp present, rfl⟩)
    injective := fun first inFirst second inSecond => injective_on_list_of_map_nodup root mapping imageDistinct
      first ((single.vertices first).mp inFirst) second ((single.vertices second).mp inSecond)
    maps_edges := fun targetEdge present => (host.hasEdge_perm ((single.edges targetEdge present).map mapping)).mpr
      (by simpa only [prescribed] using edge)
  }
  exact ⟨embedding, prescribed, fun vertex present => List.mem_append_left block
    (prescribed ▸ List.mem_map.mpr ⟨vertex, (single.vertices vertex).mp present, rfl⟩)⟩

theorem singleRoot_global_count (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) (uniformity : Nat) (positive : 0 < uniformity)
    (single : SingleRoot target root uniformity) (uniform : host.Uniform uniformity) :
    globalSupportCount target host root = edgeStateCount host := by
  apply (globalSupportListing target host root).card_eq_of_iff (edgeStateListing host)
  intro state
  constructor
  · intro supported
    exact ⟨supported.1, supported.2.1⟩
  · intro valid
    exact ⟨valid.1, valid.2, singleRoot_orderedSupport target host root uniformity positive single uniform
      state.1 state.2.prefix valid.1⟩

end Kalai
