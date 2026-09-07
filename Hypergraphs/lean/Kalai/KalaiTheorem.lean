import Kalai.TightTree

namespace Kalai

universe u v

variable {Vertex : Type u} {Host : Type v}

def binomial : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | count + 1, size + 1 => binomial count size + binomial count (size + 1)

def subsetsOfSize : List Vertex → Nat → List (List Vertex)
  | [], 0 => [[]]
  | [], _ + 1 => []
  | _ :: _, 0 => [[]]
  | head :: tail, size + 1 => (subsetsOfSize tail size).map (head :: ·) ++ subsetsOfSize tail (size + 1)

theorem subsetsOfSize_length (vertices : List Vertex) (size : Nat) :
    (subsetsOfSize vertices size).length = binomial vertices.length size := by
  induction vertices generalizing size with
  | nil => cases size <;> rfl
  | cons head tail inductionHypothesis =>
    cases size with
    | zero => rfl
    | succ size => simp only [subsetsOfSize, List.length_append, List.length_map, inductionHypothesis, List.length_cons, binomial]

theorem subsetsOfSize_complete {vertices face : List Vertex} (included : face.Sublist vertices) :
    face ∈ subsetsOfSize vertices face.length := by
  induction included with
  | slnil => simp [subsetsOfSize]
  | @cons smaller larger head included inductionHypothesis =>
    cases smaller with
    | nil => simp [subsetsOfSize]
    | cons first rest => exact List.mem_append_right _ inductionHypothesis
  | cons₂ head included inductionHypothesis =>
    exact List.mem_append_left _ (List.mem_map.mpr ⟨_, inductionHypothesis, rfl⟩)

theorem shadowCount_le_binomial (host : FiniteHypergraph Host) (size : Nat) :
    shadowCount host size ≤ binomial host.vertices.length size := by
  classical
  rw [← subsetsOfSize_length host.vertices size]
  apply nodup_length_le_of_subset (shadowFaceListing host size).values (subsetsOfSize host.vertices size)
    (shadowFaceListing host size).distinct
  intro face present
  have valid := ((shadowFaceListing host size).membership face).mp present
  have sublist : face.Sublist host.vertices := by
    rw [← valid.2.2]
    exact List.filter_sublist
  have member := subsetsOfSize_complete sublist
  simpa only [valid.1] using member

theorem kalai_bound {target : FiniteHypergraph Vertex} {uniformity : Nat}
    (tree : IsTightTree target uniformity) (host : FiniteHypergraph Host)
    (atLeastTwo : 2 ≤ uniformity) (uniform : host.Uniform uniformity)
    (free : ¬ Nonempty (Embedding target host)) :
    uniformity * host.edges.length ≤
      (target.edges.length - 1) * binomial host.vertices.length (uniformity - 1) :=
  Nat.le_trans (kalai_shadow_bound tree host atLeastTwo uniform free)
    (Nat.mul_le_mul_left (target.edges.length - 1) (shadowCount_le_binomial host (uniformity - 1)))

theorem kalai_contains_tree {target : FiniteHypergraph Vertex} {uniformity : Nat}
    (tree : IsTightTree target uniformity) (host : FiniteHypergraph Host)
    (atLeastTwo : 2 ≤ uniformity) (uniform : host.Uniform uniformity)
    (dense : (target.edges.length - 1) * binomial host.vertices.length (uniformity - 1) <
      uniformity * host.edges.length) : Nonempty (Embedding target host) := by
  apply Classical.byContradiction
  intro free
  have bound := kalai_bound tree host atLeastTwo uniform free
  omega

end Kalai
