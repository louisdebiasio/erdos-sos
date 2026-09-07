import NormalizationTests

namespace Kalai.GlobalTests

open Kalai.HypergraphTests

def threeFaces : FiniteHypergraph Nat where
  vertices := [1, 2, 3, 4, 5, 6]
  edges := [[1, 2, 3], [1, 2, 4], [1, 3, 5], [2, 3, 6]]
  vertices_nodup := by decide
  edge_nodup := by decide
  edge_vertices := by decide
  simple := by decide

theorem threeFacesTree : IsTightTree threeFaces 3 := by
  refine ⟨by simp [FiniteHypergraph.Uniform, threeFaces], ?_, threeFaces.edges, List.Perm.refl _, ?_⟩
  · intro vertex
    simp [threeFaces, or_assoc, or_left_comm, or_comm]
  · apply tightEdgeOrder_of_index _ (by decide)
    intro position nonzero
    have bound := position.isLt
    change position.val < 4 at bound
    have alternatives : position.val = 1 ∨ position.val = 2 ∨ position.val = 3 := by omega
    rcases alternatives with first | second | third
    · refine ⟨4, [1, 2, 3], ?_⟩
      simp [threeFaces, first]
    · refine ⟨5, [1, 2, 3], ?_⟩
      simp [threeFaces, second]
    · refine ⟨6, [1, 2, 3], ?_⟩
      simp [threeFaces, third]

example : RootedConstruction 3 threeFaces [3, 2, 6] 4 :=
  threeFacesTree.growth.rooted [3, 2, 6]
    ((threeFaces.hasEdge_perm (show [2, 3, 6].Perm [3, 2, 6] by decide)).mp
      (threeFaces.hasEdge_of_mem (by decide)))

example (host : FiniteHypergraph Nat) (uniform : host.Uniform 3)
    (free : ¬ Nonempty (Embedding threeFaces host)) :
    3 * host.edges.length ≤ 3 * binomial host.vertices.length 2 :=
  kalai_bound threeFacesTree host (by decide) uniform free

def pathThree : FiniteHypergraph Nat where
  vertices := [0, 1, 2, 3]
  edges := [[0, 1], [1, 2], [2, 3]]
  vertices_nodup := by decide
  edge_nodup := by decide
  edge_vertices := by decide
  simple := by decide

theorem pathThreeTree : IsTightTree pathThree 2 := by
  refine ⟨by simp [FiniteHypergraph.Uniform, pathThree], ?_, pathThree.edges, List.Perm.refl _, ?_⟩
  · intro vertex
    simp [pathThree, or_assoc, or_left_comm, or_comm]
  · apply tightEdgeOrder_of_index _ (by decide)
    intro position nonzero
    have bound := position.isLt
    change position.val < 3 at bound
    have alternatives : position.val = 1 ∨ position.val = 2 := by omega
    rcases alternatives with first | second
    · refine ⟨2, [0, 1], ?_⟩
      simp [pathThree, first]
    · refine ⟨3, [1, 2], ?_⟩
      simp [pathThree, second]

def triangle : FiniteHypergraph Nat where
  vertices := [0, 1, 2]
  edges := [[0, 1], [0, 2], [1, 2]]
  vertices_nodup := by decide
  edge_nodup := by decide
  edge_vertices := by decide
  simple := by decide

theorem triangleNotTree : ¬ IsTightTree triangle 2 := by
  intro tree
  have impossible := tree.vertex_count
  change 4 = 5 at impossible
  omega

def isolated : FiniteHypergraph Nat where
  vertices := [0, 1, 2]
  edges := [[0, 1]]
  vertices_nodup := by decide
  edge_nodup := by decide
  edge_vertices := by decide
  simple := by decide

theorem isolatedNotTree : ¬ IsTightTree isolated 2 := by
  intro tree
  have impossible := tree.vertex_count
  change 4 = 3 at impossible
  omega

theorem triangleAvoidsPath : ¬ Nonempty (Embedding pathThree triangle) :=
  no_embedding_of_too_many_vertices pathThree triangle (by decide)

example : 2 * triangle.edges.length ≤
    (pathThree.edges.length - 1) * binomial triangle.vertices.length 1 :=
  kalai_bound pathThreeTree triangle (by decide) (by simp [FiniteHypergraph.Uniform, triangle]) triangleAvoidsPath

example : 2 * triangle.edges.length =
    (pathThree.edges.length - 1) * binomial triangle.vertices.length 1 := by decide

example : edgeStateCount triangle = 12 := by
  rw [edgeStateCount_normalization triangle 2 (by simp [FiniteHypergraph.Uniform, triangle])]
  rfl

example : edgeStateCount threeFaces = 576 := by
  rw [edgeStateCount_normalization threeFaces 3 (by simp [FiniteHypergraph.Uniform, threeFaces])]
  rfl

example : globalSupportCount threeFaces threeFaces [1, 2, 3] =
    globalSupportCount threeFaces threeFaces [3, 1, 2] :=
  globalSupportCount_root_perm threeFaces threeFaces [1, 2, 3] [3, 1, 2] (by decide)

example : globalSupportCount pathThree triangle [0, 1] = 0 :=
  globalSupportCount_eq_zero_of_free pathThree triangle [0, 1] triangleAvoidsPath

def emptyHost : FiniteHypergraph Nat where
  vertices := []
  edges := []
  vertices_nodup := by decide
  edge_nodup := by decide
  edge_vertices := by decide
  simple := by decide

example : 3 * emptyHost.edges.length ≤
    (threeFaces.edges.length - 1) * binomial emptyHost.vertices.length 2 :=
  kalai_bound threeFacesTree emptyHost (by decide) (by simp [FiniteHypergraph.Uniform, emptyHost])
    (no_embedding_of_too_many_vertices threeFaces emptyHost (by decide))

example : binomial 5 2 = 10 := by decide

example : binomial 3 4 = 0 := by decide

example : binomial 0 0 = 1 := rfl

example : subsetsOfSize ([0, 1, 2] : List Nat) 2 = [[0, 1], [0, 2], [1, 2]] := rfl

end Kalai.GlobalTests
