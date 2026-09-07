import Kalai.SingleRoot

namespace Kalai

universe u v

variable {Vertex : Type u} {Host : Type v}

inductive RootedConstruction (uniformity : Nat) : FiniteHypergraph Vertex → List Vertex → Nat → Prop where
  | single (target : FiniteHypergraph Vertex) (root : List Vertex)
      (data : SingleRoot target root uniformity) : RootedConstruction uniformity target root 1
  | leaf (smaller larger : FiniteHypergraph Vertex) (face : List Vertex) (oldEndpoint newVertex : Vertex)
      (size : Nat) (built : RootedConstruction uniformity smaller (face ++ [oldEndpoint]) size)
      (extension : LeafExtension smaller larger face oldEndpoint newVertex) :
      RootedConstruction uniformity larger (face ++ [newVertex]) (size + 1)
  | glue (first second joined : FiniteHypergraph Vertex) (root : List Vertex) (firstSize secondSize : Nat)
      (firstBuilt : RootedConstruction uniformity first root firstSize)
      (secondBuilt : RootedConstruction uniformity second root secondSize)
      (amalgam : EdgeAmalgam first second joined root) :
      RootedConstruction uniformity joined root (firstSize + secondSize - 1)
  | reorder (target : FiniteHypergraph Vertex) (root otherRoot : List Vertex) (size : Nat)
      (built : RootedConstruction uniformity target root size) (ordering : root.Perm otherRoot) :
      RootedConstruction uniformity target otherRoot size

theorem RootedConstruction.root_spec {uniformity size : Nat} {target : FiniteHypergraph Vertex}
    {root : List Vertex} (built : RootedConstruction uniformity target root size) :
    target.HasEdge root ∧ root.length = uniformity ∧ 0 < size := by
  induction built with
  | single target root data => exact ⟨data.root_edge, data.root_length, by decide⟩
  | leaf smaller larger face oldEndpoint newVertex size built extension inductionHypothesis =>
    refine ⟨(extension.edges_added _).mpr (Or.inr (List.Perm.refl _)), ?_, by omega⟩
    simpa only [List.length_append, List.length_cons, List.length_nil] using inductionHypothesis.2.1
  | glue first second joined root firstSize secondSize firstBuilt secondBuilt amalgam firstIH secondIH =>
    exact ⟨(amalgam.edges_union root).mpr (Or.inl firstIH.1), firstIH.2.1, by omega⟩
  | reorder target root otherRoot size built ordering inductionHypothesis =>
    exact ⟨(target.hasEdge_perm ordering).mp inductionHypothesis.1,
      ordering.length_eq.symm.trans inductionHypothesis.2.1, inductionHypothesis.2.2⟩

theorem rootedConstruction_master {uniformity size : Nat} {target : FiniteHypergraph Vertex}
    {root : List Vertex} (built : RootedConstruction uniformity target root size)
    (host : FiniteHypergraph Host) (positive : 0 < uniformity) (uniform : host.Uniform uniformity) :
    edgeStateCount host ≤ globalSupportCount target host root + (size - 1) * shadowPermutationCount host (uniformity - 1) := by
  induction built with
  | single target root data =>
    rw [singleRoot_global_count target host root uniformity positive data uniform]
    simp
  | leaf smaller larger face oldEndpoint newVertex size built extension inductionHypothesis =>
    have transfer := global_leaf_count smaller larger host face oldEndpoint newVertex extension
    have sizePositive := built.root_spec.2.2
    have faceLength : face.length = uniformity - 1 := by
      have lengthEq := built.root_spec.2.1
      simp only [List.length_append, List.length_cons, List.length_nil] at lengthEq
      omega
    rw [faceLength] at transfer
    have coefficient : size = (size - 1) + 1 := by omega
    simp only [Nat.add_sub_cancel]
    rw [coefficient, Nat.add_mul, Nat.one_mul]
    omega
  | glue first second joined root firstSize secondSize firstBuilt secondBuilt amalgam firstIH secondIH =>
    have transfer := global_gluing_count first second joined host root amalgam
    have firstPositive := firstBuilt.root_spec.2.2
    have secondPositive := secondBuilt.root_spec.2.2
    have coefficient : firstSize + secondSize - 1 - 1 = (firstSize - 1) + (secondSize - 1) := by omega
    rw [coefficient, Nat.add_mul]
    omega
  | reorder target root otherRoot size built ordering inductionHypothesis =>
    rw [← globalSupportCount_root_perm target host root otherRoot ordering]
    exact inductionHypothesis

theorem uniform_edges_empty_of_too_small (host : FiniteHypergraph Host) (uniformity : Nat)
    (uniform : host.Uniform uniformity) (tooSmall : host.vertices.length < uniformity) : host.edges = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro edge present
  have bound := nodup_length_le_of_subset edge host.vertices (host.edge_nodup edge present)
    (host.edge_vertices edge present)
  have size := uniform edge present
  omega

theorem rootedConstruction_shadow_bound {uniformity size : Nat} {target : FiniteHypergraph Vertex}
    {root : List Vertex} (built : RootedConstruction uniformity target root size)
    (host : FiniteHypergraph Host) (positive : 0 < uniformity) (uniform : host.Uniform uniformity)
    (free : ¬ Nonempty (Embedding target host)) :
    uniformity * host.edges.length ≤ (size - 1) * shadowCount host (uniformity - 1) := by
  by_cases large : uniformity ≤ host.vertices.length
  · have master := rootedConstruction_master built host positive uniform
    rw [globalSupportCount_eq_zero_of_free target host root free, Nat.zero_add,
      edgeStateCount_normalization host uniformity uniform,
      shadowPermutationCount_normalization host (uniformity - 1)] at master
    have rootFactor : factorial uniformity = uniformity * factorial (uniformity - 1) := by
      have restored : uniformity - 1 + 1 = uniformity := by omega
      calc
        factorial uniformity = factorial (uniformity - 1 + 1) := congrArg factorial restored.symm
        _ = uniformity * factorial (uniformity - 1) := by rw [factorial, restored]
    have tailLength : host.vertices.length - (uniformity - 1) = host.vertices.length - uniformity + 1 := by omega
    have scaled : (uniformity * host.edges.length) *
        (factorial (uniformity - 1) * factorial (host.vertices.length - uniformity + 1)) ≤
        ((size - 1) * shadowCount host (uniformity - 1)) *
        (factorial (uniformity - 1) * factorial (host.vertices.length - uniformity + 1)) := by
      simpa only [rootFactor, tailLength, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using master
    exact Nat.le_of_mul_le_mul_right scaled (Nat.mul_pos (factorial_positive _) (factorial_positive _))
  · have empty := uniform_edges_empty_of_too_small host uniformity uniform (by omega)
    simp only [empty, List.length_nil, Nat.mul_zero]
    exact Nat.zero_le _

end Kalai
