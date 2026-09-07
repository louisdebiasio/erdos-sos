import Kalai.FactorialCounts
import Kalai.FiberCounting
import Kalai.VertexComplement

namespace Kalai

universe u

variable {Vertex : Type u}

noncomputable def orderedEdgeListing (host : FiniteHypergraph Vertex) : ListingFor host.HasEdge where
  values := host.edges.flatMap (fun edge => (orderingUniverse edge).values)
  distinct := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro edge _
      exact (orderingUniverse edge).distinct
    · apply host.simple.imp
      intro first second different firstOrder inFirst secondOrder inSecond same
      have firstPerm := ((orderingUniverse first).membership firstOrder).mp inFirst
      have secondPerm := ((orderingUniverse second).membership secondOrder).mp inSecond
      exact different (firstPerm.symm.trans (same ▸ secondPerm))
  membership := by
    intro image
    simp only [List.mem_flatMap, FiniteHypergraph.HasEdge]
    constructor
    · rintro ⟨edge, present, ordered⟩
      exact ⟨edge, present, (((orderingUniverse edge).membership image).mp ordered).symm⟩
    · rintro ⟨edge, present, ordering⟩
      exact ⟨edge, present, ((orderingUniverse edge).membership image).mpr ordering.symm⟩

theorem orderedEdgeListing_card (host : FiniteHypergraph Vertex) (uniformity : Nat)
    (uniform : host.Uniform uniformity) :
    (orderedEdgeListing host).card = host.edges.length * factorial uniformity := by
  have fiberLengths : ∀ edge ∈ host.edges, (orderingUniverse edge).values.length = factorial uniformity := by
    intro edge present
    change (orderingUniverse edge).card = _
    rw [orderingUniverse_card_factorial edge (host.edge_nodup edge present), uniform edge present]
  exact length_flatMap_constant host.edges (fun edge => (orderingUniverse edge).values)
    (factorial uniformity) fiberLengths

end Kalai
