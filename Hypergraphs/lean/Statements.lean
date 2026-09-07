import Kalai

/- Public theorem statements. Each is proved by the accompanying library.
Review FiniteHypergraph and Embedding in Kalai/Hypergraph.lean and
IsTightTree in Kalai/TightTree.lean together with these statements. -/
namespace KalaiResults

open Kalai

universe u v

theorem shadow_bound {A : Type u} {B : Type v}
    {T : FiniteHypergraph A} {r : Nat}
    (tree : IsTightTree T r) (H : FiniteHypergraph B)
    (hr : 2 ≤ r) (uniform : H.Uniform r)
    (free : ¬ Nonempty (Embedding T H)) :
    r * H.edges.length ≤ (T.edges.length - 1) * shadowCount H (r - 1) :=
  kalai_shadow_bound tree H hr uniform free

theorem binomial_bound {A : Type u} {B : Type v}
    {T : FiniteHypergraph A} {r : Nat}
    (tree : IsTightTree T r) (H : FiniteHypergraph B)
    (hr : 2 ≤ r) (uniform : H.Uniform r)
    (free : ¬ Nonempty (Embedding T H)) :
    r * H.edges.length ≤
      (T.edges.length - 1) * binomial H.vertices.length (r - 1) :=
  kalai_bound tree H hr uniform free

theorem contains_tree {A : Type u} {B : Type v}
    {T : FiniteHypergraph A} {r : Nat}
    (tree : IsTightTree T r) (H : FiniteHypergraph B)
    (hr : 2 ≤ r) (uniform : H.Uniform r)
    (dense : (T.edges.length - 1) * binomial H.vertices.length (r - 1) <
      r * H.edges.length) : Nonempty (Embedding T H) :=
  kalai_contains_tree tree H hr uniform dense

end KalaiResults
