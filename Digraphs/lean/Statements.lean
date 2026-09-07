import Digraph

/- Public statements with conventional graph hypotheses.
Review FiniteDigraph, Embedding, and Antidirected in Digraph/Basic.lean,
UnderlyingConnected in Digraph/GraphStructure.lean, and NoSimpleCycle in
Digraph/SimpleCycles.lean. The structural bridge is proved in TreeBridge.lean. -/
namespace AntidirectedResults

open Digraph

universe u v

theorem density_bound {A : Type u} {B : Type v}
    (T : FiniteDigraph A) (D : FiniteDigraph B)
    (size : 2 ≤ T.vertices.length) (anti : Antidirected T)
    (connected : UnderlyingConnected T) (acyclic : NoSimpleCycle T)
    (free : ¬ Nonempty (Embedding T D)) :
    D.arcs.length ≤ (T.vertices.length - 2) * D.vertices.length :=
  addarioBerry_bound_of_no_simple_cycle T D size anti connected acyclic free

theorem contains_tree {A : Type u} {B : Type v}
    (T : FiniteDigraph A) (D : FiniteDigraph B)
    (size : 2 ≤ T.vertices.length) (anti : Antidirected T)
    (connected : UnderlyingConnected T) (acyclic : NoSimpleCycle T)
    (dense : (T.vertices.length - 2) * D.vertices.length < D.arcs.length) :
    Nonempty (Embedding T D) :=
  addarioBerry_contains_of_no_simple_cycle T D size anti connected acyclic dense

end AntidirectedResults
