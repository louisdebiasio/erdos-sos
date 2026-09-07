import Kalai.GlobalGluing

namespace Kalai

universe u v

variable {Target : Type u} {Host : Type v}

def GlobalSupportedState (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) :=
  {state : List Host × Cut Host // host.HasEdge state.1 ∧
    state.2.word.Perm (host.complement state.1) ∧ OrderedSupport target host root state.1 state.2.prefix}

noncomputable def rootOrderWitness (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) (state : GlobalSupportedState target host root) : Embedding target host :=
  Classical.choose state.property.2.2

theorem rootOrderWitness_spec (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) (state : GlobalSupportedState target host root) :
    root.map (rootOrderWitness target host root state).toFun = state.val.1 ∧
    ∀ vertex ∈ target.vertices, (rootOrderWitness target host root state).toFun vertex ∈
      state.val.1 ++ state.val.2.prefix :=
  Classical.choose_spec state.property.2.2

noncomputable def rootOrderMap (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (firstRoot secondRoot : List Target) (ordering : firstRoot.Perm secondRoot)
    (state : GlobalSupportedState target host firstRoot) : GlobalSupportedState target host secondRoot := by
  let witness := rootOrderWitness target host firstRoot state
  have specification := rootOrderWitness_spec target host firstRoot state
  let image := secondRoot.map witness.toFun
  have imageOrder : image.Perm state.val.1 := by
    rw [← specification.1]
    exact ordering.symm.map witness.toFun
  refine ⟨(image, state.val.2), (host.hasEdge_perm imageOrder).mpr state.property.1, ?_, ?_⟩
  · rw [host.complement_eq_of_perm image state.val.1 imageOrder]
    exact state.property.2.1
  · exact ⟨witness, rfl, fun vertex present =>
      (imageOrder.append_right state.val.2.prefix).mem_iff.mpr (specification.2 vertex present)⟩

theorem rootOrderMap_injective (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (firstRoot secondRoot : List Target) (ordering : firstRoot.Perm secondRoot)
    (first second : GlobalSupportedState target host firstRoot)
    (same : rootOrderMap target host firstRoot secondRoot ordering first =
      rootOrderMap target host firstRoot secondRoot ordering second) : first = second := by
  have sameValues := congrArg Subtype.val same
  have sameImage := congrArg Prod.fst sameValues
  change secondRoot.map (rootOrderWitness target host firstRoot first).toFun =
    secondRoot.map (rootOrderWitness target host firstRoot second).toFun at sameImage
  have firstSpec := rootOrderWitness_spec target host firstRoot first
  have secondSpec := rootOrderWitness_spec target host firstRoot second
  have oldImages : first.val.1 = second.val.1 := by
    rw [← firstSpec.1, ← secondSpec.1]
    apply List.map_inj_left.mpr
    intro vertex present
    exact List.map_inj_left.mp sameImage vertex (ordering.mem_iff.mp present)
  have sameCut := congrArg (fun pair : List Host × Cut Host => pair.2) sameValues
  change first.val.2 = second.val.2 at sameCut
  exact Subtype.ext (Prod.ext oldImages sameCut)

theorem globalSupportCount_root_perm (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (firstRoot secondRoot : List Target) (ordering : firstRoot.Perm secondRoot) :
    globalSupportCount target host firstRoot = globalSupportCount target host secondRoot := by
  apply Nat.le_antisymm
  · exact (globalSupportListing target host firstRoot).card_le_of_injection
      (globalSupportListing target host secondRoot)
      (rootOrderMap target host firstRoot secondRoot ordering)
      (rootOrderMap_injective target host firstRoot secondRoot ordering)
  · exact (globalSupportListing target host secondRoot).card_le_of_injection
      (globalSupportListing target host firstRoot)
      (rootOrderMap target host secondRoot firstRoot ordering.symm)
      (rootOrderMap_injective target host secondRoot firstRoot ordering.symm)

end Kalai
