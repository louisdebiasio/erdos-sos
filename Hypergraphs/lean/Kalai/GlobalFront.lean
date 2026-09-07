import Kalai.GlobalMarked

namespace Kalai

universe u v

variable {Target : Type u} {Host : Type v}

theorem ordered_front_support_iff (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (endpoint : Target) (rootEdge : target.HasEdge (face ++ [endpoint]))
    (image : List Host) (size : image.length = face.length) (state : MarkedCut Host) :
    OrderedSupportsAt target host face image endpoint state ↔
      OrderedSupport target host (face ++ [endpoint]) (image ++ [state.marker]) state.before := by
  have prefixOrder : ((image ++ [state.marker]) ++ state.before).Perm (image ++ state.prefixList) := by
    simpa only [MarkedCut.prefixList, List.append_assoc] using
      (List.perm_append_comm (l₁ := [state.marker]) (l₂ := state.before)).append_left image
  constructor
  · rintro ⟨_, embedding, faceEq, endpointEq, contained⟩
    refine ⟨embedding, ?_, fun vertex present => prefixOrder.mem_iff.mpr (contained vertex present)⟩
    simp only [List.map_append, List.map_cons, List.map_nil, faceEq, endpointEq]
  · rintro ⟨embedding, rootEq, contained⟩
    have split : face.map embedding.toFun ++ [embedding.toFun endpoint] = image ++ [state.marker] := by
      simpa only [List.map_append, List.map_cons, List.map_nil] using rootEq
    have lengthEq : (face.map embedding.toFun).length = image.length := by simp only [List.length_map, size]
    refine ⟨?_, embedding, List.append_inj_left split lengthEq,
      (List.cons.inj (List.append_inj_right split lengthEq)).1,
      fun vertex present => prefixOrder.mem_iff.mp (contained vertex present)⟩
    rw [← rootEq]
    exact embedding.map_hasEdge rootEdge

def GlobalMarkedState (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (endpoint : Target) :=
  {state : List Host × MarkedCut Host //
    (state.1.length = face.length ∧ FaceInShadow host state.1) ∧
    state.2.word.Perm (host.complement state.1) ∧ OrderedSupportsAt target host face state.1 endpoint state.2}

noncomputable def globalMarkedToFront (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (endpoint : Target) (rootEdge : target.HasEdge (face ++ [endpoint]))
    (state : GlobalMarkedState target host face endpoint) : GlobalSupportedState target host (face ++ [endpoint]) := by
  let image := state.val.1 ++ [state.val.2.marker]
  let cut : Cut Host := ⟨state.val.2.before, state.val.2.after⟩
  have marked : host.HasEdge image := state.property.2.2.1
  have fullMarked := (state.property.2.1.append_left state.val.1).trans
    (host.root_complement_perm state.val.1 (shadowFace_nodup host _ state.property.1.2)
      (shadowFace_vertices host _ state.property.1.2))
  have fullFront : (image ++ cut.word).Perm host.vertices :=
    (MarkedCut.front_word_perm state.val.1 state.val.2).trans fullMarked
  exact ⟨(image, cut), marked,
    host.tail_perm_complement image cut.word (host.hasEdge_nodup marked)
      (fun _ present => host.hasEdge_vertex marked present) fullFront,
    (ordered_front_support_iff target host face endpoint rootEdge state.val.1 state.property.1.1 state.val.2).mp
      state.property.2.2⟩

theorem globalMarkedToFront_injective (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (endpoint : Target) (rootEdge : target.HasEdge (face ++ [endpoint]))
    (first second : GlobalMarkedState target host face endpoint)
    (same : globalMarkedToFront target host face endpoint rootEdge first =
      globalMarkedToFront target host face endpoint rootEdge second) : first = second := by
  have sameValues := congrArg Subtype.val same
  have sameRoot := congrArg Prod.fst sameValues
  change first.val.1 ++ [first.val.2.marker] = second.val.1 ++ [second.val.2.marker] at sameRoot
  have lengthEq := first.property.1.1.trans second.property.1.1.symm
  have sameFace := List.append_inj_left sameRoot lengthEq
  have sameMarker := (List.cons.inj (List.append_inj_right sameRoot lengthEq)).1
  have sameCut := congrArg Prod.snd sameValues
  change first.val.2.toFront.2 = second.val.2.toFront.2 at sameCut
  have sameFront : first.val.2.toFront = second.val.2.toFront := Prod.ext sameMarker sameCut
  have sameState := congrArg MarkedCut.ofFront sameFront
  change first.val.2 = second.val.2 at sameState
  exact Subtype.ext (Prod.ext sameFace sameState)

theorem globalMarkedToFront_surjective (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (endpoint : Target) (rootEdge : target.HasEdge (face ++ [endpoint]))
    (state : GlobalSupportedState target host (face ++ [endpoint])) :
    ∃ source, globalMarkedToFront target host face endpoint rootEdge source = state := by
  obtain ⟨embedding, prescribed, contained⟩ := state.property.2.2
  let image := face.map embedding.toFun
  let marker := embedding.toFun endpoint
  let marked : MarkedCut Host := ⟨state.val.2.prefix, marker, state.val.2.suffix⟩
  have imageEq : image ++ [marker] = state.val.1 := by
    simpa only [image, marker, List.map_append, List.map_cons, List.map_nil] using prescribed
  have markingEdge : host.HasEdge (image ++ [marker]) := imageEq ▸ state.property.1
  have inShadow : FaceInShadow host image := ⟨marker, markingEdge⟩
  have fullFront : ((image ++ [marker]) ++ state.val.2.word).Perm host.vertices := by
    rw [imageEq]
    exact (state.property.2.1.append_left state.val.1).trans
      (host.root_complement_perm state.val.1 (host.hasEdge_nodup state.property.1)
        (fun _ present => host.hasEdge_vertex state.property.1 present))
  have fullMarked : (image ++ marked.word).Perm host.vertices :=
    (MarkedCut.front_word_perm image marked).symm.trans fullFront
  have ordering := host.tail_perm_complement image marked.word (shadowFace_nodup host image inShadow)
    (shadowFace_vertices host image inShadow) fullMarked
  have size : image.length = face.length := by simp only [image, List.length_map]
  have supported : OrderedSupportsAt target host face image endpoint marked := by
    apply (ordered_front_support_iff target host face endpoint rootEdge image size marked).mpr
    refine ⟨embedding, ?_, ?_⟩
    · simpa only [marked, imageEq] using prescribed
    · simpa only [marked, imageEq] using contained
  refine ⟨⟨(image, marked), ⟨size, inShadow⟩, ordering, supported⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext imageEq rfl

theorem globalMarkedCount_eq_globalSupportCount (target : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (endpoint : Target)
    (rootEdge : target.HasEdge (face ++ [endpoint])) :
    globalMarkedCount target host face endpoint = globalSupportCount target host (face ++ [endpoint]) :=
  (globalMarkedListing target host face endpoint).card_eq_of_bijection
    (globalSupportListing target host (face ++ [endpoint]))
    (globalMarkedToFront target host face endpoint rootEdge)
    (globalMarkedToFront_injective target host face endpoint rootEdge)
    (globalMarkedToFront_surjective target host face endpoint rootEdge)

theorem global_leaf_count (smaller larger : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex) :
    globalSupportCount smaller host (face ++ [oldEndpoint]) ≤
      globalSupportCount larger host (face ++ [newVertex]) + shadowPermutationCount host face.length := by
  have newRoot : larger.HasEdge (face ++ [newVertex]) :=
    (extension.edges_added _).mpr (Or.inr (List.Perm.refl _))
  rw [← globalMarkedCount_eq_globalSupportCount smaller host face oldEndpoint extension.old_root,
    ← globalMarkedCount_eq_globalSupportCount larger host face newVertex newRoot]
  exact global_marked_leaf_count smaller larger host face oldEndpoint newVertex extension

end Kalai
