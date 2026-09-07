import Kalai.RootOrderCounts

namespace Kalai

universe u v

variable {Target : Type u} {Host : Type v}

theorem shadowFace_nodup (host : FiniteHypergraph Host) (face : List Host)
    (inShadow : FaceInShadow host face) : face.Nodup := by
  obtain ⟨marker, edge⟩ := inShadow
  exact List.Sublist.nodup (List.sublist_append_left face [marker]) (host.hasEdge_nodup edge)

theorem shadowFace_vertices (host : FiniteHypergraph Host) (face : List Host)
    (inShadow : FaceInShadow host face) : ∀ vertex ∈ face, vertex ∈ host.vertices := by
  obtain ⟨marker, edge⟩ := inShadow
  exact fun _ present => host.hasEdge_vertex edge (List.mem_append_left [marker] present)

noncomputable def orderedFaceListing (host : FiniteHypergraph Host) (size : Nat) :
    ListingFor (fun face : List Host => face.length = size ∧ FaceInShadow host face) :=
  ListingFor.ofCover (wordsOfLength host.vertices size) _ (by
    intro face supported
    rw [← supported.1]
    exact wordsOfLength_complete host.vertices face (shadowFace_vertices host face supported.2))

noncomputable def shadowPermutationListing (host : FiniteHypergraph Host) (faceSize : Nat) :=
  (orderedFaceListing host faceSize).fiber (fun face => orderingUniverse (host.complement face))

noncomputable def shadowPermutationCount (host : FiniteHypergraph Host) (faceSize : Nat) : Nat :=
  (shadowPermutationListing host faceSize).card

theorem shadowPermutationCount_ordered_normalization (host : FiniteHypergraph Host) (faceSize : Nat) :
    shadowPermutationCount host faceSize = (orderedFaceListing host faceSize).card *
      factorial (host.vertices.length - faceSize) := by
  unfold shadowPermutationCount shadowPermutationListing
  rw [ListingFor.fiber_card]
  apply sumOn_constant
  intro face present
  have valid := ((orderedFaceListing host faceSize).membership face).mp present
  rw [orderingUniverse_card_factorial _ (host.complement_nodup face),
    host.complement_length face (shadowFace_nodup host face valid.2)
      (shadowFace_vertices host face valid.2), valid.1]

def OrderedSupportsAt (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (image : List Host) (endpoint : Target) (state : MarkedCut Host) : Prop :=
  host.HasEdge (image ++ [state.marker]) ∧
    ∃ embedding : Embedding target host, face.map embedding.toFun = image ∧
      embedding.toFun endpoint = state.marker ∧
      ∀ vertex ∈ target.vertices, embedding.toFun vertex ∈ image ++ state.prefixList

theorem orderedSupportsAt_iff (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (image : List Host) (endpoint : Target) (rootMap : Target → Host)
    (prescribed : face.map rootMap = image) (state : MarkedCut Host) :
    OrderedSupportsAt target host face image endpoint state ↔ SupportsAt target host face rootMap endpoint state := by
  constructor
  · rintro ⟨marked, embedding, anchored, atEndpoint, contained⟩
    refine ⟨by simpa only [prescribed] using marked, embedding,
      List.map_inj_left.mp (anchored.trans prescribed.symm), atEndpoint, ?_⟩
    simpa only [prescribed] using contained
  · rintro ⟨marked, embedding, anchored, atEndpoint, contained⟩
    exact ⟨by simpa only [prescribed] using marked, embedding,
      (List.map_inj_left.mpr anchored).trans prescribed, atEndpoint,
      by simpa only [prescribed] using contained⟩

noncomputable def globalMarkedListing (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (endpoint : Target) :=
  (orderedFaceListing host face.length).fiber (fun image =>
    markedListing (host.complement image) (OrderedSupportsAt target host face image endpoint))

noncomputable def globalMarkedCount (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (face : List Target) (endpoint : Target) : Nat := (globalMarkedListing target host face endpoint).card

theorem ordered_marked_leaf_count (smaller larger : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (image : List Host) (inShadow : FaceInShadow host image) :
    markedCount (host.complement image) (OrderedSupportsAt smaller host face image oldEndpoint) ≤
      markedCount (host.complement image) (OrderedSupportsAt larger host face image newVertex) +
      (orderingUniverse (host.complement image)).card := by
  classical
  by_cases existsWitness : ∃ state, OrderedSupportsAt smaller host face image oldEndpoint state
  · obtain ⟨state, _, embedding, prescribed, _, _⟩ := existsWitness
    have sourceEquality := (markedListing (host.complement image)
      (OrderedSupportsAt smaller host face image oldEndpoint)).card_eq_of_iff
      (markedListing (host.complement image) (SupportsAt smaller host face embedding.toFun oldEndpoint))
      (fun state => and_congr_right (fun _ =>
        orderedSupportsAt_iff smaller host face image oldEndpoint embedding.toFun prescribed state))
    have targetEquality := (markedListing (host.complement image)
      (OrderedSupportsAt larger host face image newVertex)).card_eq_of_iff
      (markedListing (host.complement image) (SupportsAt larger host face embedding.toFun newVertex))
      (fun state => and_congr_right (fun _ =>
        orderedSupportsAt_iff larger host face image newVertex embedding.toFun prescribed state))
    have frame : FaceFrame host (face.map embedding.toFun) (host.complement image) := ⟨by
      rw [prescribed]
      exact host.root_complement_perm image (shadowFace_nodup host image inShadow)
        (shadowFace_vertices host image inShadow)⟩
    change markedCount _ _ = markedCount _ _ at sourceEquality targetEquality
    rw [sourceEquality, targetEquality]
    exact leaf_transfer_count_orderings smaller larger host face embedding.toFun oldEndpoint newVertex
      extension _ frame
  · rw [markedCount_eq_zero_of_unsupported _ _ (fun state _ supported => existsWitness ⟨state, supported⟩)]
    exact Nat.zero_le _

theorem global_marked_leaf_count (smaller larger : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex) :
    globalMarkedCount smaller host face oldEndpoint ≤ globalMarkedCount larger host face newVertex +
      shadowPermutationCount host face.length := by
  have bound := sumOn_mono (orderedFaceListing host face.length).values
    (fun image => markedCount (host.complement image) (OrderedSupportsAt smaller host face image oldEndpoint))
    (fun image => markedCount (host.complement image) (OrderedSupportsAt larger host face image newVertex) +
      (orderingUniverse (host.complement image)).card)
    (fun image present => ordered_marked_leaf_count smaller larger host face oldEndpoint newVertex extension image
      (((orderedFaceListing host face.length).membership image).mp present).2)
  simpa only [globalMarkedCount, globalMarkedListing, shadowPermutationCount, shadowPermutationListing,
    ListingFor.fiber_card, sumOn_add, markedCount] using bound

end Kalai
