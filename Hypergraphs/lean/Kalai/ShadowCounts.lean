import Kalai.GlobalFront

namespace Kalai

universe u

variable {Host : Type u}

noncomputable def canonicalFace (host : FiniteHypergraph Host) (face : List Host) : List Host := by
  classical
  exact host.vertices.filter (fun vertex => decide (vertex ∈ face))

theorem canonicalFace_eq_of_perm (host : FiniteHypergraph Host) (first second : List Host)
    (ordering : first.Perm second) : canonicalFace host first = canonicalFace host second := by
  classical
  apply congrArg (fun predicate => host.vertices.filter predicate)
  funext vertex
  simp only [ordering.mem_iff]

theorem canonicalFace_perm (host : FiniteHypergraph Host) (face : List Host)
    (distinct : face.Nodup) (contained : ∀ vertex ∈ face, vertex ∈ host.vertices) :
    (canonicalFace host face).Perm face := by
  classical
  apply perm_of_nodup_membership _ _ (host.vertices_nodup.filter _) distinct
  intro vertex
  simp only [canonicalFace, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun present => present.2, fun present => ⟨contained vertex present, present⟩⟩

theorem faceInShadow_perm (host : FiniteHypergraph Host) (first second : List Host)
    (ordering : first.Perm second) : FaceInShadow host first ↔ FaceInShadow host second := by
  constructor
  · rintro ⟨marker, edge⟩
    exact ⟨marker, (host.hasEdge_perm (ordering.append_right [marker])).mp edge⟩
  · rintro ⟨marker, edge⟩
    exact ⟨marker, (host.hasEdge_perm (ordering.append_right [marker])).mpr edge⟩

def ShadowFace (host : FiniteHypergraph Host) (size : Nat) (face : List Host) : Prop :=
  face.length = size ∧ FaceInShadow host face ∧ canonicalFace host face = face

theorem canonicalFace_shadow (host : FiniteHypergraph Host) (size : Nat) (face : List Host)
    (valid : face.length = size ∧ FaceInShadow host face) : ShadowFace host size (canonicalFace host face) := by
  have ordering := canonicalFace_perm host face (shadowFace_nodup host face valid.2)
    (shadowFace_vertices host face valid.2)
  exact ⟨ordering.length_eq.trans valid.1, (faceInShadow_perm host _ _ ordering).mpr valid.2,
    canonicalFace_eq_of_perm host _ _ ordering⟩

noncomputable def shadowFaceListing (host : FiniteHypergraph Host) (size : Nat) :
    ListingFor (ShadowFace host size) :=
  ListingFor.ofCover ((orderedFaceListing host size).values.map (canonicalFace host)) _ (by
    intro face valid
    exact List.mem_map.mpr ⟨face, ((orderedFaceListing host size).membership face).mpr ⟨valid.1, valid.2.1⟩,
      valid.2.2⟩)

noncomputable def shadowCount (host : FiniteHypergraph Host) (size : Nat) : Nat := (shadowFaceListing host size).card

noncomputable def shadowOrdersListing (host : FiniteHypergraph Host) (size : Nat) :=
  (shadowFaceListing host size).fiber (fun face => orderingUniverse face)

def forgetCanonicalFace (host : FiniteHypergraph Host) (size : Nat)
    (state : {pair : List Host × List Host // ShadowFace host size pair.1 ∧ pair.2.Perm pair.1}) :
    {face : List Host // face.length = size ∧ FaceInShadow host face} :=
  ⟨state.val.2, state.property.2.length_eq.trans state.property.1.1,
    (faceInShadow_perm host _ _ state.property.2).mpr state.property.1.2.1⟩

theorem forgetCanonicalFace_injective (host : FiniteHypergraph Host) (size : Nat)
    (first second : {pair : List Host × List Host // ShadowFace host size pair.1 ∧ pair.2.Perm pair.1})
    (same : forgetCanonicalFace host size first = forgetCanonicalFace host size second) : first = second := by
  have sameOrder := congrArg Subtype.val same
  change first.val.2 = second.val.2 at sameOrder
  have sameCanonical : first.val.1 = second.val.1 := by
    calc
      first.val.1 = canonicalFace host first.val.2 :=
        ((canonicalFace_eq_of_perm host _ _ first.property.2).trans first.property.1.2.2).symm
      _ = canonicalFace host second.val.2 := congrArg (canonicalFace host) sameOrder
      _ = second.val.1 := (canonicalFace_eq_of_perm host _ _ second.property.2).trans second.property.1.2.2
  exact Subtype.ext (Prod.ext sameCanonical sameOrder)

theorem forgetCanonicalFace_surjective (host : FiniteHypergraph Host) (size : Nat)
    (face : {face : List Host // face.length = size ∧ FaceInShadow host face}) :
    ∃ state, forgetCanonicalFace host size state = face := by
  refine ⟨⟨(canonicalFace host face.val, face.val), canonicalFace_shadow host size face.val face.property, ?_⟩, rfl⟩
  exact (canonicalFace_perm host face.val (shadowFace_nodup host face.val face.property.2)
    (shadowFace_vertices host face.val face.property.2)).symm

theorem orderedFaceListing_card (host : FiniteHypergraph Host) (size : Nat) :
    (orderedFaceListing host size).card = shadowCount host size * factorial size := by
  have equalCounts := (shadowOrdersListing host size).card_eq_of_bijection (orderedFaceListing host size)
    (forgetCanonicalFace host size) (forgetCanonicalFace_injective host size) (forgetCanonicalFace_surjective host size)
  rw [← equalCounts]
  unfold shadowOrdersListing
  rw [ListingFor.fiber_card]
  apply sumOn_constant
  intro face present
  have valid := ((shadowFaceListing host size).membership face).mp present
  rw [orderingUniverse_card_factorial face (shadowFace_nodup host face valid.2.1), valid.1]

theorem shadowPermutationCount_normalization (host : FiniteHypergraph Host) (size : Nat) :
    shadowPermutationCount host size = shadowCount host size * factorial size *
      factorial (host.vertices.length - size) := by
  rw [shadowPermutationCount_ordered_normalization, orderedFaceListing_card]

theorem perm_of_nodup_subset_length (first second : List Host) (firstDistinct : first.Nodup)
    (secondDistinct : second.Nodup) (contained : ∀ vertex ∈ first, vertex ∈ second)
    (sameLength : first.length = second.length) : first.Perm second := by
  classical
  apply perm_of_nodup_membership first second firstDistinct secondDistinct
  intro vertex
  refine ⟨contained vertex, ?_⟩
  intro present
  apply Classical.byContradiction
  intro absent
  have bound := nodup_length_le_of_subset (vertex :: first) second
    (List.nodup_cons.mpr ⟨absent, firstDistinct⟩) (by
      intro item inSource
      rcases List.mem_cons.mp inSource with same | inFirst
      · exact same ▸ present
      · exact contained item inFirst)
  simp only [List.length_cons] at bound
  omega

theorem faceInShadow_iff_subset_edge (host : FiniteHypergraph Host) (size : Nat)
    (uniform : host.Uniform (size + 1)) (face : List Host) (distinct : face.Nodup)
    (lengthEq : face.length = size) :
    FaceInShadow host face ↔ ∃ edge, edge ∈ host.edges ∧ ∀ vertex ∈ face, vertex ∈ edge := by
  classical
  constructor
  · rintro ⟨marker, edge, present, ordering⟩
    exact ⟨edge, present, fun vertex inFace => ordering.mem_iff.mpr (List.mem_append_left [marker] inFace)⟩
  · rintro ⟨edge, present, contained⟩
    have edgeLength := uniform edge present
    have existsMarker : ∃ marker, marker ∈ edge ∧ marker ∉ face := by
      apply Classical.byContradiction
      intro absent
      have bound := nodup_length_le_of_subset edge face (host.edge_nodup edge present) (by
        intro vertex inEdge
        apply Classical.byContradiction
        intro notInFace
        exact absent ⟨vertex, inEdge, notInFace⟩)
      omega
    obtain ⟨marker, inEdge, notInFace⟩ := existsMarker
    have combinedDistinct : (face ++ [marker]).Nodup := by
      apply List.pairwise_append.mpr
      refine ⟨distinct, by simp, ?_⟩
      intro first inFace second inSingleton same
      have isMarker := List.mem_singleton.mp inSingleton
      exact notInFace ((same.trans isMarker) ▸ inFace)
    have ordering := perm_of_nodup_subset_length (face ++ [marker]) edge combinedDistinct
      (host.edge_nodup edge present) (by
        intro vertex inCombined
        rcases List.mem_append.mp inCombined with inFace | inSingleton
        · exact contained vertex inFace
        · exact (List.mem_singleton.mp inSingleton) ▸ inEdge)
      (by simp only [List.length_append, List.length_cons, List.length_nil, lengthEq, edgeLength])
    exact ⟨marker, edge, present, ordering.symm⟩

end Kalai
