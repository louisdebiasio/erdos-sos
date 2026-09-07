import Kalai.OrderedEdges

namespace Kalai

universe u v

variable {Target : Type u} {Host : Type v}

def OrderedSupport (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) (image block : List Host) : Prop :=
  ∃ embedding : Embedding target host, root.map embedding.toFun = image ∧
    ∀ vertex ∈ target.vertices, embedding.toFun vertex ∈ image ++ block

theorem orderedSupport_iff_anchored (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) (image block : List Host) (rootMap : Target → Host)
    (prescribed : root.map rootMap = image) :
    OrderedSupport target host root image block ↔ AnchoredSupport target host root rootMap block := by
  constructor
  · rintro ⟨embedding, agreement, contained⟩
    refine ⟨embedding, List.map_inj_left.mp (agreement.trans prescribed.symm), ?_⟩
    simpa only [prescribed] using contained
  · rintro ⟨embedding, agreement, contained⟩
    exact ⟨embedding, (List.map_inj_left.mpr agreement).trans prescribed,
      by simpa only [prescribed] using contained⟩

theorem orderedSupport_gluing_compatible (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target) (image : List Host)
    (amalgam : EdgeAmalgam first second joined root) :
    GluingCompatible (OrderedSupport first host root image) (OrderedSupport second host root image)
      (OrderedSupport joined host root image) := by
  intro firstBlock secondBlock distinct firstSupported secondSupported
  obtain ⟨embedding, prescribed, contained⟩ := firstSupported
  have firstAnchored := (orderedSupport_iff_anchored first host root image firstBlock
    embedding.toFun prescribed).mp ⟨embedding, prescribed, contained⟩
  have secondAnchored := (orderedSupport_iff_anchored second host root image secondBlock
    embedding.toFun prescribed).mp secondSupported
  exact (orderedSupport_iff_anchored joined host root image (firstBlock ++ secondBlock)
    embedding.toFun prescribed).mpr
    (anchoredSupport_glue first second joined host root embedding.toFun amalgam firstBlock secondBlock
      distinct firstAnchored secondAnchored)

theorem orderedSupport_joined_first (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target) (image block : List Host)
    (amalgam : EdgeAmalgam first second joined root)
    (supported : OrderedSupport joined host root image block) : OrderedSupport first host root image block := by
  obtain ⟨embedding, prescribed, contained⟩ := supported
  exact ⟨embedding.restrict first
    (fun vertex present => (amalgam.vertices_union vertex).mpr (Or.inl present))
    (fun edge present => (amalgam.edges_union edge).mpr (Or.inl present)), prescribed,
    fun vertex present => contained vertex ((amalgam.vertices_union vertex).mpr (Or.inl present))⟩

noncomputable def edgeStateListing (host : FiniteHypergraph Host) :=
  (orderedEdgeListing host).fiber (fun image => cutUniverse (host.complement image))

noncomputable def edgeStateCount (host : FiniteHypergraph Host) : Nat := (edgeStateListing host).card

noncomputable def globalSupportListing (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) :=
  (orderedEdgeListing host).fiber (fun image =>
    cutListing (host.complement image) (OrderedSupport target host root image))

noncomputable def globalSupportCount (target : FiniteHypergraph Target) (host : FiniteHypergraph Host)
    (root : List Target) : Nat := (globalSupportListing target host root).card

theorem edgeStateCount_normalization (host : FiniteHypergraph Host) (uniformity : Nat)
    (uniform : host.Uniform uniformity) :
    edgeStateCount host = host.edges.length * factorial uniformity *
      factorial (host.vertices.length - uniformity + 1) := by
  unfold edgeStateCount edgeStateListing
  rw [ListingFor.fiber_card]
  have constantCount : ∀ image ∈ (orderedEdgeListing host).values,
      (cutUniverse (host.complement image)).card = factorial (host.vertices.length - uniformity + 1) := by
    intro image present
    have edge := ((orderedEdgeListing host).membership image).mp present
    rw [cutUniverse_card_factorial _ (host.complement_nodup image),
      host.complement_length image (host.hasEdge_nodup edge) (fun _ present => host.hasEdge_vertex edge present),
      host.hasEdge_length uniform edge]
  rw [sumOn_constant _ _ _ constantCount]
  change (orderedEdgeListing host).card * _ = _
  rw [orderedEdgeListing_card host uniformity uniform]

theorem global_gluing_count (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target)
    (amalgam : EdgeAmalgam first second joined root) :
    globalSupportCount first host root + globalSupportCount second host root ≤
      edgeStateCount host + globalSupportCount joined host root := by
  have localBound := fun image => gluing_count (host.complement image) (host.complement_nodup image)
    (OrderedSupport first host root image) (OrderedSupport second host root image)
    (OrderedSupport joined host root image)
    (orderedSupport_gluing_compatible first second joined host root image amalgam)
    (fun block => orderedSupport_joined_first first second joined host root image block amalgam)
  have bound := sumOn_mono (orderedEdgeListing host).values
    (fun image => cutCount (host.complement image) (OrderedSupport first host root image) +
      cutCount (host.complement image) (OrderedSupport second host root image))
    (fun image => (cutUniverse (host.complement image)).card +
      cutCount (host.complement image) (OrderedSupport joined host root image))
    (fun image _ => localBound image)
  simpa only [globalSupportCount, globalSupportListing, edgeStateCount, edgeStateListing,
    ListingFor.fiber_card, sumOn_add, cutCount] using bound

theorem globalSupportCount_eq_zero_of_free (target : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target) (free : ¬ Nonempty (Embedding target host)) :
    globalSupportCount target host root = 0 := by
  have empty : (globalSupportListing target host root).values = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro state present
    have supported := ((globalSupportListing target host root).membership state).mp present
    exact free ⟨supported.2.2.choose⟩
  exact congrArg List.length empty

end Kalai
