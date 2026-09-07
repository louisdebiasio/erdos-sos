import Digraph.BranchSupport

namespace Digraph

universe u v
variable {A : Type u} {B : Type v}

def State.asCut (q : State B) : Cut B := ⟨q.cut.prefixList, q.cut.after⟩

@[simp] theorem State.asCut_word (q : State B) : q.asCut.word = q.cut.word := by
  simp [State.asCut, Cut.word, MarkedCut.prefixList, MarkedCut.word, List.append_assoc]

def EndMark (D : FiniteDigraph B) (s : Sign) (x : B) (block : List B) : Prop :=
  ∃ before z, block = before ++ [z] ∧ D.Adj s x z

def MarkedBlock (S : FiniteDigraph A) (D : FiniteDigraph B) (r : A) (s : Sign)
    (x : B) (block : List B) : Prop := EndMark D s x block ∧ Supports S D r x block

theorem endMark_suffix (D : FiniteDigraph B) (s : Sign) (x : B) (a b : List B)
    (mark : EndMark D s x (a ++ b)) (nonempty : b ≠ []) : EndMark D s x b := by
  obtain ⟨before, z, eq, adj⟩ := mark
  rcases List.eq_nil_or_concat b with empty | ⟨rest, last, hb⟩
  · exact False.elim (nonempty empty)
  · have lastEq : last = z := by
      apply List.last_eq_of_concat_eq (l₁ := a ++ rest) (l₂ := before)
      simpa [hb, List.concat_eq_append, List.append_assoc] using eq
    exact ⟨rest, last, by simpa only [List.concat_eq_append] using hb, lastEq ▸ adj⟩

def fromCut (x : B) (c : Cut B) (h : c.prefix ≠ []) : State B :=
  ⟨x, ⟨c.prefix.dropLast, c.prefix.getLast h, c.suffix⟩⟩

@[simp] theorem fromCut_asCut (x : B) (c : Cut B) (h : c.prefix ≠ []) :
    (fromCut x c h).asCut = c := by
  cases c
  simp [fromCut, State.asCut, MarkedCut.prefixList, List.dropLast_concat_getLast]

@[simp] theorem fromCut_prefix (x : B) (c : Cut B) (h : c.prefix ≠ []) :
    (fromCut x c h).cut.prefixList = c.prefix :=
  congrArg Cut.prefix (fromCut_asCut x c h)

@[simp] theorem fromCut_word (x : B) (c : Cut B) (h : c.prefix ≠ []) :
    (fromCut x c h).word = x :: c.word := by
  have eq := congrArg Cut.word (fromCut_asCut x c h)
  simpa only [State.asCut_word, State.word] using congrArg (List.cons x) eq

theorem State.asCut_injective (q t : State B) (root : q.root = t.root)
    (cut : q.asCut = t.asCut) : q = t := by
  apply State.ext q t root
  apply MarkedCut.eq_of_word_index
  · simpa using congrArg Cut.word cut
  · have h := congrArg (fun c : Cut B => c.prefix.length) cut
    simp only [State.asCut, MarkedCut.prefixList, List.length_append, List.length_singleton] at h
    omega

def RootCut (B : Type v) := B × Cut B

noncomputable def encode (q : RootCut B) : Sum (State B) (List B) := by
  classical
  exact if empty : q.2.prefix = [] then Sum.inr (q.1 :: q.2.word)
    else Sum.inl (fromCut q.1 q.2 empty)

def decode : Sum (State B) (List B) → Option (RootCut B)
  | .inl q => some (q.root, q.asCut)
  | .inr [] => none
  | .inr (x :: rest) => some (x, ⟨[], rest⟩)

theorem decode_encode (q : RootCut B) : decode (encode q) = some q := by
  classical
  rcases q with ⟨x, c⟩
  by_cases h : c.prefix = []
  · simp only [encode, dif_pos h, decode, Cut.word, h, List.nil_append]
    cases c with
    | mk a b => change a = [] at h; subst a; rfl
  · simp only [encode, dif_neg h, decode]
    rw [fromCut_asCut]
    rfl

theorem encode_injective (q t : RootCut B) (h : encode q = encode t) : q = t := by
  have eq := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using eq

noncomputable def branchRotate (S : FiniteDigraph A) (D : FiniteDigraph B)
    (r : A) (s : Sign) (q : State B) : RootCut B :=
  (q.root, rotate (MarkedBlock S D r s q.root) q.asCut)

theorem branchRotate_spec (S U T : FiniteDigraph A) (D : FiniteDigraph B)
    (r : A) (s : Sign) (am : RootAmalgam S U T r) (q : State B)
    (good : Good S D r s q) (bad : ¬ Supports T D r q.root q.cut.prefixList) :
    let out := branchRotate S D r s q
    (out.1 :: out.2.word).Perm D.vertices ∧
    ¬ Supports U D r out.1 out.2.prefix ∧
    (out.2.prefix ≠ [] → EndMark D s out.1 out.2.prefix) := by
  let P := MarkedBlock S D r s q.root
  have supported : P q.asCut.prefix := ⟨⟨q.cut.before, q.cut.marker, rfl, good.1.2⟩, good.2⟩
  have tailDistinct : q.cut.word.Nodup :=
    (List.nodup_cons.mp (good.1.1.nodup_iff.mpr D.vertices_nodup)).2
  have preDistinct : q.asCut.prefix.Nodup :=
    List.Sublist.nodup (List.sublist_append_left q.asCut.prefix q.asCut.suffix)
      (by change q.asCut.word.Nodup; simpa using tailDistinct)
  have comp : GluingCompatible P (Supports U D r q.root) (Supports T D r q.root) := by
    intro a b distinct hs hu
    exact supports_glue S U T D r am q.root a b distinct hs.2 hu
  refine ⟨?_, rotate_avoids_second P _ _ comp q.asCut preDistinct supported bad, ?_⟩
  · exact ((rotate_word_perm P q.asCut).cons q.root).trans (by simpa using good.1.1)
  · intro nonempty
    have mark : EndMark D s q.root
        (q.asCut.prefix.take (firstIndex P q.asCut.prefix) ++
          q.asCut.prefix.drop (firstIndex P q.asCut.prefix)) := by
      simpa only [List.take_append_drop] using supported.1
    exact endMark_suffix D s q.root _ _ mark nonempty

def BranchSource (S T : FiniteDigraph A) (D : FiniteDigraph B) (r : A) (s : Sign) :=
  {q // Good S D r s q ∧ ¬ Supports T D r q.root q.cut.prefixList}

def BranchTarget (U : FiniteDigraph A) (D : FiniteDigraph B) (r : A) (s : Sign) :=
  Sum {q // Valid D s q ∧ ¬ Supports U D r q.root q.cut.prefixList}
    {word : List B // word.Perm D.vertices}

noncomputable def branchMap (S U T : FiniteDigraph A) (D : FiniteDigraph B)
    (r : A) (s : Sign) (am : RootAmalgam S U T r) (q : BranchSource S T D r s) :
    BranchTarget U D r s := by
  classical
  let out := branchRotate S D r s q.val
  have spec := branchRotate_spec S U T D r s am q.val q.property.1 q.property.2
  exact if empty : out.2.prefix = [] then
    Sum.inr ⟨out.1 :: out.2.word, spec.1⟩
  else Sum.inl ⟨fromCut out.1 out.2 empty, by
    have mark := spec.2.2 empty
    obtain ⟨before, z, hz, adj⟩ := mark
    have last_aux : ∀ (block : List B) (hn : block ≠ []), block = before ++ [z] →
        block.getLast hn = z := by
      intro block hn h; subst block; exact List.getLast_concat
    have last : out.2.prefix.getLast empty = z := last_aux _ empty hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [fromCut_word] using spec.1
    · change D.Adj s out.1 (out.2.prefix.getLast empty)
      rw [last]; exact adj
    · change ¬ Supports U D r out.1 (fromCut out.1 out.2 empty).cut.prefixList
      rw [fromCut_prefix]; exact spec.2.1⟩

theorem branchMap_encode (S U T : FiniteDigraph A) (D : FiniteDigraph B)
    (r : A) (s : Sign) (am : RootAmalgam S U T r) (q : BranchSource S T D r s) :
    Sum.map Subtype.val Subtype.val (branchMap S U T D r s am q) =
      encode (branchRotate S D r s q.val) := by
  classical
  unfold branchMap encode
  split <;> simp_all

theorem branchMap_injective (S U T : FiniteDigraph A) (D : FiniteDigraph B)
    (r : A) (s : Sign) (am : RootAmalgam S U T r) (q t : BranchSource S T D r s)
    (same : branchMap S U T D r s am q = branchMap S U T D r s am t) : q = t := by
  have enc := congrArg (Sum.map Subtype.val Subtype.val) same
  rw [branchMap_encode, branchMap_encode] at enc
  have eq := encode_injective _ _ enc
  have roots : q.val.root = t.val.root := congrArg Prod.fst eq
  have cuts := congrArg Prod.snd eq
  have qs : MarkedBlock S D r s q.val.root q.val.asCut.prefix :=
    ⟨⟨q.val.cut.before, q.val.cut.marker, rfl, q.property.1.1.2⟩, q.property.1.2⟩
  have ts : MarkedBlock S D r s q.val.root t.val.asCut.prefix := by
    rw [roots]
    exact ⟨⟨t.val.cut.before, t.val.cut.marker, rfl, t.property.1.1.2⟩, t.property.1.2⟩
  have sameCuts := rotate_injective_on_support (MarkedBlock S D r s q.val.root)
    q.val.asCut t.val.asCut qs ts (by simpa only [branchRotate, roots] using cuts)
  exact Subtype.ext (State.asCut_injective q.val t.val roots sameCuts)

theorem signed_branch_count (S U T : FiniteDigraph A) (D : FiniteDigraph B)
    (r : A) (s : Sign) (am : RootAmalgam S U T r) :
    R S D r s + R U D r s ≤ M D s + Q D + R T D r s := by
  let base := validListing D s
  let ps := fun q : State B => Supports S D r q.root q.cut.prefixList
  let pu := fun q : State B => Supports U D r q.root q.cut.prefixList
  let pt := fun q : State B => Supports T D r q.root q.cut.prefixList
  have incl : ∀ q, Valid D s q → pt q → ps q := by
    intro q _ h
    exact supports_restrict S T D r q.root q.cut.prefixList
      (fun a ha => (am.vertices_union a).mpr (Or.inl ha))
      (fun a b h => (am.arcs_union a b).mpr (Or.inl h)) h
  have split := base.restrict_card_split ps pt incl
  have complement := base.restrict_card_complement pu
  have bound := ListingFor.card_le_add_of_injection
    ((goodListing S D r s).restrict (fun q => ¬ pt q))
    (base.restrict (fun q => ¬ pu q)) (orderingUniverse D.vertices)
    (branchMap S U T D r s am) (branchMap_injective S U T D r s am)
  have sameCount : ((goodListing S D r s).restrict (fun q => ¬ pt q)).card =
      (base.restrict (fun q => ps q ∧ ¬ pt q)).card := by
    apply ListingFor.card_eq_of_iff
    intro q; change ((Valid D s q ∧ ps q) ∧ ¬ pt q) ↔ (Valid D s q ∧ ps q ∧ ¬ pt q)
    exact and_assoc
  rw [sameCount] at bound
  change (base.restrict ps).card + (base.restrict pu).card ≤
    base.card + (orderingUniverse D.vertices).card + (base.restrict pt).card
  omega

end Digraph
