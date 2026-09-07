import Digraph.SignedBranch
import Digraph.FactorialCounts
import Digraph.FiberCounting

namespace Digraph

universe u
variable {B : Type u}

noncomputable def remaining (D : FiniteDigraph B) (e : B × B) : List B := by
  classical
  exact (D.vertices.erase e.1).erase e.2

theorem arc_frame (D : FiniteDigraph B) (e : B × B) (he : e ∈ D.arcs) :
    (e.1 :: e.2 :: remaining D e).Perm D.vertices := by
  classical
  have endpoints := D.endpoints e.1 e.2 he
  have different : e.2 ≠ e.1 := by
    intro eq
    exact D.loopless e.1 (by simpa only [eq] using (show (e.1, e.2) ∈ D.arcs from he))
  have second : e.2 ∈ D.vertices.erase e.1 :=
    (List.mem_erase_of_ne different).mpr endpoints.2
  exact ((List.perm_cons_erase second).symm.cons e.1).trans
    (List.perm_cons_erase endpoints.1).symm

theorem remaining_nodup (D : FiniteDigraph B) (e : B × B) : (remaining D e).Nodup := by
  classical
  exact (D.vertices_nodup.erase _).erase _

theorem remaining_length (D : FiniteDigraph B) (e : B × B) (he : e ∈ D.arcs) :
    (remaining D e).length + 2 = D.vertices.length := by
  have h := (arc_frame D e he).length_eq
  simp only [List.length_cons] at h
  omega

def arcListing (D : FiniteDigraph B) : ListingFor (fun e => e ∈ D.arcs) :=
  ⟨D.arcs, D.arcs_nodup, fun _ => Iff.rfl⟩

noncomputable def arcCuts (D : FiniteDigraph B) :=
  (arcListing D).fiber (fun e => cutUniverse (remaining D e))

noncomputable def populationEncode (D : FiniteDigraph B) (q : {q // Valid D .plus q}) :
    {p : (B × B) × Cut B // p.1 ∈ D.arcs ∧ p.2.word.Perm (remaining D p.1)} := by
  let e := (q.val.root, q.val.cut.marker)
  let cut : Cut B := ⟨q.val.cut.before, q.val.cut.after⟩
  have moved : (e.1 :: e.2 :: cut.word).Perm D.vertices :=
    (List.perm_middle.symm.cons q.val.root).trans q.property.1
  have compare := moved.trans (arc_frame D e q.property.2).symm
  exact ⟨(e, cut), q.property.2, compare.cons_inv.cons_inv⟩

def populationDecode (D : FiniteDigraph B)
    (p : {p : (B × B) × Cut B // p.1 ∈ D.arcs ∧ p.2.word.Perm (remaining D p.1)}) :
    {q // Valid D .plus q} := by
  let q : State B := ⟨p.val.1.1, ⟨p.val.2.prefix, p.val.1.2, p.val.2.suffix⟩⟩
  refine ⟨q, ?_, p.property.1⟩
  exact (List.perm_middle.cons p.val.1.1).trans
    ((p.property.2.cons p.val.1.2).cons p.val.1.1 |>.trans (arc_frame D p.val.1 p.property.1))

theorem populationDecode_encode (D : FiniteDigraph B) (q : {q // Valid D .plus q}) :
    populationDecode D (populationEncode D q) = q := by
  apply Subtype.ext
  rfl

theorem populationEncode_decode (D : FiniteDigraph B)
    (p : {p : (B × B) × Cut B // p.1 ∈ D.arcs ∧ p.2.word.Perm (remaining D p.1)}) :
    populationEncode D (populationDecode D p) = p := by
  apply Subtype.ext
  rfl

/-- There is exactly one marked state for each arc, ordering of its other vertices,
and insertion cut. No division or positive-density assumption enters this count. -/
theorem population_normalization (D : FiniteDigraph B) (s : Sign) :
    M D s = D.arcs.length * factorial (D.vertices.length - 1) := by
  have plus : M D .plus = D.arcs.length * factorial (D.vertices.length - 1) := by
    have eq := (validListing D .plus).card_eq_of_bijection (arcCuts D)
      (populationEncode D)
      (fun q t h => by
        have h' := congrArg (populationDecode D) h
        simpa only [populationDecode_encode] using h')
      (fun p => ⟨populationDecode D p, populationEncode_decode D p⟩)
    rw [arcCuts, ListingFor.fiber_card] at eq
    have count := sumOn_constant D.arcs
      (fun e => (cutUniverse (remaining D e)).card) (factorial (D.vertices.length - 1)) (by
        intro e he
        change (cutUniverse (remaining D e)).card = _
        rw [cutUniverse_card_factorial _ (remaining_nodup D e)]
        have h := remaining_length D e he
        congr 1
        omega)
    exact eq.trans count
  cases s with
  | plus => exact plus
  | minus => exact (signed_population_eq D .minus).trans plus

theorem order_normalization (D : FiniteDigraph B) : Q D = factorial D.vertices.length :=
  orderingUniverse_card_factorial D.vertices D.vertices_nodup

theorem population_density_cancel (D : FiniteDigraph B) (s : Sign) (k : Nat)
    (bound : M D s ≤ k * Q D) : D.arcs.length ≤ k * D.vertices.length := by
  by_cases empty : D.vertices.length = 0
  · have noArc : D.arcs = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      have present := (D.endpoints e.1 e.2 he).1
      have pos := List.length_pos_of_mem present
      omega
    simp [noArc]
  · have size : D.vertices.length = (D.vertices.length - 1) + 1 := by omega
    rw [population_normalization, order_normalization, size, factorial] at bound
    have bound' : D.arcs.length * factorial (D.vertices.length - 1) ≤
        (k * D.vertices.length) * factorial (D.vertices.length - 1) := by
      simpa only [Nat.add_sub_cancel, ← size, Nat.mul_assoc] using bound
    exact Nat.le_of_mul_le_mul_right bound' (factorial_positive (D.vertices.length - 1))

end Digraph
