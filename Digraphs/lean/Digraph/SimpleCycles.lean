import Digraph.GraphStructure

namespace Digraph
universe u
variable {A : Type u}

/-- A usual vertex-simple path: successive vertices are adjacent, and a new
endpoint is never a previously visited vertex. The list includes both ends. -/
inductive SimplePath (E : A → A → Prop) : A → A → List A → Prop where
  | refl (a) : SimplePath E a a [a]
  | tail {a b c xs} : SimplePath E a b xs → E b c → c ∉ xs →
      SimplePath E a c (xs ++ [c])

theorem SimplePath.start_mem {E : A → A → Prop} {a b : A} {xs : List A}
    (h : SimplePath E a b xs) : a ∈ xs := by
  induction h with
  | refl => simp
  | tail _ _ _ ih => exact List.mem_append.mpr (Or.inl ih)

theorem SimplePath.end_mem {E : A → A → Prop} {a b : A} {xs : List A}
    (h : SimplePath E a b xs) : b ∈ xs := by
  cases h with
  | refl => simp
  | tail => simp

theorem SimplePath.nodup {E : A → A → Prop} {a b : A} {xs : List A}
    (h : SimplePath E a b xs) : xs.Nodup := by
  induction h with
  | refl => simp
  | @tail b c xs path edge fresh ih =>
    apply List.pairwise_append.mpr
    refine ⟨ih,by simp,?_⟩
    intro x hx y hy eq
    have yc : y = c := by simpa using hy
    exact fresh ((eq.trans yc) ▸ hx)

theorem SimplePath.mono {E F : A → A → Prop} {a b : A} {xs : List A}
    (h : SimplePath E a b xs) (sub : ∀ x y, E x y → F x y) : SimplePath F a b xs := by
  induction h with
  | refl => exact .refl _
  | tail _ edge fresh ih => exact .tail ih (sub _ _ edge) fresh

theorem SimplePath.pathPrefix {E : A → A → Prop} {a b : A} {xs : List A}
    (h : SimplePath E a b xs) {c : A} (hc : c ∈ xs) :
    ∃ ys, SimplePath E a c ys := by
  induction h with
  | refl =>
    have eq : c = a := by simpa using hc
    subst c
    exact ⟨[a],.refl _⟩
  | @tail b d xs path edge fresh ih =>
    rcases List.mem_append.mp hc with old | last
    · exact ih old
    · have eq : c = d := by simpa using last
      subst c
      exact ⟨xs ++ [d],.tail path edge fresh⟩

theorem Reach.simple {E : A → A → Prop} {a b : A} (h : Reach E a b) :
    ∃ xs, SimplePath E a b xs := by
  classical
  induction h with
  | refl => exact ⟨[_],.refl _⟩
  | @tail b c path edge ih =>
    obtain ⟨xs,p⟩ := ih
    by_cases hc : c ∈ xs
    · exact p.pathPrefix hc
    · exact ⟨xs ++ [c],.tail p edge hc⟩

theorem SimplePath.same_ends {E : A → A → Prop} {a : A} {xs : List A}
    (h : SimplePath E a a xs) : xs = [a] := by
  cases h with
  | refl => rfl
  | tail path _ fresh => exact False.elim (fresh path.start_mem)

theorem SimplePath.reach_inside {E : A → A → Prop} {a b : A} {xs : List A}
    (h : SimplePath E a b xs) : Reach (fun x y => E x y ∧ x ∈ xs ∧ y ∈ xs) a b := by
  induction h with
  | refl => exact .refl _
  | @tail b c xs path edge fresh ih =>
    have old : Reach (fun x y => E x y ∧ x ∈ xs ++ [c] ∧ y ∈ xs ++ [c]) a b :=
      ih.mono (fun x y h => ⟨h.1,List.mem_append.mpr (Or.inl h.2.1),
      List.mem_append.mpr (Or.inl h.2.2)⟩)
    exact .tail old ⟨edge,List.mem_append.mpr (Or.inl path.end_mem),by simp⟩

/-- A simple undirected cycle has at least three distinct vertices on a
simple path, followed by the edge closing its two ends. -/
def HasSimpleCycle (G : FiniteDigraph A) : Prop :=
  ∃ a b xs, SimplePath G.UAdj a b xs ∧ 3 ≤ xs.length ∧ G.UAdj b a

def NoSimpleCycle (G : FiniteDigraph A) : Prop := ¬ HasSimpleCycle G

/-- The edge-bypass formulation is exactly the usual no-simple-cycle condition. -/
theorem acyclic_iff_no_simple_cycle (G : FiniteDigraph A) :
    UnderlyingAcyclic G ↔ NoSimpleCycle G := by
  constructor
  · intro acyclic
    rintro ⟨a,b,xs,path,size,closing⟩
    cases path with
    | refl => simp at size
    | @tail z b ys pathPrefix edge fresh =>
      have za : z ≠ a := by
        intro eq
        have same := (eq ▸ pathPrefix).same_ends
        simp [same] at size
      have walk : Reach (WithoutEdge G a b) a z := pathPrefix.reach_inside.mono (by
        intro x y h
        refine ⟨h.1,?_⟩
        rintro (⟨_,yb⟩ | ⟨xb,_⟩)
        · exact fresh (yb ▸ h.2.2)
        · exact fresh (xb ▸ h.2.1))
      have last : WithoutEdge G a b z b := by
        refine ⟨edge,?_⟩
        rintro (⟨eq,_⟩ | ⟨eq,_⟩)
        · exact za eq
        · exact fresh (eq ▸ pathPrefix.end_mem)
      exact acyclic a b (uadj_symm G closing) (.tail walk last)
  · intro no a b edge walk
    obtain ⟨xs,path⟩ := walk.simple
    have size : 3 ≤ xs.length := by
      cases path with
      | refl => exact False.elim (uadj_ne G edge rfl)
      | @tail z b ys pathPrefix last fresh =>
        cases pathPrefix with
        | refl => exact False.elim (last.2 (Or.inl ⟨rfl,rfl⟩))
        | @tail w z zs earlier step new =>
          have pos := List.length_pos_iff_exists_mem.mpr ⟨a,earlier.start_mem⟩
          simp only [List.length_append,List.length_singleton] at *
          omega
    exact no ⟨a,b,xs,path.mono (fun _ _ h => h.1),size,uadj_symm G edge⟩

end Digraph
