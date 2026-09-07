import Kalai.PrefixRotation

namespace Kalai

universe u

variable {Vertex : Type u}

def EnumeratedGluingSource (vertices : List Vertex)
    (firstSupport jointSupport : List Vertex → Prop) :=
  {state : Cut Vertex // state.word.Perm vertices ∧
    firstSupport state.prefix ∧ ¬ jointSupport state.prefix}

def EnumeratedGluingTarget (vertices : List Vertex) (secondSupport : List Vertex → Prop) :=
  {state : Cut Vertex // state.word.Perm vertices ∧ ¬ secondSupport state.prefix}

noncomputable def enumeratedGluingMap (vertices : List Vertex)
    (noDuplicates : vertices.Nodup)
    (firstSupport secondSupport jointSupport : List Vertex → Prop)
    (compatible : GluingCompatible firstSupport secondSupport jointSupport)
    (source : EnumeratedGluingSource vertices firstSupport jointSupport) :
    EnumeratedGluingTarget vertices secondSupport := by
  have wordDistinct : source.val.word.Nodup :=
    source.property.1.nodup_iff.mpr noDuplicates
  have prefixDistinct : source.val.prefix.Nodup :=
    List.Sublist.nodup
      (List.sublist_append_left source.val.prefix source.val.suffix) wordDistinct
  exact ⟨rotate firstSupport source.val,
    (rotate_word_perm firstSupport source.val).trans source.property.1,
    rotate_avoids_second firstSupport secondSupport jointSupport compatible source.val
      prefixDistinct source.property.2.1 source.property.2.2⟩

theorem enumeratedGluingMap_injective (vertices : List Vertex)
    (noDuplicates : vertices.Nodup)
    (firstSupport secondSupport jointSupport : List Vertex → Prop)
    (compatible : GluingCompatible firstSupport secondSupport jointSupport)
    (source target : EnumeratedGluingSource vertices firstSupport jointSupport)
    (sameImage : enumeratedGluingMap vertices noDuplicates firstSupport secondSupport
      jointSupport compatible source = enumeratedGluingMap vertices noDuplicates
        firstSupport secondSupport jointSupport compatible target) : source = target := by
  apply Subtype.ext
  exact rotate_injective_on_support firstSupport source.val target.val
    source.property.2.1 target.property.2.1 (congrArg Subtype.val sameImage)

end Kalai
