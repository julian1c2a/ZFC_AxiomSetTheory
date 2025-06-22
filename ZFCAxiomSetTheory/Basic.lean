import Mathlib.Logic.ExistsUnique -- Import for ExistsUnique (∃!) quantifier
import Init.Classical -- Explicitly import Classical for `ExistsUnique` (∃!) notation.
set_option diagnostics true
set_option diagnostics.threshold 1000


  open Classical -- Make `choose` and `choose_spec` available without the `Classical.` prefix.


    -- Define la clase para un modelo de la teoría de conjuntos ZFC.
    -- `U` es el tipo que representa el universo de los conjuntos.
    class ZFC (U : Type) where
      mem : U → U → Prop

      -- Axioma de Extensionalidad: Dos conjuntos son iguales si y solo si
      -- tienen los mismos elementos.
      -- Usamos la igualdad proposicional de Lean (`=`) y le damos su semántica
      -- para conjuntos con este axioma.
      extensionality : ∀ (x y : U), (∀ (z : U), mem z x ↔ mem z y) → x = y

      -- Axioma del Conjunto Vacío (o de Existencia): Existe un conjunto que no tiene elementos.
      empty_set : ∃ (e : U), ∀ (x : U), ¬ (mem x e)

      -- Axioma de Apareamiento: Para cualesquiera dos conjuntos x e y,
      -- existe un conjunto que los contiene a ambos y a nada más.
      pairing : ∀ (x y : U), ∃ (p : U), ∀ (z : U), mem z p ↔ (z = x ∨ z = y)

      -- Axioma de Unión: Para cualquier conjunto x, existe un conjunto que
      -- contiene exactamente los elementos de los elementos de x.
      union : ∀ (x : U), ∃ (u : U), ∀ (z : U), mem z u ↔ (∃ (y : U), mem z y ∧ mem y x)

      -- Axioma de Conjunto Potencia: Para cualquier conjunto x, existe un conjunto
      -- que contiene todos los subconjuntos de x. (z ⊆ x)
      -- La definición correcta es que z está en el conjunto potencia de x si z es un subconjunto de x (z ⊆ x).
      power_set : ∀ (x : U), ∃ (p : U), ∀ (z : U), mem z p ↔ (∀ (y : U), mem y z → mem y x)

      -- Axioma de Existencia de Conjunto Inductivo: Existe un conjunto que contiene
      -- el conjunto vacío y es cerrado bajo la operación de sucesión.
      -- La operación de sucesión de von Neumann es S(x) = x ∪ {x}.
      inductive_set : ∃ (i : U), mem (choose empty_set) i ∧ (∀ (x : U), mem x i →
        -- S(x) = x ∪ {x}
        mem (choose (union (choose (pairing x (choose (pairing x x)))))) i)

      -- Axioma de Regularidad: Todo conjunto no vacío tiene un elemento que es
      -- disjunto de él.
      regularity : ∀ (x : U), (∃ (z : U), mem z x) → ∃ (y : U), mem y x ∧ ∀ (z : U), mem z y → ¬ (mem z x)

      -- Axioma de Reemplazo: Para cada relación funcional P(x, y) (es decir, para cada x, existe a lo sumo un y tal que P(x, y) es verdadera),
      -- y para cada conjunto A, existe un conjunto B tal que y pertenece a B si y solo si existe un x en A tal que P(x, y) es verdadera.
      -- Formalmente: ∀ (P : U → U → Prop), (∀ (x : U), ∃! (y : U), P x y) → ∀ (a : U), ∃ (b : U), ∀ (y : U), mem y b ↔ (∃ (x : U), mem x a ∧ P x y)
      -- Lean 4 tiene `ExistsUnique` (∃!) para esto.
      replacement : ∀ (P : U → U → Prop), (∀ (x : U), ∃! (y : U), P x y) → ∀ (a : U), ∃ (b : U), ∀ (y : U), mem y b ↔ (∃ (x : U), mem x a ∧ P x y)

      -- Axioma de Elección: Para cualquier conjunto de conjuntos no vacíos,
      -- existe una función que elige un elemento de cada conjunto.
      -- Formalmente: Para cada conjunto X de conjuntos no vacíos, existe una función f tal que para cada A ∈ X, f(A) ∈ A.
      choice : ∀ (X : U), (∀ (A : U), mem A X → ∃ (z : U), mem z A) → ∃ (f : U → U), (∀ (A : U), mem A X → mem (f A) A)

namespace ZFC
open Classical
  -- Provide Membership instance for any ZFC model
  instance {U} [inst : ZFC U] : Membership U U := ⟨ZFC.mem⟩

  -- Helper definitions for ZFC (optional, but useful for clarity)

    variable {U : Type} [inst : ZFC U]

    -- 1. Demostramos que el conjunto vacío es único.
    theorem empty_set_unique : ∃! (e : U), ∀ (x : U), ¬(ZFC.mem x e) := by
      apply ExistsUnique.intro (choose inst.empty_set)
      · exact choose_spec inst.empty_set
      · intro y h_y_is_empty
        apply inst.extensionality
        intro z
        constructor
        · intro h_z_in_y
          -- mem z y is always false by the hypothesis that y is empty
          exact False.elim (h_y_is_empty z h_z_in_y)
        · intro h_z_in_e
          -- mem z (choose inst.empty_set) is always false
          exact False.elim ((choose_spec inst.empty_set) z h_z_in_e)
    -- 2. Definimos 'emptyset' usando la prueba de unicidad.
    noncomputable def emptyset : U := choose empty_set_unique
    -- 3. Notación para el conjunto vacío.
    notation "∅" => ZFC.emptyset

    noncomputable def singleton (x : U) : U := choose (inst.pairing x x)

    noncomputable def pair (x y : U) : U := choose (inst.pairing x y)

    noncomputable def succesor (x : U) : U :=
      choose (inst.union (pair x (singleton x)))

    noncomputable def ordered_pair (x y : U) : U :=
      choose (inst.pairing (singleton x) (pair x y))

    noncomputable def union_of_two (x y : U) : U := choose (inst.union (pair x y))

    -- Definition of union over a set (from the union axiom)
    noncomputable def union_set (x : U) : U := choose (inst.union x)

    -- Demostración de que un elemento pertenece a la unión de un conjunto si y solo si pertenece a algún miembro del conjunto.
    -- theorem mem_union_set (x : U) (z : U) : z ∈ union_set x ↔ ∃ (y : U), z ∈ y ∧ y ∈ x := by
    --   -- Desplegamos la definición de 'union_set' para exponer la función 'choose'.
    --   unfold union_set
    --   -- Necesitamos usar `choose_spec` en lugar de la reescritura directa de la hipótesis
    --   let hx := inst.union x
    --   -- La función 'choose_spec' devuelve la propiedad garantizada por el axioma de unión.
    --   let h := choose_spec hx
    --   -- Ahora demostramos la equivalencia dividiéndola en dos implicaciones.
    --   constructor
    --   · intro h_z_in_union_x
    --     -- Usamos 'h' para mostrar que z ∈ (union_set x) implica la existencia de tal 'y'.
    --     exact (h z).mp h_z_in_union_x
    --   · intro h_exists_y
    --     -- Usamos 'h' para mostrar que la existencia de tal 'y' implica z ∈ (union_set x).
    --     exact (h z).mpr h_exists_y

    -- -- Definition of binary intersection
    -- noncomputable def intersection (x y : U) : U :=
    --   choose (inst.extensionality ( ∀(z : U), (∃!(w : U), (z ∈ w ↔ z ∈ x ∧ z ∈ y)) ) (by
    --     intro z
    --     by_cases hz_in_y : z ∈ y
    --     . exists z
    --       constructor
    --       . exact hz_in_y
    --       . intro w hw
    --         exact hw.left
    --     . exists z
    --       constructor
    --       . exact False.elim (hz_in_y (hw.right))
    --       . intro w hw
    --         exact hw.left
    --   ) x)

    -- theorem mem_intersection (x y z : U) : z ∈ intersection x y ↔ (z ∈ x ∧ z ∈ y) := by
    --   apply (choose_spec (inst.replacement (fun (a b : U) => b = a ∧ b ∈ y) _ x) z).trans
    --   constructor
    --   . intro h
    --     cases h with a h_a
    --     cases h_a with h_a_in_x h_a_eq_z_and_in_y
    --     rw [h_a_eq_z_and_in_y.left] at h_a_in_x
    --     rw [h_a_eq_z_and_in_y.left] at h_a_eq_z_and_in_y
    --     exact ⟨h_a_in_x, h_a_eq_z_and_in_y.right⟩
    --   . intro h
    --     use z
    --     exact ⟨h.left, ⟨rfl, h.right⟩⟩

    -- -- Definition of intersection over a set
    -- -- This defines ⋂ x = {z ∈ (union_set x) | ∀ y (y ∈ x → z ∈ y)}
    -- noncomputable def intersection_set (x : U) : U := choose (inst.replacement (fun (z w : U) => w = z ∧ (∀ (y : U), y ∈ x → z ∈ y))
    --   (by
    --     intro z
    --     by_cases hz_all_y : ∀ (y : U), y ∈ x → z ∈ y
    --     . exists z
    --       constructor
    --       . exact hz_all_y
    --       . intro w hw
    --         exact hw.left
    --     . exists z
    --       constructor
    --       . exact False.elim (hz_all_y (hw.right))
    --       . intro w hw
    --         exact hw.left
    --   ) (union_set x)) -- Use union_set x as the domain for replacement

    -- theorem mem_intersection_set (x z : U) : z ∈ intersection_set x ↔ (z ∈ union_set x ∧ (∀ (y : U), y ∈ x → z ∈ y)) := by
    --   apply (choose_spec (inst.replacement (fun (a b : U) => b = a ∧ (∀ (c : U), c ∈ x → a ∈ c)) _ (union_set x)) z).trans
    --   constructor
    --   . intro h
    --     cases h with a h_a
    --     cases h_a with h_a_in_union_x h_a_eq_z_and_all_y
    --     rw [h_a_eq_z_and_all_y.left] at h_a_in_union_x
    --     rw [h_a_eq_z_and_all_y.left] at h_a_eq_z_and_all_y
    --     exact ⟨h_a_in_union_x, h_a_eq_z_and_all_y.right⟩
    --   . intro h
    --     use z
    --     exact ⟨(mem_union_set x z).mpr ⟨z, ⟨rfl, (mem_union_set x z).mp (by assumption)⟩⟩, ⟨rfl, h⟩⟩

    -- -- Definition of binary set difference
    -- noncomputable def set_difference (x y : U) : U :=
    --   choose (inst.replacement (fun (z w : U) => w = z ∧ ¬ (w ∈ y)) (by
    --     intro z
    --     by_cases hz_not_in_y : ¬ (z ∈ y)
    --     . exists z
    --       constructor
    --       . exact hz_not_in_y
    --       . intro w hw
    --         exact hw.left
    --     . exists z
    --       constructor
    --       . exact False.elim (hz_not_in_y (hw.right))
    --       . intro w hw
    --         exact hw.left
    --   ) x)

    -- theorem mem_set_difference (x y z : U) : z ∈ set_difference x y ↔ (z ∈ x ∧ ¬ (z ∈ y)) := by
    --   apply (choose_spec (inst.replacement (fun (a b : U) => b = a ∧ ¬ (b ∈ y)) _ x) z).trans
    --   constructor
    --   . intro h
    --     cases h with a h_a
    --     cases h_a with h_a_in_x h_a_eq_z_and_not_in_y
    --     rw [h_a_eq_z_and_not_in_y.left] at h_a_in_x
    --     rw [h_a_eq_z_and_not_in_y.left] at h_a_eq_z_and_not_in_y
    --     exact ⟨h_a_in_x, h_a_eq_z_and_not_in_y.right⟩
    --   . intro h
    --     use z
    --     exact ⟨h.left, ⟨rfl, h.right⟩⟩
end ZFC
