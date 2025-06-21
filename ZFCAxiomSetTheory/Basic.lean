import Mathlib.Logic.ExistsUnique -- Import for ExistsUnique (∃!) quantifier
import Init.Classical -- Explicitly import Classical for `ExistsUnique` (∃!) notation.
set_option diagnostics true

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
  inductive_set : ∃ (i : U), mem (Classical.choose empty_set) i ∧ (∀ (x : U), mem x i →
    -- S(x) = x ∪ {x}
    mem (Classical.choose (union (Classical.choose (pairing x (Classical.choose (pairing x x)))))) i)

  -- Axioma de Regularidad: Todo conjunto no vacío tiene un elemento que es
  -- disjunto de él.
  regularity : ∀ (x : U), x ≠ Classical.choose empty_set → ∃ (y : U), mem y x ∧ ∀ (z : U), mem z y → ¬ (mem z x)

  -- Axioma de Reemplazo: Para cada relación funcional P(x, y) (es decir, para cada x, existe a lo sumo un y tal que P(x, y) es verdadera),
  -- y para cada conjunto A, existe un conjunto B tal que y pertenece a B si y solo si existe un x en A tal que P(x, y) es verdadera.
  -- Formalmente: ∀ (P : U → U → Prop), (∀ (x : U), ∃! (y : U), P x y) → ∀ (a : U), ∃ (b : U), ∀ (y : U), mem y b ↔ (∃ (x : U), mem x a ∧ P x y)
  -- Lean 4 tiene `ExistsUnique` (∃!) para esto.
  replacement : ∀ (P : U → U → Prop), (∀ (x : U), ∃! (y : U), P x y) → ∀ (a : U), ∃ (b : U), ∀ (y : U), mem y b ↔ (∃ (x : U), mem x a ∧ P x y)

  -- Axioma de Elección: Para cualquier conjunto de conjuntos no vacíos,
  -- existe una función que elige un elemento de cada conjunto.
  -- Formalmente: Para cada conjunto X de conjuntos no vacíos, existe una función f tal que para cada A ∈ X, f(A) ∈ A.
  choice : ∀ (X : U), (∀ (A : U), mem A X → ∃ (z : U), mem z A) → ∃ (f : U → U), (∀ (A : U), mem A X → mem (f A) A)

-- Provide Membership instance for any ZFC model
instance {U} [inst : ZFC U] : Membership U U := ⟨ZFC.mem⟩

-- Helper definitions for ZFC (optional, but useful for clarity)
namespace ZFC
  variable {U : Type} [inst : ZFC U]

  -- 1. Demostramos que el conjunto vacío es único.
  theorem empty_set_unique : ∃! (e : U), ∀ (x : U), ¬(ZFC.mem x e) := by
    apply ExistsUnique.intro (Classical.choose inst.empty_set)
    · exact Classical.choose_spec inst.empty_set
    · intro y h_y_is_empty
      apply inst.extensionality
      intro z
      constructor
      · intro h_z_in_y
        -- mem z y is always false by the hypothesis that y is empty
        exact False.elim (h_y_is_empty z h_z_in_y)
      · intro h_z_in_empty
        -- mem z (Classical.choose inst.empty_set) is always false
        exact False.elim ((Classical.choose_spec inst.empty_set) z h_z_in_empty)


  -- 2. Definimos 'emptyset' usando la prueba de unicidad.
  noncomputable def emptyset : U := Classical.choose empty_set_unique

  noncomputable def singleton (x : U) : U := Classical.choose (inst.pairing x x)

  noncomputable def pair (x y : U) : U := Classical.choose (inst.pairing x y)

  noncomputable def union_of_two (x y : U) : U := Classical.choose (inst.union (pair x y))
end ZFC

-- 3. Introducimos la notación global para el conjunto vacío.
notation "∅" => ZFC.emptyset
