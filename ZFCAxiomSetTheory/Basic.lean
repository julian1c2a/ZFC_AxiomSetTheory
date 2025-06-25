import Mathlib.Logic.ExistsUnique -- Import for ExistsUnique (∃!) quantifier
import Init.Classical
set_option diagnostics true
set_option diagnostics.threshold 1000


  open Classical


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
      replacement : ∀ (P : U → U → Prop), (∀ (x : U), ∃! (y : U), P x y) → ∀ (a : U), ∃ (b : U), ∀ (y : U), mem y b ↔ (∃ (x : U), mem x a ∧ P x y)

      -- Axioma de Comprehensión desde el Axioma de Reemplazo (x = y)
      -- comprehension : (∀ (x : U), ∃! (y : U), x = y) → ∀ (a : U), ∃ (b : U), ∀ (y : U), mem y b ↔ (∃ (x : U), mem x a ∧ x = y)
      comprehension : ∀ (y : U), ∀ (P : U → Prop), ∃ (x : U), ∀ (α: U),  mem α x ↔ (mem α y ∧ P α)

      -- Axioma de Elección: Para cualquier conjunto de conjuntos no vacíos,
      -- existe una función que elige un elemento de cada conjunto.
      -- Formalmente: Para cada conjunto X de conjuntos no vacíos, existe una función f tal que para cada A ∈ X, f(A) ∈ A.
      choice : ∀ (X : U), (∀ (A : U), mem A X → ∃ (z : U), mem z A) → ∃ (f : U → U), (∀ (A : U), mem A X → mem (f A) A)

namespace ZFC
  open Classical
  -- Provide Membership instance for any ZFC model
  instance {U} [inst : ZFC U] : Membership U U := ⟨ZFC.mem⟩

  -- Helper definitions for ZFC

    variable {U : Type} [inst : ZFC U]

    -- 1. Demostramos que el conjunto vacío es único.
    theorem empty_set_unique : ∃! (e : U), ∀ (x : U), ¬(ZFC.mem x e) := by
      apply ExistsUnique.intro (choose empty_set)
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
          exact False.elim ((choose_spec empty_set) z h_z_in_e)
    -- 2. Definimos 'emptyset' usando la prueba de unicidad.
    noncomputable def emptyset : U := choose empty_set_unique
    -- 3. Notación para el conjunto vacío.
    notation "∅" => emptyset

    noncomputable def singleton (x : U) : U := choose (pairing x x)

    notation "{ " x " }" => singleton x

    noncomputable def pair (x y : U) : U := choose (pairing x y)

    notation "{" x ", " y "}" => pair x y

    noncomputable def succesor (x : U) : U := { x ,  { x } }

    notation " σ " => succesor

    noncomputable def ordered_pair (x y : U) : U := { { x } , { x , y } }

    noncomputable def ordered_pair_eq (x y : U) : Prop :=
      ∀ (z : U), z ∈ ordered_pair x y ↔ ( z = {x} ∨ z = {x, y} )

    noncomputable def is_a_ordered_pair (w : U) : Prop :=
      ∀ (z : U), z ∈ w ↔ ∃ (x y : U), ( z = {x} ∨ z = {x, y} ) ∧
        (∀ (u : U), u ∈ w → ∀ (v : U), (v ∈ z → v ∈ u) ∨ (v ∈ u → v ∈ z))

    notation "⟨" x ", " y "⟩" => ordered_pair x y

    noncomputable def union_of_two (x y : U) : U := choose (union (pair x y))

    notation x " ∪ " y => union_of_two x y

    theorem mem_union_of_two (z x y : U) :
        z ∈ (x ∪ y) ↔ z ∈ x ∨ z ∈ y
            := by sorry
      -- unfold ZFC.union_of_two
      -- apply Iff.intro
      -- -- Prueba para la primera dirección: (z ∈ x ∪ y) → (z ∈ x ∨ z ∈ y)
      -- · intro h_z_in_union_of_two
      --   -- Desplegamos la definición de union_of_two y luego usamos choose_spec para el axioma de unión.
      --   -- `h_z_in_union_of_two` es `z ∈ (choose (union (pair x y)))`.
      --   -- `choose_spec (union (pair x y)) z` nos da `(ZFC.mem z (choose (union (pair x y)))) ↔ (∃ (w : U), ZFC.mem z w ∧ ZFC.mem w (pair x y))`.
      --   -- Aplicando esta equivalencia a `h_z_in_union_of_two` (el lado izquierdo) obtenemos el lado derecho.

      --   -- Usamos el choose_spec directamente para obtener el existencial
      --   have h_exists : ∃ (w : U), ZFC.mem z w ∧ ZFC.mem w (pair x y) :=
      --     (choose_spec (union (pair x y)) z).mp h_z_in_union_of_two

      --   -- Ahora `h_exists` es `∃ (w : U), ZFC.mem z w ∧ ZFC.mem w (pair x y)`.
      --   obtain ⟨w, h_z_in_w_and_w_in_pair⟩ := h_exists
      --   let h_z_in_w := h_z_in_w_and_w_in_pair.left
      --   let h_w_in_pair := h_z_in_w_and_w_in_pair.right
      --     -- `h_w_in_pair` es `ZFC.mem w (pair x y)`.
      --     -- `pair x y` es `choose (pairing x y)`.
      --     -- Así que `h_w_in_pair` es `ZFC.mem w (choose (pairing x y))`.
      --     -- `choose_spec (pairing x y) w` nos da `(ZFC.mem w (choose (pairing x y))) ↔ (w = x ∨ w = y)`.
      --     -- Aplicando esta equivalencia a `h_w_in_pair` obtenemos `w = x ∨ w = y`.
      --     simp only [choose_spec (pairing x y) w] at h_w_in_pair
      --     -- Ahora `h_w_in_pair` es `w = x ∨ w = y`.
      --     cases h_w_in_pair with
      --     | inl h_w_eq_x =>
      --       -- Si `w = x`, entonces `ZFC.mem z w` se convierte en `ZFC.mem z x`.
      --       left
      --       exact h_w_eq_x ▸ h_z_in_w -- Usamos `▸` para sustituir `w` por `x` en `h_z_in_w`.
      --     | inr h_w_eq_y =>
      --       -- Si `w = y`, entonces `ZFC.mem z w` se convierte en `ZFC.mem z y`.
      --       right
      --       exact h_w_eq_y ▸ h_z_in_w
      -- -- Prueba para la segunda dirección: (z ∈ x ∨ z ∈ y) → (z ∈ x ∪ y)
      -- · intro h_z_in_x_or_y
      --   -- El objetivo es `z ∈ (x ∪ y)`, que se despliega a `ZFC.mem z (choose (union (pair x y)))`.
      --   -- Necesitamos mostrar `∃ (w : U), ZFC.mem z w ∧ ZFC.mem w (pair x y)`.
      --   -- Podemos usar `choose_spec (union (pair x y)) z` para reescribir el objetivo.
      --   simp only [choose_spec (union (pair x y)) z]
      --   -- Ahora el objetivo es `∃ (w : U), ZFC.mem z w ∧ ZFC.mem w (pair x y)`.
      --   cases h_z_in_x_or_y with
      --   | inl h_z_in_x =>
      --     -- Si `z ∈ x`, podemos elegir `w = x`.
      --     exists x
      --     constructor
      --     · exact h_z_in_x -- Probamos `z ∈ x`.
      --     · -- Probamos `x ∈ (pair x y)`.
      --       -- `pair x y` es `choose (pairing x y)`.
      --       -- Así que necesitamos probar `ZFC.mem x (choose (pairing x y))`.
      --       -- `choose_spec (pairing x y) x` nos da `(ZFC.mem x (choose (pairing x y))) ↔ (x = x ∨ x = y)`.
      --       -- Podemos reescribir el objetivo usando esto.
      --       simp only [choose_spec (pairing x y) x]
      --       left
      --       rfl -- Probamos `x = x`.
      --   | inr h_z_in_y =>
      --     -- Si `z ∈ y`, podemos elegir `w = y`.
      --     exists y
      --     constructor
      --     · exact h_z_in_y -- Probamos `z ∈ y`.
      --     · -- Probamos `y ∈ (pair x y)`.
      --       -- `pair x y` es `choose (pairing x y)`.
      --       -- Así que necesitamos probar `ZFC.mem y (choose (pairing x y))`.
      --       -- `choose_spec (pairing x y) y` nos da `(ZFC.mem y (choose (pairing x y))) ↔ (y = x ∨ y = y)`.
      --       -- Podemos reescribir el objetivo usando esto.
      --       simp only [choose_spec (pairing x y) y]
      --       right
      --       rfl -- Probamos `y = y`.

    -- Definition of union over a set (from the union axiom)
    noncomputable def union_set (x : U) : U := choose (union x)

    notation "⋃" x => ZFC.union_set x

    -- Demostración de que un elemento pertenece a la unión de un conjunto si y solo si pertenece a algún miembro del conjunto.
    theorem mem_union_set (x z : U) :
      mem z (union_set x) ↔ ∃ y, mem z y ∧ mem y x := by
      unfold union_set
      exact choose_spec (union x) z

    -- Definición de la intersección binaria (x ∩ y)
    -- fun z => mem z y es la propiedad requerida en el axioma de comprehensión,
    --    que para la intersección no es más que la pertenencia a y.
    noncomputable def intersection_of_two (x y : U) : U :=
      choose (comprehension x (fun z => mem z y))

    -- Teorema para la pertenencia a la intersección
    theorem mem_intersection_of_two (x y z : U) : mem z (intersection_of_two x y) ↔ (mem z x ∧ mem z y) := by
      unfold intersection_of_two
      exact (choose_spec (comprehension x (fun w => mem w y))) z

    notation x " ∩ " y => ZFC.intersection_of_two x y

    noncomputable def intersection_set (x : U) : U :=
      choose (comprehension x (fun z => ∀ y, mem y x → mem z y))

    notation "⋂" x => ZFC.intersection_set x

    -- Definición de la diferencia de conjuntos (x \ y)
    noncomputable def set_difference (x y : U) : U :=
      choose (comprehension x (fun z => ¬ mem z y))

    -- Teorema para la pertenencia a la diferencia de conjuntos
    theorem mem_set_difference (x y z : U) : mem z (set_difference x y) ↔ (mem z x ∧ ¬ mem z y) := by
      unfold set_difference
      exact (choose_spec (comprehension x (fun w => ¬ mem w y))) z

    -- Notación para la diferencia de conjuntos
    notation x "⧵" y => ZFC.set_difference x y

    noncomputable def snd_set (p : U) : U :=
      singleton (choose (comprehension p (fun z => z ∈ (⋃ p) ∧ is_a_ordered_pair p)))

    noncomputable def fst_set (p : U) : U :=
      singleton (choose (comprehension p (fun z => z ∈ (⋃ p) ∧ (z ∉ snd_set p) ∧ is_a_ordered_pair p)))

    noncomputable def set_power (x : U) : U :=
      choose (power_set x)

    notation "Π" x => ZFC.set_power x

    -- Teorema para la pertenencia al conjunto potencia
    theorem mem_set_power (x y : U) : mem y (set_power x) ↔ ∀ z, mem z y → mem z x := by
      unfold set_power
      exact (choose_spec (power_set x)) y

    noncomputable def subset (x y : U) : Prop :=
      ∀ (z: U), z ∈ x → z ∈ y

    notation x " ⊆ " y => ZFC.subset x y

    noncomputable def superset (x y : U) : Prop :=
      ∀ (z: U), z ∈ y → z ∈ x

    notation x " ⊇ " y => ZFC.superset x y

    noncomputable def disjoint (x y : U) : Prop :=
      ∀ (z: U), z ∈ x ↔ ¬ (z ∈ y)

    notation x "⟂" y => ZFC.disjoint x y

    noncomputable def cartesian_product (x y : U) : U :=
      choose (comprehension (Π (x ∪ y)) (fun z => ∃ a b, a ∈ x ∧ b ∈ y ∧ z = ⟨a, b⟩ ))

    notation x " × " y => ZFC.cartesian_product x y

    -- Teorema para la pertenencia al producto cartesiano
    -- theorem mem_cartesian_product (x y z : U) := by sorry

    noncomputable def is_relation (R A B : U) : Prop :=
      ∀ (z: U),  z ∈ R → z ∈ A × B

    --notation R " : " A " → " B => ZFC.is_relation R A B

    noncomputable def is_reflexive (R A : U) : Prop :=
      (is_relation R A A) ∧ ∀ (x : U), x ∈ A → ⟨x, x⟩ ∈ R

    noncomputable def is_irreflexive (R A : U) : Prop :=
      (is_relation R A A) ∧ ∀ (x : U), x ∈ A → ⟨x, x⟩ ∉ R

    noncomputable def is_symmetric (R A : U) : Prop :=
      (is_relation R A A) ∧ ∀ (x y : U), x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R

    noncomputable def is_asymmetric (R A : U) : Prop :=
      (is_relation R A A) ∧ ∀ (x y : U), x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∉ R

    noncomputable def is_antisymmetric (R A : U) : Prop :=
      (is_relation R A A) ∧ ∀ (x y : U), x ∈ A → y ∈ A → ⟨x, y⟩ ∈ R → ⟨y, x⟩ ∈ R → x = y

    noncomputable def is_transitive (R A : U) : Prop :=
      (is_relation R A A) ∧ ∀ (x y z : U),
        x ∈ A → y ∈ A → z ∈ A → ⟨x, y⟩ ∈ R → ⟨y, z⟩ ∈ R → ⟨x, z⟩ ∈ R

    noncomputable def is_equivalence (R A : U) : Prop :=
      (is_relation R A A) ∧
        is_reflexive R A ∧ is_symmetric R A ∧ is_transitive R A

    noncomputable def is_a_covering (A b : U) : Prop := (A ⊆ Πb) ∧ (b ⊆ ⋃A)

    noncomputable def is_a_partition (A b : U) : Prop :=
      is_a_covering A b ∧
        (∀ (x y : U), x ∈ A → y ∈ A → x ≠ y → (∀ (z: U), z ∉ x ∩ y))

    notation A " ⊢ " b => is_a_partition A b

    noncomputable def is_strict_order (R A : U) : Prop :=
      (is_relation R A A) ∧
        is_asymmetric R A ∧ is_transitive R A

    noncomputable def is_order (R A : U) : Prop :=
      (is_relation R A A) ∧
        is_reflexive R A ∧ is_antisymmetric R A ∧ is_transitive R A

    noncomputable def is_total_order (R A : U) : Prop :=
      (is_order R A) ∧
        ∀ (x y : U), x ∈ A → y ∈ A → (⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R)

    noncomputable def is_total_strict_order (R A : U) : Prop :=
      (is_strict_order R A) ∧
        ∀ (x y : U), x ∈ A → y ∈ A → x ≠ y → (⟨x, y⟩ ∈ R ∨ ⟨y, x⟩ ∈ R)

    noncomputable def image (R A : U) : U :=
      choose (comprehension R (fun y => ∃ x, x ∈ A ∧ ⟨x, y⟩ ∈ R))

    notation R "''" A => ZFC.image R A

    noncomputable def domain (R : U) : U :=
      choose (comprehension R (fun x => ∃ z, z ∈ R ∧ ( ∃ y, z = ⟨x, y⟩ ) ) )

    notation "dom" R => ZFC.domain R

    noncomputable def restriction (R S : U) : U :=
      choose (comprehension R (fun z => ∃ x y, x ∈ S ∧ z = ⟨x, y⟩ ∧ z ∈ R))

    notation R " ↾ " S => ZFC.restriction R S

    noncomputable def is_function (f A B : U) : Prop :=
      (is_relation f A B) ∧ (∀ (x : U), x ∈ A → ∃! (y : U), y ∈ B ∧ ⟨x, y⟩ ∈ f)

    noncomputable def is_injective (f A B : U) : Prop :=
      (is_function f A B) ∧ ∀ (x1 x2 : U), x1 ∈ A → x2 ∈ A → (⟨x1, f '' A⟩ ∈ f) → (⟨x2, f '' A⟩ ∈ f) → x1 = x2

    noncomputable def is_surjective (f A B : U) : Prop :=
      (is_function f A B) ∧ ∀ (y : U), y ∈ B → ∃ (x : U), x ∈ A ∧ ⟨x, y⟩ ∈ f


end ZFC
