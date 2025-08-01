import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Basic
import Init.Classical
import ZFCAxiomSetTheory.Extension
import ZFCAxiomSetTheory.Existence
import ZFCAxiomSetTheory.Specification

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  universe u
  variable {U : Type u}

  namespace PairingAxiom

    /-! ### Axioma de Pares (No Ordenados) ### -/
    @[simp]
    axiom Pairing (x y : U) :
      ∃ (z : U), ∀ (w : U), w ∈ z ↔ (w = x ∨ w = y)

    /-! ### Teorema de Existencia Única para el Axioma de Pares ### -/
    @[simp]
    theorem PairingUniqueSet (x y : U) :
    ∃! (z : U), ∀ (w : U), w ∈ z ↔ (w = x ∨ w = y)
      := by
    apply ExistsUnique.intro (choose (Pairing x y))
    · -- Existencia del conjunto especificado por el Axioma de Pares
      exact choose_spec (Pairing x y)
    · -- Unicidad del conjunto especificado por el Axioma de Pares
      intro z hz_pairing
      apply (ExtSet z (choose (Pairing x y)))
      intro w
      constructor
      · -- Dirección ->
        intro hw_in_z
        have h := hz_pairing w
        have h_spec := choose_spec (Pairing x y)
        exact (h_spec w).mpr (h.mp hw_in_z)
      · -- Dirección <-
        intro hw_in_pairing
        have h := choose_spec (Pairing x y)
        have h_w_in_x_or_y : w = x ∨ w = y := (h w).mp hw_in_pairing
        exact (hz_pairing w).mpr h_w_in_x_or_y

    /-! ### Definición del conjunto especificado por el Axioma de Pares ### -/
    @[simp]
    noncomputable def PairSet (x y : U) : U :=
    choose (PairingUniqueSet x y)

    @[simp]
    theorem PairSet_is_specified (x y : U) :
    ∀ (z : U), z ∈ PairSet x y ↔ (z = x ∨ z = y)
      := by
    intro z
    exact (choose_spec (PairingUniqueSet x y)).1 z

    notation " { " x ", " y " } " => PairSet x y

    @[simp]
    noncomputable def Singleton (x : U) : U := ({ x , x } : U)

    @[simp]
    theorem Singleton_is_specified (x z : U) :
      z ∈ Singleton x ↔ (z = x)
        := by
      constructor
      · -- Dirección ->
        intro hz_in_singleton
        have h := (PairSet_is_specified x x z).mp hz_in_singleton
        cases h with
        | inl h_eq => exact h_eq
        | inr h_eq => exact h_eq
      · -- Dirección <-
        intro hz_eq_x
        exact (PairSet_is_specified x x z).mpr (Or.inl hz_eq_x)

    notation " { " x " } " => Singleton x

    /-! ### Definición de ser miembro (∈) de la Intersección de una Familia de Conjuntos ### -/
    @[simp] def
    member_intersection (w v : U) : Prop :=
      ∀ (y : U), ( y ∈ w ) → ( v ∈ y )

    /-! ### Definición del conjunto Intersección de una Familia de Conjuntos ### -/
    @[simp]
    noncomputable def Intersection (w : U) : U :=
    if h : ∃ y, y ∈ w then
      let y₀ := choose h
      SpecSet y₀ (fun v => ∀ y, y ∈ w → v ∈ y)
    else
      ∅ -- convención, debería ser U

    /-! ### Notación estándar de la Intersección de una Familia de Conjuntos ### -/
    notation " ⋂ " w => Intersection w

    @[simp]
    lemma nonempty_iff_exists_mem (w : U) : w ≠ ∅ ↔ ∃ y, y ∈ w := by
      constructor
      · intro h
        apply Classical.byContradiction
        intro h_not_exists
        apply h
        apply ExtSet
        intro y
        constructor
        · intro hy
          exfalso
          apply h_not_exists
          exact ⟨y, hy⟩
        · intro hy
          exfalso
          exact EmptySet_is_empty y hy
      · intro h h_empty
        obtain ⟨y, hy⟩ := h
        rw [h_empty] at hy
        exact EmptySet_is_empty y hy

    /-! ### ⋂{A} = A ### -/
    @[simp]
    theorem Intersection_of_singleton (A : U) : (⋂ { A }) = A := by
      apply ExtSet
      intro z
      constructor
      · intro hz_in_inter
        have h_nonempty : {A} ≠ (∅ : U) := by
          intro h_empty
          have hA : A ∈ ({A} : U) := (Singleton_is_specified A A).mpr rfl
          rw [h_empty] at hA
          exact EmptySet_is_empty A hA
        have h_exists : ∃ y, y ∈ ({A} : U) := (nonempty_iff_exists_mem _).mp h_nonempty
        unfold Intersection at hz_in_inter
        simp only [dif_pos h_exists] at hz_in_inter
        let y₀ := choose h_exists
        have hy₀ : y₀ ∈ ({A} : U) := choose_spec h_exists
        have hy₀_eq_A : y₀ = A := (Singleton_is_specified A y₀).mp hy₀
        rw [SpecSet_is_specified] at hz_in_inter
        let hA : A ∈ ({A} : U) := (Singleton_is_specified A A).mpr rfl
        exact (hz_in_inter.2 A) hA
      · intro hz_in_A
        have h_nonempty : {A} ≠ (∅ : U) := by
          intro h_empty
          have hA : A ∈ ({A} : U) := (Singleton_is_specified A A).mpr rfl
          rw [h_empty] at hA
          exact EmptySet_is_empty A hA
        have h_exists : ∃ y, y ∈ ({A} : U) := (nonempty_iff_exists_mem _).mp h_nonempty
        unfold Intersection
        simp only [dif_pos h_exists]
        rw [SpecSet_is_specified]
        constructor
        · have hy₀ : choose h_exists ∈ ({A} : U) := choose_spec h_exists
          have hy₀_eq_A : choose h_exists = A := (Singleton_is_specified A _).mp hy₀
          rw [hy₀_eq_A]
          exact hz_in_A
        · intro y hy
          have hy_eq_A : y = A := (Singleton_is_specified A y).mp hy
          rw [hy_eq_A]
          exact hz_in_A

    /-! ### Definición del Par Ordenado (x,y) = { { x } , { x , y } } ### -/
    @[simp]
    noncomputable def OrderedPair (x y : U) : U
        := (({ (({ x }): U) , (({ x , y }): U) }): U)

    /-! ### Notación estándar del Par Ordenado (x,y) = { { x } , { x , y } } ### -/
    notation " ⟨ " x " , " y " ⟩ " => OrderedPair x y

    @[simp]
    theorem OrderedPair_is_specified (x y : U) :
    ∀ (z : U), z ∈ OrderedPair x y ↔ (z = ({ x } : U) ∨ z = ({ x , y } : U))
      := by
    intro z
    unfold OrderedPair
    exact PairSet_is_specified {x} {x, y} z

    /-! ### Función que dice (`Prop`) si un conjunto `w` es un par ordenado ### -/
    @[simp]
    def isOrderedPair (w : U) : Prop :=
      ∃ (x y : U), w = (⟨ x , y ⟩  : U)

    @[simp]
    noncomputable def fst (w : U) : U := (⋂ (⋂ w))

    @[simp]
    noncomputable def snd (w : U) : U :=
      let I := ⋂ w
      let s := w \ {I}
      if h : s = ∅ then
        ⋂ I
      else
        have h_exists : ∃ y, y ∈ s := (nonempty_iff_exists_mem s).mp h
        let s_elem := choose h_exists
        let r := s_elem \ I
        ⋂ r

    lemma intersection_of_ordered_pair (x y : U) : (⋂ ⟨x, y⟩) = {x} := by
      apply ExtSet
      intro z
      constructor
      · intro hz_in_inter
        have h_nonempty : ⟨x, y⟩ ≠ (∅ : U) := by
          intro h_empty; have hx : ({x} : U) ∈ (⟨x, y⟩ : U) := (OrderedPair_is_specified x y {x}).mpr (Or.inl rfl);
            rw [h_empty] at hx;
            exact EmptySet_is_empty {x} hx
        have h_exists : ∃ elem, elem ∈ (⟨x, y⟩ : U) := (nonempty_iff_exists_mem _).mp h_nonempty
        unfold Intersection at hz_in_inter
        simp only [dif_pos h_exists] at hz_in_inter
        rw [SpecSet_is_specified] at hz_in_inter
        exact hz_in_inter.2 {x} ((OrderedPair_is_specified x y {x}).mpr (Or.inl rfl))
      · intro hz_in_singleton
        have h_nonempty : ⟨x, y⟩ ≠ (∅ : U) := by
          intro h_empty; have hx : ({x} : U) ∈ (⟨x, y⟩ : U) := (OrderedPair_is_specified x y {x}).mpr (Or.inl rfl);
            rw [h_empty] at hx;
            exact EmptySet_is_empty {x} hx
        have h_exists : ∃ elem, elem ∈ (⟨x, y⟩ : U) := (nonempty_iff_exists_mem _).mp h_nonempty
        unfold Intersection
        simp only [dif_pos h_exists]
        rw [SpecSet_is_specified]
        constructor
        · have hz_eq_x : z = x := (Singleton_is_specified x z).mp hz_in_singleton
          have h_choose_spec := choose_spec h_exists
          have h_choose_cases := (OrderedPair_is_specified x y (choose h_exists)).mp h_choose_spec
          cases h_choose_cases with
          | inl h_choose_eq_singleton => rw [h_choose_eq_singleton]; exact hz_in_singleton
          | inr h_choose_eq_pair => rw [h_choose_eq_pair]; exact (PairSet_is_specified x y z).mpr (Or.inl hz_eq_x)
        · intro w hw_in_pair
          have hw_cases := (OrderedPair_is_specified x y w).mp hw_in_pair
          have hz_eq_x : z = x := (Singleton_is_specified x z).mp hz_in_singleton;
            cases hw_cases with
            | inl hw_eq_singleton => rw [hw_eq_singleton]; exact hz_in_singleton
            | inr hw_eq_pair => rw [hw_eq_pair]; exact (PairSet_is_specified x y z).mpr (Or.inl hz_eq_x)

    /-! ### Lemas auxiliares para las pruebas principales ### -/
    /-! ### Lemas auxiliares para las pruebas principales de fst y snd ### -/

    lemma is_singleton_unique_elem (s a : U) :
      s = {a} → ∀ x, x ∈ s → x = a
        := by
          intro h_s_eq x hx_in_s
          rw [h_s_eq] at hx_in_s
          exact (Singleton_is_specified a x).mp hx_in_s

    lemma pair_set_eq_singleton (x : U) :
      ({x, x} : U) = ({x} : U)
        := by
          apply ExtSet
          intro z
          rw [PairSet_is_specified, Singleton_is_specified, or_self]

    lemma ordered_pair_self_eq_singleton_singleton (x : U) :
      (⟨x, x⟩ : U) = ({{x}} : U)
        := by
          unfold OrderedPair
          rw [pair_set_eq_singleton x] -- Simplifica {x, x} a {x}
          rw [pair_set_eq_singleton ({x} : U)] -- Simplifica {{x}, {x}} a {{x}}

    lemma diff_ordered_pair_neq (x y : U) (h_neq : x ≠ y) :
      ((⟨x, y⟩ : U) \ ({{x}} : U)) = {{x, y}}
        := by
          apply ExtSet
          intro z
          rw [Difference_is_specified,
              OrderedPair_is_specified,
              Singleton_is_specified,
              Singleton_is_specified]
          constructor
          · -- Dirección ->
            intro h_diff
            -- h_diff.1: z = {x} ∨ z = {x, y}
            -- h_diff.2: z ≠ {x}
            cases h_diff.1 with
            | inl hz_eq_singleton_x =>
              -- z = {x}, pero tenemos z ≠ {x} de h_diff.2, una contradicción
              exfalso
              exact h_diff.2 hz_eq_singleton_x
            | inr hz_eq_pair =>
              -- z = {x, y}, que es nuestro objetivo
              exact hz_eq_pair
          · -- Dirección <-
            intro hz_eq_pair
            -- hz_eq_pair: z = {x, y}
            constructor
            · -- Probar z ∈ ⟨x, y⟩
              rw [hz_eq_pair]
              exact Or.inr rfl
            · -- Probar z ≠ {x}
              rw [hz_eq_pair]
              intro h_contra
              -- h_contra: {x, y} = {x}
              have h_y_in_lhs : y ∈ ({x, y} : U)
                := (PairSet_is_specified x y y).mpr (Or.inr rfl)
              rw [h_contra] at h_y_in_lhs -- Ahora tenemos y ∈ {x}
              have h_y_eq_x : y = x := (Singleton_is_specified x y).mp h_y_in_lhs
              -- Esto contradice h_neq
              exact h_neq h_y_eq_x.symm

    lemma diff_pair_singleton (x y : U) (h_neq : x ≠ y) :
      (({x, y} : U) \ ({x} : U)) = ({y} : U) := by
      apply ExtSet
      intro z
      rw [Difference_is_specified, PairSet_is_specified, Singleton_is_specified, Singleton_is_specified]
      constructor
      · -- Dirección ->
        intro h_diff
        -- h_diff is (z = x ∨ z = y) ∧ z ≠ x
        cases h_diff.1 with
        | inl hz_eq_x =>
          -- z = x, pero tenemos z ≠ x de h_diff.2, una contradicción
          exact (h_diff.2 hz_eq_x).elim
        | inr hz_eq_y =>
          -- z = y. El objetivo es z ∈ {y}, que es z = y.
          exact hz_eq_y
      · -- Dirección <-
        intro hz_in_singleton_y -- Hipótesis: z ∈ {y}
        -- Ahora hz_in_singleton_y : z = y
        constructor
        · -- Probar z ∈ {x, y}
          -- El objetivo es z = x ∨ z = y. Ahora z = y.
          exact Or.inr hz_in_singleton_y
        · -- Probar z ∉ {x}
          -- El objetivo es z ≠ x. Ahora z = y y la hipótesis h_neq: x ≠ y.
          intro h_eq
          exact h_neq (h_eq.symm ▸ hz_in_singleton_y)

      lemma auxiliary_idempotence_of_or_in (x y : U) :
        x ∈ y ↔ x ∈ y ∨ x ∈ y
        := by
        constructor
        · intro hx_in_y
          exact Or.inl hx_in_y
        · intro h_or
          cases h_or with
          | inl hx_in_y => exact hx_in_y
          | inr hx_in_y => exact hx_in_y

    lemma auxiliary_idempotence_of_or_eq (x y : U) :
      x = y ↔ x = y ∨ x = y
        := by
      constructor
      · intro hx_eq_y
        exact Or.inl hx_eq_y
      · intro h_or
        cases h_or with
        | inl hx_eq_y => exact hx_eq_y
        | inr hx_eq_y => exact hx_eq_y

    lemma ordered_pair_eq_mem (x y : U) (h_eq : x = y) :
      ∀ (z : U), z ∈ (⟨x, y⟩ : U) → z = ({y} : U)
        := by
      -- Instead of subst, use the membership proof and OrderedPair_is_specified
      -- ⟨ x, y ⟩ = ⟨ y, y ⟩
      -- ⋂ ⟨ x, y ⟩ = ⋂ ⟨ y, y ⟩
      -- ⋂ ⟨ y, y ⟩ = ⋂ {{y},{y,y}}
      -- ⋂ {{y},{y,y}} = ⋂ {{y}}
      -- ⋂ {{y}} = {y}
      have h_I : ((⋂ ( (⟨ y, y ⟩) : U)) : U) = ({ y } : U) := (intersection_of_ordered_pair y y)
      have h_s : ((⟨y, y⟩ : U) \ ({{y}} : U)) = (∅ : U) := by
        calc
          ((⟨ y , y ⟩ : U) \ ({{y}} : U) : U) = ((({({y} : U), ({y, y} : U)} : U) \ ({({y} : U)} : U)) : U) := by rfl
          _ = ((({({y} : U), ({y} : U)} : U)  \ ({({y} : U)} : U)) : U) := by rfl
          _ = ((({({y} : U)} : U)  \ ({({y} : U)} : U)) : U) := by rfl
          _ = (∅ : U) := Difference_self_empty ({({y} : U)} : U)
      intro z hz_in_pair
      rw [h_eq] at hz_in_pair
      have h_1_eq_2 : ({y} : U) = ({y, y} : U) := by
        apply ExtSet;
        intro w;
        rw [PairSet_is_specified, Singleton_is_specified];
        exact (auxiliary_idempotence_of_or_eq w y);
      have hz_in_pair_cases : z = { y } ∨ z = { y, y } := (OrderedPair_is_specified y y z).mp hz_in_pair
      have hz_eq_singleton : z = {y} :=
        match hz_in_pair_cases with
        | Or.inl h => h
        | Or.inr h =>
          -- Use h_1_eq_2 : {y} = {y, y}
          h_1_eq_2.symm ▸ h
      have h_z_eq_sing_y : z = ({y} : U) := by
        apply ExtSet;
        intro w;
        rw [hz_eq_singleton];
      have h_y_in_z : y ∈ z := by
        rw [hz_eq_singleton];
        exact (Singleton_is_specified y y).mpr rfl;
      exact h_z_eq_sing_y

    lemma diff_pair_sing_intersection (x y : U) :
      (x = y) → (((⟨x, y⟩ : U) \ ({(⋂ (⟨x, y⟩ : U))})) = (∅ : U))
        := by
          intro h_eq
          -- Con la hipótesis x = y, el objetivo se simplifica enormemente.
          rw [h_eq]
          -- El objetivo ahora es: (⟨y, y⟩ \ {⋂ ⟨y, y⟩}) = ∅
          -- Simplificamos ⋂ ⟨y, y⟩
          have h_inter : (⋂ (⟨y, y⟩ : U)) = {y} := intersection_of_ordered_pair y y
          rw [h_inter]
          -- El objetivo ahora es: (⟨y, y⟩ \ {{y}}) = ∅
          -- Simplificamos ⟨y, y⟩
          have h_pair_self_eq : (⟨y, y⟩ : U) = {{y}} := ordered_pair_self_eq_singleton_singleton y
          rw [h_pair_self_eq]
          -- El objetivo ahora es: ({{y}} \ {{y}}) = ∅
          -- Esto es cierto por la definición de diferencia de un conjunto consigo mismo.
          exact Difference_self_empty {{y}}

    lemma ordered_pair_neq_mem (x y : U) :
      ∀ (z : U), (z ∈ (⟨x, y⟩ : U)) → (z = ({x, y} : U) ∨ (z = ({x} : U)))
        := by
          intro z hz_in_pair
          rw [OrderedPair_is_specified] at hz_in_pair
          cases hz_in_pair with
          | inl hx_eq_y => exact Or.inr hx_eq_y
          | inr hx_eq_y => exact Or.inl hx_eq_y

    lemma intersection_of_ordered_pair_neq_mem (x y : U) (h_eq : x ≠ y) :
      (((⟨x, y⟩ : U)  \ ({((⋂ (⟨x, y⟩ : U)) : U)} : U)  : U) = ({{x, y}} : U))
        := by
          apply ExtSet
          intro z
          rw [Difference_is_specified, OrderedPair_is_specified, Singleton_is_specified]
          constructor
          · intro h
            have h_inter : (⋂ (⟨x, y⟩ : U)) = {x} := intersection_of_ordered_pair x y
            let h_I := h_inter
            -- Swap the disjunction manually
            have h_z_eq_xy : z = {x, y} ∨ z = {x} :=
              match h.1 with
              | Or.inl h1 => Or.inr h1
              | Or.inr h2 => Or.inl h2
            -- Now, from the conjunction, only z = {x, y} ∧ ¬z = {x} is possible
            cases h_z_eq_xy with
            | inl hz_eq_xy =>
              -- z = {x, y}, and ¬z = {x}
              rw [hz_eq_xy]
              exact (Singleton_is_specified {x, y} {x, y}).mpr rfl
            | inr hz_eq_x =>
              -- z = {x}, but ¬z = {x}, contradiction
              exfalso
              apply h.2
              rw [hz_eq_x, h_I]
          · intro h
            have h_z_eq_xy := (Singleton_is_specified {x, y} z).mp h
            constructor
            · exact Or.inr h_z_eq_xy
            · intro h_contra
              rw [h_z_eq_xy] at h_contra
              have h_inj : ({x, y} : U) = (⋂ (⟨x, y⟩ : U)) := h_contra
              rw [intersection_of_ordered_pair x y] at h_inj
              have h_y_in_x : y ∈ ({x} : U) := by
                rw [←h_inj]
                exact (PairSet_is_specified x y y).mpr (Or.inr rfl)
              have h_y_eq_x := (Singleton_is_specified x y).mp h_y_in_x
              exact h_eq h_y_eq_x.symm

    /-! ### Teoremas principales sobre la corrección de fst y snd ### -/
    -- Demostración de que fst recupera el primer elemento.
    @[simp]
    theorem fst_of_ordered_pair (x y : U) :
      fst (⟨x, y⟩ : U) = x
        := by
      unfold fst
      rw [intersection_of_ordered_pair, Intersection_of_singleton]

    theorem snd_of_ordered_pair_eq (x y : U) (h_eq : x = y) :
      snd ⟨x, y⟩ = y
        := by
      rw [h_eq]
      -- El objetivo es snd ⟨y, y⟩ = y
      unfold snd
      have h_s_is_empty : ((⟨y, y⟩ : U) \ {(⋂ (⟨y, y⟩ : U))}) = (∅ : U)
        := diff_pair_sing_intersection y y rfl
      rw [dif_pos h_s_is_empty]
      rw [intersection_of_ordered_pair, Intersection_of_singleton]

    -- Demostración de que snd recupera el segundo elemento.
    @[simp]
    theorem snd_of_ordered_pair (x y : U) : snd ⟨x, y⟩ = y := by
      unfold snd
      by_cases h_eq : x = y
      -- Caso 1: x = y
      · exact snd_of_ordered_pair_eq x y h_eq
      -- Caso 2: x ≠ y
      · -- El objetivo es (if h : s = ∅ then ... else ...), donde s = ⟨x, y⟩ \ {⋂⟨x, y⟩}
        -- Primero, probamos que la condición del 'if' es falsa.
        have h_s_ne : ((⟨x, y⟩ : U) \ {(⋂ (⟨x, y⟩ : U))}) ≠ (∅ : U) := by
          have h_I : (⋂ (⟨x, y⟩ : U)) = ({x} : U) := intersection_of_ordered_pair x y
          rw [h_I] -- El conjunto es ⟨x, y⟩ \ {{x}}
          have h_s_eq : ((⟨x, y⟩ : U) \ ({{x}} : U)) = ({{x, y}} : U) := diff_ordered_pair_neq x y h_eq
          rw [h_s_eq]
          intro h_contra -- Suponemos {{x, y}} = ∅ para llegar a una contradicción
          have h_mem : ({x, y} : U) ∈ ({{x, y}} : U) := (Singleton_is_specified _ _).mpr rfl
          rw [h_contra] at h_mem
          exact EmptySet_is_empty _ h_mem

        -- Como la condición es falsa, el 'if' se resuelve a la rama 'else'.
        simp only [dif_neg h_s_ne]

        -- El objetivo ahora es: ⋂ (choose (...) \ ⋂ ⟨x, y⟩) = y
        -- Probamos que el 'choose' selecciona el único elemento de s, que es {x, y}.
        have h_s_elem_eq :
          choose ((nonempty_iff_exists_mem ((⟨x, y⟩ : U) \ {(⋂ (⟨x, y⟩ : U))})).mp h_s_ne) = ({x, y} : U)
            := by
          -- Sea 's' el conjunto del que estamos escogiendo.
          let s := (⟨x, y⟩ : U) \ {(⋂ (⟨x, y⟩ : U))}
          -- La propiedad de 'choose' nos dice que el elemento escogido está en 's'.
          have h_mem_of_choose : choose ((nonempty_iff_exists_mem s).mp h_s_ne) ∈ s :=
            choose_spec ((nonempty_iff_exists_mem s).mp h_s_ne)
          -- Ahora, probamos que 's' es en realidad el singleton {{x, y}}.
          have h_s_is_singleton : s = ({{x, y}} : U) := by
            -- Para evitar problemas con la reescritura de 's',
            -- hacemos explícito el objetivo con 'change'.
            change ((⟨x, y⟩ : U) \ {(⋂ (⟨x, y⟩ : U))}) = ({{x, y}} : U)
            -- Reemplazamos la intersección directamente usando el lema.
            rw [intersection_of_ordered_pair x y]
            -- El objetivo ahora es (⟨x, y⟩ \ {{x}}) = {{x, y}}, que es un lema.
            exact diff_ordered_pair_neq x y h_eq
          -- Usamos el lema que dice que si un conjunto es un singleton,
          -- cualquier elemento de ese conjunto es igual al elemento del singleton.
          apply is_singleton_unique_elem s ({x, y} : U) h_s_is_singleton
          -- El elemento que nos interesa es el que 'choose' nos da.
          exact h_mem_of_choose

        -- Reemplazamos el 'choose' en el objetivo.
        rw [h_s_elem_eq]
        -- El objetivo ahora es: ⋂ ({x, y} \ ⋂ ⟨x, y⟩) = y
        have h_I : (⋂ (⟨x, y⟩ : U)) = ({x} : U) := intersection_of_ordered_pair x y
        rw [h_I]
        -- El objetivo ahora es: ⋂ ({x, y} \ {x}) = y
        have h_r_eq : (({x, y} : U) \ ({x} : U)) = ({y} : U) := diff_pair_singleton x y h_eq
        rw [h_r_eq]
        -- El objetivo final es: ⋂ {y} = y, lo cual es cierto.
        exact Intersection_of_singleton y

    -- El teorema principal que une todo.
    @[simp]
    theorem OrderedPairSet_is_WellConstructed (w : U) :
      (isOrderedPair w) → w = (⟨ fst w, snd w ⟩ : U) := by
      unfold isOrderedPair
      intro h_is_op
      obtain ⟨x, y, h_w_eq⟩ := h_is_op
      rw [h_w_eq, fst_of_ordered_pair, snd_of_ordered_pair]

    theorem Eq_of_OrderedPairs_given_projections (a b c d : U) :
      (⟨a, b⟩ : U) = (⟨c, d⟩ : U) → a = c ∧ b = d
        := by
      intro h_eq
      -- Descomponemos el par ordenado y usamos la definición de igualdad de conjuntos.
      have h_a_eq_c : fst (⟨a, b⟩ : U) = fst (⟨c, d⟩ : U) := by
        rw [h_eq]
        -- goal is solved by rw
      have h_b_eq_d : snd (⟨a, b⟩ : U) = snd (⟨c, d⟩ : U) := by
        rw [h_eq]
      -- Ahora, probamos que fst y snd son iguales a los elementos correspondientes.
      constructor
      · rw [fst_of_ordered_pair, fst_of_ordered_pair] at h_a_eq_c
        exact h_a_eq_c
      · rw [snd_of_ordered_pair, snd_of_ordered_pair] at h_b_eq_d
        exact h_b_eq_d

    theorem Eq_OrderedPairs (w v : U) :
      isOrderedPair w → isOrderedPair v → ((fst w = fst v ∧ snd w = snd v) ↔ (w = v))
        := by
          intro h_w_is_op h_v_is_op
          -- Obtenemos los componentes y sustituimos w y v por sus formas de par ordenado
          obtain ⟨x₁, y₁, h_w_eq⟩ := h_w_is_op
          subst h_w_eq -- Reemplaza w con ⟨x₁, y₁⟩ en todo el contexto
          obtain ⟨x₂, y₂, h_v_eq⟩ := h_v_is_op
          subst h_v_eq -- Reemplaza v con ⟨x₂, y₂⟩ en todo el contexto

          -- Ahora el objetivo es mucho más claro:
          -- (fst ⟨x₁, y₁⟩ = fst ⟨x₂, y₂⟩ ∧ snd ⟨x₁, y₁⟩ = snd ⟨x₂, y₂⟩) ↔ ⟨x₁, y₁⟩ = ⟨x₂, y₂⟩

          -- Usamos los teoremas de corrección de fst y snd
          simp only [fst_of_ordered_pair, snd_of_ordered_pair]

          -- El objetivo ahora es (x₁ = x₂ ∧ y₁ = y₂) ↔ ⟨x₁, y₁⟩ = ⟨x₂, y₂⟩
          constructor
          · -- Dirección ->
            intro h_comps_eq
            -- Si los componentes son iguales, los pares son iguales por reescritura
            rw [h_comps_eq.1, h_comps_eq.2]
          · -- Dirección <-
            -- Esto es exactamente el teorema que ya has probado
            apply Eq_of_OrderedPairs_given_projections

    theorem isOrderedPair_equiv_isOrderedPair_concept (w : U) :
      isOrderedPair w ↔ ∃ (x y : U), w = ⟨ x , y ⟩
        := by
          constructor
          · intro h_is_op
            obtain ⟨x, y, h_w_eq⟩ := h_is_op
            exact Exists.intro x (Exists.intro y h_w_eq)
          · intro h_exists
            obtain ⟨x, y, h_w_eq⟩ := h_exists
            exact ⟨x, y, h_w_eq⟩

    theorem isOrderedPair_by_construction (w : U) :
      isOrderedPair w ↔ (w = (⟨ fst w , snd w ⟩ : U))
        := by
          constructor
          · intro h_is_op
            exact OrderedPairSet_is_WellConstructed w h_is_op
          · intro h_w_eq
            -- If w = ⟨fst w, snd w⟩, then w is an ordered pair by definition
            exact ⟨fst w, snd w, h_w_eq⟩

    /-! ### Relaciones y Funciones: Inyectividad, Sobreyectividad, Equivalencia y Orden ### -/

    noncomputable def isRelation (R : U) : Prop :=
      ∀ (z : U), (z ∈ R) ↔ (isOrderedPair z)

    noncomputable def isRelation_in_Set (A B R : U) : Prop :=
      ∀ (z : U), z ∈ R → ∃ (x y : U), z = ⟨ x , y ⟩ ∧ x ∈ A ∧ y ∈ B

    noncomputable def isRelation_in_Sets (A B R : U) : Prop :=
      ∀ (z : U), z ∈ R → ∃ (x y : U), z = ⟨ x , y ⟩ → x ∈ A ∧ y ∈ B

    noncomputable def ReverseOrderedPair (w : U) : U := { snd w , fst w }

    noncomputable def isReverseRelation (R S : U) : Prop :=
      ∀ (w : U), w ∈ R ↔ (ReverseOrderedPair w) ∈ S

    noncomputable def isIdRelation (I : U) : Prop :=
      ∀ (x : U), x ∈ I → fst x = snd x

    noncomputable def isInComposition (R S w : U) : Prop :=
      ∃ (W : U), w ∈ W ↔ ∃ (r : U), r ∈ R → ∃ (s : U), s ∈ S → snd r = fst s ∧ w = ⟨ fst r , snd s ⟩


    noncomputable def domain (R : U) : U :=
      SpecSet (fst R) (fun x => ∃ y, ⟨ x , y ⟩ ∈ R)

    noncomputable def range (R : U) : U :=
      SpecSet (snd R) (fun y => ∃ x, ⟨ x , y ⟩ ∈ R)

    noncomputable def isReflexive (w : U) : Prop :=
      ∃ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ x , x ⟩ ∈ w

    noncomputable def isReflexive_in_Set ( A R : U ) : Prop :=
      ∃ (x : U), x ∈ A → ⟨ x , x ⟩ ∈ R

    noncomputable def isIReflexive (w : U) : Prop :=
      ∀ (x : U), ⟨ x , x ⟩ ∉ w

    noncomputable def isSymmetric (w : U) : Prop :=
      ∀ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ y , x ⟩ ∈ w

    noncomputable def isAsymmetric (w : U) : Prop :=
      ∀ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ y , x ⟩ ∉ w

    noncomputable def isAntiSymmetric (w : U) : Prop :=
      ∀ (x y : U), ⟨ x , y ⟩ ∈ w → ⟨ y , x ⟩ ∈ w → x = y

    noncomputable def isTransitive (w : U) : Prop :=
      ∀ (x y z : U), ⟨ x , y ⟩ ∈ w → ⟨ y , z ⟩ ∈ w → ⟨ x , z ⟩ ∈ w

    noncomputable def isEquivalenceRelation (w : U) : Prop :=
      isReflexive w ∧ isSymmetric w ∧ isTransitive w

    noncomputable def isEquivalenceRelation_in_Set (A R : U) : Prop :=
      isReflexive_in_Set A R ∧ isSymmetric R ∧ isTransitive R

    noncomputable def isPartialOrder (R : U) : Prop :=
      isReflexive R ∧ isAntiSymmetric R ∧ isTransitive R

    noncomputable def isStrictOrder (R : U) : Prop :=
      isAsymmetric R ∧ isTransitive R

    noncomputable def isWellDefined (R : U) : Prop :=
      ∀ (x y₁ y₂ : U), ⟨ x , y₁ ⟩ ∈ R → ⟨ x , y₂ ⟩ ∈ R → y₁ = y₂

    noncomputable def isTotalOrder (R : U) : Prop :=
      isPartialOrder R ∧ ∀ (x y : U), x ≠ y → ⟨ x , y ⟩ ∈ R ∨ ⟨ y , x ⟩ ∈ R

    noncomputable def isWellFounded (R : U) : Prop :=
      ∀ (A : U), A ≠ ∅ → ∃ (x : U), x ∈ A ∧ ∀ (y : U), ⟨ y , x ⟩ ∈ R → y ∉ A

    noncomputable def isFunction (A R : U) : Prop :=
      ∀ (x : U), x ∈ A → ∃ (y₁ : U), ∀ (y₂ : U), ⟨ x , y₁ ⟩ ∈ R → ⟨ x , y₂ ⟩ ∈ R → y₁ = y₂

    noncomputable def isInyective (R : U) : Prop :=
      ∀ (x₁ x₂ : U), ∃ (y : U), ⟨ x₁ , y ⟩ ∈ R → ⟨ x₂ , y ⟩ ∈ R → x₁ = x₂

    noncomputable def isSurjectiveFunction (A B R : U) : Prop :=
      ∀ (y : U), y ∈ B → ∃ (x : U), x ∈ A ∧ ⟨ x , y ⟩ ∈ R

    noncomputable def isBijectiveFunction (A B R : U) : Prop :=
      isFunction A R ∧ isInyective R ∧ isSurjectiveFunction A B R

  end PairingAxiom
end SetUniverse

export SetUniverse.PairingAxiom (
    Pairing
    PairingUniqueSet
    PairSet
    PairSet_is_specified
    Singleton
    Singleton_is_specified
    member_intersection
    Intersection
    OrderedPair
    OrderedPair_is_specified
    isOrderedPair
    fst
    snd
    fst_of_ordered_pair
    snd_of_ordered_pair
    OrderedPairSet_is_WellConstructed
    isRelation
    isRelation_in_Sets
    domain
    range
    isReflexive
    isReflexive_in_Set
    isIReflexive
    isSymmetric
    isAsymmetric
    isAntiSymmetric
    isTransitive
    isEquivalenceRelation
    isEquivalenceRelation_in_Set
    isPartialOrder
    isStrictOrder
    isWellDefined
    isTotalOrder
    isWellFounded
    isFunction
    isInyective
    isSurjectiveFunction
    isBijectiveFunction
    is_singleton_unique_elem
    pair_set_eq_singleton
    ordered_pair_self_eq_singleton_singleton
    diff_ordered_pair_neq
    diff_pair_singleton
    auxiliary_idempotence_of_or_in
    auxiliary_idempotence_of_or_eq
    ordered_pair_eq_mem
    ordered_pair_neq_mem
    intersection_of_ordered_pair_neq_mem
    Eq_of_OrderedPairs_given_projections
    Eq_OrderedPairs
)
