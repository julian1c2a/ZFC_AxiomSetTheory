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
          ((⟨ y , y ⟩ : U) \ ({{y}} : U) : U) = ((({({y} : U), ({y, y} : U)} : U)  \ ({({y} : U)} : U)) : U) := by rfl
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

    lemma pair_set_eq_singleton (x : U) : ({x, x} : U) = ({x} : U) := by
      apply ExtSet
      intro z
      rw [PairSet_is_specified, Singleton_is_specified, or_self]

    lemma ordered_pair_self_eq_singleton_singleton (x : U) : (⟨x, x⟩ : U) = ({{x}} : U) := by
      unfold OrderedPair
      rw [pair_set_eq_singleton x] -- Simplifica {x, x} a {x}
      rw [pair_set_eq_singleton ({x} : U)] -- Simplifica {{x}, {x}} a {{x}}

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


    -- Demostración de que fst recupera el primer elemento.
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
    theorem snd_of_ordered_pair (x y : U) : snd ⟨x, y⟩ = y := by
      unfold snd
      by_cases h_eq : x = y
      -- Caso 1: x = y
      · rw [h_eq]
        exact snd_of_ordered_pair_eq y y rfl
      -- Caso 2: x ≠ y
      · have h_I : (⋂ (⟨x, y⟩ : U)) = ({x} : U) := intersection_of_ordered_pair x y
        have h_s_ne : ((⟨x, y⟩ \ {h_I}) ≠ ∅) := by
          rw [h_I] -- Ahora el objetivo es (⟨x, y⟩ \ {{x}}) ≠ ∅
          intro h_s_eq_empty
          rw [Difference_empty_iff_subseteq] at h_s_eq_empty
          have h_subset := h_s_eq_empty
          have h_xy_in_pair : ({x, y} : U) ∈ (⟨x, y⟩ : U) := (OrderedPair_is_specified x y {x, y}).mpr (Or.inr rfl)
          have h_xy_in_singleton : ({x, y} : U) ∈ (⟨x, y⟩ : U) := h_subset _ h_xy_in_pair
          have h_xy_eq_I : ({x, y} : U) = h_I := (Singleton_is_specified h_I ({x,y} : U)).mp h_xy_in_singleton
          rw [h_I] at h_xy_eq_I
          have h_y_in_xy : y ∈ ({x, y} : U) := (PairSet_is_specified x y y).mpr (Or.inr rfl)
          rw [h_xy_eq_I] at h_y_in_xy
          have h_y_eq_x := (Singleton_is_specified x y).mp h_y_in_xy
          exact h_eq h_y_eq_x.symm
        rw [dif_neg h_s_ne]
        have h_s_eq : ((⟨x, y⟩ : U) \ ({h_I} : U)) = ({{x, y}} : U) := by
          apply ExtSet; intro z
          rw [Difference_is_specified, OrderedPair_is_specified, Singleton_is_specified]
          constructor
          · intro h;
            cases h.1 with
            | inl h1 => exfalso; exact h.2 h1
            | inr h2 => exact (Singleton_is_specified {x,y} z).mpr h2
          · intro h;
            have h_z_eq_xy := (Singleton_is_specified {x,y} z).mp h;
            constructor
            · exact (OrderedPair_is_specified x y z).mpr (Or.inr h_z_eq_xy)
            · intro h_contra;
              rw [h_z_eq_xy] at h_contra;
              have h_inj : ({x,y} : U) = h_I := h_contra
              rw [h_I] at h_inj
              have h_y_in_x : y ∈ ({x} : U) := by
                rw [←h_inj];
                exact (PairSet_is_specified x y y).mpr (Or.inr rfl)
              have h_y_eq_x := (Singleton_is_specified x y).mp h_y_in_x
              exact h_eq h_y_eq_x.symm
        have h_s_elem : choose ((nonempty_iff_exists_mem _).mp h_s_ne) = ({x, y} : U) := by
          have h_s_is_singleton : ∀ a, a ∈ ({{x, y}} : U) → a = ({x, y} : U) := by
            intro a ha;
            exact (Singleton_is_specified {x, y} a).mp ha
          apply h_s_is_singleton
          rw [h_s_eq];
          exact choose_spec ((nonempty_iff_exists_mem _).mp h_s_ne)
        have h_r : (choose ((nonempty_iff_exists_mem _).mp h_s_ne) \ h_I) = ({y} : U) := by
          rw [h_s_elem, h_I]
          apply ExtSet; intro z
          rw [Difference_is_specified, PairSet_is_specified, Singleton_is_specified]
          constructor
          · intro h;
            have h_z_cases := h.1;
            have h_z_neq_x := h.2;
            cases h_z_cases with
            | inl hz_eq_x =>
              exfalso;
              exact h_z_neq_x hz_eq_x
            | inr hz_eq_y =>
              exact (Singleton_is_specified y z).mpr hz_eq_y
          · intro hz_in_y; have hz_eq_y := (Singleton_is_specified y z).mp hz_in_y; constructor
            · exact (PairSet_is_specified x y z).mpr (Or.inr hz_eq_y)
            · intro h_z_eq_x;
              rw [hz_eq_y] at h_z_eq_x;
              exact h_eq h_z_eq_x.symm
        have h_final : (⋂ ( (choose ((nonempty_iff_exists_mem ((⟨x, y⟩ : U) \ {h_I})).mp h_s_ne)) \ h_I )) = y := by
          rw [h_r, Intersection_of_singleton]
        exact h_final

    -- El teorema principal que une todo.
    @[simp]
    theorem OrderedPairSet_is_WellConstructed (w : U) :
      (isOrderedPair w) → w = (⟨ fst w, snd w ⟩ : U) := by
      unfold isOrderedPair
      intro h_is_op
      obtain ⟨x, y, h_w_eq⟩ := h_is_op
      rw [h_w_eq, fst_of_ordered_pair, snd_of_ordered_pair]

    /-! ### Relaciones y Funciones: Inyectividad, Sobreyectividad, Equivalencia y Orden ### -/

    noncomputable def isRelation (w : U) : Prop :=
      ∀ (z : U), (z ∈ w) ↔ (isOrderedPair z)

    noncomputable def isRelation_in_Sets (A B R : U) : Prop :=
      ∀ (z : U), z ∈ R → ∃ (x y : U), z = ⟨ x , y ⟩ → x ∈ A ∧ y ∈ B

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
)

/-!
  w = ⟨ x, y ⟩ = { { x } , { x , y } }

  fst w = choose (∃ (z : U), z ∈ (⋂ w))
  snd w = choose (∃ (z : U), z ∈ ( ( w \ { ⋂ w } ) \ (⋂ w) ) )

  w = ⟨ x, y ⟩ = { { x } , { x , y } }
  fst w  -- No interfiere si x = y o si x ≠ y
    ⋂ w = { x } ∩ { x, y } = { x }
    ∃! (z: U), z ∈ ⋂ w ↔ z = x
    ∃! (z: U), z ∈ { x } ↔ z = x

  w = { }
  { x } = ∅ !!!
  { x , y } = ∅ !!!

  snd w
    -- caso x ≠ y
    ⋂ w = { x } ∩ { x, y } = { x }
    {⋂ w} ={ { x } }
    s = w \ { ⋂ w } = { { x }, { x  , y } } \ { { x } } =
      = { { x  , y } }
    z = choose ( ∃ (z : U), z ∈ s )
    z == { x , y }
    t = z \ ⋂ w
    t == { x , y } \ { x } == { y }
    snd w = choose ( ∃ (z : U), z ∈ t )
    -- caso x = y
    ⋂ w = { x } ∩ { x, x } = { x }
    {⋂ w} ={ { x } }
    s = w \ { ⋂ w } = { { x }, { x  , x } } \ { { x } } =
      = { { x } } \ { { x } } = ∅
    snd w = s

    -- en general
    -- ⋂ w = { x } ∩ { x, y } = { x }
    -- {⋂ w} ={ { x } }
    -- s = w \ { ⋂ w } = { { x }, { x  , y } } \ { { x } } =
    --   = { { x  , y } }
    let s : U := w \ { (⋂ w) }
    if h: s = ∅ then
      ∅
    else
      let z : U := choose ( ∃ (z : U), z ∈ s )
      -- z == { x , y }
      let t : U := z \ (⋂ w)
      -- t == { x , y } \ { x } == { y }
      choose ( ∃ (z : U), z ∈ t )

    let s : U := w \ { (⋂ w) }
    if h: s = ∅ then
      ∅
    else
      let z : U := choose ( ∃ (z : U), z ∈ s )
      let t : U := z \ (⋂ w)
      choose ( ∃ (z : U), z ∈ t )
-/
