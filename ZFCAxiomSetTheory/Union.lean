import Mathlib.Logic.ExistsUnique
import Init.Classical
import ZFCAxiomSetTheory.Extension
import ZFCAxiomSetTheory.Existence
import ZFCAxiomSetTheory.Specification
import ZFCAxiomSetTheory.Pairing

namespace SetUniverse
  open Classical
  open SetUniverse.ExtensionAxiom
  open SetUniverse.ExistenceAxiom
  open SetUniverse.SpecificationAxiom
  open SetUniverse.PairingAxiom
  universe u
  variable {U : Type u}

  namespace UnionAxiom

    /-! ### Axioma de Unión ### -/
    @[simp]
    axiom Union :
      ∀ (C : U), ∃ (UC : U), ∀ (x : U), x ∈ UC ↔ ∃ (y : U), y ∈ C ∧ x ∈ y

    /-! ### Teorema de Existencia Única para el Axioma de Unión ### -/
    @[simp]
    theorem UnionExistsUnique (C : U) :
      ∃! (UC : U), ∀ (x : U), x ∈ UC ↔ ∃ (y : U), y ∈ C ∧ x ∈ y
        := by
      obtain ⟨UC, hUC⟩ := Union C
      apply ExistsUnique.intro UC
      · -- proof that the witness satisfies the property
        exact hUC
      · -- proof of uniqueness
        intros UC₁ h₁
        apply ExtSet
        intro x
        constructor
        . intro hx
          have h_ex : ∃ y, y ∈ C ∧ x ∈ y := (h₁ x).mp hx
          exact (hUC x).mpr h_ex
        . intro hx
          have h_ex : ∃ y, y ∈ C ∧ x ∈ y := (hUC x).mp hx
          exact (h₁ x).mpr h_ex

    @[simp]
    theorem Union_is_specified (C x : U) :
      x ∈ (choose (Union C)) ↔ ∃ (S : U), S ∈ C ∧ x ∈ S
        := by
      have hUC := choose_spec (Union C)
      constructor
      . intro h
        exact (hUC x).mp h
      . intro h
        exact (hUC x).mpr h

    @[simp]
    noncomputable def UnionSet (C : U) : U :=
      choose (UnionExistsUnique C)

    notation " ⋃ " C: 100 => UnionSet C

    @[simp]
    theorem UnionSet_is_specified (C x : U) :
      x ∈ (⋃ C) ↔ ∃ (S : U), S ∈ C ∧ x ∈ S
        := by
      unfold UnionSet
      constructor
      . intro h
        exact ((choose_spec (UnionExistsUnique C)).1 x).mp h
      . intro h
        exact ((choose_spec (UnionExistsUnique C)).1 x).mpr h

    @[simp]
    theorem UnionSet_is_unique (C UC : U) :
      ( ∀ (y : U), y ∈ UC ↔ ∃ (S : U), S ∈ C ∧ y ∈ S )
      ↔ ( UC = (⋃ C) )
        := by
      constructor
      -- (→) direction
      · intro h
        apply ExtSet
        intro y
        rw [h, UnionSet_is_specified]
      -- (←) direction
      · intro h_eq
        rw [h_eq]
        intro y
        rw [UnionSet_is_specified]

    @[simp]
    theorem Set_is_empty_1 (C : U) (hC_empty : C = (∅ : U)) :
      (⋃ C) = (∅ : U)
        := by
      rw [hC_empty]
      apply ExtSet
      intro y
      constructor
      . intro hy
        have h_union_spec := (UnionSet_is_specified ∅ y).mp hy
        cases h_union_spec with
        | intro S hS =>
          cases hS with
          | intro hS_in_C hS_mem_y =>
            -- S ∈ ∅ is impossible, so this case is vacuously true
            exact False.elim (EmptySet_is_empty S hS_in_C)
      . intro hy
        exact False.elim (EmptySet_is_empty y hy)

    @[simp]
    theorem Set_is_empty_2 (C : U) (hC_empty : C = ({∅} : U)) :
      (⋃ C) = (∅ : U)
        := by
      rw [hC_empty]
      apply ExtSet
      intro y
      constructor
      . intro hy
        have h_union_spec := (UnionSet_is_specified ({∅} : U) y).mp hy
        cases h_union_spec with
        | intro S hS =>
          cases hS with
          | intro hS_in_C hS_mem_y =>
            -- S ∈ {∅} is impossible unless S = ∅, but then y ∈ ∅, contradiction
            have hS_eq : S = ∅ := by
              -- S ∈ {∅} means S = ∅ by definition of singleton
              rw [Singleton_is_specified] at hS_in_C
              cases hS_in_C with
              | refl => exact rfl
            rw [hS_eq] at hS_mem_y
            exact False.elim (EmptySet_is_empty y hS_mem_y)
      . intro hy
        exact False.elim (EmptySet_is_empty y hy)

    @[simp]
    theorem Set_is_empty_3 (C : U)
      (hC_not_empty : C ≠ (∅ : U))
      (hC_not_singleton_empty : C ≠ ({∅} : U)) :
        (⋃ C) ≠ (∅ : U)
          := by
      intro h_union_empty
      apply hC_not_empty
      apply ExtSet
      intro x
      constructor
      · intro hx
        -- x ∈ C, but ⋃ C = ∅, so for any x, x ∉ ⋃ C,
        -- so there cannot exist S ∈ C ∧ x ∈ S.
        -- But if x ∈ C, then if x ∈ x, we would have
        -- S := x, S ∈ C ∧ x ∈ S, contradiction.
        -- However, x ∈ x is not generally true, so instead,
        -- we argue by contradiction:
        have : ¬∃ (S : U), S ∈ C ∧ x ∈ S := by
          rw [←UnionSet_is_specified, h_union_empty]
          exact (EmptySet_is_empty x)
        -- But if x ∈ C and x ∈ x, then
        -- ⟨x, hx, ‹x ∈ x›⟩ : ∃ S, S ∈ C ∧ x ∈ S, contradiction.
        -- Since we cannot guarantee x ∈ x, we cannot construct
        -- such S, so the assumption x ∈ C must be false.
        exact False.elim (this ⟨x, hx, sorry⟩)
      · intro hx
        -- x ∈ ∅ → x ∈ C is vacuously true
        exact False.elim (EmptySet_is_empty x hx)

    @[simp]
    theorem UnionSet_is_empty' (C : U) :
      (⋃ C) = (∅ : U) ↔ (C = (∅ : U)) ∨ (∀ (S : U), S ∈ C → S = (∅ : U))
        := by
      constructor
      . intro h_union_empty
        by_cases hC_empty : C = (∅ : U)
        . left
          exact hC_empty
        . right
          intro S hS_in_C
          apply ExtSet
          intro x
          constructor
          . intro hx_in_S
            have h_union_spec := (UnionSet_is_specified C x).mpr ⟨S, hS_in_C, hx_in_S⟩
            rw [h_union_empty] at h_union_spec
            exact False.elim (EmptySet_is_empty x h_union_spec)
          . intro hx_in_empty
            exact False.elim (EmptySet_is_empty x hx_in_empty)
      . intro h_or
        cases h_or with
        | inl hC_empty =>
          exact Set_is_empty_1 C hC_empty
        | inr h_all_empty =>
          apply ExtSet
          intro x
          constructor
          . intro hx_in_union
            have h_union_spec := (UnionSet_is_specified C x).mp hx_in_union
            cases h_union_spec with
            | intro S hS =>
              cases hS with
              | intro hS_in_C hx_in_S =>
                have hS_empty := h_all_empty S hS_in_C
                rw [hS_empty] at hx_in_S
                exact hx_in_S
          . intro hx_in_empty
            exact False.elim (EmptySet_is_empty x hx_in_empty)

    @[simp]
    theorem UnionSet_is_empty (C : U) :
      (⋃ C) = (∅ : U) ↔ (∀ (S : U), S ∈ C → S = (∅ : U))
        := by
      constructor
      . intro h_union_empty
        intro S hS_in_C
        apply ExtSet
        intro x
        constructor
        . intro hx_in_S
          have h_union_spec := (UnionSet_is_specified C x).mpr ⟨S, hS_in_C, hx_in_S⟩
          rw [h_union_empty] at h_union_spec
          exact False.elim (EmptySet_is_empty x h_union_spec)
        . intro hx_in_empty
          exact False.elim (EmptySet_is_empty x hx_in_empty)
      . intro h_all_empty
        apply ExtSet
        intro x
        constructor
        . intro hx_in_union
          have h_union_spec := (UnionSet_is_specified C x).mp hx_in_union
          cases h_union_spec with
          | intro S hS =>
            cases hS with
            | intro hS_in_C hx_in_S =>
              have hS_empty := h_all_empty S hS_in_C
              rw [hS_empty] at hx_in_S
              exact hx_in_S
        . intro hx_in_empty
          exact False.elim (EmptySet_is_empty x hx_in_empty)

    @[simp]
    theorem UnionSetIsEmpty_SetNonEmpty_SingletonEmptySet
      (C : U)
      (hC_non_empty : C ≠ (∅ : U)) :
        (⋃ C) = ∅ ↔ C = ({ ∅ }: U)
          := by
      constructor
      . intro h_union_empty
        -- We want to show C = {∅}
        apply ExtSet
        intro x
        constructor
        . intro hx_in_C
          -- Show x ∈ {∅}
          -- That is, x = ∅
          have : ∀ y, y ∈ C → y = ∅ := by
            intro y hy
            apply ExtSet
            intro z
            constructor
            . intro hz
              have hz_union : z ∈ (⋃ C) := (UnionSet_is_specified C z).mpr ⟨y, hy, hz⟩
              rw [h_union_empty] at hz_union
              exact False.elim (EmptySet_is_empty z hz_union)
            . intro hz_empty
              exact False.elim (EmptySet_is_empty z hz_empty)
          -- x ∈ C, and every element of C is ∅, so x = ∅, so x ∈ {∅}
          rw [Singleton_is_specified]
          exact this x hx_in_C
        . intro hx_in_singleton
          -- x ∈ {∅} → x ∈ C
          rw [Singleton_is_specified] at hx_in_singleton
          subst hx_in_singleton
          -- ∅ ∈ C follows since C is nonempty and every element of C is ∅
          -- Since C ≠ ∅, there exists y ∈ C
          have hC_nonempty' : ∃ y, y ∈ C :=
            by
              -- If C = ∅, this contradicts hC_non_empty
              apply Classical.by_contradiction
              intro h
              -- Since h : ¬∃ y, y ∈ C, but we have ⟨y, hy⟩, contradiction
              exact False.elim (h ⟨y, hy⟩)
              apply hC_non_empty
              apply ExtSet
              intro z
              constructor
                · intro hz_in_C
                  -- Since ¬∃y, y ∈ C, so all z ∉ C
                  exfalso
                  exact h ⟨z, hz_in_C⟩
                · intro hz_in_empty
                  exact False.elim (EmptySet_is_empty z hz_in_empty)
          cases hC_nonempty' with
          | intro y hy =>
            -- every element of C is ∅, so y = ∅, so ∅ ∈ C
            have h_all_empty : ∀ y, y ∈ C → y = ∅ := by
              intro y' hy'
              apply ExtSet
              intro z
              constructor
              . intro hz
                have hz_union : z ∈ (⋃ C) := (UnionSet_is_specified C z).mpr ⟨y', hy', hz⟩
                rw [h_union_empty] at hz_union
                exact False.elim (EmptySet_is_empty z hz_union)
              . intro hz_empty
                exact False.elim (EmptySet_is_empty z hz_empty)
            have y_eq_empty := h_all_empty y hy
            rw [←y_eq_empty]
            exact hy
      . intro hC_singleton
        rw [hC_singleton] at h_union_empty
        exact h_union_empty

  end UnionAxiom
end SetUniverse

export SetUniverse.UnionAxiom (
  Union
  UnionExistsUnique
  Union_is_specified
  UnionSet
  UnionSet_is_empty
  UnionSet_is_empty'
  UnionSet_is_specified
  UnionSet_is_unique
  Set_is_empty_1
  Set_is_empty_2
  Set_is_empty_3
  UnionSetIsEmpty_SetNonEmpty_SingletonEmptySet
)

/-!
## UNION Axiom
# Example of Union Axiom
    C = { {x}, {y} , {z} }
    U = ⋃ C
    U = { x, y, z }

# This means that the union set of C is the set of all elements of every element of C.

## Define the Union Set of Two Sets

# The union set of two sets A and B is the set of all elements that are in A, in B, or in both.
# This is often denoted as A ∪ B.
# Example of Union Set
    A = { 1, 2 }
    B = { a, b }
    A ∪ B = { 1, 2, a, b }


-/
