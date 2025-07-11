import Mathlib.Logic.ExistsUnique
import Init.Classical
import Mathlib.Tactic

namespace SetUniverse
  open Classical
  universe u
  variable {U : Type u}

  /-! ### Clase (sin 'class' ni 'structure') que representa pertenencia estensional entre conjuntos ### -/
  axiom ExtSet_from_Eq {U : type u} (x y : U): x = y → (∀ (z: U), mem z x ↔ mem z y)
  def mem {U : Type u} (x y : U) : Prop :=
    ExtSet_from_Eq x y (by rfl)
  class ExtSet (U : Type u) where
    mem : U → U → Prop
    ext : ∀ (x y : U), (∀ (z: U), mem z x ↔ mem z y) → x = y

  /-! ### Notación estándar de la pertenecia a conjuntos ### -/
  notation:48 lhs: 49 " ∈ " rhs:49 => ExtSet.mem rhs lhs

  /-! ### Subconjunto (no estricto) ### -/
  def subseteq {U : Type u} [ExtSet U] (x y : U) : Prop :=
    ∀ (z: U), z ∈ x → z ∈ y

  /-! ### Notación estándar de subconjunto y subconjunto propio ### -/
  notation:50 lhs:51 " ⊆ " rhs:51 => subseteq lhs rhs
  notation:50 lhs:51 " ⊂ " rhs:51 => subseteq lhs rhs ∧ (lhs ≠ rhs)

  /-! ### Notación estándar de superconjunto y superconjunto propio ### -/
  notation:50 lhs:51 " ⊇ " rhs:51 => rhs ⊆ lhs
  notation:50 lhs:51 " ⊃ " rhs:51 => rhs ⊂ lhs

  /-! ### Teorema de igualdad de conjuntos a través de ser subconjunto uno de otro ### -/
  /-! ### EqualityOfSubset : A ⊆ B ∧ B ⊆ A ↔ A = B                                ### -/
  theorem EqualityOfSubset {U : Type u} [ExtSet U] (x y : U) :
    (x ⊆ y) → (y ⊆ x) → (x = y)
    := by
    intro h_xy h_yx
    apply ExtSet.ext
    intro z
    constructor
    · -- Dirección ->
      intro hz_in_x
      unfold subseteq at h_xy
      have h_xy_z : z ∈ y := h_xy z hz_in_x
      have h_subset_xy_z : ∀ (w : U), w ∈ x → w ∈ y := h_xy
      intro hz_in_y
      unfold subseteq at h_yx
      have h_yx_z : z ∈ x := h_yx z hz_in_y
      have h_subset_yx_z : ∀ (w : U), w ∈ y → w ∈ x := h_yx
      have hequival : z ∈ y ↔ z ∈ x := by
        constructor
        · exact h_subset_xy_z z hz_in_x
        · exact h_subset_yx_z z hz_in_y
      exact
    · -- Dirección <-
      intro hz_in_y
      apply h_yx
      exact hz_in_y

  /-! ### Disjuntos ### -/

  -- Instancia explícita de PartialOrder
  instance {U : Type u} [ExtSet U] : PartialOrder U where
    le := (· ⊆ ·) -- le (≤) es la relación de subconjunto (⊆)
    le_refl := by -- Prueba de reflexividad: x ⊆ x
      intro x z h_mem
      exact h_mem
    le_trans := by -- Prueba de transitividad: x ⊆ y → y ⊆ z → x ⊆ z
      intro x y z h_xy h_yz
      intro w h_w_in_x
      apply h_yz
      apply h_xy
      exact h_w_in_x
    le_antisymm := by
      intro x y h_xy h_yx
      apply EqualityOfSubset h_xy h_yx

  -- Ahora, esta instancia debería funcionar sin problemas
  -- instance {U : Type u} [ExtSet U] : Disjoint U where
  --   Disjoint x y := ∀ z, z ∈ x → z ∉ y

end SetUniverse
