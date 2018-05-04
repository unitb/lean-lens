
import util.data.sum

universes u v

def arrow (α : Sort u) (β : Sort v) := α → β

class profunctor (p : Type u → Type u → Type u) :=
  (dimap : Π {α α' β β'}, (α' → α) → (β → β') → p α β → p α' β')
  (dimap_id : ∀ {α β} (x : p α β), dimap id id x = x)
  (dimap_map : ∀ {α α' α'' β β' β''}
                 (f : α → α') (f' : α' → α'')
                 (g : β → β') (g' : β' → β'')
                 (x : p α'' β),
                 dimap (f' ∘ f) (g' ∘ g) x = dimap f g' (dimap f' g x))

export profunctor ( dimap )
open sum functor
class choice (p : Type u → Type u → Type u) extends profunctor p :=
  (left : Π {α β : Type u} (γ : Type u), p α β → p (α ⊕ γ) (β ⊕ γ))
  (right : Π {α β : Type u} (γ : Type u), p α β → p (γ ⊕ α) (γ ⊕ β))
  (dimap_swap_right_eq_left : Π {α β γ : Type u} (x : p α β), dimap swap swap (right γ x) = left γ x)
  (right_dimap : Π {α α' β β' γ : Type u} (x : p α β) (f : α' → α) (g : β → β'),
    right γ (dimap f g x) = dimap (map f) (map g) (right γ x))

instance : profunctor arrow :=
{ dimap := λ α α' β β' f g x, g ∘ x ∘ f
, dimap_id := by { intros, refl }
, dimap_map := by { intros, simp } }

instance : choice arrow :=
{ left := by { introv x i, cases i,
                { left, apply x i },
                { right, exact i } }
, right := by { introv x i, cases i,
                 { left, exact i },
                 { right, apply x i } }
, dimap_swap_right_eq_left := by { intros, simp, funext y, cases y ; refl, }
, right_dimap := by { simp_intros, funext, casesm _ ⊕ _ ; refl }
}
