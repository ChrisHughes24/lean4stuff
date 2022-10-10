class category (C : Type) :=
( hom : C → C → Type )
( id : (X : C) → hom X X )
( comp : {X Y Z : C} → hom X Y → hom Y Z → hom X Z )
( id_comp {X Y : C} (f : hom X Y) : comp (id X) f = f )
( comp_id {X Y : C} (f : hom X Y) : comp f (id Y) = f )
( assoc {W X Y Z : C} (f : hom W X) (g : hom X Y) (h : hom Y Z) :
    comp (comp f g) h = comp f (comp g h) )

notation " 𝟙 " => category.id
infixr: 80 " ≫ " => category.comp
infixr: 10 " ⟶ " => category.hom

instance {α : Type} {β : α → Type} [DecidableEq α] [(a : α) → DecidableEq (β a)] :
  DecidableEq (Sigma β)
| ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ =>
  if h : x₁ = x₂
  then by
    subst h;
    exact @decidable_of_decidable_of_iff (y₁ = y₂) _ _
      ⟨λ h => by subst h; rfl, λ h => by injection h; assumption⟩
  else isFalse (λ h2 => h $ by injection h2; assumption)
