inductive Cat :=
| Set : Cat
| var (n : Nat) : Cat

open Sum

mutual

inductive Obj : Cat → Type where
| var (C : Cat) (n : Nat) : Obj C
| corepr {C : Cat} (F : Func C Cat.Set) : Obj C
| app' {C D : Cat} (F : Func' C D) (X : Obj C) : Obj D

inductive Func' : (C : Cat) → Cat → Type where
| var (C D : Cat) (n : Nat) : Func' C D
| hom (C : Cat) (X : Obj C) : Func' C Cat.Set -- X is the domain
| prod {C : Cat} (F G : Func C Cat.Set) : Func' C Cat.Set

inductive Func : Cat → Cat → Type where
| id (C : Cat) : Func C C
| comp' {C D E : Cat} (F : Func' C D) (G : Func D E) : Func C E

end

def Func.comp : {C D E : Cat} → (F : Func C D) → (G : Func D E) → Func C E
| _, _, _, Func.id _,      G => G
| _, _, _, Func.comp' F G, H => Func.comp' F (comp G H)

def Func.app : {C D : Cat} → (F : Func C D) → Obj C → Obj D
| _, _, Func.id _,      X => X
| _, _, Func.comp' F G, X => app G (Obj.app' F X)

def Func.hom {C : Cat} (X : Obj C) : Func C Cat.Set :=
Func.comp' (Func'.hom C X) (Func.id _)

def Func.var (C D : Cat) (n : Nat) : Func C D :=
Func.comp' (Func'.var C D n) (Func.id _)

def Func.prod {C : Cat} (F G : Func C Cat.Set) : Func C Cat.Set :=
Func.comp' (Func'.prod F G) (Func.id _)

open Func Obj

structure Context : Type 1 :=
(elem : Obj Cat.Set → Type)
(isCorepr : {C : Cat} → Func C Set → Prop)

variable (Γ : Context)

inductive Elem : (X : Obj Cat.Set) → Type
| var (X : Obj Cat.Set) (x : Γ.elem X) : Elem X
| id {C : Cat} (X : Obj C) : Elem ((Func.hom X).app X)
| comp {C : Cat} {X Y Z : Obj C}
  (f : Elem ((hom X).app Y))
  (g : Elem ((hom Y).app Z)) : Elem ((hom X).app Z)
| app {X Y : Obj Cat.Set} (f : Elem ((hom X).app Y)) (x : Elem X) : Elem Y
| map {C D : Cat} (F : Func C D) {X Y : Obj C} (f : Elem ((hom X).app Y)) :
  Elem (app (hom (app F X)) (app F Y))
| extend {C : Cat} (F : Func C Cat.Set) (h : Γ.isCorepr F) {X : Obj C} :
  Elem ((app (hom (app F X)) (app (hom (corepr F)) X)))
| unit {C : Cat} (F : Func C Cat.Set)  (h : Γ.isCorepr F) :
  Elem (app F (corepr F))
-- | prod_mk {C : Cat} (F G : Func C Cat.Set) (X : Obj C) :
--   Elem (app (hom (app F X)) (app (hom (app G X)) (app (prod F G) X)))
| prodMk {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x : Elem (F.app X)) (y : Elem (G.app X)) :
  Elem ((F.prod G).app X)
| prodFst {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x : Elem ((F.prod G).app X)) : Elem (F.app X)
| prodSnd {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x : Elem ((F.prod G).app X)) : Elem (G.app X)

inductive Rel : {X : Obj Cat.Set} → (x y : Elem Γ X) → Prop
| refl {X : Obj Cat.Set} (x : Elem Γ X) : Rel x x
| symm {X : Obj Cat.Set} {x y : Elem Γ X} : Rel x y → Rel y x
| trans {X : Obj Cat.Set} {x y z : Elem Γ X} : Rel x y → Rel y z → Rel x z
| idComp {C : Cat} {X Y : Obj C} {f : Elem Γ ((hom X).app Y)} :
  Rel ((Elem.id X).comp f) f
| compId {C : Cat} {X Y : Obj C} {f : Elem Γ ((hom X).app Y)} :
  Rel (f.comp (Elem.id Y)) f
| compAssoc {C : Cat} {W X Y Z : Obj C} (f : Elem Γ ((hom W).app X))
  (g : Elem Γ ((hom X).app Y)) (h : Elem Γ ((hom Y).app Z)) :
  Rel ((f.comp g).comp h) (f.comp (g.comp h))
| idApp {X : Obj Cat.Set} (x : Elem Γ X) :
  Rel ((Elem.id X).app x) x
| compApp {X Y Z : Obj Cat.Set} (f : Elem Γ ((hom X).app Y))
  (g : Elem Γ ((hom Y).app Z)) (x : Elem Γ X):
  Rel ((f.comp g).app x) (g.app (f.app x))
| mapId {C D : Cat} (F : Func C D) (X : Obj C) :
  Rel (Elem.map F (Elem.id X)) (Elem.id (F.app X))
| mapComp {C D : Cat} (F : Func C D) {X Y Z : Obj C}
  (f : Elem Γ ((hom X).app Y)) (g : Elem Γ ((hom Y).app Z)) :
  Rel (Elem.map F (f.comp g)) ((Elem.map F f).comp (Elem.map F g))
| fstMk {C : Cat} (F G : Func C Cat.Set){X : Obj C}
  (x : Elem Γ (F.app X)) (y : Elem Γ (G.app X)) :
  Rel (Elem.prodFst (x.prodMk y)) x
| sndMk {C : Cat} (F G : Func C Cat.Set){X : Obj C}
  (x : Elem Γ (F.app X)) (y : Elem Γ (G.app X)) :
  Rel (Elem.prodSnd (x.prodMk y)) y
| compCongr {C : Cat} {X Y Z : Obj Cat.Set} {f₁ f₂ : Elem Γ ((hom X).app Y)}
  {g₁ g₂ : Elem Γ ((hom Y).app Z)} :
  Rel f₁ f₂ → Rel g₁ g₂ → Rel (f₁.comp g₁) (f₂.comp g₂)
| appCongr {X Y : Obj Cat.Set} {f₁ f₂ : Elem Γ ((hom X).app Y)} {x₁ x₂ : Elem Γ X} :
  Rel f₁ f₂ → Rel x₁ x₂ → Rel (f₁.app x₁) (f₂.app x₂)
| mapCongr {C D : Cat} {F : Func C D} {X Y : Obj C} {f₁ f₂ : Elem Γ ((hom X).app Y)} :
  Rel f₁ f₂ → Rel (Elem.map F f₁) (Elem.map F f₂)
| prodMkCongr {C : Cat} (F G : Func C Cat.Set) {X : Obj C}
  {x₁ x₂ : Elem Γ (F.app X)} {y₁ y₂ : Elem Γ (G.app X)} :
  Rel x₁ x₂ → Rel y₁ y₂ → Rel (x₁.prodMk y₁) (x₂.prodMk y₂)
| prodFstCongr {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x₁ x₂ : Elem Γ ((F.prod G).app X)) :
  Rel x₁ x₂ → Rel x₁.prodFst x₂.prodFst
| prodSndCongr {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x₁ x₂ : Elem Γ ((F.prod G).app X)) :
  Rel x₁ x₂ → Rel x₁.prodSnd x₂.prodSnd

namespace NormElem

mutual

-- prodMk can only be applied to terms not of the form fst snd.

-- We have raw Elems and Elems. Elems are the closure under identity
-- and composition functor map and function application of raw Elems.
-- We can only apply or map raw homs.

inductive RawElem : Obj Cat.Set → Type where
| var (X : Obj Cat.Set) (x : Γ.elem X) : RawElem X
| extend {C : Cat} (F : Func C Cat.Set) (h : Γ.isCorepr F) {X : Obj C} :
  RawElem ((app (hom (app F X)) (app (hom (corepr F)) X)))
| unit {C : Cat} (F : Func C Cat.Set)  (h : Γ.isCorepr F) :
  RawElem (app F (corepr F))

inductive RawElemFst : Obj Cat.Set → Type where
| ofVar {C : Cat} {F G : Func C Cat.Set} {X : Obj C} (x : Γ.elem ((F.prod G).app X)) :
  RawElemFst (F.app X)
| ofRawElemSnd {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x : RawElemSnd ((F.prod G).app X)) : RawElemFst (F.app X)

inductive RawElemSnd : Obj Cat.Set → Type where
| ofVar {C : Cat} {F G : Func C Cat.Set} {X : Obj C} (x : Γ.elem ((F.prod G).app X)) :
  RawElemSnd (G.app X)
| ofRawElemFst {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x : RawElemFst ((F.prod G).app X)) : RawElemSnd (G.app X)

inductive RawElemProdMk : Obj Cat.Set → Type where
| ofFstLeft :

inductive Elem : Obj Cat.Set → Type where
| id {C : Cat} (X : Obj C) : Elem ((Func.hom X).app X)
|

end

end NormElem