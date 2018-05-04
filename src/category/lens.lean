
import .classes

import util.data.functor

inductive lens_type
| lens | traversal | prism

universes u v

/-
  Features
  - Lens types: lens, traversal, prism, indexed (...),
  - conversion
  - lens laws
  - parametric lens laws
-/

def const {α : Sort u} {β : Sort v} (x : α) (_ : β) := x

instance {α} : functor (const α) :=
by { refine { functor . map := λ β γ f x, x, .. } ; intros ; refl, }

instance {α} [monoid α] : applicative (const α) :=
by { refine { applicative .
              map := λ β γ f (x : α), x,
              pure := λ β x, (1 : α),
              seq := λ β γ (f : α) (x : α), (f * x : α), .. }
      ; intros ; dsimp only [const] at * ; try { refl <|> apply one_mul <|> apply mul_one },
      symmetry, apply mul_assoc, }

namespace lens

-- @[class]
def rep : lens_type → Type u → Type u → Type u → Type u → Type.{u+1}
| lens_type.lens x x' y y'      :=
  Π (f : Type u → Type u) [functor f], (y → f y') → (x → f x')
| lens_type.traversal x x' y y' :=
  Π (f : Type u → Type u) [applicative f], (y → f y') → (x → f x')
| lens_type.prism x x' y y'     :=
  Π (f : Type u → Type u) (p : Type u → Type u → Type u)
    [applicative f] [choice p],
    (y → f y') → (x → f x')

namespace rep

def getting (r s a : Type u) := (a → const r a) → (s → const r s)
def a_setter (s t a b : Type u) := (a → identity b) → (s → identity t)

def get {s a} (ln : getting a s a) (x : s) : a :=
ln id x

def set {s t a b} (ln : a_setter s t a b) (i : b) (x : s) : t :=
(ln (const $ identity.mk i) x).run_identity

def over {s t a b} (ln : a_setter s t a b) (f : a → b) (x : s) : t :=
(ln (identity.mk ∘ f) x).run_identity

local notation x ` & `:40 y := y x
#print notation = $
local infix ` .~ `:35 := set
local infix ` %~ `:35 := over
local notation x ` ^. `:35 ln := get ln x

structure lens_fam (F G : Type u → Type u) :=
  (ln : Π a b, lens.rep lens_type.lens (F a) (F b) (G a) (G b))
  (law1 : ∀ a b (v : G b) (x : F a),
      ((x & ln a b _ .~ v)^.ln b b _) = v)
  (law2 : ∀ a (x : F a),
      (x & ln a a _ .~ (x^.ln a a _)) = x)
  (law3 : ∀ a b c (v : G b) (v' : G c) (x : F a),
      ((x & ln a b _ .~ v) & ln b c _ .~ v') = (x & ln a c _ .~ v'))
  (law4 : ∀ a b (x : F a) (f : G a → G b),
      (x & ln a b _ %~ f) = (x & ln a b _ .~ f (x^.ln a a _)))

def mono_lens (s a : Type u) := lens_fam (const s) (const a)

end rep

end lens

structure lens_like (lens_t : lens_type) (s t a b : Type u) :=
  (F : lens.rep lens_t s t a b)

def lens := lens_like lens_type.lens
def traversal := lens_like lens_type.traversal
def prism := lens_like lens_type.traversal

namespace lens

def comp_res : lens_type → lens_type → lens_type
 | lens_type.lens lens_type.lens := lens_type.lens
 | _ _ := lens_type.traversal

-- @[instance]
-- def lens_ctx_left : Π {l₀ l₁} {f : Type u → Type u}, lens_ctx (comp_res l₀ l₁) f → lens_ctx l₀ f :=
-- by { introv inst, cases l₀ ; cases l₁ ; exact inst <|> exact inst.to_functor, }

-- -- @[instance]
-- def lens_ctx_right : Π {l₀ l₁} {f : Type u → Type u}, lens_ctx (comp_res l₀ l₁) f → lens_ctx l₁ f :=
-- by { introv inst, cases l₀ ; cases l₁ ; exact inst <|> exact inst.to_functor, }

variables {x x' y y' z z' : Type u}

def comp : Π {l₀ l₁},
             lens_like l₀ x x' y y' →
             lens_like l₁ y y' z z' →
             lens_like (comp_res l₀ l₁) x x' z z'
 | lens_type.lens lens_type.lens l l' := ⟨ λ F ctx, l.F _ _ ∘ {! !} ⟩

#print notation .
local infixr ` ∘ ` := comp

instance has_coe_to_fun_lens : Π {l : lens_type}, has_coe_to_fun (lens_like l x x' y y')
| lens_type.traversal :=
  { F := λ _, Π {f : Type u → Type u} [applicative f], (y → f y') → (x → f x')
  , coe := λ ln f inst, ln.F _ inst }
| lens_type.lens :=
  { F := λ _, Π {f : Type u → Type u} [functor f], (y → f y') → (x → f x')
  , coe := λ ln f inst, ln.F _ inst }

instance : has_coe (lens x x' y y') (traversal x x' y y') :=
{ coe := λ ⟨ f ⟩, ⟨ λ _ inst, f _ inst.to_functor ⟩ }



section ex

variable ln : lens x x' y y'
variable ln' : traversal y y' z z'
variable f : Type u → Type u
variable [applicative f]
variable m : z → f z'
variables (i : x) (i' : f x')

#check (ln ∘ ln') m i

end ex

end lens
