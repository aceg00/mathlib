/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Miscellaneous function constructions and lemmas.
-/
import logic.basic data.option.defs

universes u v w

namespace function

section
variables {α : Sort u} {β : Sort v} {f : α → β}

lemma hfunext {α α': Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : Πa, β a} {f' : Πa, β' a}
  (hα : α = α') (h : ∀a a', a == a' → f a == f' a') : f == f' :=
begin
  subst hα,
  have : ∀a, f a == f' a,
  { intro a, exact h a a (heq.refl a) },
  have : β = β',
  { funext a, exact type_eq_of_heq (this a) },
  subst this,
  apply heq_of_eq,
  funext a,
  exact eq_of_heq (this a)
end

lemma funext_iff {β : α → Sort*} {f₁ f₂ : Π (x : α), β x} : f₁ = f₂ ↔ (∀a, f₁ a = f₂ a) :=
iff.intro (assume h a, h ▸ rfl) funext

lemma comp_apply {α : Sort u} {β : Sort v} {φ : Sort w} (f : β → φ) (g : α → β) (a : α) :
  (f ∘ g) a = f (g a) := rfl

@[simp] theorem injective.eq_iff (I : injective f) {a b : α} :
  f a = f b ↔ a = b :=
⟨@I _ _, congr_arg f⟩

lemma injective.ne (hf : function.injective f) {a₁ a₂ : α} : a₁ ≠ a₂ → f a₁ ≠ f a₂ :=
mt (assume h, hf h)

def injective.decidable_eq [decidable_eq β] (I : injective f) : decidable_eq α
| a b := decidable_of_iff _ I.eq_iff

lemma injective.of_comp {γ : Sort w} {g : γ → α} (I : injective (f ∘ g)) : injective g :=
λ x y h, I $ show f (g x) = f (g y), from congr_arg f h

lemma surjective.of_comp {γ : Sort w} {g : γ → α} (S : surjective (f ∘ g)) : surjective f :=
λ y, let ⟨x, h⟩ := S y in ⟨g x, h⟩

instance decidable_eq_pfun (p : Prop) [decidable p] (α : p → Type*)
  [Π hp, decidable_eq (α hp)] : decidable_eq (Π hp, α hp)
| f g := decidable_of_iff (∀ hp, f hp = g hp) funext_iff.symm

theorem cantor_surjective {α} (f : α → α → Prop) : ¬ function.surjective f | h :=
let ⟨D, e⟩ := h (λ a, ¬ f a a) in
(iff_not_self (f D D)).1 $ iff_of_eq (congr_fun e D)

theorem cantor_injective {α : Type*} (f : (α → Prop) → α) :
  ¬ function.injective f | i :=
cantor_surjective (λ a b, ∀ U, a = f U → U b) $
surjective_of_has_right_inverse ⟨f, λ U, funext $
  λ a, propext ⟨λ h, h U rfl, λ h' U' e, i e ▸ h'⟩⟩

/-- `g` is a partial inverse to `f` (an injective but not necessarily
  surjective function) if `g y = some x` implies `f x = y`, and `g y = none`
  implies that `y` is not in the range of `f`. -/
def is_partial_inv {α β} (f : α → β) (g : β → option α) : Prop :=
∀ x y, g y = some x ↔ f x = y

theorem is_partial_inv_left {α β} {f : α → β} {g} (H : is_partial_inv f g) (x) : g (f x) = some x :=
(H _ _).2 rfl

theorem injective_of_partial_inv {α β} {f : α → β} {g} (H : is_partial_inv f g) : injective f :=
λ a b h, option.some.inj $ ((H _ _).2 h).symm.trans ((H _ _).2 rfl)

theorem injective_of_partial_inv_right {α β} {f : α → β} {g} (H : is_partial_inv f g)
 (x y b) (h₁ : b ∈ g x) (h₂ : b ∈ g y) : x = y :=
((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)

theorem left_inverse.comp_eq_id {f : α → β} {g : β → α} (h : left_inverse f g) : f ∘ g = id :=
funext h

theorem right_inverse.comp_eq_id {f : α → β} {g : β → α} (h : right_inverse f g) : g ∘ f = id :=
funext h

theorem left_inverse.comp {γ} {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : left_inverse f g) (hh : left_inverse h i) : left_inverse (h ∘ f) (g ∘ i) :=
assume a, show h (f (g (i a))) = a, by rw [hf (i a), hh a]

theorem right_inverse.comp {γ} {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : right_inverse f g) (hh : right_inverse h i) : right_inverse (h ∘ f) (g ∘ i) :=
left_inverse.comp hh hf

local attribute [instance, priority 10] classical.prop_decidable

/-- We can use choice to construct explicitly a partial inverse for
  a given injective function `f`. -/
noncomputable def partial_inv {α β} (f : α → β) (b : β) : option α :=
if h : ∃ a, f a = b then some (classical.some h) else none

theorem partial_inv_of_injective {α β} {f : α → β} (I : injective f) :
  is_partial_inv f (partial_inv f) | a b :=
⟨λ h, if h' : ∃ a, f a = b then begin
    rw [partial_inv, dif_pos h'] at h,
    injection h with h, subst h,
    apply classical.some_spec h'
  end else by rw [partial_inv, dif_neg h'] at h; contradiction,
 λ e, e ▸ have h : ∃ a', f a' = f a, from ⟨_, rfl⟩,
   (dif_pos h).trans (congr_arg _ (I $ classical.some_spec h))⟩

theorem partial_inv_left {α β} {f : α → β} (I : injective f) : ∀ x, partial_inv f (f x) = some x :=
is_partial_inv_left (partial_inv_of_injective I)

end

section inv_fun
variables {α : Type u} [inhabited α] {β : Sort v} {f : α → β} {s : set α} {a : α} {b : β}

local attribute [instance, priority 10] classical.prop_decidable

/-- Construct the inverse for a function `f` on domain `s`. -/
noncomputable def inv_fun_on (f : α → β) (s : set α) (b : β) : α :=
if h : ∃a, a ∈ s ∧ f a = b then classical.some h else default α

theorem inv_fun_on_pos (h : ∃a∈s, f a = b) : inv_fun_on f s b ∈ s ∧ f (inv_fun_on f s b) = b :=
by rw [bex_def] at h; rw [inv_fun_on, dif_pos h]; exact classical.some_spec h

theorem inv_fun_on_mem (h : ∃a∈s, f a = b) : inv_fun_on f s b ∈ s := (inv_fun_on_pos h).left

theorem inv_fun_on_eq (h : ∃a∈s, f a = b) : f (inv_fun_on f s b) = b := (inv_fun_on_pos h).right

theorem inv_fun_on_eq' (h : ∀ x y ∈ s, f x = f y → x = y) (ha : a ∈ s) :
  inv_fun_on f s (f a) = a :=
have ∃a'∈s, f a' = f a, from ⟨a, ha, rfl⟩,
h _ _ (inv_fun_on_mem this) ha (inv_fun_on_eq this)

theorem inv_fun_on_neg (h : ¬ ∃a∈s, f a = b) : inv_fun_on f s b = default α :=
by rw [bex_def] at h; rw [inv_fun_on, dif_neg h]

/-- The inverse of a function (which is a left inverse if `f` is injective
  and a right inverse if `f` is surjective). -/
noncomputable def inv_fun (f : α → β) : β → α := inv_fun_on f set.univ

theorem inv_fun_eq (h : ∃a, f a = b) : f (inv_fun f b) = b :=
inv_fun_on_eq $ let ⟨a, ha⟩ := h in ⟨a, trivial, ha⟩

lemma inv_fun_neg (h : ¬ ∃ a, f a = b) : inv_fun f b = default α :=
by refine inv_fun_on_neg (mt _ h); exact assume ⟨a, _, ha⟩, ⟨a, ha⟩

theorem inv_fun_eq_of_injective_of_right_inverse {g : β → α}
  (hf : injective f) (hg : right_inverse g f) : inv_fun f = g :=
funext $ assume b,
hf begin rw [hg b], exact inv_fun_eq ⟨g b, hg b⟩ end

lemma right_inverse_inv_fun (hf : surjective f) : right_inverse (inv_fun f) f :=
assume b, inv_fun_eq $ hf b

lemma left_inverse_inv_fun (hf : injective f) : left_inverse (inv_fun f) f :=
assume b,
have f (inv_fun f (f b)) = f b,
  from inv_fun_eq ⟨b, rfl⟩,
hf this

lemma inv_fun_surjective (hf : injective f) : surjective (inv_fun f) :=
surjective_of_has_right_inverse ⟨_, left_inverse_inv_fun hf⟩

lemma inv_fun_comp (hf : injective f) : inv_fun f ∘ f = id := funext $ left_inverse_inv_fun hf

lemma injective.has_left_inverse (hf : injective f) : has_left_inverse f :=
⟨inv_fun f, left_inverse_inv_fun hf⟩

lemma injective_iff_has_left_inverse : injective f ↔ has_left_inverse f :=
⟨injective.has_left_inverse, injective_of_has_left_inverse⟩

end inv_fun

section surj_inv
variables {α : Sort u} {β : Sort v} {f : α → β}

/-- The inverse of a surjective function. (Unlike `inv_fun`, this does not require
  `α` to be inhabited.) -/
noncomputable def surj_inv {f : α → β} (h : surjective f) (b : β) : α := classical.some (h b)

lemma surj_inv_eq (h : surjective f) (b) : f (surj_inv h b) = b := classical.some_spec (h b)

lemma right_inverse_surj_inv (hf : surjective f) : right_inverse (surj_inv hf) f :=
surj_inv_eq hf

lemma left_inverse_surj_inv (hf : bijective f) : left_inverse (surj_inv hf.2) f :=
right_inverse_of_injective_of_left_inverse hf.1 (right_inverse_surj_inv hf.2)

lemma surjective.has_right_inverse (hf : surjective f) : has_right_inverse f :=
⟨_, right_inverse_surj_inv hf⟩

lemma surjective_iff_has_right_inverse : surjective f ↔ has_right_inverse f :=
⟨surjective.has_right_inverse, surjective_of_has_right_inverse⟩

lemma bijective_iff_has_inverse : bijective f ↔ ∃ g, left_inverse g f ∧ right_inverse g f :=
⟨λ hf, ⟨_, left_inverse_surj_inv hf, right_inverse_surj_inv hf.2⟩,
 λ ⟨g, gl, gr⟩, ⟨injective_of_left_inverse gl, surjective_of_has_right_inverse ⟨_, gr⟩⟩⟩

lemma injective_surj_inv (h : surjective f) : injective (surj_inv h) :=
injective_of_has_left_inverse ⟨f, right_inverse_surj_inv h⟩

end surj_inv

section update
variables {α : Sort u} {β : α → Sort v} {α' : Sort w} [decidable_eq α] [decidable_eq α']

/-- Replacing the value of a function at a given point by a given value. -/
def update (f : Πa, β a) (a' : α) (v : β a') (a : α) : β a :=
if h : a = a' then eq.rec v h.symm else f a

@[simp] lemma update_same (a : α) (v : β a) (f : Πa, β a) : update f a v a = v :=
dif_pos rfl

@[simp] lemma update_noteq {a a' : α} (h : a ≠ a') (v : β a') (f : Πa, β a) : update f a' v a = f a :=
dif_neg h

@[simp] lemma update_eq_self (a : α) (f : Πa, β a) : update f a (f a) = f :=
begin
  refine funext (λi, _),
  by_cases h : i = a,
  { rw h, simp },
  { simp [h] }
end

lemma update_comp {β : Sort v} (f : α → β) {g : α' → α} (hg : injective g) (a : α') (v : β) :
  (update f (g a) v) ∘ g = update (f ∘ g) a v :=
begin
  refine funext (λi, _),
  by_cases h : i = a,
  { rw h, simp },
  { simp [h, hg.ne] }
end

end update

lemma uncurry_def {α β γ} (f : α → β → γ) : uncurry f = (λp, f p.1 p.2) :=
funext $ assume ⟨a, b⟩, rfl

-- `uncurry'` is the version of `uncurry` with correct definitional reductions
def uncurry' {α β γ} (f : α → β → γ) := λ p : α × β, f p.1 p.2

@[simp]
lemma curry_uncurry' {α : Type*} {β : Type*} {γ : Type*} (f : α → β → γ) : curry (uncurry' f) = f :=
by funext ; refl

@[simp]
lemma uncurry'_curry {α : Type*} {β : Type*} {γ : Type*} (f : α × β → γ) : uncurry' (curry f) = f :=
by { funext, simp [curry, uncurry', prod.mk.eta] }

def restrict {α β} (f : α → β) (s : set α) : subtype s → β := λ x, f x.val

theorem restrict_eq {α β} (f : α → β) (s : set α) : function.restrict f s = f ∘ (@subtype.val _ s) := rfl

section bicomp
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ε : Type*}

def bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) (a b) :=
f (g a) (h b)

def bicompr (f : γ → δ) (g : α → β → γ) (a b) :=
f (g a b)

-- Suggested local notation:
local notation f `∘₂` g := bicompr f g

lemma uncurry_bicompr (f : α → β → γ) (g : γ → δ) :
  uncurry (g ∘₂ f) = (g ∘ uncurry f) :=
funext $ λ ⟨p, q⟩, rfl

lemma uncurry'_bicompr (f : α → β → γ) (g : γ → δ) :
  uncurry' (g ∘₂ f) = (g ∘ uncurry' f) := rfl
end bicomp

/-- A function is involutive, if `f ∘ f = id`. -/
def involutive {α} (f : α → α) : Prop := ∀ x, f (f x) = x

lemma involutive_iff_iter_2_eq_id {α} {f : α → α} : involutive f ↔ (f^[2] = id) :=
funext_iff.symm

namespace involutive
variables {α : Sort u} {f : α → α} (h : involutive f)

protected lemma left_inverse : left_inverse f f := h
protected lemma right_inverse : right_inverse f f := h

protected lemma injective : injective f := injective_of_left_inverse h.left_inverse
protected lemma surjective : surjective f := λ x, ⟨f x, h x⟩
protected lemma bijective : bijective f := ⟨h.injective, h.surjective⟩

end involutive

end function

/-- `s.piecewise f g` is the function equal to `f` on the set `s`, and to `g` on its complement. -/
def set.piecewise {α : Type u} {β : α → Sort v} (s : set α) (f g : Πi, β i) [∀j, decidable (j ∈ s)] :
  Πi, β i :=
λi, if i ∈ s then f i else g i
