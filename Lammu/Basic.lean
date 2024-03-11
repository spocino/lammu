import «Mathlib».Control.Monad.Cont

-- implementation of the typed ̅λμ̃μ calculus

inductive All {α : Type} (p : α → Type) : List α → Type where
| nil : All p []
| cons : {x : α} → (px : p x) → (pxs : All p xs) -> All p (x :: xs)

inductive Elem {α : Type} : α → List α → Type
| here : Elem x (x :: xs)
| there : Elem x xs → Elem x (y :: xs)

inductive Any (p : k -> Type) : List k → Type where
| this : p x → Any p (x :: xs)
| that : Any p xs -> Any p (x :: xs)

theorem empty_elem_nil : Elem x [] → Empty := by
  intro a
  cases a

def lookup (ctx : All p Γ) (x_in_Γ : Elem x Γ) : p x :=
  match ctx with
  | All.nil => Empty.elim (empty_elem_nil x_in_Γ)
  | All.cons px pxs => match x_in_Γ with
    | Elem.here => px
    | Elem.there a => lookup pxs a

def merge (op : p x → p x' → p x'') : Any p (x::xs) → Any p (x'::xs) →  Any p (x''::xs) :=
  λα β ↦ match α, β with
  | (Any.this a), (Any.this b) => Any.this (op a b)
  | (Any.that a), _ => Any.that a
  | _, (Any.that b) => Any.that b

def fromElem (v : p a) (e : Elem a d) : Any p d :=
  match e with
  | Elem.here => Any.this v
  | Elem.there t => Any.that (fromElem v t)

def fromAny (cctx : Any p [a]) : p a :=
  match cctx with
  | Any.this a => a

namespace STLC

inductive Ty where
| n   : Ty
| imp : Ty → Ty → Ty

inductive Term : List Ty → Ty → Type where
| var  : Elem a Γ → Term Γ a
| lam  : Term (a::Γ) b → Term Γ (Ty.imp a b)
| app  : Term Γ (Ty.imp a b) → Term Γ a → Term Γ b
| int  : ℤ → Term Γ Ty.n
| plus : Term Γ Ty.n → Term Γ Ty.n → Term Γ Ty.n

def EvTy (r : Type) (t : Ty) : Type :=
  match t with
  | Ty.n => ℤ
  | Ty.imp t t' => EvTy r t → Cont r (EvTy r t')

def eval (term : Term Γ t) (env : All (EvTy r) Γ) : Cont r (EvTy r t) :=
  match term with
  | Term.var v => pure $ lookup env v
  | Term.lam t => pure λx ↦ eval t (All.cons x env)
  | Term.app t t' => λk ↦ eval t env (λx ↦ eval t' env (λy ↦ x y k))
  | Term.int n => letFun n
  | Term.plus t t' => do
    let n1 ← eval t env
    let n2 ← eval t' env
    pure (Int.add n1 n2)

end STLC

namespace LambdaMu

inductive Ty where
| n   : Ty
| imp : Ty → Ty → Ty
| bot : Ty

inductive Term : List Ty → Ty → List Ty → Type where
| var   : Elem a Γ → Term Γ a Δ
| lam   : Term (a::Γ) b Δ → Term Γ (Ty.imp a b) Δ
| app   : Term Γ (Ty.imp a b) Δ → Term Γ a Δ → Term Γ b Δ
| let   : Term Γ s Δ → Term (s::Γ) t Δ → Term Γ t Δ
| mu    : Term Γ Ty.bot (a::Δ) → Term Γ a Δ
| named : Elem a Δ → Term Γ a Δ → Term Γ Ty.bot Δ
| int   : ℤ → Term Γ Ty.n Δ
| plus  : Term Γ Ty.n Δ → Term Γ Ty.n Δ → Term Γ Ty.n Δ

def EvTy (r : Type) (t : Ty) : Type :=
  match t with
  | Ty.n => Int
  | Ty.bot => Empty
  | Ty.imp t t' => EvTy r t → Cont r (EvTy r t')

def eval (term : Term Γ t Δ) (env : All (EvTy r) Γ) : Cont r (Any (EvTy r) (t::Δ)) :=
  match term with
  | Term.var v => pure $ Any.this $ lookup env v
  | Term.mu t => λk ↦ eval t env λf ↦ match f with
    | Any.that t => k t
  | Term.named v t => λk ↦ eval t env λf ↦ match f with
    | Any.this n => k $ Any.that (fromElem n v)
    | Any.that t => k $ Any.that t
  | Term.let this inThis => λk ↦ eval this env λf ↦ match f with
    | Any.this t => eval inThis (All.cons t env) k
    | Any.that t => k (Any.that t)
  | Term.app t t' => λk ↦
    eval t env λx ↦ eval t' env λy ↦ match x, y with
    | Any.this t, Any.this t' => t t' λv ↦ k (Any.this v)
    | Any.that t, _ => k (Any.that t)
    | _, Any.that t => k (Any.that t)
  | Term.lam t => λk ↦ k $ Any.this λa b ↦ eval t (All.cons a env) λc ↦ match c with
    | Any.this t => b t
    | Any.that t => k (Any.that t)
  | Term.int n => pure $ Any.this n
  | Term.plus t t' => do
    let n  ← eval t env
    let n' ← eval t' env
    let add : EvTy r Ty.n → EvTy r Ty.n → EvTy r Ty.n := Int.add
    pure $ merge add n n'



end LambdaMu
