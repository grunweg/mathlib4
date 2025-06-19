/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.Positivity.Core
import Mathlib.Util.AtomM


/-! # A tactic for clearing denominators in fields

-/

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List

namespace List
variable {M : Type*}

def prod' {M : Type*} [Mul M] [One M] : List M → M := foldr (fun a t ↦ t * a) 1

@[simp]
theorem prod'_cons [Mul M] [One M] {a} {l : List M} : (a :: l).prod' = l.prod' * a := rfl

@[simp]
theorem prod'_nil [Mul M] [One M] : (([] : List M)).prod' = 1 := rfl

-- generalize library `List.prod_inv`
theorem prod'_inv₀ {K : Type*} [DivisionCommMonoid K] :
    ∀ (L : List K), L.prod'⁻¹ = (map (fun x ↦ x⁻¹) L).prod'
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod'_inv₀ xs]

theorem _root_.map_list_prod' {M : Type*} {N : Type*} [Monoid M] [Monoid N] {F : Type*}
    [FunLike F M N] [MonoidHomClass F M N] (f : F) (l : List M) :
    f l.prod' = (map (⇑f) l).prod' :=
  sorry

-- in the library somewhere?
theorem prod'_zpow {β : Type*} [DivisionCommMonoid β] {r : ℤ} {l : List β} :
    l.prod' ^ r = (map (fun x ↦ x ^ r) l).prod' :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_zpow r⟩, (mul_zpow · · r)⟩
  map_list_prod' fr l

-- in the library somewhere?
theorem _root_.List.prod'_pow {β : Type*} [CommMonoid β] {r : ℕ} {l : List β} :
    l.prod' ^ r = (map (fun x ↦ x ^ r) l).prod' :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_pow r⟩, (mul_pow · · r)⟩
  map_list_prod' fr l

end List

namespace Mathlib.Tactic.FieldSimp

/-! ### Theory of lists of pairs (exponent, atom)

This section contains the lemmas which are orchestrated by the `field_simp` tactic
to prove goals in fields.  The basic object which these lemmas concern is `NF M`, a type synonym
for a list of ordered pairs in `ℤ × M`, where typically `M` is a field.
-/

/-- Basic theoretical "normal form" object of the `field_simp` tactic: a type
synonym for a list of ordered pairs in `ℤ × M`, where typically `M` is a field.  This is the
form to which the tactics reduce field expressions. -/
def NF (M : Type*) := List (ℤ × M)

namespace NF
variable {M : Type*}

/-- Augment a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, by prepending another
pair `p : ℤ × M`. -/
@[match_pattern]
def cons (p : ℤ × M) (l : NF M) : NF M := p :: l

@[inherit_doc cons] infixl:100 " ::ᵣ " => cons

/-- Evaluate a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, to an element of `M`,
by forming the "multiplicative linear combination" it specifies: raise each `M` term to the power of
the corresponding `ℤ` term, then multiply them all together. -/
def eval [DivInvMonoid M] (l : NF M) : M := (l.map (fun (⟨r, x⟩ : ℤ × M) ↦ x ^ r)).prod'

@[simp] theorem eval_cons [DivInvMonoid M] (p : ℤ × M) (l : NF M) :
    (p ::ᵣ l).eval = l.eval * p.2 ^ p.1 := by
  unfold eval cons
  rw [List.map_cons]
  rw [List.prod'_cons]

theorem atom_eq_eval [DivInvMonoid M] (x : M) : x = NF.eval [(1, x)] := by simp [eval]

variable (M) in
theorem one_eq_eval [DivInvMonoid M] : (1:M) = NF.eval (M := M) [] := rfl

theorem mul_eq_eval₁ [DivisionCommMonoid M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval * (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, mul_assoc]
  congr! 1
  rw [mul_comm, mul_assoc]

theorem mul_eq_eval₂ [CommGroupWithZero M] {r₁ r₂ : ℤ} (hr : r₁ + r₂ = 0) (x : M) (hx : x ≠ 0)
    {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval * ((r₂, x) ::ᵣ l₂).eval = ((0, x) ::ᵣ l).eval := by
  rw [← hr]
  simp only [← h, eval_cons, zpow_add₀ hx, mul_assoc]
  congr! 1
  simp only [← mul_assoc]
  congr! 1
  rw [mul_comm]

theorem mul_eq_eval₂' [CommGroupWithZero M] {r₁ r₂ : ℤ} (hr : r₁ + r₂ ≠ 0) (x : M)
    {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval * ((r₂, x) ::ᵣ l₂).eval = ((r₁ + r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons]
  obtain rfl | h := eq_or_ne x 0
  · rw [zero_zpow _ hr]
    obtain hr₁ | hr₂ : r₁ ≠ 0 ∨ r₂ ≠ 0 := by omega
    · simp [zero_zpow _ hr₁]
    · simp [zero_zpow _ hr₂]
  simp only [zpow_add₀ h, mul_assoc]
  congr! 1
  simp only [← mul_assoc]
  rw [mul_comm (x ^ r₁)]

theorem mul_eq_eval₃ [DivInvMonoid M] {a₁ : ℤ × M} (a₂ : ℤ × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval * l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₂ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, mul_assoc]

theorem mul_eq_eval [DivisionMonoid M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) :
    x₁ * x₂ = l.eval := by
  rw [hx₁, hx₂, h]

theorem div_eq_eval₁ [DivisionCommMonoid M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval / (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, div_eq_mul_inv, mul_assoc]
  congr! 1
  rw [mul_comm]

theorem div_eq_eval₂ [CommGroupWithZero M] {r₁ r₂ : ℤ} (hr : r₁ - r₂ = 0) (x : M) (hx : x ≠ 0)
    {l₁ l₂ l : NF M} (h : l₁.eval / l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval / ((r₂, x) ::ᵣ l₂).eval = ((0, x) ::ᵣ l).eval := by
  rw [← hr]
  simp only [← h, eval_cons, zpow_sub₀ hx, div_eq_mul_inv, mul_inv, mul_zpow, zpow_neg, mul_assoc]
  congr! 1
  simp only [← mul_assoc]
  congr! 1
  rw [mul_comm]

theorem div_eq_eval₂' [CommGroupWithZero M] {r₁ r₂ : ℤ} (hr : r₁ - r₂ ≠ 0) (x : M)
    {l₁ l₂ l : NF M} (h : l₁.eval / l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval / ((r₂, x) ::ᵣ l₂).eval = ((r₁ - r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, sub_neg_eq_add, zpow_neg]
  obtain rfl | h := eq_or_ne x 0
  · rw [zero_zpow _ hr]
    obtain hr₁ | hr₂ : r₁ ≠ 0 ∨ r₂ ≠ 0 := by omega
    · simp [zero_zpow _ hr₁]
    · simp [zero_zpow _ hr₂]
  simp only [zpow_sub₀ h, mul_assoc]
  simp only [pow_add, div_eq_mul_inv, mul_inv, mul_assoc, inv_inv]
  congr! 1
  simp only [← mul_assoc]
  congr! 1
  rw [mul_comm]

theorem div_eq_eval₃ [DivisionCommMonoid M] {a₁ : ℤ × M} (a₂ : ℤ × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval / l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = ((-a₂.1, a₂.2) ::ᵣ l).eval := by
  simp only [eval_cons, zpow_neg, mul_inv, div_eq_mul_inv, ← h, ← mul_assoc]

theorem div_eq_eval [DivisionMonoid M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval / l₂.eval = l.eval) :
    x₁ / x₂ = l.eval := by
  rw [hx₁, hx₂, h]

instance : Inv (NF M) where
  inv l := l.map fun (a, x) ↦ (-a, x)

-- generalize library `List.prod_inv`
theorem _root_.List.prod_inv₀ {K : Type*} [DivisionCommMonoid K] :
    ∀ (L : List K), L.prod⁻¹ = (map (fun x ↦ x⁻¹) L).prod
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod_inv₀ xs]

theorem eval_inv [DivisionCommMonoid M] (l : NF M) : (l⁻¹).eval = l.eval⁻¹ := by
  simp only [NF.eval, List.map_map, List.prod'_inv₀, NF.instInv]
  congr
  ext p
  simp

theorem one_div_eq_eval [DivisionCommMonoid M] (l : NF M) : 1 / l.eval = (l⁻¹).eval := by
  simp [eval_inv]

theorem inv_eq_eval [DivisionCommMonoid M] {l : NF M} {x : M} (h : x = l.eval) :
    x⁻¹ = (l⁻¹).eval := by
  rw [h, eval_inv]

instance : Pow (NF M) ℤ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem zpow_apply (r : ℤ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) :=
  rfl

-- in the library somewhere?
theorem _root_.List.prod_zpow {β : Type*} [DivisionCommMonoid β] {r : ℤ} {l : List β} :
    l.prod ^ r = (map (fun x ↦ x ^ r) l).prod :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_zpow r⟩, (mul_zpow · · r)⟩
  map_list_prod fr l

theorem eval_zpow [DivisionCommMonoid M] {l : NF M} {x : M} (h : x = l.eval) (r : ℤ) :
    (l ^ r).eval = x ^ r := by
  unfold NF.eval at h ⊢
  simp only [h, List.prod'_zpow, map_map, NF.zpow_apply]
  congr
  ext p
  simp [← zpow_mul, mul_comm]

theorem zpow_eq_eval [DivisionCommMonoid M] {l : NF M} (r : ℤ) {x : M} (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [hx, eval_zpow]
  rfl

theorem zpow_zero_eq_eval [DivisionCommMonoid M] (x : M) : x ^ (0:ℤ) = NF.eval [] := by
  rw [zpow_zero, one_eq_eval]

instance : Pow (NF M) ℕ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem pow_apply (r : ℕ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) :=
  rfl

-- in the library somewhere?
theorem _root_.List.prod_pow {β : Type*} [CommMonoid β] {r : ℕ} {l : List β} :
    l.prod ^ r = (map (fun x ↦ x ^ r) l).prod :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_pow r⟩, (mul_pow · · r)⟩
  map_list_prod fr l

theorem eval_pow [DivisionCommMonoid M] {l : NF M} {x : M} (h : x = l.eval) (r : ℕ) :
    (l ^ r).eval = x ^ r := by
  unfold NF.eval at h ⊢
  simp only [h, prod'_pow, map_map, NF.pow_apply]
  congr! 2
  ext p
  dsimp
  rw [mul_comm, zpow_mul]
  norm_cast

theorem pow_eq_eval [DivisionCommMonoid M] {l : NF M} (r : ℕ) {x : M} (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [hx, eval_pow]
  rfl

theorem pow_zero_eq_eval [DivisionCommMonoid M] (x : M) : x ^ (0:ℕ) = NF.eval [] := by
  rw [pow_zero, one_eq_eval]

theorem eq_cons_cons [DivInvMonoid M] {r₁ r₂ : ℤ} (m : M) {l₁ l₂ : NF M} (h1 : r₁ = r₂)
    (h2 : l₁.eval = l₂.eval) :
    ((r₁, m) ::ᵣ l₁).eval = ((r₂, m) ::ᵣ l₂).eval := by
  simp only [NF.eval, NF.cons] at *
  simp [h1, h2]

theorem eq_cons_const [DivisionMonoid M] {r : ℤ} (m : M) {n : M} {l : NF M} (h1 : r = 0)
    (h2 : l.eval = n) :
    ((r, m) ::ᵣ l).eval = n := by
  simp only [NF.eval, NF.cons] at *
  simp [h1, h2]

theorem eq_const_cons [DivisionMonoid M] {r : ℤ} (m : M) {n : M} {l : NF M} (h1 : 0 = r)
    (h2 : n = l.eval) :
    n = ((r, m) ::ᵣ l).eval := by
  simp only [NF.eval, NF.cons] at *
  simp [← h1, h2]

theorem eq_of_eval_eq_eval [DivisionMonoid M]
    {l₁ l₂ : NF M} {l₁' : NF M} {l₂' : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁'.eval) (hx₂ : x₂ = l₂'.eval)
    (h₁ : l₁.eval = l₁'.eval) (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval = l₂.eval) :
    x₁ = x₂ := by
  rw [hx₁, hx₂, ← h₁, ← h₂, h]

end NF

variable {v : Level}

/-! ### Lists of expressions representing exponents and atoms, and operations on such lists -/

/-- Basic meta-code "normal form" object of the `field_simp` tactic: a type synonym
for a list of ordered triples comprising an expression representing a term of a type `M` (where
typically `M` is a field), together with an integer "power" and a natural number "index".

The natural number represents the index of the `M` term in the `AtomM` monad: this is not enforced,
but is sometimes assumed in operations.  Thus when items `((a₁, x₁), k)` and `((a₂, x₂), k)`
appear in two different `FieldSimp.qNF` objects (i.e. with the same `ℕ`-index `k`), it is expected
that the expressions `x₁` and `x₂` are the same.  It is also expected that the items in a
`FieldSimp.qNF` list are in strictly decreasing order by natural-number index.

By forgetting the natural number indices, an expression representing a `Mathlib.Tactic.FieldSimp.NF`
object can be built from a `FieldSimp.qNF` object; this construction is provided as
`Mathlib.Tactic.FieldSimp.qNF.toNF`. -/
abbrev qNF (M : Q(Type v)) := List ((ℤ × Q($M)) × ℕ)

namespace qNF

variable {M : Q(Type v)}

/-- Given `l` of type `qNF M`, i.e. a list of `(ℤ × Q($M)) × ℕ`s (two `Expr`s and a natural
number), build an `Expr` representing an object of type `NF M` (i.e. `List (ℤ × M)`) in the
in the obvious way: by forgetting the natural numbers and gluing together the integers and `Expr`s.
-/
def toNF (l : qNF M) : Q(NF $M) :=
  let l' : List Q(ℤ × $M) := (l.map Prod.fst).map (fun (a, x) ↦ q(($a, $x)))
  let qt : List Q(ℤ × $M) → Q(List (ℤ × $M)) := List.rec q([]) (fun e _ l ↦ q($e ::ᵣ $l))
  qt l'

/-- Given `l` of type `qNF M`, i.e. a list of `(ℤ × Q($M)) × ℕ`s (two `Expr`s and a natural
number), apply an expression representing a function with domain `ℤ` to each of the `ℤ`
components. -/
def onExponent (l : qNF M) (f : ℤ → ℤ) : qNF M :=
  l.map fun ((a, x), k) ↦ ((f a, x), k)

/-- Build a transparent expression for the product of powers represented by `l : qNF M`. -/
def evalPrettyMonomial (iM : Q(Field $M)) (r : ℤ) (x : Q($M)) :
    MetaM (Σ e : Q($M), Q($x ^ $r = $e)) := do
  match r with
  | 0 => unreachable! -- design of tactic is supposed to prevent this, let's panic if we see it
  | 1 => return ⟨x, q(zpow_one $x)⟩
  | .ofNat r => return ⟨q($x ^ $r), q(zpow_natCast $x $r)⟩
  | r => return ⟨q($x ^ $r), q(rfl)⟩

/-- Build a transparent expression for the product of powers represented by `l : qNF M`. -/
def evalPretty (iM : Q(Field $M)) (l : qNF M) : MetaM (Σ e : Q($M), Q(NF.eval $(l.toNF) = $e)) := do
  match l with
  | [] => return ⟨q(1), q(rfl)⟩
  | [((r, x), _)] =>
    let ⟨e, pf⟩ ← evalPrettyMonomial iM r x
    return ⟨e, q(Eq.trans (one_mul _) $pf)⟩
  | ((r, x), _) :: t =>
    let ⟨e, pf_e⟩ ← evalPrettyMonomial iM r x
    let ⟨t', pf⟩ ← evalPretty iM t
    return ⟨q($t' * $e), (q(congr_arg₂ HMul.hMul $pf $pf_e):)⟩

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), construct another such term `l`, which will have the property that in
the field `$M`, the product of the "multiplicative linear combinations" represented by `l₁` and
`l₂` is the multiplicative linear combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly decreasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the two lists, except that if pairs `(a₁, x₁)` and `(a₂, x₂)`
appear in `l₁`, `l₂` respectively with the same `ℕ`-component `k`, then contribute a term
`(a₁ + a₂, x₁)` to the output list with `ℕ`-component `k`. -/
def mul : qNF M → qNF M → qNF M
  | [], l => l
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      ((a₁, x₁), k₁) :: mul t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      if a₁ + a₂ = 0 then
        mul t₁ t₂
      else
        ((a₁ + a₂, x₁), k₁) :: mul t₁ t₂
    else
      ((a₂, x₂), k₂) :: mul (((a₁, x₁), k₁) :: t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), recursively construct a proof that in the field `$M`, the product of
the "multiplicative linear combinations" represented by `l₁` and `l₂` is the multiplicative linear
combination represented by `FieldSimp.qNF.mul l₁ l₁`. -/
def mkMulProof (iM : Q(Field $M)) (l₁ l₂ : qNF M) :
    Q((NF.eval $(l₁.toNF)) * NF.eval $(l₂.toNF) = NF.eval $((qNF.mul l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(one_mul (NF.eval $(l.toNF))):)
  | l, [] => (q(mul_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkMulProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.mul_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkMulProof iM t₁ t₂
      if a₁ + a₂ = 0 then
        -- how do you quote a proof of a `ℤ` equality?
        let h : Q($a₁ + $a₂ = 0) := (q(Eq.refl (0:ℤ)):)
        let hx₁ : Q($x₁ ≠ 0) := q(sorry) -- use the discharger here
        (q(NF.mul_eq_eval₂ $h $x₁ $hx₁ $pf):)
      else
        -- how do you quote a proof of a `ℤ` disequality?
        let z : Q(decide ($a₁ + $a₂ ≠ 0) = true) := (q(Eq.refl true):)
        let h : Q($a₁ + $a₂ ≠ 0) := q(of_decide_eq_true $z)
        (q(NF.mul_eq_eval₂' $h $x₁ $pf):)
    else
      let pf := mkMulProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.mul_eq_eval₃ ($a₂, $x₂) $pf):)

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), construct another such term `l`, which will have the property that in
the field `$M`, the quotient of the "multiplicative linear combinations" represented by `l₁` and
`l₂` is the multiplicative linear combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly decreasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the first list and the negation of the second list, except
that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with the same
`ℕ`-component `k`, then contribute a term `(a₁ - a₂, x₁)` to the output list with `ℕ`-component `k`.
-/
def div : qNF M → qNF M → qNF M
  | [], l => l.onExponent Neg.neg
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      ((a₁, x₁), k₁) :: div t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      if a₁ - a₂ = 0 then
        div t₁ t₂
      else
        ((a₁ - a₂, x₁), k₁) :: div t₁ t₂
    else
      ((-a₂, x₂), k₂) :: div (((a₁, x₁), k₁) :: t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), recursively construct a proof that in the field `$M`, the quotient
of the "multiplicative linear combinations" represented by `l₁` and `l₂` is the multiplicative
linear combination represented by `FieldSimp.qNF.div l₁ l₁`. -/
def mkDivProof (iM : Q(Field $M)) (l₁ l₂ : qNF M) :
    Q(NF.eval $(l₁.toNF) / NF.eval $(l₂.toNF) = NF.eval $((qNF.div l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(NF.one_div_eq_eval $(l.toNF)):)
  | l, [] => (q(div_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkDivProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.div_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkDivProof iM t₁ t₂
      if a₁ - a₂ = 0 then
        -- how do you quote a proof of a `ℤ` equality?
        let h : Q($a₁ - $a₂ = 0) := (q(Eq.refl (0:ℤ)):)
        let hx₁ : Q($x₁ ≠ 0) := q(sorry) -- use the discharger here
        (q(NF.div_eq_eval₂ $h $x₁ $hx₁ $pf):)
      else
        -- how do you quote a proof of a `ℤ` disequality?
        let z : Q(decide ($a₁ - $a₂ ≠ 0) = true) := (q(Eq.refl true):)
        let h : Q($a₁ - $a₂ ≠ 0) := q(of_decide_eq_true $z)
        (q(NF.div_eq_eval₂' $h $x₁ $pf):)
    else
      let pf := mkDivProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.div_eq_eval₃ ($a₂, $x₂) $pf):)

-- minimum of the
partial /- TODO figure out why! -/ def minimum : qNF M → qNF M → qNF M
| [], [] => []
| [], ((n, e), i) :: rest | ((n, e), i) :: rest, [] =>
  if 0 ≤ n then (minimum [] rest) else ((n, e), i) :: (minimum [] rest)
| ((n, e), i) :: rest, ((n', e'), i') :: rest' =>
    -- should factor into a separate definition
    if i > i' then
      if 0 ≤ n then minimum rest (((n', e'), i') :: rest')
      else ((n, e), i) :: minimum rest (((n', e'), i') :: rest')
    else if i = i' then
      ((min n n', e), i) :: minimum rest rest'
    else
      if 0 ≤ n' then minimum rest' (((n, e), i) :: rest)
      else ((n', e'), i') :: minimum rest' (((n, e), i) :: rest)

end qNF

/-! ### Core of the `field_simp` tactic -/

variable {M : Q(Type v)}

/-- The main algorithm behind the `field_simp` tactic: partially-normalizing an
expression in a field `M` into the form x1 ^ c1 * x2 ^ c2 * ... x_k ^ c_k,
where x1, x2, ... are distinct atoms in `M`, and c1, c2, ... are integers.

Possible TODO, if poor performance on large problems is witnessed: switch the implementation from
`AtomM` to `CanonM`, per the discussion
https://github.com/leanprover-community/mathlib4/pull/16593/files#r1749623191 -/
partial def normalize (iM : Q(Field $M)) (x : Q($M)) :
    AtomM (Σ l : qNF M, Q($x = NF.eval $(l.toNF))) := do
  let baseCase (y : Q($M)) : AtomM (Σ l : qNF M, Q($y = NF.eval $(l.toNF))):= do
    let (k, ⟨x', _⟩) ← AtomM.addAtomQ y
    trace[debug] "{y} is the {k}-th atom"
    pure ⟨[((1, x'), k)], q(NF.atom_eq_eval $x')⟩
  match x with
  /- normalize a multiplication: `x₁ * x₂` -/
  | ~q($x₁ * $x₂) =>
    let ⟨l₁, pf₁⟩ ← normalize iM x₁
    let ⟨l₂, pf₂⟩ ← normalize iM x₂
    -- build the new list and proof
    let pf := qNF.mkMulProof iM l₁ l₂
    pure ⟨qNF.mul l₁ l₂, (q(NF.mul_eq_eval $pf₁ $pf₂ $pf):)⟩
  /- normalize a division: `x₁ / x₂` -/
  | ~q($x₁ / $x₂) =>
    let ⟨l₁, pf₁⟩ ← normalize iM x₁
    let ⟨l₂, pf₂⟩ ← normalize iM x₂
    -- build the new list and proof
    let pf := qNF.mkDivProof iM l₁ l₂
    pure ⟨qNF.div l₁ l₂, (q(NF.div_eq_eval $pf₁ $pf₂ $pf):)⟩
  /- normalize a inversion: `y⁻¹` -/
  | ~q($y⁻¹) =>
    let ⟨l, pf⟩ ← normalize iM y
    -- build the new list and proof
    pure ⟨l.onExponent Neg.neg, (q(NF.inv_eq_eval $pf):)⟩
  | ~q($a + $b) =>
    let ⟨l₁, pf₁⟩ ← normalize iM a
    let ⟨l₂, pf₂⟩ ← normalize iM b
    let L : qNF M := qNF.minimum l₁ l₂
    let l₁' := qNF.div l₁ L -- write `l₁ = l₁' * L`, pr₁' is a proof of that
    let l₂' := qNF.div l₂ L
    let ⟨e₁, _⟩ ← qNF.evalPretty iM l₁'
    let ⟨e₂, _⟩ ← qNF.evalPretty iM l₂'
    let e : Q($M) := q($e₁ + $e₂)
    let ⟨sum, _pf⟩ ← baseCase e
    pure ⟨qNF.mul L sum, q(sorry)⟩
  /- normalize an integer exponentiation: `y ^ (s : ℤ)` -/
  | ~q($y ^ ($s : ℤ)) =>
    let some s := Expr.int? s | baseCase x
    if s = 0 then
      pure ⟨[], (q(NF.zpow_zero_eq_eval $y):)⟩
    else
      let ⟨l, pf⟩ ← normalize iM y
      -- build the new list and proof
      pure ⟨l.onExponent (HMul.hMul s), (q(NF.zpow_eq_eval $s $pf):)⟩
  /- normalize an integer exponentiation: `y ^ (s : ℤ)` -/
  | ~q($y ^ ($s : ℕ)) =>
    let some s := Expr.nat? s | baseCase x
    if s = 0 then
      pure ⟨[], (q(NF.pow_zero_eq_eval $y):)⟩
    else
      let ⟨l, pf⟩ ← normalize iM y
      -- build the new list and proof
      pure ⟨l.onExponent (HMul.hMul s), (q(NF.pow_eq_eval $s $pf):)⟩
  /- normalize a `(1:M)` -/
  | ~q(1) => pure ⟨[], q(NF.one_eq_eval $M)⟩
  /- anything else should be treated as an atom -/
  | _ => baseCase x

open Elab Tactic

/-- Conv tactic for field_simp normalisation.
Wraps the `MetaM` normalization function `normalize`. -/
elab "field_simp2" : conv => do
  -- find the expression `x` to `conv` on
  let x ← Conv.getLhs
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, _⟩ ← inferTypeQ' x
  -- find a `Field` instance on `K`
  let iK : Q(Field $K) ← synthInstanceQ q(Field $K)
  -- run the core normalization function `normalize` on `x`
  let ⟨l, pf⟩ ← AtomM.run .reducible <| normalize iK x
  let ⟨e, pf'⟩ ← l.evalPretty iK
  -- convert `x` to the output of the normalization
  Conv.applySimpResult { expr := e, proof? := some (← mkAppM `Eq.trans #[pf, pf']) }

end Mathlib.Tactic.FieldSimp

open Mathlib.Tactic.FieldSimp

variable {x y z : ℚ}

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => (1 : ℚ)

-- Combining powers of a single atom.
section singleAtom

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x ^ 0

/-- info: x -/
#guard_msgs in
#conv field_simp2 => x ^ 1

/-- info: x -/
#guard_msgs in
#conv field_simp2 => x

/-- info: x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x ^ 2

/-- info: x ^ 3 -/
#guard_msgs in
#conv field_simp2 => x ^ 1 * x ^ 2

/-- info: x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x * x

/-- info: x ^ 45 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x ^ 42

-- Inverses and exponent -1 are normalised to the same output.
/-- info: x ^ (-1) -/
#guard_msgs in
#conv field_simp2 => x⁻¹

/-- info: x ^ (-1) -/
#guard_msgs in
#conv field_simp2 => x ^ (-1 : ℤ)

-- Exponents in ℕ and ℤ are treated the same.
/-- info: x ^ 5 -/
#guard_msgs in
#conv field_simp2 => x ^ 2 * x ^ (3 : ℤ)

/-- info: x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x ^ (1 : ℤ) * x

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x ^ (0 : ℤ)

/-- info: x ^ (-3) -/
#guard_msgs in
#conv field_simp2 => x ^ (-1 : ℤ) * x ^ (-2 : ℤ)

/-- info: x ^ (-3) -/
#guard_msgs in
#conv field_simp2 => x⁻¹ ^ 1 * x⁻¹ ^ 2

section -- variable exponents are not supported

variable {k : ℤ}

/-- info: x ^ k * x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x ^ k * x ^ 2

/-- info: x ^ k * x ^ (-k) -/
#guard_msgs in
#conv field_simp2 => x ^ k * x ^ (-k)

end

section cancellation

-- If the exponents for a single atom do not add to zero, we can always cancel them.
/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x * x⁻¹

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x⁻¹ * x

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x / x

/-- info: x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x⁻¹

/-- info: x ^ (-3) -/
#guard_msgs in
#conv field_simp2 => x / x ^ 4

/-- info: x ^ (-31) -/
#guard_msgs in
#conv field_simp2 => x * x ^5 * x⁻¹ ^ 37

-- This also holds if the exponents added up to zero at some intermediate stage.
/-- info: x -/
#guard_msgs in
#conv field_simp2 => x * x ^ 2 * x ^ (-2 : ℤ)

/-- info: x -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x ^ (-3 : ℤ) * x

/-- info: x -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x⁻¹ ^ 3 * x

-- Some atom "in the middle" does not inhibit cancellation.
/-- info: x ^ 3 * y ^ 4 -/
#guard_msgs in
#conv field_simp2 => x ^ 2 * y ^ 2 * x⁻¹ * y ^ 2 * x ^ (-1 : ℤ) * x ^ 3

/-- info: x ^ 2 * y ^ 2 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x⁻¹ * y ^ 2 * x⁻¹ * x ^ (-1 : ℤ) * x ^ 2

-- If x could be zero, we cannot cancel a term `x * x⁻¹`.
-- However, we can simplify e.g. `x ^ 3 * x ^ (-3)` to `x * x⁻¹`.

-- TODO: right now, we always cancel (which we should not do!!)
/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x ^ 17 * x ^ (-17 : ℤ)

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x⁻¹ ^ 3

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x ^ (-2 : ℤ) * x⁻¹

-- If x is non-zero, we do cancel.
section docancel

variable {hx : x ≠ 0}

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x * x⁻¹

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x⁻¹ * x

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x / x

/-- info: x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x⁻¹

/-- info: x ^ (-3) -/
#guard_msgs in
#conv field_simp2 => x / x ^ 4

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x ^ 17 * x ^ (-17 : ℤ)

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x⁻¹ ^ 3

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x ^ (-2 : ℤ) * x⁻¹

end docancel

end cancellation

end singleAtom

-- Combining cancellation across multiple atoms.
section

/-- info: x ^ 3 * y ^ 4 -/
#guard_msgs in
#conv field_simp2 => x ^ 1 * y * x ^ 2 * y ^ 3

/-- info: x ^ 3 -/
#guard_msgs in
#conv field_simp2 => x ^ 1 * y * x ^ 2 * y⁻¹

variable {y' : ℚ} (hy' : y' ≠ 0)

/-- info: x ^ 3 -/
#guard_msgs in
#conv field_simp2 => x ^ 1 * y * x ^ 2 * y⁻¹

-- TODO: is wrong, cannot prove the atom is non-zero
/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => (x * y) / (y * x)

section

variable {h : x * y ≠ 0}
/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => (x * y) / (y * x)

end

section -- Inferring non-zeroness from non-zeroness of each factor.

section
variable {hx : x ≠ 0} {hy : y ≠ 0}
/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => (x * y) / (y * x)
end

section

variable {hx : x ≠ 0} {h' : y * z ≠ 0}
/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => (x * y * z) / (y * z * x)

end

end

end

/-- info: x + y -/
#guard_msgs in
#conv field_simp2 => x + y

/-- info: x * y -/
#guard_msgs in
#conv field_simp2 => x * y



/-- info: x * (y + 1) -/
#guard_msgs in
#conv field_simp2 => x * y + x * 1

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => (x * y) * (y * x)⁻¹

/-- info: y -/
#guard_msgs in
#conv field_simp2 => x ^ (0:ℤ) * y

/-- info: y ^ 2 -/
#guard_msgs in
#conv field_simp2 => y * (y + x) ^ (0:ℤ) * y

/-- info: x * y ^ (-1) -/
#guard_msgs in
#conv field_simp2 => x / y

/-- info: (x + 1) ^ (-1) * (y + 1) ^ (-1) * (x * (y + 1) + (x + 1) * y) -/
#guard_msgs in
#conv field_simp2 => x / (x + 1) + y / (y + 1)

example : (1 : ℚ) = 1 := by
  conv_lhs => field_simp2

example : x = x := by
  conv_lhs => field_simp2

example : x * y = x * y := by
  conv_lhs => field_simp2

example : x / y = x * y ^ (-1:ℤ) := by
  conv_lhs => field_simp2

example : x / (y / x) = x ^ 2 * y ^ (-1:ℤ) := by
  conv_lhs => field_simp2

example : x / (y ^ (-3:ℤ) / x) = x ^ 2 * y ^ 3 := by
  conv_lhs => field_simp2

example : (x / y ^ (-3:ℤ)) * x = x ^ 2 * y ^ 3 := by
  conv_lhs => field_simp2

example : (x * y) / (y * x) = 1 := by
  conv_lhs => field_simp2

example : (x * y) * (y * x)⁻¹ = 1 := by
  conv_lhs => field_simp2

example : x ^ (0:ℤ) * y = y := by
  conv_lhs => field_simp2

example : y * (y + x) ^ (0:ℤ) * y = y ^ 2 := by
  conv_lhs => field_simp2

example : x * y * z = x * y * z := by
  conv_lhs => field_simp2

example : x * y + x * z = x * (y + z) := by
  conv_lhs => field_simp2

example : x / (x * y + x * z) = (y + z) ^ (-1:ℤ) := by
  conv_lhs => field_simp2

example : ((x ^ (2:ℤ)) ^ 3) = x ^ 6 := by
  conv_lhs => field_simp2

example : x ^ 3 * x⁻¹ = x ^ 2 := by
  conv_lhs => field_simp2

example : x / x ^ 4 = x ^ (-3:ℤ) := by
  conv_lhs => field_simp2

example : x ^ 1 * x ^ 2 = x ^ 3 := by
  conv_lhs => field_simp2

example : x * x = x ^ 2 := by
  conv_lhs => field_simp2

example : x ^ 3 * x ^ 42 = x ^ 45 := by
  conv_lhs => field_simp2
