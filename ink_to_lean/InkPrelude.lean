/-
  Ink value semantics in core Lean 4 (no Mathlib), for laws exported by
  ink-to-lean. Each definition follows the reduction rules of Ink's semantic
  law kernel (core/src/laws.rs and core/src/owned_semantic.rs):

  * u32/u64/i32 are UInt32/UInt64/Int32 (wrapping), Int is Int.
  * Lists are List; buffers are their frozen list.
  * Option is Option; Result T E is Except E T.
  * Local maps are sorted association lists without duplicate keys (Ink's
    maps are BTreeMaps), with Ink's insertion, lookup and removal.
  * `foldr`/`foldl` callbacks take the item first, then the accumulator.
  * `sum` of words folds from the right; `scan` is the inclusive prefix sum;
    `sort` is Ink's stable insertion sort.

  This file is the trusted bridge of an export: a law proved in Lean is a
  statement about these definitions.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Ink

abbrev foldr {α β : Type} (xs : List α) (init : β) (f : α → β → β) : β :=
  List.foldr f init xs

abbrev foldl {α β : Type} (xs : List α) (init : β) (f : α → β → β) : β :=
  List.foldl (fun acc x => f x acc) init xs

def foldUntil {α β : Type} : List α → β → (α → β → Bool) → (α → β → β) → β
  | [], init, _, _ => init
  | h :: t, init, stop, step =>
    if stop h init then step h init else foldUntil t (step h init) stop step

abbrev length {α : Type} (xs : List α) : UInt32 := xs.length.toUInt32

abbrev atOr {α : Type} (xs : List α) (i : UInt32) (d : α) : α := xs.getD i.toNat d

abbrev mapIdx {α β : Type} (f : UInt32 → α → β) (xs : List α) : List β :=
  xs.mapIdx (fun i x => f i.toUInt32 x)

def sumR {α : Type} [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | h :: t => h + sumR t

def sumL {α : Type} [Add α] [OfNat α 0] (xs : List α) : α :=
  List.foldl (· + ·) 0 xs

def scanFrom {α : Type} [Add α] : List α → α → List α
  | [], _ => []
  | h :: t, acc => (acc + h) :: scanFrom t (acc + h)

abbrev scan {α : Type} [Add α] [OfNat α 0] (xs : List α) : List α := scanFrom xs 0

def insertSorted {α : Type} [LE α] [DecidableRel (α := α) (· ≤ ·)] (x : α) : List α → List α
  | [] => [x]
  | h :: t => if x ≤ h then x :: h :: t else h :: insertSorted x t

def sort {α : Type} [LE α] [DecidableRel (α := α) (· ≤ ·)] : List α → List α
  | [] => []
  | h :: t => insertSorted h (sort t)

def repeatN {α : Type} : Nat → α → (UInt32 → α → α) → α
  | 0, init, _ => init
  | n + 1, init, f => f n.toUInt32 (repeatN n init f)

abbrev foldOption {α β : Type} (o : Option α) (some : α → β) (none : Unit → β) : β :=
  match o with
  | .some v => some v
  | .none => none ()

abbrev foldResult {α ε β : Type} (r : Except ε α) (ok : α → β) (err : ε → β) : β :=
  match r with
  | .ok v => ok v
  | .error e => err e

abbrev choose {α : Type} (c : Bool) (a b : α) : α := if c then a else b

structure Vec2 (α : Type) where
  x : α
  y : α
deriving Repr

structure Vec3 (α : Type) where
  x : α
  y : α
  z : α
deriving Repr

structure Vec4 (α : Type) where
  x : α
  y : α
  z : α
  w : α
deriving Repr

/-- A local map: keys ascending, unique, as Ink's ordered maps. -/
abbrev Map (κ ν : Type) := List (κ × ν)

namespace Map
variable {κ ν : Type} [BEq κ] [LT κ] [DecidableRel (α := κ) (· < ·)]

def empty : Map κ ν := []

def set : Map κ ν → κ → ν → Map κ ν
  | [], k, v => [(k, v)]
  | (j, w) :: rest, k, v =>
    if k == j then (k, v) :: rest
    else if k < j then (k, v) :: (j, w) :: rest
    else (j, w) :: set rest k v

def getOr : Map κ ν → κ → ν → ν
  | [], _, d => d
  | (j, w) :: rest, k, d => if k == j then w else getOr rest k d

def contains : Map κ ν → κ → Bool
  | [], _ => false
  | (j, _) :: rest, k => if k == j then true else contains rest k

/-- Removes the key's binding. Ink's maps hold each key once, so removing
every matching entry agrees with Ink on every map Ink can build. -/
def remove (m : Map κ ν) (k : κ) : Map κ ν := m.filter (fun p => !(p.1 == k))

def keys (m : Map κ ν) : List κ := m.map (·.1)
def values (m : Map κ ν) : List ν := m.map (·.2)
def len (m : Map κ ν) : UInt32 := m.length.toUInt32

variable [LawfulBEq κ]

@[simp] theorem getOr_set_self (m : Map κ ν) (k : κ) (v d : ν) :
    getOr (set m k v) k d = v := by
  induction m with
  | nil => simp [set, getOr]
  | cons p rest ih =>
    obtain ⟨j, w⟩ := p
    by_cases h : k = j
    · subst h; simp [set, getOr]
    · by_cases l : k < j <;> simp_all [set, getOr]

@[simp] theorem getOr_set_other (m : Map κ ν) (k j : κ) (v d : ν) (h : (j == k) = false) :
    getOr (set m k v) j d = getOr m j d := by
  have hne : j ≠ k := by simpa using h
  induction m with
  | nil => simp [set, getOr, hne]
  | cons p rest ih =>
    obtain ⟨i, w⟩ := p
    by_cases hk : k = i
    · subst hk; simp [set, getOr, hne]
    · by_cases l : k < i <;> simp_all [set, getOr]

@[simp] theorem contains_set_self (m : Map κ ν) (k : κ) (v : ν) :
    contains (set m k v) k = true := by
  induction m with
  | nil => simp [set, contains]
  | cons p rest ih =>
    obtain ⟨j, w⟩ := p
    by_cases h : k = j
    · subst h; simp [set, contains]
    · by_cases l : k < j <;> simp_all [set, contains]

@[simp] theorem getOr_remove_self (m : Map κ ν) (k : κ) (d : ν) :
    getOr (remove m k) k d = d := by
  induction m with
  | nil => simp [remove, getOr]
  | cons p rest ih =>
    obtain ⟨j, w⟩ := p
    by_cases h : j = k
    · subst h; simp_all [remove]
    · have hj : (j == k) = false := by simpa using h
      have hk : (k == j) = false := by
        rw [beq_eq_false_iff_ne]; exact fun e => h e.symm
      simp only [remove, List.filter_cons, hj, Bool.not_false, ite_true] at ih ⊢
      simp [getOr, hk, ih]

@[simp] theorem getOr_empty (k : κ) (d : ν) : getOr (empty : Map κ ν) k d = d := rfl
@[simp] theorem contains_empty (k : κ) : contains (empty : Map κ ν) k = false := rfl

end Map

/-- Exact conversions to Int. -/
abbrev intOfU32 (x : UInt32) : Int := Int.ofNat x.toNat
abbrev intOfU64 (x : UInt64) : Int := Int.ofNat x.toNat
abbrev intOfI32 (x : Int32) : Int := x.toInt

/-- Total division: a zero divisor (or i32 minimum / -1) selects the fallback. -/
abbrev quotOrU32 (a b fallback : UInt32) : UInt32 := if b = 0 then fallback else a / b
abbrev remOrU32 (a b fallback : UInt32) : UInt32 := if b = 0 then fallback else a % b
abbrev quotOrU64 (a b fallback : UInt64) : UInt64 := if b = 0 then fallback else a / b
abbrev remOrU64 (a b fallback : UInt64) : UInt64 := if b = 0 then fallback else a % b
abbrev quotOrI32 (a b fallback : Int32) : Int32 :=
  if b = 0 ∨ (a = Int32.minValue ∧ b = -1) then fallback else a / b
abbrev remOrI32 (a b fallback : Int32) : Int32 :=
  if b = 0 ∨ (a = Int32.minValue ∧ b = -1) then fallback else a % b

end Ink

/-- Leaf automation for exported proofs: computation, hypotheses as rewrites,
and ring/linear arithmetic (the counterpart of Ink's `normalize`). -/
macro "ink_auto" : tactic =>
  `(tactic| first
    | with_reducible rfl
    | (simp_all [Ink.Map.getOr_set_self, Ink.Map.getOr_set_other, Ink.Map.contains_set_self, Ink.Map.getOr_remove_self]; done)
    | (simp_all [Ink.foldUntil, Ink.sumR, Ink.scanFrom, Ink.insertSorted, Ink.sort, Ink.repeatN]; done)
    | grind
    | (simp_all <;> grind)
    | omega)
