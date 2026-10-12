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

namespace InkLaws

theorem filter_append {E : Type} (p : (E → Bool)) (xs : (List E)) (ys : (List E)) :
    (List.filter (fun (x0 : E) => (p x0)) (xs ++ ys)) = ((List.filter (fun (x1 : E) => (p x1)) xs) ++ (List.filter (fun (x2 : E) => (p x2)) ys)) := by
  induction xs with
  | nil =>
      ink_auto
  | cons h t ih =>
      cases hc : (p h) with
      | false =>
          ink_auto
      | true =>
          ink_auto

@[simp] def no_groups  : (Ink.Map UInt64 Int) :=
  (Ink.Map.empty : (Ink.Map UInt64 Int))

theorem group_sum_append {E : Type} (amount : (E → Int)) (k : UInt64) (key : (E → UInt64)) (xs : (List E)) (ys : (List E)) :
    (Ink.Map.getOr (Ink.foldr (xs ++ ys) no_groups (fun (x0 : E) => (fun (x1 : (Ink.Map UInt64 Int)) => (Ink.Map.set x1 (key x0) ((Ink.Map.getOr x1 (key x0) (0 : Int)) + (amount x0)))))) k (0 : Int)) = ((Ink.Map.getOr (Ink.foldr xs no_groups (fun (x2 : E) => (fun (x3 : (Ink.Map UInt64 Int)) => (Ink.Map.set x3 (key x2) ((Ink.Map.getOr x3 (key x2) (0 : Int)) + (amount x2)))))) k (0 : Int)) + (Ink.Map.getOr (Ink.foldr ys no_groups (fun (x4 : E) => (fun (x5 : (Ink.Map UInt64 Int)) => (Ink.Map.set x5 (key x4) ((Ink.Map.getOr x5 (key x4) (0 : Int)) + (amount x4)))))) k (0 : Int))) := by
  induction xs generalizing k with
  | nil =>
      ink_auto
  | cons h t ih =>
      cases hc : (k == (key h)) with
      | false =>
          calc _ = (Ink.Map.getOr (Ink.foldr (t ++ ys) no_groups (fun (x6 : E) => (fun (x7 : (Ink.Map UInt64 Int)) => (Ink.Map.set x7 (key x6) ((Ink.Map.getOr x7 (key x6) (0 : Int)) + (amount x6)))))) k (0 : Int)) := by
                ink_auto
            _ = _ := by
                calc _ = ((Ink.Map.getOr (Ink.foldr t no_groups (fun (x8 : E) => (fun (x9 : (Ink.Map UInt64 Int)) => (Ink.Map.set x9 (key x8) ((Ink.Map.getOr x9 (key x8) (0 : Int)) + (amount x8)))))) k (0 : Int)) + (Ink.Map.getOr (Ink.foldr ys no_groups (fun (x10 : E) => (fun (x11 : (Ink.Map UInt64 Int)) => (Ink.Map.set x11 (key x10) ((Ink.Map.getOr x11 (key x10) (0 : Int)) + (amount x10)))))) k (0 : Int))) := by
                      ink_auto
                  _ = _ := by
                      ink_auto
      | true =>
          have heq : k = (key h) := by
            have hb : (k == (key h)) = true := by
              ink_auto
            simpa using hb
          calc _ = ((Ink.Map.getOr (Ink.foldr (t ++ ys) no_groups (fun (x12 : E) => (fun (x13 : (Ink.Map UInt64 Int)) => (Ink.Map.set x13 (key x12) ((Ink.Map.getOr x13 (key x12) (0 : Int)) + (amount x12)))))) (key h) (0 : Int)) + (amount h)) := by
                ink_auto
            _ = _ := by
                calc _ = (((Ink.Map.getOr (Ink.foldr t no_groups (fun (x14 : E) => (fun (x15 : (Ink.Map UInt64 Int)) => (Ink.Map.set x15 (key x14) ((Ink.Map.getOr x15 (key x14) (0 : Int)) + (amount x14)))))) (key h) (0 : Int)) + (Ink.Map.getOr (Ink.foldr ys no_groups (fun (x16 : E) => (fun (x17 : (Ink.Map UInt64 Int)) => (Ink.Map.set x17 (key x16) ((Ink.Map.getOr x17 (key x16) (0 : Int)) + (amount x16)))))) (key h) (0 : Int))) + (amount h)) := by
                      ink_auto
                  _ = _ := by
                      ink_auto

theorem filtered_group_sum_append {E : Type} (amount : (E → Int)) (k : UInt64) (key : (E → UInt64)) (p : (E → Bool)) (xs : (List E)) (ys : (List E)) :
    (Ink.Map.getOr (Ink.foldr (List.filter (fun (x0 : E) => (p x0)) (xs ++ ys)) no_groups (fun (x1 : E) => (fun (x2 : (Ink.Map UInt64 Int)) => (Ink.Map.set x2 (key x1) ((Ink.Map.getOr x2 (key x1) (0 : Int)) + (amount x1)))))) k (0 : Int)) = ((Ink.Map.getOr (Ink.foldr (List.filter (fun (x3 : E) => (p x3)) xs) no_groups (fun (x4 : E) => (fun (x5 : (Ink.Map UInt64 Int)) => (Ink.Map.set x5 (key x4) ((Ink.Map.getOr x5 (key x4) (0 : Int)) + (amount x4)))))) k (0 : Int)) + (Ink.Map.getOr (Ink.foldr (List.filter (fun (x6 : E) => (p x6)) ys) no_groups (fun (x7 : E) => (fun (x8 : (Ink.Map UInt64 Int)) => (Ink.Map.set x8 (key x7) ((Ink.Map.getOr x8 (key x7) (0 : Int)) + (amount x7)))))) k (0 : Int))) := by
  calc _ = (Ink.Map.getOr (Ink.foldr ((List.filter (fun (x9 : E) => (p x9)) xs) ++ (List.filter (fun (x10 : E) => (p x10)) ys)) no_groups (fun (x11 : E) => (fun (x12 : (Ink.Map UInt64 Int)) => (Ink.Map.set x12 (key x11) ((Ink.Map.getOr x12 (key x11) (0 : Int)) + (amount x11)))))) k (0 : Int)) := by
        have hc8_0 := @filter_append E p xs ys
        ink_auto
    _ = _ := by
        have h := @group_sum_append E amount k key (List.filter (fun (x13 : E) => (p x13)) xs) (List.filter (fun (x14 : E) => (p x14)) ys)
        first | exact h | (simp only at h ⊢; exact h) | (simp_all; done) | ink_auto

theorem group_count_append {E : Type} (k : UInt64) (key : (E → UInt64)) (sign : (E → Int)) (xs : (List E)) (ys : (List E)) :
    (Ink.Map.getOr (Ink.foldr (xs ++ ys) no_groups (fun (x0 : E) => (fun (x1 : (Ink.Map UInt64 Int)) => (Ink.Map.set x1 (key x0) ((Ink.Map.getOr x1 (key x0) (0 : Int)) + (sign x0)))))) k (0 : Int)) = ((Ink.Map.getOr (Ink.foldr xs no_groups (fun (x2 : E) => (fun (x3 : (Ink.Map UInt64 Int)) => (Ink.Map.set x3 (key x2) ((Ink.Map.getOr x3 (key x2) (0 : Int)) + (sign x2)))))) k (0 : Int)) + (Ink.Map.getOr (Ink.foldr ys no_groups (fun (x4 : E) => (fun (x5 : (Ink.Map UInt64 Int)) => (Ink.Map.set x5 (key x4) ((Ink.Map.getOr x5 (key x4) (0 : Int)) + (sign x4)))))) k (0 : Int))) := by
  have h := @group_sum_append E sign k key xs ys
  first | exact h | (simp only at h ⊢; exact h) | (simp_all; done) | ink_auto

theorem sum_append {E : Type} (a : (E → Int)) (xs : (List E)) (ys : (List E)) :
    (Ink.foldr (xs ++ ys) (Ink.intOfU64 (0 : UInt64)) (fun (x0 : E) => (fun (x1 : Int) => ((a x0) + x1)))) = ((Ink.foldr xs (Ink.intOfU64 (0 : UInt64)) (fun (x2 : E) => (fun (x3 : Int) => ((a x2) + x3)))) + (Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x4 : E) => (fun (x5 : Int) => ((a x4) + x5))))) := by
  induction xs with
  | nil =>
      ink_auto
  | cons xs_head xs_tail ih =>
      ink_auto

theorem join_sum_append_left {L R : Type} (dxs : (List L)) (lk : (L → UInt64)) (rk : (R → UInt64)) (w : (L → (R → Int))) (xs : (List L)) (ys : (List R)) :
    (Ink.foldr (xs ++ dxs) (Ink.intOfU64 (0 : UInt64)) (fun (x0 : L) => (fun (x1 : Int) => ((Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x2 : R) => (fun (x3 : Int) => ((if ((lk x0) == (rk x2)) then ((w x0) x2) else (0 : Int)) + x3)))) + x1)))) = ((Ink.foldr xs (Ink.intOfU64 (0 : UInt64)) (fun (x4 : L) => (fun (x5 : Int) => ((Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x6 : R) => (fun (x7 : Int) => ((if ((lk x4) == (rk x6)) then ((w x4) x6) else (0 : Int)) + x7)))) + x5)))) + (Ink.foldr dxs (Ink.intOfU64 (0 : UInt64)) (fun (x8 : L) => (fun (x9 : Int) => ((Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x10 : R) => (fun (x11 : Int) => ((if ((lk x8) == (rk x10)) then ((w x8) x10) else (0 : Int)) + x11)))) + x9))))) := by
  calc _ = (Ink.foldr (xs ++ dxs) (Ink.intOfU64 (0 : UInt64)) (fun (x12 : L) => (fun (x13 : Int) => (((fun (x14 : L) => (Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x15 : R) => (fun (x16 : Int) => ((if ((lk x14) == (rk x15)) then ((w x14) x15) else (0 : Int)) + x16))))) x12) + x13)))) := by
        ink_auto
    _ = _ := by
        calc _ = ((Ink.foldr xs (Ink.intOfU64 (0 : UInt64)) (fun (x17 : L) => (fun (x18 : Int) => (((fun (x19 : L) => (Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x20 : R) => (fun (x21 : Int) => ((if ((lk x19) == (rk x20)) then ((w x19) x20) else (0 : Int)) + x21))))) x17) + x18)))) + (Ink.foldr dxs (Ink.intOfU64 (0 : UInt64)) (fun (x22 : L) => (fun (x23 : Int) => (((fun (x24 : L) => (Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x25 : R) => (fun (x26 : Int) => ((if ((lk x24) == (rk x25)) then ((w x24) x25) else (0 : Int)) + x26))))) x22) + x23))))) := by
              have h := @sum_append L (fun (x27 : L) => (Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x28 : R) => (fun (x29 : Int) => ((if ((lk x27) == (rk x28)) then ((w x27) x28) else (0 : Int)) + x29))))) xs dxs
              first | exact h | (simp only at h ⊢; exact h) | (simp_all; done) | ink_auto
          _ = _ := by
              ink_auto

theorem join_sum_append_right {L R : Type} (dys : (List R)) (lk : (L → UInt64)) (rk : (R → UInt64)) (w : (L → (R → Int))) (xs : (List L)) (ys : (List R)) :
    (Ink.foldr xs (Ink.intOfU64 (0 : UInt64)) (fun (x0 : L) => (fun (x1 : Int) => ((Ink.foldr (ys ++ dys) (Ink.intOfU64 (0 : UInt64)) (fun (x2 : R) => (fun (x3 : Int) => ((if ((lk x0) == (rk x2)) then ((w x0) x2) else (0 : Int)) + x3)))) + x1)))) = ((Ink.foldr xs (Ink.intOfU64 (0 : UInt64)) (fun (x4 : L) => (fun (x5 : Int) => ((Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x6 : R) => (fun (x7 : Int) => ((if ((lk x4) == (rk x6)) then ((w x4) x6) else (0 : Int)) + x7)))) + x5)))) + (Ink.foldr xs (Ink.intOfU64 (0 : UInt64)) (fun (x8 : L) => (fun (x9 : Int) => ((Ink.foldr dys (Ink.intOfU64 (0 : UInt64)) (fun (x10 : R) => (fun (x11 : Int) => ((if ((lk x8) == (rk x10)) then ((w x8) x10) else (0 : Int)) + x11)))) + x9))))) := by
  induction xs with
  | nil =>
      ink_auto
  | cons h t ih =>
      calc _ = ((Ink.foldr (ys ++ dys) (Ink.intOfU64 (0 : UInt64)) (fun (x12 : R) => (fun (x13 : Int) => ((if ((lk h) == (rk x12)) then ((w h) x12) else (0 : Int)) + x13)))) + ((Ink.foldr t (Ink.intOfU64 (0 : UInt64)) (fun (x14 : L) => (fun (x15 : Int) => ((Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x16 : R) => (fun (x17 : Int) => ((if ((lk x14) == (rk x16)) then ((w x14) x16) else (0 : Int)) + x17)))) + x15)))) + (Ink.foldr t (Ink.intOfU64 (0 : UInt64)) (fun (x18 : L) => (fun (x19 : Int) => ((Ink.foldr dys (Ink.intOfU64 (0 : UInt64)) (fun (x20 : R) => (fun (x21 : Int) => ((if ((lk x18) == (rk x20)) then ((w x18) x20) else (0 : Int)) + x21)))) + x19)))))) := by
            ink_auto
        _ = _ := by
            calc _ = (((Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x22 : R) => (fun (x23 : Int) => ((if ((lk h) == (rk x22)) then ((w h) x22) else (0 : Int)) + x23)))) + (Ink.foldr dys (Ink.intOfU64 (0 : UInt64)) (fun (x24 : R) => (fun (x25 : Int) => ((if ((lk h) == (rk x24)) then ((w h) x24) else (0 : Int)) + x25))))) + ((Ink.foldr t (Ink.intOfU64 (0 : UInt64)) (fun (x26 : L) => (fun (x27 : Int) => ((Ink.foldr ys (Ink.intOfU64 (0 : UInt64)) (fun (x28 : R) => (fun (x29 : Int) => ((if ((lk x26) == (rk x28)) then ((w x26) x28) else (0 : Int)) + x29)))) + x27)))) + (Ink.foldr t (Ink.intOfU64 (0 : UInt64)) (fun (x30 : L) => (fun (x31 : Int) => ((Ink.foldr dys (Ink.intOfU64 (0 : UInt64)) (fun (x32 : R) => (fun (x33 : Int) => ((if ((lk x30) == (rk x32)) then ((w x30) x32) else (0 : Int)) + x33)))) + x31)))))) := by
                  have hc18_0 := @sum_append R (fun (x34 : R) => (if ((lk h) == (rk x34)) then ((w h) x34) else (0 : Int))) ys dys
                  ink_auto
              _ = _ := by
                  ink_auto

theorem sum_split {E : Type} (a : (E → Int)) (b : (E → Int)) (xs : (List E)) :
    (Ink.foldr xs (Ink.intOfU64 (0 : UInt64)) (fun (x0 : E) => (fun (x1 : Int) => (((a x0) + (b x0)) + x1)))) = ((Ink.foldr xs (Ink.intOfU64 (0 : UInt64)) (fun (x2 : E) => (fun (x3 : Int) => ((a x2) + x3)))) + (Ink.foldr xs (Ink.intOfU64 (0 : UInt64)) (fun (x4 : E) => (fun (x5 : Int) => ((b x4) + x5))))) := by
  induction xs with
  | nil =>
      ink_auto
  | cons xs_head xs_tail ih =>
      ink_auto

end InkLaws
