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

theorem bool_and_true (p : Bool) :
    (p && true) = p := by
  cases hc : p with
  | false =>
      ink_auto
  | true =>
      ink_auto

theorem buffer_freeze_push {T : Type} (b : (List T)) (x : T) :
    (b ++ [x]) = (b ++ (x :: ([] : (List T)))) := by
  ink_auto

theorem choose_map {A B : Type} (c : Bool) (f : (A → B)) (x : A) (y : A) :
    (f (if c then x else y)) = (if c then (f x) else (f y)) := by
  cases hc : c with
  | false =>
      ink_auto
  | true =>
      ink_auto

theorem choose_same {T : Type} (c : Bool) (x : T) :
    (if c then x else x) = x := by
  ink_auto

theorem concat_associates {A : Type} (xs : (List A)) (ys : (List A)) (zs : (List A)) :
    ((xs ++ ys) ++ zs) = (xs ++ (ys ++ zs)) := by
  induction xs with
  | nil =>
      ink_auto
  | cons xs_head xs_tail ih =>
      ink_auto

theorem concat_empty {A : Type} (xs : (List A)) :
    (xs ++ ([] : (List A))) = xs := by
  induction xs with
  | nil =>
      ink_auto
  | cons xs_head xs_tail ih =>
      ink_auto

theorem fold_append {A M : Type} (plus : (M → (M → M))) (w : (A → M)) (xs : (List A)) (ys : (List A)) (zero : M) (zero_left : ∀ (a : M), ((plus zero) a) = a) (associates : ∀ (a : M) (b : M) (c : M), ((plus ((plus a) b)) c) = ((plus a) ((plus b) c))) :
    (Ink.foldr (xs ++ ys) zero (fun (x0 : A) => (fun (x1 : M) => ((plus (w x0)) x1)))) = ((plus (Ink.foldr xs zero (fun (x2 : A) => (fun (x3 : M) => ((plus (w x2)) x3))))) (Ink.foldr ys zero (fun (x4 : A) => (fun (x5 : M) => ((plus (w x4)) x5))))) := by
  induction xs with
  | nil =>
      apply Eq.symm
      calc _ = ((plus zero) (Ink.foldr ys zero (fun (x6 : A) => (fun (x7 : M) => ((plus (w x6)) x7))))) := by
            ink_auto
        _ = _ := by
            calc _ = (Ink.foldr ys zero (fun (x8 : A) => (fun (x9 : M) => ((plus (w x8)) x9)))) := by
                  have h := zero_left (Ink.foldr ys zero (fun (x10 : A) => (fun (x11 : M) => ((plus (w x10)) x11))))
                  first | exact h | (simp_all; done) | (rw [h]; done) | ink_auto
              _ = _ := by
                  ink_auto
  | cons h t ih =>
      calc _ = ((plus (w h)) ((plus (Ink.foldr t zero (fun (x12 : A) => (fun (x13 : M) => ((plus (w x12)) x13))))) (Ink.foldr ys zero (fun (x14 : A) => (fun (x15 : M) => ((plus (w x14)) x15)))))) := by
            ink_auto
        _ = _ := by
            apply Eq.symm
            calc _ = ((plus ((plus (w h)) (Ink.foldr t zero (fun (x16 : A) => (fun (x17 : M) => ((plus (w x16)) x17)))))) (Ink.foldr ys zero (fun (x18 : A) => (fun (x19 : M) => ((plus (w x18)) x19))))) := by
                  ink_auto
              _ = _ := by
                  have h := associates (w h) (Ink.foldr t zero (fun (x20 : A) => (fun (x21 : M) => ((plus (w x20)) x21)))) (Ink.foldr ys zero (fun (x22 : A) => (fun (x23 : M) => ((plus (w x22)) x23))))
                  first | exact h | (simp_all; done) | (rw [h]; done) | ink_auto

theorem count_append (xs : (List Bool)) (ys : (List Bool)) :
    (Ink.foldr (xs ++ ys) (0 : UInt64) (fun (x0 : Bool) => (fun (x1 : UInt64) => ((if x0 then (1 : UInt64) else (0 : UInt64)) + x1)))) = ((Ink.foldr xs (0 : UInt64) (fun (x2 : Bool) => (fun (x3 : UInt64) => ((if x2 then (1 : UInt64) else (0 : UInt64)) + x3)))) + (Ink.foldr ys (0 : UInt64) (fun (x4 : Bool) => (fun (x5 : UInt64) => ((if x4 then (1 : UInt64) else (0 : UInt64)) + x5))))) := by
  calc _ = (Ink.foldr (xs ++ ys) (0 : UInt64) (fun (x6 : Bool) => (fun (x7 : UInt64) => (((fun (x8 : UInt64) => (fun (x9 : UInt64) => (x8 + x9))) ((fun (x10 : Bool) => (if x10 then (1 : UInt64) else (0 : UInt64))) x6)) x7)))) := by
        ink_auto
    _ = _ := by
        calc _ = (((fun (x11 : UInt64) => (fun (x12 : UInt64) => (x11 + x12))) (Ink.foldr xs (0 : UInt64) (fun (x13 : Bool) => (fun (x14 : UInt64) => (((fun (x15 : UInt64) => (fun (x16 : UInt64) => (x15 + x16))) ((fun (x17 : Bool) => (if x17 then (1 : UInt64) else (0 : UInt64))) x13)) x14))))) (Ink.foldr ys (0 : UInt64) (fun (x18 : Bool) => (fun (x19 : UInt64) => (((fun (x20 : UInt64) => (fun (x21 : UInt64) => (x20 + x21))) ((fun (x22 : Bool) => (if x22 then (1 : UInt64) else (0 : UInt64))) x18)) x19))))) := by
              have h := @fold_append Bool UInt64 (fun (x23 : UInt64) => (fun (x24 : UInt64) => (x23 + x24))) (fun (x25 : Bool) => (if x25 then (1 : UInt64) else (0 : UInt64))) xs ys (0 : UInt64) (by intros; ink_auto) (by intros; ink_auto)
              first | exact h | (simp only at h ⊢; exact h) | (simp_all; done) | ink_auto
          _ = _ := by
              ink_auto

theorem filter_append {A : Type} (p : (A → Bool)) (xs : (List A)) (ys : (List A)) :
    (List.filter (fun (x0 : A) => (p x0)) (xs ++ ys)) = ((List.filter (fun (x1 : A) => (p x1)) xs) ++ (List.filter (fun (x2 : A) => (p x2)) ys)) := by
  induction xs with
  | nil =>
      ink_auto
  | cons h t ih =>
      cases hc : (p h) with
      | false =>
          ink_auto
      | true =>
          ink_auto

theorem filter_fusion {A : Type} (p : (A → Bool)) (q : (A → Bool)) (xs : (List A)) :
    (List.filter (fun (x1 : A) => (q x1)) (List.filter (fun (x0 : A) => (p x0)) xs)) = (List.filter (fun (x2 : A) => ((p x2) && (q x2))) xs) := by
  induction xs with
  | nil =>
      ink_auto
  | cons h t ih =>
      cases hc : (p h) with
      | false =>
          ink_auto
      | true =>
          cases hc : (q h) with
          | false =>
              ink_auto
          | true =>
              ink_auto

theorem fold_congruence {A M : Type} (plus : (M → (M → M))) (v : (A → M)) (w : (A → M)) (xs : (List A)) (zero : M) (agree : ∀ (x : A), (w x) = (v x)) :
    (Ink.foldr xs zero (fun (x0 : A) => (fun (x1 : M) => ((plus (w x0)) x1)))) = (Ink.foldr xs zero (fun (x2 : A) => (fun (x3 : M) => ((plus (v x2)) x3)))) := by
  induction xs with
  | nil =>
      ink_auto
  | cons h t ih =>
      calc _ = ((plus (w h)) (Ink.foldr t zero (fun (x4 : A) => (fun (x5 : M) => ((plus (v x4)) x5))))) := by
            ink_auto
        _ = _ := by
            calc _ = ((plus (v h)) (Ink.foldr t zero (fun (x6 : A) => (fun (x7 : M) => ((plus (v x6)) x7))))) := by
                  have hc18_0 := agree h
                  ink_auto
              _ = _ := by
                  ink_auto

theorem fold_filter {A M : Type} (p : (A → Bool)) (plus : (M → (M → M))) (w : (A → M)) (xs : (List A)) (zero : M) (zero_left : ∀ (a : M), ((plus zero) a) = a) :
    (Ink.foldr (List.filter (fun (x0 : A) => (p x0)) xs) zero (fun (x1 : A) => (fun (x2 : M) => ((plus (w x1)) x2)))) = (Ink.foldr xs zero (fun (x3 : A) => (fun (x4 : M) => ((plus (if (p x3) then (w x3) else zero)) x4)))) := by
  induction xs with
  | nil =>
      ink_auto
  | cons h t ih =>
      cases hc : (p h) with
      | false =>
          calc _ = (Ink.foldr t zero (fun (x5 : A) => (fun (x6 : M) => ((plus (if (p x5) then (w x5) else zero)) x6)))) := by
                ink_auto
            _ = _ := by
                apply Eq.symm
                calc _ = ((plus zero) (Ink.foldr t zero (fun (x7 : A) => (fun (x8 : M) => ((plus (if (p x7) then (w x7) else zero)) x8))))) := by
                      ink_auto
                  _ = _ := by
                      have h := zero_left (Ink.foldr t zero (fun (x9 : A) => (fun (x10 : M) => ((plus (if (p x9) then (w x9) else zero)) x10))))
                      first | exact h | (simp_all; done) | (rw [h]; done) | ink_auto
      | true =>
          ink_auto

theorem foldl_append {A S : Type} (f : (S → (A → S))) (s : S) (xs : (List A)) (ys : (List A)) :
    (Ink.foldl (xs ++ ys) s (fun (x0 : A) => (fun (x1 : S) => ((f x1) x0)))) = (Ink.foldl ys (Ink.foldl xs s (fun (x2 : A) => (fun (x3 : S) => ((f x3) x2)))) (fun (x4 : A) => (fun (x5 : S) => ((f x5) x4)))) := by
  induction xs generalizing s with
  | nil =>
      ink_auto
  | cons h t ih =>
      calc _ = (Ink.foldl (t ++ ys) ((f s) h) (fun (x6 : A) => (fun (x7 : S) => ((f x7) x6)))) := by
            ink_auto
        _ = _ := by
            calc _ = (Ink.foldl ys (Ink.foldl t ((f s) h) (fun (x8 : A) => (fun (x9 : S) => ((f x9) x8)))) (fun (x10 : A) => (fun (x11 : S) => ((f x11) x10)))) := by
                  ink_auto
              _ = _ := by
                  ink_auto

theorem foldr_map {A B S : Type} (f : (A → B)) (init : S) (step : (B → (S → S))) (xs : (List A)) :
    (Ink.foldr (List.map (fun (x0 : A) => (f x0)) xs) init (fun (x1 : B) => (fun (x2 : S) => ((step x1) x2)))) = (Ink.foldr xs init (fun (x3 : A) => (fun (x4 : S) => ((step (f x3)) x4)))) := by
  induction xs with
  | nil =>
      ink_auto
  | cons xs_head xs_tail ih =>
      ink_auto

theorem int_distributes (a : Int) (b : Int) (c : Int) :
    (a * (b + c)) = ((a * b) + (a * c)) := by
  ink_auto

theorem length_append {A : Type} (xs : (List A)) (ys : (List A)) :
    (Ink.length (xs ++ ys)) = ((Ink.length xs) + (Ink.length ys)) := by
  induction xs with
  | nil =>
      ink_auto
  | cons xs_head xs_tail ih =>
      ink_auto

theorem length_map {A B : Type} (f : (A → B)) (xs : (List A)) :
    (Ink.length (List.map (fun (x0 : A) => (f x0)) xs)) = (Ink.length xs) := by
  induction xs with
  | nil =>
      ink_auto
  | cons xs_head xs_tail ih =>
      ink_auto

theorem map_append {A B : Type} (f : (A → B)) (xs : (List A)) (ys : (List A)) :
    (List.map (fun (x0 : A) => (f x0)) (xs ++ ys)) = ((List.map (fun (x1 : A) => (f x1)) xs) ++ (List.map (fun (x2 : A) => (f x2)) ys)) := by
  induction xs with
  | nil =>
      ink_auto
  | cons xs_head xs_tail ih =>
      ink_auto

theorem map_fusion {A B C : Type} (f : (A → B)) (g : (B → C)) (xs : (List A)) :
    (List.map (fun (x1 : B) => (g x1)) (List.map (fun (x0 : A) => (f x0)) xs)) = (List.map (fun (x2 : A) => (g (f x2))) xs) := by
  induction xs with
  | nil =>
      ink_auto
  | cons xs_head xs_tail ih =>
      ink_auto

theorem map_identity {A : Type} (xs : (List A)) :
    (List.map (fun (x0 : A) => x0) xs) = xs := by
  induction xs with
  | nil =>
      ink_auto
  | cons xs_head xs_tail ih =>
      ink_auto

theorem map_remove_get {V : Type} (d : V) (k : UInt32) (m : (Ink.Map UInt32 V)) :
    (Ink.Map.getOr (Ink.Map.remove m k) k d) = d := by
  ink_auto

theorem map_set_contains {V : Type} (k : UInt64) (m : (Ink.Map UInt64 V)) (v : V) :
    (Ink.Map.contains (Ink.Map.set m k v) k) = true := by
  ink_auto

theorem map_set_get {V : Type} (d : V) (k : UInt32) (m : (Ink.Map UInt32 V)) (v : V) :
    (Ink.Map.getOr (Ink.Map.set m k v) k d) = v := by
  ink_auto

theorem map_set_get_other {V : Type} (d : V) (j : UInt32) (k : UInt32) (m : (Ink.Map UInt32 V)) (v : V) (h0 : (j == k) = false) :
    (Ink.Map.getOr (Ink.Map.set m k v) j d) = (Ink.Map.getOr m j d) := by
  ink_auto

theorem option_map_fusion {A B C : Type} (f : (A → B)) (g : (B → C)) (o : (Option A)) :
    (Ink.foldOption (Ink.foldOption o (fun (x0 : A) => (Option.some (f x0))) (fun (x1 : Unit) => (Option.none : (Option B)))) (fun (x2 : B) => (Option.some (g x2))) (fun (x3 : Unit) => (Option.none : (Option C)))) = (Ink.foldOption o (fun (x4 : A) => (Option.some (g (f x4)))) (fun (x5 : Unit) => (Option.none : (Option C)))) := by
  cases o with
  | none =>
      ink_auto
  | some v =>
      ink_auto

theorem option_map_identity {A : Type} (o : (Option A)) :
    (Ink.foldOption o (fun (x0 : A) => (Option.some x0)) (fun (x1 : Unit) => (Option.none : (Option A)))) = o := by
  cases o with
  | none =>
      ink_auto
  | some v =>
      ink_auto

theorem option_ok_or_map {A B E : Type} (e : E) (f : (A → B)) (o : (Option A)) :
    (Ink.foldOption (Ink.foldOption o (fun (x0 : A) => (Option.some (f x0))) (fun (x1 : Unit) => (Option.none : (Option B)))) (fun (x2 : B) => (Except.ok x2 : (Except E B))) (fun (x3 : Unit) => (Except.error e : (Except E B)))) = (Ink.foldResult (Ink.foldOption o (fun (x4 : A) => (Except.ok x4 : (Except E A))) (fun (x5 : Unit) => (Except.error e : (Except E A)))) (fun (x6 : A) => (Except.ok (f x6) : (Except E B))) (fun (x7 : E) => (Except.error x7 : (Except E B)))) := by
  cases o with
  | none =>
      ink_auto
  | some v =>
      ink_auto

structure Point where
  x : UInt32
  y : UInt32
deriving Repr

theorem point_x (a : UInt32) (b : UInt32) :
    ((Point.mk a b)).x = a := by
  ink_auto

theorem result_map_fusion {A B C E : Type} (f : (A → B)) (g : (B → C)) (r : (Except E A)) :
    (Ink.foldResult (Ink.foldResult r (fun (x0 : A) => (Except.ok (f x0) : (Except E B))) (fun (x1 : E) => (Except.error x1 : (Except E B)))) (fun (x2 : B) => (Except.ok (g x2) : (Except E C))) (fun (x3 : E) => (Except.error x3 : (Except E C)))) = (Ink.foldResult r (fun (x4 : A) => (Except.ok (g (f x4)) : (Except E C))) (fun (x5 : E) => (Except.error x5 : (Except E C)))) := by
  cases r with
  | ok v =>
      ink_auto
  | error e =>
      ink_auto

theorem result_maps_commute {A B E F : Type} (f : (A → B)) (g : (E → F)) (r : (Except E A)) :
    (Ink.foldResult (Ink.foldResult r (fun (x0 : A) => (Except.ok (f x0) : (Except E B))) (fun (x1 : E) => (Except.error x1 : (Except E B)))) (fun (x2 : B) => (Except.ok x2 : (Except F B))) (fun (x3 : E) => (Except.error (g x3) : (Except F B)))) = (Ink.foldResult (Ink.foldResult r (fun (x4 : A) => (Except.ok x4 : (Except F A))) (fun (x5 : E) => (Except.error (g x5) : (Except F A)))) (fun (x6 : A) => (Except.ok (f x6) : (Except F B))) (fun (x7 : F) => (Except.error x7 : (Except F B)))) := by
  cases r with
  | ok v =>
      ink_auto
  | error e =>
      ink_auto

theorem sum_append_u64 (xs : (List UInt64)) (ys : (List UInt64)) :
    (Ink.foldr (xs ++ ys) (0 : UInt64) (fun (x0 : UInt64) => (fun (x1 : UInt64) => (x0 + x1)))) = ((Ink.foldr xs (0 : UInt64) (fun (x2 : UInt64) => (fun (x3 : UInt64) => (x2 + x3)))) + (Ink.foldr ys (0 : UInt64) (fun (x4 : UInt64) => (fun (x5 : UInt64) => (x4 + x5))))) := by
  calc _ = (Ink.foldr (xs ++ ys) (0 : UInt64) (fun (x6 : UInt64) => (fun (x7 : UInt64) => (((fun (x8 : UInt64) => (fun (x9 : UInt64) => (x8 + x9))) ((fun (x10 : UInt64) => x10) x6)) x7)))) := by
        ink_auto
    _ = _ := by
        calc _ = (((fun (x11 : UInt64) => (fun (x12 : UInt64) => (x11 + x12))) (Ink.foldr xs (0 : UInt64) (fun (x13 : UInt64) => (fun (x14 : UInt64) => (((fun (x15 : UInt64) => (fun (x16 : UInt64) => (x15 + x16))) ((fun (x17 : UInt64) => x17) x13)) x14))))) (Ink.foldr ys (0 : UInt64) (fun (x18 : UInt64) => (fun (x19 : UInt64) => (((fun (x20 : UInt64) => (fun (x21 : UInt64) => (x20 + x21))) ((fun (x22 : UInt64) => x22) x18)) x19))))) := by
              have h := @fold_append UInt64 UInt64 (fun (x23 : UInt64) => (fun (x24 : UInt64) => (x23 + x24))) (fun (x25 : UInt64) => x25) xs ys (0 : UInt64) (by intros; ink_auto) (by intros; ink_auto)
              first | exact h | (simp only at h ⊢; exact h) | (simp_all; done) | ink_auto
          _ = _ := by
              ink_auto

theorem vector_y (a : Float32) (b : Float32) (c : Float32) :
    ((Ink.Vec3.mk a b c)).y = b := by
  ink_auto

theorem word_wraps (x : UInt32) :
    ((x + (4294967295 : UInt32)) + (1 : UInt32)) = x := by
  ink_auto

end InkLaws
