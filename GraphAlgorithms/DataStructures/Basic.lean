/-!
# Basic Data Structures Formalization
-/

namespace FormalDataStructures

/-!
## Lists & Linked Lists
Lean already has a highly optimized built-in `List α`, but defining a custom
Singly Linked List is the standard starting point for structural induction.
-/

variable (α : Type)

/-!
## Stack
(Last In First Out)
-/
structure Stack where
  elements : List α
  deriving Repr
namespace Stack
/-- Pushes a new element `x` onto the top of the stack. -/
def push (x : α) (s : Stack α) : Stack α :=
  { elements := x :: s.elements }

/--
Pops the top element from the stack.
Returns `none` if the stack is empty, otherwise returns the element and the new stack state.
-/
def pop (s : Stack α) : Option (α × Stack α) :=
  match s.elements with
  | [] => none
  | head :: tail => some (head, ⟨tail⟩)

#eval pop (⟨[1]⟩ : Stack Nat)
#eval pop (push (1 : Nat) (push (2 : Nat) (push (3 : Nat) ⟨[]⟩)))

end Stack

/-!
## Queue
Queues are First-In-First-Out (FIFO) structures.
-/

/--
A common, efficient functional formalization of a Queue uses two lists:
an `inbox` for enqueueing and an `outbox` for dequeueing. This achieves
amortized O(1) time complexity for both operations without requiring mutation.
-/
structure Queue (α : Type) where
  /-- Elements are pushed here. -/
  inbox : List α
  /-- Elements are popped from here. -/
  outbox : List α

namespace Queue

/-- Enqueues an element to the back of the queue (added to the head of the inbox). -/
def enqueue (x : α) (q : Queue α) : Queue α :=
  { q with inbox := x :: q.inbox }

/--
Dequeues an element. If the outbox is empty, it reverses the inbox to become
the new outbox, maintaining FIFO order.
-/
def dequeue (q : Queue α) : Option (α × Queue α) :=
  match q.outbox with
  | head :: tail => some (head, { q with outbox := tail })
  | [] =>
    match q.inbox.reverse with
    | [] => none
    | head :: tail => some (head, ⟨[], tail⟩)

end Queue

/-!
## Hash Tables
Pure functional hash tables are complex due to immutability.
-/

/--
We model a Hash Table here as an `Array` of buckets (using `List (K × V)`
for collision resolution via chaining). This requires the Key type `K` to
implement both `Hashable` and `BEq` (Boolean equality).
-/
structure HashTable (K : Type) (V : Type) [Hashable K] [BEq K] where
  /-- The total number of allocated buckets. -/
  capacity : Nat
  /-- The buckets storing key-value pairs. -/
  buckets : Array (List (K × V))
  /-- A formal proof that the underlying array size always matches the stated capacity. -/
  size_eq : buckets.size = capacity

end FormalDataStructures
