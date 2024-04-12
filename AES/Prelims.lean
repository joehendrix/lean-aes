/-
This module contains various preliminary definitions that we may want to consider upstreaming.
-/


namespace Nat

def lg2Aux (x w : Nat) : Nat :=
  if x = 0 then
    w
  else
    lg2Aux (x / 2) (w+1)
  termination_by x

def lg2 (x : Nat) : Nat := lg2Aux x 0

end Nat

namespace Fin

/-- Folds over `Fin n` from the left: `foldl 3 f x = f (f (f x 0) 1) 2`. -/
@[specialize] def foldl (n) (f : α → Fin n → α) (init : α) : α := loop init 0 where
  /-- Inner loop for `Fin.foldl`. `Fin.foldl.loop n f x i = f (f (f x i) ...) (n-1)`  -/
  loop (x : α) (i : Nat) : α :=
    if h : i < n then loop (f x ⟨i, h⟩) (i+1) else x
  termination_by n - i

end Fin

/-
namespace UInt8

instance : HShiftRight UInt8 Nat UInt8 where
  hShiftRight x i := UInt8.ofNat (x.toNat >>> i)

end UInt8
-/

def ofRangeAux (motive : Nat → Sort u) (s e : Nat) (f : ∀(i : Nat), s ≤ i → i < e → motive i → motive (i+1)) (i : Nat) (lb : s ≤ i) (ub : i ≤ e) (c : motive i) : motive e :=
  if lt : i < e then
    ofRangeAux motive s e f (i+1) (by omega) lt (f i lb lt c)
  else
    have p : i = e := by omega
    cast (congrArg motive p) c
  termination_by e - i

def ofRange {motive : Nat → Sort u}
            (s e : Nat)
            (p : s ≤ e)
            (init : motive s)
            (f : ∀(i : Nat), s ≤ i → i < e → motive i → motive (i+1)) : motive e :=
  ofRangeAux motive s e f s (Nat.le_refl s) p init
