import AES.Prelims
import Lean.Elab.Term

structure Vec (n : Nat) (α : Type _) where
  value : Array α
  sizeEq : value.size = n

namespace Vec

theorem eq_of_val_eq : ∀ {i j : Vec n α}, i.value = j.value → i = j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem val_eq_of_eq {n} {i j : Vec n α} (h : i = j) : i.value = j.value :=
  h ▸ rfl

theorem ne_of_val_ne {n} {i j : Vec n α} (h : Not (i.value = j.value)) : ¬(i = j) :=
  fun h' => absurd (val_eq_of_eq h') h

instance [DecidableEq α] : DecidableEq (Vec n α) :=
  fun i j =>
    match decEq i.value j.value with
    | isTrue h  => isTrue (eq_of_val_eq h)
    | isFalse h => isFalse (ne_of_val_ne h)

def cast : n = m → Vec n α → Vec m α | rfl, x => x

def mkEmpty (n : Nat) : Vec 0 α := { value := .mkEmpty n, sizeEq := rfl }

def empty : Vec 0 α := mkEmpty 0


def push (v : Vec n α) (a : α) : Vec (n + 1) α :=
  { value := v.value.push a,
    sizeEq := by rw [Array.size_push, v.sizeEq]
    }

def ofFnAux (f : Fin n → α) (a : Vec m α) (h : m ≤ n) : Vec n α :=
  if p : m < n then
    ofFnAux f (a.push (f ⟨m, p⟩)) p
  else
    cast (by omega) a
  termination_by n - m

protected def ofFn {n : Nat} {α : Type u} (f : Fin n → α) : Vec n α :=
  ofFnAux f (mkEmpty n) (Nat.zero_le n)

instance [Inhabited α] : Inhabited (Vec n α) where
  default := .ofFn fun _ => default

protected def get {n : Nat} {α : Type u} (v : Vec n α) (i : Fin n) : α := v.value[i.val]'(by simp [v.sizeEq])

instance : GetElem (Vec n α) (Fin n) α (fun _ _ => True) where
  getElem v i _ := v.get i

instance : GetElem (Vec n α) Nat α (fun _ i => i < n) where
  getElem v i p := v.get ⟨i, p⟩


@[simp] theorem castGetElem : ∀(v : Vec m α) (g : m = n) (i : Nat) (h : i < n),
      (cast g v)[i]'h = v[i]'(by simp [g, h])
  | _, rfl, _, _ => rfl


@[simp] theorem pushGetElem (v : Vec n α) (a : α) (i : Nat) (h : i < n + 1) :
    (v.push a)[i]'h = if p : i < n then v[i]'p else a := by
  unfold push
  simp [GetElem.getElem]
  unfold Vec.get
  if p : i < n then
    simp [p, Vec.sizeEq, Array.get_push_lt]
  else
    have q : i = v.value.size := by
      simp [Vec.sizeEq];
      omega
    simp only [p, dite_false]
    simp [q, Array.get_push_eq]

theorem getElemOfFn (f : Fin n → α) (i : Nat) (h : i < n) :
    (Vec.ofFn f)[i]'h = f ⟨i, h⟩ := by
  unfold Vec.ofFn
  let rec auxP {m : Nat} (a : Vec m α) (p : m ≤ n) : (ofFnAux f a p)[i] =
          if q : i < m then a[i]'q else f ⟨i, h⟩ := by
    unfold ofFnAux
    if lt : m < n then
      simp [lt, auxP (a.push _)]
      match Nat.lt_trichotomy i m with
      | Or.inl q =>
        simp [q, Nat.lt_succ_of_lt q]
      | Or.inr (Or.inl q) =>
        simp [q]
      | Or.inr (Or.inr q) =>
        have q2 : ¬(i < m + 1) := by omega
        have q3 : ¬(i < m) := by omega
        simp [q2, q3]
    else
      have q2 : i < m := by omega
      simp [lt, q2]
    termination_by n - m
  simp [auxP]
  intro q
  contradiction

theorem valueGetElem (x : Vec n α) (i : Nat) (h : i < x.value.size) :
    x.value[i]'h = x[i]'(by simp [x.sizeEq] at h; exact h) := by
  rfl

def ext {x y : Vec n α} (p : ∀(i : Fin n), x[i] = y[i]) : x = y := by
  apply eq_of_val_eq
  apply Array.ext
  · simp [Vec.sizeEq]
  intros i ltx lty
  simp only [valueGetElem]
  exact p ..

protected def map (f : α → β) (x : Vec n α) : Vec n β := .ofFn (fun i => f x[i])

instance : Functor (Vec n) where
  map := Vec.map

def ofList (l : List α) : Vec l.length α := { value := l.toArray, sizeEq := Array.size_toArray l }

/--
Rotate value to left if `i` is positive and to right if negative.
-/
def rotate (x : Vec n α) (i : Int) : Vec n α := .ofFn fun j =>
  let idx := ((j.val + i)%n).toNat
  let p : idx < n := by
    rw [Int.toNat_lt]
    · apply Int.emod_lt_of_pos
      have q := j.isLt
      omega
    · apply Int.emod_nonneg
      have q := j.isLt
      omega
  x[idx]'p

def rotateL (x : Vec n α) (i : Nat) : Vec n α := x.rotate i
def rotateR (x : Vec n α) (i : Nat) : Vec n α := x.rotate (-(i : Int))

instance [HAnd α β γ] : HAnd (Vec n α) (Vec n β) (Vec n γ) where
  hAnd x y := .ofFn fun i => x[i] &&& y[i]

instance [HOr α β γ] : HOr (Vec n α) (Vec n β) (Vec n γ) where
  hOr x y := .ofFn fun i => x[i] ||| y[i]

instance [HXor α β γ] : HXor (Vec n α) (Vec n β) (Vec n γ) where
  hXor x y := .ofFn fun i => x[i] ^^^ y[i]

def mmult [HMul α β γ] [Add γ] [OfNat γ 0] (x : Vec m (Vec n α)) (y : Vec n (Vec p β)) : Vec m (Vec p γ) :=
  .ofFn fun i => .ofFn fun k => Fin.foldl n (init := 0) fun a j => a + x[i][j] * y[j][k]

def slice [Inhabited α] (x : Vec m α) (s n : Nat) : Vec n α := .ofFn fun i => x[s+i]!

def split {m n : Nat} (v : Vec (m * n) α) : Vec m (Vec n α) :=
  .ofFn fun i => .ofFn fun j => v[i.val * n + j.val]'(by
    apply Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _)
    rw [Nat.mul_comm _ n, ←Nat.mul_succ, Nat.mul_comm n _]
    exact Nat.mul_le_mul_right _ i.isLt
    )

def join {m n : Nat} (v : Vec m (Vec n α)) : Vec (m * n) α := .ofFn fun i =>
  have p0 : m * n > 0 := Nat.zero_lt_of_lt i.isLt
  have mp : m > 0 := Nat.pos_of_mul_pos_right p0
  have p : n > 0 := Nat.pos_of_mul_pos_left p0
  (v[(i.val/n) % m]'(Nat.mod_lt _ mp))[i % n]'(Nat.mod_lt _ p)

def joinBV {m n : Nat} (v : Vec m (BitVec n)) : BitVec (m * n) :=
  let go (r : Nat) (x : BitVec n) : Nat := (r <<< n) + x.toNat
  .ofNat (m*n) (v.value.foldl (init := 0) go)

def transpose (x : Vec m (Vec n α)) : Vec n (Vec m α) := .ofFn fun i => .ofFn fun j => x[j][i]

instance [Repr α] : Repr (Vec n α) where
  reprPrec v w := reprPrec v.value w

end Vec

syntax "#v[" withoutPosition(sepBy(term, ", ")) "]" : term

section

open Lean Meta Elab

def freshNatExpr : MetaM Expr := mkFreshExprMVar (some (.const ``Nat []))


def mkVecExpr (nExpr : Expr) : MetaM (Level × Expr × Expr) := do
  let lvl <- mkFreshLevelMVar
  let etp <- mkFreshExprMVar (some (.sort (.succ lvl)))
  let vtp := mkApp2 (.const ``Vec [lvl]) nExpr etp
  pure (lvl, etp, vtp)

elab_rules : term <= ptp
  | `(#v[ $elems,* ]) => do

    let a := elems.getElems
    let n := a.size
    let rnExpr <- freshNatExpr
    let (lvl, etp, vtp) <- mkVecExpr rnExpr
    if ← isDefEq ptp vtp then
      let nExpr := toExpr n
      let empty : Expr := mkApp2 (.const ``Vec.mkEmpty [lvl]) etp nExpr
      let pushVal (p : Expr × Nat) (e : Syntax) : TermElabM (Expr × Nat) := do
            let v := p.1
            let n := p.2
            let e ← Term.elabTerm e (some etp)
            let v' := mkApp4 (.const ``Vec.push [lvl]) (toExpr n) etp v e
            pure (v', n + 1)
      let (v, _) <- a.foldlM (init := (empty, 0)) pushVal
--      unless (← isDefEq rnExpr (natExpr n)) do
--        logError "bad"
      pure v
    else
      throwError m!"Expected vector instead of {ptp}"

end

def BitVec.split {m n : Nat} (v : BitVec (m * n)) : Vec m (BitVec n) :=
  Vec.ofFn fun i => truncate n (v >>> (n * (m - 1 - i.val)))
