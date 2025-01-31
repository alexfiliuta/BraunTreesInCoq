(*IMPORTS================================================================================*)

Require Import Nat.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Wf.
Require Import Coq.Wellfounded.Inclusion.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Lia.

(*Data Type and operations definitions===================================================*)

(*Braun Tree definition:*)
Inductive BraunTree (V : Type) : Type :=
  | Empty
  | Braun (l : BraunTree V) (v : V) (r : BraunTree V).

  Arguments Empty {V}.
  Arguments Braun {V} _ _ _.

(*Braun Tree example:*)
Definition exampleBraun1 : BraunTree nat :=
  Braun (Braun (Braun Empty 3 Empty) 1 Empty) 0 (Braun (Braun Empty 4 Empty) 2 Empty).
Compute exampleBraun1.


(*Size definition: O(n) time complexity*)
Fixpoint sizeOrg {V : Type} (t : BraunTree V) : nat :=
  match t with
  | Empty => 0
  | Braun l _ r => 1 + sizeOrg l + sizeOrg r
  end.

(*Size example:*)
Compute sizeOrg exampleBraun1.


(*Insert definition: O(log n) time complexity*)
Fixpoint insert {V : Type} (v : V) (t : BraunTree V) : BraunTree V :=
  match t with
  | Empty => Braun Empty v Empty
  | Braun l v' r => if Nat.eqb (sizeOrg l) (sizeOrg r)
                    then Braun (insert v l) v' r
                    else Braun l v' (insert v r)
  end.

(*Insert example:*)
Compute insert 5 exampleBraun1.


(*Remove definition: O(log n) time complexity*)
Fixpoint removeRoot {V : Type} (t : BraunTree V) : option (V * BraunTree V) :=
  match t with
  | Empty => None
  | Braun Empty v Empty => Some (v, Empty)
  | Braun l v r => 
    match removeRoot l with
    | Some (lv, newL) => Some (v, Braun r lv newL)
    | None => None (* UNREACHABLE CASE, HOW CAN I REMOVE IT *)
    end
  end.

Definition remove {V : Type} (t : BraunTree V) : option (BraunTree V) :=
  match removeRoot t with
  | Some (_ , newT) => Some newT
  | None => None
  end.

(*Remove example:*)
Compute removeRoot exampleBraun1.
Compute remove exampleBraun1.


(*Lookup definition: O(log n) time complexity*)
Fixpoint lookup {V : Type} (t : BraunTree V) (n : nat) : option V :=
  match t with
  | Empty => None
  | Braun l v r => 
      match n with
      | 0 => Some v
      | S m => if Nat.even m
               then lookup l (Nat.div2 m)
               else lookup r (Nat.div2 m)
      end
  end.

(*Lookup example:*)
Compute lookup exampleBraun1 2.
Compute lookup exampleBraun1 7.


(*Update definition: O(log n) time complexity*)
Fixpoint update {V : Type} (n : nat) (v : V) (t : BraunTree V) : BraunTree V :=
  match t with
  | Empty => Empty
  | Braun l v' r =>
      match n with
      | 0 => Braun l v r 
      | S m =>
          if Nat.odd n
          then Braun (update (Nat.div2 m) v l) v' r
          else Braun l v' (update (Nat.div2 (n - 1)) v r)
      end
  end.

(*Update example:*)
Compute update 0 10 exampleBraun1.


(*Tree-to-List definition: O(n * log n) time complexity*)
Fixpoint merge_lists {V : Type} (l1 l2 : list V) : list V :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | x::xs, y::ys => x :: y :: (merge_lists xs ys)
  end.

Fixpoint tree_to_list {V : Type} (t : BraunTree V) : list V :=
  match t with
  | Empty => []
  | Braun l v r => v :: (merge_lists (tree_to_list l) (tree_to_list r))
  end.

(*Tree-to-List example:*)
Compute tree_to_list exampleBraun1.
Compute tail (tree_to_list exampleBraun1).


(*Replicate definition: O(n * log n) time complexity*)
Fixpoint replicate {V : Type} (x : V) (n : nat) : BraunTree V :=
  match n with
  | 0 => Empty
  | S n' => insert x (replicate x n')
  end.

(*Replicate example:*)
Compute replicate 5 4.

(*The Invariant==========================================================================*)

Inductive IsBraun {V : Type} : BraunTree V -> Prop :=
  | IsBraun_Empty : IsBraun Empty
  | IsBraun_Node : forall l v r,
    IsBraun l ->
    IsBraun r ->
    (sizeOrg l = sizeOrg r \/ sizeOrg l = sizeOrg r + 1) ->
    IsBraun (Braun l v r).

Hint Constructors IsBraun : core.

(*Okasaki's Algorithms===================================================================*)

(*Size definition: O(log^2 n) time complexity*)
Fixpoint diff {V: Type} (t: BraunTree V) (n: nat) : nat :=
  match t, n with
  | Empty, 0 => 0
  | Braun _ _ _, 0 => 1
  | Braun l _ r, S (S n') =>
    if even n then diff r (div2 n)
    else diff l (Nat.div2 n)
  | _, _ => 0
  end.

Fixpoint size {V : Type} (t : BraunTree V) : nat :=
  match t with
  | Empty => 0
  | Braun l _ r => 
    let m := size r in 1 + 2 * m + diff l m
  end.


(*Replicate definition: O(log n) time complexity*)
Program Fixpoint copyOkasaki {V : Type} (x : V) (n : nat) {measure n} :
  (BraunTree V * BraunTree V) :=
  match n with
  | 0 => (Braun Empty x Empty, Empty)
  | S _ =>
      let (s, t) := copyOkasaki x (div2 (n-1)) in
      if even n 
      then (Braun s x s, Braun s x t)
      else (Braun s x t, Braun t x t)
  end.
Next Obligation.
  destruct wildcard'.
  + simpl. lia.
  + destruct wildcard' eqn:Hm.
    - simpl. lia.
    - apply Nat.lt_succ_r. apply Nat.lt_succ_r. apply Nat.div2_decr. lia.
Qed.

Definition copyOkasakiComplete {V: Type} (x: V) (n : nat) : BraunTree V :=
  snd (copyOkasaki x n).

(*Replicate example:*)
Compute copyOkasakiComplete 2 4.