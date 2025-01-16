(*Imports:*)

Require Import Nat.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import Coq.Wellfounded.Inclusion.
Require Import Coq.Wellfounded.Wellfounded.
Require Import NAxioms NSub NDiv.
Require Import Coq.Program.Wf.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry. apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

#[local]Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in
  let e := fresh "e" in
  evar (e: Prop);
  assert (H: reflect e X); subst e;
  [ auto with bdestruct
  | destruct H as [H|H];
    [ | try (apply not_lt in H; fail 1) | try (apply not_le in H; fail 1) ]].

(*Data Type definition:*)

Inductive BraunTree (V : Type) : Type :=
  | Empty
  | Braun (l : BraunTree V) (v : V) (r : BraunTree V).

  Arguments Empty {V}.
  Arguments Braun {V} _ _ _.

    (*Braun Trees examples:*)
    Definition exampleBraun1 : BraunTree nat :=
    Braun (Braun (Braun Empty 3 Empty) 1 Empty) 0 (Braun (Braun Empty 4 Empty) 2 Empty).

    Compute exampleBraun1.


(*Size operation: O(n) time complexity
  - calulcate the size of the Braun Tree*)
(* ALGORITHM 1 *)
Fixpoint sizeOrg {V : Type} (t : BraunTree V) : nat :=
  match t with
  | Empty => 0
  | Braun l _ r => 1 + sizeOrg l + sizeOrg r
  end.

Compute sizeOrg exampleBraun1.



(*Insert operation at the end of the tree and at the root*)

Fixpoint insert {V : Type} (v : V) (t : BraunTree V) : BraunTree V :=
  match t with
  | Empty => Braun Empty v Empty
  | Braun l v' r => if Nat.eqb (sizeOrg l) (sizeOrg r) then Braun (insert v l) v' r else Braun l v' (insert v r)
  end.

Compute insert 5 exampleBraun1.


(* Not necessary*)
Fixpoint rootInsert {V : Type} (v : V) (t : BraunTree V) : BraunTree V :=
  match t with
  | Empty => Braun Empty v Empty
  | Braun l v' r => Braun (rootInsert v' r) v l
  end.

Compute rootInsert 10 (insert 5 exampleBraun1).
Compute rootInsert 11 (rootInsert 10 (insert 5 exampleBraun1)).



(*Remove operation at the root*)

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

Compute removeRoot exampleBraun1.

Definition remove {V : Type} (t : BraunTree V) : option (BraunTree V) :=
  match removeRoot t with
  | Some (_ , newT) => Some newT
  | None => None
  end.

Compute remove exampleBraun1.



(*lookup operation, start from 0:*)

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

Compute exampleBraun1.
Compute lookup exampleBraun1 0.
Compute lookup exampleBraun1 1.
Compute lookup exampleBraun1 2.
Compute lookup exampleBraun1 3.
Compute lookup exampleBraun1 4.
Compute lookup exampleBraun1 5.
Compute lookup exampleBraun1 6.
Compute lookup exampleBraun1 7.



(*Update operation*)
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

Compute update 0 10 exampleBraun1.
Compute update 1 11 exampleBraun1.
Compute update 2 22 exampleBraun1.
Compute update 4 44 exampleBraun1.
Compute update 5 55 exampleBraun1.



(*List to a tree:*)



(*Tree to a list:*)
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

Compute tree_to_list exampleBraun1.
Compute tail (tree_to_list exampleBraun1).
Compute skipn (5-1) (tree_to_list exampleBraun1).


Fixpoint replicate {V : Type} (x : V) (n : nat) : BraunTree V :=
  match n with
  | 0 => Empty
  | S n' => insert x (replicate x n')
  end.

Compute replicate 5 4.


(*Invariants:*)

Inductive IsBraun {V : Type} : BraunTree V -> Prop :=
  | IsBraun_Empty : IsBraun Empty
  | IsBraun_Node : forall l v r,
    IsBraun l ->
    IsBraun r ->
    (sizeOrg l = sizeOrg r \/ sizeOrg l = sizeOrg r + 1) ->
    IsBraun (Braun l v r).

Hint Constructors IsBraun : core.


(*--------------------------------------------------------------------------------------------------------*)

(*Size operation: O(log^2 n) time complexity
  - calulcate the size of the Braun Tree*)
(* OKASAKI ALGORITHM 1 *)
Fixpoint diff {V: Type} (s: BraunTree V) (m: nat) : nat :=
  match s, m with
  | Empty, 0 => 0
  | Braun _ _ _, 0 => 1
  | Braun l _ r, S (S m') =>
    if even m then diff r (div2 m)
    else diff l (Nat.div2 m)
  | _, _ => 0
  end.

Fixpoint size {V : Type} (t : BraunTree V) : nat :=
  match t with
  | Empty => 0
  | Braun l _ r => 
    let m := size r in 1 + 2 * m + diff l m
  end.

Search snd.

(*Replicate operation: O(log n) time complexity
  - creates a braun tree from n copies of an element
(* OKASAKI ALGORITHM 2 *) *)
Program Fixpoint copyOkasaki {V : Type} (x : V) (n : nat) {measure n} : (BraunTree V * BraunTree V) :=
  match n with
  | 0 => (Braun Empty x Empty, Empty)
  | S _ =>
      let (s, t) := copyOkasaki x (div2 (n-1)) in
      if even n then
      (Braun s x s, Braun s x t)
      else 
      (Braun s x t, Braun t x t)
  end.
Next Obligation.
  destruct wildcard' .
  - simpl. lia.
  - destruct wildcard' eqn:Hm.
    -- simpl. lia.
    -- apply Nat.lt_succ_r. apply Nat.lt_succ_r. Search div2. apply Nat.div2_decr. lia.
Qed.

Definition copyOkasakiComplete {V: Type} (x: V) (n : nat) : BraunTree V :=
  snd (copyOkasaki x n).

Compute copyOkasakiComplete 2 4.

(*Convert operation: O(n) time complexity
  - converts a list into a braun tree*)
(* OKASAKI ALGORITHM 3 *)
Fixpoint take {A : Type} (n : nat) (xs : list A) : list A :=
  match n, xs with
  | 0, _ => []
  | _, [] => []
  | S n, x :: xs => x :: take n xs
  end.

Fixpoint drop {A : Type} (n : nat) (xs : list A) : list A :=
  match n, xs with
  | 0, _ => xs
  | _, [] => []
  | S n, _ :: xs => drop n xs
  end.

(*
Fixpoint rows {A : Type} (k : nat) (xs : list A) : list (list A) :=
  match xs with
  | [] => []
  | _ => let current := take k xs in
         let remaining := drop k xs in
         current :: rows (2 * k) remaining
  end.
*)
(* TODO: same issue as earlier, Cannot guess decreasing argument of fix.*)

(*PROOF SIZE--------------------------------------------------------------------------------------------------------*)

Lemma size_non_negative : forall (V : Type) (t : BraunTree V),
    0 <= sizeOrg t.
Proof.
  intros V t.
  induction t as [| l IHl v r IHr].
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma size_empty : forall (V : Type),
    sizeOrg (@Empty V) = 0.
Proof.
  intros V.
  simpl. reflexivity.
Qed.

(*Helper lemma*)Lemma length_merge_lists : forall (V : Type) (l r : list V),
    length (merge_lists l r) = length l + length r.
Proof.
  intros V l r.
  generalize dependent r.
  induction l as [| x xs IHxs]; intros r.
  - simpl. reflexivity.
  - destruct r as [| y ys].
    + simpl. rewrite Nat.add_0_r. reflexivity.
    + simpl. rewrite IHxs. simpl. lia.
Qed.

Lemma size_list_equiv : forall (V : Type) (t : BraunTree V),
    sizeOrg t = length (tree_to_list t).
Proof.
  intros V t.
  induction t as [| l IHl v r IHr].
  - simpl. reflexivity.
  - simpl. rewrite IHl. rewrite IHr. rewrite length_merge_lists. reflexivity.
Qed.

(*PROOF INSERT--------------------------------------------------------------------------------------------------------*)

Lemma size_insert_inc : forall (V : Type) (v : V) (t : BraunTree V),
    sizeOrg (insert v t) = sizeOrg t + 1.
Proof.
  intros V v t. induction t as [|l IHl v' r IHr].
  - simpl. reflexivity.
  - simpl. destruct (sizeOrg l =? sizeOrg r) eqn:Heq.
    + simpl. rewrite IHl. lia.
    + simpl. rewrite IHr. lia.
Qed.

Check Nat.even_spec .
Check Nat.odd_spec.
Search add.
Search even.
Lemma n_plus_n_even : forall n : nat, Nat.even (n + n) = true.
Proof.
  intro n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_Sm. simpl. assumption.
Qed.

Search div2.
Lemma div2_double : forall n : nat, Nat.div2 (n + n) = n.
Proof.
  intro n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_Sm. simpl.
    rewrite IHn'. reflexivity.
Qed.

Lemma neq_cases : forall n m : nat,
  n <> m ->
  (n < m \/ n > m).
Proof.
  intros n m Hneq.
  assert (Htrichotomy : n < m \/ n = m \/ n > m) by lia.
  destruct Htrichotomy as [Hlt | [Heq | Hgt]].
  - left. assumption.
  - exfalso. apply Hneq. assumption.
  - right. assumption.
Qed.

Search add (forall n: nat, _).

Theorem add_n_n_twice : forall n : nat, n + n = 2 * n.
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_O. reflexivity.
Qed.

Lemma insert_last_lookup : forall (V : Type) (t : BraunTree V) (v : V),
  IsBraun t -> lookup (insert v t) (sizeOrg t) = Some v.
Proof.
  intros V t v.
  induction t as [|l IHl v' r IHr].
  - simpl. reflexivity.
  - simpl. destruct (sizeOrg l =? sizeOrg r) eqn:Heq.
    + simpl. rewrite Nat.eqb_eq in Heq. rewrite Heq. simpl. rewrite n_plus_n_even. rewrite div2_double. rewrite <- Heq. intros.
      apply IHl. inversion H. apply H3.
    + intros. simpl. rewrite Nat.eqb_neq in Heq. simpl. assert (Hsize: sizeOrg l = S (sizeOrg r)). {
        inversion H. destruct H5.
        ++ contradiction.
        ++ rewrite Nat.add_1_r in H5. assumption. }
    simpl. assert (HFalse: Nat.even (sizeOrg l + sizeOrg r) = false). {
    rewrite Hsize. rewrite Nat.add_succ_l. Search even. rewrite Nat.even_succ. Search even. 
    rewrite <- Nat.negb_even. rewrite n_plus_n_even. simpl. reflexivity. }
    rewrite HFalse. inversion H. rewrite Hsize. rewrite Nat.add_succ_l. rewrite add_n_n_twice. rewrite Nat.div2_succ_double.
    apply IHr. assumption.
Qed.

Lemma insert_maintains_braun : forall V (v : V) (t : BraunTree V),
  IsBraun t -> IsBraun (insert v t).
Proof.
  intros V v t Hbraun. induction t as [|l IHl v' r IHr].
  - simpl. constructor; simpl; constructor. reflexivity.
  - simpl. destruct (Nat.eqb (sizeOrg l) (sizeOrg r)) eqn:Heq.
    + constructor.
      * apply IHl. inversion Hbraun; assumption.
      * inversion Hbraun; assumption.
      * simpl. rewrite size_insert_inc.
        inversion Hbraun as [|lF vF rF H0 H1 H2]. right. apply Nat.add_cancel_r with (p := 1). rewrite Nat.eqb_eq in Heq. assumption.
    + constructor.
      * inversion Hbraun. assumption.
      * inversion Hbraun. apply IHr. assumption.
      * inversion Hbraun. left. destruct H4.
        ** apply Nat.eqb_neq in Heq. contradiction.
        ** rewrite H4. rewrite size_insert_inc. reflexivity.
Qed.

Lemma merge_lists_app : forall (V : Type) (l1 l2 : list V) (x : V),
    length l1 = length l2 ->
    merge_lists (l1 ++ [x]) l2 = (merge_lists l1 l2) ++ [x].
Proof.
  intros V l1 l2 x H.
  revert l2 H.
  induction l1 as [| y l1' IH]; intros l2 H.
  - destruct l2 as [| z l2']; [simpl; reflexivity | simpl in H; discriminate].
  - destruct l2 as [| z l2']; [simpl in H; discriminate |].
    simpl in H.
    apply eq_add_S in H.
    simpl.
    rewrite IH; auto.
Qed.

Lemma cons_inj_iff : forall (V : Type) (x : V) (l1 l2 : list V),
    (x :: l1 = x :: l2) <-> (l1 = l2).
Proof.
  intros V x l1 l2.
  split.
  - intro H.
    inversion H.
    reflexivity.
  - intro H.
    rewrite H.
    reflexivity.
Qed.

Lemma merge_lists_app_r_one_extra : forall (V : Type) (l1 l2 : list V) (x : V),
    length l1 = length l2 + 1 ->
    merge_lists l1 (l2 ++ [x]) = (merge_lists l1 l2) ++ [x].
Proof.
  intros V l1 l2 x H.
  revert l2 H.
  induction l1 as [| y l1' IH]; intros l2 H.
  - simpl in H. lia. (* impossible case, l1 cannot be empty and longer than l2 *)
  - destruct l2 as [| z l2'].
    + simpl.
      f_equal. simpl in H. (* F EQUAL WHAT DOES IT DO, it takes out first elem? *)
      assert (length l1' = 0) as Hlen by lia.
      apply length_zero_iff_nil in Hlen.
      subst. simpl. reflexivity. (* and subst *)
    + simpl in H.
      simpl.
      f_equal.
      rewrite cons_inj_iff.
      simpl in H.
      apply eq_add_S in H.
      apply IH. assumption.
Qed.

Lemma insert_to_list_equiv : forall (V : Type) (v : V) (t : BraunTree V),
    IsBraun t -> tree_to_list (insert v t) = tree_to_list t ++ [v].
Proof.
  intros V v t H. induction t as [| l IHl x r IHr].
  - simpl. reflexivity.
  - simpl. destruct (sizeOrg l =? sizeOrg r) eqn:Hyp.
    + apply Nat.eqb_eq in Hyp.
      inversion H.
      simpl. rewrite (IHl H3). rewrite merge_lists_app.
      ++ reflexivity.
      ++ rewrite <- size_list_equiv. rewrite <- size_list_equiv. assumption.
    + apply Nat.eqb_neq in Hyp. inversion H. simpl. rewrite (IHr H4). rewrite merge_lists_app_r_one_extra.
      ++ reflexivity.
      ++ destruct H5. contradiction. rewrite <- size_list_equiv. rewrite <- size_list_equiv. assumption.
Qed.

(*PROOF REMOVE--------------------------------------------------------------------------------------------------------*)

Lemma remove_empty : forall (V : Type),
    remove (@Empty V) = None.
Proof.
  intros V.
  simpl. reflexivity.
Qed.

Lemma size_removeRoot_empty_one :
  forall (V : Type) (v : V) t,
    IsBraun t ->
    removeRoot t = Some (v, Empty) ->
    sizeOrg t = 1.
Proof.
  intros V v t Hbraun.
  destruct t as [| l v' r ].
  - simpl. inversion 1. (* How does inversion on l work*)
  - simpl. (*How to read this*)
    destruct l as [|l' v_l r'].
    + destruct r as [|l'' v_r r''].
      ++ simpl. auto.
      ++ simpl. inversion 1.
    + destruct (removeRoot (Braun l' v_l r')) as [ [lv newL] | ].
      ++ inversion 1.
      ++ inversion 1.
Qed.

Lemma size_remove_empty_one:
  forall (V : Type) (t : BraunTree V),
  IsBraun (t) -> remove t = Some Empty -> sizeOrg t = 1.
Proof.
  intros V t Hbraun Hrem. unfold remove in Hrem.
  destruct (removeRoot t) as [ [v newT] | ] eqn:Hroot. (* why not the other way around possible cus of the match ?*)
  - inversion Hrem; subst. clear Hrem. apply size_removeRoot_empty_one in Hroot; auto.
  - discriminate Hrem.
Qed.

Lemma size_removeRoot_dec {V : Type} (t : BraunTree V) v :
    IsBraun t -> forall t', removeRoot t = Some (v, t') -> sizeOrg t' = sizeOrg t - 1.
Proof.
  intros Hbraun. revert v. induction t as [|l IHl v' r IHr]; intros v t' Hassumption.
  - discriminate.
  - simpl in Hassumption.
    destruct l as [|l' v_l r'].
    + destruct r as [|l'' v_r r''].
      ++ simpl. inversion Hassumption. reflexivity.
      ++ simpl in Hassumption. inversion Hassumption.
    + destruct (removeRoot (Braun l' v_l r')) as [ [lv newL] | ] eqn:Hremove.
      ++ assert (sizeOrg newL = sizeOrg (Braun l' v_l r') - 1) as HsizenewL.
        { eapply IHl.
          - inversion Hbraun; auto.
          - reflexivity. }
        inversion Hassumption.
        simpl. rewrite HsizenewL.
        simpl. lia.
      ++ inversion Hassumption.
Qed.

Lemma size_remove_dec : forall (V : Type) (t : BraunTree V),
    IsBraun t -> forall t', remove t = Some t' -> sizeOrg t' = sizeOrg t - 1.
Proof.
  intros V t Hbraun t' Hremove.
  unfold remove in Hremove.
  destruct (removeRoot t) as [ [v newT] | ] eqn:Hroot.
    inversion Hremove; subst; clear Hremove.
  - apply size_removeRoot_dec with (v := v) in Hroot; auto.
  - discriminate Hremove.
Qed.

Lemma removeRoot_value_eq : forall (V : Type) (l1 r1 : BraunTree V) (v1 lv : V) (newL : BraunTree V),
  removeRoot (Braun l1 v1 r1) = Some (lv, newL) -> v1 = lv.
Proof.
intros V l1 r1 v1 lv newL H.
simpl in H.
destruct l1.
- inversion H; auto. destruct r1. inversion H; reflexivity. discriminate H.
- simpl in H. destruct l1_1 as [|x1 x2 x3].
  + inversion H; subst; auto. destruct l1_2 as [|y1 y2 y3]. inversion H; reflexivity. discriminate H1.
  + destruct (removeRoot (Braun x1 x2 x3)) as [ [z newT] | ] eqn:Hroot.
    * inversion H. rewrite <- H1. reflexivity.
    * discriminate H.
Qed.
(*
Lemma removeRoot_value_newL : forall (V : Type) (l1 r1 : BraunTree V) (v1 lv : V) (newL : BraunTree V),
  removeRoot (Braun l1 v1 r1) = Some (lv, newL) -> merge_lists (tree_to_list l1) (tree_to_list r1) = tree_to_list newL.
Proof.
  intros V l1 r1 v1 lv.
  induction l1 as [ | l1_left HypL l1_val l1_right HypR ]; intros newL H.
  - destruct r1 as [ | rl rv rr ].
    + inversion H; subst. simpl. reflexivity.
    + inversion H.
  - destruct r1 as [| r1 rv rr]. 
    + simpl. rewrite <- HypL.
      * simpl. admit.
      * clear. induction l1_left; simpl; auto. admit.
    + destruct (removeRoot (Braun (Braun l1_left l1_val l1_right) v1 (Braun r1 rv rr))) as [[lv_sub newL_sub]|] eqn:HeqRemove.
      *
      * simpl. destruct (removeRoot (Braun l1_left l1_val l1_right)) as [[lv_sub newL_sub]|] eqn:HeqRemove.
        ** rewrite HypL in HeqRemove.
        ** simpl in HeqRemove.
    + inversion H; subst; clear H.
      simpl. destruct (tree_to_list r1) as [| y ys] eqn:E_r1.
      * simpl. apply removeRoot_value_eq in HeqRemove. rewrite HeqRemove. destruct l1_left.
        ** simpl. inversion H1. destruct l1_right.
          *** simpl. inversion H0. simpl. rewrite E_r1. simpl. rewrite HeqRemove. reflexivity.
          *** simpl. inversion H0.
        ** simpl. destruct (tree_to_list l1_right).
          *** destruct (removeRoot (Braun l1_left1 v l1_left2)).
            **** destruct H1 eqn:HP. simpl. admit.
            **** inversion H1.
          *** destruct (removeRoot (Braun l1_left1 v l1_left2)).
            **** admit.
            **** inversion H1.
      * destruct  l1_left. admit. admit.
    + inversion HeqRemove. admit.
Admitted.

Lemma removeRoot_value_newL : forall (V : Type) (l1 r1 : BraunTree V) (v1 lv : V) (newL : BraunTree V),
  removeRoot (Braun l1 v1 r1) = Some (lv, newL) -> merge_lists (tree_to_list l1) (tree_to_list r1) = tree_to_list newL.
Proof.
  intros V l1 r1 v1 lv newL H.
  simpl in H.
  destruct l1 as [ | l1_left l1_val l1_right ].
  - destruct r1 as [ | rl rv rr ].
    + inversion H; subst. simpl. reflexivity.
    + inversion H.
  - simpl in H.
    destruct (removeRoot (Braun l1_left l1_val l1_right)) as [[lv_sub newL_sub]|] eqn:HeqRemove.
    + inversion H; subst; clear H.
      simpl. destruct (tree_to_list r1) as [| y ys] eqn:E_r1.
      * simpl. f_equal.
        -- apply removeRoot_value_eq in HeqRemove. admit.
      
      * simpl. f_equal. f_equal.
        -- apply removeRoot_value_eq in  HeqRemove. admit.
    + inversion HeqRemove. rewrite H1.
Admitted.
*)
Lemma merge_lists_twist_L {V : Type} (x : V) (xs ys : list V) :
  merge_lists (x :: xs) ys = x :: merge_lists ys xs
with merge_lists_twist_R {V : Type} (y : V) (ys xs : list V) :
  merge_lists (y :: ys) xs = y :: merge_lists xs ys.
Proof.
- destruct ys as [| y' ys']; simpl.
  + reflexivity.
  + f_equal. destruct xs as [| x'xs']; simpl.
    -- simpl. reflexivity.
    -- f_equal. apply merge_lists_twist_R.
- destruct xs as [| x' xs']; simpl.
  + reflexivity.
  + f_equal. destruct ys as [| y'ys']; simpl.
    -- reflexivity.
    -- f_equal. apply merge_lists_twist_L.
Qed. 

Lemma remove_to_list_equiv {V : Type} (t : BraunTree V) (v : V) :
    IsBraun t ->
    forall t', removeRoot t = Some (v, t') ->
               tree_to_list t = v :: tree_to_list t'.
Proof.
  intros Hbraun t' Hremove.
  induction t as [| l IHl v' r IHr].
  - simpl in Hremove. discriminate Hremove.
  - simpl in Hremove. destruct l as [| l1 vl r1].
    + destruct r as [| l2 vr r2].
      * inversion Hremove. simpl. reflexivity.
      * inversion Hremove.
    + destruct (removeRoot (Braun l1 vl r1)) as [[lv newL]|] eqn:HremL.
      * inversion Hremove. subst. clear Hremove. simpl. inversion Hbraun; subst. rename H2 into Hl.
        rename H3 into Hr. rename H4 into HsizeCond.
        assert (H_Head := HremL). apply removeRoot_value_eq in H_Head.
        assert (H_Tail: merge_lists (tree_to_list l1) (tree_to_list r1) = tree_to_list newL).
        {
          admit.
        }
        subst vl. destruct (tree_to_list r) as [| y ys] eqn:HrList.
        *** simpl. rewrite H_Tail. reflexivity.
        *** simpl. rewrite H_Tail. rewrite <- merge_lists_twist_L.
          f_equal.
      * inversion Hremove.
Admitted.

Lemma removeRoot_maintains_braun : forall (V : Type) (t : BraunTree V) v t',
    IsBraun t -> removeRoot t = Some (v, t') -> IsBraun t'.
Proof.
  intros V t v t' Hbraun. revert v. revert t'. induction t as [| l IHl v' r IHr]; intros v t' Hremove.
  - discriminate Hremove.
  - simpl in Hremove. destruct l as [| l1 v1 r1].
    + destruct r as [| l2 v2 r2].
      * simpl in Hremove. inversion Hremove; subst; clear Hremove. constructor.
      * simpl in Hremove. inversion Hremove. (* How can inversion find out it is contradictory with the constructor*)
    + destruct (removeRoot (Braun l1 v1 r1)) as [ [lv newL] | ] eqn:Hremove2.
      * inversion Hremove.
        assert (IsBraun r). { inversion Hbraun. assumption. }
        assert (IsBraun newL). { apply IHl with (v := lv); auto. inversion Hbraun. assumption. }
        constructor; auto.
        inversion Hbraun. destruct H8.
        ** right. rewrite <- H8. apply size_removeRoot_dec in Hremove2; auto. rewrite Hremove2. simpl. lia.
        ** left. apply size_removeRoot_dec in Hremove2; auto. rewrite Hremove2. rewrite H8. lia.
      * apply IHl with (v := v1); auto. inversion Hbraun; auto. discriminate.
Qed.

Lemma remove_maintains_braun : forall (V : Type) (t : BraunTree V),
    IsBraun t -> forall t', remove t = Some t' -> IsBraun t'.
Proof.
  intros V t Hbraun t' Hremove.
  unfold remove in Hremove.
  destruct (removeRoot t) as [[v newT] |] eqn:Hroot.
  - inversion Hremove; subst; clear Hremove.
    eapply removeRoot_maintains_braun; eauto.
  - discriminate Hremove.
Qed.

(*PROOF LOOKUP--------------------------------------------------------------------------------------------------------*)

Lemma lookup_empty : forall (V : Type) (i : nat),
    lookup (@Empty V) i = None.
Proof. intros V i.
  simpl. reflexivity.
Qed.

Lemma lookup_root : forall (V : Type) (v : V) (l r : BraunTree V),
    lookup (Braun l v r) 0 = Some v.
Proof.
  intros V v l r.
  simpl. reflexivity.
Qed.

Lemma subtract_one_lemma : forall a b : nat, a <= b -> a - 1 <= b - 1.
Proof.
  intros a b H. lia.
Qed.

Lemma div2_ge : forall i x : nat, i >= 2 * x -> Nat.div2 i >= x.
Proof.
  intros i x H.
  assert (Hdiv: 2 * x / 2 = x). { rewrite <- Nat.div_mul with (b := 2).  - rewrite Nat.mul_comm at 1. reflexivity. - lia. }
  rewrite <- Hdiv.
  apply Nat.le_trans with (m := i / 2).
  - apply Nat.div_le_mono with (c := 2); lia.
  - rewrite <- Nat.div2_div; apply Nat.le_refl.
Qed.

Lemma div2_ge_even : forall i x : nat, Nat.even i = true -> S i >= 2 * x -> Nat.div2 i >= x.
Proof.
  intros i x Heven Hsi.
  apply Nat.even_spec in Heven.
  destruct Heven as [k Hk].
  rewrite Hk in *.
  rewrite Nat.div2_double in *.
  simpl in Hsi.
  assert (2 * k + 1 >= 2 * x) as Hge by lia.
  assert (2 * k >= 2 * x - 1) as Hkx by lia.
  apply Nat.mul_le_mono_pos_l with (p := 2) in Hkx; try lia.
Qed.

Lemma x_ge_y_plus_1_implies_x_ge_y : forall x y : nat,
  x >= y + 1 -> x >= y.
Proof.
  intros x y H.
  apply Nat.le_trans with (m := y + 1); auto with arith.
Qed.

Lemma lookup_out_of_bounds : forall (V : Type) (t : BraunTree V) (i : nat),
    IsBraun t ->i >= sizeOrg t -> lookup t i = None.
Proof.
  intros V t i Hbraun Hi.
  generalize dependent i.
  induction t as [| l IHl v r IHr]; intros i Hi.
  - simpl in *. reflexivity.
  - inversion Hbraun as [| l' v' r' Hl Hr SizeCond]; subst.
    simpl in *.
    destruct i.
    + lia.
    + destruct (Nat.even i) eqn:Heven.
      * apply IHl. assumption. apply Nat.succ_le_mono in Hi. destruct SizeCond.
        ** rewrite <- H in Hi. rewrite add_n_n_twice in Hi. apply div2_ge. assumption.
        ** Compute Nat.add_sub_eq_l. assert ( sizeOrg l - 1 = sizeOrg r). { lia. } rewrite <- H0 in Hi. clear H0. clear H.
           assert (sizeOrg l + ( sizeOrg l - 1) = 2 * sizeOrg l - 1). { lia. } rewrite H in Hi. clear H. assert ( 2 * sizeOrg l <= S i). { lia. }
           clear Hi. apply div2_ge_even; assumption.
      * apply IHr; auto. apply Nat.succ_le_mono in Hi. destruct SizeCond.
        ** rewrite H in Hi. rewrite add_n_n_twice in Hi. assert ((sizeOrg r <= Nat.div2 i) -> (Nat.div2 i >= sizeOrg r)). { lia. } apply H0.
           clear H0. apply div2_ge. assumption.
        ** rewrite H in Hi. assert (sizeOrg r + 1 + sizeOrg r = 2 * sizeOrg r + 1). { lia. } rewrite H0 in Hi. clear H0.
           assert ((sizeOrg r <= Nat.div2 i) -> (Nat.div2 i >= sizeOrg r)). { lia. } apply H0. clear H0. apply div2_ge.
           apply x_ge_y_plus_1_implies_x_ge_y. assumption.
Qed.


Lemma div2_less_implies_double_less : forall i s : nat,
  Nat.div2 i < s -> i < 2 * s.
Proof.
  intros i s His. destruct (Nat.lt_ge_cases i (2*s)) as [Hlt | Hge].
  - exact Hlt.
  - apply div2_ge in Hge.
    lia.
Qed.

Lemma div2_less_implies_double_less_minus_one : forall i s : nat,
  Nat.even i = true -> i < 2 * s -> i < 2 * s - 1.
Proof.
  intros i s Heven Hlt. assert ( S i < 2 * s -> i < 2 * s - 1). { lia. } apply H; clear H. apply div2_less_implies_double_less.
  rewrite <- (Nat.Even_div2 i).
    - assert (2 * Nat.div2 i < 2 * s -> Nat.div2 i < s ). { lia. } apply H; clear H. Search div2.
      assert ( 2 * Nat.div2 i = Nat.double (Nat.div2 i) ). { rewrite Nat.double_twice. reflexivity. }  rewrite H.
      assert (Nat.double (Nat.div2 i) = i). { symmetry. apply Nat.Even_double. apply Nat.even_spec. assumption. } rewrite H0. assumption.
    - apply Nat.even_spec. assumption.
Qed. 

Lemma lookup_implies_valid_index : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
  IsBraun t -> lookup t i = Some v -> i < sizeOrg t.
Proof.
  intros V t i v HBraun Hi. generalize dependent i.
  induction t as [| l IHl v' r IHr]; intros i Hi.
  - simpl in Hi. discriminate Hi.
  - simpl. simpl in Hi. destruct i.
    + lia.
    + assert (i < sizeOrg l + sizeOrg r -> S i < S (sizeOrg l + sizeOrg r)). { lia. } apply H. clear H.
      inversion HBraun as [| l' v'' r' Hl Hr SizeCond]; subst. destruct (Nat.even i) eqn:Hev.
      * apply IHl in Hi. 
        ** destruct SizeCond.
          *** rewrite <- H. rewrite add_n_n_twice. apply div2_less_implies_double_less. assumption.
          *** assert ( sizeOrg l - 1 = sizeOrg r). { lia. } rewrite <- H0. assert (sizeOrg l + ( sizeOrg l - 1) = 2 * sizeOrg l - 1).
              { lia. } rewrite H1. apply div2_less_implies_double_less_minus_one. assumption. apply div2_less_implies_double_less. assumption.
        ** assumption.
      * apply IHr in Hi.
        ** destruct SizeCond.
          *** rewrite H; rewrite add_n_n_twice; apply div2_less_implies_double_less. assumption.
          *** rewrite H. assert (sizeOrg r + 1 + sizeOrg r = 2 * sizeOrg r + 1). { lia. } rewrite H0. clear H0. assert (i < 2 * sizeOrg r ->
              i < 2 * sizeOrg r + 1). { lia. } apply H0; clear H0. apply div2_less_implies_double_less. assumption.
        ** assumption.
Qed.

Search nth_error. Compute nth_error.

Lemma nth_S :
  forall (V : Type) (xs : list V) (i : nat) (x : V),
    nth_error (x :: xs) (S i) = nth_error xs i.
Proof. reflexivity. Qed.

Lemma nth_empty :
  forall (V : Type) (i : nat),
    nth_error (@nil V) i = None.
Proof.
  intros. destruct i.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma nth_error_merge_lists_even :
  forall (V : Type) (l1 l2 : list V) (k : nat),
    (length l1 = length l2 \/ length l1 = length l2 + 1) ->
    nth_error (merge_lists l1 l2) (2*k) = nth_error l1 k.
Proof.
  intros V l1 l2 k Hlen.
  generalize dependent k.
  generalize dependent l2.
  induction l1 as [|x xs IHl1]; intros l2 k.
  - destruct k.
    -- simpl in H; symmetry in H;  rewrite length_zero_iff_nil in H. rewrite H; simpl. intro k. rewrite nth_empty.
       rewrite nth_empty. reflexivity.
    -- simpl in H. rewrite Nat.add_1_r in H. discriminate H.
  - destruct l2 as [|y ys].
    + destruct k as [Hlen|Hlen]; simpl in Hlen.
      * inversion Hlen.
      * simpl. destruct k.
        -- simpl. reflexivity.
        -- simpl. assert (S (length xs) = 1 -> length xs = 0) by lia. apply H in Hlen; clear H. rewrite length_zero_iff_nil in
           Hlen. rewrite Hlen. rewrite nth_empty. rewrite nth_empty. reflexivity.
    + intro k0. destruct k; simpl.
      * destruct k0. 
        ** simpl. reflexivity. 
        ** rewrite nth_S. assert (S k0 + (S k0 + 0) = S (S (2 * k0))) by lia. rewrite H0. rewrite nth_S. rewrite nth_S. 
           apply IHl1. left. simpl in H. lia.
      * destruct k0. 
        ** simpl. reflexivity.
        ** rewrite nth_S. assert ((S k0 + (S k0 + 0)) = S (S (2 * k0))) by lia. rewrite H0.
        rewrite nth_S. rewrite nth_S. apply IHl1. right. simpl in H. lia.
Qed.

Lemma nth_error_merge_lists_odd :
  forall (V : Type) (l1 l2 : list V) (k : nat),
    (length l1 = length l2 \/ length l1 = length l2 + 1) ->
    nth_error (merge_lists l1 l2) ( 2*k + 1) = nth_error l2 k.
Proof.
  intros V l1 l2 k Hlen.
  generalize dependent k.
  generalize dependent l1.
  induction l2 as [|x xs IHl2]; intros l1 k.
  - intro k0. destruct k.
    -- simpl in H;  rewrite length_zero_iff_nil in H. rewrite H; simpl. rewrite nth_empty.
       rewrite nth_empty. reflexivity.
    -- simpl in H. rewrite nth_empty. destruct l1.
      --- simpl in H. discriminate H.
      --- simpl in H. assert (length l1 = 0) by lia. rewrite length_zero_iff_nil in H0. rewrite H0. simpl.
          rewrite Nat.add_1_r. simpl. rewrite nth_empty. reflexivity.
  - destruct l1 as [|y ys].
    + destruct k as [Hlen|Hlen]; simpl in Hlen.
      * inversion Hlen.
      * simpl. destruct k.
        -- discriminate Hlen.
        -- discriminate Hlen.
    + intro k0. destruct k; simpl.
      * destruct k0. 
        ** simpl. reflexivity. 
        ** rewrite nth_S. assert (S k0 + (S k0 + 0) = S (S (2 * k0))) by lia. rewrite H0. rewrite Nat.add_1_r. 
           rewrite nth_S. rewrite nth_S. rewrite <- Nat.add_1_r. apply IHl2. left. simpl in H. lia.
      * destruct k0. 
        ** simpl. reflexivity.
        ** rewrite nth_S. assert (S k0 + (S k0 + 0) = S (S (2 * k0))) by lia. rewrite H0. rewrite Nat.add_1_r. 
           rewrite nth_S. rewrite nth_S. rewrite <- Nat.add_1_r. apply IHl2. right. simpl in H. lia.
Qed.

Lemma lookup_to_list_equiv : forall (V : Type) (t : BraunTree V) (i : nat),
    IsBraun t -> lookup t i = nth_error (tree_to_list t) i.
Proof.
  intros V t i Hbraun.
  generalize dependent i.
  induction t as [| l IHl v r IHr].
  - simpl. destruct i; simpl; reflexivity.
  - simpl. destruct i.
    -- simpl. reflexivity.
    -- inversion Hbraun. destruct (Nat.even i) eqn:Heven.
      --- simpl. rewrite IHl.
          * destruct H4.
            ** rewrite Nat.even_spec in Heven. inversion Heven as [k Hk]. rewrite Hk. rewrite nth_error_merge_lists_even.
              *** rewrite Nat.div2_double. reflexivity.
              *** left. rewrite size_list_equiv in H4. rewrite size_list_equiv in H4. assumption.
            **  rewrite Nat.even_spec in Heven. inversion Heven as [k Hk]. rewrite Hk. rewrite nth_error_merge_lists_even.
              *** rewrite Nat.div2_double. reflexivity.
              *** right. rewrite size_list_equiv in H4. rewrite size_list_equiv in H4. assumption.
          * assumption.
      --- simpl. rewrite IHr. 
          * rewrite <- Nat.negb_odd in Heven. rewrite negb_false_iff in Heven. rewrite Nat.odd_spec in Heven.
            inversion Heven as [k Hk]. rewrite Hk. rewrite nth_error_merge_lists_odd.
            ** simpl. rewrite Nat.add_0_r. rewrite add_n_n_twice. rewrite Nat.add_1_r. Search div2. rewrite <- Nat.Even_div2.
               rewrite Nat.div2_double. reflexivity. rewrite <- Nat.even_spec. rewrite <- add_n_n_twice. rewrite n_plus_n_even.
               reflexivity.
            ** rewrite size_list_equiv in H4. rewrite size_list_equiv in H4. assumption.
          * assumption.
Qed.

Lemma odd_double_sizeOrg : forall m, Nat.odd (m + m) = false.
Proof.
  intros m.
  rewrite Nat.odd_add. apply xorb_nilpotent.
Qed.

Lemma lookup_after_insert_Some {V} (t : BraunTree V) (v : V) :
  IsBraun t ->
  lookup (insert v t) (sizeOrg t) = Some v.
Proof.
  intros Hbraun. induction t.
  - simpl. reflexivity.
  - simpl. destruct (sizeOrg t1 =? sizeOrg t2) eqn:HS.
    + apply Nat.eqb_eq in HS. rewrite HS. simpl. rewrite n_plus_n_even. rewrite <- HS. rewrite div2_double.
      inversion Hbraun; subst. apply IHt1. assumption.
    + inversion Hbraun. apply Nat.eqb_neq in HS. simpl. destruct H4.
      * contradiction.
      * rewrite H4. assert (sizeOrg t2 + 1 + sizeOrg t2 = S(sizeOrg t2 + sizeOrg t2)). { lia. } 
        rewrite H5. Search Nat.even. rewrite Nat.even_succ. rewrite odd_double_sizeOrg. Search div2.
        rewrite add_n_n_twice. rewrite Nat.div2_succ_double. rewrite IHt2. reflexivity. assumption.
Qed.

Lemma div2_distinct_if_even_and_unequal :
  forall a b : nat,
  a <> b -> Nat.Even a -> Nat.Even b -> Nat.div2 a <> Nat.div2 b.
Proof.
  intros a b Hneq Hevena Hevenb.
  destruct Hevena as [a' Ha'].
  destruct Hevenb as [b' Hb'].
  intros H. rewrite Ha' in H. rewrite Hb' in H. simpl in H.
  assert (a' + (a' + 0) = a' + a'). { lia. }  rewrite H0 in H.
  assert (b' + (b' + 0) = b' + b'). { lia. } rewrite H1 in H. Search add. rewrite add_n_n_twice in H. rewrite add_n_n_twice in H.
   rewrite Nat.div2_double in H. rewrite Nat.div2_double in H. rewrite Ha' in Hneq. rewrite Hb' in Hneq. contradiction Hneq.
  rewrite H. reflexivity.
Qed.

Lemma div2_distinct_if_odd_and_unequal :
  forall a b : nat,
  a <> b -> Nat.Odd a -> Nat.Odd b -> Nat.div2 a <> Nat.div2 b.
Proof.
  intros a b Hneq Hodda Hoddb.
  destruct Hodda as [a' Ha'].
  destruct Hoddb as [b' Hb'].
  intros H. rewrite Ha' in H. rewrite Hb' in H. Search Nat.add. rewrite Nat.add_1_r in H. rewrite Nat.add_1_r in H.
  rewrite Nat.div2_succ_double in H. rewrite Nat.div2_succ_double in H. rewrite Ha', Hb' in Hneq. contradiction Hneq.
  f_equal. rewrite H. reflexivity.
Qed.

Lemma lookup_after_insert_lookup {V} (t : BraunTree V) (v : V) i :
  IsBraun t -> i <> sizeOrg t -> lookup (insert v t) i = lookup t i.
Proof.
  intros Hbraun. revert i. induction t; inversion Hbraun.
  + simpl. destruct i.
    * intros H. contradiction H. reflexivity.
    * intros H. destruct (Nat.even i); reflexivity.
  + destruct i; simpl.
    * intros. destruct ( sizeOrg t1 =? sizeOrg t2) eqn:heq.
      -- rewrite lookup_root. reflexivity.
      -- rewrite lookup_root. reflexivity.
    * intros Hyp. assert (S i <> S (sizeOrg t1 + sizeOrg t2) -> i <> sizeOrg t1 + sizeOrg t2). { lia. }
      destruct (sizeOrg t1 =? sizeOrg t2) eqn: Heq. simpl.
      -- destruct (Nat.even i) eqn:Hequiv.
        --- rewrite IHt1.
          ---- reflexivity.
          ---- assumption.
          ---- apply Nat.eqb_eq in Heq. apply H5 in Hyp. rewrite <- Heq in Hyp. apply div2_distinct_if_even_and_unequal in Hyp.
            *** rewrite add_n_n_twice in Hyp. rewrite Nat.div2_double in Hyp. assumption.
            *** apply Nat.even_spec in Hequiv. assumption.
            *** rewrite <- Nat.even_spec. rewrite n_plus_n_even. reflexivity.
        --- reflexivity.
      -- destruct (Nat.even i) eqn:Hequiv.
        --- simpl. rewrite Hequiv. reflexivity.
        --- simpl. rewrite Hequiv. rewrite IHt2.
          ---- reflexivity.
          ---- assumption.
          ---- apply Nat.eqb_neq in Heq. destruct H4.
              ++ contradiction.
              ++ apply H5 in Hyp. rewrite H4 in Hyp. apply div2_distinct_if_odd_and_unequal in Hyp.
                +++ assert (sizeOrg t2 + 1 + sizeOrg t2 = S(2 * sizeOrg t2)). { lia. } rewrite H6 in Hyp. 
                    rewrite Nat.div2_succ_double in Hyp. assumption.
                +++ Search Nat.even. apply Nat.odd_spec. unfold Nat.odd. rewrite Hequiv. simpl. reflexivity.
                +++ assert (sizeOrg t2 + 1 + sizeOrg t2 = S(sizeOrg t2 + sizeOrg t2)). { lia. } rewrite H6.
                    rewrite Nat.Odd_succ. rewrite <- Nat.even_spec. rewrite n_plus_n_even. reflexivity.
Qed.

Lemma lookup_after_insert : forall (V : Type) (t : BraunTree V) (v : V) (i : nat),
    IsBraun t -> 
    lookup (insert v t) i = 
    if i =? sizeOrg t then Some v else lookup t i.
Proof.
  intros. destruct (i =? sizeOrg t) eqn:Heq.
  - apply Nat.eqb_eq in Heq. rewrite Heq. rewrite lookup_after_insert_Some. reflexivity. assumption.
  - rewrite lookup_after_insert_lookup. reflexivity. assumption. apply Nat.eqb_neq in Heq.  assumption.
Qed.

(*PROOF UPDATE--------------------------------------------------------------------------------------------------------*)

Lemma update_root : forall (V : Type) (v v' : V) (l r : BraunTree V),
    update 0 v (Braun l v' r) = Braun l v r.
Proof.
  intros V v v' l r.
  simpl. reflexivity.
Qed.

Lemma succ_ge_succ_gt : forall i x : nat, S i >= S x -> S i > x.
Proof.
  intros i x H.
  apply le_S_n in H.
  unfold gt.
  lia.
Qed.

Lemma succ_ge_sizeOrg : 
    forall (V : Type) (i : nat) (l : BraunTree V),
      i >= sizeOrg l -> S i >= sizeOrg l.
  Proof.
    intros i l t H. lia.
  Qed.

Lemma succ_ge_succ : forall x y : nat, S x >= S y -> x >= y.
Proof.
  intros x y H.
  unfold ge in H.
  apply le_S_n.
  assumption.
Qed.

Lemma succ_ge_succ2 :
  forall x y : nat, x >= y -> S x >= S y.
Proof.
  intros x y H.
  apply le_n_S in H.
  assumption.
Qed.

Lemma nat_ge_S_impl_gt:
  forall x y : nat,
    x >= S y -> x > y.
Proof.
  intros x y H.
  unfold gt.
  lia.
Qed.

Lemma even_minus_one_even_eq:
  forall x y : nat,
    Nat.even x = true -> Nat.even y = true -> x - 1<= y -> x <= y.
Proof.
 intros x y Hx Hy. intro Hcond. destruct Hcond.
  - Search pred. rewrite <- PeanoNat.pred_of_minus in Hy. Search pred. destruct x.
    -- simpl. reflexivity.
    -- rewrite Nat.even_pred in Hy.
      --- exfalso. rewrite Nat.odd_spec in *. rewrite Nat.even_spec in Hx. Search Nat.Even.
          apply Nat.Even_Odd_False with (x := S x); assumption.
      --- lia.
  - apply succ_ge_succ2 in Hcond. lia.
Qed.

Lemma update_out_of_bounds:
  forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    IsBraun t ->
    i >= sizeOrg t ->
    update i v t = t.
Proof.
  intros V t.
  induction t as [|l IHl x r IHr]; intros i val Hbraun Hi; simpl in *.
  - reflexivity.
  - inversion Hbraun. destruct i as [| i'].
    + exfalso. lia.
    + destruct (Nat.odd (S i')) eqn:Hodd.
      * apply succ_ge_succ in Hi. rewrite Nat.odd_succ in Hodd. destruct H4.
        ** rewrite <- H4 in Hi. rewrite add_n_n_twice in Hi.  apply div2_ge in Hi. rewrite IHl; auto.
        ** apply succ_ge_succ2 in Hi. assert (S (sizeOrg l + sizeOrg r) = sizeOrg l + sizeOrg r + 1).
           { rewrite <- Nat.add_1_r. reflexivity. } rewrite H5 in Hi. assert ((S i' >= sizeOrg l + sizeOrg r + 1) = (S i' >= sizeOrg l + (sizeOrg r + 1))).
           { rewrite <- Nat.add_assoc. reflexivity. } rewrite H6 in Hi. rewrite <- H4 in Hi. rewrite add_n_n_twice in Hi.
           rewrite IHl; auto. apply div2_ge_even; auto.
      * simpl. Search minus. rewrite Nat.sub_0_r. apply succ_ge_succ in Hi. rewrite Nat.odd_succ in Hodd. destruct H4.
        ** rewrite H4 in Hi. rewrite add_n_n_twice in Hi. apply div2_ge in Hi. rewrite IHr; auto.
        ** rewrite H4 in Hi. Search add. assert (sizeOrg r + 1 + sizeOrg r = sizeOrg r + sizeOrg r + 1). { lia. } rewrite H5 in Hi. rewrite add_n_n_twice in Hi.
            rewrite IHr; auto. apply div2_ge. apply x_ge_y_plus_1_implies_x_ge_y. assumption.
Qed.

Lemma odd_even_div2:
  forall x y : nat,
    Nat.Odd x ->
    Nat.Even y ->
    x < y ->
    Nat.div2 x < Nat.div2 y.
Proof.
  intros x y [kx Hx] [ky Hy] Hlt. rewrite Hx in Hlt. rewrite Hy in Hlt. simpl in *. apply Nat.lt_le_incl in Hlt. 
  assert (kx < ky) as Hkxky.
  { rewrite Nat.add_0_r in Hlt. rewrite Nat.add_0_r in Hlt. apply (Nat.mul_lt_mono_pos_l 2). lia. 
    rewrite Nat.mul_succ_l. lia. } rewrite Hx, Hy. assert (2 * kx < 2 * ky) by lia. rewrite Nat.add_0_r. rewrite Nat.add_0_r.
    rewrite add_n_n_twice. rewrite add_n_n_twice. rewrite Nat.add_1_r. Search Nat.div2. rewrite <- Nat.Even_div2.
    - rewrite <- add_n_n_twice. rewrite div2_double. rewrite <- add_n_n_twice. rewrite div2_double. assumption.
    - assert (2 * kx = kx * 2) by lia. rewrite H0. apply Nat.Even_mul_r with (m := 2). exists 1. simpl. reflexivity.
Qed.

Lemma even_even_div2:
  forall x y : nat,
    Nat.Even x ->
    Nat.Even y ->
    x < y ->
    Nat.div2 x < Nat.div2 y.
Proof.
  intros x y [kx Hx] [ky Hy] Hlt. rewrite Hx in Hlt; rewrite Hy in Hlt. apply Nat.mul_lt_mono_pos_l with (p:=2) in Hlt; [ | lia ].
  rewrite Hx, Hy. simpl. rewrite Nat.add_0_r. rewrite Nat.add_0_r. rewrite div2_double. rewrite div2_double. assumption.
Qed.

Lemma odd_odd_div2:
  forall x y : nat,
    Nat.Odd x ->
    Nat.Odd y ->
    x < y ->
    Nat.div2 x < Nat.div2 y.
Proof.
  intros x y [kx Hx] [ky Hy] Hlt. rewrite Hx in Hlt; rewrite Hy in Hlt. assert (kx < ky) by lia. rewrite Hx, Hy. Search Nat.div2.
  rewrite Nat.add_1_r. rewrite Nat.add_1_r. rewrite <- Nat.Even_div2. rewrite <- Nat.Even_div2. rewrite Nat.div2_double.
  rewrite Nat.div2_double. assumption. rewrite <- Nat.even_spec. rewrite <- add_n_n_twice. rewrite n_plus_n_even; reflexivity.
  rewrite <- Nat.even_spec. rewrite <- add_n_n_twice. rewrite n_plus_n_even; reflexivity.
Qed.

Lemma lookup_after_update_Some {V} (t : BraunTree V) (i j : nat) (v : V) :
  IsBraun t -> i = j /\ i < sizeOrg t -> lookup (update i v t) j = Some v.
Proof.
  intros Hbraun. revert i j. induction t as [| tl IHl v' tr IHr].
  - simpl. intros i j. intro Hyp. destruct Hyp as [Hyp1 Hyp2]. assert (i < 0 = False). { lia. } rewrite H in Hyp2. contradiction.
  - intros i j Hyp. simpl. destruct i eqn:Hi.
    -- simpl. destruct j. reflexivity. destruct Hyp. discriminate H.
    -- simpl. rewrite Nat.sub_0_r. destruct (Nat.odd (S n)) eqn:Hodd.
      --- simpl. destruct j eqn:Hj.
        ---- destruct Hyp as [Hyp1 Hyp2]. discriminate Hyp1.
        ---- destruct (Nat.even n0) eqn:Heven.
          * apply IHl. inversion Hbraun; assumption. destruct Hyp as [Hyp1 Hyp2]. split.
            ** f_equal. assert (S n = S n0 -> n = n0) by lia. apply H in Hyp1. assumption.
            ** simpl in Hyp2. inversion Hbraun. assert (S n < S (sizeOrg tl + sizeOrg tr) -> n < sizeOrg tl + sizeOrg tr) by lia.
               apply H5 in Hyp2; clear H5. destruct H4.
              *** rewrite <- H4 in Hyp2. rewrite add_n_n_twice in Hyp2. rewrite Nat.odd_succ in Hodd. Search Nat.div2.
                  apply even_even_div2 in Hyp2. rewrite <- add_n_n_twice in Hyp2. rewrite div2_double in Hyp2. assumption.
                  rewrite Nat.even_spec in Hodd. assumption. assert (2 * sizeOrg tl = sizeOrg tl * 2) by lia. 
                  rewrite H5. apply Nat.Even_mul_r with (m := 2). exists 1. simpl. reflexivity.
              *** assert (n < sizeOrg tl + sizeOrg tl - 1) by lia. clear Hyp2. rewrite add_n_n_twice in H5. 
                  rewrite Nat.odd_spec in Hodd. rewrite Nat.Odd_succ in Hodd. assert (S n < 2 * sizeOrg tl) by lia. 
                  apply Nat.Even_div2 in Hodd. rewrite Hodd. rewrite <- Nat.double_twice in H6. Search Nat.div2. Search Nat.div2.
                  apply odd_even_div2 in H6.
                **** rewrite Nat.double_twice in H6. assert (Nat.div2 (2 * sizeOrg tl) = sizeOrg tl). 
                     { rewrite <- add_n_n_twice. rewrite div2_double. reflexivity. } rewrite <- H7; assumption. 
                **** assert (n = n0) by lia. rewrite <- H7 in Heven. rewrite <- Nat.odd_succ in Heven. rewrite <- Nat.odd_spec.
                     assumption.
                **** rewrite Nat.double_twice. assert (2 * sizeOrg tl = sizeOrg tl * 2) by lia. rewrite H7. apply Nat.Even_mul_r.
                     exists 1. simpl. reflexivity.
          * destruct Hyp. assert ( n = n0). { lia. } rewrite Nat.odd_succ in Hodd. rewrite H1 in Hodd. rewrite Hodd in Heven.
            discriminate Heven.
      --- simpl. destruct j eqn:Hj.
        ---- destruct Hyp as [Hyp1 Hyp2]. discriminate Hyp1.
        ---- destruct (Nat.even n0) eqn:Heven.
          * destruct Hyp. assert ( n = n0). { lia. } rewrite Nat.odd_succ in Hodd. rewrite H1 in Hodd. rewrite Hodd in Heven.
            discriminate Heven.
          * apply IHr. inversion Hbraun; assumption. split.
            ** f_equal. destruct Hyp. lia.
            ** destruct Hyp. assert (n = n0) by lia. rewrite Nat.odd_succ in Hodd. Search Nat.even. rewrite <- Nat.negb_odd in Hodd.
               rewrite <- Nat.negb_odd in Heven. Search negb. rewrite negb_false_iff in Hodd. rewrite negb_false_iff in Heven.
               simpl in H0. assert (n < sizeOrg tl + sizeOrg tr) by lia; clear H0. inversion Hbraun. destruct H7.
              *** rewrite H7 in H2. apply odd_even_div2 in H2.
                **** rewrite div2_double in H2. assumption.
                **** rewrite Nat.odd_spec in Hodd; assumption.
                **** rewrite <- Nat.even_spec. rewrite n_plus_n_even. reflexivity.
              *** rewrite H7 in H2. assert (sizeOrg tr + 1 + sizeOrg tr = S (2 * sizeOrg tr)) by lia. rewrite H8 in H2.
                  assert (Nat.div2 (2 * sizeOrg tr) = Nat.div2 (S (2 * sizeOrg tr))). apply Nat.Even_div2. 
                  rewrite <- Nat.even_spec. rewrite <- add_n_n_twice. rewrite n_plus_n_even. reflexivity. apply odd_odd_div2 in H2.
                **** rewrite <- H9 in H2. rewrite <- add_n_n_twice in H2. rewrite div2_double in H2. assumption.
                **** rewrite Nat.odd_spec in Hodd; assumption.
                **** rewrite <- Nat.odd_spec. rewrite Nat.odd_succ. rewrite <- add_n_n_twice. rewrite n_plus_n_even. reflexivity.
Qed.

Lemma lookup_after_update_Lookup {V} (t : BraunTree V) (i j : nat) (v : V) :
  IsBraun t -> i =? j = false -> lookup (update i v t) j = lookup t j.
Proof.
  intros Hbraun. revert i j. induction t as [|tl IHl v' tr IHr].
  - simpl. reflexivity.
  -  intros i j Hneq. simpl. destruct i eqn:Hi.
    -- destruct j eqn:Hj.
      --- simpl in Hneq. discriminate Hneq.
      --- simpl. destruct (Nat.even n).
        ---- reflexivity.
        ---- reflexivity.
    -- destruct j eqn:Hj.
      --- destruct (Nat.odd (S n)) eqn:Hodd.
        ---- simpl. reflexivity.
        ---- simpl. reflexivity.
      --- destruct (Nat.odd (S n)) eqn:Hodd.
        ---- simpl. destruct (Nat.even n0) eqn:Heven.
          * apply IHl with (i := (Nat.div2 n)).
            ** inversion Hbraun; assumption.
            ** rewrite Nat.odd_succ in Hodd. Search false. rewrite Nat.eqb_neq in Hneq.
            rewrite Nat.eqb_neq. apply div2_distinct_if_even_and_unequal.
              *** assert (S n <> S n0 -> n <> n0). { lia. } apply H in Hneq. assumption.
              *** apply Nat.even_spec in Hodd; assumption.
              *** apply Nat.even_spec in Heven; assumption. Compute Nat.even_spec.
          * reflexivity.
        ---- simpl. destruct (Nat.even n0) eqn:Heven.
          * reflexivity.
          * rewrite Nat.sub_0_r. apply IHr.
            ** inversion Hbraun; assumption.
            ** rewrite Nat.odd_succ in Hodd. Search Nat.odd. Search Nat.odd . Search negb. rewrite <- negb_true_iff in Hodd.
               rewrite <- negb_true_iff in Heven. Search Nat.even. rewrite Nat.negb_even in Hodd. rewrite Nat.negb_even in
               Heven. rewrite Nat.eqb_neq. rewrite Nat.odd_spec in Hodd. rewrite Nat.odd_spec in Heven.
               rewrite Nat.eqb_neq in Hneq. assert (S n <> S n0 -> n <> n0). { lia. } apply H in Hneq; clear H.
               apply div2_distinct_if_odd_and_unequal; assumption.
Qed.

Lemma lookup_after_update {V} (t : BraunTree V) (i j : nat) (v : V) :
  IsBraun t -> lookup (update i v t) j = if (i =? j) && (i <? sizeOrg t) then Some v else lookup t j.
Proof.
  intro Hbraun. destruct (i =? j) eqn:Heq.
    - destruct (i <? sizeOrg t) eqn:Hsize.
      -- simpl. apply lookup_after_update_Some. assumption. split.
        --- Search Nat.eqb. rewrite Nat.eqb_eq in Heq. assumption.
        --- Search Nat.leb. Search lt. rewrite Nat.ltb_lt in Hsize. assumption.
      -- simpl. rewrite update_out_of_bounds. reflexivity. assumption. rewrite Nat.ltb_nlt in Hsize.
         Search negb. assert (i >= sizeOrg t <-> sizeOrg t <= i). { lia. }  rewrite H. assert ( ~ i < sizeOrg t ->
         i >= sizeOrg t). { lia. } apply H0 in Hsize; assumption.
    - simpl. apply lookup_after_update_Lookup; assumption.
Qed.

Fixpoint upd {V : Type} (l : list V) (i : nat) (v : V) : list V :=
    match l, i with
    | [], _ => []
    | _::xs, 0 => v::xs
    | x::xs, S j => x::(upd xs j v)
    end.

Definition my_list : list nat := [0; 1; 2; 3].
Compute upd my_list 4 50.

Definition tree : BraunTree nat :=
    Braun (Braun (Braun Empty 3 Empty) 1 Empty) 0 (Braun Empty 2 Empty).
Compute tree.
Compute update 4 50 tree.

Lemma upd_S :
  forall (A : Type) (y : A) (xs : list A) (i : nat) (x : A),
    upd (y :: xs) (S i) x = y :: upd xs i x.
Proof. reflexivity. Qed.

Lemma upd_even_index : forall (V : Type) (l1 l2 : list V) (k : nat) (v : V), 
  length l1 = length l2 \/ length l1 = length l2 + 1 ->
  upd (merge_lists l1 l2) (2 * k) v = merge_lists (upd l1 k v) l2.
Proof.
  intros V l1 l2 k v Hlen.
  generalize dependent k.
  generalize dependent l2.
  induction l1 as [|x xs IHl1]; intros l2 k.
  - destruct k.
    -- simpl in H; symmetry in H;  rewrite length_zero_iff_nil in H. rewrite H; simpl. intro k. reflexivity.
    -- simpl in H. rewrite Nat.add_1_r in H. discriminate H.
  - destruct l2 as [|y ys].
    + destruct k as [Hlen|Hlen]; simpl in Hlen.
      * inversion Hlen.
      * simpl. destruct k.
        -- simpl. reflexivity.
        -- simpl. assert (S (length xs) = 1 -> length xs = 0) by lia. apply H in Hlen; clear H. rewrite length_zero_iff_nil in
           Hlen. rewrite Hlen. simpl. reflexivity.
    + intro k0. destruct k; simpl.
      * destruct k0. 
        ** simpl. reflexivity. 
        ** assert (S k0 + (S k0 + 0) = S (S (2 * k0))) by lia. rewrite H0. rewrite IHl1.
          *** rewrite merge_lists_twist_L. f_equal. rewrite merge_lists_twist_L. f_equal.
          *** left. simpl in H. lia.
      * destruct k0. 
        ** simpl. reflexivity.
        ** assert ((S k0 + (S k0 + 0)) = S (S (2 * k0))) by lia. simpl. assert (k0 + S (k0 + 0) = S(2 * k0)) by lia.
           rewrite  H1. rewrite IHl1.
          *** reflexivity.
          *** right. simpl in H. lia.
Qed.


Lemma upd_odd_index : forall (V : Type) (l1 l2 : list V) (k : nat) (v : V), 
  length l1 = length l2 \/ length l1 = length l2 + 1 ->
  upd (merge_lists l1 l2) (2 * k + 1) v = merge_lists l1 (upd l2 k v).
Proof.
  intros V l1 l2 k v Hlen.
  generalize dependent k.
  generalize dependent l1.
  induction l2 as [|x xs IHl2]; intros l1 k.
  - intro k0. destruct k.
    -- simpl in H;  rewrite length_zero_iff_nil in H. rewrite H; simpl. reflexivity.
    -- simpl in H. simpl. destruct l1.
      --- simpl in H. discriminate H.
      --- simpl in H. assert (length l1 = 0) by lia. rewrite length_zero_iff_nil in H0. rewrite H0. simpl.
          rewrite Nat.add_1_r. reflexivity.
  - destruct l1 as [|y ys].
    + destruct k as [Hlen|Hlen]; simpl in Hlen.
      * inversion Hlen.
      * simpl. destruct k.
        -- discriminate Hlen.
        -- discriminate Hlen.
    + intro k0. destruct k; simpl.
      * destruct k0. 
        ** simpl. reflexivity. 
        ** assert (S k0 + (S k0 + 0) = S (S (2 * k0))) by lia. rewrite H0. rewrite Nat.add_1_r. 
           f_equal; f_equal. rewrite <- Nat.add_1_r. apply IHl2. left. simpl in H. lia.
      * destruct k0. 
        ** simpl. reflexivity.
        ** assert (S k0 + (S k0 + 0) = S (S (2 * k0))) by lia. rewrite H0. rewrite Nat.add_1_r. 
           f_equal; f_equal. rewrite <- Nat.add_1_r. apply IHl2. right. simpl in H. lia.
Qed.

Lemma update_to_list_equiv : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    IsBraun t -> tree_to_list (update i v t) = upd (tree_to_list t) i v.
Proof.
 intros V t i v. intro HBraun. revert i. induction t as [|l IHl x r IHr].
  - simpl. reflexivity.
  - intros i. inversion HBraun. simpl. destruct i eqn:Hi.
    + simpl. reflexivity.
    + destruct (Nat.odd (S n)) eqn:Hodd.
      * simpl. f_equal. rewrite Nat.odd_succ in Hodd. apply Nat.even_spec in Hodd. destruct Hodd as [n0 Hn0]; subst.
        rewrite upd_even_index. 
        ** rewrite IHl.
          *** simpl. rewrite Nat.add_0_r. rewrite div2_double. reflexivity.
          *** inversion HBraun; assumption.
        ** repeat rewrite <- size_list_equiv. assumption. 
      * simpl. f_equal. rewrite Nat.sub_0_r. rewrite IHr with ( i := Nat.div2 n).
        ** rewrite <- Nat.negb_even in Hodd. rewrite negb_false_iff in Hodd. rewrite Nat.even_succ in Hodd.
           rewrite Nat.odd_spec in Hodd. destruct Hodd as [n0 Hn0]; subst. rewrite upd_odd_index.
          *** rewrite Nat.add_1_r. Search Nat.div2. rewrite Nat.div2_succ_double. reflexivity.
          *** repeat rewrite <- size_list_equiv. assumption.
        ** inversion HBraun; assumption.
Qed.

Lemma update_preserves_size:
  forall (V : Type) (t : BraunTree V) (n : nat) (v : V),
    sizeOrg (update n v t) = sizeOrg t.
Proof.
  induction t as [|l IHl x r IHr]; intros n val; simpl.
  - reflexivity.
  - destruct n as [| n']; simpl.
    + reflexivity.
    + destruct (Nat.odd (S n')) eqn:Hodd.
      * simpl. f_equal. assert (sizeOrg (update (Nat.div2 n') val l)=sizeOrg l) as Hass.
        { apply IHl with (v := val).  }
        rewrite Hass. reflexivity.
      * simpl. f_equal. assert (sizeOrg (update (Nat.div2 (n' - 0)) val r)=sizeOrg r) as Hass.
        { apply IHr with (v := val). }
        rewrite Hass. reflexivity. 
Qed.

Theorem zero_not_geq_one_plus : forall x y : nat, ~ (0 >= 1 + x + y).
Proof.
  intros x y.
  unfold not.
  intros H.
  inversion H.
Qed.

Lemma update_maintains_braun : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    IsBraun t -> IsBraun (update i v t).
Proof.
  intros V t i v Hbraun. revert i Hbraun.
  induction t as [| l IHl v' r IHr].
  - simpl. intros i H. assumption.
  - intros i Hbraun. destruct i.
    + simpl. inversion Hbraun; subst. constructor; assumption.
    + simpl. inversion Hbraun; subst. destruct (Nat.odd (S i)) eqn:Hodd.
      ** constructor.
        *** apply IHl with (i := (Nat.div2 i)); assumption.
        *** assumption.
        *** assert (sizeOrg (update (Nat.div2 i) v l) = sizeOrg l). { apply update_preserves_size. }
            rewrite H. assumption.
      ** constructor.
        *** assumption.
        *** rewrite Nat.sub_0_r. apply IHr with (i := (Nat.div2 i)); assumption.
        *** assert (sizeOrg (update (Nat.div2 (i - 0)) v r ) = sizeOrg r). { apply update_preserves_size. }
            rewrite H; assumption.
Qed.

Lemma update_idempotent : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    IsBraun t -> i >= sizeOrg t \/ lookup t i = Some v -> update i v t = t.
Proof.
  intros V t i v Hbraun Hcond. revert i Hcond.
  induction t as [| l IHl v' r IHr]. intros i Hcond.
  - reflexivity.
  - destruct i.
    + simpl. intro Hcond. destruct Hcond as [Hsize | Hlookup].
      * exfalso. simpl in Hsize. lia.
      * inversion Hlookup. reflexivity.
    + destruct (Nat.odd (S i)) eqn:Hodd.
      * simpl. rewrite Hodd. inversion Hbraun. intro Hcond. destruct Hcond as [Hsize | Hlookup].
        -- simpl in Hsize. apply Nat.succ_lt_mono in Hsize. rewrite Nat.odd_succ in Hodd. 
           assert (S (sizeOrg l + sizeOrg r) < S (S i) -> sizeOrg l + sizeOrg r < S i). { lia. }
           apply H5 in Hsize. rewrite IHl with (i := Nat.div2 i ). reflexivity. assumption. left. destruct H4.
          --- rewrite <- H4 in Hsize. assert (sizeOrg l + sizeOrg l < S i -> i >= 2 * sizeOrg l). { lia. }
              apply H6 in Hsize. apply div2_ge in Hsize. assumption.
          --- assert (sizeOrg r = sizeOrg l - 1). { lia. } rewrite H6 in Hsize. assert (sizeOrg l + (sizeOrg l - 1)
              = 2 * sizeOrg l - 1). { lia. } rewrite H7 in Hsize. assert (2 * sizeOrg l - 1 < S i -> 2 * sizeOrg l - 1 <= i).
              { lia. } apply H8 in Hsize. apply even_minus_one_even_eq in Hsize.  apply div2_ge in Hsize. assumption.
               rewrite <- add_n_n_twice. rewrite n_plus_n_even. reflexivity. assumption.
        -- rewrite IHl with (i := Nat.div2 i ). reflexivity. assumption. right. rewrite Nat.odd_succ in Hodd.
           rewrite Hodd in Hlookup. assumption.
      * simpl. rewrite Hodd. inversion Hbraun. intro Hcond. destruct Hcond as [Hsize | Hlookup].
        -- rewrite Nat.sub_0_r. rewrite IHr with (i := Nat.div2 i ).
          --- reflexivity.
          --- assumption.
          --- left. destruct H4.
            ---- rewrite H4 in Hsize. apply succ_ge_succ in Hsize. rewrite add_n_n_twice in Hsize. apply div2_ge. assumption.
            ---- rewrite H4 in Hsize. apply succ_ge_succ in Hsize. assert (sizeOrg r + 1 + sizeOrg r = S (2 * sizeOrg r)).
                 { lia. } rewrite H5 in Hsize. apply div2_ge. Search plus. rewrite <- Nat.add_1_r in Hsize.
                 apply x_ge_y_plus_1_implies_x_ge_y in Hsize. assumption.
        -- rewrite Nat.sub_0_r. rewrite IHr with (i := Nat.div2 i).
          --- reflexivity.
          --- assumption.
          --- rewrite Nat.odd_succ in Hodd. rewrite Hodd in Hlookup. right. assumption.
Qed.

(*PROOF REPLICATE--------------------------------------------------------------------------------------------------------*)
Lemma replicate_size : forall {V : Type} (x : V) (n : nat),
  sizeOrg (replicate x n) = n.
Proof.
  intros. induction n as [|n'].
  - simpl. reflexivity.
  - simpl. rewrite size_insert_inc. rewrite IHn'. lia.
Qed.

Lemma replicate_is_braun : forall {V : Type} (x : V) (n : nat) ,
  IsBraun (replicate x n).
Proof.
  intros. induction n as [| n' IH].
  - simpl. constructor.
  - simpl. apply insert_maintains_braun. assumption.
Qed.

Lemma lookup_replicate : forall {V : Type} (x : V) (n i : nat),
  i < n ->
  lookup (replicate x n) i = Some x.
Proof.
  intros V x n.
  induction n as [| n' IH].
  - intros i Hi. lia.
  - intros i Hi. simpl replicate. destruct (Nat.eq_dec i n') as [Heq | Hneq].
    + subst i. assert (sizeOrg (replicate x n') = n'). { rewrite replicate_size. reflexivity. }
      assert (Hbraun: IsBraun (replicate x n')). { apply replicate_is_braun. }
      assert (Hsize: sizeOrg (replicate x n') = n') by apply replicate_size.
      rewrite <- Hsize at 2. apply insert_last_lookup; auto.
    + assert (Hi' : i < n') by lia. apply IH in Hi'. assert (Hbraun: IsBraun (replicate x n')) by apply replicate_is_braun. 
      rewrite lookup_after_insert by auto. destruct (i =? sizeOrg (replicate x n')).
      * reflexivity.
      * rewrite IH. reflexivity. lia. 
Qed. 

(*PROOF TREE-TO-LIST--------------------------------------------------------------------------------------------------------*)
(*
Lemma length_merge_lists : forall (V : Type) (l r : BraunTree V),
    length (merge_lists l r) = length l + length r.
Proof.
  intros V l r.
  generalize dependent r.
  induction l as [| x xs IHxs]; intros r.
  - simpl. reflexivity.
  - destruct r as [| y ys].
    + simpl. rewrite Nat.add_0_r. reflexivity.
    + simpl. rewrite IHxs. simpl. lia.
Qed.
*)
(*PROOF LIST-TO-TREE--------------------------------------------------------------------------------------------------------*)


(*OKASAKI PROOF--------------------------------------------------------------------------------------------------------*)

Lemma diff_size_tree : forall (V : Type) (t : BraunTree V),
  IsBraun t -> diff t (sizeOrg t) = 0.
Proof.
  intros. revert H. induction t as [| l Hl v r Hr].
  - simpl. reflexivity.
  - revert Hl Hr. simpl. destruct (sizeOrg l + sizeOrg r) eqn:Hsz.
    + reflexivity.
    + inversion H; subst. destruct H5.
      * rewrite H0 in Hsz. apply Hl in H3. apply Hr in H4. rewrite add_n_n_twice in Hsz. destruct (even n) eqn:Hevv.
        ** admit. (*I need to prove that S n/2 = (S n) / 2 but n is even so it is not correct*)
        ** assert (S n = Nat.div2 (2 * (S n))). { rewrite Nat.div2_double. reflexivity. } rewrite H1 in Hsz. admit.
      * admit.
Admitted.

Lemma okasaki_alg_1_proof : forall (V: Type) (t : BraunTree V),
  IsBraun t -> sizeOrg t = size t.
Proof.
  intros v t Hyp.
  induction t as [| l IHl v' r IHr].
  - simpl. reflexivity.
  - simpl. rewrite Nat.add_0_r. inversion Hyp. apply IHl in H2.  apply IHr in H3. destruct H4. 
    + rewrite H2, H3. rewrite H2, H3 in H4. rewrite <- H4. assert ( diff l (size l) = 0). { admit. }
      rewrite H5. lia.
    + rewrite H2, H3. rewrite H2, H3 in H4. rewrite H4. assert ( diff l (size r) = 1). {admit. }
      rewrite H5. lia. Admitted.
  