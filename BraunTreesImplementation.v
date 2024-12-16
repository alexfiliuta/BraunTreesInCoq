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
(* OKASAKI ALGORITHM 2 *)
Fixpoint copy2 {V: Type} (x : V) (n : nat) : (BraunTree V * BraunTree V) :=
  match n with
  | 0 => ( Braun Empty x Empty, Empty)
  | S m =>
    if even m then
    let (l, r) := copy2 x (div2 m) in (Braun l x l, Braun l x r)
    else
    let (l, r) := copy2 x (div2 m) in (Braun l x r, Braun r x r)
  end.
Definition copy {V: Type} (x: V) (n : nat) : BraunTree V :=
  snd (copy2 x n).
*)
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

(*lookup n+1 of a tree in which i removed root*)

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

Lemma removeRoot_list_concat {V : Type} (l1 r1 : BraunTree V) (v1 lv : V) (newL : BraunTree V):
  removeRoot (Braun l1 v1 r1) = Some (lv, newL) ->
  tree_to_list newL = tree_to_list l1 ++ tree_to_list r1.
Proof.
intros H.
simpl in H.
destruct l1.
- inversion H; subst. simpl. destruct r1; inversion H. reflexivity.
- simpl in H. destruct l1_1 as [|x1 x2 x3].
  + inversion H; subst; simpl. destruct l1_2 as [|x1 x2 x3]. inversion H. simpl. f_equal. admit. discriminate H.
  + destruct (removeRoot (Braun x1 x2 x3)) as [ [z newT] | ] eqn:Hroot.
    * inversion H; subst; simpl. (* Apply inductive hypothesis to newT *)
      remember (tree_to_list (Braun r1 lv newT)) as newL_list.
      simpl in HeqnewL_list. destruct (tree_to_list l1_2) as [|xs] eqn:Hex. f_equal.
      ** inversion H. admit.
      ** admit.
    * discriminate H.
Admitted.

Lemma remove_to_list_equiv {V : Type} (t : BraunTree V) (v : V) :
    IsBraun t -> forall t', removeRoot t = Some (v, t') -> tree_to_list t = v :: (tree_to_list t').
Proof.
  intros Hbraun t' Hassumption.
  destruct t as [|l v' r].
  - simpl in Hassumption. discriminate Hassumption.
  - simpl in Hassumption. inversion Hbraun; subst; clear Hbraun.
    destruct l as [|l1 v1 r1] eqn:Hol.
    + simpl in Hassumption. destruct r as [|lr vr rr] eqn:Hor.
      * inversion Hassumption; subst; clear Hassumption. simpl. reflexivity.
      * discriminate Hassumption.
    + destruct (removeRoot (Braun l1 v1 r1)) as [[lv newL] |] eqn:Hrem; inversion Hassumption; subst; clear Hassumption.
      simpl. f_equal.
      * assert (Htl: tree_to_list (Braun l1 v1 r1) = v1 :: merge_lists (tree_to_list l1) (tree_to_list r1)).
        { simpl. reflexivity. } rewrite <- Htl.
       destruct r as [|lr vr rr] eqn:Hr; simpl; f_equal. 
        ** apply removeRoot_value_eq in Hrem. assumption.
        ** simpl in Hrem. destruct l1 eqn:HL. inversion Hrem;auto. destruct r1. inversion H0;auto. discriminate  H0. 
           destruct (removeRoot (Braun b1 v0 b2)) as [ [z newT] | ] eqn:Hroot. simpl. admit. admit. 
        ** apply removeRoot_value_eq in Hrem. assumption.
        ** destruct (tree_to_list newL) as [|restL] eqn:HnewL.
          *** f_equal. destruct Hrem. simpl. admit.
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
    + simpl.
      destruct (Nat.even i) eqn:Heven.
      * rewrite Nat.even_spec in Heven. simpl in Hi. apply Nat.succ_le_mono in Hi.
        simpl in Heven. destruct Heven as [k Hk]. rewrite Hk. simpl. apply IHl; auto. rewrite Hk in Hi. simpl in Hi. destruct SizeCond.
        ** rewrite <- H in Hi. assert (Nat.div2 (2 * k) = k) as Hdiv.
      { simpl. rewrite <- plus_n_O at 1. rewrite <- Nat.div2_double. rewrite add_n_n_twice. reflexivity. }
        rewrite add_n_n_twice in Hi. rewrite <- plus_n_O in Hi. rewrite add_n_n_twice in Hi. rewrite <- plus_n_O. rewrite add_n_n_twice.
        rewrite Hdiv. lia.
        ** admit.
      * 
specialize (IHr Hr (Nat.div2 i) k_ge_r).
assumption.
Admitted.

Lemma div2_less_implies_double_less : forall i s : nat,
  Nat.div2 i < s -> i < 2 * s.
Proof.
  intros i s H.
  destruct (Nat.even i) eqn:E.
  - rewrite (Nat.even_spec i) in E.
    destruct E as [k Hk]; subst i.
    admit.
  - rewrite <- negb_true_iff in E. rewrite (Nat.odd_spec i) in E.
    destruct E as [k Hk]; subst i. rewrite Nat.add_1_r in H.
    rewrite Nat.div2_succ_double in H.
    assert (2 * k + 1 = S (2 * k)) by lia.
    admit.
Admitted.

Lemma lookup_implies_valid_index : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
  IsBraun t -> lookup t i = Some v -> i < sizeOrg t.
Proof.
  intros V t i v HBraun Hlookup.
  induction t as [|].
  - simpl in Hlookup. discriminate Hlookup.
  - destruct i as [|].
    + simpl. lia.
    +  simpl in Hlookup.
      destruct (Nat.even i) eqn:Heven.
      * assert (IsBraun t1 -> lookup t1 (Nat.div2 i) = Some v -> Nat.div2 i < sizeOrg t1) as HsizeL.
        { admit. }
        simpl. apply lt_S. inversion HBraun. apply HsizeL in H2. 
        ** apply div2_less_implies_double_less in H2. destruct H4.
          *** rewrite <- H4. lia.
          *** admit.
        ** assumption.
      * admit.
Admitted.

Search nth_error.

Lemma lookup_to_list_equiv : forall (V : Type) (t : BraunTree V) (i : nat),
    IsBraun t -> lookup t i = nth_error (tree_to_list t) i.
Proof.
  intros V t i Hbraun.
  generalize dependent i.
  induction t as [| l IHl v r IHr].
  - intros i. simpl. Admitted.

Lemma odd_double_sizeOrg : forall m, Nat.odd (m + m) = false.
Proof.
  intros m.
  rewrite Nat.odd_add. apply xorb_nilpotent.
Qed.

Lemma lookup_after_insert : forall (V : Type) (t : BraunTree V) (v : V) (i : nat),
    IsBraun t -> 
    lookup (insert v t) i = 
    if i =? sizeOrg t then Some v else lookup t i.
Proof.
  intros. destruct (i =? sizeOrg t) eqn:Heq.
  - apply Nat.eqb_eq in Heq. rewrite Heq. induction t.
    + simpl. reflexivity.
    + simpl. destruct (sizeOrg t1 =? sizeOrg t2) eqn:HS.
      * apply Nat.eqb_eq in HS. rewrite HS. simpl. rewrite n_plus_n_even. rewrite <- HS. rewrite div2_double. inversion H; subst. apply IHt1 in H3. assumption.
        admit.
      * simpl. rewrite Nat.eqb_neq in HS. inversion H. destruct H5.
         -- contradiction. 
         -- rewrite H5. simpl. Search Nat.even. assert ((sizeOrg t2 + 1 + sizeOrg t2) =
        (sizeOrg t2 + sizeOrg t2 + 1)). { lia. } rewrite H6. rewrite <- plus_n_Sm. rewrite Nat.even_succ. rewrite <- plus_n_O. rewrite odd_double_sizeOrg.
        apply IHt2 in H4. rewrite add_n_n_twice. rewrite Nat.div2_succ_double. assumption.
         admit.
  - rewrite Nat.eqb_neq in Heq. induction t.
    + simpl. destruct i. rewrite size_empty in Heq. contradiction Heq. reflexivity. destruct (Nat.even i); reflexivity.
    + destruct i. simpl.
      * destruct (sizeOrg t1 =? sizeOrg t2); simpl; reflexivity.
      * simpl. destruct (sizeOrg t1 =? sizeOrg t2) eqn:Hequiv.
        ** admit.
        ** admit.
Admitted.


(* ADD THE REMOVE*) 

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

Lemma div2_ge : forall i x : nat, i >= 2 * x -> Nat.div2 i >= x.
Proof.
  intros i x H.
  assert (Hdiv: 2 * x / 2 = x). { rewrite <- Nat.div_mul with (b := 2).  - rewrite Nat.mul_comm at 1. reflexivity. - lia. }
  rewrite <- Hdiv.
  apply Nat.le_trans with (m := i / 2).
  - apply Nat.div_le_mono with (c := 2); lia.
  - rewrite <- Nat.div2_div; apply Nat.le_refl.
Qed.

Lemma x_ge_y_plus_1_implies_x_ge_y : forall x y : nat,
  x >= y + 1 -> x >= y.
Proof.
  intros x y H.
  apply Nat.le_trans with (m := y + 1); auto with arith.
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

Lemma lookup_after_update : forall (V : Type) (t : BraunTree V) (i j : nat) (v : V),
    IsBraun t -> i < sizeOrg t ->
    lookup (update i v t) j = (if Nat.eqb i j then Some v else lookup t j).
Proof.
  intros V t.  induction t as [|l IHl x r IHr]; intros i j val Hbraun Hi; simpl in *.
  - inversion Hi.
  - inversion Hbraun.
    destruct i as [| i'].
    + destruct j as [|j'].
      * simpl. reflexivity.
      * simpl. destruct (Nat.odd (S j')) eqn:Hodd.
        -- reflexivity.
        -- reflexivity.
    + destruct (Nat.odd (S i')) eqn:Hiodd.
      * simpl. destruct j as [| j'].
        -- reflexivity.
        -- admit.
      * simpl. destruct j as [|j'].
        -- reflexivity.
        -- destruct (Nat.odd (S j')) eqn:Hjodd.
            --- assert (Nat.even j' = true) as Hev. { rewrite Nat.odd_succ in Hjodd. assumption. } rewrite Hev. rewrite Nat.odd_succ in Hiodd.
                assert (i' =? j' = false) as Hequal. { admit. } rewrite Hequal. reflexivity.
            --- assert (Nat.even j' = false) as Hev. { rewrite Nat.odd_succ in Hjodd. assumption. } rewrite Hev. admit.
Admitted.

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

Lemma update_to_list_equiv : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    IsBraun t -> tree_to_list (update i v t) = upd (tree_to_list t) i v.
Proof.
 intros V t i v. intro HBraun. induction t as [|l IHl x r IHr].
  - simpl. reflexivity.
  - inversion HBraun. simpl. destruct i as [| i'].
    + simpl. reflexivity.
    + destruct (Nat.odd (S i')) eqn:Hodd.
      * simpl. f_equal. destruct l as [|l' v_l r'].
        ** simpl. destruct H4. 
          *** simpl in H4. rewrite size_list_equiv in H4.
           assert (0 = length (tree_to_list r) -> length (tree_to_list r) = 0). { lia. }
           apply H5 in H4. rewrite length_zero_iff_nil in H4. rewrite H4. simpl. reflexivity.
          *** simpl in H4. rewrite size_list_equiv in H4. assert (Himp: 0 = length (tree_to_list r) + 1 -> False).
         { intros HF. admit. }
         exfalso. apply Himp. exact H4.
      ** admit.
    * simpl. f_equal. admit.
Admitted.

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

Lemma update_idempotent:
  forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    IsBraun t ->
    i < sizeOrg t ->
    lookup t i = Some v ->
    update i v t = t.
Proof.
  intros V t.
  induction t as [| l IHl x r IHr]; intros i val Hbraun Hi Hlookup; simpl in *.
  - inversion Hi.
  - admit.
Admitted.

Lemma update_idempotence : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    IsBraun t -> i < sizeOrg t -> lookup t i = Some v -> update i v t = t.
Proof.
  intros V t i v Hbraun Hlt Hlookup.
  induction t as [| l IHl v' r IHr].
  - simpl in Hlt. lia.
  - simpl in Hlt. simpl in Hlookup.
    destruct i.
    + simpl. inversion Hlookup. subst. reflexivity.
    + simpl. destruct (Nat.odd i) eqn:Hodd.
      * simpl in Hlookup. Admitted.

Lemma update_maintains_braun : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    IsBraun t -> i < sizeOrg t -> IsBraun (update i v t).
Proof.
  intros V t i v Hbraun Hlt.
  induction t as [| l IHl v' r IHr].
  - simpl in Hlt. lia.
  - simpl in Hlt. destruct i.
    + simpl. inversion Hbraun; subst.
      constructor; assumption.
    + simpl. inversion Hbraun; subst. destruct (Nat.odd (S i)) eqn:Hodd.
      ** constructor.
        *** rewrite <- PeanoNat.Nat.succ_lt_mono in Hlt. rewrite <- Nat.div2_succ_double in Hlt. destruct H4.
          ++ rewrite <- H in Hlt. admit.
          ++ admit.
        *** assumption.
        *** admit.
      ** simpl.
      * Admitted.

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
  intros. induction t as [| l Hl v r Hr].
  - simpl. reflexivity.
  - simpl. destruct (sizeOrg l + sizeOrg r) eqn:Hsz.
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
  