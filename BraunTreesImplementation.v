(*Imports:*)

Require Import Nat.
Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

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
    else diff l (div2 m)
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

Lemma contradictory_case : forall (V : Type) (l r : BraunTree V) (v' v : V),
  sizeOrg l <> sizeOrg r ->
  sizeOrg l - sizeOrg r = 0 ->
  False.
Proof.
  intros V l r v' v Heq Hd.
  apply Nat.sub_0_le in Hd as Hle_lr.
  assert (Hle_rl: sizeOrg r <= sizeOrg l). {
    apply Nat.le_trans with (sizeOrg r + (sizeOrg l - sizeOrg r)).
    - rewrite Hd. lia.
    - rewrite Hd. clear Hle_lr. apply Nat.sub_0_le in Hd. rewrite Nat.add_0_r. apply neq_cases in Heq. destruct Heq as [Hlt | Hgt].
      ++ Admitted.

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
        
(* loookup an element different from the one that was inserted = lookup the element ??? The same as in lookup ???*)



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
    + simpl. admit.
    + simpl in H.
      simpl.
      f_equal.
      rewrite cons_inj_iff.
      simpl in H.
      apply eq_add_S in H.
      apply IH. assumption.
Admitted.

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


Lemma size_remove_braun_empty:
  forall (V : Type) (l : BraunTree V) (v' : V) (r : BraunTree V),
    IsBraun (Braun l v' r) ->
    remove (Braun l v' r) = Some Empty ->
    sizeOrg (Braun l v' r) = 1.
Proof.
  intros V l v' r Hbraun Hrem.
  unfold remove in Hrem.
  Admitted.




Lemma size_remove_dec : forall (V : Type) (t : BraunTree V),
    IsBraun t -> forall t', remove t = Some t' -> sizeOrg t' = sizeOrg t - 1.
Proof.
    intros V t Hbraun t' Hassumption. induction t as [|l IHl v' r IHr].
  - discriminate.
  - induction t' as [|l' IHl' v'' r' IHr'].
    + apply size_remove_braun_empty in Hassumption. rewrite Hassumption. simpl. reflexivity. assumption.
    + unfold remove in Hassumption. simpl in Hassumption. remember (removeRoot (Braun l v' r)) as remRoot.
      destruct remRoot as [(rootV, newT)|] eqn:HremRoot; try discriminate Hassumption. Admitted.





Check skipn.
Lemma remove_to_list_equiv : forall (V : Type) (t : BraunTree V) (v : V),
    IsBraun t -> forall t', removeRoot t = Some (v, t') -> 
    tree_to_list t = v :: tree_to_list t' /\ tree_to_list t' = skipn 1 (tree_to_list t).
Proof.
  intros V t v Hbraun t' HremoveRoot.
  induction t as [| l IHl v' r IHr].
  - simpl in HremoveRoot. discriminate.
  - simpl in HremoveRoot.
    destruct l as [| ll lval lr].
    + destruct r as [| rl rval rr].
      * inversion HremoveRoot; subst. simpl. split.
        -- reflexivity.
        -- simpl. reflexivity.
      * simpl in HremoveRoot. discriminate.
    + Admitted.





Lemma remove_maintains_braun : forall (V : Type) (t : BraunTree V),
    IsBraun t -> forall t', remove t = Some t' -> IsBraun t'.
Proof.
  intros V t Hbraun t' Hremove.
  unfold remove in Hremove.
  destruct (removeRoot t) as [[v' newT] | ] eqn:HremoveRoot; inversion Hremove; subst; clear Hremove.
  destruct t as [| l v'' r].
  - inversion HremoveRoot. (* Empty case should never happen because removeRoot on Empty should return None *)
  - inversion Hbraun; subst; clear Hbraun.
    remember (removeRoot l) as remL.
    destruct remL as [[lv newL] |]; inversion HremoveRoot; subst; clear HremoveRoot.
    + simpl. induction t' as [|l' IHl' vx r' IHr'].
      * constructor.
      * admit.
    + induction t' as [|l' IHl' vx r' IHr'].
Admitted.



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
(*
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
        rewrite <- Nat.div2_double, <- Heven in Hi.
        rewrite Nat.div2_double in Hi by assumption.
        apply IHl in Hi; assumption.
      * (* Odd case, lookup in right subtree *)
        apply Nat.odd_spec in Heven.
        rewrite <- Heven in Hi.
        simpl in Hi. apply Nat.succ_le_mono in Hi.
        rewrite Nat.div2_succ_double in Hi by assumption.
        apply IHr in Hi; assumption.
Qed.
*)

Lemma lt_S : forall x y, x < y -> S x < S y.
Proof.
  intros x y H.
  apply lt_n_S.
  apply H.
Qed.

Lemma lookup_implies_valid_index : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
  IsBraun t -> lookup t i = Some v -> i < sizeOrg t.
Proof.
  intros V t i v HBraun Hlookup.
  induction t as [| l IHl x r IHr].
  - simpl in Hlookup. discriminate Hlookup.
  - simpl in Hlookup.
    destruct i as [|i'].
    + simpl. lia.
    + simpl in Hlookup.
      destruct (Nat.even i') eqn:Heven.
      * assert (Nat.div2 i' < sizeOrg l) as HsizeL.
        { admit. }
        simpl. apply lt_S. inversion HBraun. destruct H4.
        ** rewrite <- H4. rewrite add_n_n_twice. admit.
        ** admit.
      * assert (Nat.div2 i' < sizeOrg r) as HsizeR.
        admit. admit.
Admitted.

Search nth_error.
Lemma lookup_to_list_equiv : forall (V : Type) (t : BraunTree V) (i : nat),
    IsBraun t -> lookup t i = nth_error (tree_to_list t) i.
Proof.
  intros V t i Hbraun.
  generalize dependent i.
  induction t as [| l IHl v r IHr].
  - intros i. simpl. Admitted.

Lemma lookup_after_insert : forall (V : Type) (t : BraunTree V) (v : V) (i : nat),
    IsBraun t -> 
    lookup (insert v t) i = 
    if i =? sizeOrg t then Some v else lookup t i.
Proof.
  intros V t v i Hbraun.
  generalize dependent i.
  induction t as [| l IHl v' r IHr].
  - intros i. simpl. destruct i.
    + simpl. reflexivity.
    + simpl. destruct i.
      * simpl. reflexivity.
      * simpl. Admitted.

(*PROOF UPDATE--------------------------------------------------------------------------------------------------------*)

Lemma update_maintains_braun : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    IsBraun t -> i < sizeOrg t -> IsBraun (update i v t).
Proof.
  intros V t i v Hbraun Hlt.
  induction t as [| l IHl v' r IHr].
  - simpl in Hlt. lia.
  - simpl in Hlt.
    destruct i.
    + simpl. inversion Hbraun; subst.
      constructor; assumption.
    + simpl. inversion Hbraun; subst.
      destruct (Nat.odd i) eqn:Hodd.
      * Admitted.

Lemma update_root : forall (V : Type) (v v' : V) (l r : BraunTree V),
    update 0 v (Braun l v' r) = Braun l v r.
Proof.
  intros V v v' l r.
  simpl. reflexivity.
Qed.

Lemma update_out_of_bounds : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    i >= sizeOrg t -> update i v t = t.
Proof.
  intros V t i v Hge.
  induction t as [| l IHl v' r IHr].
  - simpl. reflexivity.
  - simpl in Hge. simpl.
    destruct i.
    + simpl in Hge. lia.
    + destruct (Nat.odd i) eqn:Hodd.
      * Admitted.


Lemma lookup_after_update : forall (V : Type) (t : BraunTree V) (i j : nat) (v : V),
    IsBraun t -> i < sizeOrg t ->
    lookup (update i v t) j = if i =? j then Some v else lookup t j.
Proof.
  intros V t i j v Hbraun Hlt.
  generalize dependent j.
  induction t as [| l IHl v' r IHr].
  - simpl in Hlt. lia.
  - intros j.
    simpl in Hlt.
    simpl. destruct i.
    + simpl. destruct j.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + simpl. destruct (Nat.odd i) eqn:Hodd.
      * destruct j.
        -- simpl. Admitted.

Fixpoint upd {V : Type} (l : list V) (i : nat) (v : V) : list V :=
    match l, i with
    | [], _ => []
    | _::xs, 0 => v::xs
    | x::xs, S j => x::(upd xs j v)
    end.

Lemma update_to_list_equiv : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    IsBraun t -> i < sizeOrg t ->
    tree_to_list (update i v t) = upd (tree_to_list t) i v.
Proof. Admitted.

Lemma size_update_const : forall (V : Type) (t : BraunTree V) (i : nat) (v : V),
    IsBraun t -> i < sizeOrg t -> sizeOrg (update i v t) = sizeOrg t.
Proof.
  intros V t i v Hbraun Hlt.
  induction t as [| l IHl v' r IHr].
  - simpl in Hlt. lia.
  - simpl in Hlt. simpl.
    destruct i.
    + simpl. reflexivity.
    + simpl. destruct (Nat.odd i) eqn:Hodd.
      * Admitted.

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

 Search nth_error.
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
  