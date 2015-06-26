Require Import List NArith.
Import N.

Local Open Scope list_scope.
Local Open Scope N_scope.


Module BV.

  Definition t := (list bool * N)%type.

  Definition empty : t := (nil, 0).

  Definition concat (b1 b2 : t) : t :=
    let (b1, n1) := b1 in
    let (b2, n2) := b2 in
    (b1 ++ b2, n1 + n2).

  Definition bvnot (bv1 : t) : t :=
    let (b1, n1) := bv1 in
    (List.map negb b1, n1).

  (* how to ensure they have same N? *)
  Fixpoint bl_map2 (l1 : list bool) (l2 : list bool)
                   (f : bool -> bool -> bool) : list bool :=
    match l1 with
      | nil => nil
      | cons b1 tl1 =>
        match l2 with
          | nil => nil
          | cons b2 tl2 => cons (f b1 b2) (bl_map2 tl1 tl2 f)
        end
    end.

  Definition bvand (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (bl_map2 b1 b2 andb, n1).

  Definition bvor (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (bl_map2 b1 b2 orb, n1).

  Definition bvxor (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (bl_map2 b1 b2 xorb, n1).

  Definition bvlow (bv1 : t) : bool :=
    let (b1, n1) := bv1 in
    match b1 with
      | nil => false
      | x :: _ => x
    end.

  Definition bvhigh (bv1 : t) : bool :=
    let (b1, n1) := bv1 in
    (List.last b1 false).

  Definition bvshiftleft (bv1 : t) : t :=
    let (b1, n1) := bv1 in
    (cons false (List.removelast b1), n1).

  Definition bvshiftright (bv1 : t) : t :=
    let (b1, n1) := bv1 in
    ((List.tl b1) ++ (cons false nil), n1).

  Fixpoint bvshiftleft_n (bv1 : t) (n1 : nat) : t :=
    match n1 with
      | O => bv1
      | S n2 => bvshiftleft_n (bvshiftleft bv1) n2
    end.

  Fixpoint bvshiftright_n (bv1 : t) (n1 : nat) : t :=
    match n1 with
      | O => bv1
      | S n2 => bvshiftright_n (bvshiftright bv1) n2
    end.

  Fixpoint bl2n (l : list bool) (c : N) (c2 : N) : N :=
    match l with
      | nil => c
      | cons true l2 => bl2n l2 (c + c2) (c2 + c2)
      | cons false l2 => bl2n l2 c (c2 + c2)
    end.

  Definition bv2n (bv1 : t) : N :=
    let (b1, n1) := bv1 in
    (bl2n b1 0 1).

  Fixpoint nb2bl (n : positive) : list bool :=
    match n with
      | xO p => false :: nb2bl p
      | xI p => true :: nb2bl p
      | xH => true :: nil
    end.

  Definition n2bl (n : N) : list bool :=
    match n with
      | 0 => cons false nil
      | 1 => cons true nil
      | pos p => nb2bl p
    end.

  Definition bvadd (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 + n4) in
    let b3 := (n2bl n5) in
    (b3, n1).

  Definition bvsub (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 - n4) in
    let b3 := (n2bl n5) in
    (b3, n1).

  Definition bvmul (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 * n4) in
    let b3 := (n2bl n5) in
    (b3, n1).

  Definition bvneg (bv1 : t) (n : N) : t :=
    let (b1, n1) := bv1 in
    let n2 := 2 ^ n in
    let n3 := (bv2n bv1) in
    let n4 := n2 - n3 in
    ((n2bl n4), n).

  Definition bvudiv (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n4 := (bv2n bv2) in
    match n4 with
      | 0 => (nil, 0)
      | _ =>
      let n3 := (bv2n bv1) in
      ((n2bl (n3 / n4)), n1)
    end.

  Definition bvurem (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n4 := (bv2n bv2) in
    match n4 with
      | 0 => (nil, 0)
      | _ =>
      let n3 := (bv2n bv1) in
      ((n2bl (n3 mod n4)), n1)
    end.

  Definition bvult (bv1 : t) (bv2 : t) :=
    let n1 := (bv2n bv1) in
    let n2 := (bv2n bv2) in
    (n1 < n2).

  Fixpoint drop_n (l : list bool) (n : nat) : list bool :=
    match n with
      | O => l
      | S n2 => drop_n (@List.tl bool l) n2
    end.

  Fixpoint first_n (l : list bool) (n : nat) : list bool :=
    match n with
      | O => nil
      | S n2 =>
      match l with
        | nil => nil
        | x :: l2 => x :: (first_n l2 n2)
      end
    end.

  Definition extract (l : list bool) (i : nat) (j : nat) : list bool :=
    let l2 := drop_n l i in
    (first_n l2 j).

  (* Check nth. *)
  Definition bb_nth (i : nat) (bv1 : t) : bool :=
    let (b1, n1) := bv1 in
    nth i b1 false.

End BV.



Module BVProof.

  Import BV.

  Definition bitof (bv : t)(m : nat) :=
    bb_nth m bv.

  Definition bblt_len (bv : t) :=
    let (b, n) := bv in
    n.




  Definition wf (bv:t) : Prop :=
     let (b,n) := bv in N.of_nat (length b) = n.

  Check N.of_nat.
  Print N.of_nat.
  SearchAbout N.of_nat.
  Search (N.of_nat (_ + _) = (N.of_nat _) + (N.of_nat _)).

  Lemma concat_wf : forall (bv1 bv2:t), wf bv1 -> wf bv2 -> wf (concat bv1 bv2).
  Proof.
    intros [b1 n1] [b2 n2] H1 H2.
    simpl.
    Search ((length (_ ++ _)) = ((length _) + (length _))%nat).
    SearchAbout length.
    rewrite app_length.
    rewrite Nat2N.inj_add.
    simpl in H1. simpl in H2.
    rewrite H1. rewrite H2.
    reflexivity.
  Qed.

  Lemma nth_append1 : forall A (l1 l2:list A) (i:nat) (d:A),
    (i < length l1)%nat -> nth i (l1 ++ l2) d = nth i l1 d.
  Proof.
    intros A. induction l1.
    - simpl. Search (~ ((_ < 0)%nat)).
      intros l2 i d H. elim (Lt.lt_n_0 _ H).
    - simpl. intros l2 [ |i] d Hi.
      * reflexivity.
      * apply IHl1. apply Lt.lt_S_n. assumption.
  Qed.

  Lemma of_nat_lt : forall i j,
    (of_nat i < of_nat j) -> (i < j)%nat.
  Admitted.

  Check nth.
  Lemma nth_wf : forall(bv1 bv2:t) (i : nat),
   let (b1, n1) := bv1 in
   wf bv1 -> wf bv2 -> (of_nat i < n1) -> bb_nth i (concat bv1 bv2) = bb_nth i bv1.
  Proof.
   intros [b1 n1] [b2 n2]. simpl. intros i H1 H2 Hi.
   rewrite nth_append1.
     - reflexivity.
     - rewrite <- H1 in Hi.
       apply of_nat_lt.
       assumption.
  Qed.


(* term *)
Definition formula := Type.
Definition sort := Type.
Definition term := sort -> Type.

Definition BitVec := nat -> sort.

Inductive bit :=
| b0
| b1.

(*
Definition const_bv := Type.
Definition bvn := const_bv.
Definition bvc := (bool * const_bv)
*)

Inductive const_bv :=
| bvn : const_bv
| bvc : bit -> const_bv ->const_bv.

Definition toBV (n : nat) (v : const_bv) :=
  (term (BitVec n)).
(* SC := n = bv_len v *)

Definition concat (t1 :term) (t2 :term) :=
  let (term (BitVec n)) := t1 in
  let (term (BitVec m)) := t2 in
  let m' := n + m in
  (term (BitVec m')).

Inductive bblt :=
| bbltn : bblt
| bbltc : formula -> bblt ->bblt.

Definition bblast_term := nat -> term -> bblt -> Type.

Definition var_bv := Type.

Definition bitof := var_bv -> nat -> formula.

Definition a_var_bv (n :nat) :=
  (term (BitVec n)).

Fixpoint bblt_len (v :bblt) : nat :=
  match v with
  | bbltn => 0
  | bbltc b v' => (bblt_len v') + 1
  end.

Definition decl_bblast (n :nat) (b : bblt)
  (t : term (BitVec n)) (bb : bblast_term) :=
  match (bblt_len b) with
  | n => (* (bblast_term n t b)?? *) abort
  | _ => abort
  end.

Definition bblast_var (x : var_bv) (n :nat) : bblt :=
  (bbltc (bitof x n) (bblast_var x (n - 1))).

Definition bv_bbl_var (n : nat)(x : var_bv)(f : bblt) :=
  match (bblast_var x (n - 1)) with
  | f => (bblast_term n (a_var_bv n x) f)
  | _ => abort
  end.

Definition bblast_bvand (x : bblt) (y : bblt) : bblt :=
  match x with
  | bbltn =>
    match y with
    | bbltn => bbltn
    | bbltc y''' y'' => abort
    end
  | bbltc bx x' =>
    match y with
    | bbltn => abort
    | bbltc by y' => (bbltc (and bx by) (bblast_bvand x' y'))
    end
  end.

Definition bv_bbl_bvand (n : nat) (x : (term (BitVec n))) (y : (term (BitVec n)))
  (xb : bblt) (yb : bblt) (rb : bblt)
  (xbb : (bblast_term n x xb)) (ybb : (bblast_term n y yb)) :=
  match (bblast_bvadd xb yb) with
  | rb => (bblast_term n (bvadd n x y) rb)
  | _ => abort
  end.

Fixpoint bblt_bvand_carry (a : bblt) (b : bblt) (c : formula) : formula :=
  match a with
  | bbltn =>
    match b with
    | bbltn => c
    | _ => abort
    end
  | bbltc ai a' =>
    match b with
    | bbltn => abort
    | bbltc bi b' => (or (and ai bi) (and xor ai bi) (bblt_bvand_carry a' b' c))
    end
  end.

Fixpoint bblast_bvand (a : bblt) (b : bblt) (carry : formula) : bblt :=
  match a with
  | bbltn =>
    match b with
    | bbltn => bbltn
    | _ => abort
    end
  | bbltc ai a' =>
    match b with
    | bbltn => abort
    | bbltc bi b' =>
      (bbltc (xor ai (xor bi (bblt_bvadd_carry a' b' carry))) (bblast_bvadd a' b' carry))
    end
  end.

Definition bv_bbl_bvadd (n : nat) (x : (term (BitVec n))) (y : (term (BitVec n)))
  (xb : bblt) (yb : bblt) (rb : bblt)
  (xbb : (bblast_term n x xb)) (ybb : (bblast_term n y yb)) :=
  match (bblast_bvadd xb yb) with
  | rb => (bblast_term n (bvadd n x y) rb)
  | _ => abort
  end.

End BVProof.
