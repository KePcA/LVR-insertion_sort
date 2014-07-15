(***************************************** Proofs of correctness for insertion insertion_sort *****************************************)
Require Import List.
Require Import ZArith.
Open Scope Z_scope.

(************************************** Implementation of the insertion insertion_sort algorithm **************************************)

(* Inserts the specified element z into the lst at the correct position. *)
Fixpoint insert (z:Z) (l : list Z) {struct l} : list Z :=
	match l with
		| nil => z::nil
		| head::tail => if Z_le_gt_dec z head then z::head::tail else head::(insert z tail)
	end.

(* The insertion_sort function. *)
Fixpoint insertion_sort (l : list Z) {struct l} : (list Z) := 
	match l with
		| nil => nil
		| head::tail => insert head (insertion_sort tail)
end.

(*********************************************************** Helper methods ***********************************************************)

(* Inductive check for when a list is sorted. *)
Inductive sorted : list Z -> Prop :=
	| sorted0 : sorted nil
	| sorted1: forall z:Z, sorted (z::nil)
	| sorted2: forall (z1 z2 : Z) (l : list Z),
		z1 <= z2 -> sorted (z2::l) -> sorted (z1::z2::l).

(* Insertion sort hints for sorted list. *)
Hint Resolve sorted0 sorted1 sorted2 : insertion_sort.

(* Counts the number of occurrences of the element z in list l. *)
Fixpoint count (z:Z) (l : list Z) {struct l} : nat :=
	match l with
	| nil => O
	| (head::tail) => if Z_eq_dec z head then S (count z tail) else count z tail
	end.

(* Definition of equality for two lists. Two lists are equal if they contain the same elements (are permuted). *)
Definition is_equal (l l' : list Z) :=
	forall z : Z, count z l = count z l'.

(* Definition of reflexive for a list. *)
Lemma is_equal_refl : forall l : list Z, is_equal l l.
Proof.
	unfold is_equal.
	trivial.
Qed.

(* Definition of simetry for two lists that have been permuted. *)
Lemma is_equal_syme : forall l l' : list Z, is_equal l l' -> is_equal l' l.
Proof.
	unfold is_equal.
	auto.
Qed.

(* Definition of transitivity for three lists. *)
Lemma is_equal_trans : forall l l' l'' : list Z, 
	is_equal l l' -> is_equal l' l'' -> is_equal l l''.
Proof.
	intros.
	unfold is_equal in *.
	intro; eapply trans_eq; eauto.
Qed.

(* Definition of equality for two lists that have been extended with a value. *)
Lemma is_equal_cons : forall (z : Z) (l l' : list Z), 
	is_equal l l' -> is_equal (z::l) (z::l').
Proof.
	intros z l l' H z'.
	simpl.
	case (Z_eq_dec z' z).
	auto.
	auto.
Qed.

(* Definition of equality for two lists that have been extended with two value in permutated order. *)
Lemma is_equal_perm : forall (x y : Z) (l l' : list Z),
	is_equal l l' -> is_equal (x::y::l) (y::x::l').
Proof.
	intros x y l l' H z; simpl.
	case (Z_eq_dec z x); case (Z_eq_dec z y); simpl; case (H z); auto.
Qed.

(* Insertion sort hints for the equality of permuted lists. *)
Hint Resolve is_equal_cons is_equal_refl is_equal_perm : insertion_sort.

(******************************************************** Proofs of correctness *******************************************************)

(* Lemma that states that applying the inser method on an already sorted list stays sorted. *)
Lemma sorted_insert : forall (l : list Z) (x : Z),
	sorted l -> sorted (insert x l).
Proof.
	intros l x H; elim H.

	simpl; auto with insertion_sort.

	intro z; simpl.
	case (Z_le_gt_dec x z); simpl; auto with insertion_sort zarith. 

	simpl.
	intros z1 z2; case (Z_le_gt_dec x z2); simpl; intros;
	case (Z_le_gt_dec x z1); simpl; auto with insertion_sort zarith.
Qed.

(* Lemma that states the insert method preserves all of the elements. *)
Lemma insert_preserves : forall (l : list Z) (x : Z), 
	is_equal (x::l) (insert x l).
Proof.
	induction l as [ | a l0 H]; simpl.
	auto with insertion_sort.
	intros x; case (Z_le_gt_dec x a); simpl.
	auto with insertion_sort.
	intro; apply is_equal_trans with (a :: x :: l0); auto with insertion_sort.
Qed.

(* Lemma that states that applying the insertion sort on an already sorted list stays sorted. *)
Lemma sorted_insertion_sort : forall (l : list Z), sorted (insertion_sort l).
Proof.
	induction l.
	auto with insertion_sort.
	simpl.
	apply sorted_insert.
	assumption.
Qed.

(* Lemma that states that insertion sort algorithm preserves all of the elements. *)
Lemma insertion_sort_preserves: forall (l : list Z), (is_equal l (insertion_sort l)).
Proof.
	induction l.
	auto with insertion_sort.
	simpl.
	eauto using is_equal_trans, insert_preserves with insertion_sort.
Qed.

(******************************************************* Testing insertion sort *******************************************************)

Eval compute in (insert 1 (2::5:: nil)).
Eval compute in (insert 6 (1::2::3::4::5::7:: nil)).
Eval compute in (insert 6 (1::2::3::4::5::6::7:: nil)).
Eval compute in (insert 4 (24::50::nil)).

Eval compute in (insertion_sort (3::2::4::7::1::5::nil)).
Eval compute in (insertion_sort (15::23::74::90::0::10::nil)).