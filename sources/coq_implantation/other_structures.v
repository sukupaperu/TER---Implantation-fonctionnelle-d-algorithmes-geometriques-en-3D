Require Import List.
Require Import Arith.
Require Export List.

Fixpoint new_ordered_int_list (n: nat): list nat :=
	match n with
		| 0 => nil
		| S n => (new_ordered_int_list n) ++ (n :: nil)
	end
.

Fixpoint list_length {A} (l: list A): nat :=
	match l with
		| nil => 0
		| _ :: m => S (list_length m)
	end
.

Fixpoint value_in_list_by_index_rec {A} (l: list A) (index: nat) (default: A) (current_index: nat): A :=
  match l with
	| nil => default
	| el :: m =>
		if beq_nat index current_index
		then el
		else value_in_list_by_index_rec m index default (S current_index)
  end
.
Fixpoint value_in_list_by_index {A} (l: list A) (index: nat) (default: A): A :=
	value_in_list_by_index_rec l index default 0
.

Definition list_is_empty {A} (l: list A): bool :=
	match l with
	| nil => true
	| _ => false
	end
.

Definition first_arg_if_true {T} (f: T->T->bool) : T->T->T :=
	fun (a b: T) => if (f a b) then a else b
.

Fixpoint reduce_list {A B} (l: list A) (action_on_reduce: A->B->B) (default: B): B :=
  match l with
    | nil => default
    | a :: b => action_on_reduce a (reduce_list b action_on_reduce default)
  end
.

Fixpoint filter_list {A} (l: list A) (predicate: A->bool): list A :=
  match l with
	| nil => nil
	| a :: b =>
	  if predicate a
	  then a :: (filter_list b predicate)
	  else filter_list b predicate
  end
.