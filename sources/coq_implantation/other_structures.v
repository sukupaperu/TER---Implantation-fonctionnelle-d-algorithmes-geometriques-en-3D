Require Import List.
Require Import Arith.
Require Export List.

Fixpoint newOrderedIntList (n: nat): list nat :=
	match n with
		| 0 => nil
		| S n => (newOrderedIntList n) ++ (n :: nil)
	end
.

Fixpoint listLength {A} (l: list A): nat :=
	match l with
		| nil => 0
		| _ :: m => S (listLength m)
	end
.

Fixpoint valueInListByIndexRec {A} (l: list A) (index: nat) (default: A) (current_index: nat): A :=
  match l with
	| nil => default
	| el :: m =>
		if beq_nat index current_index
		then el
		else valueInListByIndexRec m index default (S current_index)
  end
.
Fixpoint valueInListByIndex {A} (l: list A) (index: nat) (default: A): A :=
	valueInListByIndexRec l index default 0
.

Definition listIsEmpty {A} (l: list A): bool :=
	match l with
	| nil => true
	| _ => false
	end
.

Definition firstArgIfTrue {T} (f: T->T->bool) : T->T->T :=
	fun (a b: T) => if (f a b) then a else b
.

Fixpoint reduceList {A B} (l: list A) (action_on_reduce: A->B->B) (default: B): B :=
  match l with
    | nil => default
    | a :: b => action_on_reduce a (reduceList b action_on_reduce default)
  end
.

Fixpoint filterList {A} (l: list A) (predicate: A->bool): list A :=
  match l with
	| nil => nil
	| a :: b =>
	  if predicate a
	  then a :: (filterList b predicate)
	  else filterList b predicate
  end
.