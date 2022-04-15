Require Import List.
Require Import Arith.
Require Export List.

Fixpoint newOrderedIntList (n: nat): list nat :=
	match n with
		| 0 => nil
		| S n => (newOrderedIntList n) ++ (n :: nil)
	end
.

Fixpoint valueInListByIndexRec {A} (l: list A) (index: nat) (current_index: nat): option A :=
  match l with
	| nil => None
	| el :: m =>
		if beq_nat index current_index
		then Some el
		else valueInListByIndexRec m index (S current_index)
  end
.
Fixpoint valueInListByIndex {A} (l: list A) (index: nat): option A :=
	valueInListByIndexRec l index 0
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

Definition firstArgIfTrueOption {T} (f: T->T->option bool) : T->T->option T :=
	fun (a b: T) =>
		match f a b with
		| Some res => Some (if res then a else b)
		| None => None
		end
.

Fixpoint reduceList {A B} (l: list A) (action_on_reduce: A->B->B) (init_value: B): B :=
	match l with
	| nil => init_value
	| a :: l' => action_on_reduce a (reduceList l' action_on_reduce init_value)
	end
.

Definition reduceListSimple {A} (l: list A) (action_on_reduce: A->A->A): option A :=
	match hd_error l with
	| Some head_value => Some (reduceList l action_on_reduce head_value)
	| None => None
	end
.

Fixpoint reduceListOption {A B} (l: list A) (action_on_reduce: A->B->option B) (init_value: B): option B :=
	match l with
	| nil => Some init_value
	| a :: l' =>
		match reduceListOption l' action_on_reduce init_value with
		| Some res => action_on_reduce a res
		| None => None
		end
	end
.

Fixpoint reduceListSimpleOption {A} (l: list A) (action_on_reduce: A->A->option A): option A :=
	match hd_error l with
	| Some head_value => reduceListOption l action_on_reduce head_value
	| None => None
	end
.