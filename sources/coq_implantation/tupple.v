Inductive tupple (A: Set) (B: Set): Set :=
	| Tupple : A -> B -> tupple A B
.

Definition tupple_first {A B} (t : tupple A B) : A :=
    match t with
    | Tupple _ _ a _ => a
    end
.

Definition tupple_second {A B} (t : tupple A B) : B :=
    match t with
    | Tupple _ _ _ b => b
    end
.

(* Eval compute in tupple_second (Tupple nat bool 5 true). *)