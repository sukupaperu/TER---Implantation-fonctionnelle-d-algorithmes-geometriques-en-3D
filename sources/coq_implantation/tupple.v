Inductive tupple (A: Set) (B: Set): Set :=
	| Tupple : A -> B -> tupple A B
.

Definition tuppleFirst {A B} (t : tupple A B) : A :=
    match t with
    | Tupple _ _ a _ => a
    end
.

Definition tuppleSecond {A B} (t : tupple A B) : B :=
    match t with
    | Tupple _ _ _ b => b
    end
.