Require Import List.
Require Import Nat Bool.
(* Inductive tupple (A: Set) (B: Set): Set :=
| Tupple : A -> B -> tupple A B
. *)

Inductive he : Set :=
    | NullHe : he
    (* index -> opposite -> vertex *)
    | He : nat -> option nat -> nat -> he
.

Definition setHeOpposite (h: he) (o: option nat) : he :=
    match h with
    | NullHe => NullHe
    | He i _ v => He i o v
    end
.

Definition setHeToBoundaryHe (h: he) : he :=
    setHeOpposite h None
.

Inductive dcel : Set :=
    | EmptyDcel : dcel
    (* he_list -> available_he_index *)
    | Dcel : list he -> nat -> dcel
.

Definition heIndex (h: he) : option nat :=
    match h with
    | NullHe => None
    | He i _ _ => Some i
    end
.

Definition nextHeIndex (h: he) : option nat :=
    match h with
    | NullHe => None
    | He i _ _ => Some ((i - (modulo i 3)) + (modulo (i + 1) 3))
    end
.

Definition previousHeIndex (h: he) : option nat :=
    match h with
    | NullHe => None
    | He i _ _ => Some ((i - (modulo i 3)) + (modulo (3 + i - 1) 3))
    end
.

Definition oppositeHeIndex (h: he) : option nat :=
    match h with
    | NullHe => None
    | He _ o _ => o
    end
.

Definition sourceVertexOfHe (h: he) : option nat :=
    match h with
    | NullHe => None
    | He _ _ v => Some v
    end
.

(* Definition destinationVertexOfHe (d: dcel) (h: he) : option nat :=
    match d with
    | EmptyDcel => 
    end
. *)

(* 

	// dcel -> he -> int
	const destination_vertex_of_he = (dcel, he) =>
		source_vertex_of_he(next_he(dcel, he))
	;

	// dcel -> int -> he
	const get_he_by_he_index = (dcel, he_index_to_find) =>
		{
			const he_found = dcel.he_list.find((he) => he_index(he) === he_index_to_find);
			return is_defined(he_found) ? he_found : new_null_he();
		}	
	; *)