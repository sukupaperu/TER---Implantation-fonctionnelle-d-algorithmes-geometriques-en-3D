Require Import other_structures Nat Bool.

(* Constructeurs et définitions *)

Inductive he : Set :=
    (* index -> opposite -> vertex *)
    | He : nat -> option nat -> nat -> he
.

Definition setHeOpposite (h: he) (o: nat) : he :=
    match h with
    | He i _ v => He i (Some o) v
    end
.

Definition setHeToBoundaryHe (h: he) : he :=
    match h with
    | He i _ v => He i None v
    end
.

Inductive dcel : Set :=
    (* he_list -> available_he_index *)
    | Dcel : list he -> nat -> dcel
.

Definition emptyDcel : dcel :=
    Dcel nil 0
.

(* Accesseurs *)

Definition heIndex (h: he) : nat :=
    match h with
    | He i _ _ => i
    end
.

Definition nextHeIndex (h: he) : nat :=
    match h with
    | He i _ _ => ((i - (modulo i 3)) + (modulo (i + 1) 3))
    end
.


Definition previousHeIndex (h: he) : nat :=
    match h with
    | He i _ _ => ((i - (modulo i 3)) + (modulo (3 + i - 1) 3))
    end
.

Definition oppositeHeIndex (h: he) : option nat :=
    match h with
    | He _ o _ => o
    end
.

Definition sourceVertexOfHe (h: he) : nat :=
    match h with
    | He _ _ v => v
    end
.

Definition getHeByHeIndex (d: dcel) (i: nat) : option he :=
    match d with
    | Dcel l _ => find (fun h' => i =? heIndex(h')) l
    end
.

(* Propriétés *)

Definition heIsBoundary (h: he) : bool :=
    match oppositeHeIndex h with
    | None => true
    | Some _ => false
    end
.

(* Accesseurs avancés *)

Definition oppositeHe (d: dcel) (h: he) : option he :=
    match oppositeHeIndex h with
    | None => None
    | Some o => getHeByHeIndex d o
    end
.

Definition nextHe (d: dcel) (h: he) : option he :=
    getHeByHeIndex d (nextHeIndex h)
.

Definition previousHe (d: dcel) (h: he) : option he :=
    getHeByHeIndex d (previousHeIndex h)
.

Definition heByFaceIndex (d: dcel) (face_index: nat) : option he :=
    getHeByHeIndex d (face_index*3)
.

Definition destinationVertexOfHe (d: dcel) (h: he) : option nat :=
    match nextHe d h with
    | None => None
    | Some h' => Some (sourceVertexOfHe h')
    end
.

Definition addFace (d: dcel) (vert_A vert_B vert_C: nat) : dcel :=
    let ' Dcel he_list available_he_index := d in
    let he_AB_index := available_he_index in
	let he_BC_index := available_he_index + 1 in
	let he_CA_index := available_he_index + 2 in
    
    let lookUpForOppositeHeIndex :=
        fun (src_vert_index dest_vert_index: nat) =>
            match
                find
                (fun (h': he) =>
                    match destinationVertexOfHe d h' with
                    | Some destinationVertex =>
                        (src_vert_index =? sourceVertexOfHe h') && (dest_vert_index =? destinationVertex)
                    | None => false
                    end
                )
                he_list
            with
            | Some h' => Some (heIndex h')
            | None => None
            end
        in
    
    let he_AB_opposite_index := lookUpForOppositeHeIndex vert_A vert_B in
    let he_BC_opposite_index := lookUpForOppositeHeIndex vert_B vert_C in
    let he_CA_opposite_index := lookUpForOppositeHeIndex vert_C vert_A in
    
    let areEqual :=
        fun (i: nat) (j: option nat) =>
            match j with
            | Some j' => i =? j'
            | None => false
            end
        in

    Dcel
    (
        (
            map
            (fun (h': he) =>
                let i := heIndex h' in
                if areEqual i he_AB_opposite_index then setHeOpposite h' he_AB_index
                else if areEqual i he_BC_opposite_index then setHeOpposite h' he_BC_index
                else if areEqual i he_CA_opposite_index then setHeOpposite h' he_CA_index
                else h'
            )
            he_list
        )
        ++ (He he_AB_index he_AB_opposite_index vert_A) :: nil
        ++ (He he_BC_index he_BC_opposite_index vert_B) :: nil
        ++ (He he_CA_index he_CA_opposite_index vert_C) :: nil
    )
    (available_he_index + 3)
.