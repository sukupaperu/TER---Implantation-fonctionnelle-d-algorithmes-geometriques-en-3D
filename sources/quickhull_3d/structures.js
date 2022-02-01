"use strict";

// https://github.com/MostlyAdequate/mostly-adequate-guide/blob/master/SUMMARY.md

let DISPLAY_STRUC;
function set_display_struct(d)
{
    DISPLAY_STRUC = d;
}

// ------------- Structures de données simples -------------
const vec3 = (x,y,z) => ({x:x, y:y, z:z});

const new_he = (i,n,o,v) => ({
	index: i,
	next: n,
	opposite: o,
	vert: v
});
// const new_null_he = () => new_he(-1,-1,-1,-1);
const new_he_set_opposite = (he,opposite) => new_he(
	he.index,
	he.next,
	opposite,
	he.vert
);

// half-edge-list -> half-edge -> half-edge
const he_opposite = (he_l, he) => he_l[he.opposite];
const he_next = (he_l, he) => he_l[he.next];
const he_prev = (he_l, he) => he_next(he_l, he_next(he_l, he));
// half-edge-list -> half-edge -> integer
const he_from_vert = (he) => he.vert;
const he_to_vert = (he_l, he) => he_from_vert(he_next(he_l, he));

// half-edge -> integer
const he_index = (he) => he.index;
// half-edge -> boolean
// const he_is_null = (he) => he_index(he) === -1;
const he_is_boundary = (he) => !he_is_null(he) && he.opposite === -1;

function he_for_each_vertices(he_l, he, action)
{
    action(
        he_from_vert(he),
        he_from_vert(he_next(he_l, he)),
        he_from_vert(he_prev(he_l, he))
    );
}
function he_for_each_faces(he_l, action)
{
    for(let i = 0; i < he_l.length; i += 3)
    {
        action(he_l[i]);
    }
}

const find_opposite_he_index = (he_l, from_vert, to_vert) =>
{
	if(he_l.length > 0)
	{
		const he_from_to_are_opposite = (he_l, he, from_vert, to_vert) =>
			he_from_vert(he) === to_vert && he_to_vert(he_l, he) === from_vert;

		const he_found = reduce_list(
			he_l,
			(he_a, he_b) => 
				he_from_to_are_opposite(he_l, he_a, from_vert, to_vert)
				? he_a
				: he_b
		);
		
		return he_from_to_are_opposite(he_l, he_found, from_vert, to_vert)
			? he_index(he_found)
			: -1;
	}
	return -1;
};

const concat_face_vertices = (he_l, vert_A, vert_B, vert_C) =>
{
	const he_opposite_filler = (he_opposite_index, he_current_index) =>
		(he) => 
			he_index(he) === he_opposite_index
				? new_he_set_opposite(he, he_current_index)
				: he
	;

    disp.push_indices([vert_A, vert_B, vert_C]);

	const he_AB_index = he_l.length;
	const he_BC_index = he_l.length + 1;
	const he_CA_index = he_l.length + 2;

	const he_AB_opposite_index = find_opposite_he_index(he_l, vert_A, vert_B);
	const he_BC_opposite_index = find_opposite_he_index(he_l, vert_B, vert_C);
	const he_CA_opposite_index = find_opposite_he_index(he_l, vert_C, vert_A);

	return he_l
		.map(he_opposite_filler(he_AB_opposite_index, he_AB_index))
		.map(he_opposite_filler(he_BC_opposite_index, he_BC_index))
		.map(he_opposite_filler(he_CA_opposite_index, he_CA_index))
		.concat(
			new_he(he_AB_index, he_BC_index, he_AB_opposite_index, vert_A),
			new_he(he_BC_index, he_CA_index, he_BC_opposite_index, vert_B),
			new_he(he_CA_index, he_AB_index, he_CA_opposite_index, vert_C)
		)
	;
};
const concat_face = (he_l, tri) => concat_face_vertices(he_l, tri[0], tri[1], tri[2]);

// ------------- Fonctions sur les listes -------------

/*
    Créé une liste ordonnée d'entiers de 0 à n - 1
*/
const new_ordered_int_list = (n) =>
    n === 0
        ? []
        : n === 1
            ? [0]
            : new_ordered_int_list(n - 1).concat(n - 1)
;

/*
	list_el -> (el -> el -> el) -> el
	Exemple :
		reduce_list([2,5,8,4,6], (x,y) => x > y ? x : y);
		-> 8
*/
const reduce_list = (list,reducer) => 
    list.length === 0
        ? (function(){ throw new Error("reduce_list of empty list with no initial value"); })()
        : list.length === 1
            ? list[0]
            : reducer(
                reduce_list(list.slice(1), reducer),
                list[0]
            );
;

/*
	list_el -> (el -> bool) -> list_el
	Exemple :
		filter_list([2,5,8,4,6], x => x > 2 && x < 6);
		-> [4,5]
*/
const filter_list = (list,filter) =>
	list.length === 0
		? []
		: filter(list[0])
            ? filter_list(list.slice(1), filter).concat(list[0])
            : filter_list(list.slice(1), filter)
;

/*
	(vertex -> vertex -> bool) -> vertex
*/
const bool_reducer = bool_cond => 
    (u,v) => bool_cond(u, v) ? u : v;