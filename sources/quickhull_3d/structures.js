"use strict";

// https://github.com/MostlyAdequate/mostly-adequate-guide/blob/master/SUMMARY.md

// ------------- Structures de données simples -------------

const new_he = (i,n,o,v) => ({
	index: i,
	next: n,
	opposite: o,
	vert: v
});
const new_null_he = () => new_he(-1,-1,-1,-1);
const new_he_set_opposite = (he,opposite) => new_he(
	he.index, he.next, opposite, he.vert
);
const new_he_set_no_opposite = (he) => new_he(
	he.index, he.next, -1, he.vert
);

// half-edge-list -> half-edge -> half-edge
const he_opposite = (he_l, he) => he_l[he.opposite];
const he_next = (he_l, he) => he_l[he.next];
const he_prev = (he_l, he) => he_next(he_l, he_next(he_l, he));
// half-edge-list -> half-edge -> integer
const he_from_vert = (he) => he.vert;
const he_to_vert = (he_l, he) => he_from_vert(he_next(he_l, he));

const he_nb_faces = (he_l) => he_l.length/3;

const he_by_face_index = (he_l, face_index) => he_l[face_index*3];
const he_face_2_he_index_list = (he_l, he) => [
	he_from_vert(he),
	he_to_vert(he_l, he),
	he_to_vert(he_l, he_next(he_l, he))
];
const he_2_face_index = (he) => Math.floor(he_index(he)/3);
const he_last_face_added = (he_l) => he_l[he_l.length - 1];

const he_find_in_face = (he_l, condition_on_he) =>
	he_l.length === 0
		? undefined
		: condition_on_he(he_l[he_l.length - 3], he_l.length - 3)
			? he_l[he_l.length - 3]
			: he_find_in_face(he_l.slice(0, he_l.length - 3), condition_on_he)
;

/*const he_concat_face = (he_l_dest, he_l_source, he_source) =>
	he_l_dest
		.concat(he_source)
		.concat(he_next(he_l_source, he_source))
		.concat(he_prev(he_l_source, he_source))
;*/

// half-edge -> integer
const he_index = (he) => he.index;
const he_opposite_index = (he) => he.opposite;
// half-edge -> boolean
const he_is_null = (he) => he_index(he) === -1;
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
		if(!he_is_null(he_l[i]))
        	action(he_l[i]);
    }
}

const look_up_for_opposite_he_index = (he_l, from_vert, to_vert) =>
	look_up_in_list(he_l, 
		(he) => he_from_vert(he) === to_vert && he_to_vert(he_l, he) === from_vert
	)
;

const concat_face_vertices = (he_l, vert_A, vert_B, vert_C) =>
{
	//GLOBAL_DISP.push_indices([vert_A, vert_B, vert_C]);
	GLOBAL_DISP.push_he_l(he_l);

	const he_AB_index = he_l.length;
	const he_BC_index = he_l.length + 1;
	const he_CA_index = he_l.length + 2;

	const he_AB_opposite_index = look_up_for_opposite_he_index(he_l, vert_A, vert_B);
	const he_BC_opposite_index = look_up_for_opposite_he_index(he_l, vert_B, vert_C);
	const he_CA_opposite_index = look_up_for_opposite_he_index(he_l, vert_C, vert_A);

	const he_l_result = he_l
		.map((he_curr) => {
			if(!he_is_null(he_curr))
				switch(he_index(he_curr))
				{
					case he_AB_opposite_index: return new_he_set_opposite(he_curr, he_AB_index);
					case he_BC_opposite_index: return new_he_set_opposite(he_curr, he_BC_index);
					case he_CA_opposite_index: return new_he_set_opposite(he_curr, he_CA_index);
				}
			return he_curr;
		})
		.concat(new_he(he_AB_index, he_BC_index, he_AB_opposite_index, vert_A))
		.concat(new_he(he_BC_index, he_CA_index, he_BC_opposite_index, vert_B))
		.concat(new_he(he_CA_index, he_AB_index, he_CA_opposite_index, vert_C))
	;

	GLOBAL_DISP.push_he_l(he_l_result);

	return he_l_result;
};
const concat_face = (he_l, tri) => concat_face_vertices(he_l, tri[0], tri[1], tri[2]);

const remove_face = (he_l, he) => {
	if(he_is_null(he))
		console.error("Ne devrait pas arriver : suppression d'une face déjà supprimée.");

	//GLOBAL_DISP.push_he_l(he_l);

	const he_A = he;
	const he_B = he_next(he_l, he);
	const he_C = he_prev(he_l, he);

	const he_A_index = he_index(he_A);
    const he_B_index = he_index(he_B);
    const he_C_index = he_index(he_C);

	const he_A_opposite_index = he_opposite_index(he_A);
    const he_B_opposite_index = he_opposite_index(he_B);
    const he_C_opposite_index = he_opposite_index(he_C);

	const he_l_result = he_l
		.map((he_curr) => {
			if(!he_is_null(he_curr))
				switch(he_index(he_curr))
				{
					case he_A_index:
					case he_B_index:
					case he_C_index:
						return new_null_he();
					case he_A_opposite_index:
					case he_B_opposite_index:
					case he_C_opposite_index:
						return new_he_set_no_opposite(he_curr);
				}
			return he_curr;
		})
	;

	GLOBAL_DISP.push_he_l(he_l_result);

	return he_l_result;
};

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

const look_up_in_list = (list,condition) =>
	list.length === 0
		? -1
		: condition(list[list.length - 1])
			? list.length - 1
			: look_up_in_list(list.slice(0,-1), condition)
;

// const is_in_list = (list,value) =>
// 	list.length === 0
// 		? false
// 		: list[list.length - 1] === value
// 			? true
// 			: is_in_list(list.slice(0,-1), value)
// ;

const replace_value_in_list = (list,i,new_value) =>
	list.slice(0, i).concat(new_value).concat(list.slice(i + 1));

/*
	(vertex -> vertex -> bool) -> vertex
*/
const bool_reducer = bool_cond => 
    (u,v) => bool_cond(u, v) ? u : v;

const is_defined = (a) => a !== undefined;
const list_is_empty = (l) => l.length === 0;