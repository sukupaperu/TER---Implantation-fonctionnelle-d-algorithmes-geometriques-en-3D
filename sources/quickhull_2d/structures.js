"use strict";

// https://github.com/MostlyAdequate/mostly-adequate-guide/blob/master/SUMMARY.md

// ------------- Structures de données simples -------------
const vertex_3d = (x,y,z) => ({ x:x, y:y, z:z });
const vertex_2d = (x,y) => vertex_3d(x,y,0);

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
        ? []
        : list.length === 1
            ? list[0]
            : reducer(
                reduce_list(list.slice(1), reducer),
                list[0]
            )
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